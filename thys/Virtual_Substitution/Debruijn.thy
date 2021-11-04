section "Debruijn Indicies Formulation"
theory Debruijn
  imports PolyAtoms
begin
subsection "Lift and Lower Functions"

text "these functions are required for debruijn notation
  the (liftPoly n a p) functions increment each variable greater n in polynomial p by a
  the (lowerPoly n a p) functions lower each variable greater than n by a so variables n through n+a-1 shouldn't exist
"
context includes poly_mapping.lifting begin

definition "inc_above b i x = (if x < b then x else x + i::nat)"
definition "dec_above b i x = (if x \<le> b then x else x - i::nat)"

lemma inc_above_dec_above: "x < b \<or> b + i \<le> x \<Longrightarrow> inc_above b i (dec_above b i x) = x"
  by (auto simp: inc_above_def dec_above_def)
lemma dec_above_inc_above: "dec_above b i (inc_above b i x) = x"
  by (auto simp: inc_above_def dec_above_def)

lemma inc_above_dec_above_iff: "inc_above b i (dec_above b i x) = x \<longleftrightarrow> x < b \<or> b + i \<le> x"
  by (auto simp: inc_above_def dec_above_def)

lemma inj_on_dec_above: "inj_on (dec_above b i) {x. x < b \<or> b + i \<le> x}"
  by (rule inj_on_inverseI[where g = "inc_above b i"]) (auto simp: inc_above_dec_above)

lemma finite_inc_above_ne: "finite {x. f x \<noteq> c} \<Longrightarrow> finite {x. f (inc_above b i x) \<noteq> c}"
proof -
  fix b and f::"nat\<Rightarrow>'a"
  assume f: "finite {x. f x \<noteq> c}"
  moreover
  have "finite {x. f (x + i) \<noteq> c}"
  proof -
    have "{x. f (x + i) \<noteq> c} = (+) i -` {x. f x \<noteq> c}"
      by (auto simp: ac_simps)
    also have "finite \<dots>"
      by (rule finite_vimageI) (use f in auto)
    finally show ?thesis .
  qed
  ultimately have "finite ({x. f x \<noteq> c} \<union> {x. f (x + i) \<noteq> c})"
    by auto
  from _ this show "finite {x. f (inc_above b i x) \<noteq> c}"
    by (rule finite_subset) (auto simp: inc_above_def)
qed

lemma finite_dec_above_ne: "finite {x. f x \<noteq> c} \<Longrightarrow> finite {x. f (dec_above b i x) \<noteq> c}"
proof -
  fix b and f::"nat\<Rightarrow>'a"
  assume f: "finite {x. f x \<noteq> c}"
  moreover
  have "finite {x. f (x - i) \<noteq> c}"
  proof -
    have "{x. f (x - i) \<noteq> c} \<subseteq> {0..i} \<union> ((\<lambda>x. x - i) -` {x. f x \<noteq> c} \<inter> {i<..})"
      by auto
    also have "finite \<dots>"
      apply (rule finite_UnI[OF finite_atLeastAtMost])
      by (rule finite_vimage_IntI) (use f in \<open>auto simp: inj_on_def\<close>)
    finally (finite_subset) show ?thesis .
  qed
  ultimately have "finite ({x. f x \<noteq> c} \<union> {x. f (x - i) \<noteq> c} \<union> {b})"
    by auto
  from _ this show "finite {x. f (dec_above b i x) \<noteq> c}"
    by (rule finite_subset) (auto simp: dec_above_def)
qed

lift_definition lowerPowers::"nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow>\<^sub>0 'a) \<Rightarrow> (nat \<Rightarrow>\<^sub>0 'a::zero)"
  is "\<lambda>b i p x. if x \<in> {b..<b+i} then 0 else p (dec_above b i x)::'a"
proof -
  fix b i::nat and p::"nat \<Rightarrow> 'a"
  assume "finite {x. p x \<noteq> 0}"
  then have "finite {x. p (dec_above b i x) \<noteq> 0}"
    by (rule finite_dec_above_ne)
  from _ this show "finite {x. (if x \<in> {b..<b+i} then 0 else p (dec_above b i x)) \<noteq> 0}"
    by (rule finite_subset) auto
qed

lift_definition higherPowers::"nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow>\<^sub>0 'a) \<Rightarrow> (nat \<Rightarrow>\<^sub>0 'a::zero)"
  is "\<lambda>b i p x. p (inc_above b i x)::'a"
  by (simp_all add: finite_inc_above_ne)

lemma higherPowers_lowerPowers: "higherPowers n i (lowerPowers n i x) = x"
  by transfer (force simp: dec_above_def inc_above_def antisym_conv2)

lemma inj_lowerPowers: "inj (lowerPowers b i)"
  using higherPowers_lowerPowers
  by (rule inj_on_inverseI)

lemma lowerPowers_higherPowers:
  "(\<And>j. n \<le> j \<Longrightarrow> j < n + i \<Longrightarrow> lookup x j = 0) \<Longrightarrow> lowerPowers n i (higherPowers n i x) = x"
  by (transfer fixing: n i) (force simp: inc_above_dec_above)

lemma inj_on_higherPowers: "inj_on (higherPowers n i) {x. \<forall>j. n \<le> j \<and> j < n + i \<longrightarrow> lookup x j = 0}"
  using lowerPowers_higherPowers
  by (rule inj_on_inverseI) auto

lemma higherPowers_eq: "lookup (higherPowers b i p) x = lookup p (inc_above b i x)"
  by (simp_all add: higherPowers.rep_eq)

lemma lowerPowers_eq: "lookup (lowerPowers b i p) x = (if b \<le> x \<and> x < b + i then 0 else lookup p (dec_above b i x))"
  by (auto simp add: lowerPowers.rep_eq)

lemma keys_higherPowers: "keys (higherPowers b i m) = dec_above b i ` (keys m \<inter> {x. x \<notin> {b..<b+i}})"
  apply safe
  subgoal for x
    apply (rule image_eqI[where x="inc_above b i x"])
     apply (auto simp: dec_above_inc_above in_keys_iff higherPowers.rep_eq)
    by (metis add_less_cancel_right inc_above_def leD)
  subgoal for x
    by (auto simp: inc_above_dec_above in_keys_iff higherPowers.rep_eq)
  done

context includes fmap.lifting begin

lift_definition lowerPowers\<^sub>f::"nat \<Rightarrow> nat \<Rightarrow> (nat, 'a) fmap \<Rightarrow> (nat, 'a::zero) fmap"
  is "\<lambda>b i p x. if x \<in> {b..<b+i} then None else p (dec_above b i x)"
proof -
  fix b i::nat and p::"nat \<Rightarrow> 'a option"
  assume "finite (dom p)"
  then have "finite {x. p x \<noteq> None}" by (simp add: dom_def)

  have "dom (\<lambda>x. p (dec_above b i x)) = {x. p (dec_above b i x) \<noteq> None}"
    by auto
  also have "finite \<dots>"
    by (rule finite_dec_above_ne) fact
  finally
  have "finite (dom (\<lambda>x. p (dec_above b i x)))" .
  from _ this
  show "finite (dom (\<lambda>x. if x \<in> {b..<b+i} then None else p (dec_above b i x)))"
    by (rule finite_subset) (auto split: if_splits)
qed

lift_definition higherPowers\<^sub>f::"nat \<Rightarrow> nat \<Rightarrow> (nat, 'a) fmap \<Rightarrow> (nat, 'a) fmap"
  is "\<lambda>b i f x. f (inc_above b i x)"
proof -
  fix b i::nat and f::"nat \<Rightarrow> 'a option"
  assume "finite (dom f)"
  then have "finite {i. f i \<noteq> None}" by (simp add: dom_def)

  have "dom (\<lambda>x. f (inc_above b i x)) = {x. f (inc_above b i x) \<noteq> None}"
    by auto
  also have "finite \<dots>"
    by (rule finite_inc_above_ne) fact
  finally show "finite (dom (\<lambda>x. f (inc_above b i x)))"
    .
qed

lemma map_of_map_key_inverse_fun_eq:
  "map_of (map (\<lambda>(k, y). (f k, y)) xs) x = map_of xs (g x)"
  if "\<And>x. x \<in> set xs \<Longrightarrow> g (f (fst x)) = fst x" "f (g x) = x"
  for f::"'a \<Rightarrow> 'b"
  using that
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  from Cons
  have IH: "map_of (map (\<lambda>a. (f (fst a), snd a)) xs) x = map_of xs (g x)"
    by (auto simp: split_beta')
  have inv_into: "g (f (fst a)) = fst a"
    by (rule Cons) simp
  show ?case
    using Cons
    by (auto simp add: split_beta' inv_into IH)
qed

lemma map_of_filter_key_in: "P x \<Longrightarrow> map_of (filter (\<lambda>(k, v). P k) xs) x = map_of xs x"
  by (induction xs) (auto simp: )

lemma map_of_eq_NoneI: "x\<notin>fst`set xs \<Longrightarrow> map_of xs x = None"
  by (induction xs) (auto simp: )

lemma compute_higherPowers\<^sub>f[code]: "higherPowers\<^sub>f b i (fmap_of_list xs) =
  fmap_of_list (map (\<lambda>(k, v). (if k < b then k else k - i, v)) (filter (\<lambda>(k, v). k \<notin> {b..<b+i}) xs))"
proof -
  have *: "map_of (map (\<lambda>(k, y). (if k < b then k else k - i, y)) (filter (\<lambda>(k, v).  b \<le> k \<longrightarrow> \<not> k < b + i) xs)) x =
    map_of (filter (\<lambda>(k, v).  b \<le> k \<longrightarrow> \<not> k < b + i) xs) (if x < b then x else x + i)"
    for x
    by (rule map_of_map_key_inverse_fun_eq[where g="\<lambda>k. if k < b then k else k + i"
          and f = "\<lambda>k. if k < b then k else k - i"]) auto
  show ?thesis
    by (auto
        simp add: * higherPowers\<^sub>f.rep_eq lowerPowers\<^sub>f.rep_eq fmlookup_of_list fmlookup_default_def 
        inc_above_def
        map_of_filter_key_in
        split: option.splits
        intro!: fmap_ext)
qed

lemma compute_lowerPowers\<^sub>f[code]: "lowerPowers\<^sub>f b i (fmap_of_list xs) =
  fmap_of_list (map (\<lambda>(k, v). (if k < b then k else k + i, v)) xs)"
  apply (auto 
      simp add: lowerPowers\<^sub>f.rep_eq fmlookup_of_list fmlookup_default_def 
      dec_above_def
      map_of_filter_key_in
      split: option.splits
      intro!: fmap_ext)
  subgoal by (rule map_of_eq_NoneI[symmetric]) (auto split: if_splits)
  subgoal by (subst map_of_map_key_inverse_fun_eq[where g="\<lambda>k. if k < b then k else k - i"]) auto
  subgoal by (subst map_of_map_key_inverse_fun_eq[where g="\<lambda>k. if k < b then k else k - i"]) auto
  subgoal by (rule map_of_eq_NoneI[symmetric]) (auto split: if_splits)
  subgoal by (subst map_of_map_key_inverse_fun_eq[where g="\<lambda>k. if k < b then k else k - i"]) auto
  done

lemma compute_higherPowers[code]: "higherPowers n i (Pm_fmap xs) = Pm_fmap (higherPowers\<^sub>f n i xs)"
  by (rule poly_mapping_eqI)
    (auto simp: higherPowers\<^sub>f.rep_eq higherPowers.rep_eq fmlookup_default_def dec_above_def
      split: option.splits)

lemma compute_lowerPowers[code]: "lowerPowers n i (Pm_fmap xs) = Pm_fmap (lowerPowers\<^sub>f n i xs)"
  by (rule poly_mapping_eqI)
    (auto simp: lowerPowers\<^sub>f.rep_eq lowerPowers.rep_eq fmlookup_default_def dec_above_def
      split: option.splits)

lemma finite_nonzero_coeff: "finite {x. MPoly_Type.coeff mpoly x \<noteq> 0}"
  by transfer auto

lift_definition lowerPoly\<^sub>0::"nat \<Rightarrow> nat \<Rightarrow> ((nat\<Rightarrow>\<^sub>0nat)\<Rightarrow>\<^sub>0'a::zero) \<Rightarrow> ((nat\<Rightarrow>\<^sub>0nat)\<Rightarrow>\<^sub>0 'a)" is
  "\<lambda>b i (mp::(nat\<Rightarrow>\<^sub>0nat)\<Rightarrow>'a) mon. mp (lowerPowers b i mon)"
proof -
  fix b i and mp::"(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'a"
  assume "finite {x. mp x \<noteq> 0}"
  have "{x. mp (lowerPowers b i x) \<noteq> 0} = (lowerPowers b i -` {x. mp x \<noteq> 0})"
    (is "?set = ?vimage")
    by auto
  also 
  from finite_vimageI[OF \<open>finite _\<close> inj_lowerPowers]
  have "finite ?vimage" .
  finally show "finite ?set" .
qed

lemma higherPowers_zero[simp]: "higherPowers b i 0 = 0"
  by transfer auto

lemma keys_lowerPoly\<^sub>0: "keys (lowerPoly\<^sub>0 b i mp) = higherPowers b i ` (keys mp \<inter> {x. \<forall>j\<in>{b..<b+i}. lookup x j = 0})"
  apply (auto )
  subgoal for x
    apply (rule image_eqI[where x="lowerPowers b i x"])
     apply (auto simp: higherPowers_lowerPowers in_keys_iff lowerPoly\<^sub>0.rep_eq lowerPowers.rep_eq)
    done
  subgoal for x
    apply (auto simp: in_keys_iff lowerPoly\<^sub>0.rep_eq)
    apply (subst (asm) lowerPowers_higherPowers)
     apply auto
    done
  done


lift_definition higherPoly\<^sub>0::"nat \<Rightarrow> nat \<Rightarrow> ((nat\<Rightarrow>\<^sub>0nat)\<Rightarrow>\<^sub>0'a::zero) \<Rightarrow> ((nat\<Rightarrow>\<^sub>0nat)\<Rightarrow>\<^sub>0 'a)" is
  "\<lambda>b i (mp::(nat\<Rightarrow>\<^sub>0nat)\<Rightarrow>'a) mon.
    if (\<exists>j\<in>{b..<b+i}. lookup mon j > 0)
    then 0
    else mp (higherPowers b i mon)"
proof -
  fix b i and mp::"(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'a"
  assume "finite {x. mp x \<noteq> 0}"
  have "{x. (if \<exists>j\<in>{b..<b + i}. 0 < lookup x j then 0 else mp (higherPowers b i x)) \<noteq> 0} \<subseteq>
    insert 0 (higherPowers b i -` {x. mp x \<noteq> 0} \<inter> {x. \<forall>j\<in>{b..<b+i}. lookup x j = 0})"
    (is "?set \<subseteq> ?vimage")
    by auto
  also
  from finite_vimage_IntI[OF \<open>finite _\<close> inj_on_higherPowers, of b i]
  have "finite ?vimage" by (auto simp: Ball_def)
  finally (finite_subset) show "finite ?set" .
qed


context includes fmap.lifting begin

lift_definition lowerPoly\<^sub>f::"nat \<Rightarrow> nat \<Rightarrow> ((nat\<Rightarrow>\<^sub>0nat), 'a::zero)fmap \<Rightarrow> ((nat\<Rightarrow>\<^sub>0nat), 'a)fmap" is
  "\<lambda>b i (mp::((nat\<Rightarrow>\<^sub>0nat)\<rightharpoonup>'a)) mon::(nat\<Rightarrow>\<^sub>0nat). mp (lowerPowers b i mon)"
proof -\<comment> \<open>TODO: this is exactly the same proof as the one for \<open>lowerPoly\<^sub>0\<close>\<close>
  fix b i and mp::"(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'a option"
  assume "finite (dom mp)"
  also have "dom mp = {x. mp x \<noteq> None}" by auto
  finally have "finite {x. mp x \<noteq> None}" .
  have "(dom (\<lambda>mon. mp (lowerPowers b i mon))) = {mon. mp (lowerPowers b i mon) \<noteq> None}"
    (is "?set = _")
    by (auto split: if_splits)
  also have "\<dots> = lowerPowers b i -` {x. mp x \<noteq> None}" (is "_ = ?vimage")
    by auto
  also
  from finite_vimageI[OF \<open>finite {x. mp x \<noteq> None}\<close> inj_lowerPowers]
  have "finite ?vimage" .
  finally show "finite ?set" .
qed

lift_definition higherPoly\<^sub>f::"nat \<Rightarrow> nat \<Rightarrow> ((nat\<Rightarrow>\<^sub>0nat), 'a::zero)fmap \<Rightarrow> ((nat\<Rightarrow>\<^sub>0nat), 'a)fmap" is
  "\<lambda>b i (mp::((nat\<Rightarrow>\<^sub>0nat)\<rightharpoonup>'a)) mon::(nat\<Rightarrow>\<^sub>0nat).
    if (\<exists>j\<in>{b..<b+i}. lookup mon j > 0)
    then None
    else mp (higherPowers b i mon)"
proof -
  fix b i and mp::"(nat \<Rightarrow>\<^sub>0 nat) \<rightharpoonup> 'a"
  assume "finite (dom mp)"
  have "dom (\<lambda>x. (if \<exists>j\<in>{b..<b + i}. 0 < lookup x j then None else mp (higherPowers b i x))) \<subseteq>
    insert 0 (higherPowers b i -` (dom mp) \<inter> {x. \<forall>j\<in>{b..<b+i}. lookup x j = 0})"
    (is "?set \<subseteq> ?vimage")
    by (auto split: if_splits)
  also
  from finite_vimage_IntI[OF \<open>finite _\<close> inj_on_higherPowers, of b i]
  have "finite ?vimage" by (auto simp: Ball_def)
  finally (finite_subset) show "finite ?set" .
qed


lemma keys_lowerPowers: "keys (lowerPowers b i m) = inc_above b i ` (keys m)"
  apply safe
  subgoal for x
    apply (rule image_eqI[where x="dec_above b i x"])
     apply (auto simp: inc_above_dec_above in_keys_iff lowerPowers.rep_eq)
     apply (metis inc_above_dec_above not_less)
    by meson
  by (metis higherPowers.rep_eq higherPowers_lowerPowers in_keys_iff)


lemma keys_higherPoly\<^sub>0: "keys (higherPoly\<^sub>0 b i mp) = lowerPowers b i ` (keys mp)"
  apply (auto )
  subgoal for x
    apply (rule image_eqI[where x="higherPowers b i x"])
     apply (auto simp: lowerPowers_higherPowers in_keys_iff higherPoly\<^sub>0.rep_eq higherPowers.rep_eq)
     apply (metis atLeastLessThan_iff lowerPowers_higherPowers neq0_conv)
    by meson
  subgoal for x
    apply (auto simp: in_keys_iff higherPoly\<^sub>0.rep_eq)
     apply (simp add: lowerPowers_eq)
    by (simp add: higherPowers_lowerPowers)
  done

end

lemma inc_above_id[simp]: "n < m \<Longrightarrow> inc_above m i n = n" by (auto simp: inc_above_def)
lemma inc_above_Suc[simp]: "n \<ge> m \<Longrightarrow> inc_above m i n = n + i" by (auto simp: inc_above_def)

lemma compute_lowerPoly\<^sub>0[code]: "lowerPoly\<^sub>0 n i (Pm_fmap m) = Pm_fmap (lowerPoly\<^sub>f n i m)"
  by (auto simp: lowerPoly\<^sub>0.rep_eq fmlookup_default_def lowerPoly\<^sub>f.rep_eq
      split: option.splits
      intro!: poly_mapping_eqI)

lemma compute_higherPoly\<^sub>0[code]: "higherPoly\<^sub>0 n i (Pm_fmap m) = Pm_fmap (higherPoly\<^sub>f n i m)"
  by (auto simp: higherPoly\<^sub>0.rep_eq fmlookup_default_def higherPoly\<^sub>f.rep_eq
      split: option.splits
      intro!: poly_mapping_eqI)

lemma compute_lowerPoly\<^sub>f[code]: "lowerPoly\<^sub>f n i (fmap_of_list xs) =
  (fmap_of_list (map (\<lambda>(mon, c). (higherPowers n i mon, c))
    (filter (\<lambda>(mon, v). \<forall>j\<in>{n..<n+i}. lookup mon j = 0) xs)))"
  apply (rule sym)
  apply (rule fmap_ext)
  unfolding lowerPoly\<^sub>f.rep_eq fmlookup_of_list
  apply (subst map_of_map_key_inverse_fun_eq[where g="lowerPowers n i"])
  subgoal
    by (auto simp add: lowerPowers_higherPowers)
  subgoal by (auto simp add: higherPowers_lowerPowers)
  apply (auto simp: fmlookup_of_list lowerPoly\<^sub>f.rep_eq map_of_eq_None_iff map_of_filter_key_in
      fmdom'_fmap_of_list higherPowers.rep_eq lowerPowers.rep_eq dec_above_def
      intro!: fmap_ext)
  done

lemma compute_higherPoly\<^sub>f[code]: "higherPoly\<^sub>f n i (fmap_of_list xs) =
  fmap_of_list (filter (\<lambda>(mon, v). \<forall>j\<in>{n..<n+i}. lookup mon j = 0)
    (map (\<lambda>(mon, c). (lowerPowers n i mon, c)) xs))"
  apply (rule sym)
  apply (rule fmap_ext)
  unfolding higherPoly\<^sub>f.rep_eq fmlookup_of_list
  apply auto
  subgoal
    by (rule map_of_eq_NoneI) auto
  subgoal
    apply (subst map_of_filter_key_in)
    apply auto
    apply (subst map_of_map_key_inverse_fun_eq[where g="higherPowers n i"])
    subgoal
      by (auto simp add: higherPowers_lowerPowers)
    subgoal by (auto simp add: lowerPowers_higherPowers)
    apply (auto simp: fmlookup_of_list lowerPoly\<^sub>f.rep_eq map_of_eq_None_iff map_of_filter_key_in
        fmdom'_fmap_of_list higherPowers.rep_eq lowerPowers.rep_eq dec_above_def
        intro!: fmap_ext)
    done
  done

end

lift_definition lowerPoly::"nat \<Rightarrow> nat \<Rightarrow> 'a::zero mpoly \<Rightarrow> 'a mpoly" is lowerPoly\<^sub>0 .
lift_definition liftPoly::"nat \<Rightarrow> nat \<Rightarrow> 'a::zero mpoly \<Rightarrow> 'a mpoly" is higherPoly\<^sub>0 .

lemma coeff_lowerPoly: "MPoly_Type.coeff (lowerPoly b i mp) x = MPoly_Type.coeff mp (lowerPowers b i x)"
  by (transfer') (simp add: lowerPoly\<^sub>0.rep_eq lowerPowers.rep_eq)

lemma coeff_liftPoly: "MPoly_Type.coeff (liftPoly b i mp) x = (if (\<exists>j\<in>{b..<b+i}. lookup x j > 0)
    then 0
    else MPoly_Type.coeff mp (higherPowers b i x))"
  by (transfer') (simp add: higherPowers.rep_eq higherPoly\<^sub>0.rep_eq )

lemma monomials_lowerPoly: "monomials (lowerPoly b i mp) = higherPowers b i ` (monomials mp \<inter> {x. \<forall>j\<in>{b..<b + i}. lookup x j = 0}) "
  by transfer' (simp add: keys_lowerPoly\<^sub>0)


lemma monomials_liftPoly: "monomials (liftPoly b i mp) = lowerPowers b i ` (monomials mp) "
  using keys_higherPoly\<^sub>0
  by (simp add: keys_higherPoly\<^sub>0 liftPoly.rep_eq monomials.rep_eq) 


value [code] "lowerPoly 1 1 (1 * Var 0 + 2 * Var 2 ^ 2 + 3 * Var 3 ^ 4::int mpoly) = (Var 0 + 2 * Var 1^2 + 3 * Var 2^4::int mpoly)"
value [code] "lowerPoly 1 3 (1 * Var 0 + 2 * Var 4 ^ 2 + 3 * Var 5 ^ 4::int mpoly) = (Var 0 + 2 * Var 1^2 + 3 * Var 2^4::int mpoly)"

value [code] "liftPoly 1 3 (1 * Var 0 + 2 * Var 4 ^ 2 + 3 * Var 5 ^ 4::int mpoly) = (Var 0 + 2 * Var 7^2 + 3 * Var 8^4::int mpoly)"

fun lowerAtom :: "nat \<Rightarrow> nat \<Rightarrow> atom \<Rightarrow> atom" where
  "lowerAtom d amount (Eq p) = Eq(lowerPoly d amount p)"|
  "lowerAtom d amount (Less p) = Less(lowerPoly d amount p)"|
  "lowerAtom d amount (Leq p) = Leq(lowerPoly d amount p)"|
  "lowerAtom d amount (Neq p) = Neq(lowerPoly d amount p)"

lemma lookup_not_in_vars_eq_zero: "x \<in> monomials p \<Longrightarrow> i \<notin> vars p \<Longrightarrow> lookup x i = 0"
  by (meson degree_eq_iff varNotIn_degree)

lemma nth_dec_above:
  assumes "length xs = i" "length ys = j" "k \<notin> {i..<i+j}"
  shows "nth_default 0 (xs @ zs) (dec_above i j k) = (nth_default 0 (xs @ ys @ zs)) k"
  using assms dec_above_def nth_append add.commute
  by (smt add_diff_cancel_left add_le_cancel_left add_strict_increasing append_Nil2 atLeastLessThan_iff le_add_diff_inverse length_append length_greater_0_conv less_imp_le_nat not_less nth_default_append)

lemma insertion_lowerPoly:
  assumes i_notin: "vars p \<inter> {i..<i+j} = {}"
    and lprfx: "length prfx = i"
    and lxs: "length xs = j"
  shows "insertion (nth_default 0 (prfx@L)) (lowerPoly i j p) = insertion (nth_default 0 (prfx@xs@L)) p" (is "?lhs = ?rhs")
proof -
  have *: "monomials p \<inter> {x. \<forall>j\<in>{i..<i + j}. lookup x j = 0} = monomials p"
    using assms(1) by (auto intro: lookup_not_in_vars_eq_zero)
  then have "monomials p \<subseteq> {x. \<forall>k. i \<le> k \<and> k < i + j \<longrightarrow> lookup x k = 0}"
    by force
  have "?lhs = (\<Sum>m\<in>monomials (lowerPoly i j p). MPoly_Type.coeff (lowerPoly i j p) m * (\<Prod>k\<in>keys m. (nth_default 0 (prfx @ L)) k ^ lookup m k))"
    unfolding insertion_code ..
  also have "\<dots> = (\<Sum>m\<in>monomials p.
       MPoly_Type.coeff p m * (\<Prod>k\<in>keys m. (nth_default 0 (prfx @ xs @ L) k) ^ lookup m k))"
  proof (rule sum.reindex_cong)
    note inj_on_higherPowers[of i j]
    moreover note \<open>monomials p \<subseteq> _\<close>
    ultimately show "inj_on (higherPowers i j) (monomials p)"
      by (rule inj_on_subset)
  next
    show "monomials (lowerPoly i j p) = higherPowers i j ` monomials p"
      unfolding monomials_lowerPoly * ..
  next
    fix m
    assume m: "m \<in> monomials p"
    from m \<open>monomials p \<subseteq> _\<close> have "keys m \<subseteq> {x. x \<notin> {i..<i + j}}"
      by auto
    then have "lookup m k = 0" if "i \<le> k" "k < i + j" for k
      using that by (auto simp: in_keys_iff)
    then have "lowerPowers i j (higherPowers i j m) = m"
      by (rule lowerPowers_higherPowers)
    then have "MPoly_Type.coeff (lowerPoly i j p) (higherPowers i j m) = MPoly_Type.coeff p m"
      unfolding coeff_lowerPoly by simp
    moreover
    have "(\<Prod>k\<in>keys (higherPowers i j m). (nth_default 0 (prfx @ L)) k ^ lookup (higherPowers i j m) k) = 
      (\<Prod>k\<in>keys m. (nth_default 0 (prfx @ xs @ L)) k ^ lookup m k)"
    proof (rule prod.reindex_cong)
      show "keys (higherPowers i j m) = dec_above i j ` keys m"
        unfolding keys_higherPowers using \<open>keys m \<subseteq> _\<close> by auto
    next
      from inj_on_dec_above[of i j]
      show "inj_on (dec_above i j) (keys m)"
        by (rule inj_on_subset) (use \<open>keys m \<subseteq> _\<close> in auto)
    next
      fix k assume k: "k \<in> keys m"
      from k \<open>keys m \<subseteq> _\<close> have "k \<notin> {i..<i+j}" by auto
      from k \<open>keys m \<subseteq> _\<close>
      have "inc_above i j (dec_above i j k) = k"
        by (subst inc_above_dec_above) auto
      then have "lookup (higherPowers i j m) (dec_above i j k) = lookup m k"
        unfolding higherPowers.rep_eq by simp
      moreover have "nth_default 0 (prfx @ L) (dec_above i j k) = (nth_default 0 (prfx @ xs @ L)) k"
        apply (rule nth_dec_above)
        using assms \<open>k \<notin> _\<close>
        by auto
      ultimately
      show "((nth_default 0 (prfx @ L)) (dec_above i j k)) ^ lookup (higherPowers i j m) (dec_above i j k) = ((nth_default 0 (prfx @ xs @ L)) k) ^ lookup m k"
        by simp
    qed
    ultimately
    show "MPoly_Type.coeff (lowerPoly i j p) (higherPowers i j m) * (\<Prod>k\<in>keys (higherPowers i j m). (nth_default 0(prfx @ L)) k ^ lookup (higherPowers i j m) k) =
          MPoly_Type.coeff p m * (\<Prod>k\<in>keys m. (nth_default 0 (prfx @ xs @ L)) k ^ lookup m k)"
      by simp
  qed
  finally show ?thesis
    unfolding insertion_code .
qed

lemma insertion_lowerPoly1:
  assumes i_notin: "i \<notin> vars p"
    and lprfx: "length prfx = i"
  shows "insertion (nth_default 0 (prfx@x#L)) p = insertion (nth_default 0 (prfx@L)) (lowerPoly i 1 p)"
  using assms nth_default_def apply simp
  by (subst insertion_lowerPoly[where xs="[x]"]) auto

lemma insertion_lowerPoly01:
  assumes i_notin: "0 \<notin> vars p"
  shows "insertion (nth_default 0 (x#L)) p = insertion (nth_default 0 L) (lowerPoly 0 1 p)"
  using insertion_lowerPoly1[OF assms, of Nil x L]
  by simp

lemma aEval_lowerAtom : "(freeIn 0 (Atom A)) \<Longrightarrow> (aEval A (x#L) = aEval (lowerAtom 0 1 A) L)"
  by (cases A) (simp_all add:insertion_lowerPoly01)


fun map_fm_binders :: "(atom \<Rightarrow> nat \<Rightarrow> atom) \<Rightarrow> atom fm \<Rightarrow> nat \<Rightarrow> atom fm" where
  "map_fm_binders f TrueF n = TrueF"|
  "map_fm_binders f FalseF n = FalseF"|
  "map_fm_binders f (Atom \<phi>) n = Atom (f \<phi> n)"|
  "map_fm_binders f (And \<phi> \<psi>) n = And (map_fm_binders f \<phi> n) (map_fm_binders f \<psi> n)"|
  "map_fm_binders f (Or \<phi> \<psi>) n = Or (map_fm_binders f \<phi> n) (map_fm_binders f \<psi> n)"|
  "map_fm_binders f (ExQ \<phi>) n = ExQ(map_fm_binders f \<phi> (n+1))"|
  "map_fm_binders f (AllQ \<phi>) n = AllQ(map_fm_binders f \<phi> (n+1))"|
  "map_fm_binders f (AllN i \<phi>) n = AllN i (map_fm_binders f \<phi> (n+i))"|
  "map_fm_binders f (ExN i \<phi>) n = ExN i (map_fm_binders f \<phi> (n+i))"|
  "map_fm_binders f (Neg \<phi>) n = Neg(map_fm_binders f \<phi> n)"



fun lowerFm :: "nat \<Rightarrow> nat \<Rightarrow> atom fm \<Rightarrow> atom fm" where
  "lowerFm d amount f = map_fm_binders (\<lambda>a. \<lambda>x. lowerAtom (d+x) amount a) f 0"

fun delete_nth :: "nat \<Rightarrow> real list \<Rightarrow> real list" where
  "delete_nth n xs = take n xs @ drop n xs"

lemma eval_lowerFm_helper :
  assumes "freeIn i F"
  assumes "length init = i"
  shows "eval (lowerFm i 1 F) (init @xs) = eval F (init@[x]@xs)"
  using assms
proof(induction F arbitrary : i init)
  case TrueF
  then show ?case by simp
next
  case FalseF
  then show ?case by simp
next
  case (Atom A)
  then show ?case apply(cases A) by (simp_all add: insertion_lowerPoly1)
next
  case (And F1 F2)
  then show ?case by auto
next
  case (Or F1 F2)
  then show ?case by auto
next
  case (Neg F)
  then show ?case by simp
next
  case (ExQ F)
  have map: "\<And>y. (map_fm_binders (\<lambda>a x. lowerAtom (i + x) 1 a) F (y + 1)) = (map_fm_binders (\<lambda>a x. lowerAtom (i + 1 + x) 1 a) F y)"
    apply(induction F) by(simp_all)
  show ?case apply simp apply(rule ex_cong1)
    subgoal for xa
      using map[of 0] ExQ(1)[of "Suc i" "xa#init"] ExQ(2) ExQ(3)
      by simp
    done
next
  case (AllQ F)
  have map: "\<And>y. (map_fm_binders (\<lambda>a x. lowerAtom (i + x) 1 a) F (y + 1)) = (map_fm_binders (\<lambda>a x. lowerAtom (i + 1 + x) 1 a) F y)"
    apply(induction F) by(simp_all)
  show ?case apply simp apply(rule all_cong1)
    subgoal for xa
      using map[of 0] AllQ(1)[of "Suc i" "xa#init"] AllQ(2) AllQ(3)
      by simp
    done
next
  case (ExN x1 F)
  have map: "\<And>y. (map_fm_binders (\<lambda>a x. lowerAtom (i + x) 1 a) F (y + x1)) = (map_fm_binders (\<lambda>a x. lowerAtom (i + x1 + x) 1 a) F y)"
    apply(induction F) apply(simp_all add:add.commute add.left_commute)
    apply (metis add_Suc)
    apply (metis add_Suc)
    apply (metis add.assoc)
    by (metis add.assoc)
  show ?case apply simp apply(rule ex_cong1)
    subgoal for l
      using map[of 0] ExN(1)[of "i+x1" "l@init"] ExN(2) ExN(3)
      by auto
    done
next
  case (AllN x1 F)
  have map: "\<And>y. (map_fm_binders (\<lambda>a x. lowerAtom (i + x) 1 a) F (y + x1)) = (map_fm_binders (\<lambda>a x. lowerAtom (i + x1 + x) 1 a) F y)"
    apply(induction F) apply(simp_all add:add.commute add.left_commute)
    apply (metis add_Suc)
    apply (metis add_Suc)
    apply (metis add.assoc)
    by (metis add.assoc)
  show ?case apply simp apply(rule all_cong1)
    subgoal for l
      using map[of 0] AllN(1)[of "i+x1" "l@init"] AllN(2) AllN(3)
      by auto
    done
qed

lemma eval_lowerFm :
  assumes h : "freeIn 0 F"
  shows " \<forall>xs. (eval (lowerFm 0 1 F) xs = eval (ExQ F) xs)"
  using eval_lowerFm_helper[OF h] by simp

fun liftAtom :: "nat \<Rightarrow> nat \<Rightarrow> atom \<Rightarrow> atom" where
  "liftAtom d amount (Eq p) = Eq(liftPoly d amount p)"|
  "liftAtom d amount (Less p) = Less(liftPoly d amount p)"|
  "liftAtom d amount (Leq p) = Leq(liftPoly d amount p)"|
  "liftAtom d amount (Neq p) = Neq(liftPoly d amount p)"


fun liftFm :: "nat \<Rightarrow> nat \<Rightarrow> atom fm \<Rightarrow> atom fm" where
  "liftFm d amount f = map_fm_binders (\<lambda>a. \<lambda>x. liftAtom (d+x) amount a) f 0"

fun insert_into :: "real list \<Rightarrow> nat \<Rightarrow> real list \<Rightarrow> real list" where
  "insert_into xs n l = take n xs @ l @ drop n xs"


lemma higherPoly\<^sub>0_add : "higherPoly\<^sub>0 x y (p + q) = higherPoly\<^sub>0 x y p + higherPoly\<^sub>0 x y q"
  using poly_mapping_eq_iff[where a = "higherPoly\<^sub>0 x y (p + q)", where b = "higherPoly\<^sub>0 x y p + higherPoly\<^sub>0 x y q"]
    plus_poly_mapping.rep_eq[where x = "higherPoly\<^sub>0 x y (p + q)", where xa = "higherPoly\<^sub>0 x y p + higherPoly\<^sub>0 x y q"]
  apply (auto) 
  by (simp add: higherPoly\<^sub>0.rep_eq lookup_add poly_mapping_eqI)   

lemma liftPoly_add: "liftPoly w z (a + b) = (liftPoly w z a) + (liftPoly w z b)"
  unfolding liftPoly_def apply (auto)
proof - 
  have h1: "mapping_of (a + b) = mapping_of a + mapping_of b"
    by (simp add: plus_mpoly.rep_eq) 
  have h2: "MPoly (higherPoly\<^sub>0 w z (mapping_of a + mapping_of b)) = 
    MPoly (higherPoly\<^sub>0 w z (mapping_of a)) + MPoly (higherPoly\<^sub>0 w z (mapping_of b))"
  proof - 
    have h0a: "higherPoly\<^sub>0 w z (mapping_of a + mapping_of b) = (higherPoly\<^sub>0 w z (mapping_of a)) + (higherPoly\<^sub>0 w z (mapping_of b))"
      using higherPoly\<^sub>0_add[of w z _ _ ] by auto  
    then show ?thesis
      by (simp add: plus_mpoly.abs_eq) 
  qed
  show "MPoly (higherPoly\<^sub>0 w z (mapping_of (a + b))) =
    MPoly (higherPoly\<^sub>0 w z (mapping_of a)) +
    MPoly (higherPoly\<^sub>0 w z (mapping_of b))" using h1 h2 by auto    
qed


lemma vars_lift_add : "vars(liftPoly a b (p+q)) \<subseteq> vars(liftPoly a b (p))\<union> vars(liftPoly a b (q))"
  using liftPoly_add[of a b p q]
  using vars_add[of "liftPoly a b p" "liftPoly a b q"]
  by auto

lemma mapping_of_lift_add : "mapping_of (liftPoly x y (a + b)) = mapping_of (liftPoly x y a) + mapping_of (liftPoly x y b)"
  unfolding liftPoly.rep_eq plus_mpoly.rep_eq
  using higherPoly\<^sub>0_add .

lemma coeff_lift_add : "MPoly_Type.coeff (liftPoly x y (a + b)) m = MPoly_Type.coeff (liftPoly x y a) m + MPoly_Type.coeff (liftPoly x y b) m"
proof-
  have "MPoly_Type.coeff (liftPoly x y (a + b)) m = MPoly_Type.coeff (liftPoly x y a + liftPoly x y b) m"
    apply( simp add : mapping_of_lift_add coeff_def  ) using lookup_add
    by (simp add: plus_mpoly.rep_eq) 
  also have "... = MPoly_Type.coeff (liftPoly x y a) m + MPoly_Type.coeff (liftPoly x y b) m"
    using MPolyExtension.coeff_add[of "liftPoly x y a" "liftPoly x y b" m]  .
  finally show ?thesis
    by auto
qed

lemma lift_add : "insertion (f::nat\<Rightarrow>real)  (liftPoly 0 z (a + b)) = insertion f (liftPoly 0 z a + liftPoly 0 z b)"
  using liftPoly_add[of 0 z a b]
  by simp

lemma lower_power_zero : "lowerPowers a b 0 = 0"
  unfolding lowerPowers_def dec_above_def id_def apply auto
  unfolding Poly_Mapping.lookup_zero by auto

lemma lift_vars_monom : "vars (liftPoly i j ((MPoly_Type.monom m a)::real mpoly)) = (\<lambda>x. if x\<ge>i then x+j else x) ` vars(MPoly_Type.monom m a)" 
proof(cases "a=0")
  case True
  then show ?thesis
    by (smt MPolyExtension.monom_zero add.left_neutral add_diff_cancel_right' image_empty liftPoly_add vars_monom_single_cases)
next
  case False
  have h1: "vars (liftPoly i j (MPoly_Type.monom m a)) = keys (lowerPowers i j m)"
    unfolding liftPoly_def
    unfolding keys_lowerPowers keys_higherPoly\<^sub>0 vars_def apply auto
    apply (smt imageE keys_higherPoly\<^sub>0 keys_lowerPowers lookup_eq_zero_in_keys_contradict lookup_single_not_eq mapping_of_inverse monomials.abs_eq)
    by (metis False higherPowers.rep_eq higherPowers_lowerPowers image_eqI in_keys_iff keys_higherPoly\<^sub>0 lookup_single_eq mapping_of_inverse monomials.abs_eq)
  show ?thesis
    unfolding h1  vars_monom_keys[OF False]
      keys_lowerPowers inc_above_def by auto
qed

lemma lift_clear_vars : "vars (liftPoly i j (p::real mpoly)) \<inter> {i..<i + j} = {}"
proof(induction p rule: mpoly_induct)
  case (monom m a)
  then show ?case
    unfolding lift_vars_monom by auto
next
  case (sum p1 p2 m a)
  then show ?case
    using vars_lift_add[of i j p1 p2]
    by blast 
qed

lemma lift0: "(liftPoly i j 0) = 0"
  by (simp add: coeff_liftPoly mpoly_eq_iff)

lemma lower0: "(lowerPoly i j 0) = 0"
  by (simp add: coeff_all_0 coeff_lowerPoly)

lemma lower_lift_monom : "insertion f (MPoly_Type.monom m a :: real mpoly) = insertion f (lowerPoly i j (liftPoly i j (MPoly_Type.monom  m a)))"
proof (cases "a=0")
  case True
  show ?thesis unfolding True lift0 monom_zero lower0 ..
next
  case False
  have h1 :  "higherPowers i j ` ({lowerPowers i j m} \<inter> {x. \<forall>j\<in>{i..<i + j}. lookup x j = 0}) = {m}"
    apply (simp add: lowerPowers.rep_eq higherPowers.rep_eq)
    using higherPowers_lowerPowers .
  have higher_lower : "higherPowers i j (lowerPowers i j m) = m"
    using higherPowers_lowerPowers by blast 
  show ?thesis using False
    unfolding insertion_code monomials_monom apply auto
    unfolding monomials_lowerPoly monomials_liftPoly apply auto
    unfolding More_MPoly_Type.coeff_monom  h1 apply auto
    unfolding coeff_lowerPoly coeff_liftPoly higherPowers_lowerPowers coeff_monom
    apply(cases "\<exists>ja\<in>{i..<i + j}. 0 < lookup (lowerPowers i j m) ja")
    apply auto
    by (simp add: lowerPowers_eq)
qed 


lemma lower_lift : "insertion f (p::real mpoly) = insertion f (lowerPoly i j (liftPoly i j p))"
  unfolding insertion_code proof(induction p rule: mpoly_induct)
  case (monom m a)
  then show ?case using lower_lift_monom unfolding insertion_code monomials_lowerPoly monomials_liftPoly coeff_lowerPoly coeff_liftPoly by auto
next
  case (sum p1 p2 m a)
  have h1 : "monomials p1 \<inter> monomials p2 = {}" using sum
    by (metis Int_insert_right_if0 inf_bot_right monomials_monom)
  have h4 : "monomials (lowerPoly i j (liftPoly i j (p1 + p2))) = monomials (lowerPoly i j (liftPoly i j (p1))) \<union> monomials (lowerPoly i j (liftPoly i j (p2)))"
    using monomials_lowerPoly monomials_liftPoly monomials_add_disjoint[OF h1]
    by (simp add: monomials_liftPoly monomials_lowerPoly Int_Un_distrib2 image_Un)
  have h5 : "MPoly_Type.coeff (lowerPoly i j (liftPoly i j (p1 + p2))) = MPoly_Type.coeff (lowerPoly i j (liftPoly i j (p1))) + MPoly_Type.coeff (lowerPoly i j (liftPoly i j (p2)))"
    unfolding coeff_lowerPoly coeff_liftPoly MPolyExtension.coeff_add by auto
  show ?case
    unfolding MPolyExtension.coeff_add
    unfolding h4 h5
    unfolding monomials_add_disjoint[OF h1]
    by (smt IntE coeff_eq_zero_iff disjoint_iff_not_equal finite_monomials h1 higherPowers_lowerPowers imageE monomials_liftPoly monomials_lowerPoly plus_fun_apply sum.IH(1) sum.IH(2) sum.cong sum.union_disjoint
        )
qed
lemma lift_insertion : " \<forall>init.
       length init = (i::nat) \<longrightarrow>
       (\<forall>I xs.
           (insertion (nth_default 0 (init @ xs)) (p::real mpoly)) = (insertion ((nth_default 0) (init @ I @ xs)) (liftPoly i (length I) p)))"
proof safe
  fix init I xs
  assume "i = length (init::real list)"
  then have i_len : "length init = i" by auto
  have h: "higherPoly\<^sub>0 i (length (I::real list)) (mapping_of p) \<in> UNIV"
    by simp
  have h2 : "vars (liftPoly i (length I) p) \<inter> {i..<i + length I} = {}"
    using lift_clear_vars by auto
  show "insertion ((nth_default 0) (init @ xs)) p = insertion ((nth_default 0) (init @ I @ xs)) (liftPoly (length init) (length I) p) "
    using lower_lift insertion_lowerPoly[OF h2 i_len refl, of xs] i_len by auto
qed

lemma eval_liftFm_helper :
  assumes "length init = i"
  assumes "length I = amount"
  shows "eval F (init @xs) = eval (liftFm i amount F) (init@I@xs)"
  using assms(1)
proof(induction F arbitrary: i init)
  case (Atom x)
  then show ?case
    apply(cases x) apply simp_all using lift_insertion assms Atom.prems by force+
next
  case (ExQ F)
  have map: "\<And>y. (map_fm_binders (\<lambda>a x. liftAtom (i + x) (amount) a) F (y + Suc 0)) = (map_fm_binders (\<lambda>a x. liftAtom (i + 1 + x) amount a) F y)"
    apply(induction F) by(simp_all)
  show ?case apply simp apply(rule ex_cong1)
    subgoal for x
      using map[of 0] using ExQ(1)[of "x#init" "i+1"] ExQ(2)
      by simp
    done
next
  case (AllQ F)
  have map: "\<And>y. (map_fm_binders (\<lambda>a x. liftAtom (i + x) (amount) a) F (y + Suc 0)) = (map_fm_binders (\<lambda>a x. liftAtom (i + 1 + x) amount a) F y)"
    apply(induction F) by(simp_all)
  show ?case apply simp apply(rule all_cong1)
    subgoal for x
      using map[of 0] using AllQ(1)[of "x#init" "i+1"] AllQ(2)
      by simp
    done
next
  case (ExN x1 F)
  have map: "\<And>y. (map_fm_binders (\<lambda>a x. liftAtom (i + x) (amount) a) F (y + x1)) = (map_fm_binders (\<lambda>a x. liftAtom (i + x1 + x) amount a) F y)"
    apply(induction F) apply(simp_all add: add.commute add.left_commute)
    apply (metis add_Suc)
    apply (metis add_Suc)
    apply (metis add.assoc)
    by (metis add.assoc)
  show ?case apply simp apply(rule ex_cong1)
    subgoal for l
      using map[of 0] ExN(1)[of "l@init" "i+x1"] ExN(2)
      by auto
    done
next
  case (AllN x1 F)
  have map: "\<And>y. (map_fm_binders (\<lambda>a x. liftAtom (i + x) (amount) a) F (y + x1)) = (map_fm_binders (\<lambda>a x. liftAtom (i + x1 + x) amount a) F y)"
    apply(induction F) apply(simp_all add: add.commute add.left_commute)
    apply (metis add_Suc)
    apply (metis add_Suc)
    apply (metis add.assoc)
    by (metis add.assoc)
  show ?case apply simp apply(rule all_cong1)
    subgoal for l
      using map[of 0] AllN(1)[of "l@init" "i+x1"] AllN(2)
      by auto
    done
qed auto

lemma eval_liftFm :
  assumes "length I = amount"
  assumes "length L \<ge> d"
  shows "eval F L = eval (liftFm d amount F) (insert_into L d I)"
proof -
  define init where "init = take d L"
  then have "length init = d" using assms by simp
  then have "(eval F (init @ (drop d L)) = eval (liftFm d amount F) (init @ I @ (drop d L)))"
    using eval_liftFm_helper[of init d I amount  F "(drop d L)"] assms by auto
  then show ?thesis
    unfolding insert_into.simps assms init_def by auto
qed


lemma not_in_lift : "var\<notin>vars(p::real mpoly) \<Longrightarrow> var+z\<notin>vars(liftPoly 0 z p)"
proof(induction p rule: mpoly_induct)
  case (monom m a)
  then show ?case 
    using lift_vars_monom[of 0 z m a] by auto
next
  case (sum p1 p2 m a)
  show ?case 
    using sum using vars_lift_add[of 0 z p1 p2]
      vars_add[of p1 p2]
    by (metis (no_types, lifting) Set.basic_monos(7) Un_iff monomials.rep_eq vars_add_monom)
qed

lemma lift_const : "insertion f (liftPoly 0 z (Const (C::real))) = insertion f (Const C :: real mpoly)"
  apply(cases "C=0")
  unfolding insertion_code monomials_Const coeff_Const monomials_liftPoly  apply auto
  unfolding lower_power_zero[of 0 z] lookup_zero power.power_0 comm_monoid_mult_class.prod.neutral_const coeff_liftPoly coeff_Const
  unfolding higherPowers_def by auto

lemma liftPoly_sub: "liftPoly 0 z (a - b) = (liftPoly 0 z a) - (liftPoly 0 z b)"
  unfolding liftPoly_def apply (auto)
proof - 
  have h1: "mapping_of (a - b) = mapping_of a - mapping_of b"
    by (simp add: minus_mpoly.rep_eq) 
  have h2: "MPoly (higherPoly\<^sub>0 0 z (mapping_of a - mapping_of b)) = 
    MPoly (higherPoly\<^sub>0 0 z (mapping_of a)) - MPoly (higherPoly\<^sub>0 0 z (mapping_of b))"
  proof - 
    have h0a: "higherPoly\<^sub>0 0 z (mapping_of a - mapping_of b) = (higherPoly\<^sub>0 0 z (mapping_of a)) - (higherPoly\<^sub>0 0 z (mapping_of b))"
      using poly_mapping_eq_iff[where a = "higherPoly\<^sub>0 0 z (mapping_of a - mapping_of b)", where b = "(higherPoly\<^sub>0 0 z (mapping_of a)) - (higherPoly\<^sub>0 0 z (mapping_of b))"]
        minus_poly_mapping.rep_eq[where x = "higherPoly\<^sub>0 0 z (mapping_of a - mapping_of b)", where xa = "(higherPoly\<^sub>0 0 z (mapping_of a)) - (higherPoly\<^sub>0 0 z (mapping_of b))"]
      apply (auto) 
      by (simp add: higherPoly\<^sub>0.rep_eq poly_mapping_eqI minus_poly_mapping.rep_eq)
    then show ?thesis
      by (simp add: minus_mpoly.abs_eq) 
  qed
  show "MPoly (higherPoly\<^sub>0 0 z (mapping_of (a - b))) =
    MPoly (higherPoly\<^sub>0 0 z (mapping_of a)) -
    MPoly (higherPoly\<^sub>0 0 z (mapping_of b))" using h1 h2 by auto    
qed

lemma lift_sub : "insertion (f::nat\<Rightarrow>real) (liftPoly 0 z (a - b)) = insertion f (liftPoly 0 z a - liftPoly 0 z b)"
  using liftPoly_sub[of "z" "a" "b"] by auto

lemma lift_minus : 
  assumes "insertion (f::nat \<Rightarrow> real) (liftPoly 0 z (c - Const (C::real))) = 0"
  shows "insertion f (liftPoly 0 z c) = C"
proof-
  have "insertion f (liftPoly 0 z (c - Const C)) = insertion f ((liftPoly 0 z c) - (liftPoly 0 z (Const C)))"
    by (simp add: lift_sub) 
  have "... = insertion f (liftPoly 0 z c) - (insertion f (liftPoly 0 z (Const C)))"
    using insertion_sub by auto
  also have "... = insertion f (liftPoly 0 z c) - C"
    using lift_const[of f z C] insertion_const by auto
  then show ?thesis
    using \<open>insertion f (liftPoly 0 z (c - Const C)) = insertion f (liftPoly 0 z c - liftPoly 0 z (Const C))\<close> assms calculation by auto
qed

end

lemma lift00 : "liftPoly 0 0 (a::real mpoly) = a"
  unfolding liftPoly_def apply auto
  unfolding higherPoly\<^sub>0_def apply auto
  unfolding higherPowers_def apply auto
  by (simp add: mapping_of_inverse)

end
