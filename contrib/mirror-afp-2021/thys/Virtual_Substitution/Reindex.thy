subsection "Swapping Indicies"
theory Reindex
  imports Debruijn
begin

context includes poly_mapping.lifting begin

definition "swap i j x = (if x = i then j else if x = j then i else x)"

lemma swap_swap : "swap i j (swap i j x) = x"
  unfolding swap_def by auto


lemma finite_swap_ne: "finite {x. f x \<noteq> c} \<Longrightarrow> finite {x. f (swap b i x) \<noteq> c}"
proof - 
  assume finset: "finite {x. f x \<noteq> c}"
  let ?A = "{x. f x \<noteq> c}"
  let ?B = "{x. f (swap b i x) \<noteq> c}"
  have finsubset: "finite (?A - {i, b})" using finset by auto
  have sames: "(?A - {i, b}) = (?B - {i, b})"
    unfolding swap_def by auto
  then have "finite (?B - {i, b})" 
    using finsubset by auto
  then have finBset: "finite ((?B - {i, b}) \<union> {i, b})" by auto
  then have "?B \<subseteq> ((?B - {i, b}) \<union> {i, b})" by auto
  then show ?thesis using finBset by auto
qed

lift_definition swap0::"nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow>\<^sub>0 'a) \<Rightarrow> (nat \<Rightarrow>\<^sub>0 'a::zero)"
  is "\<lambda>b i p x. p (swap b i x)::'a"
proof -
  fix b i::nat and p::"nat \<Rightarrow> 'a"
  assume "finite {x. p x \<noteq> 0}"
  then have "finite {x. p (swap b i x) \<noteq> 0}"
    by (rule finite_swap_ne)
  from _ this show "finite {x. p (swap b i x)  \<noteq> 0}"
    by (rule finite_subset) auto
qed

lemma swap0_swap0: "swap0 n i (swap0 n i x) = x"
  by transfer (force simp: swap_def)

lemma inj_swap: "inj (swap b i)"
  using swap_swap
  by (rule inj_on_inverseI)

lemma inj_swap0: "inj (swap0 b i)"
  using swap0_swap0
  by (rule inj_on_inverseI)


lemma swap0_eq: "lookup (swap0 b i p) x = lookup p (swap b i x)"
  by (simp_all add: swap0.rep_eq)

lemma eq_onp_swap : "eq_onp (\<lambda>f. finite {x. f x \<noteq> 0}) (\<lambda>x. lookup m (swap b i x))
   (\<lambda>x. lookup m (swap b i x))"
  unfolding eq_onp_def apply simp
  apply(rule finite_swap_ne)
  by auto

lemma keys_swap: "keys (swap0 b i m) = swap b i ` keys m"  
  apply safe
  subgoal for x
    unfolding swap0_def apply simp
    unfolding keys.abs_eq[OF eq_onp_swap]
    by (metis (mono_tags, lifting) Reindex.swap_swap image_eqI lookupNotIn mem_Collect_eq)
  subgoal for x y
    unfolding swap0_def apply simp
    unfolding keys.abs_eq[OF eq_onp_swap]
    by (metis (mono_tags, lifting) Reindex.swap_swap lookup_eq_zero_in_keys_contradict mem_Collect_eq)
  done


context includes fmap.lifting begin

lift_definition swap\<^sub>f::"nat \<Rightarrow> nat \<Rightarrow> (nat, 'a) fmap \<Rightarrow> (nat, 'a::zero) fmap"
  is "\<lambda>b i p x. p (swap b i x)"
proof -
  fix b i::nat and p::"nat \<Rightarrow> 'a option"
  assume "finite (dom p)"
  then have "finite {x. p x \<noteq> None}" by (simp add: dom_def)

  have "dom (\<lambda>x. p (swap b i x)) = {x. p (swap b i x) \<noteq> None}"
    by auto
  also have "finite \<dots>"
    by (rule finite_swap_ne) fact
  finally
  have "finite (dom (\<lambda>x. p (swap b i x)))" .
  from _ this
  show "finite (dom (\<lambda>x. p (swap b i x)))"
    by (rule finite_subset) (auto split: if_splits)
qed


lemma compute_swap\<^sub>f[code]: "swap\<^sub>f b i (fmap_of_list xs) =
  fmap_of_list (map (\<lambda>(k, v). (swap b i k, v)) xs)"
proof -
  have *: "map_of (map (\<lambda>(k, y). (swap b i k, y)) (xs)) x =
    map_of xs (swap b i x)"
    for x
    apply (rule map_of_map_key_inverse_fun_eq)
    unfolding swap_swap by auto
  show ?thesis
    unfolding swap\<^sub>f_def apply simp
    unfolding fmlookup_of_list
    unfolding Finite_Map.fmap_of_list.abs_eq
    using map_of_map_key_inverse_fun_eq[where f="swap b i", where g="swap b i", where xs=xs]
    unfolding swap_swap
    apply simp
    by presburger
qed

lemma compute_swap[code]: "swap0 n i (Pm_fmap xs) = Pm_fmap (swap\<^sub>f n i xs)"
  apply(rule poly_mapping_eqI)
  by  (auto simp: swap\<^sub>f.rep_eq swap0.rep_eq fmlookup_default_def swap_def
      split: option.splits)

lift_definition swapPoly\<^sub>0::"nat \<Rightarrow> nat \<Rightarrow> ((nat\<Rightarrow>\<^sub>0nat)\<Rightarrow>\<^sub>0'a::zero) \<Rightarrow> ((nat\<Rightarrow>\<^sub>0nat)\<Rightarrow>\<^sub>0 'a)" is
  "\<lambda>b i (mp::(nat\<Rightarrow>\<^sub>0nat)\<Rightarrow>'a) mon. mp (swap0 b i mon)"
proof -
  fix b i and mp::"(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'a"
  assume "finite {x. mp x \<noteq> 0}"
  have "{x. mp (swap0 b i x) \<noteq> 0} = (swap0 b i -` {x. mp x \<noteq> 0})"
    (is "?set = ?vimage")
    by auto
  also 
  from finite_vimageI[OF \<open>finite _\<close> inj_swap0]
  have "finite ?vimage" .
  finally show "finite ?set" .
qed

lemma swap_zero[simp]: "swap0 b i 0 = 0"
  by transfer auto


context includes fmap.lifting begin

lift_definition swapPoly\<^sub>f::"nat \<Rightarrow> nat \<Rightarrow> ((nat\<Rightarrow>\<^sub>0nat), 'a::zero)fmap \<Rightarrow> ((nat\<Rightarrow>\<^sub>0nat), 'a)fmap" is
  "\<lambda>b i (mp::((nat\<Rightarrow>\<^sub>0nat)\<rightharpoonup>'a)) mon::(nat\<Rightarrow>\<^sub>0nat). mp (swap0 b i mon)"
proof -\<comment> \<open>TODO: this is exactly the same proof as the one for \<open>lowerPoly\<^sub>0\<close>\<close>
  fix b i and mp::"(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'a option"
  assume "finite (dom mp)"
  also have "dom mp = {x. mp x \<noteq> None}" by auto
  finally have "finite {x. mp x \<noteq> None}" .
  have "(dom (\<lambda>mon. mp (swap0 b i mon))) = {mon. mp (swap0 b i mon) \<noteq> None}"
    (is "?set = _")
    by (auto split: if_splits)
  also have "\<dots> = swap0 b i -` {x. mp x \<noteq> None}" (is "_ = ?vimage")
    by auto
  also
  from finite_vimageI[OF \<open>finite {x. mp x \<noteq> None}\<close> inj_swap0]
  have "finite ?vimage" .
  finally show "finite ?set" .
qed


lemma keys_swap\<^sub>0: "keys (swapPoly\<^sub>0 b i mp) = swap0 b i ` (keys mp)"
  apply (auto )
  subgoal for x
    apply (rule image_eqI[where x="swap0 b i x"])
    by (auto simp: swap0_swap0 in_keys_iff swapPoly\<^sub>0.rep_eq)
  subgoal for x
    apply (auto simp: in_keys_iff swapPoly\<^sub>0.rep_eq)
    by (simp add: swap0_swap0)
  done

end

lemma compute_swapPoly\<^sub>0[code]: "swapPoly\<^sub>0 n i (Pm_fmap m) = Pm_fmap (swapPoly\<^sub>f n i m)"
  by (auto simp: swapPoly\<^sub>0.rep_eq fmlookup_default_def swapPoly\<^sub>f.rep_eq
      split: option.splits
      intro!: poly_mapping_eqI)

lemma compute_swapPoly\<^sub>f[code]: "swapPoly\<^sub>f n i (fmap_of_list xs) =
  (fmap_of_list (map (\<lambda>(mon, c). (swap0 n i mon, c))
    xs))"
  apply (rule sym)
  apply (rule fmap_ext)
  unfolding swapPoly\<^sub>f.rep_eq fmlookup_of_list
  apply (subst map_of_map_key_inverse_fun_eq[where g="swap0 n i"])
  unfolding swap0_swap0 by auto

end
end

lift_definition swap_poly::"nat \<Rightarrow> nat \<Rightarrow> 'a::zero mpoly \<Rightarrow> 'a mpoly" is swapPoly\<^sub>0 .

value "swap_poly 0 1 (Var 0 :: real mpoly)"

lemma coeff_swap_poly: "MPoly_Type.coeff (swap_poly b i mp) x = MPoly_Type.coeff mp (swap0 b i x)"
  by (transfer') (simp add: swapPoly\<^sub>0.rep_eq)

lemma monomials_swap_poly: "monomials (swap_poly b i mp) = swap0 b i ` (monomials mp) "
  by transfer' (simp add: keys_swap\<^sub>0)

fun swap_atom :: "nat \<Rightarrow> nat \<Rightarrow> atom \<Rightarrow> atom" where
  "swap_atom a b (Eq p) = Eq (swap_poly a b p)"|
  "swap_atom a b (Less p) = Less (swap_poly a b p)"|
  "swap_atom a b (Leq p) = Leq (swap_poly a b p)"|
  "swap_atom a b (Neq p) = Neq (swap_poly a b p)"

fun swap_fm :: "nat \<Rightarrow> nat \<Rightarrow> atom fm \<Rightarrow> atom fm" where
  "swap_fm a b TrueF = TrueF"|
  "swap_fm a b FalseF = FalseF"|
  "swap_fm a b (Atom At) = Atom(swap_atom a b At)"|
  "swap_fm a b (And A B) = And(swap_fm a b A)(swap_fm a b B)"|
  "swap_fm a b (Or A B) = Or(swap_fm a b A)(swap_fm a b B)"|
  "swap_fm a b (Neg A) = Neg(swap_fm a b A)"|
  "swap_fm a b (ExQ A) = ExQ(swap_fm (a+1) (b+1) A)"|
  "swap_fm a b (AllQ A) = AllQ(swap_fm (a+1) (b+1) A)"|
  "swap_fm a b (ExN i A) = ExN i (swap_fm (a+i) (b+i) A)"|
  "swap_fm a b (AllN i A) = AllN i (swap_fm (a+i) (b+i) A)"

fun swap_list :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list"where
  "swap_list i j l = l[j := nth l i, i := nth l j]"

lemma swap_list_cons: "swap_list (Suc a) (Suc b) (x # L) = x # swap_list a b L"
  by auto

lemma inj_on : "inj_on (swap0 a b) (monomials p)"
  unfolding inj_on_def
  by (metis swap0_swap0) 

lemma inj_on' : "inj_on (swap a b) (keys m)"
  unfolding inj_on_def
  by (meson Reindex.inj_swap injD)

lemma swap_list : 
  assumes  "a < length L"
  assumes "b < length L"
  shows "nth_default 0 (L[b := L ! a, a := L ! b]) (swap a b xa) = nth_default 0 L xa"
  using assms unfolding swap_def apply auto
  apply (simp_all add: nth_default_nth)
  by (simp add: nth_default_def)

lemma swap_poly : 
  assumes "length L > a"
  assumes "length L > b"
  shows "insertion (nth_default 0 L) p = insertion (nth_default 0 (swap_list a b L)) (swap_poly a b p)"
  unfolding insertion_code apply auto
  unfolding monomials.abs_eq 
  unfolding coeff_swap_poly monomials_swap_poly apply auto
  unfolding Groups_Big.comm_monoid_add_class.sum.reindex[OF inj_on] apply simp
  unfolding swap0_swap0
  unfolding keys_swap
  unfolding Groups_Big.comm_monoid_mult_class.prod.reindex[OF inj_on']
  apply simp 
  unfolding swap0_eq swap_swap swap_list[OF assms] by auto

lemma swap_fm :
  assumes "length L > a"
  assumes "length L > b"
  shows "eval F L = eval (swap_fm a b F) (swap_list a b L)"
  using assms proof(induction F arbitrary: a b L)
  case TrueF
  then show ?case by auto
next
  case FalseF
  then show ?case by auto
next
  case (Atom At)
  then show ?case apply(cases At) using swap_poly[OF Atom(1) Atom(2)] by auto
next
  case (And F1 F2)
  show ?case using And(1)[OF And(3-4)] And(2)[OF And(3-4)] by auto
next
  case (Or F1 F2)
  then show ?case using Or(1)[OF Or(3-4)] Or(2)[OF Or(3-4)] by auto
next
  case (Neg F)
  then show ?case using Neg(1)[OF Neg(2-3)] by auto
next
  case (ExQ F)
  show ?case apply simp 
    apply(rule ex_cong1)
    subgoal for x
      using ExQ(1)[of "Suc a" "x#L" "Suc b"] unfolding swap_list_cons using ExQ(2-3) by simp
    done
next
  case (AllQ F)
  then show ?case apply simp 
    apply(rule all_cong1)
    subgoal for x
      using AllQ(1)[of "Suc a" "x#L" "Suc b"] unfolding swap_list_cons using AllQ(2-3) by simp
    done
next
  case (ExN i F)
  show ?case
    apply simp
    apply(rule ex_cong1)
    subgoal for l
      using ExN(1)[of "a+i" "l@L" "b+i"]
      by (smt (verit, del_insts) ExN.prems(1) ExN.prems(2) add.commute add_diff_cancel_right' add_less_cancel_left length_append list_update_append not_add_less2 nth_append swap_list.elims) 
    done
next
  case (AllN i F)
  then show ?case
    apply simp apply(rule all_cong1)
    by (smt (z3) add.commute add_diff_cancel_right' le_add2 length_append less_diff_conv2 list_update_append not_add_less2 nth_append)
qed

lemma "eval (ExQ (ExQ F)) L = eval (ExQ (ExQ (swap_fm 0 1 F))) L"
  apply simp
  apply safe
  subgoal for i j
    apply(rule exI[where x=j])
    apply(rule exI[where x=i])
    using swap_fm[of 0 "j # i # L" "Suc 0" F]
    by simp
  subgoal for i j
    apply(rule exI[where x=j])
    apply(rule exI[where x=i])
    using swap_fm[of 0 "i # j # L" "Suc 0" F]
    by simp
  done

lemma swap_atom:
  assumes "length L > a"
  assumes "length L > b"
  shows "aEval F L = aEval (swap_atom a b F) (swap_list a b L)"
  using swap_fm[OF assms, of "Atom F"] by auto
end