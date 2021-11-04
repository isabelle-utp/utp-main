theory More_CC imports
  Constructive_Cryptography.Constructive_Cryptography
begin

section \<open>Material for Isabelle library\<close>

lemma eq_alt_conversep: "(=) = (BNF_Def.Grp UNIV id)\<inverse>\<inverse>"
  by(simp add: Grp_def fun_eq_iff)

parametric_constant 
  swap_parametric [transfer_rule]: prod.swap_def 

lemma Sigma_parametric [transfer_rule]: includes lifting_syntax shows
  "(rel_set A ===> (A ===> rel_set B) ===> rel_set (rel_prod A B)) Sigma Sigma"
  unfolding Sigma_def by transfer_prover

lemma empty_eq_Plus [simp]: "{} = A <+> B \<longleftrightarrow> A = {} \<and> B = {}"
  by auto

lemma insert_Inl_Plus [simp]: "insert (Inl x) (A <+> B) = insert x A <+> B" by auto

lemma insert_Inr_Plus [simp]: "insert (Inr x) (A <+> B) = A <+> insert x B" by auto

lemma map_sum_image_Plus [simp]: "map_sum f g ` (A <+> B) = f ` A <+> g ` B"
  by(auto intro: rev_image_eqI)

lemma Plus_subset_Plus_iff [simp]: "A <+> B \<subseteq> C <+> D \<longleftrightarrow> A \<subseteq> C \<and> B \<subseteq> D"
  by auto

lemma map_sum_eq_Inl_iff: "map_sum f g x = Inl y \<longleftrightarrow> (\<exists>x'. x = Inl x' \<and> y = f x')"
  by(cases x) auto

lemma map_sum_eq_Inr_iff: "map_sum f g x = Inr y \<longleftrightarrow> (\<exists>x'. x = Inr x' \<and> y = g x')"
  by(cases x) auto

lemma surj_map_sum: "surj (map_sum f g)" if "surj f" "surj g"
  apply(safe; simp)
  subgoal for x using that 
    by(cases x)(auto 4 3 intro: image_eqI[where x="Inl _"] image_eqI[where x="Inr _"])
  done

lemma bij_map_sumI [simp]: "bij (map_sum f g)" if "bij f" "bij g"
  using that by(clarsimp simp add: bij_def sum.inj_map surj_map_sum)

lemma inv_map_sum [simp]:
  "\<lbrakk> bij f; bij g \<rbrakk> \<Longrightarrow> inv_into UNIV (map_sum f g) = map_sum (inv_into UNIV f) (inv_into UNIV g)"
  by(rule inj_imp_inv_eq)(simp_all add: sum.map_comp sum.inj_map bij_def surj_iff sum.map_id)


context conditionally_complete_lattice begin

lemma admissible_le1I:
  "ccpo.admissible lub ord (\<lambda>x. f x \<le> y)"
  if "cont lub ord Sup (\<le>) f"
  by(rule ccpo.admissibleI)(auto simp add: that[THEN contD] intro!: cSUP_least)

lemma admissible_le1_mcont [cont_intro]:
  "ccpo.admissible lub ord (\<lambda>x. f x \<le> y)" if "mcont lub ord Sup (\<le>) f"
  using that by(simp add: admissible_le1I mcont_def)

end

lemma eq_alt_conversep2: "(=) = ((BNF_Def.Grp UNIV id)\<inverse>\<inverse>)\<inverse>\<inverse>"
  by(auto simp add: Grp_def fun_eq_iff)

lemma nn_integral_indicator_singleton1 [simp]:
  assumes [measurable]: "{y} \<in> sets M"
  shows "(\<integral>\<^sup>+x. indicator {y} x * f x \<partial>M) = emeasure M {y} * f y"
  by(simp add: mult.commute)

lemma nn_integral_indicator_singleton1' [simp]:
  assumes "{y} \<in> sets M"
  shows "(\<integral>\<^sup>+x. indicator {x} y * f x \<partial>M) = emeasure M {y} * f y"
  by(subst nn_integral_indicator_singleton1[symmetric, OF assms])(rule nn_integral_cong; simp split: split_indicator)

subsection \<open>Probabilities\<close>

lemma pmf_eq_1_iff: "pmf p x = 1 \<longleftrightarrow> p = return_pmf x" (is "?lhs = ?rhs")
proof(rule iffI)
  assume ?lhs
  have "pmf p i = 0" if "x \<noteq> i" for i
  proof(rule antisym)
    have "pmf p i + 1 \<le> pmf p i + pmf p x" using \<open>?lhs\<close> by simp
    also have "\<dots> = measure (measure_pmf p) {i, x}" using that
      by(subst measure_pmf.finite_measure_eq_sum_singleton)(simp_all add: pmf.rep_eq)
    also have "\<dots> \<le> 1" by(rule measure_pmf.subprob_measure_le_1)
    finally show "pmf p i \<le> 0" by simp
  qed(rule pmf_nonneg)
  then show ?rhs if ?lhs
    by(intro pmf_eqI)(auto simp add: that split: split_indicator)
qed simp

lemma measure_spmf_cong: "measure (measure_spmf p) A = measure (measure_spmf p) B"
  if "A \<inter> set_spmf p = B \<inter> set_spmf p"
proof -
  have "measure (measure_spmf p) A = measure (measure_spmf p) (A \<inter> set_spmf p) + measure (measure_spmf p) (A - set_spmf p)"
    by(subst measure_spmf.finite_measure_Union[symmetric])(auto intro: arg_cong2[where f=measure])
  also have "measure (measure_spmf p) (A - set_spmf p) = 0" by(simp add: measure_spmf_zero_iff)
  also have "0 = measure (measure_spmf p) (B - set_spmf p)" by(simp add: measure_spmf_zero_iff)
  also have "measure (measure_spmf p) (A \<inter> set_spmf p) + \<dots> = measure (measure_spmf p) B"
    unfolding that by(subst measure_spmf.finite_measure_Union[symmetric])(auto intro: arg_cong2[where f=measure])
  finally show ?thesis .
qed

definition weight_spmf' where "weight_spmf' = weight_spmf"
lemma weight_spmf'_parametric [transfer_rule]: "rel_fun (rel_spmf A) (=) weight_spmf' weight_spmf'"
  unfolding weight_spmf'_def by(rule weight_spmf_parametric)

lemma bind_spmf_to_nat_on:
  "bind_spmf (map_spmf (to_nat_on (set_spmf p)) p) (\<lambda>n. f (from_nat_into (set_spmf p) n)) = bind_spmf p f"
  by(simp add: bind_map_spmf cong: bind_spmf_cong)

lemma try_cond_spmf_fst:
  "try_spmf (cond_spmf_fst p x) q = (if x \<in> fst ` set_spmf p then cond_spmf_fst p x else q)"
  by (metis cond_spmf_fst_eq_return_None lossless_cond_spmf_fst try_spmf_lossless try_spmf_return_None)

lemma measure_try_spmf:
  "measure (measure_spmf (try_spmf p q)) A = measure (measure_spmf p) A + pmf p None * measure (measure_spmf q) A"
proof -
  have "emeasure (measure_spmf (try_spmf p q)) A = emeasure (measure_spmf p) A + pmf p None * emeasure (measure_spmf q) A"
    by(fold nn_integral_spmf)(simp add: spmf_try_spmf nn_integral_add ennreal_mult' nn_integral_cmult)
  then show ?thesis by(simp add: measure_spmf.emeasure_eq_measure ennreal_mult'[symmetric] ennreal_plus[symmetric] del: ennreal_plus)
qed

lemma rel_spmf_OO_trans_strong:
  "\<lbrakk> rel_spmf R p q; rel_spmf S q r \<rbrakk> \<Longrightarrow> rel_spmf (R OO eq_onp (\<lambda>x. x \<in> set_spmf q) OO S) p r"
  by(auto intro: rel_spmf_OO_trans rel_spmf_reflI simp add: eq_onp_def)

lemma mcont2mcont_spmf [cont_intro]:
  "mcont lub ord Sup (\<le>) (\<lambda>p. spmf (f p) x)"
  if "mcont lub ord lub_spmf (ord_spmf (=)) f"
  using that unfolding mcont_def
  apply safe
  subgoal by(rule monotone2monotone, rule monotone_spmf; simp)
  apply(rule contI)
  apply(subst contD[where f=f and luba=lub]; simp)
  apply(subst cont_spmf[THEN contD])
    apply(erule (2) chain_imageI[OF _ monotoneD])
   apply simp
  apply(simp add: image_image)
  done

lemma ord_spmf_try_spmf2: "ord_spmf R p (try_spmf p q)" if "rel_spmf R p p"
proof -
  have "ord_spmf R (bind_pmf p return_pmf) (try_spmf p q)" unfolding try_spmf_def
    by(rule rel_pmf_bindI[where R="rel_option R"])
       (use that in \<open>auto simp add: rel_pmf_return_pmf1 elim!: option.rel_cases\<close>)
  then show ?thesis by(simp add: bind_return_pmf')
qed

lemma ord_spmf_lossless_spmfD1:
  assumes "ord_spmf R p q"
    and "lossless_spmf p"
  shows "rel_spmf R p q"
  by (metis (no_types, lifting) assms lossless_iff_set_pmf_None option.simps(11) ord_option.cases pmf.rel_mono_strong)

lemma restrict_spmf_mono:
  "ord_spmf (=) p q \<Longrightarrow> ord_spmf (=) (p \<upharpoonleft> A) (q \<upharpoonleft> A)"
  by(auto simp add: restrict_spmf_def pmf.rel_map elim!: pmf.rel_mono_strong elim: ord_option.cases)

lemma restrict_lub_spmf:
  assumes chain: "Complete_Partial_Order.chain (ord_spmf (=)) Y"
  shows "restrict_spmf (lub_spmf Y) A = lub_spmf ((\<lambda>p. restrict_spmf p A) ` Y)" (is "?lhs = ?rhs")
proof(cases "Y = {}")
  case Y: False
  have chain': "Complete_Partial_Order.chain (ord_spmf (=)) ((\<lambda>p. p \<upharpoonleft> A) ` Y)"
    using chain by(rule chain_imageI)(auto intro: restrict_spmf_mono)
  show ?thesis by(rule spmf_eqI)(simp add: spmf_lub_spmf[OF chain'] Y image_image spmf_restrict_spmf spmf_lub_spmf[OF chain])
qed simp

lemma mono2mono_restrict_spmf [THEN spmf.mono2mono]:
  shows monotone_restrict_spmf: "monotone (ord_spmf (=)) (ord_spmf (=)) (\<lambda>p. p \<upharpoonleft> A)"
  by(rule monotoneI)(rule restrict_spmf_mono)

lemma mcont2mcont_restrict_spmf [THEN spmf.mcont2mcont, cont_intro]:
  shows  mcont_restrict_spmf: "mcont lub_spmf (ord_spmf (=)) lub_spmf (ord_spmf (=)) (\<lambda>p. restrict_spmf p A)"
  using monotone_restrict_spmf by(rule mcontI)(simp add: contI restrict_lub_spmf)

lemma ord_spmf_case_option: "ord_spmf R (case x of None \<Rightarrow> a | Some y \<Rightarrow> b y) (case x of None \<Rightarrow> a' | Some y \<Rightarrow> b' y)"
  if "ord_spmf R a a'" "\<And>y. ord_spmf R (b y) (b' y)" using that by(cases x) auto

lemma ord_spmf_map_spmfI: "ord_spmf (=) (map_spmf f p) (map_spmf f q)" if "ord_spmf (=) p q"
  using that by(auto simp add: pmf.rel_map elim!: pmf.rel_mono_strong ord_option.cases)

subsubsection \<open>Conditional probabilities\<close>

lemma mk_lossless_cond_spmf [simp]: "mk_lossless (cond_spmf p A) = cond_spmf p A"
  by(simp add: cond_spmf_alt)

context
  fixes p :: "'a pmf"
    and f :: "'a \<Rightarrow> 'b pmf"
    and A :: "'b set"
    and F :: "'a \<Rightarrow> real"
  defines "F \<equiv> \<lambda>x. pmf p x * measure (measure_pmf (f x)) A / measure (measure_pmf (bind_pmf p f)) A"
begin

definition cond_bind_pmf :: "'a pmf" where "cond_bind_pmf = embed_pmf F"

lemma cond_bind_pmf_nonneg: "F x \<ge> 0"
  by(simp add: F_def)

context assumes defined: "A \<inter> (\<Union>x\<in>set_pmf p. set_pmf (f x)) \<noteq> {}" begin

private lemma nonzero: "measure (measure_pmf (bind_pmf p f)) A > 0"
  using defined by(auto 4 3 intro: measure_pmf_posI)

lemma cond_bind_pmf_prob: "(\<integral>\<^sup>+ x. F x \<partial>count_space UNIV) = 1"
proof -
  have nonzero': "(\<integral>\<^sup>+ x. ennreal (pmf p x) * ennreal (measure_pmf.prob (f x) A) \<partial>count_space UNIV) \<noteq> 0"
    using defined by(auto simp add: nn_integral_0_iff_AE AE_count_space pmf_eq_0_set_pmf measure_pmf_zero_iff)
  have finite: "(\<integral>\<^sup>+ x. ennreal (pmf p x) * ennreal (measure_pmf.prob (f x) A) \<partial>count_space UNIV) < \<top>" (is "?lhs < _")
  proof(rule order.strict_trans1)
    show "?lhs \<le> (\<integral>\<^sup>+ x. ennreal (pmf p x) * 1 \<partial>count_space UNIV)"
      by(rule nn_integral_mono)(simp add: mult_left_le)
    show "\<dots> < \<top>" by(simp add: nn_integral_pmf_eq_1)
  qed
  have "(\<integral>\<^sup>+ x. F x \<partial>count_space UNIV) = 
    (\<Sum>\<^sup>+ x. ennreal (pmf p x * measure_pmf.prob (f x) A)) / emeasure (measure_pmf (bind_pmf p f)) A"
    using nonzero unfolding F_def measure_pmf.emeasure_eq_measure 
    by(simp add: divide_ennreal[symmetric] divide_ennreal_def nn_integral_multc)
  also have "\<dots> = 1" unfolding emeasure_bind_pmf 
    by(simp add: measure_pmf.emeasure_eq_measure nn_integral_measure_pmf ennreal_mult' nonzero' finite)
  finally show ?thesis .           
qed

lemma pmf_cond_bind_pmf: "pmf cond_bind_pmf x = F x"
  unfolding cond_bind_pmf_def by(rule pmf_embed_pmf[OF cond_bind_pmf_nonneg cond_bind_pmf_prob])

lemma set_cond_bind_pmf: "set_pmf cond_bind_pmf = {x\<in>set_pmf p. set_pmf (f x) \<inter> A \<noteq> {}}"
  unfolding cond_bind_pmf_def 
  by(subst set_embed_pmf[OF cond_bind_pmf_nonneg cond_bind_pmf_prob])
    (auto simp add: F_def pmf_eq_0_set_pmf measure_pmf_zero_iff)

lemma cond_bind_pmf: "cond_pmf (bind_pmf p f) A = bind_pmf cond_bind_pmf (\<lambda>x. cond_pmf (f x) A)"
  (is "?lhs = ?rhs")
proof(rule pmf_eqI)
  fix i
  have "ennreal (pmf ?lhs i) = ennreal (pmf ?rhs i)"
  proof(cases "i \<in> A")
    case True
    have "ennreal (pmf ?lhs i) = (\<integral>\<^sup>+ x. ennreal (pmf p x) * ennreal (pmf (f x) i) / ennreal (measure_pmf.prob (p \<bind> f) A) \<partial>count_space UNIV)"
      using True defined
      by(simp add: pmf_cond bind_UNION Int_commute divide_ennreal[symmetric] nonzero ennreal_pmf_bind)
        (simp add: divide_ennreal_def nn_integral_multc[symmetric] nn_integral_measure_pmf)
    also have "\<dots> =  (\<integral>\<^sup>+ x. ennreal (F x) * ennreal (pmf (cond_pmf (f x) A) i) \<partial>count_space UNIV)"
      using True nonzero
      apply(intro nn_integral_cong)
      subgoal for x
        by(clarsimp simp add: F_def ennreal_mult'[symmetric] divide_ennreal)
          (cases "measure_pmf.prob (f x) A = 0"; auto simp add: pmf_cond pmf_eq_0_set_pmf measure_pmf_zero_iff)
      done
    also have "\<dots> = ennreal (pmf ?rhs i)"
      by(simp add: ennreal_pmf_bind nn_integral_measure_pmf pmf_cond_bind_pmf)
    finally show ?thesis .
  next
    case False
    then show ?thesis using defined
      by(simp add: pmf_cond bind_UNION Int_commute pmf_eq_0_set_pmf set_cond_bind_pmf)
  qed 
  then show "pmf ?lhs i = pmf ?rhs i" by simp
qed

end

end


lemma cond_spmf_try1:
  "cond_spmf (try_spmf p q) A = cond_spmf p A" if "set_spmf q \<inter> A = {}"
  apply(rule spmf_eqI)
  using that
  apply(auto simp add: spmf_try_spmf measure_try_spmf measure_spmf_zero_iff)
  apply(subst (2) spmf_eq_0_set_spmf[THEN iffD2])
   apply blast
  apply simp
  apply(simp add: measure_try_spmf measure_spmf_zero_iff)
  done

lemma cond_spmf_cong: "cond_spmf p A = cond_spmf p B" if "A \<inter> set_spmf p = B \<inter> set_spmf p"
  apply(rule spmf_eqI)
  using that by(auto simp add: measure_spmf_zero_iff spmf_eq_0_set_spmf measure_spmf_cong[OF that])

lemma cond_spmf_pair_spmf:
  "cond_spmf (pair_spmf p q) (A \<times> B) = pair_spmf (cond_spmf p A) (cond_spmf q B)" (is "?lhs = ?rhs")
proof(rule spmf_eqI)
  show "spmf ?lhs i = spmf ?rhs i" for i
  proof(cases i)
    case i [simp]: (Pair a b)
    then show ?thesis by(simp add: measure_pair_spmf_times)
  qed
qed

lemma cond_spmf_pair_spmf1:
  "cond_spmf_fst (map_spmf (\<lambda>((x, s'), y). (f x, s', y)) (pair_spmf p q)) x =
   pair_spmf (cond_spmf_fst (map_spmf (\<lambda>(x, s'). (f x, s')) p) x) q" (is "?lhs = ?rhs")
  if "lossless_spmf q"
proof -
  have "?lhs = map_spmf (\<lambda>((_, s'), y). (s', y)) (cond_spmf (pair_spmf p q) ((\<lambda>((x, s'), y). (f x, s', y)) -` ({x} \<times> UNIV)))" 
    by(simp add: cond_spmf_fst_def spmf.map_comp o_def split_def)
  also have "((\<lambda>((x, s'), y). (f x, s', y)) -` ({x} \<times> UNIV)) = ((\<lambda>(x, y). (f x, y)) -` ({x} \<times> UNIV)) \<times> UNIV"
    by(auto)
  also have "map_spmf (\<lambda>((_, s'), y). (s', y)) (cond_spmf (pair_spmf p q) \<dots>) = ?rhs"
    by(simp add: cond_spmf_fst_def cond_spmf_pair_spmf that spmf.map_comp pair_map_spmf1 apfst_def map_prod_def split_def)
  finally show ?thesis .
qed

lemma try_cond_spmf: "try_spmf (cond_spmf p A) q = (if set_spmf p \<inter> A \<noteq> {} then cond_spmf p A else q)"
  apply(clarsimp simp add: cond_spmf_def lossless_iff_set_pmf_None intro!: try_spmf_lossless)
  apply(subst (asm) set_cond_pmf)
   apply(auto simp add: in_set_spmf)
  done

lemma cond_spmf_try2:
  "cond_spmf (try_spmf p q) A = (if lossless_spmf p then return_pmf None else cond_spmf q A)" if "set_spmf p \<inter> A = {}"
  apply(rule spmf_eqI)
  using that
  apply(auto simp add: spmf_try_spmf measure_try_spmf measure_spmf_zero_iff lossless_iff_pmf_None)
  apply(subst spmf_eq_0_set_spmf[THEN iffD2])
   apply blast
  apply(simp add: measure_spmf_zero_iff[THEN iffD2])
  done


definition cond_bind_spmf :: "'a spmf \<Rightarrow> ('a \<Rightarrow> 'b spmf) \<Rightarrow> 'b set \<Rightarrow> 'a spmf" where 
  "cond_bind_spmf p f A = 
   (if \<exists>x\<in>set_spmf p. set_spmf (f x) \<inter> A \<noteq> {} then 
     cond_bind_pmf p (\<lambda>x. case x of None \<Rightarrow> return_pmf None | Some x \<Rightarrow> f x) (Some ` A)
    else return_pmf None)"

context begin

private lemma defined: "\<lbrakk> y \<in> set_spmf (f x); y \<in> A; x \<in> set_spmf p \<rbrakk> 
  \<Longrightarrow> Some ` A \<inter> (\<Union>x\<in>set_pmf p. set_pmf (case x of None \<Rightarrow> return_pmf None | Some x \<Rightarrow> f x)) \<noteq> {}"
  by(fastforce simp add: in_set_spmf bind_spmf_def)

lemma spmf_cond_bind_spmf [simp]:
  "spmf (cond_bind_spmf p f A) x = spmf p x * measure (measure_spmf (f x)) A / measure (measure_spmf (bind_spmf p f)) A"
  by(clarsimp simp add: cond_bind_spmf_def measure_spmf_zero_iff bind_UNION pmf_cond_bind_pmf defined split!: if_split)
     (fastforce simp add: in_set_spmf bind_spmf_def measure_measure_spmf_conv_measure_pmf)+

lemma set_cond_bind_spmf [simp]:
  "set_spmf (cond_bind_spmf p f A) = {x\<in>set_spmf p. set_spmf (f x) \<inter> A \<noteq> {}}"
  by(clarsimp simp add: cond_bind_spmf_def set_spmf_def bind_UNION)
    (subst set_cond_bind_pmf; fastforce simp add: measure_measure_spmf_conv_measure_pmf)

lemma cond_bind_spmf: "cond_spmf (bind_spmf p f) A = bind_spmf (cond_bind_spmf p f A) (\<lambda>x. cond_spmf (f x) A)"
  by(auto simp add: cond_spmf_def bind_UNION cond_bind_spmf_def split!: if_splits)
    (fastforce split: option.splits simp add: cond_bind_pmf set_cond_bind_pmf defined in_set_spmf bind_spmf_def intro!: bind_pmf_cong[OF refl])

end

lemma cond_spmf_fst_parametric [transfer_rule]: includes lifting_syntax shows
  "(rel_spmf (rel_prod (=) B) ===> (=) ===> rel_spmf B) cond_spmf_fst cond_spmf_fst"
  apply(rule rel_funI)+
  apply(clarsimp simp add: cond_spmf_fst_def spmf_rel_map elim!: rel_spmfE)
  subgoal for x pq
    by(subst (1 2) cond_spmf_cong[where B="fst -` ({x} \<times> UNIV) \<inter> snd -` ({x} \<times> UNIV)"])
      (fastforce intro: rel_spmf_reflI)+
  done

lemma cond_spmf_fst_map_prod:
  "cond_spmf_fst (map_spmf (\<lambda>(x, y). (f x, g x y)) p) (f x) = map_spmf (g x) (cond_spmf_fst p x)"
  if "inj_on f (insert x (fst ` set_spmf p))"
proof -
  have "cond_spmf p ((\<lambda>(x, y). (f x, g x y)) -` ({f x} \<times> UNIV)) = cond_spmf p (((\<lambda>(x, y). (f x, g x y)) -` ({f x} \<times> UNIV)) \<inter> set_spmf p)"
    by(rule cond_spmf_cong) simp
  also have "((\<lambda>(x, y). (f x, g x y)) -` ({f x} \<times> UNIV)) \<inter> set_spmf p = ({x} \<times> UNIV) \<inter> set_spmf p"
    using that by(auto 4 3 dest: inj_onD intro: rev_image_eqI)
  also have "cond_spmf p \<dots> = cond_spmf p ({x} \<times> UNIV)"
    by(rule cond_spmf_cong) simp
  finally show ?thesis
    by(auto simp add: cond_spmf_fst_def spmf.map_comp o_def split_def intro: map_spmf_cong)
qed

lemma cond_spmf_fst_map_prod_inj:
  "cond_spmf_fst (map_spmf (\<lambda>(x, y). (f x, g x y)) p) (f x) =  map_spmf (g x) (cond_spmf_fst p x)"
  if "inj f"
  apply(rule cond_spmf_fst_map_prod)
  using that by(simp add: inj_on_def)

definition cond_bind_spmf_fst :: "'a spmf \<Rightarrow> ('a \<Rightarrow> 'b spmf) \<Rightarrow> 'b \<Rightarrow> 'a spmf" where
  "cond_bind_spmf_fst p f x = cond_bind_spmf p (map_spmf (\<lambda>b. (b, ())) \<circ> f) ({x} \<times> UNIV)"

lemma cond_bind_spmf_fst_map_spmf_fst:
  "cond_bind_spmf_fst p (map_spmf fst \<circ> f) x = cond_bind_spmf p f ({x} \<times> UNIV)" (is "?lhs = ?rhs")
proof -
  have [simp]: "(\<lambda>x. (fst x, ())) -` ({x} \<times> UNIV) = {x} \<times> UNIV" by auto
  have "?lhs = cond_bind_spmf p (\<lambda>x. map_spmf (\<lambda>x. (fst x, ())) (f x)) ({x} \<times> UNIV)"
    by(simp add: cond_bind_spmf_fst_def spmf.map_comp o_def)
  also have "\<dots> = ?rhs" by(rule spmf_eqI)(simp add: measure_map_spmf map_bind_spmf[unfolded o_def, symmetric])
  finally show ?thesis .
qed

lemma cond_spmf_fst_bind: "cond_spmf_fst (bind_spmf p f) x = 
  bind_spmf (cond_bind_spmf_fst p (map_spmf fst \<circ> f) x) (\<lambda>y. cond_spmf_fst (f y) x)"
  by(simp add: cond_spmf_fst_def cond_bind_spmf map_bind_spmf cond_bind_spmf_fst_map_spmf_fst)(simp add: o_def)

lemma spmf_cond_bind_spmf_fst [simp]:
  "spmf (cond_bind_spmf_fst p f x) i = spmf p i * spmf (f i) x / spmf (bind_spmf p f) x"
  by(simp add: cond_bind_spmf_fst_def)
    (auto simp add: spmf_conv_measure_spmf measure_map_spmf map_bind_spmf[symmetric] intro!: arg_cong2[where f="(/)"] arg_cong2[where f="(*)"] arg_cong2[where f="measure"])

lemma set_cond_bind_spmf_fst [simp]:
  "set_spmf (cond_bind_spmf_fst p f x) = {y \<in> set_spmf p. x \<in> set_spmf (f y)}"
  by(auto simp add: cond_bind_spmf_fst_def intro: rev_image_eqI)

lemma map_cond_spmf_fst: "map_spmf f (cond_spmf_fst p x) = cond_spmf_fst (map_spmf (apsnd f) p) x"
  by(auto simp add: cond_spmf_fst_def spmf.map_comp intro!: map_spmf_cong arg_cong2[where f="cond_spmf"])

lemma cond_spmf_fst_try1:
  "cond_spmf_fst (try_spmf p q) x = cond_spmf_fst p x" if "x \<notin> fst ` set_spmf q"
  using that
  apply(simp add: cond_spmf_fst_def)
  apply(subst cond_spmf_try1)
   apply(auto intro: rev_image_eqI)
  done

lemma cond_spmf_fst_try2:
  "cond_spmf_fst (try_spmf p q) x = (if lossless_spmf p then return_pmf None else cond_spmf_fst q x)" if "x \<notin> fst ` set_spmf p"
  using that
  apply(simp add: cond_spmf_fst_def split!: if_split)
  apply (metis cond_spmf_fst_def cond_spmf_fst_eq_return_None)
  by (metis cond_spmf_fst_def cond_spmf_try2 lossless_cond_spmf lossless_cond_spmf_fst lossless_map_spmf)

lemma cond_spmf_fst_map_inj:
  "cond_spmf_fst (map_spmf (apfst f) p) (f x) = cond_spmf_fst p x" if "inj f"
  by(auto simp add: cond_spmf_fst_def spmf.map_comp intro!: map_spmf_cong arg_cong2[where f=cond_spmf] dest: injD[OF that])

lemma cond_spmf_fst_pair_spmf1:
  "cond_spmf_fst (map_spmf (\<lambda>(x, y). (f x, g x y)) (pair_spmf p q)) a =
   bind_spmf (cond_spmf_fst (map_spmf (\<lambda>x. (f x, x)) p) a) (\<lambda>x. map_spmf (g x) (mk_lossless q))" (is "?lhs = ?rhs")
proof -
  have "(\<lambda>(x, y). (f x, g x y)) -` ({a} \<times> UNIV) = f -` {a} \<times> UNIV" by(auto)
  moreover have "(\<lambda>x. (f x, x)) -` ({a} \<times> UNIV) = f -` {a}" by auto
  ultimately show ?thesis 
    by(simp add: cond_spmf_fst_def spmf.map_comp o_def split_beta cond_spmf_pair_spmf)
      (simp add: pair_spmf_alt_def map_bind_spmf o_def map_spmf_conv_bind_spmf)
qed

lemma cond_spmf_fst_return_spmf':
  "cond_spmf_fst (return_spmf (x, y)) z = (if x = z then return_spmf y else return_pmf None)"
  by(simp add: cond_spmf_fst_def)






section \<open>Material for CryptHOL\<close>

lemma left_gpv_lift_spmf [simp]: "left_gpv (lift_spmf p) = lift_spmf p"
  by(rule gpv.expand)(simp add: spmf.map_comp o_def)

lemma right_gpv_lift_spmf [simp]: "right_gpv (lift_spmf p) = lift_spmf p"
  by(rule gpv.expand)(simp add: spmf.map_comp o_def)

lemma map'_lift_spmf: "map_gpv' f g h (lift_spmf p) = lift_spmf (map_spmf f p)"
  by(rule gpv.expand)(simp add: gpv.map_sel spmf.map_comp o_def)

lemma in_set_sample_uniform [simp]: "x \<in> set_spmf (sample_uniform n) \<longleftrightarrow> x < n"
  by(simp add: sample_uniform_def)

lemma (in cyclic_group) inj_on_generator_iff [simp]: "\<lbrakk> x < order G; y < order G \<rbrakk> \<Longrightarrow> \<^bold>g [^] x = \<^bold>g [^] y \<longleftrightarrow> x = y"
  using inj_on_generator by(auto simp add: inj_on_def)

lemma map_\<I>_bot [simp]: "map_\<I> f g \<bottom> = \<bottom>"
  unfolding bot_\<I>_def map_\<I>_\<I>_uniform by simp

lemma map_\<I>_Inr_plus [simp]: "map_\<I> Inr f (\<I>1 \<oplus>\<^sub>\<I> \<I>2) = map_\<I> id (f \<circ> Inr) \<I>2"
  by(rule \<I>_eqI) auto

lemma interaction_bound_map_gpv'_le:
  defines "ib \<equiv> interaction_bound" 
  shows "interaction_bound consider (map_gpv' f g h gpv) \<le> ib (consider \<circ> g) gpv"
proof(induction arbitrary: gpv rule: interaction_bound_fixp_induct)
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step interaction_bound')
  show ?case unfolding ib_def
    by(subst interaction_bound.simps)
      (auto simp add: image_comp ib_def split: generat.split intro!: SUP_mono rev_bexI step.IH[unfolded ib_def])
qed

lemma interaction_bounded_by_map_gpv' [interaction_bound]:
  assumes "interaction_bounded_by (consider \<circ> g) gpv n"
  shows "interaction_bounded_by consider (map_gpv' f g h gpv) n"
  using assms interaction_bound_map_gpv'_le[of "consider" f g h gpv] by(simp add: interaction_bounded_by.simps)

lemma map_gpv'_bind_gpv:
  "map_gpv' f g h (bind_gpv gpv F) = bind_gpv (map_gpv' id g h gpv) (\<lambda>x. map_gpv' f g h (F x))"
  by(coinduction arbitrary: gpv rule: gpv.coinduct_strong)
    (auto simp del: bind_gpv_sel' simp add: bind_gpv.sel spmf_rel_map bind_map_spmf generat.rel_map rel_fun_def intro!: rel_spmf_bind_reflI rel_spmf_reflI generat.rel_refl_strong split!: generat.split)

lemma exec_gpv_map_gpv':
  "exec_gpv callee (map_gpv' f g h gpv) s =
   map_spmf (map_prod f id) (exec_gpv (map_fun id (map_fun g (map_spmf (map_prod h id))) callee) gpv s)"
  using exec_gpv_parametric'[
    where S="(=)" and CALL="BNF_Def.Grp UNIV g" and R="conversep (BNF_Def.Grp UNIV h)" and A="BNF_Def.Grp UNIV f",
     unfolded rel_gpv''_Grp, simplified]
  apply(subst (asm) (2) conversep_eq[symmetric])
  apply(subst (asm) prod.rel_conversep)
  apply(subst (asm) (2 4) eq_alt)
  apply(subst (asm) prod.rel_Grp)
  apply simp
  apply(subst (asm) spmf_rel_conversep)
  apply(subst (asm) option.rel_Grp)
  apply(subst (asm) pmf.rel_Grp)
  apply simp
  apply(subst (asm) prod.rel_Grp)
  apply simp
  apply(subst (asm) (1 3) conversep_conversep[symmetric])
  apply(subst (asm) rel_fun_conversep)
  apply(subst (asm) rel_fun_Grp)
  apply(subst (asm) rel_fun_conversep)
  apply simp
  apply(simp add: option.rel_Grp pmf.rel_Grp fun.rel_Grp)
  apply(simp add: rel_fun_def BNF_Def.Grp_def o_def map_fun_def)
  apply(erule allE)+
  apply(drule fun_cong)
  apply(erule trans)
  apply simp                   
  done

lemma colossless_gpv_sub_gpvs:
  assumes "colossless_gpv \<I> gpv" "gpv' \<in> sub_gpvs \<I> gpv"
  shows "colossless_gpv \<I> gpv'"
using assms(2,1) by(induction)(auto dest: colossless_gpvD)

lemma pfinite_gpv_sub_gpvs:
  assumes "pfinite_gpv \<I> gpv" "gpv' \<in> sub_gpvs \<I> gpv" "\<I> \<turnstile>g gpv \<surd>"
  shows "pfinite_gpv \<I> gpv'"
  using assms(2,1,3) by(induction)(auto dest: pfinite_gpv_ContD WT_gpvD)

lemma pfinite_gpv_id_oracle [simp]: "pfinite_gpv \<I> (id_oracle s x)" if "x \<in> outs_\<I> \<I>"
  by(simp add: id_oracle_def pgen_lossless_gpv_PauseI[OF that])

subsection \<open>@{term try_gpv}\<close>

lemma plossless_gpv_try_gpvI:
  assumes "pfinite_gpv \<I> gpv"
    and "\<not> colossless_gpv \<I> gpv \<Longrightarrow> plossless_gpv \<I> gpv'"
  shows "plossless_gpv \<I> (TRY gpv ELSE gpv')"
  using assms unfolding pgen_lossless_gpv_def
  by(cases "colossless_gpv \<I> gpv")(simp cong: expectation_gpv_cong_fail, simp)

lemma WT_gpv_try_gpvI [WT_intro]:
  assumes "\<I> \<turnstile>g gpv \<surd>"
    and "\<not> colossless_gpv \<I> gpv \<Longrightarrow> \<I> \<turnstile>g gpv' \<surd>"
  shows "\<I> \<turnstile>g try_gpv gpv gpv' \<surd>"
  using assms by(coinduction arbitrary: gpv)(auto 4 4 dest: WT_gpvD colossless_gpvD split: if_split_asm)

lemma (in callee_invariant_on) exec_gpv_try_gpv:
  fixes exec_gpv1
  defines "exec_gpv1 \<equiv> exec_gpv"
  assumes WT: "\<I> \<turnstile>g gpv \<surd>"
    and pfinite: "pfinite_gpv \<I> gpv"
    and I: "I s"
    and f: "\<And>s. I s \<Longrightarrow> f (x, s) = z"
    and lossless: "\<And>s x. \<lbrakk>x \<in> outs_\<I> \<I>; I s\<rbrakk> \<Longrightarrow> lossless_spmf (callee s x)"
  shows "map_spmf f (exec_gpv callee (try_gpv gpv (Done x)) s) =
    try_spmf (map_spmf f (exec_gpv1 callee gpv s)) (return_spmf z)"
  (is "?lhs = ?rhs")
proof -
  note [[show_variants]]
  have le: "ord_spmf (=) ?lhs ?rhs" using WT I
  proof(induction arbitrary: gpv s rule: exec_gpv_fixp_induct)
    case adm show ?case by simp
    case bottom show ?case by simp
    case (step exec_gpv')
    show ?case using step.prems unfolding exec_gpv1_def
      apply(subst exec_gpv.simps)
      apply(simp add: map_spmf_bind_spmf)
      apply(subst (1 2) try_spmf_def)
      apply(simp add: map_bind_pmf bind_spmf_pmf_assoc o_def)
      apply(simp add: bind_spmf_def bind_map_pmf bind_assoc_pmf)
      apply(rule rel_pmf_bindI[where R="eq_onp (\<lambda>x. x \<in> set_pmf (the_gpv gpv))"])
       apply(rule pmf.rel_refl_strong)
       apply(simp add: eq_onp_def)
      apply(clarsimp split!: option.split generat.split simp add: bind_return_pmf f map_spmf_bind_spmf o_def eq_onp_def)
      apply(simp add: bind_spmf_def bind_assoc_pmf)
      subgoal for out c
        apply(rule rel_pmf_bindI[where R="eq_onp (\<lambda>x. x \<in> set_pmf (callee s out))"])
         apply(rule pmf.rel_refl_strong)
         apply(simp add: eq_onp_def)
        apply(clarsimp split!: option.split simp add: eq_onp_def)
        apply(simp add: in_set_spmf[symmetric])
        apply(rule spmf.leq_trans)
         apply(rule step.IH)
          apply(frule (1) WT_gpvD)
          apply(erule (1) WT_gpvD)
          apply(drule WT_callee)
          apply(erule (2) WT_calleeD)
          apply(frule (1) WT_gpvD)
         apply(erule (2) callee_invariant)
        apply(simp add: try_spmf_def exec_gpv1_def)
        done
      done
  qed

  have "lossless_spmf ?lhs" 
    apply simp
    apply(rule plossless_exec_gpv)
       apply(rule plossless_gpv_try_gpvI)
        apply(rule pfinite)
       apply simp
      apply(rule WT_gpv_try_gpvI)
       apply(simp add: WT)
      apply simp
     apply(simp add: lossless)
    apply(simp add: I)
    done
  from ord_spmf_lossless_spmfD1[OF le this] show ?thesis by(simp add: spmf_rel_eq)
qed

lemma try_gpv_bind_gen_lossless': \<comment> \<open>generalises @{thm try_gpv_bind_gen_lossless}\<close>
  assumes lossless: "gen_lossless_gpv b \<I> gpv"
    and WT1: "\<I> \<turnstile>g gpv \<surd>"
    and WT2: "\<I> \<turnstile>g gpv' \<surd>"
    and WTf: "\<And>x. x \<in> results_gpv \<I> gpv \<Longrightarrow> \<I> \<turnstile>g f x \<surd>"
  shows "eq_\<I>_gpv (=) \<I> (TRY bind_gpv gpv f ELSE gpv') (bind_gpv gpv (\<lambda>x. TRY f x ELSE gpv'))"
  using lossless WT1 WTf
proof(coinduction arbitrary: gpv)
  case (eq_\<I>_gpv gpv)
  note [simp] = spmf_rel_map generat.rel_map map_spmf_bind_spmf
    and [intro!] = rel_spmf_reflI rel_generat_reflI rel_funI
  show ?case using gen_lossless_gpvD[OF eq_\<I>_gpv(1)] WT_gpvD[OF eq_\<I>_gpv(2)] WT_gpvD[OF WT2] WT_gpvD[OF eq_\<I>_gpv(3)[rule_format, OF results_gpv.Pure]] WT2
    apply(auto simp del: bind_gpv_sel' simp add: bind_gpv.sel try_spmf_bind_spmf_lossless generat.map_comp o_def intro!: rel_spmf_bind_reflI rel_spmf_try_spmf split!: generat.split)
    apply(auto 4 4 intro!: eq_\<I>_gpv(3)[rule_format] eq_\<I>_gpv_reflI eq_\<I>_generat_reflI intro: results_gpv.IO WT_intro)
    done
qed

\<comment> \<open>We instantiate the parameter @{term b} such that it can be used as a conditional simp rule.\<close>
lemmas try_gpv_bind_lossless' = try_gpv_bind_gen_lossless'[where b=False]
  and try_gpv_bind_colossless' = try_gpv_bind_gen_lossless'[where b=True]

lemma try_gpv_bind_gpv:
   "try_gpv (bind_gpv gpv f) gpv' =
    bind_gpv (try_gpv (map_gpv Some id gpv) (Done None)) (\<lambda>x. case x of None \<Rightarrow> gpv' | Some x' \<Rightarrow> try_gpv (f x') gpv')"
  by(coinduction arbitrary: gpv rule: gpv.coinduct_strong)
    (auto simp add: rel_fun_def generat.rel_map bind_return_pmf spmf_rel_map map_bind_spmf o_def bind_gpv.sel bind_map_spmf try_spmf_def bind_spmf_def spmf.map_comp bind_map_pmf bind_assoc_pmf gpv.map_sel simp del: bind_gpv_sel' intro!: rel_pmf_bind_reflI generat.rel_refl_strong rel_spmf_reflI split!: option.split generat.split)

lemma bind_gpv_try_gpv_map_Some:
  "bind_gpv (try_gpv (map_gpv Some id gpv) (Done None)) (\<lambda>x. case x of None \<Rightarrow> Fail | Some y \<Rightarrow> f y) =
   bind_gpv gpv f"
  by(coinduction arbitrary: gpv rule: gpv.coinduct_strong)
    (auto simp add: bind_gpv.sel map_bind_spmf bind_map_spmf try_spmf_def bind_spmf_def spmf_rel_map bind_map_pmf gpv.map_sel bind_assoc_pmf bind_return_pmf generat.rel_map rel_fun_def simp del: bind_gpv_sel' intro!: rel_pmf_bind_reflI rel_spmf_reflI generat.rel_refl_strong split!: option.split generat.split)

lemma try_gpv_left_gpv:
  assumes "\<I> \<turnstile>g gpv \<surd>" and WT2: "\<I> \<turnstile>g gpv' \<surd>"
  shows "eq_\<I>_gpv (=) (\<I> \<oplus>\<^sub>\<I> \<I>') (try_gpv (left_gpv gpv) (left_gpv gpv')) (left_gpv (try_gpv gpv gpv'))"
  using assms(1)
  apply(coinduction arbitrary: gpv)
  apply(auto simp add: map_try_spmf spmf.map_comp o_def generat.map_comp spmf_rel_map intro!: rel_spmf_try_spmf rel_spmf_reflI)
  subgoal for gpv generat by(cases generat)(auto dest: WT_gpvD)
  subgoal for gpv generat using WT2
    by(cases generat)(auto 4 4 dest: WT_gpvD intro!: eq_\<I>_gpv_reflI WT_gpv_left_gpv)
  done

lemma try_gpv_right_gpv:
  assumes "\<I>' \<turnstile>g gpv \<surd>" and WT2: "\<I>' \<turnstile>g gpv' \<surd>"
  shows "eq_\<I>_gpv (=) (\<I> \<oplus>\<^sub>\<I> \<I>') (try_gpv (right_gpv gpv) (right_gpv gpv')) (right_gpv (try_gpv gpv gpv'))"
  using assms(1)
  apply(coinduction arbitrary: gpv)
  apply(auto simp add: map_try_spmf spmf.map_comp o_def generat.map_comp spmf_rel_map intro!: rel_spmf_try_spmf rel_spmf_reflI)
  subgoal for gpv generat by(cases generat)(auto dest: WT_gpvD)
  subgoal for gpv generat using WT2
    by(cases generat)(auto 4 4 dest: WT_gpvD intro!: eq_\<I>_gpv_reflI WT_gpv_right_gpv)
  done

lemma bind_try_Done_Fail: "bind_gpv (TRY gpv ELSE Done x) f = bind_gpv gpv f" if "f x = Fail"
  apply(coinduction arbitrary: gpv rule: gpv.coinduct_strong)
  apply(auto simp del: bind_gpv_sel' simp add: bind_gpv.sel map_bind_spmf bind_map_spmf try_spmf_def bind_spmf_def map_bind_pmf bind_assoc_pmf bind_map_pmf bind_return_pmf spmf.map_comp o_def that rel_fun_def intro!: rel_pmf_bind_reflI rel_spmf_reflI generat.rel_refl_strong split!: option.split generat.split)
  done


lemma inline_map_gpv':
  "inline callee (map_gpv' f g h gpv) s = 
   map_gpv (apfst f) id (inline (map_fun id (map_fun g (map_gpv (apfst h) id)) callee) gpv s)"
  using inline_parametric'[where S="(=)" and C="BNF_Def.Grp UNIV g" and R="conversep (BNF_Def.Grp UNIV h)" and A="BNF_Def.Grp UNIV f" and C'="(=)" and R'="(=)"]
  apply(subst (asm) (2 3 8) eq_alt_conversep)
  apply(subst (asm) (1 3 4 5) eq_alt)
  apply(subst (asm) (1) eq_alt_conversep2)
  apply(unfold prod.rel_conversep rel_gpv''_conversep prod.rel_Grp rel_gpv''_Grp)
  apply(force simp add: rel_fun_def Grp_def map_gpv_conv_map_gpv' map_fun_def[abs_def] o_def apfst_def)
  done

lemma interaction_bound_try_gpv:
  fixes "consider" defines "ib \<equiv> interaction_bound consider"
  shows "interaction_bound consider (try_gpv gpv gpv') \<le> ib gpv + ib gpv'"
proof(induction arbitrary: gpv gpv' rule: interaction_bound_fixp_induct)
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step interaction_bound')
  show ?case unfolding ib_def
    apply(clarsimp simp add: generat.map_comp image_image o_def case_map_generat cong del: generat.case_cong split!: if_split generat.split intro!: SUP_least)
    subgoal
      apply(subst interaction_bound.simps)
      apply simp
      apply(subst Sup_image_eadd1[symmetric])
       apply clarsimp
      apply(rule SUP_upper2)
       apply(rule rev_image_eqI)
        apply simp
       apply simp
      apply(simp add: iadd_Suc)
      apply(subst Sup_image_eadd1[symmetric])
       apply simp
      apply(rule SUP_mono)
      apply simp
      apply(rule exI)
      apply(rule step.IH[unfolded ib_def])
      done
    subgoal
      apply(subst interaction_bound.simps)
      apply simp
      apply(subst Sup_image_eadd1[symmetric])
       apply clarsimp
      apply(rule SUP_upper2)
       apply(rule rev_image_eqI)
        apply simp
       apply simp
      apply(subst Sup_image_eadd1[symmetric])
       apply simp
      apply(rule SUP_upper2)
       apply(rule rev_image_eqI)
        apply simp
       apply simp
      apply(rule step.IH[unfolded ib_def])
      done
    subgoal
      apply(subst interaction_bound.simps)
      apply simp
      apply(subst Sup_image_eadd1[symmetric])
       apply clarsimp
      apply(rule SUP_upper2)
       apply(rule rev_image_eqI)
        apply simp
       apply simp
      apply(simp add: iadd_Suc)
      apply(subst Sup_image_eadd1[symmetric])
       apply simp
      apply(rule SUP_mono)
      apply simp
      apply(rule exI)
      apply(rule step.IH[unfolded ib_def])
      done
    subgoal
      apply(subst interaction_bound.simps)
      apply simp
      apply(subst Sup_image_eadd1[symmetric])
       apply clarsimp
      apply(rule SUP_upper2)
       apply(rule rev_image_eqI)
        apply simp
       apply simp
      apply(subst Sup_image_eadd1[symmetric])
       apply simp
      apply(rule SUP_upper2)
       apply(rule rev_image_eqI)
        apply simp
       apply simp
      apply(rule step.IH[unfolded ib_def])
      done
    subgoal
      apply(subst (2) interaction_bound.simps)
      apply simp
      apply(subst Sup_image_eadd2[symmetric])
       apply clarsimp
      apply simp
      apply(rule SUP_upper2)
       apply(rule rev_image_eqI)
        apply simp
       apply simp
      apply(simp add: iadd_Suc_right)
      apply(subst Sup_image_eadd2[symmetric])
       apply clarsimp
      apply(rule SUP_mono)
      apply clarsimp
      apply(rule exI)
      apply(rule order_trans)
       apply(rule step.hyps)
      apply(rule enat_le_plus_same)
      done
    subgoal
      apply(subst (2) interaction_bound.simps)
      apply simp
      apply(subst Sup_image_eadd2[symmetric])
       apply clarsimp
      apply simp
      apply(rule SUP_upper2)
       apply(rule rev_image_eqI)
        apply simp
       apply simp
      apply(subst Sup_image_eadd2[symmetric])
       apply clarsimp
      apply(rule SUP_upper2)
       apply(rule imageI)
       apply simp
      apply(rule order_trans)
       apply(rule step.hyps)
      apply(rule enat_le_plus_same)
      done
    done
qed

lemma interaction_bounded_by_try_gpv [interaction_bound]:
  "interaction_bounded_by consider (try_gpv gpv1 gpv2) (bound1 + bound2)"
  if "interaction_bounded_by consider gpv1 bound1" "interaction_bounded_by consider gpv2 bound2"
  using that interaction_bound_try_gpv[of "consider" gpv1 gpv2]
  by(simp add: interaction_bounded_by.simps)(meson add_left_mono_trans add_right_mono le_left_mono)


subsection \<open>term \<open>gpv_stop\<close>\<close>

lemma interaction_bounded_by_gpv_stop [interaction_bound]:
  assumes "interaction_bounded_by consider gpv n"
  shows "interaction_bounded_by consider (gpv_stop gpv) n"
  using assms by(simp add: interaction_bounded_by.simps)

context includes \<I>.lifting begin

lift_definition stop_\<I> :: "('a, 'b) \<I> \<Rightarrow> ('a, 'b option) \<I>" is
  "\<lambda>resp x. if (resp x = {}) then {} else insert None (Some ` resp x)" .

lemma outs_stop_\<I> [simp]: "outs_\<I> (stop_\<I> \<I>) = outs_\<I> \<I>"
  by transfer auto

lemma responses_stop_\<I> [simp]: 
  "responses_\<I> (stop_\<I> \<I>) x = (if x \<in> outs_\<I> \<I> then insert None (Some ` responses_\<I> \<I> x) else {})" 
  by transfer auto

lemma stop_\<I>_full [simp]: "stop_\<I> \<I>_full = \<I>_full"
  by transfer(auto simp add: fun_eq_iff notin_range_Some)

lemma stop_\<I>_uniform [simp]: 
  "stop_\<I> (\<I>_uniform A B) = (if B = {} then \<bottom> else \<I>_uniform A (insert None (Some ` B)))"
  unfolding bot_\<I>_def by transfer(simp add: fun_eq_iff)

lifting_update \<I>.lifting
lifting_forget \<I>.lifting

end

lemma stop_\<I>_bot [simp]: "stop_\<I> \<bottom> = \<bottom>"
  by(simp only: bot_\<I>_def stop_\<I>_uniform)(simp)

lemma WT_gpv_stop [simp, WT_intro]: "stop_\<I> \<I> \<turnstile>g gpv_stop gpv \<surd>" if "\<I> \<turnstile>g gpv \<surd>"
  using that by(coinduction arbitrary: gpv)(auto 4 3 dest: WT_gpvD)

lemma expectation_gpv_stop:
  fixes fail and gpv :: "('a, 'b, 'c) gpv"
  assumes WT: "\<I> \<turnstile>g gpv \<surd>"
  and fail: "fail \<le> c"
  shows "expectation_gpv fail (stop_\<I> \<I>) (\<lambda>_. c) (gpv_stop gpv) = expectation_gpv fail \<I> (\<lambda>_. c) gpv" (is "?lhs = ?rhs")
proof(rule antisym)
  show "expectation_gpv fail (stop_\<I> \<I>) (\<lambda>_. c) (gpv_stop gpv) \<le> expectation_gpv fail \<I> (\<lambda>_. c) gpv"
    using WT
  proof(induction arbitrary: gpv rule: parallel_fixp_induct_1_1[OF complete_lattice_partial_function_definitions complete_lattice_partial_function_definitions expectation_gpv.mono expectation_gpv.mono expectation_gpv_def expectation_gpv_def, case_names adm bottom step])
    case adm show ?case by simp
    case bottom show ?case by simp
    case (step f g)
    then show ?case
      apply(simp add: pmf_map_spmf_None measure_spmf_return_spmf nn_integral_return)
      apply(rule disjI2 nn_integral_mono_AE)+
      apply(auto split!: generat.split simp add: image_image dest: WT_gpvD intro!: le_infI2 INF_mono)
      done
  qed

  define stop :: "('a option, 'b, 'c option) gpv \<Rightarrow> _" where "stop = expectation_gpv fail (stop_\<I> \<I>) (\<lambda>_. c)"
  show "?rhs \<le> stop (gpv_stop gpv)" using WT
  proof(induction arbitrary: gpv rule: expectation_gpv_fixp_induct)
    case adm show ?case by simp
    case bottom show ?case by simp
    case (step expectation_gpv')
    have "expectation_gpv' gpv' \<le> c" if "\<I> \<turnstile>g gpv' \<surd>" for gpv'
      using expectation_gpv_const_le[of \<I> gpv' fail c] fail step.hyps(1)[of gpv'] that
      by(simp add: max_def split: if_split_asm)
    then show ?case using step unfolding stop_def
      apply(subst expectation_gpv.simps)
      apply(simp add: pmf_map_spmf_None)
      apply(rule disjI2 nn_integral_mono_AE)+
      apply(clarsimp split!: generat.split simp add: image_image)
      subgoal by(auto 4 3 simp add: in_outs_\<I>_iff_responses_\<I> dest: WT_gpv_ContD intro: INF_lower2)
      subgoal by(auto intro!: INF_mono rev_bexI dest: WT_gpvD)
      done
  qed
qed

lemma pgen_lossless_gpv_stop:
  fixes fail and gpv :: "('a, 'b, 'c) gpv"
  assumes WT: "\<I> \<turnstile>g gpv \<surd>"
  and fail: "fail \<le> 1"
  shows "pgen_lossless_gpv fail (stop_\<I> \<I>) (gpv_stop gpv) = pgen_lossless_gpv fail \<I> gpv"
  by(simp add: pgen_lossless_gpv_def expectation_gpv_stop assms)

lemma pfinite_gpv_stop [simp]:
  "pfinite_gpv (stop_\<I> \<I>) (gpv_stop gpv) \<longleftrightarrow> pfinite_gpv \<I> gpv" if "\<I> \<turnstile>g gpv \<surd>"
  using that by(simp add: pgen_lossless_gpv_stop)

lemma plossless_gpv_stop [simp]:
  "plossless_gpv (stop_\<I> \<I>) (gpv_stop gpv) \<longleftrightarrow> plossless_gpv \<I> gpv" if "\<I> \<turnstile>g gpv \<surd>"
  using that by(simp add: pgen_lossless_gpv_stop)

lemma results_gpv_stop_SomeD: "Some x \<in> results_gpv (stop_\<I> \<I>) (gpv_stop gpv) \<Longrightarrow> x \<in> results_gpv \<I> gpv"
  by(induction gpv'\<equiv>"gpv_stop gpv" arbitrary: gpv rule: results_gpv.induct)
    (auto 4 3 intro: results_gpv.intros split: if_split_asm)

lemma Some_in_results'_gpv_gpv_stopD: "Some xy \<in> results'_gpv (gpv_stop gpv) \<Longrightarrow> xy \<in> results'_gpv gpv"
  unfolding results_gpv_\<I>_full[symmetric]
  by(rule results_gpv_stop_SomeD) simp

subsection \<open>term \<open>exception_\<I>\<close>\<close>

datatype 's exception = Fault | OK (ok: 's)

lemma inj_on_OK [simp]: "inj_on OK A"
  by(auto simp add: inj_on_def)

function join_exception :: "'a exception \<Rightarrow> 'b exception \<Rightarrow> ('a \<times> 'b) exception" where
  "join_exception Fault _ = Fault"
| "join_exception _ Fault = Fault"
| "join_exception (OK a) (OK b) = OK (a, b)"
  by pat_completeness auto
termination by lexicographic_order

primrec merge_exception :: "'a exception + 'b exception \<Rightarrow> ('a + 'b) exception" where
  "merge_exception (Inl x) = map_exception Inl x"
| "merge_exception (Inr y) = map_exception Inr y"

fun option_of_exception :: "'a exception \<Rightarrow> 'a option" where
  "option_of_exception Fault = None"
| "option_of_exception (OK x) = Some x"

fun exception_of_option :: "'a option \<Rightarrow> 'a exception" where
  "exception_of_option None = Fault"
| "exception_of_option (Some x) = OK x"


lemma option_of_exception_exception_of_option [simp]: "option_of_exception (exception_of_option x) = x"
  by(cases x) simp_all

lemma exception_of_option_option_of_exception [simp]: "exception_of_option (option_of_exception x) = x"
  by(cases x) simp_all

lemma case_exception_of_option [simp]: "case_exception f g (exception_of_option x) = case_option f g x"
  by(simp split: exception.split option.split)

lemma case_option_of_exception [simp]: "case_option f g (option_of_exception x) = case_exception f g x"
  by(simp split: exception.split option.split)

lemma surj_exception_of_option [simp]: "surj exception_of_option"
  by(rule surjI[where f="option_of_exception"])(simp)

lemma surj_option_of_exception [simp]: "surj option_of_exception"
  by(rule surjI[where f="exception_of_option"])(simp)

lemma case_map_exception [simp]: "case_exception f g (map_exception h x) = case_exception f (g \<circ> h) x"
  by(simp split: exception.split)

definition exception_\<I> :: "('a, 'b) \<I> \<Rightarrow> ('a, 'b exception) \<I>" where 
  "exception_\<I> \<I> = map_\<I> id exception_of_option (stop_\<I> \<I>)"

lemma outs_exception_\<I> [simp]: "outs_\<I> (exception_\<I> \<I>) = outs_\<I> \<I>"
  by(simp add: exception_\<I>_def)

lemma responses_exception_\<I> [simp]: 
  "responses_\<I> (exception_\<I> \<I>) x = (if x \<in> outs_\<I> \<I> then insert Fault (OK ` responses_\<I> \<I> x) else {})" 
  by(simp add: exception_\<I>_def image_image)

lemma map_\<I>_full [simp]: "map_\<I> f g \<I>_full = \<I>_uniform UNIV (range g)"
  unfolding \<I>_uniform_UNIV[symmetric] map_\<I>_\<I>_uniform by simp

lemma exception_\<I>_full [simp]: "exception_\<I> \<I>_full = \<I>_full"
  unfolding exception_\<I>_def by simp

lemma exception_\<I>_uniform [simp]: 
  "exception_\<I> (\<I>_uniform A B) = (if B = {} then \<bottom> else \<I>_uniform A (insert Fault (OK ` B)))"
  by(simp add: exception_\<I>_def image_image)

lemma option_of_exception_\<I> [simp]: "map_\<I> id option_of_exception (exception_\<I> \<I>) = stop_\<I> \<I>"
  by(simp add: exception_\<I>_def o_def id_def[symmetric])

lemma exception_of_option_\<I> [simp]: "map_\<I> id exception_of_option (stop_\<I> \<I>) = exception_\<I> \<I>"
  by(simp add: exception_\<I>_def)

subsection \<open>inline\<close>

context raw_converter_invariant begin

context
  fixes gpv :: "('a, 'call, 'ret) gpv"
  assumes gpv: "plossless_gpv \<I> gpv" "\<I> \<turnstile>g gpv \<surd>"
begin

lemma lossless_spmf_inline1:
  assumes lossless: "\<And>s x. \<lbrakk> x \<in> outs_\<I> \<I>; I s \<rbrakk> \<Longrightarrow> lossless_spmf (the_gpv (callee s x))"
    and I: "I s"
  shows "lossless_spmf (inline1 callee gpv s)"
proof -
  have "1 = expectation_gpv 0 \<I> (\<lambda>_. 1) gpv" using gpv by(simp add: pgen_lossless_gpv_def)
  also have "\<dots> \<le> weight_spmf (inline1 callee gpv s)" using gpv(2) I
  proof(induction arbitrary: gpv s rule: expectation_gpv_fixp_induct)
    case adm show ?case by simp
    case bottom show ?case by simp
    case (step expectation_gpv')
    { fix out c
      assume IO: "IO out c \<in> set_spmf (the_gpv gpv)"
      with step.prems have out: "out \<in> outs_\<I> \<I>" by(auto dest: WT_gpvD)
      from out[unfolded in_outs_\<I>_iff_responses_\<I>] obtain input where input: "input \<in> responses_\<I> \<I> out" by auto
      from out have "(\<Sqinter>r\<in>responses_\<I> \<I> out. expectation_gpv' (c r)) = \<integral>\<^sup>+ x. (\<Sqinter>r\<in>responses_\<I> \<I> out. expectation_gpv' (c r)) \<partial>measure_spmf (the_gpv (callee s out))"
        using lossless \<open>I s\<close> by(simp add: lossless_spmf_def measure_spmf.emeasure_eq_measure)
      also have "\<dots> \<le> \<integral>\<^sup>+ generat. (case generat of Pure (r, s') \<Rightarrow> weight_spmf (inline1 callee (c r) s') | _ \<Rightarrow> 1) \<partial>measure_spmf (the_gpv (callee s out))"
        apply(intro nn_integral_mono_AE)
        apply(clarsimp split!: generat.split)
        subgoal Pure
          apply(rule INF_lower2)
           apply(fastforce dest: results_callee[OF out \<open>I s\<close>, THEN subsetD, OF results_gpv.Pure])
          apply(rule step.IH)
           apply(fastforce intro: WT_gpvD[OF step.prems(1) IO] dest: results_callee[OF out \<open>I s\<close>, THEN subsetD, OF results_gpv.Pure])
          apply(fastforce dest: results_callee[OF out \<open>I s\<close>, THEN subsetD, OF results_gpv.Pure])
          done
        subgoal IO
          apply(rule INF_lower2[OF input])
          apply(rule order_trans)
           apply(rule step.hyps)
          apply(rule order_trans)
           apply(rule expectation_gpv_const_le)
           apply(rule WT_gpvD[OF step.prems(1) IO])
           apply(simp_all add: input)
          done
        done
      finally have "(\<Sqinter>r\<in>responses_\<I> \<I> out. expectation_gpv' (c r)) \<le> \<dots>" . }
    then show ?case using step.prems
      apply(subst inline1.simps)
      apply(simp add: measure_spmf.emeasure_eq_measure[symmetric])
      apply(simp add: measure_spmf_bind)
      apply(subst emeasure_bind[where N="count_space UNIV"])
         apply(simp add: space_measure_spmf)
        apply(simp add: o_def)
       apply(simp)
      apply(rule nn_integral_mono_AE)
      apply(clarsimp split!: generat.split simp add: measure_spmf_return_spmf space_measure_spmf)
      apply(simp add: measure_spmf_bind)
      apply(subst emeasure_bind[where N="count_space UNIV"])
         apply(simp add: space_measure_spmf)
        apply(simp add: o_def)
       apply(simp)
      apply (simp add: measure_spmf.emeasure_eq_measure)
      apply(subst generat.case_distrib[where h="\<lambda>x. measure (measure_spmf x) _"])
      apply(simp add: split_def measure_spmf_return_spmf space_measure_spmf measure_return cong del: generat.case_cong)
      done
  qed
  finally show ?thesis using weight_spmf_le_1[of "inline1 callee gpv s"] by(simp add: lossless_spmf_def)
qed

end

end

lemma (in raw_converter_invariant) inline1_try_gpv:
  defines "inline1' \<equiv> inline1"
  assumes WT: "\<I> \<turnstile>g gpv \<surd>"
    and pfinite: "pfinite_gpv \<I> gpv"
    and f: "\<And>s. I s \<Longrightarrow> f (x, s) = z"
    and lossless: "\<And>s x. \<lbrakk> x \<in> outs_\<I> \<I>; I s \<rbrakk> \<Longrightarrow> colossless_gpv \<I>' (callee s x)"
    and I: "I s"
  shows "map_spmf (map_sum f id) (inline1 callee (try_gpv gpv (Done x)) s) =
   try_spmf (map_spmf (map_sum f (\<lambda>(out, c, rpv). (out, c, \<lambda>input. try_gpv (rpv input) (Done x)))) (inline1' callee gpv s)) (return_spmf (Inl z))"
  (is "?lhs = ?rhs")
proof -
  have le: "ord_spmf (=) ?lhs ?rhs" using WT I
  proof(induction arbitrary: gpv s rule: inline1_fixp_induct)
    case adm show ?case by simp
    case bottom show ?case by simp
    case (step inline1'')
    show ?case using step.prems unfolding inline1'_def
      apply(subst inline1.simps)
      apply(simp add: bind_map_spmf map_bind_spmf o_def)
      apply(simp add: try_spmf_def)
      apply(subst bind_spmf_pmf_assoc)
      apply(simp add: bind_map_pmf)
      apply(subst (3) bind_spmf_def)
      apply(simp add: bind_assoc_pmf)
      apply(rule rel_pmf_bindI[where R="eq_onp (\<lambda>x. x \<in> set_pmf (the_gpv gpv))"])
       apply(rule pmf.rel_refl_strong)
       apply(simp add: eq_onp_def)
      apply(clarsimp simp add: eq_onp_def bind_return_pmf f split!: option.split generat.split)
      subgoal for out c
        apply(simp add: in_set_spmf[symmetric] bind_map_pmf map_bind_spmf)
        apply(subst option.case_distrib[where h=return_pmf, symmetric, abs_def])
        apply(fold map_pmf_def)
        apply(simp add: bind_spmf_def map_bind_pmf)
        apply(rule rel_pmf_bindI[where R="eq_onp (\<lambda>x. x \<in> set_pmf (the_gpv (callee s out)))"])
         apply(rule pmf.rel_refl_strong)
         apply(simp add: eq_onp_def)
        apply(simp add: in_set_spmf[symmetric] bind_map_pmf map_bind_spmf eq_onp_def split!: option.split generat.split)
        apply(rule spmf.leq_trans)
         apply(rule step.IH[unfolded inline1'_def])
        subgoal
          by(auto dest: results_callee[THEN subsetD, OF _ _ results_gpv.Pure, rotated -1] WT_gpvD)
        subgoal 
          by(auto dest: results_callee[THEN subsetD, OF _ _ results_gpv.Pure, rotated -1] WT_gpvD)
        apply(simp add: try_spmf_def)
        apply(subst option.case_distrib[where h=return_pmf, symmetric, abs_def])
        apply(fold map_pmf_def)
        apply simp
        done
      done
  qed
  have "lossless_spmf ?lhs" using I
    apply simp
    apply(rule lossless_spmf_inline1)
       apply(rule plossless_gpv_try_gpvI)
        apply(rule pfinite)
       apply simp
      apply(rule WT_gpv_try_gpvI)
       apply(rule WT)
      apply simp
     apply(rule colossless_gpv_lossless_spmfD[OF lossless])
      apply simp_all
    done
  from ord_spmf_lossless_spmfD1[OF le this] show ?thesis by(simp add: spmf_rel_eq)
qed
                        
lemma (in raw_converter_invariant) inline_try_gpv:
  assumes WT: "\<I> \<turnstile>g gpv \<surd>"
    and pfinite: "pfinite_gpv \<I> gpv"
    and f: "\<And>s. I s \<Longrightarrow> f (x, s) = z"
    and lossless: "\<And>s x. \<lbrakk> x \<in> outs_\<I> \<I>; I s \<rbrakk> \<Longrightarrow> colossless_gpv \<I>' (callee s x)"
    and I: "I s"
  shows "eq_\<I>_gpv (=) \<I>' (map_gpv f id (inline callee (try_gpv gpv (Done x)) s)) (try_gpv (map_gpv f id (inline callee gpv s)) (Done z))"
  (is "eq_\<I>_gpv _ _ ?lhs ?rhs")
  using WT pfinite I
proof(coinduction arbitrary: gpv s rule: eq_\<I>_gpv_coinduct_bind)
  case (eq_\<I>_gpv gpv s)
  show "?case TYPE(('ret \<times> 's) option) TYPE(('ret \<times> 's) option)" (is "rel_spmf (eq_\<I>_generat _ _ ?X) ?lhs ?rhs")
  proof -
   have "?lhs = map_spmf
           (\<lambda>x. case x of Inl rs \<Rightarrow> Pure rs | Inr (out, oracle, rpv) \<Rightarrow> IO out (\<lambda>input. 
               map_gpv f id (bind_gpv (try_gpv (map_gpv Some id (oracle input)) (Done None)) (\<lambda>xy. case xy of None \<Rightarrow> Fail | Some (x, y) \<Rightarrow> inline callee (rpv x) y))))
           (map_spmf (map_sum f id) (inline1 callee (TRY gpv ELSE Done x) s))"
      (is "_ = map_spmf ?f ?lhs2")
      by(auto simp add: gpv.map_sel inline_sel spmf.map_comp o_def bind_gpv_try_gpv_map_Some intro!: map_spmf_cong[OF refl] split: sum.split)
    also from eq_\<I>_gpv
    have "?lhs2 = TRY map_spmf (map_sum f (\<lambda>(out, c, rpv). (out, c, \<lambda>input. TRY rpv input ELSE Done x))) (inline1 callee gpv s) ELSE return_spmf (Inl z)"
      by(intro inline1_try_gpv)(auto intro: f lossless)
    also have "\<dots> = map_spmf (\<lambda>y. case y of None \<Rightarrow> Inl z | Some x' \<Rightarrow> map_sum f (\<lambda>(out, c, rpv). (out, c, \<lambda>input. try_gpv (rpv input) (Done x))) x') 
        (try_spmf (map_spmf Some (inline1 callee gpv s)) (return_spmf None))"
      (is "_ = ?lhs3") by(simp add: map_try_spmf spmf.map_comp o_def)
    also have "?rhs = map_spmf (\<lambda>y. case y of None \<Rightarrow> Pure z | Some (Inl x) \<Rightarrow> Pure (f x)
           | Some (Inr (out, oracle, rpv)) \<Rightarrow> IO out (\<lambda>input. try_gpv (map_gpv f id (bind_gpv (oracle input) (\<lambda>(x, y). inline callee (rpv x) y))) (Done z)))
       (try_spmf (map_spmf Some (inline1 callee gpv s)) (return_spmf None))"
      by(auto simp add: gpv.map_sel inline_sel spmf.map_comp o_def generat.map_comp spmf_rel_map map_try_spmf intro!: try_spmf_cong map_spmf_cong split: sum.split)
    moreover have "rel_spmf (eq_\<I>_generat (=) \<I>' ?X) (map_spmf ?f ?lhs3) \<dots>"
      apply(clarsimp simp add: gpv.map_sel inline_sel spmf.map_comp o_def generat.map_comp spmf_rel_map intro!: rel_spmf_reflI)
      apply(erule disjE)
      subgoal
        apply(clarsimp split!: generat.split sum.split simp add: map_gpv_id_bind_gpv)
        apply(subst (3) try_gpv_bind_gpv)
        apply(rule conjI)
         apply(erule WT_gpv_inline1[OF _ eq_\<I>_gpv(1,3)])
        apply(rule strip)+
        apply(rule disjI2)+
        subgoal for out rpv rpv' input
          apply(rule exI)
          apply(rule exI)
          apply(rule exI[where x="\<lambda>x y. x = y \<and> y \<in> results_gpv \<I>' (TRY map_gpv Some id (rpv input) ELSE Done None)"])
          apply(rule exI conjI refl)+
           apply(rule eq_\<I>_gpv_reflI)
            apply(simp add: eq_onp_def)
           apply(rule WT_intro)
            apply simp
            apply(erule (1) WT_gpv_inline1[OF _ eq_\<I>_gpv(1,3)])
           apply simp
          apply(rule rel_funI)
          apply(clarsimp simp add: eq_onp_def split: if_split_asm)
          subgoal
            apply(rule exI conjI refl)+
             apply(drule (2) WT_gpv_inline1(3)[OF _ eq_\<I>_gpv(1,3)])
             apply simp
            apply(frule (2) WT_gpv_inline1(3)[OF _ eq_\<I>_gpv(1,3)])
            apply(drule (2) inline1_in_sub_gpvs[OF _ _ _ eq_\<I>_gpv(1,3)])
            apply clarsimp
            apply(erule pfinite_gpv_sub_gpvs[OF eq_\<I>_gpv(2) _ eq_\<I>_gpv(1)])
            done
          subgoal
            apply(erule disjE; clarsimp)
             apply(rule exI conjI refl)+
              apply(drule (2) WT_gpv_inline1(3)[OF _ eq_\<I>_gpv(1,3)])
              apply simp
             apply(frule (2) WT_gpv_inline1(3)[OF _ eq_\<I>_gpv(1,3)])
             apply(drule (2) inline1_in_sub_gpvs[OF _ _ _ eq_\<I>_gpv(1,3)])
             apply clarsimp
             apply(erule pfinite_gpv_sub_gpvs[OF eq_\<I>_gpv(2) _ eq_\<I>_gpv(1)])
            apply(erule notE)
            apply(drule inline1_in_sub_gpvs_callee[OF _ eq_\<I>_gpv(1,3)])
            apply clarify
            apply(drule (1) bspec)
            apply(erule colossless_gpv_sub_gpvs[rotated])
            apply(rule lossless; simp)
            done
          done
        done
      subgoal by(clarsimp split: if_split_asm)
      done
    ultimately show ?thesis by(simp only:)
  qed
qed


definition cr_prod2 :: "'a \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> 'a \<times> 'c \<Rightarrow> bool" where
  "cr_prod2 x A = (\<lambda>b (a, c). A b c \<and> x = a)"

lemma cr_prod2_simps [simp]: "cr_prod2 x A a (b, c) \<longleftrightarrow> A a c \<and> x = b"
by(simp add: cr_prod2_def)

lemma cr_prod2I: "A a b \<Longrightarrow> cr_prod2 x A a (x, b)" by simp

lemma cr_prod2_Grp: "cr_prod2 x (BNF_Def.Grp A f) = BNF_Def.Grp A (\<lambda>b. (x, f b))"
by(auto simp add: Grp_def fun_eq_iff)

(* A stronger version of the existing extend_state_oracle_transfer *)
lemma extend_state_oracle_transfer': includes lifting_syntax shows
  "((S ===> C ===> rel_spmf (rel_prod R S)) ===> cr_prod2 s S ===> C ===> rel_spmf (rel_prod R (cr_prod2 s S))) (\<lambda>oracle. oracle) extend_state_oracle"
unfolding extend_state_oracle_def[abs_def]
apply(rule rel_funI)+
apply clarsimp
apply(drule (1) rel_funD)+
apply(auto simp add: spmf_rel_map split_def dest: rel_funD intro: rel_spmf_mono)
done

(* @Reza: This is a proof based on parametricity,
 using the relation cr_prod2 s (=) to fix the first component of the extended callee state to s *)

lemma exec_gpv_extend_state_oracle:
  "exec_gpv (extend_state_oracle callee) gpv (s, s') =
  map_spmf (\<lambda>(x, s''). (x, (s, s''))) (exec_gpv callee gpv s')"
  using exec_gpv_parametric'[THEN rel_funD, OF extend_state_oracle_transfer'[THEN rel_funD], of "(=)" "(=)" "(=)" callee callee "(=)" s]
  unfolding relator_eq rel_gpv''_eq
  apply(clarsimp simp add: rel_fun_def)
  apply(unfold eq_alt cr_prod2_Grp prod.rel_Grp option.rel_Grp pmf.rel_Grp)
  apply(simp add: Grp_def map_prod_def)
  apply(blast intro: sym)
  done





section \<open>Material for Constructive Crypto\<close>

lemma WT_resource_\<I>_uniform_UNIV [simp]: "\<I>_uniform A UNIV \<turnstile>res res \<surd>"
  by(coinduction arbitrary: res) auto

lemma WT_converter_of_callee_invar:
  assumes WT: "\<And>s q. \<lbrakk> q \<in> outs_\<I> \<I>; I s \<rbrakk> \<Longrightarrow> \<I>' \<turnstile>g callee s q \<surd>"
    and res: "\<And>s q r s'. \<lbrakk> (r, s') \<in> results_gpv \<I>' (callee s q); q \<in> outs_\<I> \<I>; I s  \<rbrakk> \<Longrightarrow> r \<in> responses_\<I> \<I> q \<and> I s'"
    and I: "I s"
  shows "\<I>, \<I>' \<turnstile>\<^sub>C converter_of_callee callee s \<surd>"
  using I by(coinduction arbitrary: s)(auto simp add: WT res)

lemma eq_\<I>_gpv_eq_OO:
  assumes "eq_\<I>_gpv (=) \<I> gpv gpv'" "eq_\<I>_gpv A \<I> gpv' gpv''"
  shows "eq_\<I>_gpv A \<I> gpv gpv''"
  using eq_\<I>_gpv_relcompp[THEN fun_cong, THEN fun_cong, THEN iffD2, OF relcomppI, OF assms]
  by(simp add: eq_OO)

lemma eq_\<I>_gpv_eq_OO2:
  assumes "eq_\<I>_gpv (=) \<I> gpv'' gpv'" "eq_\<I>_gpv A \<I> gpv gpv'"
  shows "eq_\<I>_gpv A \<I> gpv gpv''"
  using eq_\<I>_gpv_relcompp[where A'="conversep (=)", THEN fun_cong, THEN fun_cong, THEN iffD2, OF relcomppI, OF assms(2)] assms(1)
  unfolding eq_\<I>_gpv_conversep by(simp add: OO_eq)

lemma eq_\<I>_gpv_try_gpv_cong:
  assumes "eq_\<I>_gpv A \<I> gpv1 gpv1'"
    and "eq_\<I>_gpv A \<I> gpv2 gpv2'"
  shows "eq_\<I>_gpv A \<I> (try_gpv gpv1 gpv2) (try_gpv gpv1' gpv2')"
  using assms(1)
  apply(coinduction arbitrary: gpv1 gpv1')
  using assms(2)
  apply(fastforce simp add: spmf_rel_map intro!: rel_spmf_try_spmf dest: eq_\<I>_gpvD elim!: rel_spmf_mono_strong eq_\<I>_generat.cases)
  done

lemma eq_\<I>_gpv_map_gpv':
  assumes "eq_\<I>_gpv (BNF_Def.vimage2p f f' A) (map_\<I> g h \<I>) gpv1 gpv2"
  shows "eq_\<I>_gpv A \<I> (map_gpv' f g h gpv1) (map_gpv' f' g h gpv2)"
  using assms
proof(coinduction arbitrary: gpv1 gpv2)
  case eq_\<I>_gpv
  from this[THEN eq_\<I>_gpvD] show ?case
    apply(simp add: spmf_rel_map)
    apply(erule rel_spmf_mono)
    apply(auto 4 4 simp add: BNF_Def.vimage2p_def elim!: eq_\<I>_generat.cases)
    done
qed

lemma eq_\<I>_converter_map_converter:
  assumes "map_\<I> (inv_into UNIV f) (inv_into UNIV g) \<I>, map_\<I> f' g' \<I>' \<turnstile>\<^sub>C conv1 \<sim> conv2"
    and "inj f" "surj g"
  shows "\<I>, \<I>' \<turnstile>\<^sub>C map_converter f g f' g' conv1 \<sim> map_converter f g f' g' conv2"
  using assms(1)
proof(coinduction arbitrary: conv1 conv2)
  case eq_\<I>_converter
  from this(2) have "f q \<in> outs_\<I> (map_\<I> (inv_into UNIV f) (inv_into UNIV g) \<I>)" using assms(2) by simp
  from eq_\<I>_converter(1)[THEN eq_\<I>_converterD, OF this] show ?case using assms(2,3)
    apply simp
    apply(rule eq_\<I>_gpv_map_gpv')
    apply(simp add: BNF_Def.vimage2p_def prod.rel_map)
    apply(erule eq_\<I>_gpv_mono')
     apply(auto 4 4 simp add: eq_onp_def surj_f_inv_f)
    done
qed

lemma resource_of_oracle_run_resource: "resource_of_oracle run_resource res = res"
  by(coinduction arbitrary: res)(auto simp add: rel_fun_def spmf_rel_map intro!: rel_spmf_reflI)

lemma connect_map_gpv':
  "connect (map_gpv' f g h adv) res = map_spmf f (connect adv (map_resource g h res))"
  unfolding connect_def
  by(subst (3) resource_of_oracle_run_resource[symmetric])
    (simp add: exec_gpv_map_gpv' map_resource_resource_of_oracle spmf.map_comp exec_gpv_resource_of_oracle)

primcorec fail_resource :: "('a, 'b) resource" where
  "run_resource fail_resource = (\<lambda>_. return_pmf None)"

lemma WT_fail_resource [WT_intro]: "\<I> \<turnstile>res fail_resource \<surd>"
  by(rule WT_resourceI) simp

context fixes y :: "'b" begin

primcorec const_resource :: "('a, 'b) resource" where
  "run_resource const_resource = (\<lambda>_. map_spmf (map_prod id (\<lambda>_. const_resource)) (return_spmf (y, ())))" 

end

lemma const_resource_sel [simp]: "run_resource (const_resource y) = (\<lambda>_. return_spmf (y, const_resource y))"
  by simp

declare const_resource.sel [simp del]

lemma lossless_const_resource [simp]: "lossless_resource \<I> (const_resource y)"
  by(coinduction) simp

lemma WT_const_resource [simp]:
  "\<I> \<turnstile>res const_resource y \<surd> \<longleftrightarrow> (\<forall>x\<in>outs_\<I> \<I>. y \<in> responses_\<I> \<I> x)" (is "?lhs \<longleftrightarrow> ?rhs")
proof(intro iffI ballI)
  show "y \<in> responses_\<I> \<I> x" if ?lhs and "x \<in> outs_\<I> \<I>" for x using WT_resourceD[OF that] by auto
  show ?lhs if ?rhs using that by(coinduction)(auto)
qed

context fixes y :: "'b" begin

primcorec const_converter :: "('a, 'b, 'c, 'd) converter" where
  "run_converter const_converter = (\<lambda>_. map_gpv (map_prod id (\<lambda>_. const_converter)) id (Done (y, ())))"

end

lemma const_converter_sel [simp]: "run_converter (const_converter y) = (\<lambda>_. Done (y, const_converter y))"
  by simp

lemma attach_const_converter [simp]: "attach (const_converter y) res = const_resource y"
  by(coinduction)(simp add: rel_fun_def)

declare const_converter.sel [simp del]

lemma comp_const_converter [simp]: "comp_converter (const_converter x) conv = const_converter x"
  by(coinduction)(simp add: rel_fun_def)

lemma interaction_bounded_const_converter [simp, interaction_bound]: 
  "interaction_any_bounded_converter (const_converter Fault) bound"
  by(coinduction) simp


primcorec merge_exception_converter :: "('a, ('b + 'c) exception, 'a, 'b exception + 'c exception) converter" where
  "run_converter merge_exception_converter = 
   (\<lambda>x. map_gpv (map_prod id (\<lambda>conv. case conv of None \<Rightarrow> merge_exception_converter | Some conv' \<Rightarrow> conv')) id (
     Pause x (\<lambda>y. Done (case merge_exception y of Fault \<Rightarrow> (Fault, Some (const_converter Fault))
                              | OK y' \<Rightarrow> (OK y', None)))))"

lemma merge_exception_converter_sel [simp]:
  "run_converter merge_exception_converter x =
   Pause x (\<lambda>y. Done (case merge_exception y of Fault \<Rightarrow> (Fault, const_converter Fault) | OK y' \<Rightarrow> (OK y', merge_exception_converter)))"
  by(simp add: o_def fun_eq_iff split: exception.split)

declare merge_exception_converter.sel[simp del]

lemma plossless_const_converter[simp]: "plossless_converter \<I> \<I>' (const_converter x)"
  by(coinduction) auto

lemma plossless_merge_exception_converter [simp]:
  "plossless_converter (exception_\<I> (\<I> \<oplus>\<^sub>\<I> \<I>')) (exception_\<I> \<I> \<oplus>\<^sub>\<I> exception_\<I> \<I>') merge_exception_converter"
  by(coinduction) auto

lemma WT_const_converter [WT_intro, simp]:
  "\<I>, \<I>' \<turnstile>\<^sub>C const_converter x \<surd>" if "\<forall>q \<in> outs_\<I> \<I>. x \<in> responses_\<I> \<I> q"
  by(coinduction)(auto simp add: that)

lemma WT_merge_exception_converter [WT_intro, simp]: 
  "exception_\<I> (\<I>1' \<oplus>\<^sub>\<I> \<I>2'), exception_\<I> \<I>1' \<oplus>\<^sub>\<I> exception_\<I> \<I>2' \<turnstile>\<^sub>C merge_exception_converter \<surd>"
  by(coinduction) auto

lemma inline_left_gpv_merge_exception_converter:
  "bind_gpv (inline run_converter (map_gpv' id id option_of_exception (gpv_stop (left_gpv gpv))) merge_exception_converter) (\<lambda>(x, conv'). case x of None \<Rightarrow> Fail | Some x' \<Rightarrow> Done (x, conv')) =
   bind_gpv (left_gpv (map_gpv' id id option_of_exception (gpv_stop gpv))) (\<lambda>x. case x of None \<Rightarrow> Fail | Some x' \<Rightarrow> Done (x, merge_exception_converter))"
  apply(coinduction arbitrary: gpv rule: gpv.coinduct_strong)
  apply(simp add: bind_gpv.sel inline_sel map_bind_spmf bind_map_spmf del: bind_gpv_sel')
  apply(subst inline1_unfold)
  apply(clarsimp simp add: bind_map_spmf intro!: rel_spmf_bind_reflI simp add: generat.map_comp case_map_generat o_def split!: generat.split intro!: rel_funI)
  subgoal for gpv out c input by(cases input; auto split!: exception.split)
  done

lemma inline_right_gpv_merge_exception_converter:
  "bind_gpv (inline run_converter (map_gpv' id id option_of_exception (gpv_stop (right_gpv gpv))) merge_exception_converter) (\<lambda>(x, conv'). case x of None \<Rightarrow> Fail | Some x' \<Rightarrow> Done (x, conv')) =
   bind_gpv (right_gpv (map_gpv' id id option_of_exception (gpv_stop gpv))) (\<lambda>x. case x of None \<Rightarrow> Fail | Some x' \<Rightarrow> Done (x, merge_exception_converter))"
  apply(coinduction arbitrary: gpv rule: gpv.coinduct_strong)
  apply(simp add: bind_gpv.sel inline_sel map_bind_spmf bind_map_spmf del: bind_gpv_sel')
  apply(subst inline1_unfold)
  apply(clarsimp simp add: bind_map_spmf intro!: rel_spmf_bind_reflI simp add: generat.map_comp case_map_generat o_def split!: generat.split intro!: rel_funI)
  subgoal for gpv out c input by(cases input; auto split!: exception.split)
  done

subsection \<open>@{theory Constructive_Cryptography.Wiring}\<close>

abbreviation (input) 
  id_wiring :: "('a, 'b, 'a, 'b) wiring" ("1\<^sub>w")
  where
    "id_wiring \<equiv> (id, id)"

definition 
  swap_lassocr\<^sub>w :: "('a + 'b + 'c, 'd + 'e + 'f, 'b + 'a + 'c, 'e + 'd + 'f) wiring" 
  where
    "swap_lassocr\<^sub>w \<equiv> rassocl\<^sub>w \<circ>\<^sub>w ((swap\<^sub>w |\<^sub>w 1\<^sub>w) \<circ>\<^sub>w lassocr\<^sub>w)"

schematic_goal 
  wiring_swap_lassocr[wiring_intro]: "wiring ?\<I>1 ?\<I>2 swap_lassocr swap_lassocr\<^sub>w"
  unfolding swap_lassocr_def swap_lassocr\<^sub>w_def
  by(rule wiring_intro)+

definition 
  parallel_wiring\<^sub>w :: "(('a + 'b) + ('c + 'd), ('e + 'f) + ('g + 'h),
   ('a + 'c) + ('b + 'd), ('e + 'g) + ('f + 'h)) wiring" 
  where
    "parallel_wiring\<^sub>w \<equiv> lassocr\<^sub>w \<circ>\<^sub>w ((1\<^sub>w |\<^sub>w swap_lassocr\<^sub>w) \<circ>\<^sub>w rassocl\<^sub>w)"

schematic_goal 
  wiring_parallel_wiring[wiring_intro]: "wiring ?\<I>1 ?\<I>2 parallel_wiring parallel_wiring\<^sub>w"
  unfolding parallel_wiring_def parallel_wiring\<^sub>w_def
  by(rule wiring_intro)+


lemma lassocr_inverse: "rassocl\<^sub>C \<odot> lassocr\<^sub>C = 1\<^sub>C"
  unfolding rassocl\<^sub>C_def lassocr\<^sub>C_def
  apply(simp add: comp_converter_map1_out comp_converter_map_converter2 comp_converter_id_right)
  apply(subst map_converter_id_move_right)
  apply(simp add: o_def id_def[symmetric])
  done

lemma rassocl_inverse: "lassocr\<^sub>C \<odot> rassocl\<^sub>C = 1\<^sub>C"
  unfolding rassocl\<^sub>C_def lassocr\<^sub>C_def
  apply(simp add: comp_converter_map1_out comp_converter_map_converter2 comp_converter_id_right)
  apply(subst map_converter_id_move_right)
  apply(simp add: o_def id_def[symmetric])
  done

lemma swap_sum_swap_sum [simp]: "swap_sum (swap_sum x) = x"
  by(cases x) simp_all

lemma inj_on_lsumr [simp]: "inj_on lsumr A"
  by(auto simp add: inj_on_def elim: lsumr.elims)

lemma inj_on_rsuml [simp]: "inj_on rsuml A"
  by(auto simp add: inj_on_def elim: rsuml.elims)

lemma bij_lsumr [simp]: "bij lsumr"
  by(rule o_bij[where g=rsuml]) auto

lemma bij_swap_sum [simp]: "bij swap_sum"
  by(rule o_bij[where g=swap_sum]) auto

lemma bij_rsuml [simp]: "bij rsuml"
  by(rule o_bij[where g=lsumr]) auto

lemma bij_lassocr_swap_sum [simp]: "bij lassocr_swap_sum"
  unfolding lassocr_swap_sum_def
  by(simp add: bij_comp)

lemma inj_lassocr_swap_sum [simp]: "inj lassocr_swap_sum"
  by(simp add: bij_is_inj)

lemma inv_rsuml [simp]: "inv_into UNIV rsuml = lsumr"
  by(rule inj_imp_inv_eq) auto

lemma inv_lsumr [simp]: "inv_into UNIV lsumr = rsuml"
  by(rule inj_imp_inv_eq) auto

lemma lassocr_swap_sum_inverse [simp]: "lassocr_swap_sum (lassocr_swap_sum x) = x"
  by(simp add: lassocr_swap_sum_def sum.map_comp o_def id_def[symmetric] sum.map_id)

lemma inv_lassocr_swap_sum [simp]: "inv_into UNIV lassocr_swap_sum = lassocr_swap_sum"
  by(rule inj_imp_inv_eq)(simp_all add: sum.map_comp sum.inj_map bij_def surj_iff sum.map_id)

lemma swap_inverse: "swap\<^sub>C \<odot> swap\<^sub>C = 1\<^sub>C"
  unfolding swap\<^sub>C_def
  apply(simp add: comp_converter_map1_out comp_converter_map_converter2 comp_converter_id_right)
  apply(subst map_converter_id_move_right)
  apply(simp add: o_def id_def[symmetric])
  done

lemma swap_lassocr_inverse: "\<I>1 \<oplus>\<^sub>\<I> (\<I>2 \<oplus>\<^sub>\<I> \<I>3), \<I>1 \<oplus>\<^sub>\<I> (\<I>2 \<oplus>\<^sub>\<I> \<I>3) \<turnstile>\<^sub>C swap_lassocr \<odot> swap_lassocr \<sim> 1\<^sub>C"
  (is "?\<I>,_ \<turnstile>\<^sub>C ?lhs \<sim> _")
proof -
  have "?lhs = (rassocl\<^sub>C \<odot> (swap\<^sub>C |\<^sub>= 1\<^sub>C)) \<odot> (lassocr\<^sub>C \<odot> rassocl\<^sub>C) \<odot> ((swap\<^sub>C |\<^sub>= 1\<^sub>C) \<odot> lassocr\<^sub>C)"
    by(simp add: swap_lassocr_def comp_converter_assoc)
  also have "\<dots> = rassocl\<^sub>C \<odot> ((swap\<^sub>C \<odot> swap\<^sub>C) |\<^sub>= 1\<^sub>C) \<odot> lassocr\<^sub>C"
    unfolding rassocl_inverse comp_converter_id_left
    by(simp add: parallel_converter2_comp1_out comp_converter_assoc)
  also have "?\<I>,?\<I> \<turnstile>\<^sub>C \<dots> \<sim> rassocl\<^sub>C \<odot> 1\<^sub>C \<odot> lassocr\<^sub>C" unfolding swap_inverse
    by(rule eq_\<I>_converter_reflI eq_\<I>_comp_cong WT_intro parallel_converter2_id_id)+
  also have "rassocl\<^sub>C \<odot> 1\<^sub>C \<odot> lassocr\<^sub>C = 1\<^sub>C" by(simp add: comp_converter_id_left lassocr_inverse)
  finally show ?thesis .
qed

lemma parallel_wiring_inverse:
  "(\<I>1 \<oplus>\<^sub>\<I> \<I>2) \<oplus>\<^sub>\<I> (\<I>3 \<oplus>\<^sub>\<I> \<I>4),(\<I>1 \<oplus>\<^sub>\<I> \<I>2) \<oplus>\<^sub>\<I> (\<I>3 \<oplus>\<^sub>\<I> \<I>4) \<turnstile>\<^sub>C parallel_wiring \<odot> parallel_wiring \<sim> 1\<^sub>C"
  (is "?\<I>, _ \<turnstile>\<^sub>C ?lhs \<sim> _")
proof -
  have "?lhs = (lassocr\<^sub>C \<odot> (1\<^sub>C |\<^sub>= swap_lassocr)) \<odot> (rassocl\<^sub>C \<odot> lassocr\<^sub>C) \<odot> ((1\<^sub>C |\<^sub>= swap_lassocr) \<odot> rassocl\<^sub>C)"
    by(simp add: parallel_wiring_def comp_converter_assoc)
  also have "\<dots> = (lassocr\<^sub>C \<odot> (1\<^sub>C |\<^sub>= swap_lassocr)) \<odot> (1\<^sub>C |\<^sub>= swap_lassocr) \<odot> rassocl\<^sub>C"
    by(simp add: lassocr_inverse comp_converter_id_left)
  also have "\<dots> = lassocr\<^sub>C \<odot> (1\<^sub>C |\<^sub>= (swap_lassocr \<odot> swap_lassocr)) \<odot> rassocl\<^sub>C"
    by(simp add: parallel_converter2_comp2_out comp_converter_assoc)
  also have "?\<I>,?\<I> \<turnstile>\<^sub>C \<dots> \<sim> lassocr\<^sub>C \<odot> (1\<^sub>C |\<^sub>= 1\<^sub>C) \<odot> rassocl\<^sub>C"
    by(rule eq_\<I>_converter_reflI eq_\<I>_comp_cong parallel_converter2_eq_\<I>_cong WT_intro swap_lassocr_inverse)+
  also have "?\<I>,?\<I> \<turnstile>\<^sub>C lassocr\<^sub>C \<odot> (1\<^sub>C |\<^sub>= 1\<^sub>C) \<odot> rassocl\<^sub>C \<sim> lassocr\<^sub>C \<odot> 1\<^sub>C \<odot> rassocl\<^sub>C"
    by(rule eq_\<I>_converter_reflI eq_\<I>_comp_cong parallel_converter2_id_id WT_intro)+
  also have "lassocr\<^sub>C \<odot> 1\<^sub>C \<odot> rassocl\<^sub>C = 1\<^sub>C" by(simp add: comp_converter_id_left rassocl_inverse)
  finally show ?thesis .
qed

\<comment> \<open> Analogous to @{term \<open>attach_wiring\<close>} in Wiring.thy\<close>
definition 
  attach_wiring_right :: "
    ('a, 'b, 'c, 'd) wiring \<Rightarrow> 
      ('s \<Rightarrow> 'e \<Rightarrow> ('f \<times> 's, 'a, 'b) gpv) \<Rightarrow> ('s \<Rightarrow> 'e \<Rightarrow> ('f \<times> 's, 'c, 'd) gpv)"
  where 
    "attach_wiring_right = (\<lambda>(f, g). map_fun id (map_fun id (map_gpv' id f g)))"

lemma 
  attach_wiring_right_simps: 
    "attach_wiring_right (f, g) = map_fun id (map_fun id (map_gpv' id f g))"
  by(simp add: attach_wiring_right_def)

lemma 
  comp_converter_of_callee_wiring:
  assumes wiring: "wiring \<I>2 \<I>3 conv w"
      and WT: "\<I>1, \<I>2 \<turnstile>\<^sub>C CNV callee s \<surd>"
  shows "\<I>1, \<I>3 \<turnstile>\<^sub>C CNV callee s \<odot> conv \<sim> CNV (attach_wiring_right w callee) s"
  using wiring
proof cases
  case (wiring f g)
  from _ wiring(2) have "\<I>1,\<I>3 \<turnstile>\<^sub>C CNV callee s \<odot> conv \<sim> CNV callee s \<odot> map_converter id id f g 1\<^sub>C"
    by(rule eq_\<I>_comp_cong)(rule eq_\<I>_converter_reflI[OF WT])
  also have "CNV callee s \<odot> map_converter id id f g 1\<^sub>C = map_converter id id f g (CNV callee s)"
    by(subst comp_converter_map_converter2)(simp add: comp_converter_id_right)
  also have "\<dots> = CNV (attach_wiring_right w callee) s"
    by(simp add: map_converter_of_callee attach_wiring_right_simps wiring(1) prod.map_id0)
  finally show ?thesis .
qed

lemma attach_wiring_right_comp_wiring:
  "attach_wiring_right (w1 \<circ>\<^sub>w w2) callee = attach_wiring_right w2 (attach_wiring_right w1 callee)"
  by(simp add: attach_wiring_right_def comp_wiring_def split_def map_fun_def o_def map_gpv'_comp id_def fun_eq_iff)

lemma attach_wiring_comp_wiring:
  "attach_wiring (w1 \<circ>\<^sub>w w2) callee = attach_wiring w1 (attach_wiring w2 callee)"
  unfolding attach_wiring_def comp_wiring_def
  by (simp add: split_def map_fun_def o_def map_gpv_conv_map_gpv' map_gpv'_comp id_def map_prod_def)




subsection \<open>Probabilistic finite converter\<close>

coinductive pfinite_converter :: "('a, 'b) \<I> \<Rightarrow> ('c, 'd) \<I> \<Rightarrow> ('a, 'b, 'c, 'd) converter \<Rightarrow> bool" 
  for \<I> \<I>' where
  pfinite_converterI: "pfinite_converter \<I> \<I>' conv" if 
  "\<And>a. a \<in> outs_\<I> \<I> \<Longrightarrow> pfinite_gpv \<I>' (run_converter conv a)"
  "\<And>a b conv'. \<lbrakk> a \<in> outs_\<I> \<I>; (b, conv') \<in> results_gpv \<I>' (run_converter conv a) \<rbrakk> \<Longrightarrow> pfinite_converter \<I> \<I>' conv'"

lemma pfinite_converter_coinduct[consumes 1, case_names pfinite_converter, case_conclusion pfinite_converter pfinite step, coinduct pred: pfinite_converter]:
  assumes "X conv"
    and step: "\<And>conv a. \<lbrakk> X conv; a \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> pfinite_gpv \<I>' (run_converter conv a) \<and>
     (\<forall>(b, conv') \<in> results_gpv \<I>' (run_converter conv a). X conv' \<or> pfinite_converter \<I> \<I>' conv')"
  shows "pfinite_converter \<I> \<I>' conv"
  using assms(1) by(rule pfinite_converter.coinduct)(auto dest: step)

lemma pfinite_converterD:
  "\<lbrakk> pfinite_converter \<I> \<I>' conv; a \<in> outs_\<I> \<I> \<rbrakk> 
  \<Longrightarrow> pfinite_gpv \<I>' (run_converter conv a) \<and>
     (\<forall>(b, conv') \<in> results_gpv \<I>' (run_converter conv a). pfinite_converter \<I> \<I>' conv')"
  by(auto elim: pfinite_converter.cases)

lemma pfinite_converter_bot1 [simp]: "pfinite_converter bot \<I> conv"
  by(rule pfinite_converterI) auto

lemma pfinite_converter_mono:
  assumes *: "pfinite_converter \<I>1 \<I>2 conv"
    and le: "outs_\<I> \<I>1' \<subseteq> outs_\<I> \<I>1" "\<I>2 \<le> \<I>2'"
    and WT: "\<I>1, \<I>2 \<turnstile>\<^sub>C conv \<surd>"
  shows "pfinite_converter \<I>1' \<I>2' conv"
  using * WT
  apply(coinduction arbitrary: conv)
  apply(drule pfinite_converterD)
   apply(erule le(1)[THEN subsetD])
  apply(drule WT_converterD')
   apply(erule le(1)[THEN subsetD])
  using le(2)[THEN responses_\<I>_mono]
  by(auto intro: pfinite_gpv_mono[OF _ le(2)] results_gpv_mono[OF le(2), THEN subsetD] dest: bspec)

context raw_converter_invariant begin
lemma pfinite_converter_of_callee:
  assumes step: "\<And>x s. \<lbrakk> x \<in> outs_\<I> \<I>; I s \<rbrakk> \<Longrightarrow> pfinite_gpv \<I>' (callee s x)"
    and I: "I s"
  shows "pfinite_converter \<I> \<I>' (converter_of_callee callee s)"
  using I
  by(coinduction arbitrary: s)(auto 4 3 simp add: step dest: results_callee)
end

lemma raw_converter_invariant_run_pfinite_converter: 
  "raw_converter_invariant \<I> \<I>' run_converter (\<lambda>conv. pfinite_converter \<I> \<I>' conv \<and> \<I>,\<I>' \<turnstile>\<^sub>C conv \<surd>)"
  by(unfold_locales)(auto dest: WT_converterD pfinite_converterD)

interpretation run_pfinite_converter: raw_converter_invariant
  \<I> \<I>' run_converter "\<lambda>conv. pfinite_converter \<I> \<I>' conv \<and> \<I>,\<I>' \<turnstile>\<^sub>C conv \<surd>" for \<I> \<I>'
  by(rule raw_converter_invariant_run_pfinite_converter)

named_theorems pfinite_intro "Introduction rules for probabilistic finiteness"

lemma pfinite_id_converter [pfinite_intro]: "pfinite_converter \<I> \<I> id_converter"
  by(coinduction) simp

lemma pfinite_fail_converter [pfinite_intro]: "pfinite_converter \<I> \<I>' fail_converter"
  by coinduction simp

lemma pfinite_parallel_converter2 [pfinite_intro]:
  "pfinite_converter (\<I>1 \<oplus>\<^sub>\<I> \<I>2) (\<I>1' \<oplus>\<^sub>\<I> \<I>2') (conv1 |\<^sub>= conv2)"
  if "pfinite_converter \<I>1 \<I>1' conv1" "pfinite_converter \<I>2 \<I>2' conv2"
  using that by(coinduction arbitrary: conv1 conv2)(fastforce dest: pfinite_converterD)

context raw_converter_invariant begin

lemma expectation_gpv_1_le_inline:
  defines "expectation_gpv2 \<equiv> expectation_gpv 1 \<I>'"
  assumes callee: "\<And>s x. \<lbrakk> x \<in> outs_\<I> \<I>; I s \<rbrakk> \<Longrightarrow> pfinite_gpv \<I>' (callee s x)"
    and WT_gpv: "\<I> \<turnstile>g gpv \<surd>"
    and I: "I s"
    and f_le_1: "\<And>x. f x \<le> 1"
  shows "expectation_gpv 1 \<I> f gpv \<le> expectation_gpv2 (\<lambda>(x, s). f x) (inline callee gpv s)"
  using WT_gpv I
proof(induction arbitrary: gpv s rule: expectation_gpv_fixp_induct)
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step expectation_gpv')
  have "(\<integral>\<^sup>+ x. (case x of Pure a \<Rightarrow> f a | IO out c \<Rightarrow> \<Sqinter>r\<in>responses_\<I> \<I> out. expectation_gpv' (c r)) \<partial>measure_spmf (the_gpv gpv)) + 1 * ennreal (pmf (the_gpv gpv) None) = 
    (\<Sum>\<^sup>+ x. pmf (the_gpv gpv) x * (case x of Some (Pure a) \<Rightarrow> f a | Some (IO out c) \<Rightarrow> \<Sqinter>r\<in>responses_\<I> \<I> out. expectation_gpv' (c r) | None \<Rightarrow> 1))"
    apply(simp add: nn_integral_measure_spmf_conv_measure_pmf nn_integral_restrict_space nn_integral_measure_pmf)
    apply(subst (2) nn_integral_disjoint_pair_countspace[where B="range Some" and C="{None}", simplified, folded UNIV_option_conv, simplified])
    apply(auto simp add: mult.commute intro!: nn_integral_cong split: split_indicator)
    done
  also have "\<dots> \<le> (\<Sum>\<^sup>+ x. pmf (the_gpv gpv) x * (case x of None \<Rightarrow> 1 | Some (Pure a) \<Rightarrow> f a | Some (IO out c) \<Rightarrow> 
          (\<Sum>\<^sup>+ x. ennreal (pmf (the_gpv (callee s out) \<bind> case_generat (\<lambda>(x, y). inline1 callee (c x) y) (\<lambda>out rpv'. return_spmf (Inr (out, rpv', c)))) x) *
            (case x of None \<Rightarrow> 1 | Some (Inl (a, s)) \<Rightarrow> f a
             | Some (Inr (r, rpv, rpv')) \<Rightarrow> \<Sqinter>x\<in>responses_\<I> \<I>' r. expectation_gpv 1 \<I>' (\<lambda>(x, s'). expectation_gpv 1 \<I>' (\<lambda>(x, s). f x) (inline callee (rpv' x) s')) (rpv x)))))"
    (is "nn_integral _ ?lhs \<le> nn_integral _ ?rhs")
  proof(rule nn_integral_mono)
    fix x :: "('a, 'call, ('a, 'call, 'ret) rpv) generat option"
    consider (None) "x = None" | (Pure) a where "x = Some (Pure a)" 
      | (IO) out c where "x = Some (IO out c)" "IO out c \<in> set_spmf (the_gpv gpv)"
      | (outside) out c where "x = Some (IO out c)" "IO out c \<notin> set_spmf (the_gpv gpv)"
      by (metis dest_IO.elims not_None_eq)
    then show "?lhs x \<le> ?rhs x"
    proof cases
      case None then show ?thesis by simp
    next
      case Pure then show ?thesis by simp
    next
      case (IO out c)
      with step.prems have out: "out \<in> outs_\<I> \<I>" by(auto dest: WT_gpvD)
      then obtain response where resp: "response \<in> responses_\<I> \<I> out" unfolding in_outs_\<I>_iff_responses_\<I> by blast
      with out step.prems IO have WT_resp [WT_intro]: "\<I> \<turnstile>g c response \<surd>" by(auto dest: WT_gpvD)
      have exp_resp: "expectation_gpv' (c response) \<le> 1"
        using step.hyps[of "c response"] expectation_gpv_mono[of 1 1 f "\<lambda>_. 1" \<I> "c response"] expectation_gpv_const_le[OF WT_resp, of 1 1]
        by(simp add: le_fun_def f_le_1)

      have "(\<Sqinter>r\<in>responses_\<I> \<I> out. expectation_gpv' (c r)) = 
        (\<integral>\<^sup>+ generat. (\<Sqinter>r\<in>responses_\<I> \<I> out. expectation_gpv' (c r)) \<partial>measure_spmf (the_gpv (callee s out))) +
        (\<Sqinter>r\<in>responses_\<I> \<I> out. expectation_gpv' (c r)) * (1 - ennreal (weight_spmf (the_gpv (callee s out))))"
        by(simp add: measure_spmf.emeasure_eq_measure add_mult_distrib2[symmetric] semiring_class.distrib_left[symmetric] add_diff_inverse_ennreal weight_spmf_le_1)
      also have "\<dots> \<le> (\<integral>\<^sup>+ generat. (\<Sqinter>r\<in>responses_\<I> \<I> out. expectation_gpv' (c r)) \<partial>measure_spmf (the_gpv (callee s out))) +
        1 * ennreal (pmf (the_gpv (callee s out)) None)" unfolding pmf_None_eq_weight_spmf
        by(intro add_mono mult_mono order_refl INF_lower2[OF resp])(auto simp add: ennreal_minus[symmetric] weight_spmf_le_1 exp_resp)
      also have "\<dots> = (\<Sum>\<^sup>+ z. ennreal (pmf (the_gpv (callee s out)) z) * (case z of None \<Rightarrow> 1 | Some generat \<Rightarrow> (\<Sqinter>r\<in>responses_\<I> \<I> out. expectation_gpv' (c r))))"
        apply(simp add: nn_integral_measure_spmf_conv_measure_pmf nn_integral_restrict_space nn_integral_measure_pmf del: nn_integral_const)
        apply(subst (2) nn_integral_disjoint_pair_countspace[where B="range Some" and C="{None}", simplified, folded UNIV_option_conv, simplified])
        apply(auto simp add: mult.commute intro!: nn_integral_cong split: split_indicator)
        done
      also have "\<dots> \<le> (\<Sum>\<^sup>+ z. ennreal (pmf (the_gpv (callee s out)) z) *
         (case z of None \<Rightarrow> 1 | Some (IO out' rpv') \<Rightarrow> \<Sqinter>x\<in>responses_\<I> \<I>' out'. expectation_gpv 1 \<I>' (\<lambda>(x, s'). expectation_gpv 1 \<I>' (\<lambda>(x, s). f x) (inline callee (c x) s')) (rpv' x)
          | Some (Pure (r, s')) \<Rightarrow> (\<Sum>\<^sup>+ x. ennreal (pmf (inline1 callee (c r) s') x) * (case x of None \<Rightarrow> 1 | Some (Inl (a, s)) \<Rightarrow> f a | Some (Inr (out', rpv, rpv')) \<Rightarrow>
                  \<Sqinter>x\<in>responses_\<I> \<I>' out'. expectation_gpv 1 \<I>' (\<lambda>(x, s'). expectation_gpv 1 \<I>' (\<lambda>(x, s). f x) (inline callee (rpv' x) s')) (rpv x)))))"
         (is "nn_integral _ ?lhs2 \<le> nn_integral _ ?rhs2")
      proof(intro nn_integral_mono)
        fix z :: "('ret \<times> 's, 'call', ('ret \<times> 's, 'call', 'ret') rpv) generat option"
        consider (None) "z = None" | (Pure) x' s' where "z = Some (Pure (x', s'))" "Pure (x', s') \<in> set_spmf (the_gpv (callee s out))"
          | (IO') out' c' where "z = Some (IO out' c')" "IO out' c' \<in> set_spmf (the_gpv (callee s out))"
          | (outside) generat where "z = Some generat" "generat \<notin> set_spmf (the_gpv (callee s out))"
          by (metis dest_IO.elims not_Some_eq old.prod.exhaust)
        then show "?lhs2 z \<le> ?rhs2 z"
        proof cases
          case None then show ?thesis by simp
        next
          case Pure
          hence "(x', s') \<in> results_gpv \<I>' (callee s out)" by(simp add: results_gpv.Pure)
          with results_callee step.prems out have x: "x' \<in> responses_\<I> \<I> out" and s': "I s'" by auto
          with IO out step.prems have WT_c [WT_intro]: "\<I> \<turnstile>g c x' \<surd>" by(auto dest: WT_gpvD)
          from x have "(INF r\<in>responses_\<I> \<I> out. expectation_gpv' (c r)) \<le> expectation_gpv' (c x')" by(rule INF_lower)
          also have "\<dots> \<le> expectation_gpv2 (\<lambda>(x, s). f x) (inline callee (c x') s')" using WT_c s' by(rule step.IH)
          also have "\<dots> = \<integral>\<^sup>+ xx. (case xx of Inl (x, _) \<Rightarrow> f x 
               | Inr (out', callee', rpv) \<Rightarrow> INF r'\<in>responses_\<I> \<I>' out'. expectation_gpv 1 \<I>' (\<lambda>(r, s'). expectation_gpv 1 \<I>' (\<lambda>(x, s). f x) (inline callee (rpv r) s')) (callee' r'))
            \<partial>measure_spmf (inline1 callee (c x') s') + ennreal (pmf (the_gpv (inline callee (c x') s')) None)"
            unfolding expectation_gpv2_def
            by(subst expectation_gpv.simps)(auto simp add: inline_sel split_def o_def intro!: nn_integral_cong split: generat.split sum.split)
          also have "\<dots> = (\<Sum>\<^sup>+ xx. ennreal (pmf (inline1 callee (c x') s') xx) * (case xx of None \<Rightarrow> 1 | Some (Inl (x, _)) \<Rightarrow> f x 
            | Some (Inr (out', callee', rpv)) \<Rightarrow> INF r'\<in>responses_\<I> \<I>' out'. expectation_gpv 1 \<I>' (\<lambda>(r, s'). expectation_gpv 1 \<I>' (\<lambda>(x, s). f x) (inline callee (rpv r) s')) (callee' r')))"
            apply(subst inline_sel)
            apply(simp add: nn_integral_measure_spmf_conv_measure_pmf nn_integral_restrict_space nn_integral_measure_pmf pmf_map_spmf_None del: nn_integral_const)
            apply(subst (2) nn_integral_disjoint_pair_countspace[where B="range Some" and C="{None}", simplified, folded UNIV_option_conv, simplified])
            apply(auto simp add: mult.commute intro!: nn_integral_cong split: split_indicator)
            done
          finally show ?thesis using Pure by(simp add: mult_mono)
        next
          case IO'
          then have out': "out' \<in> outs_\<I> \<I>'" using WT_callee out step.prems by(auto dest: WT_gpvD)
          have "(INF r\<in>responses_\<I> \<I> out. expectation_gpv' (c r)) \<le> min (INF (r, s')\<in>(\<Union>r'\<in>responses_\<I> \<I>' out'. results_gpv \<I>' (c' r')). expectation_gpv' (c r)) 1"
            using IO' results_callee[OF out, of s] step.prems by(intro INF_mono min.boundedI)(auto intro: results_gpv.IO intro!: INF_lower2[OF resp] exp_resp)
          also have "\<dots> \<le> (INF r'\<in>responses_\<I> \<I>' out'. min (INF (r, s')\<in>results_gpv \<I>' (c' r'). expectation_gpv' (c r)) 1)"
            using resp out' unfolding inf_min[symmetric] in_outs_\<I>_iff_responses_\<I>
            by(subst INF_inf_const2)(auto simp add: INF_UNION)
          also have "\<dots> \<le> (INF r'\<in>responses_\<I> \<I>' out'. expectation_gpv 1 \<I>' (\<lambda>(r', s'). expectation_gpv 1 \<I>' (\<lambda>(x, s). f x) (inline callee (c r') s')) (c' r'))"
            (is "_ \<le> (INF r'\<in>_. ?r r')")
          proof(rule INF_mono, rule bexI)
            fix r'
            assume r': "r' \<in> responses_\<I> \<I>' out'"
            have fin: "pfinite_gpv \<I>' (c' r')" using callee[OF out, of s] IO' r' WT_callee[OF out, of s] step.prems by(auto dest: pfinite_gpv_ContD)
            have "min (INF (r, s')\<in>results_gpv \<I>' (c' r'). expectation_gpv' (c r)) 1 \<le> min (INF (r, s')\<in>results_gpv \<I>' (c' r'). expectation_gpv2 (\<lambda>(x, s). f x) (inline callee (c r) s')) 1"
              using IO IO' step.prems out results_callee[OF out, of s] r'
              by(intro min.mono)(auto intro!: INF_mono rev_bexI step.IH dest: WT_gpv_ContD intro: results_gpv.IO)
            also have "\<dots> \<le> ?r r'" unfolding expectation_gpv2_def using fin by(rule pfinite_INF_le_expectation_gpv)
            finally show "min (INF (r, s')\<in>results_gpv \<I>' (c' r'). expectation_gpv' (c r)) 1 \<le> \<dots>" .
          qed
          finally show ?thesis using IO' by(simp add: mult_mono)
        next
          case outside then show ?thesis by(simp add: in_set_spmf_iff_spmf)
        qed
      qed
      also have "\<dots> = (\<Sum>\<^sup>+ z. \<Sum>\<^sup>+ x.
             ennreal (pmf (the_gpv (callee s out)) z) *
             ennreal (pmf (case z of None \<Rightarrow> return_pmf None | Some (Pure (x, xb)) \<Rightarrow> inline1 callee (c x) xb | Some (IO out rpv') \<Rightarrow> return_spmf (Inr (out, rpv', c))) x) *
             (case x of None \<Rightarrow> 1 | Some (Inl (a, s)) \<Rightarrow> f a | Some (Inr (out, rpv, rpv')) \<Rightarrow> \<Sqinter>x\<in>responses_\<I> \<I>' out.
                expectation_gpv 1 \<I>' (\<lambda>(x, s'). expectation_gpv 1 \<I>' (\<lambda>(x, s). f x) (inline callee (rpv' x) s')) (rpv x)))"
        (is "\<dots> = (\<Sum>\<^sup>+ z. \<Sum>\<^sup>+ x. ?f x z)")
        by(auto intro!: nn_integral_cong split!: option.split generat.split simp add: mult.assoc nn_integral_cmult ennreal_indicator)
      also have "(\<Sum>\<^sup>+ z. \<Sum>\<^sup>+ x. ?f x z) = (\<Sum>\<^sup>+ x. \<Sum>\<^sup>+ z. ?f x z)"
        by(subst nn_integral_fst_count_space[where f="case_prod _", simplified])(simp add: nn_integral_snd_count_space[symmetric])
      also have "\<dots> = (\<Sum>\<^sup>+ x.
              ennreal (pmf (the_gpv (callee s out) \<bind> case_generat (\<lambda>(x, y). inline1 callee (c x) y) (\<lambda>out rpv'. return_spmf (Inr (out, rpv', c)))) x) *
              (case x of None \<Rightarrow> 1 | Some (Inl (a, s)) \<Rightarrow> f a | Some (Inr (r, rpv, rpv')) \<Rightarrow>
                   \<Sqinter>x\<in>responses_\<I> \<I>' r. expectation_gpv 1 \<I>' (\<lambda>(x, s'). expectation_gpv 1 \<I>' (\<lambda>(x, s). f x) (inline callee (rpv' x) s')) (rpv x)))"
        by(simp add: bind_spmf_def ennreal_pmf_bind nn_integral_multc[symmetric] nn_integral_measure_pmf)
      finally show ?thesis using IO by(auto intro!: mult_mono)
    next
      case outside then show ?thesis by(simp add: in_set_spmf_iff_spmf)
    qed
  qed
  also have "\<dots> = (\<Sum>\<^sup>+ y. \<Sum>\<^sup>+ x.
         ennreal (pmf (the_gpv gpv) y) *
         ennreal (case y of None \<Rightarrow> pmf (return_pmf None) x | Some (Pure xa) \<Rightarrow> pmf (return_spmf (Inl (xa, s))) x
                | Some (IO out rpv) \<Rightarrow>
                    pmf (bind_spmf (the_gpv (callee s out)) (\<lambda>generat' \<Rightarrow> case generat' of Pure (x, y) \<Rightarrow> inline1 callee (rpv x) y | IO out rpv' \<Rightarrow> return_spmf (Inr (out, rpv', rpv)))) x) *
         (case x of None \<Rightarrow> 1 | Some (Inl (a, s)) \<Rightarrow> f a 
         | Some (Inr (out, rpv, rpv')) \<Rightarrow> \<Sqinter>x\<in>responses_\<I> \<I>' out. expectation_gpv 1 \<I>' (\<lambda>(x, s'). expectation_gpv 1 \<I>' (\<lambda>(x, s). f x) (inline callee (rpv' x) s')) (rpv x)))"
    (is "_ = (\<Sum>\<^sup>+ y. \<Sum>\<^sup>+ x. ?f x y)")
    by(auto intro!: nn_integral_cong split!: option.split generat.split simp add: nn_integral_cmult mult.assoc ennreal_indicator)
  also have "(\<Sum>\<^sup>+ y. \<Sum>\<^sup>+ x. ?f x y) = (\<Sum>\<^sup>+ x. \<Sum>\<^sup>+ y. ?f x y)"
    by(subst nn_integral_fst_count_space[where f="case_prod _", simplified])(simp add: nn_integral_snd_count_space[symmetric])
  also have "\<dots> = (\<Sum>\<^sup>+ x. (pmf (inline1 callee gpv s) x) * (case x of None \<Rightarrow> 1 | Some (Inl (a, s)) \<Rightarrow> f a |
        Some (Inr (out, rpv, rpv')) \<Rightarrow> \<Sqinter>x\<in>responses_\<I> \<I>' out. expectation_gpv 1 \<I>' (\<lambda>(x, s'). expectation_gpv 1 \<I>' (\<lambda>(x, s). f x) (inline callee (rpv' x) s')) (rpv x)))"
    by(rewrite in "_ = \<hole>" inline1.simps)
      (auto simp add: bind_spmf_def ennreal_pmf_bind nn_integral_multc[symmetric] nn_integral_measure_pmf intro!: nn_integral_cong split: option.split generat.split)
  also have "\<dots> = (\<integral>\<^sup>+ res. (case res of Inl (a, s) \<Rightarrow> f a
            | Inr (out, rpv, rpv') \<Rightarrow> \<Sqinter>x\<in>responses_\<I> \<I>' out. expectation_gpv 1 \<I>' (\<lambda>(x, s'). expectation_gpv 1 \<I>' (\<lambda>(x, s). f x) (inline callee (rpv' x) s')) (rpv x))
       \<partial>measure_spmf (inline1 callee gpv s) +
    ennreal (pmf (inline1 callee gpv s) None))"
    apply(simp add: nn_integral_measure_spmf_conv_measure_pmf nn_integral_restrict_space nn_integral_measure_pmf)
    apply(subst nn_integral_disjoint_pair_countspace[where B="range Some" and C="{None}", simplified, folded UNIV_option_conv, simplified])
    apply(auto simp add: mult.commute intro!: nn_integral_cong split: split_indicator)
    done
  also have "\<dots> = expectation_gpv2 (\<lambda>(x, s). f x) (inline callee gpv s)" unfolding expectation_gpv2_def
    by(rewrite in "_ = \<hole>" expectation_gpv.simps, subst (1 2) inline_sel)
      (simp add: o_def pmf_map_spmf_None sum.case_distrib[where h="case_generat _ _"] split_def cong: sum.case_cong)
  finally show ?case .
qed

lemma pfinite_inline:
  assumes fin: "pfinite_gpv \<I> gpv"
    and WT: "\<I> \<turnstile>g gpv \<surd>"
    and callee: "\<And>s x. \<lbrakk> x \<in> outs_\<I> \<I>; I s \<rbrakk> \<Longrightarrow> pfinite_gpv \<I>' (callee s x)"
    and I: "I s"
  shows "pfinite_gpv \<I>' (inline callee gpv s)"
unfolding pgen_lossless_gpv_def
proof(rule antisym)
  have WT': "\<I>' \<turnstile>g inline callee gpv s \<surd>" using WT I by(rule WT_gpv_inline_invar)
  from expectation_gpv_const_le[OF WT', of 1 1]
  show "expectation_gpv 1 \<I>' (\<lambda>_. 1) (inline callee gpv s) \<le> 1" by(simp add: max_def)

  have "1 = expectation_gpv 1 \<I> (\<lambda>_. 1) gpv" using fin by(simp add: pgen_lossless_gpv_def)
  also have "\<dots> \<le> expectation_gpv 1 \<I>' (\<lambda>_. 1) (inline callee gpv s)"
    by(rule expectation_gpv_1_le_inline[unfolded split_def]; rule callee I WT WT_callee order_refl)
  finally show "1 \<le> \<dots>" .
qed

end

lemma pfinite_comp_converter [pfinite_intro]:
  "pfinite_converter \<I>1 \<I>3 (conv1 \<odot> conv2)"
  if "pfinite_converter \<I>1 \<I>2 conv1" "pfinite_converter \<I>2 \<I>3 conv2" "\<I>1,\<I>2 \<turnstile>\<^sub>C conv1 \<surd>" "\<I>2,\<I>3 \<turnstile>\<^sub>C conv2 \<surd>"
  using that 
proof(coinduction arbitrary: conv1 conv2)
  case pfinite_converter
  have conv1: "pfinite_gpv \<I>2 (run_converter conv1 a)" 
    using pfinite_converter(1, 5) by(simp add: pfinite_converterD)
  have conv2: "\<I>2 \<turnstile>g run_converter conv1 a \<surd>"
    using pfinite_converter(3, 5) by(simp add: WT_converterD)
  have ?pfinite using pfinite_converter(2,4,5)
    by(auto intro!:run_pfinite_converter.pfinite_inline[OF conv1] dest: pfinite_converterD intro: conv2)
  moreover have ?step (is "\<forall>(b, conv')\<in>?res. ?P b conv' \<or> _")
  proof(clarify)
    fix b conv''
    assume "(b, conv'') \<in> ?res"
    then obtain conv1' conv2' where [simp]: "conv'' = comp_converter conv1' conv2'" 
      and inline: "((b, conv1'), conv2') \<in> results_gpv \<I>3 (inline run_converter (run_converter conv1 a) conv2)" 
      by auto
    from run_pfinite_converter.results_gpv_inline[OF inline conv2] pfinite_converter(2,4)
    have run: "(b, conv1') \<in> results_gpv \<I>2 (run_converter conv1 a)"
      and *: "pfinite_converter \<I>2 \<I>3 conv2'" "\<I>2, \<I>3 \<turnstile>\<^sub>C conv2' \<surd>" by auto
    with WT_converterD(2)[OF pfinite_converter(3,5) run] pfinite_converterD[THEN conjunct2, rule_format, OF pfinite_converter(1,5) run]
    show "?P b conv''" by auto
  qed
  ultimately show ?case ..
qed

lemma pfinite_map_converter [pfinite_intro]:
  "pfinite_converter \<I>  \<I>' (map_converter f g f' g' conv)" if 
  *: "pfinite_converter (map_\<I> (inv_into UNIV f) (inv_into UNIV g) \<I>) (map_\<I> f' g' \<I>') conv"
  and f: "inj f" and g: "surj g"
  using *
proof(coinduction arbitrary: conv)
  case (pfinite_converter a conv)
  with f have a: "inv_into UNIV f (f a) \<in> outs_\<I> \<I>" by simp
  with pfinite_converterD[OF \<open>pfinite_converter _ _ conv\<close>, of "f a"] have "?pfinite" by simp
  moreover have ?step
  proof(safe)
    fix r conv'
    assume "(r, conv') \<in> results_gpv \<I>' (run_converter (map_converter f g f' g' conv) a)"
    then obtain r' conv''
      where results: "(r', conv'') \<in> results_gpv (map_\<I> f' g' \<I>') (run_converter conv (f a))"
        and r: "r = g r'"
        and conv': "conv' = map_converter f g f' g' conv''"
      by auto
    from pfinite_converterD[OF \<open>pfinite_converter _ _ conv\<close>, THEN conjunct2, rule_format, OF _ results] a r conv'
    show "\<exists>conv. conv' = map_converter f g f' g' conv \<and>
              pfinite_converter (map_\<I> (inv_into UNIV f) (inv_into UNIV g) \<I>) (map_\<I> f' g' \<I>') conv"
      by auto
  qed
  ultimately show ?case ..
qed

lemma pfinite_lassocr\<^sub>C [pfinite_intro]: "pfinite_converter ((\<I>1 \<oplus>\<^sub>\<I> \<I>2) \<oplus>\<^sub>\<I> \<I>3) (\<I>1 \<oplus>\<^sub>\<I> (\<I>2 \<oplus>\<^sub>\<I> \<I>3)) lassocr\<^sub>C"
  by(coinduction)(auto simp add: lassocr\<^sub>C_def)

lemma pfinite_rassocl\<^sub>C [pfinite_intro]: "pfinite_converter (\<I>1 \<oplus>\<^sub>\<I> (\<I>2 \<oplus>\<^sub>\<I> \<I>3)) ((\<I>1 \<oplus>\<^sub>\<I> \<I>2) \<oplus>\<^sub>\<I> \<I>3) rassocl\<^sub>C"
  by(coinduction)(auto simp add: rassocl\<^sub>C_def)

lemma pfinite_swap\<^sub>C [pfinite_intro]: "pfinite_converter (\<I>1 \<oplus>\<^sub>\<I> \<I>2) (\<I>2 \<oplus>\<^sub>\<I> \<I>1) swap\<^sub>C"
  by(coinduction)(auto simp add: swap\<^sub>C_def)

lemma pfinite_swap_lassocr [pfinite_intro]: "pfinite_converter (\<I>1 \<oplus>\<^sub>\<I> (\<I>2 \<oplus>\<^sub>\<I> \<I>3)) (\<I>2 \<oplus>\<^sub>\<I> (\<I>1 \<oplus>\<^sub>\<I> \<I>3)) swap_lassocr"
  unfolding swap_lassocr_def by(rule pfinite_intro WT_intro)+

lemma pfinite_swap_rassocl [pfinite_intro]: "pfinite_converter ((\<I>1 \<oplus>\<^sub>\<I> \<I>2) \<oplus>\<^sub>\<I> \<I>3) ((\<I>1 \<oplus>\<^sub>\<I> \<I>3) \<oplus>\<^sub>\<I> \<I>2) swap_rassocl"
  unfolding swap_rassocl_def by(rule pfinite_intro WT_intro)+

lemma pfinite_parallel_wiring [pfinite_intro]:
  "pfinite_converter ((\<I>1 \<oplus>\<^sub>\<I> \<I>2) \<oplus>\<^sub>\<I> (\<I>3 \<oplus>\<^sub>\<I> \<I>4)) ((\<I>1 \<oplus>\<^sub>\<I> \<I>3) \<oplus>\<^sub>\<I> (\<I>2 \<oplus>\<^sub>\<I> \<I>4)) parallel_wiring"
  unfolding parallel_wiring_def by(rule pfinite_intro WT_intro)+

lemma pfinite_parallel_converter [pfinite_intro]:
  "pfinite_converter (\<I>1 \<oplus>\<^sub>\<I> \<I>2) \<I>3 (conv1 |\<^sub>\<propto> conv2)"
  if "pfinite_converter \<I>1 \<I>3 conv1" and "pfinite_converter \<I>2 \<I>3 conv2"
  using that by(coinduction arbitrary: conv1 conv2)(fastforce dest: pfinite_converterD)

lemma pfinite_converter_of_resource [simp, pfinite_intro]: "pfinite_converter \<I>1 \<I>2 (converter_of_resource res)"
  by(coinduction arbitrary: res) auto

subsection \<open>colossless converter\<close>

coinductive colossless_converter :: "('a, 'b) \<I> \<Rightarrow> ('c, 'd) \<I> \<Rightarrow> ('a, 'b, 'c, 'd) converter \<Rightarrow> bool"
  for \<I> \<I>' where
  colossless_converterI:
  "colossless_converter \<I> \<I>' conv" if 
    "\<And>a. a \<in> outs_\<I> \<I> \<Longrightarrow> colossless_gpv \<I>' (run_converter conv a)"
    "\<And>a b conv'. \<lbrakk> a \<in> outs_\<I> \<I>; (b, conv') \<in> results_gpv \<I>' (run_converter conv a) \<rbrakk> \<Longrightarrow> colossless_converter \<I> \<I>' conv'"

lemma colossless_converter_coinduct[consumes 1, case_names colossless_converter, case_conclusion colossless_converter plossless step, coinduct pred: colossless_converter]:
  assumes "X conv"
    and step: "\<And>conv a. \<lbrakk> X conv; a \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> colossless_gpv \<I>' (run_converter conv a) \<and>
     (\<forall>(b, conv') \<in> results_gpv \<I>' (run_converter conv a). X conv' \<or> colossless_converter \<I> \<I>' conv')"
  shows "colossless_converter \<I> \<I>' conv"
  using assms(1) by(rule colossless_converter.coinduct)(auto dest: step)

lemma colossless_converterD:
  "\<lbrakk> colossless_converter \<I> \<I>' conv; a \<in> outs_\<I> \<I> \<rbrakk> 
  \<Longrightarrow> colossless_gpv \<I>' (run_converter conv a) \<and>
     (\<forall>(b, conv') \<in> results_gpv \<I>' (run_converter conv a). colossless_converter \<I> \<I>' conv')"
  by(auto elim: colossless_converter.cases)

lemma colossless_converter_bot1 [simp]: "colossless_converter bot \<I> conv"
  by(rule colossless_converterI) auto

lemma raw_converter_invariant_run_colossless_converter: "raw_converter_invariant \<I> \<I>' run_converter (\<lambda>conv. colossless_converter \<I> \<I>' conv \<and> \<I>,\<I>' \<turnstile>\<^sub>C conv \<surd>)"
  by(unfold_locales)(auto dest: WT_converterD colossless_converterD)

interpretation run_colossless_converter: raw_converter_invariant
  \<I> \<I>' run_converter "\<lambda>conv. colossless_converter \<I> \<I>' conv \<and> \<I>,\<I>' \<turnstile>\<^sub>C conv \<surd>" for \<I> \<I>'
  by(rule raw_converter_invariant_run_colossless_converter)

lemma colossless_const_converter [simp]: "colossless_converter \<I> \<I>' (const_converter x)"
  by(coinduction)(auto)

subsection \<open>trace equivalence\<close>

lemma distinguish_trace_eq: (* generalized from Distinguisher.thy *)
  assumes distinguish: "\<And>distinguisher. \<I> \<turnstile>g distinguisher \<surd> \<Longrightarrow> connect distinguisher res = connect distinguisher res'"
  shows "outs_\<I> \<I> \<turnstile>\<^sub>R res \<approx> res'"
  using assms by(rule distinguish_trace_eq)(auto intro: WT_fail_resource)

lemma attach_trace_eq':
  assumes eq: "outs_\<I> \<I> \<turnstile>\<^sub>R res1 \<approx> res2"
    and WT1 [WT_intro]: "\<I> \<turnstile>res res1 \<surd>"
    and WT2 [WT_intro]: "\<I> \<turnstile>res res2 \<surd>"
    and WT_conv [WT_intro]: "\<I>',\<I> \<turnstile>\<^sub>C conv \<surd>"
  shows "outs_\<I> \<I>' \<turnstile>\<^sub>R conv \<rhd> res1 \<approx> conv \<rhd> res2"
proof(rule distinguish_trace_eq)
  fix \<D> :: "('c, 'd) distinguisher"
  assume [WT_intro]: "\<I>' \<turnstile>g \<D> \<surd>"
  have "connect (absorb \<D> conv) res1 = connect (absorb \<D> conv) res2" using eq 
    by(rule connect_cong_trace)(rule WT_intro | fold WT_gpv_iff_outs_gpv)+
  then show "connect \<D> (conv \<rhd> res1) = connect \<D> (conv \<rhd> res2)" by(simp add: distinguish_attach)
qed

lemma trace_callee_eq_trans [trans]:
  "\<lbrakk> trace_callee_eq callee1 callee2 A p q; trace_callee_eq callee2 callee3 A q r \<rbrakk>
   \<Longrightarrow> trace_callee_eq callee1 callee3 A p r"
  by(simp add: trace_callee_eq_def)

lemma trace_eq'_parallel_resource:
  fixes res1 :: "('a, 'b) resource" and res2 :: "('c, 'd) resource"
  assumes 1: "trace_eq' A res1 res1'"
    and 2: "trace_eq' B res2 res2'"
  shows "trace_eq' (A <+> B) (res1 \<parallel> res2) (res1' \<parallel> res2')"
proof -
  let ?\<I> = "\<I>_uniform A (UNIV :: 'b set) \<oplus>\<^sub>\<I> \<I>_uniform B (UNIV :: 'd set)"
  have "trace_eq' (outs_\<I> ?\<I>) (res1 \<parallel> res2) (res1' \<parallel> res2)"
    apply(subst (1 2) attach_converter_of_resource_conv_parallel_resource2[symmetric])
    apply(rule attach_trace_eq'[where ?\<I> = "\<I>_uniform A UNIV"]; auto simp add: 1 intro: WT_intro WT_resource_\<I>_uniform_UNIV)
    done
  also have "trace_eq' (outs_\<I> ?\<I>) (res1' \<parallel> res2) (res1' \<parallel> res2')"
    apply(subst (1 2) attach_converter_of_resource_conv_parallel_resource[symmetric])
    apply(rule attach_trace_eq'[where ?\<I> = "\<I>_uniform B UNIV"]; auto simp add: 2 intro: WT_intro WT_resource_\<I>_uniform_UNIV)
    done
  finally show ?thesis by simp
qed

proposition trace_callee_eq_coinduct [consumes 1, case_names step sim]: (* stronger version of trace'_eq_simI *)
  fixes callee1 :: "('a, 'b, 's1) callee" and callee2 :: "('a, 'b, 's2) callee"
  assumes start: "S p q"
    and step: "\<And>p q a. \<lbrakk> S p q; a \<in> A \<rbrakk> \<Longrightarrow>
      bind_spmf p (\<lambda>s. map_spmf fst (callee1 s a)) = bind_spmf q (\<lambda>s. map_spmf fst (callee2 s a))"
    and sim: "\<And>p q a res res' b s'' s'. \<lbrakk> S p q; a \<in> A; res \<in> set_spmf p; (b, s'') \<in> set_spmf (callee1 res a); res' \<in> set_spmf q; (b, s') \<in> set_spmf (callee2 res' a) \<rbrakk>
      \<Longrightarrow> S (cond_spmf_fst (bind_spmf p (\<lambda>s. callee1 s a)) b)
            (cond_spmf_fst (bind_spmf q (\<lambda>s. callee2 s a)) b)"
  shows "trace_callee_eq callee1 callee2 A p q"
proof(rule trace_callee_eqI)
  fix xs :: "('a \<times> 'b) list" and z
  assume xs: "set xs \<subseteq> A \<times> UNIV" and z: "z \<in> A"

  from start show "trace_callee callee1 p xs z = trace_callee callee2 q xs z" using xs
  proof(induction xs arbitrary: p q)
    case Nil
    then show ?case using z by(simp add: step)
  next
    case (Cons xy xs)
    obtain x y where xy [simp]: "xy = (x, y)" by(cases xy)
    have "trace_callee callee1 p (xy # xs) z = 
      trace_callee callee1 (cond_spmf_fst (bind_spmf p (\<lambda>s. callee1 s x)) y) xs z"
      by(simp add: bind_map_spmf split_def o_def)
    also have "\<dots> = trace_callee callee2 (cond_spmf_fst (bind_spmf q (\<lambda>s. callee2 s x)) y) xs z"
    proof(cases "\<exists>s \<in> set_spmf q. \<exists>s'. (y, s') \<in> set_spmf (callee2 s x)")
      case True
      then obtain s s' where ss': "s \<in> set_spmf q" "(y, s') \<in> set_spmf (callee2 s x)" by blast
      from Cons have "x \<in> A" by simp
      from ss' step[THEN arg_cong[where f="set_spmf"], OF \<open>S p q\<close> this] obtain ss ss'
        where "ss \<in> set_spmf p" "(y, ss') \<in> set_spmf (callee1 ss x)" 
        by(clarsimp simp add: bind_UNION) force
      from sim[OF \<open>S p q\<close> _ this ss'] show ?thesis using Cons.prems by (auto intro: Cons.IH)
    next
      case False
      then have "cond_spmf_fst (bind_spmf q (\<lambda>s. callee2 s x)) y = return_pmf None"
        by(auto simp add: bind_eq_return_pmf_None)
      moreover from step[OF \<open>S p q\<close>, of x, THEN arg_cong[where f=set_spmf], THEN eq_refl] Cons.prems False
      have "cond_spmf_fst (bind_spmf p (\<lambda>s. callee1 s x)) y = return_pmf None"
        by(clarsimp simp add: bind_eq_return_pmf_None)(rule ccontr; fastforce)
      ultimately show ?thesis by(simp del: cond_spmf_fst_eq_return_None)
    qed
    also have "\<dots> = trace_callee callee2 q (xy # xs) z"
      by(simp add: split_def o_def)
    finally show ?case .
  qed
qed

proposition trace_callee_eq_coinduct_strong [consumes 1, case_names step sim, case_conclusion step lhs rhs, case_conclusion sim sim eq]:
  fixes callee1 :: "('a, 'b, 's1) callee" and callee2 :: "('a, 'b, 's2) callee"
  assumes start: "S p q"
    and step: "\<And>p q a. \<lbrakk> S p q; a \<in> A \<rbrakk> \<Longrightarrow>
      bind_spmf p (\<lambda>s. map_spmf fst (callee1 s a)) = bind_spmf q (\<lambda>s. map_spmf fst (callee2 s a))"
    and sim: "\<And>p q a res res' b s'' s'. \<lbrakk> S p q; a \<in> A; res \<in> set_spmf p; (b, s'') \<in> set_spmf (callee1 res a); res' \<in> set_spmf q; (b, s') \<in> set_spmf (callee2 res' a) \<rbrakk>
      \<Longrightarrow> S (cond_spmf_fst (bind_spmf p (\<lambda>s. callee1 s a)) b)
            (cond_spmf_fst (bind_spmf q (\<lambda>s. callee2 s a)) b) \<or>
          trace_callee_eq callee1 callee2 A (cond_spmf_fst (bind_spmf p (\<lambda>s. callee1 s a)) b) (cond_spmf_fst (bind_spmf q (\<lambda>s. callee2 s a)) b)"
  shows "trace_callee_eq callee1 callee2 A p q"
proof -
  from start have "S p q \<or> trace_callee_eq callee1 callee2 A p q" by simp
  thus ?thesis
    apply(rule trace_callee_eq_coinduct)
     apply(erule disjE)
      apply(erule (1) step)
     apply(drule trace_callee_eqD[where xs="[]"]; simp)
    apply(erule disjE)
     apply(erule (5) sim)
    apply(rule disjI2)
    apply(rule trace_callee_eqI)
    apply(drule trace_callee_eqD[where xs="(_, _) # _"])
    apply simp_all
    done
qed

lemma trace_callee_return_pmf_None [simp]:
  "trace_callee_eq callee1 callee2 A (return_pmf None) (return_pmf None)"
  by(rule trace_callee_eqI) simp

lemma trace_callee_eq_sym [sym]: "trace_callee_eq callee1 callee2 A p q \<Longrightarrow> trace_callee_eq callee2 callee1 A q p"
  by(simp add: trace_callee_eq_def)

lemma eq_resource_on_imp_trace_eq: "A \<turnstile>\<^sub>R res1 \<approx> res2" if "A \<turnstile>\<^sub>R res1 \<sim> res2"
proof -
  have "outs_\<I> (\<I>_uniform A UNIV :: ('a, 'b) \<I>) \<turnstile>\<^sub>R res1 \<approx> res2" using that
    by -(rule distinguish_trace_eq[OF connect_eq_resource_cong], simp+)
  thus ?thesis by simp
qed

lemma advantage_nonneg: "0 \<le> advantage \<A> res1 res2"
  by(simp add: advantage_def)

lemma comp_converter_of_resource_conv_parallel_converter:
  "(converter_of_resource res |\<^sub>\<propto> 1\<^sub>C) \<odot> conv = converter_of_resource res |\<^sub>\<propto> conv"
  by(coinduction arbitrary: res conv)
    (auto 4 3 simp add: rel_fun_def gpv.map_comp map_lift_spmf spmf_rel_map split_def map_gpv_conv_bind[symmetric] id_def[symmetric] gpv.rel_map split!: sum.split intro!: rel_spmf_reflI gpv.rel_refl_strong)

lemma comp_converter_of_resource_conv_parallel_converter2:
  "(1\<^sub>C |\<^sub>\<propto> converter_of_resource res) \<odot> conv = conv |\<^sub>\<propto> converter_of_resource res"
  by(coinduction arbitrary: res conv)
    (auto 4 3 simp add: rel_fun_def gpv.map_comp map_lift_spmf spmf_rel_map split_def map_gpv_conv_bind[symmetric] id_def[symmetric] gpv.rel_map split!: sum.split intro!: rel_spmf_reflI gpv.rel_refl_strong)

lemma parallel_converter_map_converter:
  "map_converter f g f' g' conv1 |\<^sub>\<propto> map_converter f'' g'' f' g' conv2 = 
   map_converter (map_sum f f'') (map_sum g g'') f' g' (conv1 |\<^sub>\<propto> conv2)"
  using parallel_callee_parametric[
      where A="conversep (BNF_Def.Grp UNIV f)" and B="BNF_Def.Grp UNIV g" and C="BNF_Def.Grp UNIV f'" and R="conversep (BNF_Def.Grp UNIV g')" and A'="conversep (BNF_Def.Grp UNIV f'')" and B'="BNF_Def.Grp UNIV g''",
      unfolded rel_converter_Grp sum.rel_conversep sum.rel_Grp,
      simplified,
      unfolded rel_converter_Grp]
  by(simp add: rel_fun_def Grp_def)

lemma map_converter_parallel_converter_out2:
  "conv1 |\<^sub>\<propto> map_converter f g id id conv2 = map_converter (map_sum id f) (map_sum id g) id id (conv1 |\<^sub>\<propto> conv2)"
  by(rule parallel_converter_map_converter[where f=id and g=id and f'=id and g'=id, simplified])

lemma parallel_converter_assoc2:
  "parallel_converter conv1 (parallel_converter conv2 conv3) =                                   
   map_converter lsumr rsuml id id (parallel_converter (parallel_converter conv1 conv2) conv3)"
  by(coinduction arbitrary: conv1 conv2 conv3)
    (auto 4 5 intro!: rel_funI gpv.rel_refl_strong split: sum.split simp add: gpv.rel_map map_gpv'_id map_gpv_conv_map_gpv'[symmetric])

lemma parallel_converter_of_resource:
  "converter_of_resource res1 |\<^sub>\<propto> converter_of_resource res2 = converter_of_resource (res1 \<parallel> res2)"
  by(coinduction arbitrary: res1 res2)
    (auto 4 3 simp add: rel_fun_def map_lift_spmf spmf_rel_map intro!: rel_spmf_reflI split!: sum.split)

lemma map_Inr_parallel_converter:
  "map_converter Inr f g h (conv1 |\<^sub>\<propto> conv2) = map_converter id (f \<circ> Inr) g h conv2"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = map_converter Inr f id id (map_converter id id g h conv1 |\<^sub>\<propto> map_converter id id g h conv2)"
    by(simp add: parallel_converter_map_converter sum.map_id0)
  also have "map_converter Inr f id id (conv1 |\<^sub>\<propto> conv2) = map_converter id (f \<circ> Inr) id id conv2" for conv1 conv2
    by(coinduction arbitrary: conv2)
      (auto simp add: rel_fun_def map_gpv_conv_map_gpv'[symmetric] gpv.rel_map intro!: gpv.rel_refl_strong)
  also have "map_converter id (f \<circ> Inr) id id (map_converter id id g h conv2) = ?rhs" by simp
  finally show ?thesis .
qed

lemma map_Inl_parallel_converter:
  "map_converter Inl f g h (conv1 |\<^sub>\<propto> conv2) = map_converter id (f \<circ> Inl) g h conv1"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = map_converter Inl f id id (map_converter id id g h conv1 |\<^sub>\<propto> map_converter id id g h conv2)"
    by(simp add: parallel_converter_map_converter sum.map_id0)
  also have "map_converter Inl f id id (conv1 |\<^sub>\<propto> conv2) = map_converter id (f \<circ> Inl) id id conv1" for conv1 conv2
    by(coinduction arbitrary: conv1)
      (auto simp add: rel_fun_def map_gpv_conv_map_gpv'[symmetric] gpv.rel_map intro!: gpv.rel_refl_strong)
  also have "map_converter id (f \<circ> Inl) id id (map_converter id id g h conv1) = ?rhs" by simp
  finally show ?thesis .
qed

lemma left_interface_parallel_converter:
  "left_interface (conv1 |\<^sub>\<propto> conv2) = left_interface conv1 |\<^sub>\<propto> left_interface conv2"
  by(coinduction arbitrary: conv1 conv2)
    (auto 4 3 split!: sum.split simp add: rel_fun_def gpv.rel_map left_gpv_map[where h=id] sum.map_id0 intro!: gpv.rel_refl_strong)

lemma right_interface_parallel_converter:
  "right_interface (conv1 |\<^sub>\<propto> conv2) = right_interface conv1 |\<^sub>\<propto> right_interface conv2"
  by(coinduction arbitrary: conv1 conv2)
    (auto 4 3 split!: sum.split simp add: rel_fun_def gpv.rel_map right_gpv_map[where h=id] sum.map_id0 intro!: gpv.rel_refl_strong)

lemma left_interface_converter_of_resource [simp]: 
  "left_interface (converter_of_resource res) = converter_of_resource res"
  by(coinduction arbitrary: res)(auto simp add: rel_fun_def map_lift_spmf spmf_rel_map intro!: rel_spmf_reflI)

lemma right_interface_converter_of_resource [simp]: 
  "right_interface (converter_of_resource res) = converter_of_resource res"
  by(coinduction arbitrary: res)(auto simp add: rel_fun_def map_lift_spmf spmf_rel_map intro!: rel_spmf_reflI)

lemma parallel_converter_swap: "map_converter swap_sum swap_sum id id (conv1 |\<^sub>\<propto> conv2) = conv2 |\<^sub>\<propto> conv1"
  by(coinduction arbitrary: conv1 conv2)
    (auto 4 3 split!: sum.split simp add: rel_fun_def map_gpv_conv_map_gpv'[symmetric] gpv.rel_map intro!: gpv.rel_refl_strong)

lemma eq_\<I>_converter_map_converter':
  assumes "\<I>'', map_\<I> f' g' \<I>' \<turnstile>\<^sub>C conv1 \<sim> conv2"
    and "f ` outs_\<I> \<I> \<subseteq> outs_\<I> \<I>''"
    and "\<forall>q\<in>outs_\<I> \<I>. g ` responses_\<I> \<I>'' (f q) \<subseteq> responses_\<I> \<I> q"
  shows "\<I>, \<I>' \<turnstile>\<^sub>C map_converter f g f' g' conv1 \<sim> map_converter f g f' g' conv2"
  using assms(1)
proof(coinduction arbitrary: conv1 conv2)
  case eq_\<I>_converter
  from this(2) have "f q \<in> outs_\<I> \<I>''" using assms(2) by auto
  from eq_\<I>_converter(1)[THEN eq_\<I>_converterD, OF this] eq_\<I>_converter(2)
  show ?case
    apply simp
    apply(rule eq_\<I>_gpv_map_gpv')
    apply(simp add: BNF_Def.vimage2p_def prod.rel_map)
    apply(erule eq_\<I>_gpv_mono')
    using assms(3)
     apply(auto 4 4 simp add: eq_onp_def)
    done
qed

lemma parallel_converter_eq_\<I>_cong:
  "\<lbrakk> \<I>1, \<I> \<turnstile>\<^sub>C conv1 \<sim> conv1'; \<I>2, \<I> \<turnstile>\<^sub>C conv2 \<sim> conv2' \<rbrakk>
  \<Longrightarrow> \<I>1 \<oplus>\<^sub>\<I> \<I>2, \<I> \<turnstile>\<^sub>C parallel_converter conv1 conv2 \<sim> parallel_converter conv1' conv2'"
  by(coinduction arbitrary: conv1 conv2 conv1' conv2')
    (fastforce dest: eq_\<I>_converterD elim!: eq_\<I>_gpv_mono' simp add: eq_onp_def)

\<comment> \<open>Helper lemmas for simplyfing @{term exec_gpv}\<close>
lemma
  exec_gpv_parallel_oracle_right: 
    "exec_gpv (oracle1 \<ddagger>\<^sub>O oracle2) (right_gpv gpv) s = exec_gpv (\<dagger>oracle2) gpv s"
  unfolding spmf_rel_eq[symmetric]
  apply (rule rel_spmf_mono)
  by (rule exec_gpv_parametric'[where S="(=)" and A="(=)" and CALL="\<lambda>l r. l = Inr r" and R="\<lambda>l r. l = Inr r" , THEN rel_funD, THEN rel_funD, THEN rel_funD ])
    (auto simp add: prod.rel_eq extend_state_oracle_def parallel_oracle_def split_def
      spmf_rel_map1 spmf_rel_map2 map_prod_def rel_spmf_reflI right_gpv_Inr_transfer intro!:rel_funI)

lemma
  exec_gpv_parallel_oracle_left: 
    "exec_gpv (oracle1 \<ddagger>\<^sub>O oracle2) (left_gpv gpv) s = exec_gpv (oracle1\<dagger>) gpv s" (is "?L = ?R")
  unfolding spmf_rel_eq[symmetric]
  apply (rule rel_spmf_mono)
   by (rule exec_gpv_parametric'[where S="(=)" and A="(=)" and CALL="\<lambda>l r. l = Inl r" and R="\<lambda>l r. l = Inl r" , THEN rel_funD, THEN rel_funD, THEN rel_funD ])
     (auto simp add: prod.rel_eq extend_state_oracle2_def parallel_oracle_def split_def
       spmf_rel_map1 spmf_rel_map2 map_prod_def rel_spmf_reflI left_gpv_Inl_transfer intro!:rel_funI)

end