theory PAC_Polynomials
  imports PAC_Specification Finite_Map_Multiset
begin


section \<open>Polynomials of strings\<close>

text \<open>

  Isabelle's definition of polynomials only work with variables of type
  \<^typ>\<open>nat\<close>. Therefore, we introduce a version that uses strings by using an injective function
  that converts a string to a natural number. It exists because strings are countable. Remark that
  the whole development is independent of the function.

\<close>

subsection \<open>Polynomials and Variables\<close>

lemma poly_embed_EX:
  \<open>\<exists>\<phi>. bij (\<phi> :: string \<Rightarrow> nat)\<close>
  by (rule countableE_infinite[of \<open>UNIV :: string set\<close>])
     (auto intro!: infinite_UNIV_listI)

text \<open>Using a multiset instead of a list has some advantage from an abstract point of view. First,
  we can have monomials that appear several times  and the coefficient can also be zero. Basically,
  we can represent un-normalised polynomials, which is very useful to talk about intermediate states
  in our program.
\<close>
type_synonym term_poly = \<open>string multiset\<close>
type_synonym mset_polynomial =
  \<open>(term_poly * int) multiset\<close>

definition normalized_poly :: \<open>mset_polynomial \<Rightarrow> bool\<close> where
  \<open>normalized_poly p \<longleftrightarrow>
     distinct_mset (fst `# p) \<and>
     0 \<notin># snd `# p\<close>

lemma normalized_poly_simps[simp]:
  \<open>normalized_poly {#}\<close>
  \<open>normalized_poly (add_mset t p) \<longleftrightarrow> snd t \<noteq> 0 \<and>
    fst t \<notin># fst `# p \<and> normalized_poly p\<close>
  by (auto simp: normalized_poly_def)

lemma normalized_poly_mono:
  \<open>normalized_poly B \<Longrightarrow> A \<subseteq># B \<Longrightarrow> normalized_poly A\<close>
  unfolding normalized_poly_def
  by (auto intro: distinct_mset_mono image_mset_subseteq_mono)

definition mult_poly_by_monom :: \<open>term_poly * int \<Rightarrow> mset_polynomial \<Rightarrow> mset_polynomial\<close> where
  \<open>mult_poly_by_monom  = (\<lambda>ys q. image_mset (\<lambda>xs. (fst xs + fst ys, snd ys * snd xs)) q)\<close>


definition mult_poly_raw :: \<open>mset_polynomial \<Rightarrow> mset_polynomial \<Rightarrow> mset_polynomial\<close> where
  \<open>mult_poly_raw p q =
    (sum_mset ((\<lambda>y. mult_poly_by_monom y q) `# p))\<close>


definition remove_powers :: \<open>mset_polynomial \<Rightarrow> mset_polynomial\<close> where
  \<open>remove_powers xs =  image_mset (apfst remdups_mset) xs\<close>


definition all_vars_mset :: \<open>mset_polynomial \<Rightarrow> string multiset\<close> where
  \<open>all_vars_mset p = \<Sum>\<^sub># (fst `# p)\<close>

abbreviation all_vars :: \<open>mset_polynomial \<Rightarrow> string set\<close> where
  \<open>all_vars p \<equiv> set_mset (all_vars_mset p)\<close>

definition add_to_coefficient :: \<open>_ \<Rightarrow> mset_polynomial \<Rightarrow> mset_polynomial\<close>  where
  \<open>add_to_coefficient = (\<lambda>(a, n) b. {#(a', _) \<in># b. a' \<noteq> a#} +
             (if n + sum_mset (snd `# {#(a', _) \<in># b. a' = a#}) = 0 then {#}
               else {#(a, n + sum_mset (snd `# {#(a', _) \<in># b. a' = a#}))#}))\<close>

definition normalize_poly :: \<open>mset_polynomial \<Rightarrow> mset_polynomial\<close> where
  \<open>normalize_poly p = fold_mset add_to_coefficient {#} p\<close>

lemma add_to_coefficient_simps:
  \<open>n + sum_mset (snd `# {#(a', _) \<in># b. a' = a#}) \<noteq> 0 \<Longrightarrow>
    add_to_coefficient (a, n) b = {#(a', _) \<in># b. a' \<noteq> a#} +
             {#(a, n + sum_mset (snd `# {#(a', _) \<in># b. a' = a#}))#}\<close>
  \<open>n + sum_mset (snd `# {#(a', _) \<in># b. a' = a#}) = 0 \<Longrightarrow>
    add_to_coefficient (a, n) b = {#(a', _) \<in># b. a' \<noteq> a#}\<close> and
  add_to_coefficient_simps_If:
  \<open>add_to_coefficient (a, n) b = {#(a', _) \<in># b. a' \<noteq> a#} +
             (if n + sum_mset (snd `# {#(a', _) \<in># b. a' = a#}) = 0 then {#}
               else {#(a, n + sum_mset (snd `# {#(a', _) \<in># b. a' = a#}))#})\<close>
  by (auto simp: add_to_coefficient_def)

interpretation comp_fun_commute \<open>add_to_coefficient\<close>
proof -
  have [iff]:
    \<open>a \<noteq> aa \<Longrightarrow>
    ((case x of (a', _) \<Rightarrow> a' = a) \<and> (case x of (a', _) \<Rightarrow> a' \<noteq> aa)) \<longleftrightarrow>
    (case x of (a', _) \<Rightarrow> a' = a)\<close> for a' aa a x
    by auto
  show \<open>comp_fun_commute add_to_coefficient\<close>
    unfolding add_to_coefficient_def
    by standard
     (auto intro!: ext simp: filter_filter_mset ac_simps add_eq_0_iff)
qed

lemma normalized_poly_normalize_poly[simp]:
  \<open>normalized_poly (normalize_poly p)\<close>
  unfolding normalize_poly_def
  apply (induction p)
  subgoal by auto
  subgoal for x p
    by (cases x)
      (auto simp: add_to_coefficient_simps_If
      intro: normalized_poly_mono)
  done


subsection \<open>Addition\<close>

inductive add_poly_p :: \<open>mset_polynomial \<times> mset_polynomial \<times> mset_polynomial \<Rightarrow> mset_polynomial \<times> mset_polynomial \<times> mset_polynomial \<Rightarrow> bool\<close> where
add_new_coeff_r:
    \<open>add_poly_p (p, add_mset x q, r) (p, q, add_mset x r)\<close> |
add_new_coeff_l:
    \<open>add_poly_p (add_mset x p, q, r) (p, q, add_mset x r)\<close> |
add_same_coeff_l:
    \<open>add_poly_p (add_mset (x, n) p, q, add_mset (x, m) r) (p, q, add_mset (x, n + m) r)\<close> |
add_same_coeff_r:
    \<open>add_poly_p (p, add_mset (x, n) q, add_mset (x, m) r) (p, q, add_mset (x, n + m) r)\<close> |
rem_0_coeff:
    \<open>add_poly_p (p, q, add_mset (x, 0) r) (p, q, r)\<close>

inductive_cases add_poly_pE: \<open>add_poly_p S T\<close>

lemmas add_poly_p_induct =
  add_poly_p.induct[split_format(complete)]

lemma add_poly_p_empty_l:
  \<open>add_poly_p\<^sup>*\<^sup>* (p, q, r) ({#}, q, p + r)\<close>
  apply (induction p arbitrary: r)
  subgoal by auto
  subgoal
    by (metis (no_types, lifting) add_new_coeff_l r_into_rtranclp
      rtranclp_trans union_mset_add_mset_left union_mset_add_mset_right)
  done

lemma add_poly_p_empty_r:
  \<open>add_poly_p\<^sup>*\<^sup>* (p, q, r) (p, {#}, q + r)\<close>
  apply (induction q arbitrary: r)
  subgoal by auto
  subgoal
    by (metis (no_types, lifting) add_new_coeff_r r_into_rtranclp
      rtranclp_trans union_mset_add_mset_left union_mset_add_mset_right)
  done

lemma add_poly_p_sym:
  \<open>add_poly_p (p, q, r) (p', q', r') \<longleftrightarrow> add_poly_p (q, p, r) (q', p', r')\<close>
  apply (rule iffI)
  subgoal
    by (cases rule: add_poly_p.cases, assumption)
      (auto intro: add_poly_p.intros)
  subgoal
    by (cases rule: add_poly_p.cases, assumption)
      (auto intro: add_poly_p.intros)
  done

lemma wf_if_measure_in_wf:
  \<open>wf R \<Longrightarrow> (\<And>a b. (a, b) \<in> S \<Longrightarrow> (\<nu> a, \<nu> b)\<in>R) \<Longrightarrow> wf S\<close>
  by (metis in_inv_image wfE_min wfI_min wf_inv_image)

lemma lexn_n:
  \<open>n > 0 \<Longrightarrow> (x # xs, y # ys) \<in> lexn r n \<longleftrightarrow>
  (length xs = n-1 \<and> length ys = n-1) \<and> ((x, y) \<in> r \<or> (x = y \<and> (xs, ys) \<in> lexn r (n - 1)))\<close>
  apply (cases n)
   apply simp
  by (auto simp: map_prod_def image_iff lex_prod_def)

lemma wf_add_poly_p:
  \<open>wf {(x, y). add_poly_p y x}\<close>
  by (rule wf_if_measure_in_wf[where R = \<open>lexn less_than 3\<close> and
     \<nu> = \<open>\<lambda>(a,b,c). [size a , size b, size c]\<close>])
    (auto simp: add_poly_p.simps wf_lexn
     simp: lexn_n simp del: lexn.simps(2))

lemma mult_poly_by_monom_simps[simp]:
  \<open>mult_poly_by_monom t {#} = {#}\<close>
  \<open>mult_poly_by_monom t (ps + qs) =  mult_poly_by_monom t ps + mult_poly_by_monom t qs\<close>
  \<open>mult_poly_by_monom a (add_mset p ps) = add_mset (fst a + fst p, snd a * snd p) (mult_poly_by_monom a ps)\<close>
proof -
  interpret comp_fun_commute \<open>(\<lambda>xs. add_mset (xs + t))\<close> for t
    by standard auto
  show
    \<open>mult_poly_by_monom t (ps + qs) =  mult_poly_by_monom t ps + mult_poly_by_monom t qs\<close> for t
    by (induction ps)
      (auto simp: mult_poly_by_monom_def)
  show
    \<open>mult_poly_by_monom a (add_mset p ps) = add_mset (fst a + fst p, snd a * snd p) (mult_poly_by_monom a ps)\<close>
    \<open>mult_poly_by_monom t {#} = {#}\<close>for t
    by (auto simp: mult_poly_by_monom_def)
qed

inductive mult_poly_p :: \<open>mset_polynomial \<Rightarrow> mset_polynomial \<times> mset_polynomial \<Rightarrow> mset_polynomial \<times> mset_polynomial \<Rightarrow> bool\<close>
  for q :: mset_polynomial where
mult_step:
    \<open>mult_poly_p q (add_mset (xs, n) p, r) (p, (\<lambda>(ys, m). (remdups_mset (xs + ys), n * m)) `# q + r)\<close>


lemmas mult_poly_p_induct = mult_poly_p.induct[split_format(complete)]

subsection \<open>Normalisation\<close>

inductive normalize_poly_p :: \<open>mset_polynomial \<Rightarrow> mset_polynomial \<Rightarrow> bool\<close>where
rem_0_coeff[simp, intro]:
    \<open>normalize_poly_p p q \<Longrightarrow> normalize_poly_p (add_mset (xs, 0) p) q\<close> |
merge_dup_coeff[simp, intro]:
    \<open>normalize_poly_p p q \<Longrightarrow> normalize_poly_p (add_mset (xs, m) (add_mset (xs, n) p)) (add_mset (xs, m + n) q)\<close> |
same[simp, intro]:
    \<open>normalize_poly_p p p\<close> |
keep_coeff[simp, intro]:
    \<open>normalize_poly_p p q \<Longrightarrow> normalize_poly_p (add_mset x p) (add_mset x q)\<close>


subsection \<open>Correctness\<close>
text \<open>
  This locales maps string polynomials to real polynomials.
\<close>
locale poly_embed =
  fixes \<phi> :: \<open>string \<Rightarrow> nat\<close>
  assumes \<phi>_inj: \<open>inj \<phi>\<close>
begin

definition poly_of_vars :: "term_poly \<Rightarrow> ('a :: {comm_semiring_1}) mpoly" where
  \<open>poly_of_vars xs = fold_mset (\<lambda>a b. Var (\<phi> a) * b) (1 :: 'a mpoly) xs\<close>

lemma poly_of_vars_simps[simp]:
  shows
    \<open>poly_of_vars (add_mset x xs) = Var (\<phi> x) * (poly_of_vars xs :: ('a :: {comm_semiring_1}) mpoly)\<close> (is ?A) and
    \<open>poly_of_vars (xs + ys) = poly_of_vars xs * (poly_of_vars ys :: ('a :: {comm_semiring_1}) mpoly)\<close> (is ?B)
proof -
  interpret comp_fun_commute \<open>(\<lambda>a b. (b :: 'a :: {comm_semiring_1} mpoly) * Var (\<phi> a))\<close>
    by standard
      (auto simp: algebra_simps ac_simps
         Var_def times_monomial_monomial intro!: ext)

  show ?A
    by (auto simp: poly_of_vars_def comp_fun_commute_axioms fold_mset_fusion
      ac_simps)
  show ?B
    apply (auto simp: poly_of_vars_def ac_simps)
    by (simp add: local.comp_fun_commute_axioms local.fold_mset_fusion
      semiring_normalization_rules(18))
qed


definition mononom_of_vars where
  \<open>mononom_of_vars \<equiv> (\<lambda>(xs, n). (+) (Const n * poly_of_vars xs))\<close>

interpretation comp_fun_commute \<open>mononom_of_vars\<close>
  by standard
    (auto simp: algebra_simps ac_simps mononom_of_vars_def
       Var_def times_monomial_monomial intro!: ext)

lemma [simp]:
  \<open>poly_of_vars {#} = 1\<close>
  by (auto simp: poly_of_vars_def)

lemma mononom_of_vars_add[simp]:
  \<open>NO_MATCH 0 b \<Longrightarrow> mononom_of_vars xs b = Const (snd xs) * poly_of_vars (fst xs) + b\<close>
  by (cases xs)
    (auto simp: ac_simps mononom_of_vars_def)

definition polynomial_of_mset :: \<open>mset_polynomial \<Rightarrow> _\<close> where
  \<open>polynomial_of_mset p = sum_mset (mononom_of_vars `# p) 0\<close>

lemma polynomial_of_mset_append[simp]:
  \<open>polynomial_of_mset (xs + ys) = polynomial_of_mset xs + polynomial_of_mset ys\<close>
  by (auto simp: ac_simps Const_def polynomial_of_mset_def)

lemma polynomial_of_mset_Cons[simp]:
  \<open>polynomial_of_mset (add_mset x ys) = Const (snd x) * poly_of_vars (fst x) + polynomial_of_mset ys\<close>
  by (cases x)
    (auto simp: ac_simps polynomial_of_mset_def mononom_of_vars_def)

lemma polynomial_of_mset_empty[simp]:
  \<open>polynomial_of_mset {#} = 0\<close>
  by (auto simp: polynomial_of_mset_def)

lemma polynomial_of_mset_mult_poly_by_monom[simp]:
  \<open>polynomial_of_mset (mult_poly_by_monom x ys) =
       (Const (snd x) * poly_of_vars (fst x) * polynomial_of_mset ys)\<close>
 by (induction ys)
   (auto simp: Const_mult algebra_simps)

lemma polynomial_of_mset_mult_poly_raw[simp]:
  \<open>polynomial_of_mset (mult_poly_raw xs ys) = polynomial_of_mset xs * polynomial_of_mset ys\<close>
  unfolding mult_poly_raw_def
  by (induction xs arbitrary: ys)
   (auto simp: Const_mult algebra_simps)

lemma polynomial_of_mset_uminus:
  \<open>polynomial_of_mset {#case x of (a, b) \<Rightarrow> (a, - b). x \<in># za#} =
    - polynomial_of_mset za\<close>
  by (induction za)
    auto


lemma X2_X_polynomial_bool_mult_in:
  \<open>Var (x1) * (Var (x1) * p) -  Var (x1) * p \<in> More_Modules.ideal polynomial_bool\<close>
  using ideal_mult_right_in[OF  X2_X_in_pac_ideal[of x1 \<open>{}\<close>, unfolded pac_ideal_def], of p]
  by (auto simp: right_diff_distrib ac_simps power2_eq_square)


lemma polynomial_of_list_remove_powers_polynomial_bool:
  \<open>(polynomial_of_mset xs) - polynomial_of_mset (remove_powers xs) \<in> ideal polynomial_bool\<close>
proof (induction xs)
  case empty
  then show \<open>?case\<close> by (auto simp: remove_powers_def ideal.span_zero)
next
  case (add x xs)
  have H1: \<open>x1 \<in># x2 \<Longrightarrow>
       Var (\<phi> x1) * poly_of_vars x2 - p \<in> More_Modules.ideal polynomial_bool \<longleftrightarrow>
       poly_of_vars x2 - p \<in> More_Modules.ideal polynomial_bool
       \<close> for x1 x2 p
    apply (subst (2) ideal.span_add_eq[symmetric,
      of \<open>Var (\<phi> x1) * poly_of_vars x2 - poly_of_vars x2\<close>])
    apply (drule multi_member_split)
    apply (auto simp: X2_X_polynomial_bool_mult_in)
    done

  have diff: \<open>poly_of_vars (x) - poly_of_vars (remdups_mset (x)) \<in> ideal polynomial_bool\<close> for x
    by (induction x)
     (auto simp: remove_powers_def ideal.span_zero H1
      simp flip: right_diff_distrib intro!: ideal.span_scale)
  have [simp]: \<open>polynomial_of_mset xs -
    polynomial_of_mset (apfst remdups_mset `# xs)
    \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
    poly_of_vars ys * poly_of_vars ys -
    poly_of_vars ys * poly_of_vars (remdups_mset ys)
    \<in> More_Modules.ideal polynomial_bool \<Longrightarrow>
    polynomial_of_mset xs + Const y * poly_of_vars ys -
    (polynomial_of_mset (apfst remdups_mset `# xs) +
    Const y * poly_of_vars (remdups_mset ys))
    \<in> More_Modules.ideal polynomial_bool\<close> for y ys
    by (metis add_diff_add diff ideal.scale_right_diff_distrib ideal.span_add ideal.span_scale)
  show ?case
    using add
    apply (cases x)
    subgoal for ys y
      using ideal_mult_right_in2[OF diff, of \<open>poly_of_vars ys\<close> ys]
      by (auto simp: remove_powers_def right_diff_distrib
        ideal.span_diff ideal.span_add field_simps)
    done
qed

lemma add_poly_p_polynomial_of_mset:
  \<open>add_poly_p (p, q, r) (p', q', r') \<Longrightarrow>
    polynomial_of_mset r + (polynomial_of_mset p + polynomial_of_mset q) =
    polynomial_of_mset r' + (polynomial_of_mset p' + polynomial_of_mset q')\<close>
  apply (induction rule: add_poly_p_induct)
  subgoal
    by auto
  subgoal
    by auto
  subgoal
    by (auto simp: algebra_simps Const_add)
  subgoal
    by (auto simp: algebra_simps Const_add)
  subgoal
    by (auto simp: algebra_simps Const_add)
  done

lemma rtranclp_add_poly_p_polynomial_of_mset:
  \<open>add_poly_p\<^sup>*\<^sup>* (p, q, r) (p', q', r') \<Longrightarrow>
    polynomial_of_mset r + (polynomial_of_mset p + polynomial_of_mset q) =
    polynomial_of_mset r' + (polynomial_of_mset p' + polynomial_of_mset q')\<close>
  by (induction rule: rtranclp_induct[of add_poly_p \<open>(_, _, _)\<close> \<open>(_, _, _)\<close>, split_format(complete), of for r])
    (auto dest: add_poly_p_polynomial_of_mset)


lemma rtranclp_add_poly_p_polynomial_of_mset_full:
  \<open>add_poly_p\<^sup>*\<^sup>* (p, q, {#}) ({#}, {#}, r') \<Longrightarrow>
    polynomial_of_mset r' = (polynomial_of_mset p + polynomial_of_mset q)\<close>
  by (drule rtranclp_add_poly_p_polynomial_of_mset)
    (auto simp: ac_simps add_eq_0_iff)

lemma poly_of_vars_remdups_mset:
  \<open>poly_of_vars (remdups_mset (xs)) - (poly_of_vars xs)
    \<in> More_Modules.ideal polynomial_bool\<close>
  apply (induction xs)
  subgoal by (auto simp: ideal.span_zero)
  subgoal for x xs
    apply (cases \<open>x \<in># xs\<close>)
     apply (metis (no_types, lifting) X2_X_polynomial_bool_mult_in diff_add_cancel diff_diff_eq2
        ideal.span_diff insert_DiffM poly_of_vars_simps(1) remdups_mset_singleton_sum)
    by (metis (no_types, lifting) ideal.span_scale poly_of_vars_simps(1) remdups_mset_singleton_sum
        right_diff_distrib)
  done

lemma polynomial_of_mset_mult_map:
  \<open>polynomial_of_mset
     {#case x of (ys, n) \<Rightarrow> (remdups_mset (ys + xs), n * m). x \<in># q#} -
    Const m * (poly_of_vars xs * polynomial_of_mset q)
    \<in> More_Modules.ideal polynomial_bool\<close>
  (is \<open>?P q \<in> _\<close>)
proof (induction q)
  case empty
  then show ?case by (auto simp: algebra_simps ideal.span_zero)
next
  case (add x q)
  then have uP:  \<open>-?P q \<in> More_Modules.ideal polynomial_bool\<close>
    using ideal.span_neg by blast
  have \<open> Const b * (Const m * poly_of_vars (remdups_mset (a + xs))) -
           Const b * (Const m * (poly_of_vars a * poly_of_vars xs))
           \<in> More_Modules.ideal polynomial_bool\<close> for a b
    by (auto simp: Const_mult simp flip: right_diff_distrib' poly_of_vars_simps
        intro!: ideal.span_scale poly_of_vars_remdups_mset)
  then show ?case
    apply (subst ideal.span_add_eq2[symmetric, OF uP])
    apply (cases x)
    apply (auto simp: field_simps Const_mult  simp flip:
        intro!: ideal.span_scale poly_of_vars_remdups_mset)
    done
qed

lemma mult_poly_p_mult_ideal:
  \<open>mult_poly_p q (p, r) (p', r') \<Longrightarrow>
     (polynomial_of_mset p' * polynomial_of_mset q + polynomial_of_mset r') - (polynomial_of_mset p * polynomial_of_mset q + polynomial_of_mset r)
       \<in> ideal polynomial_bool\<close>
proof (induction rule: mult_poly_p_induct)
  case (mult_step xs n p r)
  show ?case
    by (auto simp: algebra_simps polynomial_of_mset_mult_map)
qed

lemma rtranclp_mult_poly_p_mult_ideal:
  \<open>(mult_poly_p q)\<^sup>*\<^sup>* (p, r) (p', r') \<Longrightarrow>
     (polynomial_of_mset p' * polynomial_of_mset q + polynomial_of_mset r') - (polynomial_of_mset p * polynomial_of_mset q + polynomial_of_mset r)
       \<in> ideal polynomial_bool\<close>
  apply (induction p' r' rule: rtranclp_induct[of \<open>mult_poly_p q\<close> \<open>(p, r)\<close> \<open>(p', q')\<close> for p' q', split_format(complete)])
  subgoal
    by (auto simp: ideal.span_zero)
  subgoal for a b aa ba
    apply (drule mult_poly_p_mult_ideal)
    apply (drule ideal.span_add)
    apply assumption
    by (auto simp: group_add_class.diff_add_eq_diff_diff_swap
        add.inverse_distrib_swap ac_simps add_diff_eq
      simp flip:  diff_add_eq_diff_diff_swap)
  done

lemma rtranclp_mult_poly_p_mult_ideal_final:
  \<open>(mult_poly_p q)\<^sup>*\<^sup>* (p, {#}) ({#}, r) \<Longrightarrow>
    (polynomial_of_mset r) - (polynomial_of_mset p * polynomial_of_mset q)
       \<in> ideal polynomial_bool\<close>
  by (drule rtranclp_mult_poly_p_mult_ideal) auto

lemma normalize_poly_p_poly_of_mset:
  \<open>normalize_poly_p p q \<Longrightarrow> polynomial_of_mset p = polynomial_of_mset q\<close>
  apply (induction rule: normalize_poly_p.induct)
  apply (auto simp: Const_add algebra_simps)
  done


lemma rtranclp_normalize_poly_p_poly_of_mset:
  \<open>normalize_poly_p\<^sup>*\<^sup>* p q \<Longrightarrow> polynomial_of_mset p = polynomial_of_mset q\<close>
  by (induction rule: rtranclp_induct)
    (auto simp: normalize_poly_p_poly_of_mset)

end


text \<open>It would be nice to have the property in the other direction too, but this requires a deep
dive into the definitions of polynomials.\<close>
locale poly_embed_bij = poly_embed +
  fixes V N
  assumes \<phi>_bij: \<open>bij_betw \<phi> V N\<close>
begin

definition \<phi>' :: \<open>nat \<Rightarrow> string\<close> where
  \<open>\<phi>' = the_inv_into V \<phi>\<close>

lemma \<phi>'_\<phi>[simp]:
  \<open>x \<in> V \<Longrightarrow> \<phi>' (\<phi> x) = x\<close>
  using \<phi>_bij unfolding \<phi>'_def
  by (meson bij_betw_imp_inj_on the_inv_into_f_f)

lemma \<phi>_\<phi>'[simp]:
  \<open>x \<in> N \<Longrightarrow> \<phi> (\<phi>' x) = x\<close>
  using \<phi>_bij unfolding \<phi>'_def
  by (meson f_the_inv_into_f_bij_betw)

end

end

