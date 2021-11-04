(*
  File:         PAC_Specification.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory PAC_Specification
  imports PAC_More_Poly
begin


section \<open>Specification of the PAC checker\<close>

subsection \<open>Ideals\<close>

type_synonym int_poly = \<open>int mpoly\<close>
definition polynomial_bool :: \<open>int_poly set\<close> where
  \<open>polynomial_bool = (\<lambda>c. Var c ^ 2 - Var c) ` UNIV\<close>

definition pac_ideal where
  \<open>pac_ideal A \<equiv> ideal (A \<union> polynomial_bool)\<close>

lemma X2_X_in_pac_ideal:
  \<open>Var c ^ 2 - Var c \<in> pac_ideal A\<close>
  unfolding polynomial_bool_def pac_ideal_def
  by (auto intro: ideal.span_base)

lemma pac_idealI1[intro]:
  \<open>p \<in> A \<Longrightarrow> p \<in> pac_ideal A\<close>
  unfolding pac_ideal_def
  by (auto intro: ideal.span_base)

lemma pac_idealI2[intro]:
  \<open>p \<in> ideal A \<Longrightarrow> p \<in> pac_ideal A\<close>
  using ideal.span_subspace_induct pac_ideal_def by blast

lemma pac_idealI3[intro]:
  \<open>p \<in> ideal A \<Longrightarrow> p*q \<in> pac_ideal A\<close>
  by (metis ideal.span_scale mult.commute pac_idealI2)

lemma pac_ideal_Xsq2_iff:
  \<open>Var c ^ 2 \<in> pac_ideal A \<longleftrightarrow> Var c \<in> pac_ideal A\<close>
  unfolding pac_ideal_def
  apply (subst (2) ideal.span_add_eq[symmetric, OF X2_X_in_pac_ideal[of c, unfolded pac_ideal_def]])
  apply auto
  done

lemma diff_in_polynomial_bool_pac_idealI:
   assumes a1: "p \<in> pac_ideal A"
   assumes a2: "p - p' \<in> More_Modules.ideal polynomial_bool"
   shows \<open>p' \<in> pac_ideal A\<close>
 proof -
   have "insert p polynomial_bool \<subseteq> pac_ideal A"
     using a1 unfolding pac_ideal_def by (meson ideal.span_superset insert_subset le_sup_iff)
   then show ?thesis
     using a2 unfolding pac_ideal_def by (metis (no_types) ideal.eq_span_insert_eq ideal.span_subset_spanI ideal.span_superset insert_subset subsetD)
qed

lemma diff_in_polynomial_bool_pac_idealI2:
   assumes a1: "p \<in> A"
   assumes a2: "p - p' \<in> More_Modules.ideal polynomial_bool"
   shows \<open>p' \<in> pac_ideal A\<close>
   using diff_in_polynomial_bool_pac_idealI[OF _ assms(2), of A] assms(1)
   by (auto simp: ideal.span_base)

lemma pac_ideal_alt_def:
  \<open>pac_ideal A = ideal (A \<union> ideal polynomial_bool)\<close>
  unfolding pac_ideal_def
  by (meson ideal.span_eq ideal.span_mono ideal.span_superset le_sup_iff subset_trans sup_ge2)

text \<open>

  The equality on ideals is restricted to polynomials whose variable
  appear in the set of ideals. The function restrict sets:

\<close>
definition restricted_ideal_to where
  \<open>restricted_ideal_to B A = {p \<in> A. vars p  \<subseteq> B}\<close>

abbreviation restricted_ideal_to\<^sub>I where
  \<open>restricted_ideal_to\<^sub>I B A \<equiv> restricted_ideal_to B (pac_ideal (set_mset A))\<close>

abbreviation restricted_ideal_to\<^sub>V where
  \<open>restricted_ideal_to\<^sub>V B \<equiv> restricted_ideal_to (\<Union>(vars ` set_mset B))\<close>

abbreviation restricted_ideal_to\<^sub>V\<^sub>I where
  \<open>restricted_ideal_to\<^sub>V\<^sub>I B A \<equiv> restricted_ideal_to (\<Union>(vars ` set_mset B)) (pac_ideal (set_mset A))\<close>


lemma restricted_idealI:
  \<open>p \<in> pac_ideal (set_mset A) \<Longrightarrow> vars p \<subseteq> C \<Longrightarrow> p \<in> restricted_ideal_to\<^sub>I C A\<close>
  unfolding restricted_ideal_to_def
  by auto

lemma pac_ideal_insert_already_in:
  \<open>pq \<in> pac_ideal (set_mset A) \<Longrightarrow> pac_ideal (insert pq (set_mset A)) = pac_ideal (set_mset A)\<close>
  by (auto simp: pac_ideal_alt_def ideal.span_insert_idI)

lemma pac_ideal_add:
  \<open>p \<in># A \<Longrightarrow> q \<in># A \<Longrightarrow> p + q \<in> pac_ideal (set_mset A)\<close>
  by (simp add: ideal.span_add ideal.span_base pac_ideal_def)
lemma pac_ideal_mult:
  \<open>p \<in># A \<Longrightarrow> p * q \<in> pac_ideal (set_mset A)\<close>
  by (simp add: ideal.span_base pac_idealI3)

lemma pac_ideal_mono:
  \<open>A \<subseteq> B \<Longrightarrow> pac_ideal A \<subseteq> pac_ideal B\<close>
  using ideal.span_mono[of \<open>A \<union> _\<close> \<open>B \<union> _\<close>]
  by (auto simp: pac_ideal_def intro: ideal.span_mono)


subsection \<open>PAC Format\<close>

text \<open>The PAC format contains three kind of steps:
  \<^item> \<^verbatim>\<open>add\<close> that adds up two polynomials that are known.
  \<^item> \<^verbatim>\<open>mult\<close> that multiply a known polynomial with another one.
  \<^item> \<^verbatim>\<open>del\<close> that removes a polynomial that cannot be reused anymore.

To model the simplification that happens, we add the \<^term>\<open>p - p' \<in> polynomial_bool\<close>
stating that \<^term>\<open>p\<close> and  \<^term>\<open>p'\<close> are equivalent.
\<close>

type_synonym pac_st = \<open>(nat set \<times> int_poly multiset)\<close>

inductive PAC_Format :: \<open>pac_st \<Rightarrow> pac_st \<Rightarrow> bool\<close> where
add:
  \<open>PAC_Format (\<V>, A) (\<V>, add_mset p' A)\<close>
if
   \<open>p \<in># A\<close> \<open>q \<in># A\<close>
   \<open>p+q - p' \<in> ideal polynomial_bool\<close>
   \<open>vars p' \<subseteq> \<V>\<close> |
mult:
  \<open>PAC_Format (\<V>, A) (\<V>, add_mset p' A)\<close>
if
   \<open>p \<in># A\<close>
   \<open>p*q - p' \<in> ideal polynomial_bool\<close>
   \<open>vars p' \<subseteq> \<V>\<close>
   \<open>vars q \<subseteq> \<V>\<close> |
del:
   \<open>p \<in># A \<Longrightarrow> PAC_Format (\<V>, A) (\<V>, A - {#p#})\<close> |
extend_pos:
  \<open>PAC_Format (\<V>, A) (\<V> \<union> {x' \<in> vars (-Var x + p'). x' \<notin> \<V>}, add_mset (-Var x + p') A)\<close>
  if
    \<open>(p')\<^sup>2 - p' \<in> ideal polynomial_bool\<close>
    \<open>vars p' \<subseteq> \<V>\<close>
    \<open>x \<notin> \<V>\<close>

text  \<open>
  In the PAC format above, we have a technical condition on the
  normalisation: \<^term>\<open>vars p' \<subseteq> vars (p + q)\<close> is here to ensure that
  we don't normalise \<^term>\<open>0 :: int mpoly\<close> to  \<^term>\<open>Var x^2 - Var x :: int mpoly\<close>
  for a new variable \<^term>\<open>x :: nat\<close>. This is completely obvious for the normalisation
  process we have in mind when we write the specification, but we must add it
  explicitly because we are too general.
\<close>

lemmas  PAC_Format_induct_split =
   PAC_Format.induct[split_format(complete), of V A V' A' for V A V' A']

lemma PAC_Format_induct[consumes 1, case_names add mult del ext]:
  assumes
    \<open>PAC_Format (\<V>, A) (\<V>', A')\<close> and
    cases:
      \<open>\<And>p q p'  A \<V>. p \<in># A \<Longrightarrow> q \<in># A \<Longrightarrow> p+q - p' \<in> ideal polynomial_bool \<Longrightarrow> vars p' \<subseteq> \<V> \<Longrightarrow> P \<V> A \<V> (add_mset p' A)\<close>
      \<open>\<And>p q p' A \<V>. p \<in># A \<Longrightarrow> p*q - p' \<in> ideal polynomial_bool \<Longrightarrow> vars p' \<subseteq> \<V> \<Longrightarrow> vars q \<subseteq> \<V> \<Longrightarrow>
        P \<V> A \<V> (add_mset p' A)\<close>
      \<open>\<And>p A \<V>. p \<in># A \<Longrightarrow> P \<V> A \<V> (A - {#p#})\<close>
      \<open>\<And>p' x r.
        (p')^2 - (p') \<in> ideal polynomial_bool \<Longrightarrow> vars p' \<subseteq> \<V> \<Longrightarrow>
        x \<notin> \<V> \<Longrightarrow> P \<V> A (\<V> \<union> {x' \<in> vars (p' - Var x). x' \<notin> \<V>}) (add_mset (p' -Var x) A)\<close>
  shows
     \<open>P \<V> A \<V>' A'\<close>
  using assms(1) apply -
  by (induct V\<equiv>\<V> A\<equiv>A \<V>' A' rule: PAC_Format_induct_split)
   (auto intro: assms(1) cases)


text \<open>

The theorem below (based on the proof ideal by Manuel Kauers) is the
correctness theorem of extensions. Remark that the assumption \<^term>\<open>vars
q \<subseteq> \<V>\<close> is only used to show that \<^term>\<open>x' \<notin> vars q\<close>.

\<close>
lemma extensions_are_safe:
  assumes \<open>x' \<in> vars p\<close> and
    x': \<open>x' \<notin> \<V>\<close> and
    \<open>\<Union> (vars ` set_mset A) \<subseteq> \<V>\<close> and
    p_x_coeff: \<open>coeff p (monomial (Suc 0) x') = 1\<close> and
    vars_q: \<open>vars q \<subseteq> \<V>\<close> and
    q: \<open>q \<in> More_Modules.ideal (insert p (set_mset A \<union> polynomial_bool))\<close> and
    leading: \<open>x' \<notin> vars (p - Var x')\<close> and
    diff: \<open>(Var x' - p)\<^sup>2 - (Var x' - p) \<in> More_Modules.ideal polynomial_bool\<close>
  shows
    \<open>q \<in> More_Modules.ideal (set_mset A \<union> polynomial_bool)\<close>
proof -
  define p' where \<open>p' \<equiv> p - Var x'\<close>
  let ?v = \<open>Var x' :: int mpoly\<close>
  have p_p': \<open>p = ?v + p'\<close>
    by (auto simp: p'_def)
  define q' where \<open>q' \<equiv> Var x' - p\<close>
  have q_q': \<open>p = ?v - q'\<close>
    by (auto simp: q'_def)
  have diff: \<open>q'^2 - q' \<in> More_Modules.ideal polynomial_bool\<close>
    using diff unfolding q_q' by auto

  have [simp]: \<open>vars ((Var c)\<^sup>2 - Var c :: int mpoly) = {c}\<close> for c
    apply (auto simp: vars_def Var_def Var\<^sub>0_def mpoly.MPoly_inverse keys_def lookup_minus_fun
      lookup_times_monomial_right single.rep_eq split: if_splits)
    apply (auto simp: vars_def Var_def Var\<^sub>0_def mpoly.MPoly_inverse keys_def lookup_minus_fun
      lookup_times_monomial_right single.rep_eq when_def ac_simps adds_def lookup_plus_fun
      power2_eq_square times_mpoly.rep_eq minus_mpoly.rep_eq split: if_splits)
    apply (rule_tac x = \<open>(2 :: nat \<Rightarrow>\<^sub>0 nat) * monomial (Suc 0) c\<close> in exI)
    apply (auto dest: monomial_0D simp: plus_eq_zero_2 lookup_plus_fun mult_2)
    by (meson Suc_neq_Zero monomial_0D plus_eq_zero_2)


  have eq: \<open>More_Modules.ideal (insert p (set_mset A \<union> polynomial_bool)) =
      More_Modules.ideal (insert p (set_mset A \<union> (\<lambda>c. Var c ^ 2 - Var c) ` {c. c \<noteq> x'}))\<close>
      (is \<open>?A = ?B\<close> is \<open>_ = More_Modules.ideal ?trimmed\<close>)
  proof -
     let ?C = \<open>insert p (set_mset A \<union> (\<lambda>c. Var c ^ 2 - Var c) ` {c. c \<noteq> x'})\<close>
     let ?D = \<open>(\<lambda>c. Var c ^ 2 - Var c) ` {c. c \<noteq> x'}\<close>
     have diff: \<open>q'^2 - q' \<in> More_Modules.ideal ?D\<close> (is \<open>?q \<in> _\<close>)
     proof -
       obtain r t where
         q: \<open>?q = (\<Sum>a\<in>t. r a * a)\<close> and
         fin_t: \<open>finite t\<close> and
         t: \<open>t \<subseteq> polynomial_bool\<close>
         using diff unfolding ideal.span_explicit
         by auto
       show ?thesis
       proof (cases \<open>?v^2-?v \<notin> t\<close>)
         case True
         then show \<open>?thesis\<close>
           using q fin_t t unfolding ideal.span_explicit
           by (auto intro!: exI[of _ \<open>t - {?v^2 -?v}\<close>] exI[of _ r]
             simp: polynomial_bool_def sum_diff1)
        next
          case False
          define t' where \<open>t' = t - {?v^2 - ?v}\<close>
          have t_t': \<open>t = insert (?v^2 - ?v) t'\<close> and
            notin: \<open>?v^2 - ?v \<notin> t'\<close> and
            \<open>t' \<subseteq> (\<lambda>c. Var c ^ 2 - Var c) ` {c. c \<noteq> x'}\<close>
            using False t unfolding t'_def polynomial_bool_def by auto
          have mon: \<open>monom (monomial (Suc 0) x') 1 = Var x'\<close>
            by (auto simp: coeff_def minus_mpoly.rep_eq Var_def Var\<^sub>0_def monom_def
              times_mpoly.rep_eq lookup_minus lookup_times_monomial_right mpoly.MPoly_inverse)
          then have \<open>\<forall>a. \<exists>g h. r a = ?v * g + h \<and> x' \<notin> vars h\<close>
            using polynomial_split_on_var[of \<open>r _\<close> x']
            by metis
          then obtain g h where
            r: \<open>r a = ?v * g a + h a\<close> and
            x'_h: \<open>x' \<notin> vars (h a)\<close> for a
            using polynomial_split_on_var[of \<open>r a\<close> x']
            by metis
          have  \<open>?q = ((\<Sum>a\<in>t'. g a * a) + r (?v^2-?v) * (?v - 1)) * ?v + (\<Sum>a\<in>t'. h a * a)\<close>
            using fin_t notin unfolding t_t' q r
            by (auto simp: field_simps comm_monoid_add_class.sum.distrib
              power2_eq_square ideal.scale_left_commute sum_distrib_left)
          moreover have \<open>x' \<notin> vars ?q\<close>
            by (metis (no_types, hide_lams) Groups.add_ac(2) Un_iff add_diff_cancel_left'
              diff_minus_eq_add in_mono leading q'_def semiring_normalization_rules(29)
              vars_in_right_only vars_mult)
          moreover {
            have \<open>x' \<notin> (\<Union>m\<in>t' - {?v^2-?v}. vars (h m * m))\<close>
              using fin_t x'_h vars_mult[of \<open>h _\<close>] \<open>t \<subseteq> polynomial_bool\<close>
              by (auto simp: polynomial_bool_def t_t' elim!: vars_unE)
            then have \<open>x' \<notin> vars (\<Sum>a\<in>t'. h a * a)\<close>
              using vars_setsum[of \<open>t'\<close> \<open>\<lambda>a. h a * a\<close>] fin_t x'_h t notin
              by (auto simp: t_t')
          }
          ultimately have \<open>?q = (\<Sum>a\<in>t'. h a * a)\<close>
            unfolding mon[symmetric]
            by (rule polynomial_decomp_alien_var(2)[unfolded])
          then show ?thesis
            using t fin_t \<open>t' \<subseteq> (\<lambda>c. Var c ^ 2 - Var c) ` {c. c \<noteq> x'}\<close>
            unfolding ideal.span_explicit t_t'
            by auto
       qed
    qed
    have eq1: \<open>More_Modules.ideal (insert p (set_mset A \<union> polynomial_bool)) =
      More_Modules.ideal (insert (?v^2 - ?v) ?C)\<close>
      (is \<open>More_Modules.ideal _ = More_Modules.ideal (insert _ ?C)\<close>)
      by (rule arg_cong[of _ _ More_Modules.ideal])
       (auto simp: polynomial_bool_def)
    moreover have \<open>?v^2 - ?v \<in> More_Modules.ideal ?C\<close>
    proof -
      have \<open>?v - q' \<in> More_Modules.ideal ?C\<close>
        by (auto simp: q_q' ideal.span_base)
      from ideal.span_scale[OF this, of \<open>?v + q' - 1\<close>] have \<open>(?v - q') * (?v + q' - 1) \<in> More_Modules.ideal ?C\<close>
        by (auto simp: field_simps)
      moreover have \<open>q'^2 - q' \<in> More_Modules.ideal ?C\<close>
        using diff by (smt Un_insert_right ideal.span_mono insert_subset subsetD sup_ge2)
      ultimately have \<open>(?v - q') * (?v + q' - 1) + (q'^2 - q') \<in> More_Modules.ideal ?C\<close>
        by (rule ideal.span_add)
      moreover have \<open>?v^2 - ?v = (?v - q') * (?v + q' - 1) + (q'^2 - q')\<close>
        by (auto simp: p'_def q_q' field_simps power2_eq_square)
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis
      using ideal.span_insert_idI by blast
  qed

  have \<open>n < m \<Longrightarrow> n > 0 \<Longrightarrow> \<exists>q. ?v^n = ?v + q * (?v^2 - ?v)\<close> for n m :: nat
  proof (induction m arbitrary: n)
    case 0
    then show ?case by auto
  next
    case (Suc m n) note IH = this(1-)
    consider
      \<open>n < m\<close> |
      \<open>m = n\<close> \<open>n > 1\<close> |
      \<open>n = 1\<close>
      using IH
      by (cases \<open>n < m\<close>; cases n) auto
    then show ?case
    proof cases
      case 1
      then show ?thesis using IH by auto
    next
      case 2
      have eq: \<open>?v^(n) = ((?v :: int mpoly) ^ (n-2)) * (?v^2-?v) + ?v^(n-1)\<close>
        using 2 by (auto simp: field_simps power_eq_if
          ideal.scale_right_diff_distrib)
      obtain q where
        q: \<open>?v^(n-1) = ?v + q * (?v^2 - ?v)\<close>
        using IH(1)[of \<open>n-1\<close>] 2
        by auto
      show ?thesis
        using q unfolding eq
        by (auto intro!: exI[of _ \<open>Var x' ^ (n - 2) + q\<close>] simp: distrib_right)
    next
      case 3
      then show \<open>?thesis\<close>
        by auto
    qed
  qed

  obtain r t where
    q: \<open>q = (\<Sum>a\<in>t. r a * a)\<close> and
    fin_t: \<open>finite t\<close> and
    t: \<open>t \<subseteq> ?trimmed\<close>
    using q unfolding eq unfolding ideal.span_explicit
    by auto


  define t' where \<open>t' \<equiv> t - {p}\<close>
  have t': \<open>t = (if p \<in> t then insert p t' else t')\<close> and
    t''[simp]: \<open>p \<notin> t'\<close>
    unfolding t'_def by auto
  show ?thesis
  proof (cases \<open>r p = 0 \<or> p \<notin> t\<close>)
    case True
    have
      q: \<open>q = (\<Sum>a\<in>t'. r a * a)\<close> and
     fin_t: \<open>finite t'\<close> and
      t: \<open>t' \<subseteq> set_mset A \<union> polynomial_bool\<close>
      using q fin_t t True t''
      apply (subst (asm) t')
      apply (auto intro: sum.cong simp: sum.insert_remove t'_def)
      using q fin_t t True t''
      apply (auto intro: sum.cong simp: sum.insert_remove t'_def polynomial_bool_def)
      done
    then show ?thesis
      by (auto simp: ideal.span_explicit)
  next
    case False
    then have \<open>r p \<noteq> 0\<close> and \<open>p \<in> t\<close>
      by auto
    then have t: \<open>t = insert p t'\<close>
      by (auto simp: t'_def)

   have \<open>x' \<notin> vars (- p')\<close>
     using leading p'_def vars_in_right_only by fastforce
   have mon: \<open>monom (monomial (Suc 0) x') 1 = Var x'\<close>
     by (auto simp:coeff_def minus_mpoly.rep_eq Var_def Var\<^sub>0_def monom_def
       times_mpoly.rep_eq lookup_minus lookup_times_monomial_right mpoly.MPoly_inverse)
   then have \<open>\<forall>a. \<exists>g h. r a = (?v + p') * g + h \<and> x' \<notin> vars h\<close>
     using polynomial_split_on_var2[of x' \<open>-p'\<close> \<open>r _\<close>]  \<open>x' \<notin> vars (- p')\<close>
     by (metis diff_minus_eq_add)
   then obtain g h where
     r: \<open>r a = p * g a + h a\<close> and
     x'_h: \<open>x' \<notin> vars (h a)\<close> for a
     using polynomial_split_on_var2[of x' p' \<open>r a\<close>] unfolding p_p'[symmetric]
     by metis


  have ISABLLE_come_on: \<open>a * (p * g a) = p * (a * g a)\<close> for a
    by auto
  have q1: \<open>q = p * (\<Sum>a\<in>t'. g a * a) + (\<Sum>a\<in>t'. h a * a) + p * r p\<close>
    (is \<open>_ = _ + ?NOx' + _\<close>)
    using fin_t t'' unfolding q t ISABLLE_come_on r
    apply (subst semiring_class.distrib_right)+
    apply (auto simp: comm_monoid_add_class.sum.distrib semigroup_mult_class.mult.assoc
      ISABLLE_come_on simp flip: semiring_0_class.sum_distrib_right
         semiring_0_class.sum_distrib_left)
    by (auto simp: field_simps)
  also have \<open>... = ((\<Sum>a\<in>t'. g a * a) + r p) * p + (\<Sum>a\<in>t'. h a * a)\<close>
    by (auto simp: field_simps)
  finally have q_decomp: \<open>q = ((\<Sum>a\<in>t'. g a * a) + r p) * p + (\<Sum>a\<in>t'. h a * a)\<close>
    (is \<open>q = ?X * p + ?NOx'\<close>).


   have [iff]: \<open>monomial (Suc 0) c = 0 - monomial (Suc 0) c = False\<close> for c
     by (metis One_nat_def diff_is_0_eq' le_eq_less_or_eq less_Suc_eq_le monomial_0_iff single_diff zero_neq_one)
  have \<open>x \<in> t' \<Longrightarrow> x' \<in> vars x \<Longrightarrow> False\<close> for x
    using  \<open>t \<subseteq> ?trimmed\<close> t assms(2,3)
    apply (auto simp: polynomial_bool_def dest!: multi_member_split)
    apply (frule set_rev_mp)
    apply assumption
    apply (auto dest!: multi_member_split)
    done
   then have \<open>x' \<notin> (\<Union>m\<in>t'. vars (h m * m))\<close>
     using fin_t x'_h vars_mult[of \<open>h _\<close>]
     by (auto simp: t elim!: vars_unE)
   then have \<open>x' \<notin> vars ?NOx'\<close>
     using vars_setsum[of \<open>t'\<close> \<open>\<lambda>a. h a * a\<close>] fin_t x'_h
     by (auto simp: t)

  moreover {
    have \<open>x' \<notin> vars p'\<close>
      using assms(7)
      unfolding p'_def
      by auto
    then have \<open>x' \<notin> vars (h p * p')\<close>
      using vars_mult[of \<open>h p\<close> p'] x'_h
      by auto
  }
  ultimately have
    \<open>x' \<notin> vars q\<close>
    \<open>x' \<notin> vars ?NOx'\<close>
    \<open>x' \<notin> vars p'\<close>
    using x' vars_q vars_add[of \<open>h p * p'\<close> \<open>\<Sum>a\<in>t'. h a * a\<close>] x'_h
      leading p'_def
    by auto
  then have \<open>?X = 0\<close> and q_decomp: \<open>q = ?NOx'\<close>
    unfolding mon[symmetric] p_p'
    using polynomial_decomp_alien_var2[OF q_decomp[unfolded p_p' mon[symmetric]]]
    by auto

  then have \<open>r p = (\<Sum>a\<in>t'. (- g a) * a)\<close>
    (is \<open>_ = ?CL\<close>)
    unfolding add.assoc add_eq_0_iff equation_minus_iff
    by (auto simp: sum_negf ac_simps)


  then have q2: \<open>q = (\<Sum>a\<in>t'. a * (r a - p * g a))\<close>
    using fin_t unfolding q
    apply (auto simp: t r q
         comm_monoid_add_class.sum.distrib[symmetric]
         sum_distrib_left
         sum_distrib_right
         left_diff_distrib
        intro!: sum.cong)
    apply (auto simp: field_simps)
    done
  then show \<open>?thesis\<close>
    using t fin_t \<open>t \<subseteq> ?trimmed\<close> unfolding ideal.span_explicit
    by (auto intro!: exI[of _ t'] exI[of _ \<open>\<lambda>a. r a - p * g a\<close>]
      simp: field_simps polynomial_bool_def)
  qed
qed

lemma extensions_are_safe_uminus:
  assumes \<open>x' \<in> vars p\<close> and
    x': \<open>x' \<notin> \<V>\<close> and
    \<open>\<Union> (vars ` set_mset A) \<subseteq> \<V>\<close> and
    p_x_coeff: \<open>coeff p (monomial (Suc 0) x') = -1\<close> and
    vars_q: \<open>vars q \<subseteq> \<V>\<close> and
    q: \<open>q \<in> More_Modules.ideal (insert p (set_mset A \<union> polynomial_bool))\<close> and
    leading: \<open>x' \<notin> vars (p + Var x')\<close> and
    diff: \<open>(Var x' + p)^2 - (Var x' + p) \<in> More_Modules.ideal polynomial_bool\<close>
  shows
    \<open>q \<in> More_Modules.ideal (set_mset A \<union> polynomial_bool)\<close>
proof -
  have \<open>q \<in> More_Modules.ideal (insert (- p) (set_mset A \<union> polynomial_bool))\<close>
    by (metis ideal.span_breakdown_eq minus_mult_minus q)

  then show ?thesis
    using extensions_are_safe[of x' \<open>-p\<close> \<V> A q] assms
    using vars_in_right_only by force
qed

text \<open>This is the correctness theorem of a PAC step: no polynomials are
added to the ideal.\<close>

lemma vars_subst_in_left_only:
  \<open>x \<notin> vars p \<Longrightarrow> x \<in> vars (p - Var x)\<close> for p :: \<open>int mpoly\<close>
  by (metis One_nat_def Var.abs_eq Var\<^sub>0_def group_eq_aux monom.abs_eq mult_numeral_1 polynomial_decomp_alien_var(1) zero_neq_numeral)

lemma vars_subst_in_left_only_diff_iff:
  fixes p :: \<open>int mpoly\<close>
  assumes \<open>x \<notin> vars p\<close>
  shows \<open>vars (p - Var x) = insert x (vars p)\<close>
proof -
  have \<open>\<And>xa. x \<notin> vars p \<Longrightarrow> xa \<in> vars (p - Var x) \<Longrightarrow> xa \<notin> vars p \<Longrightarrow> xa = x\<close>
    by (metis (no_types, hide_lams) diff_0_right diff_minus_eq_add empty_iff in_vars_addE insert_iff
      keys_single minus_diff_eq monom_one mult.right_neutral one_neq_zero single_zero
      vars_monom_keys vars_mult_Var vars_uminus)
  moreover have \<open>\<And>xa. x \<notin> vars p \<Longrightarrow> xa \<in> vars p \<Longrightarrow> xa \<in> vars (p - Var x)\<close>
    by (metis add.inverse_inverse diff_minus_eq_add empty_iff insert_iff keys_single minus_diff_eq
      monom_one mult.right_neutral one_neq_zero single_zero vars_in_right_only vars_monom_keys
      vars_mult_Var vars_uminus)
  ultimately show ?thesis
    using assms
    by (auto simp: vars_subst_in_left_only)
qed

lemma vars_subst_in_left_only_iff:
  \<open>x \<notin> vars p \<Longrightarrow> vars (p + Var x) = insert x (vars p)\<close> for p :: \<open>int mpoly\<close>
  using vars_subst_in_left_only_diff_iff[of x \<open>-p\<close>]
  by (metis diff_0 diff_diff_add vars_uminus)

lemma coeff_add_right_notin:
  \<open>x \<notin> vars p \<Longrightarrow> MPoly_Type.coeff (Var x - p) (monomial (Suc 0) x) = 1\<close>
  apply (auto simp flip: coeff_minus simp: not_in_vars_coeff0)
  by (simp add: MPoly_Type.coeff_def Var.rep_eq Var\<^sub>0_def)

lemma coeff_add_left_notin:
  \<open>x \<notin> vars p \<Longrightarrow> MPoly_Type.coeff (p - Var x) (monomial (Suc 0) x) = -1\<close> for p :: \<open>int mpoly\<close>
  apply (auto simp flip: coeff_minus simp: not_in_vars_coeff0)
  by (simp add: MPoly_Type.coeff_def Var.rep_eq Var\<^sub>0_def)

lemma ideal_insert_polynomial_bool_swap: \<open>r - s \<in> ideal polynomial_bool \<Longrightarrow>
  More_Modules.ideal (insert r  (A \<union> polynomial_bool)) = More_Modules.ideal (insert s (A \<union> polynomial_bool))\<close>
  apply auto
  using ideal.eq_span_insert_eq ideal.span_mono sup_ge2 apply blast+
  done

lemma PAC_Format_subset_ideal:
  \<open>PAC_Format (\<V>, A) (\<V>', B) \<Longrightarrow> \<Union>(vars ` set_mset A) \<subseteq> \<V> \<Longrightarrow>
     restricted_ideal_to\<^sub>I \<V> B \<subseteq> restricted_ideal_to\<^sub>I \<V> A \<and> \<V> \<subseteq> \<V>' \<and> \<Union>(vars ` set_mset B) \<subseteq> \<V>'\<close>
  unfolding restricted_ideal_to_def
  apply (induction rule:PAC_Format_induct)
  subgoal for p q pq A \<V>
    using vars_add
    by (force simp: ideal.span_add_eq ideal.span_base pac_ideal_insert_already_in[OF diff_in_polynomial_bool_pac_idealI[of \<open>p + q\<close> \<open>_\<close> pq]]
        pac_ideal_add
      intro!: diff_in_polynomial_bool_pac_idealI[of \<open>p + q\<close> \<open>_\<close> pq])
  subgoal for p q pq
    using vars_mult[of p q]
    by (force simp: ideal.span_add_eq ideal.span_base pac_ideal_mult
      pac_ideal_insert_already_in[OF diff_in_polynomial_bool_pac_idealI[of \<open>p*q\<close> \<open>_\<close> pq]])
  subgoal for p A
    using pac_ideal_mono[of \<open>set_mset (A - {#p#})\<close> \<open>set_mset A\<close>]
    by (auto dest: in_diffD)
  subgoal for p x' r'
    apply (subgoal_tac \<open>x' \<notin> vars p\<close>)
    using extensions_are_safe_uminus[of x' \<open>-Var x' + p\<close> \<V> A] unfolding pac_ideal_def
    apply (auto simp: vars_subst_in_left_only coeff_add_left_notin)
    done
  done


text \<open>
  In general, if deletions are disallowed, then the stronger \<^term>\<open>B = pac_ideal A\<close> holds.
\<close>
lemma restricted_ideal_to_restricted_ideal_to\<^sub>ID:
  \<open>restricted_ideal_to \<V> (set_mset A) \<subseteq> restricted_ideal_to\<^sub>I \<V> A\<close>
   by (auto simp add: Collect_disj_eq pac_idealI1 restricted_ideal_to_def)


lemma rtranclp_PAC_Format_subset_ideal:
  \<open>rtranclp PAC_Format (\<V>, A) (\<V>', B) \<Longrightarrow> \<Union>(vars ` set_mset A) \<subseteq> \<V> \<Longrightarrow>
     restricted_ideal_to\<^sub>I \<V> B \<subseteq> restricted_ideal_to\<^sub>I \<V> A \<and> \<V> \<subseteq> \<V>' \<and> \<Union>(vars ` set_mset B) \<subseteq> \<V>'\<close>
  apply (induction rule:rtranclp_induct[of PAC_Format \<open>(_, _)\<close> \<open>(_, _)\<close>, split_format(complete)])
  subgoal
    by (simp add: restricted_ideal_to_restricted_ideal_to\<^sub>ID)
  subgoal
    by (drule PAC_Format_subset_ideal)
      (auto simp: restricted_ideal_to_def Collect_mono_iff)
  done


end