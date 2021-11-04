(*
   File:     Laws_of_Large_Numbers.thy
   Author:   Manuel Eberl, TU München
*)
section \<open>The Laws of Large Numbers\<close>
theory Laws_of_Large_Numbers
  imports Ergodic_Theory.Shift_Operator
begin

text \<open>
  We prove the strong law of large numbers in the following form: Let $(X_i)_{i\in\mathbb{N}}$
  be a sequence of i.i.d. random variables over a probability space \<open>M\<close>. Further assume that
  the expected value $E[X_0]$ of $X_0$ exists. Then the sequence of random variables
  \[\overline{X}_n = \frac{1}{n} \sum_{i=0}^n X_i\]
  of running averages almost surely converges to $E[X_0]$.
  This means that
  \[\mathcal{P}[\overline{X}_n \longrightarrow E[X_0]] = 1\ .\]

  We start with the strong law.
\<close>


subsection \<open>The strong law\<close>

text \<open>
  The proof uses Birkhoff's Theorem from Gouëzel's formalisation of ergodic theory~\cite{gouezel}
  and the fact that the shift operator $T(x_1, x_2, x_3, \ldots) = (x_2, x_3, \ldots)$ is ergodic.
  This proof can be found in various textbooks on probability theory/ergodic
  theory, e.g. the ones by Krengel~\cite[p.~24]{krengel} and
  Simmonet~\cite[Chapter 15, pp.~311--325]{Simonnet1996}.
\<close>
theorem (in prob_space) strong_law_of_large_numbers_iid:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes indep: "indep_vars (\<lambda>_. borel) X UNIV"
  assumes distr: "\<And>i. distr M borel (X i) = distr M borel (X 0)"
  assumes L1:    "integrable M (X 0)"
  shows "AE x in M. (\<lambda>n. (\<Sum>i<n. X i x) / n) \<longlonglongrightarrow> expectation (X 0)"
proof -
  text \<open>
    We adopt a more explicit view of \<^term>\<open>M\<close> as a countably infinite product of i.i.d.
    random variables, indexed by the natural numbers:
  \<close>
  define M' :: "(nat \<Rightarrow> real) measure" where "M' = Pi\<^sub>M UNIV (\<lambda>i. distr M borel (X i))"
  have [measurable]: "random_variable borel (X i)" for i
    using indep by (auto simp: indep_vars_def)
  have M'_eq: "M' = distr M (Pi\<^sub>M UNIV (\<lambda>i. borel)) (\<lambda>x. \<lambda>i\<in>UNIV. X i x)"
    using indep unfolding M'_def by (subst (asm) indep_vars_iff_distr_eq_PiM) auto
  have space_M': "space M' = UNIV"
    by (simp add: M'_def space_PiM)
  have sets_M' [measurable_cong]: "sets M' = sets (Pi\<^sub>M UNIV (\<lambda>i. borel))"
    by (simp add: M'_eq)
  interpret M': prob_space M'
    unfolding M'_eq by (intro prob_space_distr) auto

  text \<open>We introduce a shift operator that forgets the first variable in the sequence.\<close>
  define T :: "(nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> real)" where
    "T = (\<lambda>f. f \<circ> Suc)"
  have funpow_T: "(T ^^ i) = (\<lambda>f. f \<circ> (\<lambda>n. n + i))" for i
    by (induction i) (auto simp: T_def)

  interpret T: shift_operator_ergodic "distr M borel (X 0)" T M'
  proof -
    interpret X0: prob_space "distr M borel (X 0)"
      by (rule prob_space_distr) auto
    show "shift_operator_ergodic (distr M borel (X 0))"
      by unfold_locales
    show "M' \<equiv> Pi\<^sub>M UNIV (\<lambda>_. distr M borel (X 0)) "
      unfolding M'_def by (subst distr)
  qed (simp_all add: T_def)

  have [intro]: "integrable M' (\<lambda>f. f 0)"
    unfolding M'_eq by (subst integrable_distr_eq) (use L1 in auto)
  have "AE f in M'. (\<lambda>n. T.birkhoff_sum (\<lambda>f. f 0) n f / real n)
            \<longlonglongrightarrow> real_cond_exp M' T.Invariants (\<lambda>f. f 0) f"
    by (rule T.birkhoff_theorem_AE_nonergodic) auto
  moreover have "AE x in M'. real_cond_exp M' T.Invariants (\<lambda>f. f 0) x =
                    M'.expectation (\<lambda>f. f 0) / M'.prob (space M')"
    by (intro T.Invariants_cond_exp_is_integral_fmpt) auto
  ultimately have "AE f in M'. (\<lambda>n. T.birkhoff_sum (\<lambda>f. f 0) n f / real n)
                     \<longlonglongrightarrow> M'.expectation (\<lambda>f. f 0)"
    by eventually_elim (simp_all add: M'.prob_space)
  also have "M'.expectation (\<lambda>f. f 0) = expectation (X 0)"
    unfolding M'_eq by (subst integral_distr) simp_all
  also have "T.birkhoff_sum (\<lambda>f. f 0) = (\<lambda>n f. sum f {..<n})"
    by (intro ext) (simp_all add:T.birkhoff_sum_def funpow_T)
  finally show ?thesis
    unfolding M'_eq by (subst (asm) AE_distr_iff) simp_all
qed


subsection \<open>The weak law\<close>

text \<open>
  To go from the strong law to the weak one, we need the fact that almost sure convergence
  implies convergence in probability. We prove this for sequences of random variables here.
\<close>
lemma (in prob_space) AE_convergence_imp_convergence_in_prob:
  assumes [measurable]: "\<And>i. random_variable borel (X i)" "random_variable borel Y"
  assumes AE: "AE x in M. (\<lambda>i. X i x) \<longlonglongrightarrow> Y x"
  assumes "\<epsilon> > (0 :: real)"
  shows   "(\<lambda>i. prob {x\<in>space M. \<bar>X i x - Y x\<bar> > \<epsilon>}) \<longlonglongrightarrow> 0"
proof -
  define A where "A = (\<lambda>i. {x\<in>space M. \<bar>X i x - Y x\<bar> > \<epsilon>})"
  define B where "B = (\<lambda>n. (\<Union>i\<in>{n..}. A i))"
  have [measurable]: "A i \<in> sets M"  "B i \<in> sets M" for i
    unfolding A_def B_def by measurable

  have "AE x in M. x \<notin> (\<Inter>i. B i)"
    using AE unfolding B_def A_def
    by eventually_elim
       (use \<open>\<epsilon> > 0\<close> in \<open>fastforce simp: tendsto_iff dist_norm eventually_at_top_linorder\<close>)
  hence "(\<Inter>i. B i) \<in> null_sets M"
    by (subst AE_iff_null_sets) auto

  show "(\<lambda>i. prob (A i)) \<longlonglongrightarrow> 0"
  proof (rule Lim_null_comparison)
    have "(\<lambda>i. prob (B i)) \<longlonglongrightarrow> prob (\<Inter>i. B i)"
    proof (rule finite_Lim_measure_decseq)
      show "decseq B"
        by (rule decseq_SucI) (force simp: B_def)
    qed auto
    also have "prob (\<Inter>i. B i) = 0"
      using \<open>(\<Inter>i. B i) \<in> null_sets M\<close> by (simp add: measure_eq_0_null_sets)
    finally show "(\<lambda>i. prob (B i)) \<longlonglongrightarrow> 0" .
  next
    have "prob (A n) \<le> prob (B n)" for n
      unfolding B_def by (intro finite_measure_mono) auto
    thus "\<forall>\<^sub>F n in at_top. norm (prob (A n)) \<le> prob (B n)"
      by (intro always_eventually) auto
  qed
qed

text \<open>
  The weak law is now a simple corollary: we again have the same setting as before. The weak
  law now states that $\overline{X}_n$ converges to $E[X_0]$ in probability. This means that
  for any \<open>\<epsilon> > 0\<close>, the probability that $|\overline{X}_n - X_0| > \varepsilon$ vanishes as
  \<open>n \<rightarrow> \<infinity>\<close>.
\<close>
corollary (in prob_space) weak_law_of_large_numbers_iid:
  fixes X :: "nat \<Rightarrow> 'a \<Rightarrow> real" and \<epsilon> :: real
  assumes indep: "indep_vars (\<lambda>_. borel) X UNIV"
  assumes distr: "\<And>i. distr M borel (X i) = distr M borel (X 0)"
  assumes L1:    "integrable M (X 0)"
  assumes "\<epsilon> > 0"
  shows   "(\<lambda>n. prob {x\<in>space M. \<bar>(\<Sum>i<n. X i x) / n - expectation (X 0)\<bar> > \<epsilon>}) \<longlonglongrightarrow> 0"
proof (rule AE_convergence_imp_convergence_in_prob)
  show "AE x in M. (\<lambda>n. (\<Sum>i<n. X i x) / n) \<longlonglongrightarrow> expectation (X 0)"
    by (rule strong_law_of_large_numbers_iid) fact+
next
  have [measurable]: "random_variable borel (X i)" for i
    using indep by (auto simp: indep_vars_def)
  show "random_variable borel (\<lambda>x. (\<Sum>i<n. X i x) / real n)" for n
    by measurable
qed (use \<open>\<epsilon> > 0\<close> in simp_all)

end