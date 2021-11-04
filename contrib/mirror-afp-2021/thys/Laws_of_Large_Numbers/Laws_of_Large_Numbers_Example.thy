(*
   File:     Laws_of_Large_Numbers.thy
   Author:   Manuel Eberl, TU München
*)
subsection \<open>Example\<close>
theory Laws_of_Large_Numbers_Example
  imports Laws_of_Large_Numbers
begin

text \<open>
  As an example, we apply the strong law to the proportion of successes in an independent sequence
  of coin flips with success probability \<open>p\<close>. We will show that proportion of successful coin
  flips among the first \<open>n\<close> attempts almost surely converges to \<open>p\<close> as \<open>n \<rightarrow> \<infinity>\<close>.
\<close>

(* TODO: Move *)
lemma (in prob_space) indep_vars_iff_distr_eq_PiM':
  fixes I :: "'i set" and X :: "'i \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes "I \<noteq> {}"
  assumes rv: "\<And>i. i \<in> I \<Longrightarrow> random_variable (M' i) (X i)"
  shows "indep_vars M' X I \<longleftrightarrow>
           distr M (\<Pi>\<^sub>M i\<in>I. M' i) (\<lambda>x. \<lambda>i\<in>I. X i x) = (\<Pi>\<^sub>M i\<in>I. distr M (M' i) (X i))"
proof -
  from assms obtain j where j: "j \<in> I"
    by auto
  define N' where "N' = (\<lambda>i. if i \<in> I then M' i else M' j)"
  define Y where "Y = (\<lambda>i. if i \<in> I then X i else X j)"
  have rv: "random_variable (N' i) (Y i)" for i
    using j by (auto simp: N'_def Y_def intro: assms)

  have "indep_vars M' X I = indep_vars N' Y I"
    by (intro indep_vars_cong) (auto simp: N'_def Y_def)
  also have "\<dots> \<longleftrightarrow> distr M (\<Pi>\<^sub>M i\<in>I. N' i) (\<lambda>x. \<lambda>i\<in>I. Y i x) = (\<Pi>\<^sub>M i\<in>I. distr M (N' i) (Y i))"
    by (intro indep_vars_iff_distr_eq_PiM rv assms)
  also have "(\<Pi>\<^sub>M i\<in>I. N' i) = (\<Pi>\<^sub>M i\<in>I. M' i)"
    by (intro PiM_cong) (simp_all add: N'_def)
  also have "(\<lambda>x. \<lambda>i\<in>I. Y i x) = (\<lambda>x. \<lambda>i\<in>I. X i x)"
    by (simp_all add: Y_def fun_eq_iff)
  also have "(\<Pi>\<^sub>M i\<in>I. distr M (N' i) (Y i)) = (\<Pi>\<^sub>M i\<in>I. distr M (M' i) (X i))"
    by (intro PiM_cong distr_cong) (simp_all add: N'_def Y_def)
  finally show ?thesis .
qed

(* TODO: Move *)
lemma indep_vars_PiM_components:
  assumes "\<And>i. i \<in> A \<Longrightarrow> prob_space (M i)"
  shows   "prob_space.indep_vars (PiM A M) M (\<lambda>i f. f i) A"
proof (cases "A = {}")
  case False
  have "distr (Pi\<^sub>M A M) (Pi\<^sub>M A M) (\<lambda>x. restrict x A) = distr (Pi\<^sub>M A M) (Pi\<^sub>M A M) (\<lambda>x. x)"
    by (intro distr_cong) (auto simp: restrict_def space_PiM PiE_def extensional_def Pi_def)
  also have "\<dots> = Pi\<^sub>M A M"
    by simp
  also have "\<dots> = Pi\<^sub>M A (\<lambda>i. distr (Pi\<^sub>M A M) (M i) (\<lambda>f. f i))"
    by (intro PiM_cong refl, subst distr_PiM_component) (auto simp: assms)
  finally show ?thesis
    by (subst prob_space.indep_vars_iff_distr_eq_PiM') (simp_all add: prob_space_PiM assms False)
next
  case True
  interpret prob_space "PiM A M"
    by (intro prob_space_PiM assms)
  show ?thesis
    unfolding indep_vars_def indep_sets_def by (auto simp: True)
qed

(* TODO: Move *)
lemma indep_vars_PiM_components':
  assumes "\<And>i. i \<in> A \<Longrightarrow> prob_space (M i)"
  assumes "\<And>i. i \<in> A \<Longrightarrow> g i \<in> M i \<rightarrow>\<^sub>M N i"
  shows   "prob_space.indep_vars (PiM A M) N (\<lambda>i f. g i (f i)) A"
  by (rule prob_space.indep_vars_compose2[OF prob_space_PiM indep_vars_PiM_components])
     (use assms in simp_all)

(* TODO: Move *)
lemma integrable_bernoulli_pmf [intro]:
  fixes f :: "bool \<Rightarrow> 'a :: {banach, second_countable_topology}"
  shows "integrable (bernoulli_pmf p) f"
  by (rule integrable_measure_pmf_finite) auto

(* TODO: Move *)
lemma expectation_bernoulli_pmf:
  fixes f :: "bool \<Rightarrow> 'a :: {banach, second_countable_topology}"
  assumes p: "p \<in> {0..1}"
  shows   "measure_pmf.expectation (bernoulli_pmf p) f = p *\<^sub>R f True + (1 - p) *\<^sub>R f False"
  using p by (subst integral_measure_pmf[of UNIV]) (auto simp: UNIV_bool)

experiment
  fixes p :: real
  assumes p: "p \<in> {0..1}"
begin

definition M :: "(nat \<Rightarrow> bool) measure"
  where "M = (\<Pi>\<^sub>M i\<in>(UNIV :: nat set). measure_pmf (bernoulli_pmf p))"

definition X :: "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> real"
  where "X = (\<lambda>i f. if f i then 1 else 0)"

interpretation prob_space M
  unfolding M_def by (intro prob_space_PiM measure_pmf.prob_space_axioms)

lemma random_variable_component: "random_variable (count_space UNIV) (\<lambda>f. f i)"
  unfolding X_def M_def by measurable

lemma random_variable_X [measurable]: "random_variable borel (X i)"
  unfolding X_def M_def by measurable

lemma distr_M_component: "distr M (count_space UNIV) (\<lambda>f. f i) = measure_pmf (bernoulli_pmf p)"
proof -
  have "distr M (count_space UNIV) (\<lambda>f. f i) = distr M (measure_pmf (bernoulli_pmf p)) (\<lambda>f. f i)"
    by (rule distr_cong) auto
  also have "\<dots> = measure_pmf (bernoulli_pmf p)"
    unfolding M_def by (subst distr_PiM_component) (simp_all add: measure_pmf.prob_space_axioms)
  finally show ?thesis .
qed

lemma distr_M_X:
  "distr M borel (X i) = distr (measure_pmf (bernoulli_pmf p)) borel (\<lambda>b. if b then 1 else 0)"
proof -
  have "distr M borel (X i) = distr (distr M (count_space UNIV) (\<lambda>f. f i)) 
                                    borel (\<lambda>b. if b then 1 else 0 :: real)"
    by (subst distr_distr) (auto simp: M_def X_def o_def)
  also note distr_M_component[of i]
  finally show ?thesis
    by simp
qed

lemma X_has_expectation: "integrable M (X 0)"
proof -
  have "integrable (bernoulli_pmf p) (\<lambda>b. if b then 1 else 0 :: real)"
    by auto
  also have "measure_pmf (bernoulli_pmf p) = distr M (count_space UNIV) (\<lambda>f. f 0)"
    by (simp add: distr_M_component)
  also have "integrable \<dots> (\<lambda>b. if b then 1 else 0 :: real) = integrable M (X 0)"
    unfolding X_def using random_variable_component by (subst integrable_distr_eq) auto
  finally show ?thesis .
qed

lemma indep: "indep_vars (\<lambda>_. borel) X UNIV"
  unfolding M_def X_def
  by (rule indep_vars_PiM_components') (simp_all add: measure_pmf.prob_space_axioms)

lemma expectation_X: "expectation (X i) = p"
proof -
  have "expectation (X i) =
        lebesgue_integral (distr M (count_space UNIV) (\<lambda>f. f i)) (\<lambda>b. if b then 1 else 0 :: real)"
    by (subst integral_distr) (simp_all add: random_variable_component X_def)
  also have "distr M (count_space UNIV) (\<lambda>x. x i) = measure_pmf (bernoulli_pmf p)"
    by (rule distr_M_component)
  also have "measure_pmf.expectation (bernoulli_pmf p) (\<lambda>b. if b then 1 else 0 :: real) = p"
    using p by (subst integral_bernoulli_pmf) auto
  finally show ?thesis .
qed

theorem "AE f in M. (\<lambda>n. card {i. i < n \<and> f i} / n) \<longlonglongrightarrow> p"
proof -
  have "AE f in M. (\<lambda>n. (\<Sum>i<n. X i f) / real n) \<longlonglongrightarrow> expectation (X 0)"
    by (rule strong_law_of_large_numbers_iid)
       (use indep X_has_expectation in \<open>simp_all add: distr_M_X\<close>)
  also have "expectation (X 0) = p"
    by (simp add: expectation_X)
  also have "(\<lambda>x n. \<Sum>i<n. X i x) = (\<lambda>x n. \<Sum>i\<in>{i\<in>{..<n}. x i}. 1)"
    by (intro ext sum.mono_neutral_cong_right) (auto simp: X_def)
  also have "\<dots> = (\<lambda>x n. real (card {i. i < n \<and> x i}))"
    by simp
  finally show ?thesis .
qed

end

end