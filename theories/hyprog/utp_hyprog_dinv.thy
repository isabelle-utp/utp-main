theory utp_hyprog_dinv
  imports utp_hyprog
begin



lemma cvec_lemma: "\<lparr>cvec\<^sub>v = x, \<dots> = hybs.more s\<rparr> = s\<lparr>cvec\<^sub>v := x\<rparr>"
  by (auto)

lemma derivation_lemma1:
  fixes e :: "(real, 'i::enum, 's) hyexpr"
  assumes "differentiable\<^sub>e e" "t \<in> {0..l}" "(F has_vector_derivative F' (F t)) (at t within {0..l})"
  shows "((\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) \<circ> F has_vector_derivative \<lbrakk>\<partial>\<^sub>e e F'\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>)) (at t within {0..l})"
  using assms
  apply (rel_auto)
  apply (simp add: frechet_derivative_works)
  apply (rule vector_derivative_diff_chain_within)
   apply blast
  apply (drule_tac x="(F t)" in spec)
  apply (drule_tac x="hybs.more s" in spec)
  apply (simp add: cvec_lemma has_derivative_at_withinI)
  done

lemma derivation_lemma2:
  assumes "differentiable\<^sub>e e" "t \<in> {0..l}"
  shows "((\<lambda>a. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v:= a\<rparr>)) has_derivative \<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) (at (F t))) (at (F t))"
  using assms
  apply (rel_auto)
  apply (simp add: frechet_derivative_works)
  apply (drule_tac x="(F t)" in spec)
  apply (drule_tac x="hybs.more s" in spec)
  apply (simp add: cvec_lemma)
  done

lemma dI_eq:
  fixes e :: "(real, 'i::enum, 's) hyexpr"
  assumes "differentiable\<^sub>e e" "`B \<Rightarrow> \<partial>\<^sub>e e F' =\<^sub>u 0`"
  shows "\<lbrace>e =\<^sub>u 0\<rbrace>ode F' B\<lbrace>e =\<^sub>u 0\<rbrace>\<^sub>u"
using assms proof (rel_auto')
  fix l :: real and F :: "real \<Rightarrow> (real, 'i) vec" and s :: "('i, 's) hybs_scheme"
  assume a:
    "\<forall>s. (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) differentiable at (cvec\<^sub>v s)"
    "0 < l"
    "\<forall>t. 0 \<le> t \<and> t \<le> l \<longrightarrow>
            (F has_vector_derivative F' (F t)) (at t within {0..l}) \<and> (\<forall>b. \<lbrakk>B\<rbrakk>\<^sub>e (b\<lparr>cvec\<^sub>v := F t\<rparr>))"
    "cvec\<^sub>v s = F 0"
    "\<forall>A. \<lbrakk>B\<rbrakk>\<^sub>e A \<longrightarrow> \<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (A\<lparr>cvec\<^sub>v := x\<rparr>)) (at (cvec\<^sub>v A)) (F' (cvec\<^sub>v A)) = 0"
    "\<lbrakk>e\<rbrakk>\<^sub>e s = 0"

  have d0: "\<forall> t\<in>{0..l}. \<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) (at (F t)) (F' (F t)) = 0"
  proof
    fix t
    assume "t \<in> {0..l}"
    with a(3) have "\<lbrakk>B\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>)"
      by simp
    with a(5) have "\<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>\<lparr>cvec\<^sub>v := x\<rparr>)) (at (cvec\<^sub>v (s\<lparr>cvec\<^sub>v := F t\<rparr>))) (F' (cvec\<^sub>v (s\<lparr>cvec\<^sub>v := F t\<rparr>))) = 0"
      by (auto)
    thus "\<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) (at (F t)) (F' (F t)) = 0"
      by (simp)
  qed

  from a(1) have dE: "\<forall> t\<in>{0..l}. ((\<lambda>a. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v:= a\<rparr>)) has_derivative \<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) (at (F t))) (at (F t))"
    using assms(1) derivation_lemma2 by blast

  hence "\<forall>t\<in>{0..l}. ((\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) \<circ> F
                      has_vector_derivative 
                    \<lbrakk>\<partial>\<^sub>e e F'\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>)) (at t within {0..l})"
    by (simp add: a(3) assms(1) derivation_lemma1)

  with d0 have "\<forall>t\<in>{0..l}. ((\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) \<circ> F has_vector_derivative 0) (at t within {0..l})"
    by (metis (no_types, lifting) a(3) atLeastAtMost_iff dE has_derivative_at_withinI vector_derivative_diff_chain_within)

  hence "\<forall>t\<in>{0..l}. ((\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) \<circ> F has_derivative (\<lambda> x. 0)) (at t within {0..l})"
    by (simp add: has_vector_derivative_def)

  hence "\<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F l\<rparr>) - \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F 0\<rparr>) = (\<lambda>x. 0) (l - 0)"
    using mvt_very_simple[of 0 l "(\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) \<circ> F" "(\<lambda> _. \<lambda> x. 0)"]
    by (simp add: a(2) less_imp_le)
  
  thus "\<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F l\<rparr>) = 0"
    by (simp add: a(4)[THEN sym] a(6))
qed

lemma dI_ge:
  fixes e :: "(real, 'i::enum, 's) hyexpr"
  assumes "differentiable\<^sub>e e" "`B \<Rightarrow> \<partial>\<^sub>e e F' \<ge>\<^sub>u 0`"
  shows "\<lbrace>e \<ge>\<^sub>u 0\<rbrace>ode F' B\<lbrace>e \<ge>\<^sub>u 0\<rbrace>\<^sub>u" and "\<lbrace>e >\<^sub>u 0\<rbrace>ode F' B\<lbrace>e >\<^sub>u 0\<rbrace>\<^sub>u"
using assms proof (rel_auto')
  fix l :: real and F :: "real \<Rightarrow> (real, 'i) vec" and s :: "('i, 's) hybs_scheme"
  assume a:
    "\<forall>s. (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) differentiable at (cvec\<^sub>v s)"
    "0 < l"
    "\<forall>t. 0 \<le> t \<and> t \<le> l \<longrightarrow>
            (F has_vector_derivative F' (F t)) (at t within {0..l}) \<and> (\<forall>b. \<lbrakk>B\<rbrakk>\<^sub>e (b\<lparr>cvec\<^sub>v := F t\<rparr>))"
    "cvec\<^sub>v s = F 0"
    "\<forall>A. \<lbrakk>B\<rbrakk>\<^sub>e A \<longrightarrow> \<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (A\<lparr>cvec\<^sub>v := x\<rparr>)) (at (cvec\<^sub>v A)) (F' (cvec\<^sub>v A)) \<ge> 0"

  have d0: "\<forall> t\<in>{0..l}. \<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) (at (F t)) (F' (F t)) \<ge> 0"
  proof
    fix t
    assume "t \<in> {0..l}"
    with a(3) have "\<lbrakk>B\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>)"
      by simp
    with a(5) have "\<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>\<lparr>cvec\<^sub>v := x\<rparr>)) (at (cvec\<^sub>v (s\<lparr>cvec\<^sub>v := F t\<rparr>))) (F' (cvec\<^sub>v (s\<lparr>cvec\<^sub>v := F t\<rparr>))) \<ge> 0"
      by (auto)
    thus "\<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) (at (F t)) (F' (F t)) \<ge> 0"
      by (simp)
  qed

  from a(1) have dE: "\<forall> t\<in>{0..l}. ((\<lambda>a. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v:= a\<rparr>)) has_derivative \<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) (at (F t))) (at (F t))"
    using assms(1) derivation_lemma2 by blast

  hence "\<forall>t\<in>{0..l}. ((\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) \<circ> F
                      has_vector_derivative 
                    \<lbrakk>\<partial>\<^sub>e e F'\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>)) (at t within {0..l})"
    by (simp add: a(3) assms(1) derivation_lemma1)

  hence "\<forall>t\<in>{0..l}. ((\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) \<circ> F
                      has_derivative 
                    (\<lambda> x. x *\<^sub>R \<lbrakk>\<partial>\<^sub>e e F'\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>))) (at t within {0..l})"
    using has_vector_derivative_def by blast
  hence "\<exists>x\<in>{0..l}. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F l\<rparr>) - \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F 0\<rparr>) = l * \<lbrakk>\<partial>\<^sub>e e F'\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F x\<rparr>)"
    using a(2) mvt_very_simple[of 0 l "(\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) \<circ> F" "\<lambda> t. (\<lambda> x. x *\<^sub>R \<lbrakk>\<partial>\<^sub>e e F'\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>))"]
    by (simp)

  then obtain t 
    where "0 \<le> t" "t \<le> l" "\<lbrakk>\<partial>\<^sub>e e F'\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>) \<ge> 0" "\<lbrakk>\<partial>\<^sub>e e F'\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F l\<rparr>) \<ge> 0"
          "\<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F l\<rparr>) - \<lbrakk>e\<rbrakk>\<^sub>e s = l * \<lbrakk>\<partial>\<^sub>e e F'\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>)"
    apply (simp add: uexpr_deriv.rep_eq lens_defs a(4)[THEN sym])
    using d0 by force

  moreover have "l * \<lbrakk>\<partial>\<^sub>e e F'\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>) \<ge> 0"
    using a(2) calculation(3) by auto

  ultimately show 
    "\<lbrakk>e\<rbrakk>\<^sub>e s \<ge> 0 \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F l\<rparr>) \<ge> 0" and 
    "\<lbrakk>e\<rbrakk>\<^sub>e s > 0 \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F l\<rparr>) > 0"
    by linarith+

qed

text \<open> Example \<close>

type_synonym gravs = "(2, unit) hybs_scheme"

abbreviation h :: "real \<Longrightarrow> gravs" where "h \<equiv> eucl_lens 0 ;\<^sub>L cvec"
abbreviation v :: "real \<Longrightarrow> gravs" where "v \<equiv> eucl_lens 1 ;\<^sub>L cvec"

lemma eucl_lens_indep [simp]:
  "\<lbrakk> i < DIM('a); j < DIM('a); i \<noteq> j \<rbrakk> \<Longrightarrow> (eucl_lens i :: real \<Longrightarrow> 'a::executable_euclidean_space) \<bowtie> eucl_lens j"
  by (unfold_locales, simp_all add: lens_defs list_update_swap eucl_of_list_inner)

declare lens_comp_quotient [simp]
declare plus_lens_distr [THEN sym, simp]

lemma "\<lbrace>&v \<ge>\<^sub>u 0\<rbrace>\<langle>der(h) = v, der(v) = 9.81\<rangle>\<lbrace>&v \<ge>\<^sub>u 0\<rbrace>\<^sub>u"
  apply (rule dI_ge)
   apply (simp_all add: closure uderiv_pr_var usubst fode_def prod.case_eq_if mkuexpr alpha)
  apply (rel_auto)
  done

end