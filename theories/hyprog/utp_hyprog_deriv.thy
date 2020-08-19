section \<open> Derivatives of UTP Expressions \<close>

theory utp_hyprog_deriv
  imports utp_hyprog_prelim
begin

text \<open> We provide functions for specifying differentiability and taking derivatives of UTP expressions.
  The expressions have a hybrid state space, and so we only require differentiability of the
  continuous variable vector. The remainder of the state space is left unchanged by differentiation. \<close>

subsection \<open> Differentiability \<close>

lift_definition uexpr_differentiable_when :: 
  "('a::ordered_euclidean_space, 'c::ordered_euclidean_space, 's) hyexpr \<Rightarrow> (bool, 'c, 's) hyexpr \<Rightarrow> bool" ("differentiable\<^sub>e _ when _" [0, 100] 100)
is "\<lambda> f d. \<forall> s. d s \<longrightarrow> (\<lambda> x. f (put\<^bsub>cvec\<^esub> s x)) differentiable (at (get\<^bsub>cvec\<^esub> s))" .

utp_lift_notation uexpr_differentiable_when (0)

abbreviation uexpr_differentiable :: 
  "('a::ordered_euclidean_space, 'c::ordered_euclidean_space, 's) hyexpr \<Rightarrow> bool" ("differentiable\<^sub>e")
  where "differentiable\<^sub>e f \<equiv> differentiable\<^sub>e f when true"

translations "differentiable\<^sub>e f" <= "differentiable\<^sub>e f when true"

declare uexpr_differentiable_when_def [upred_defs]

update_uexpr_rep_eq_thms

lemma udifferentiable_consts [closure]:
  "differentiable\<^sub>e 0" "differentiable\<^sub>e 1" "differentiable\<^sub>e (numeral n)" "differentiable\<^sub>e \<guillemotleft>k\<guillemotright>"
  by (rel_simp)+

lemma udifferentiable_var [closure]:
  assumes "cont_lens x"
  shows "differentiable\<^sub>e (utp_expr.var (x ;\<^sub>L \<^bold>c))"
  by (rel_simp, simp add: assms bounded_linear_imp_differentiable)

lemma udifferentiable_pr_var [closure]: 
  assumes "cont_lens x"
  shows "differentiable\<^sub>e (utp_expr.var (pr_var (x ;\<^sub>L \<^bold>c)))"
  by (rel_simp, simp add: assms bounded_linear_imp_differentiable)

lemma udifferentiable_plus [closure]:
  "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow> differentiable\<^sub>e (e + f)"
  by (rel_simp)

lemma udifferentiable_uminus [closure]:
  "\<lbrakk> differentiable\<^sub>e e \<rbrakk> \<Longrightarrow> differentiable\<^sub>e (- e)"
  by (rel_simp)

lemma udifferentiable_minus [closure]:
  "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow> differentiable\<^sub>e (e - f)"
  by (rel_simp)

lemma udifferentiable_mult [closure]:
  fixes e f :: "('a::{ordered_euclidean_space, real_normed_algebra}, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow> differentiable\<^sub>e (e * f)"
  by (rel_simp)

lemma udifferentiable_divide [closure]:
  fixes e f :: "('a::{ordered_euclidean_space, real_normed_field}, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow> differentiable\<^sub>e (e / f) when (\<not> f = 0)"
  by (rel_simp)

lemma udifferentiable_scaleR [closure]:
  fixes e :: "('a::ordered_euclidean_space, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "\<lbrakk> differentiable\<^sub>e n; differentiable\<^sub>e e \<rbrakk> \<Longrightarrow> differentiable\<^sub>e \<^U>(n *\<^sub>R e)"
  by (rel_simp)

lemma udifferentiable_inner [closure]:
  fixes e :: "('a::ordered_euclidean_space, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "\<lbrakk> differentiable\<^sub>e n; differentiable\<^sub>e e \<rbrakk> \<Longrightarrow> differentiable\<^sub>e \<^U>(n \<bullet> e)"
  by (rel_simp)

lemma udifferentiable_power [closure]:
  fixes e :: "('a::{ordered_euclidean_space, real_normed_field}, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "differentiable\<^sub>e e \<Longrightarrow> differentiable\<^sub>e (e ^ n)"
  by (rel_simp)

lemma udifferentiable_norm [closure]:
  fixes e :: "('a::ordered_euclidean_space, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "differentiable\<^sub>e e \<Longrightarrow> differentiable\<^sub>e \<^U>(norm e) when (\<not> e = 0)"
  by (rel_simp, metis differentiable_compose differentiable_norm_at)

lemma udifferentiable_sin [closure]:
  fixes e :: "(real, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "differentiable\<^sub>e e \<Longrightarrow> differentiable\<^sub>e U(sin e)"
  using differentiable_compose field_differentiable_imp_differentiable field_differentiable_within_sin
  by (rel_blast)

lemma udifferentiable_cos [closure]:
  fixes e :: "(real, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "differentiable\<^sub>e e \<Longrightarrow> differentiable\<^sub>e U(cos e)"
  using differentiable_compose field_differentiable_imp_differentiable field_differentiable_within_cos
  by (rel_blast)

lemma udifferentiable_vector_2 [closure]:
  fixes e :: "(real, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow> differentiable\<^sub>e U(\<^bold>[[e, f]\<^bold>])"
  apply (rel_simp)
  apply (rule differentiable_Mat)
  apply (rename_tac c m i j)
  apply (case_tac "j = 0")
   apply (simp_all)
  done

subsection \<open> Differentiation \<close>

text \<open> For convenience in the use of ODEs, we differentiate with respect to a known context of
  derivative for the variables. This means we don't have to deal with symbolic variable derivatives
  and so the state space is unchanged by differentiation. \<close>

lift_definition lie_deriv :: 
  "'c usubst \<Rightarrow> ('a::ordered_euclidean_space, 'c::ordered_euclidean_space, 's) hyexpr \<Rightarrow> ('a, 'c, 's) hyexpr" ("\<L>\<^bsub>_\<^esub>")
is "\<lambda> \<sigma> f s. frechet_derivative (\<lambda> x. f (put\<^bsub>cvec\<^esub> s x)) (at (get\<^bsub>cvec\<^esub> s)) (\<sigma> (get\<^bsub>cvec\<^esub> s))" .

update_uexpr_rep_eq_thms

utp_const lie_deriv

named_theorems uderiv

lemma uderiv_zero [uderiv]: "\<L>\<^bsub>F'\<^esub> 0 = 0"
  by (rel_simp)

lemma uderiv_one [uderiv]: "\<L>\<^bsub>F'\<^esub> 1 = 0"
  by (rel_simp)

lemma uderiv_numeral [uderiv]: "\<L>\<^bsub>F'\<^esub> (numeral n) = 0"
  by (rel_simp)

lemma uderiv_lit [uderiv]: "\<L>\<^bsub>F'\<^esub> (\<guillemotleft>v\<guillemotright>) = 0"
  by (rel_simp)

lemma uderiv_plus [uderiv]:
  "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow> \<L>\<^bsub>F'\<^esub> (e + f) = (\<L>\<^bsub>F'\<^esub> e + \<L>\<^bsub>F'\<^esub> f)"
  by (rel_simp, simp add: frechet_derivative_plus)

lemma uderiv_uminus [uderiv]: 
  "differentiable\<^sub>e e \<Longrightarrow> \<L>\<^bsub>F'\<^esub> (- e) = - (\<L>\<^bsub>F'\<^esub> e)"
  by (rel_simp, simp add: frechet_derivative_uminus)

lemma uderiv_minus [uderiv]: 
  "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow> \<L>\<^bsub>F'\<^esub> (e - f) = (\<L>\<^bsub>F'\<^esub> e) - (\<L>\<^bsub>F'\<^esub> f)"
  by (rel_simp, simp add: frechet_derivative_minus)

lemma uderiv_mult [uderiv]:
  fixes e f :: "('a::{ordered_euclidean_space, real_normed_algebra}, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow>  \<L>\<^bsub>F'\<^esub> (e * f) = (e * \<L>\<^bsub>F'\<^esub> f + \<L>\<^bsub>F'\<^esub> e * f)"
  by (rel_simp, simp add: frechet_derivative_mult)

lemma uderiv_scaleR [uderiv]:
  fixes f :: "('a::{ordered_euclidean_space}, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow>  \<L>\<^bsub>F'\<^esub> \<^U>(e *\<^sub>R f) = \<^U>(e *\<^sub>R \<L>\<^bsub>F'\<^esub> f + \<L>\<^bsub>F'\<^esub> e *\<^sub>R f)"
  by (rel_simp, simp add: frechet_derivative_scaleR)

lemma uderiv_inner [uderiv]:
  fixes f :: "('a::ordered_euclidean_space, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow>  \<L>\<^bsub>F'\<^esub> \<^U>(e \<bullet> f) = \<^U>(e \<bullet> \<L>\<^bsub>F'\<^esub> f + \<L>\<^bsub>F'\<^esub> e \<bullet> f)"
  by (rel_simp, simp add: frechet_derivative_inner)

lemma uderiv_power [uderiv]:
  fixes e :: "('a::{ordered_euclidean_space, real_normed_field}, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "differentiable\<^sub>e e \<Longrightarrow>  \<L>\<^bsub>F'\<^esub> (e ^ n) = of_nat n * \<L>\<^bsub>F'\<^esub> e * e ^ (n - 1)"
  by (rel_simp, simp add: frechet_derivative_power ueval)

lemma uderiv_cos [uderiv]:
  fixes e :: "(real, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "differentiable\<^sub>e e \<Longrightarrow>  \<L>\<^bsub>F'\<^esub> U(cos e) = U(\<L>\<^bsub>F'\<^esub> e * - sin e)"
  by (rel_simp, simp add: frechet_derivative_cos)

lemma uderiv_sin [uderiv]:
  fixes e :: "(real, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "differentiable\<^sub>e e \<Longrightarrow>  \<L>\<^bsub>F'\<^esub> U(sin e) = U(\<L>\<^bsub>F'\<^esub> e * cos e)"
  by (rel_simp, simp add: frechet_derivative_sin)

lemma uderiv_vector_2 [uderiv]:
  fixes e :: "(real, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow>  \<L>\<^bsub>F'\<^esub> U(\<^bold>[[e, f]\<^bold>]) = U(\<^bold>[[\<L>\<^bsub>F'\<^esub> e, \<L>\<^bsub>F'\<^esub> f]\<^bold>])"
  apply (rel_simp)
  apply (subst frechet_derivative_Mat)
   apply (rename_tac c m i j)
   apply (case_tac "j = 0")
    apply (simp)
   apply (simp)
  apply (simp add: deriv_mat_def abs_mat_def comp_def upt_rec)
  done

text \<open> The derivative of a variable represented by a bounded linear lens into the continuous state 
  space uses the said lens to obtain the derivative from the context @{term F'}. \<close>

lemma uderiv_var:
  assumes "cont_lens x"
  shows "\<L>\<^bsub>F'\<^esub> (utp_expr.var (x ;\<^sub>L \<^bold>c)) = \<langle>F'\<rangle>\<^sub>s x \<oplus>\<^sub>p cvec"
  by (rel_simp)
     (metis assms bounded_linear_imp_has_derivative cont_lens.bounded_linear_get frechet_derivative_at)

lemma uderiv_pr_var [uderiv]:
  assumes "cont_lens x"
  shows "(\<L>\<^bsub>F'\<^esub> &\<^bold>c:x) = \<langle>F'\<rangle>\<^sub>s x \<oplus>\<^sub>p \<^bold>c"
  using assms by (simp add: pr_var_def uderiv_var)

text \<open> Example \<close>

lemma 
  fixes x :: "real \<Longrightarrow> real"
  assumes "cont_lens x"
  shows "\<L>\<^bsub>[x \<mapsto>\<^sub>s &x]\<^esub> (2*&\<^bold>c:x) = 2*&\<^bold>c:x"
  by (simp add: uderiv usubst closure assms alpha, rel_simp)

end