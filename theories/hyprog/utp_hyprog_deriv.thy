section \<open> Derivatives of UTP Expressions \<close>

theory utp_hyprog_deriv
  imports utp_hyprog_prelim
begin

text \<open> We provide functions for specifying differentiability and taking derivatives of UTP expressions.
  The expressions have a hybrid state space, and so we only require differentiability of the
  continuous variable vector. The remainder of the state space is left unchanged by differentiation. \<close>

subsection \<open> Differentiability \<close>

lift_definition uexpr_differentiable :: 
  "('a::ordered_euclidean_space, 'c::ordered_euclidean_space, 's) hyexpr \<Rightarrow> bool" ("differentiable\<^sub>e")
is "\<lambda> f. \<forall> s. (\<lambda> x. f (put\<^bsub>cvec\<^esub> s x)) differentiable (at (get\<^bsub>cvec\<^esub> s))" .

declare uexpr_differentiable_def [upred_defs]

update_uexpr_rep_eq_thms

lemma udifferentiable_consts [closure]:
  "differentiable\<^sub>e 0" "differentiable\<^sub>e 1" "differentiable\<^sub>e (numeral n)" "differentiable\<^sub>e \<guillemotleft>k\<guillemotright>"
  by (rel_simp)+

lemma udifferentiable_var [closure]: 
  "k < DIM('c::executable_euclidean_space) \<Longrightarrow> differentiable\<^sub>e(utp_expr.var ((eucl_lens k :: real \<Longrightarrow> 'c) ;\<^sub>L cvec))"
  by (rel_simp)

lemma udifferentiable_pr_var [closure]: 
  "k < DIM('c::executable_euclidean_space) \<Longrightarrow> differentiable\<^sub>e (utp_expr.var (pr_var ((eucl_lens k :: real \<Longrightarrow> 'c) ;\<^sub>L cvec)))"
  by (rel_simp)

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
  shows "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f; `\<not> (f = 0)` \<rbrakk> \<Longrightarrow> differentiable\<^sub>e (e / f)"
  by (rel_simp)

lemma udifferentiable_scaleR [closure]:
  fixes e :: "('a::ordered_euclidean_space, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "\<lbrakk> differentiable\<^sub>e n; differentiable\<^sub>e e \<rbrakk> \<Longrightarrow> differentiable\<^sub>e \<^U>(n *\<^sub>R e)"
  by (rel_simp)

lemma udifferentiable_power [closure]:
  fixes e :: "('a::{ordered_euclidean_space, real_normed_field}, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "differentiable\<^sub>e e \<Longrightarrow> differentiable\<^sub>e (e ^ n)"
  by (rel_simp)

lemma udifferentiable_norm [closure]:
  fixes e :: "('a::ordered_euclidean_space, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "\<lbrakk> differentiable\<^sub>e e; `\<not> (e = 0)` \<rbrakk> \<Longrightarrow> differentiable\<^sub>e \<^U>(norm e)"
  by (rel_simp, metis differentiable_compose differentiable_norm_at)

subsection \<open> Differentiation \<close>

text \<open> For convenience in the use of ODEs, we differentiate with respect to a known context of
  derivative for the variables. This means we don't have to deal with symbolic variable derivatives
  and so the state space is unchanged by differentiation. \<close>

lift_definition uexpr_deriv :: 
  "'c usubst \<Rightarrow> ('a::ordered_euclidean_space, 'c::ordered_euclidean_space, 's) hyexpr \<Rightarrow> ('a, 'c, 's) hyexpr" ("(_ \<turnstile> \<partial>\<^sub>e _)" [100, 101] 100)
is "\<lambda> \<sigma> f s. frechet_derivative (\<lambda> x. f (put\<^bsub>cvec\<^esub> s x)) (at (get\<^bsub>cvec\<^esub> s)) (\<sigma> (get\<^bsub>cvec\<^esub> s))" .

update_uexpr_rep_eq_thms

utp_const uexpr_deriv

named_theorems uderiv

lemma uderiv_zero [uderiv]: "F' \<turnstile> \<partial>\<^sub>e 0 = 0"
  by (rel_simp, simp add: frechet_derivative_const)

lemma uderiv_one [uderiv]: "F' \<turnstile> \<partial>\<^sub>e 1 = 0"
  by (rel_simp, simp add: frechet_derivative_const)

lemma uderiv_numeral [uderiv]: "F' \<turnstile> \<partial>\<^sub>e (numeral n) = 0"
  by (rel_simp, simp add: frechet_derivative_const)

lemma uderiv_lit [uderiv]: "F' \<turnstile> \<partial>\<^sub>e (\<guillemotleft>v\<guillemotright>) = 0"
  by (rel_simp, simp add: frechet_derivative_const)

lemma uderiv_plus [uderiv]:
  "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow> F' \<turnstile> \<partial>\<^sub>e (e + f) = (F' \<turnstile> \<partial>\<^sub>e e + F' \<turnstile> \<partial>\<^sub>e f)"
  by (rel_simp, simp add: frechet_derivative_plus)

lemma uderiv_uminus [uderiv]: 
  "differentiable\<^sub>e e \<Longrightarrow> F' \<turnstile> \<partial>\<^sub>e (- e) = - (F' \<turnstile> \<partial>\<^sub>e e)"
  by (rel_simp, simp add: frechet_derivative_uminus)

lemma uderiv_minus [uderiv]: 
  "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow> F' \<turnstile> \<partial>\<^sub>e (e - f) = (F' \<turnstile> \<partial>\<^sub>e e) - (F' \<turnstile> \<partial>\<^sub>e f)"
  by (rel_simp, simp add: frechet_derivative_minus)

lemma uderiv_mult [uderiv]:
  fixes e f :: "('a::{ordered_euclidean_space, real_normed_algebra}, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow>  F' \<turnstile> \<partial>\<^sub>e (e * f) = (e * F' \<turnstile> \<partial>\<^sub>e f + F' \<turnstile> \<partial>\<^sub>e e * f)"
  by (rel_simp, simp add: frechet_derivative_mult)

lemma uderiv_scaleR [uderiv]:
  fixes f :: "('a::{ordered_euclidean_space, real_normed_algebra}, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow>  F' \<turnstile> \<partial>\<^sub>e \<^U>(e *\<^sub>R f) = \<^U>(e *\<^sub>R F' \<turnstile> \<partial>\<^sub>e f + F' \<turnstile> \<partial>\<^sub>e e *\<^sub>R f)"
  by (rel_simp, simp add: frechet_derivative_scaleR)

lemma uderiv_power [uderiv]:
  fixes e :: "('a::{ordered_euclidean_space, real_normed_field}, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "differentiable\<^sub>e e \<Longrightarrow>  F' \<turnstile> \<partial>\<^sub>e (e ^ n) = of_nat n * F' \<turnstile> \<partial>\<^sub>e e * e ^ (n - 1)"
  by (rel_simp, simp add: frechet_derivative_power ueval)

text \<open> The derivative of a variable represented by a Euclidean lens into the continuous state space
  uses the said lens to obtain the derivative from the context @{term F'} \<close>

lemma uderiv_var:
  fixes F' :: "'c::executable_euclidean_space usubst"
  assumes "k < DIM('c)"
  shows "F' \<turnstile> \<partial>\<^sub>e (utp_expr.var ((\<Pi>[k] :: real \<Longrightarrow> 'c) ;\<^sub>L \<^bold>c)) = \<langle>F'\<rangle>\<^sub>s \<Pi>[k] \<oplus>\<^sub>p cvec"
  using assms
  by (rel_simp, metis bounded_linear_imp_has_derivative bounded_linear_inner_left frechet_derivative_at)

lemma uderiv_pr_var [uderiv]: 
  fixes F' :: "'c::executable_euclidean_space usubst"
  assumes "k < DIM('c)"
  shows "F' \<turnstile> \<partial>\<^sub>e &\<^bold>c:\<Pi>[k] = \<langle>F'\<rangle>\<^sub>s \<Pi>[k] \<oplus>\<^sub>p \<^bold>c"
  using assms by (simp add: pr_var_def uderiv_var)

end