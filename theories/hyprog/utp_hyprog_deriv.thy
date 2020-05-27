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

declare uexpr_differentiable_when_def [upred_defs]

update_uexpr_rep_eq_thms

lemma udifferentiable_consts [closure]:
  "differentiable\<^sub>e 0" "differentiable\<^sub>e 1" "differentiable\<^sub>e (numeral n)" "differentiable\<^sub>e \<guillemotleft>k\<guillemotright>"
  by (rel_simp)+

lemma udifferentiable_var [closure]:
  assumes "bounded_linear (get\<^bsub>x\<^esub>)"
  shows "differentiable\<^sub>e (utp_expr.var (x ;\<^sub>L \<^bold>c))"
  by (rel_simp, simp add: assms bounded_linear_imp_differentiable)

lemma udifferentiable_pr_var [closure]: 
  assumes "bounded_linear (get\<^bsub>x\<^esub>)"
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

lemma frechet_derivative_inner:
  fixes g :: "'a::{real_inner,real_normed_vector} \<Rightarrow> 'b::{real_inner,real_normed_vector}"
  assumes "f differentiable (at t)" "g differentiable (at t)"
  shows "\<partial> (\<lambda> x. f x \<bullet> g x) (at t) = 
         (\<lambda> x. f t \<bullet> \<partial> g (at t) x + \<partial> f (at t) x \<bullet> g t)"
proof -
  have "((\<lambda>x. f x \<bullet> g x) has_derivative (\<lambda> x. f t \<bullet> \<partial> g (at t) x + \<partial> f (at t) x \<bullet> g t)) (at t)"
  proof -
    have "(f has_derivative \<partial> f (at t)) (at t)"
      by (meson assms(1) frechet_derivative_works)
    then show ?thesis
      using assms(2) frechet_derivative_works has_derivative_inner by blast
  qed

  thus ?thesis
    using frechet_derivative_at by force
qed

lemma uderiv_inner [uderiv]:
  fixes f :: "('a::ordered_euclidean_space, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow>  F' \<turnstile> \<partial>\<^sub>e \<^U>(e \<bullet> f) = \<^U>(e \<bullet> F' \<turnstile> \<partial>\<^sub>e f + F' \<turnstile> \<partial>\<^sub>e e \<bullet> f)"
  by (rel_simp, simp add: frechet_derivative_inner)

lemma uderiv_power [uderiv]:
  fixes e :: "('a::{ordered_euclidean_space, real_normed_field}, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "differentiable\<^sub>e e \<Longrightarrow>  F' \<turnstile> \<partial>\<^sub>e (e ^ n) = of_nat n * F' \<turnstile> \<partial>\<^sub>e e * e ^ (n - 1)"
  by (rel_simp, simp add: frechet_derivative_power ueval)

lemma frechet_derivative_cos:
  fixes f :: "'a::{real_normed_vector} \<Rightarrow> real"
  assumes "f differentiable (at t)"
  shows "\<partial> (\<lambda> x. cos (f x)) (at t) = (\<lambda> x. \<partial> f (at t) x * - sin (f t))"
  by (metis assms frechet_derivative_at frechet_derivative_works has_derivative_cos)

lemma uderiv_cos [uderiv]:
  fixes e :: "(real, 'c::ordered_euclidean_space, 's) hyexpr"
  shows "differentiable\<^sub>e e \<Longrightarrow>  F' \<turnstile> \<partial>\<^sub>e U(cos e) = U(F' \<turnstile> \<partial>\<^sub>e e * - sin e)"
  by (rel_simp, simp add: frechet_derivative_cos)

text \<open> The derivative of a variable represented by a bounded linear lens into the continuous state 
  space uses the said lens to obtain the derivative from the context @{term F'}. \<close>

lemma uderiv_var:
  assumes "bounded_linear (get\<^bsub>x\<^esub>)"
  shows "F' \<turnstile> \<partial>\<^sub>e (utp_expr.var (x ;\<^sub>L \<^bold>c)) = \<langle>F'\<rangle>\<^sub>s x \<oplus>\<^sub>p cvec"
  by (rel_simp, metis assms bounded_linear_imp_has_derivative frechet_derivative_at)

lemma uderiv_pr_var [uderiv]:
  assumes "bounded_linear (get\<^bsub>x\<^esub>)"
  shows "F' \<turnstile> \<partial>\<^sub>e &\<^bold>c:x = \<langle>F'\<rangle>\<^sub>s x \<oplus>\<^sub>p \<^bold>c"
  using assms by (simp add: pr_var_def uderiv_var)

end