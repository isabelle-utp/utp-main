theory utp_hyprog_dinv
  imports utp_hyprog
begin

(*
lemma 
  fixes \<eta> :: "(real, 'a) uexpr"
  assumes "vwb_lens x" "`B \<Rightarrow> ((F' \<oplus>\<^sub>s x) \<dagger> \<eta> =\<^sub>u 0)`" 
    "\<forall> l\<ge>0. \<forall> r\<in>{0..l}. (\<lambda>t. \<lbrakk>\<eta>\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> s (F t))) differentiable (at r within {0..l})"
  shows "(\<lceil>\<eta> =\<^sub>u 0\<rceil>\<^sub>< \<Rightarrow> \<lceil>\<eta> =\<^sub>u 0\<rceil>\<^sub>>) \<sqsubseteq> ode x F' B"
using assms proof (rel_auto')
  fix l :: real and F s
  assume a:
    "\<forall>A. \<lbrakk>B\<rbrakk>\<^sub>e A \<longrightarrow> \<lbrakk>\<eta>\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> A (F' (get\<^bsub>x\<^esub> A))) = 0" "l > 0"
    "\<forall>t. 0 \<le> t \<and> t \<le> l \<longrightarrow> (F has_vector_derivative F' (F t)) (at t within {0..l}) \<and> (\<forall>b. \<lbrakk>B\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> b (F t)))"
    "get\<^bsub>x\<^esub> s = F 0" "\<lbrakk>\<eta>\<rbrakk>\<^sub>e s = 0"
  have "\<forall>r\<in>{0..l}. ((\<lambda>t. \<lbrakk>\<eta>\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> s (F t))) has_vector_derivative 0) (at r within {0..l})"
  proof
    fix r
    assume r: "r \<in> {0..l}"
    hence "\<lbrakk>B\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> s (F r))"
      using a(3) atLeastAtMost_iff by blast
    hence "\<lbrakk>\<eta>\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> s (F' (get\<^bsub>x\<^esub> s))) = 0"
      using a(1) a(2) a(3) a(4) assms(1) by force
    moreover have "(F has_vector_derivative F' (F r)) (at r within {0..l})"
      using r a(3) atLeastAtMost_iff by blast
    moreover have "((\<lambda>t. \<lbrakk>\<eta>\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> s (F t))) has_vector_derivative vector_derivative (\<lambda>t. \<lbrakk>\<eta>\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> s (F t))) (at r within {0..l})) (at r within {0..l})"
    
    ultimately show "((\<lambda>t. \<lbrakk>\<eta>\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> s (F t))) has_vector_derivative 0) (at r within {0..l})"
  show "\<lbrakk>\<eta>\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> s (F l)) = 0"
*)


lemma vector_derivative_chain_frechet: 
  fixes g :: "'a::ordered_euclidean_space \<Rightarrow> 'b::ordered_euclidean_space"
  assumes "f differentiable (at x)" "g differentiable (at (f x))"
  shows "vector_derivative (g \<circ> f) (at x) =
        (frechet_derivative g (at (f x))) (vector_derivative f (at x)) "
proof -
  have "(g has_derivative frechet_derivative g (at (f x))) (at (f x))"
    using assms(2) frechet_derivative_works by blast
  hence 1:"(g has_derivative frechet_derivative g (at (f x))) (at (f x) within range f)"
    by (simp add: has_derivative_at_withinI)
  from 1 assms show ?thesis
    by (auto intro: vector_derivative_chain_within simp add: at_eq_bot_iff)
qed

lemma frechet_derivative_const: "\<partial> (\<lambda> x. k) (at t) = (\<lambda> x. 0)"
  by (metis frechet_derivative_at has_derivative_const)

lemma frechet_derivative_uminus:
  assumes "f differentiable (at t)"
  shows "\<partial> (\<lambda> x. - f x) (at t) = (\<lambda>x. - \<partial> f (at t) x)"
proof -
  have "((\<lambda>x. - f x) has_derivative (\<lambda>x. - \<partial> f (at t) x)) (at t)"
    using assms frechet_derivative_works has_derivative_minus by blast
  thus ?thesis
    using frechet_derivative_at by force
qed

lemma frechet_derivative_plus:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "f differentiable (at t)" "g differentiable (at t)"
  shows "\<partial> (\<lambda> x. f x + g x) (at t) = (\<lambda> x. \<partial> f (at t) x + \<partial> g (at t) x)"
proof -
  have "((\<lambda>x. f x + g x) has_derivative (\<lambda>x. \<partial> f (at t) x + \<partial> g (at t) x)) (at t)"
    using assms(1) assms(2) frechet_derivative_works has_derivative_add by blast
  thus ?thesis
    using frechet_derivative_at by force
qed

lemma frechet_derivative_mult:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  assumes "f differentiable (at t)" "g differentiable (at t)"
  shows "\<partial> (\<lambda> x. f x * g x) (at t) = 
         (\<lambda> x. f t * \<partial> g (at t) x + \<partial> f (at t) x * g t)"
proof -
  have "((\<lambda>x. f x * g x) has_derivative (\<lambda> x. f t * \<partial> g (at t) x + \<partial> f (at t) x * g t)) (at t)"
    using assms(1) assms(2) frechet_derivative_works has_derivative_mult by blast
  thus ?thesis
    using frechet_derivative_at by force
qed

lift_definition uexpr_deriv :: "('a::ordered_euclidean_space, 'i::finite, 's) hyexpr \<Rightarrow> (real^'i) usubst \<Rightarrow> ('a, 'i, 's) hyexpr" ("\<partial>\<^sub>e")
is "\<lambda> f \<sigma> s. frechet_derivative (\<lambda> x. f (put\<^bsub>cvec\<^esub> s x)) (at (get\<^bsub>cvec\<^esub> s)) (\<sigma> (get\<^bsub>cvec\<^esub> s))" .

(*
lift_definition uexpr_deriv :: "('a::ordered_euclidean_space, 'b::ordered_euclidean_space) uexpr \<Rightarrow> 'b usubst \<Rightarrow> ('a, 'b) uexpr" ("\<partial>\<^sub>e")
is "\<lambda> f \<sigma> s. frechet_derivative f (at s) (\<sigma> s)" .
*)

lift_definition uexpr_differentiable :: "('a::ordered_euclidean_space, 'b::ordered_euclidean_space) uexpr \<Rightarrow> bool" ("differentiable\<^sub>e")
is "\<lambda> f. \<forall> s. f differentiable (at s)" .

update_uexpr_rep_eq_thms

declare uexpr_differentiable_def [upred_defs]

lemma uderiv_lit: "\<partial>\<^sub>e (\<guillemotleft>v\<guillemotright>) F' = 0"
  by (rel_simp, simp add: frechet_derivative_const)

lemma uderiv_uminus: 
  "differentiable\<^sub>e e \<Longrightarrow> \<partial>\<^sub>e (- e) F' = - (\<partial>\<^sub>e e) F'"
  by (rel_simp, simp add: frechet_derivative_uminus)

lemma uderiv_plus:
  fixes e f :: "('a::ordered_euclidean_space, 'b::ordered_euclidean_space) uexpr"
  shows "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow> \<partial>\<^sub>e (e + f) F' = (\<partial>\<^sub>e e F' + \<partial>\<^sub>e f F')"
  by (rel_simp, simp add: frechet_derivative_plus)

lemma uderiv_mult:
  fixes e f :: "('a::{real_normed_algebra,ordered_euclidean_space}, 'b::ordered_euclidean_space) uexpr"
  shows "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow> \<partial>\<^sub>e (e * f) F' = (e * \<partial>\<^sub>e f F' + \<partial>\<^sub>e e F' * f)"
  by (rel_simp, simp add: frechet_derivative_mult)

text \<open> The derivative of a variable represented by a Euclidean lens is the same Euclidean lens \<close>

lemma uderiv_var: 
  "k < DIM('a::executable_euclidean_space) \<Longrightarrow> \<partial>\<^sub>e (var (eucl_lens k :: real \<Longrightarrow> 'a)) F' = \<langle>F'\<rangle>\<^sub>s (eucl_lens k)"
  by (rel_simp, metis bounded_linear_imp_has_derivative bounded_linear_inner_left frechet_derivative_at)

lemma derivation_lemma:
  fixes F :: "real \<Rightarrow> 'a::executable_euclidean_space"
  assumes
    tSol: "(F has_vector_derivative F' (F t)) (at t within S)" and
    tDiff: "differentiable\<^sub>e \<eta>"
  shows "((\<lbrakk>\<eta>\<rbrakk>\<^sub>e \<circ> F) has_vector_derivative (\<lbrakk>\<partial>\<^sub>e \<eta> F'\<rbrakk>\<^sub>e (F t))) (at t within S)"
  by (metis frechet_derivative_works has_derivative_at_withinI tDiff tSol uexpr_deriv.rep_eq uexpr_differentiable.rep_eq vector_derivative_diff_chain_within)

declare [[show_types]]

term "(\<oplus>\<^sub>p)"

term "\<partial>\<^sub>e (e\<lbrakk>\<guillemotleft>v\<guillemotright>/&dst\<rbrakk> \<restriction>\<^sub>e cvec) (F' \<oplus>\<^sub>s x)"

definition uderiv_ext :: 
  "'a usubst \<Rightarrow> ('a \<Longrightarrow> (real, 'i::enum) vec) \<Rightarrow> ('a, ('i, 's) hybs_scheme) uexpr \<Rightarrow> ('a::ordered_euclidean_space, 'i, 's) hyexpr"
  ("_, _ \<turnstile> \<partial>\<^sub>e _" [100, 0, 101] 101) where
"uderiv_ext F' x e = ((\<partial>\<^sub>e (e\<lbrakk>\<guillemotleft>v\<guillemotright>/&dst\<rbrakk> \<restriction>\<^sub>e cvec) (F' \<oplus>\<^sub>s x)) \<oplus>\<^sub>p cvec) \<lbrakk>v\<rightarrow>&dst\<rbrakk>"

lemma uderiv_ext_lit: "F', x \<turnstile> \<partial>\<^sub>e (\<guillemotleft>v\<guillemotright>) = 0"
  by (simp add: uderiv_ext_def uderiv_lit usubst)


lemma 
  fixes e :: "(real, 'i::enum, 's) hyexpr"
  assumes "vwb_lens x" "`B \<Rightarrow> (F', x \<turnstile> \<partial>\<^sub>e e) =\<^sub>u 0`"

(*
assumes "vwb_lens x" "`B \<Rightarrow> ((F' \<oplus>\<^sub>s x) \<dagger> \<eta> =\<^sub>u 0)`"
    "\<forall> l\<ge>0. \<forall> r\<in>{0..l}. (\<lambda>t. \<lbrakk>\<eta>\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> s (F t))) differentiable (at r within {0..l})"
*)
  shows "(\<lceil>e =\<^sub>u 0\<rceil>\<^sub>< \<Rightarrow> \<lceil>e =\<^sub>u 0\<rceil>\<^sub>>) \<sqsubseteq> ode x F' B"
using assms proof (rel_auto')
  fix l :: real and F s
  assume a:
    "\<forall>A. \<lbrakk>B\<rbrakk>\<^sub>e A \<longrightarrow> \<lbrakk>\<eta>\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> A (F' (get\<^bsub>x\<^esub> A))) = 0" "l > 0"
    "\<forall>t. 0 \<le> t \<and> t \<le> l \<longrightarrow> (F has_vector_derivative F' (F t)) (at t within {0..l}) \<and> (\<forall>b. \<lbrakk>B\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> b (F t)))"
    "get\<^bsub>x\<^esub> s = F 0" "\<lbrakk>\<eta>\<rbrakk>\<^sub>e s = 0"
  have "\<forall>r\<in>{0..l}. ((\<lambda>t. \<lbrakk>\<eta>\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> s (F t))) has_vector_derivative 0) (at r within {0..l})"
  proof
    fix r
    assume r: "r \<in> {0..l}"
    hence "\<lbrakk>B\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> s (F r))"
      using a(3) atLeastAtMost_iff by blast
    hence "\<lbrakk>\<eta>\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> s (F' (get\<^bsub>x\<^esub> s))) = 0"
      using a(1) a(2) a(3) a(4) assms(1) by force
    moreover have "(F has_vector_derivative F' (F r)) (at r within {0..l})"
      using r a(3) atLeastAtMost_iff by blast
    moreover have "((\<lambda>t. \<lbrakk>\<eta>\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> s (F t))) has_vector_derivative vector_derivative (\<lambda>t. \<lbrakk>\<eta>\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> s (F t))) (at r within {0..l})) (at r within {0..l})"
    
    ultimately show "((\<lambda>t. \<lbrakk>\<eta>\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> s (F t))) has_vector_derivative 0) (at r within {0..l})"
  show "\<lbrakk>\<eta>\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> s (F l)) = 0"




end