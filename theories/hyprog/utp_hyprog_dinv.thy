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

lift_definition uexpr_differentiable :: "('a::ordered_euclidean_space, 'i::finite, 's) hyexpr \<Rightarrow> bool" ("differentiable\<^sub>e")
is "\<lambda> f. \<forall> s. (\<lambda> x. f (put\<^bsub>cvec\<^esub> s x)) differentiable (at (get\<^bsub>cvec\<^esub> s))" .

update_uexpr_rep_eq_thms

declare uexpr_differentiable_def [upred_defs]

lemma uderiv_lit: "\<partial>\<^sub>e (\<guillemotleft>v\<guillemotright>) F' = 0"
  by (rel_simp, simp add: frechet_derivative_const)

term " \<partial>\<^sub>e (- e) F'"

lemma uderiv_uminus: 
  "differentiable\<^sub>e e \<Longrightarrow> \<partial>\<^sub>e (- e) F' = - (\<partial>\<^sub>e e) F'"
  by (rel_simp, simp add: frechet_derivative_uminus)

lemma uderiv_plus:
  "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow> \<partial>\<^sub>e (e + f) F' = (\<partial>\<^sub>e e F' + \<partial>\<^sub>e f F')"
  by (rel_simp, simp add: frechet_derivative_plus)

typ "'a::real_algebra"

lemma uderiv_mult:
  fixes e f :: "('a::{ordered_euclidean_space, real_normed_algebra}, 'i::finite, 's) hyexpr"
  shows "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow> \<partial>\<^sub>e (e * f) F' = (e * \<partial>\<^sub>e f F' + \<partial>\<^sub>e e F' * f)"
  by (rel_simp, simp add: frechet_derivative_mult)

text \<open> The derivative of a variable represented by a Euclidean lens is the same Euclidean lens \<close>

lemma uderiv_var: 
  "k < DIM(real^'i::enum) \<Longrightarrow> \<partial>\<^sub>e (var ((eucl_lens k :: real \<Longrightarrow> real^'i::enum) ;\<^sub>L cvec)) F' = \<langle>F'\<rangle>\<^sub>s (eucl_lens k) \<oplus>\<^sub>p cvec"
  by (rel_simp, metis bounded_linear_imp_has_derivative bounded_linear_inner_left frechet_derivative_at)

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

lemma dI_le:
  fixes e :: "(real, 'i::enum, 's) hyexpr"
  assumes "differentiable\<^sub>e e" "`B \<Rightarrow> \<partial>\<^sub>e e F' \<ge>\<^sub>u 0`"
  shows "\<lbrace>e \<ge>\<^sub>u 0\<rbrace>ode F' B\<lbrace>e \<ge>\<^sub>u 0\<rbrace>\<^sub>u"
using assms proof (rel_auto')
  fix l :: real and F :: "real \<Rightarrow> (real, 'i) vec" and s :: "('i, 's) hybs_scheme"
  assume a:
    "\<forall>s. (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) differentiable at (cvec\<^sub>v s)"
    "0 < l"
    "\<forall>t. 0 \<le> t \<and> t \<le> l \<longrightarrow>
            (F has_vector_derivative F' (F t)) (at t within {0..l}) \<and> (\<forall>b. \<lbrakk>B\<rbrakk>\<^sub>e (b\<lparr>cvec\<^sub>v := F t\<rparr>))"
    "cvec\<^sub>v s = F 0"
    "\<forall>A. \<lbrakk>B\<rbrakk>\<^sub>e A \<longrightarrow> \<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (A\<lparr>cvec\<^sub>v := x\<rparr>)) (at (cvec\<^sub>v A)) (F' (cvec\<^sub>v A)) \<ge> 0"
    "\<lbrakk>e\<rbrakk>\<^sub>e s \<ge> 0"

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
    where "0 \<le> t \<and> t \<le> l \<and> \<lbrakk>\<partial>\<^sub>e e F'\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>) \<ge> 0 \<and> \<lbrakk>\<partial>\<^sub>e e F'\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F l\<rparr>) \<ge> 0 \<and>
           \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F l\<rparr>) - \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F 0\<rparr>) = l * \<lbrakk>\<partial>\<^sub>e e F'\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>)"
    apply (simp add: uexpr_deriv.rep_eq lens_defs)
    using d0 by force
    

  thus "\<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F l\<rparr>) \<ge> 0"


end