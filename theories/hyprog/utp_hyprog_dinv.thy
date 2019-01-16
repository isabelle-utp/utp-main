section \<open> Differential Induction \<close>

theory utp_hyprog_dinv
  imports 
    utp_hyprog_dL
    utp_hyprog_deriv
begin

lemma cvec_lemma: "\<lparr>cvec\<^sub>v = x, \<dots> = hybs.more s\<rparr> = s\<lparr>cvec\<^sub>v := x\<rparr>"
  by (auto)

lemma derivation_lemma1:
  fixes e :: "(real, 'c::executable_euclidean_space, 's) hyexpr"
  assumes "differentiable\<^sub>e e" "t \<in> {0..l}" "(F has_vector_derivative F' (F t)) (at t within {0..l})"
  shows "((\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) \<circ> F has_vector_derivative \<lbrakk>F' \<turnstile> \<partial>\<^sub>e e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>)) (at t within {0..l})"
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
  fixes e :: "(real, 'c::executable_euclidean_space, 's) hyexpr"
  assumes "differentiable\<^sub>e e" "`B \<Rightarrow> F' \<turnstile> \<partial>\<^sub>e e =\<^sub>u 0`"
  shows "\<lbrace>e =\<^sub>u 0\<rbrace>ode F' B\<lbrace>e =\<^sub>u 0\<rbrace>\<^sub>u"
using assms proof (rel_auto')
  fix l :: real and F :: "real \<Rightarrow> 'c" and s :: "('c, 's) hybs_scheme"
  assume a:
    "\<forall>s. (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) differentiable at (cvec\<^sub>v s)"
    "0 \<le> l"
    "solves F F' B s l"
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
                    \<lbrakk>F' \<turnstile> \<partial>\<^sub>e e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>)) (at t within {0..l})"
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
  fixes e :: "(real, 'c::executable_euclidean_space, 's) hyexpr"
  assumes "differentiable\<^sub>e e" "`B \<Rightarrow> F' \<turnstile> \<partial>\<^sub>e e  \<ge>\<^sub>u 0`"
  shows "\<lbrace>e \<ge>\<^sub>u 0\<rbrace>ode F' B\<lbrace>e \<ge>\<^sub>u 0\<rbrace>\<^sub>u" and "\<lbrace>e >\<^sub>u 0\<rbrace>ode F' B\<lbrace>e >\<^sub>u 0\<rbrace>\<^sub>u"
using assms proof (rel_auto')
  fix l :: real and F :: "real \<Rightarrow> 'c" and s :: "('c, 's) hybs_scheme"
  assume a:
    "\<forall>s. (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) differentiable at (cvec\<^sub>v s)"
    "0 \<le> l"
    "solves F F' B s l"
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
                    \<lbrakk>F' \<turnstile> \<partial>\<^sub>e e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>)) (at t within {0..l})"
    by (simp add: a(3) assms(1) derivation_lemma1)

  hence "\<forall>t\<in>{0..l}. ((\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) \<circ> F
                      has_derivative 
                    (\<lambda> x. x *\<^sub>R \<lbrakk>F' \<turnstile>  \<partial>\<^sub>e e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>))) (at t within {0..l})"
    using has_vector_derivative_def by blast
  hence "\<exists>x\<in>{0..l}. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F l\<rparr>) - \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F 0\<rparr>) = l * \<lbrakk>F' \<turnstile>  \<partial>\<^sub>e e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F x\<rparr>)"
    using a(2) mvt_very_simple[of 0 l "(\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) \<circ> F" "\<lambda> t. (\<lambda> x. x *\<^sub>R \<lbrakk>F' \<turnstile>  \<partial>\<^sub>e e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>))"]
    by (simp)

  then obtain t 
    where "0 \<le> t" "t \<le> l" "\<lbrakk>F' \<turnstile>  \<partial>\<^sub>e e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>) \<ge> 0" "\<lbrakk>F' \<turnstile>  \<partial>\<^sub>e e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F l\<rparr>) \<ge> 0"
          "\<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F l\<rparr>) - \<lbrakk>e\<rbrakk>\<^sub>e s = l * \<lbrakk>F' \<turnstile>  \<partial>\<^sub>e e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>)"
    apply (simp add: uexpr_deriv.rep_eq lens_defs a(4)[THEN sym])
    using d0 by force

  moreover have "l * \<lbrakk>F' \<turnstile> \<partial>\<^sub>e e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>) \<ge> 0"
    using a(2) calculation(3) by auto

  ultimately show 
    "\<lbrakk>e\<rbrakk>\<^sub>e s \<ge> 0 \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F l\<rparr>) \<ge> 0" and 
    "\<lbrakk>e\<rbrakk>\<^sub>e s > 0 \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F l\<rparr>) > 0"
    by linarith+

qed

datatype ('c::executable_euclidean_space, 's) hyprop =
  Eq "(real, 'c, 's) hyexpr" "(real, 'c, 's) hyexpr" (infix "=\<^sub>P" 50) |
  Less "(real, 'c, 's) hyexpr" "(real, 'c, 's) hyexpr" (infix "<\<^sub>P" 50) |
  LessEq "(real, 'c, 's) hyexpr" "(real, 'c, 's) hyexpr" (infix "\<le>\<^sub>P" 50) |
  And "('c, 's) hyprop" "('c, 's) hyprop" (infixr "\<and>\<^sub>P" 35) |
  Or "('c, 's) hyprop" "('c, 's) hyprop" (infixr "\<or>\<^sub>P" 30)

fun hyprop_deriv :: 
  "'c usubst \<Rightarrow> ('c::executable_euclidean_space, 's) hyprop \<Rightarrow> ('c, 's) hyprop" ("(_ \<turnstile> \<partial>\<^sub>P _)" [100, 101] 100) where
"F' \<turnstile> \<partial>\<^sub>P (e =\<^sub>P f) = (F' \<turnstile> \<partial>\<^sub>e e =\<^sub>P F' \<turnstile> \<partial>\<^sub>e f)" |
"F' \<turnstile> \<partial>\<^sub>P (e <\<^sub>P f) = (F' \<turnstile> \<partial>\<^sub>e e \<le>\<^sub>P F' \<turnstile> \<partial>\<^sub>e f)" |
"F' \<turnstile> \<partial>\<^sub>P (e \<le>\<^sub>P f) = (F' \<turnstile> \<partial>\<^sub>e e \<le>\<^sub>P F' \<turnstile> \<partial>\<^sub>e f)" |
"F' \<turnstile> \<partial>\<^sub>P (p \<and>\<^sub>P q) = (F' \<turnstile> \<partial>\<^sub>P p \<and>\<^sub>P F' \<turnstile> \<partial>\<^sub>P q)" |
"F' \<turnstile> \<partial>\<^sub>P (p \<or>\<^sub>P q) = (F' \<turnstile> \<partial>\<^sub>P p \<and>\<^sub>P F' \<turnstile> \<partial>\<^sub>P q)"

fun hyprop_eval :: "('c::executable_euclidean_space, 's) hyprop \<Rightarrow> ('c, 's) hypred" ("\<lbrakk>_\<rbrakk>\<^sub>P") where
"\<lbrakk>e =\<^sub>P f\<rbrakk>\<^sub>P = (e =\<^sub>u f)" |
"\<lbrakk>e <\<^sub>P f\<rbrakk>\<^sub>P = (e <\<^sub>u f)" |
"\<lbrakk>e \<le>\<^sub>P f\<rbrakk>\<^sub>P = (e \<le>\<^sub>u f)" |
"\<lbrakk>p \<and>\<^sub>P q\<rbrakk>\<^sub>P = (\<lbrakk>p\<rbrakk>\<^sub>P \<and> \<lbrakk>q\<rbrakk>\<^sub>P)" |
"\<lbrakk>p \<or>\<^sub>P q\<rbrakk>\<^sub>P = (\<lbrakk>p\<rbrakk>\<^sub>P \<or> \<lbrakk>q\<rbrakk>\<^sub>P)"

definition hyprop_pred ("[_]\<^sub>P") where "[p]\<^sub>P = \<lbrakk>p\<rbrakk>\<^sub>P"

fun hyprop_differentiable :: "('c::executable_euclidean_space, 's) hyprop \<Rightarrow> bool" ("differentiable\<^sub>P") where
"differentiable\<^sub>P (e =\<^sub>P f) = (differentiable\<^sub>e e \<and> differentiable\<^sub>e f)" |
"differentiable\<^sub>P (e <\<^sub>P f) = (differentiable\<^sub>e e \<and> differentiable\<^sub>e f)" |
"differentiable\<^sub>P (e \<le>\<^sub>P f) = (differentiable\<^sub>e e \<and> differentiable\<^sub>e f)" |
"differentiable\<^sub>P (p \<and>\<^sub>P q) = (differentiable\<^sub>P p \<and> differentiable\<^sub>P q)" |
"differentiable\<^sub>P (p \<or>\<^sub>P q) = (differentiable\<^sub>P p \<and> differentiable\<^sub>P q)"

lemma dInv:
  fixes e :: "(real, 'c::executable_euclidean_space, 's) hyexpr"
  assumes "differentiable\<^sub>P p" "`B \<Rightarrow> \<lbrakk>F' \<turnstile> \<partial>\<^sub>P p\<rbrakk>\<^sub>P`"
  shows "\<lbrace>[p]\<^sub>P\<rbrace>ode F' B\<lbrace>[p]\<^sub>P\<rbrace>\<^sub>u"
using assms proof (simp add: hyprop_pred_def, induct p)
  case (Eq x1 x2)
  hence a: "`B \<Rightarrow> F' \<turnstile> \<partial>\<^sub>e x1 =\<^sub>u F' \<turnstile> \<partial>\<^sub>e x2`" "differentiable\<^sub>e x1" "differentiable\<^sub>e x2"
    by (auto)
  from a(1) have b: "`B \<Rightarrow> (F' \<turnstile> \<partial>\<^sub>e x1 - F' \<turnstile> \<partial>\<^sub>e x2) =\<^sub>u 0`"
    by (rel_auto)
  hence "\<lbrace>(x1 - x2) =\<^sub>u 0\<rbrace> ode F' B \<lbrace>(x1 - x2) =\<^sub>u 0\<rbrace>\<^sub>u"
    by (simp add: a(2) a(3) dI_eq uderiv closure)
  then show ?case
    by (rel_auto')
next
  case (Less x1 x2)
  hence a: "`B \<Rightarrow> F' \<turnstile> \<partial>\<^sub>e x1 \<le>\<^sub>u F' \<turnstile> \<partial>\<^sub>e x2`" "differentiable\<^sub>e x1" "differentiable\<^sub>e x2"
    by (auto)
  from a(1) have b: "`B \<Rightarrow> (F' \<turnstile> \<partial>\<^sub>e x2 - F' \<turnstile> \<partial>\<^sub>e x1) \<ge>\<^sub>u 0`"
    by (rel_auto)
  hence "\<lbrace>(x2 - x1) >\<^sub>u 0\<rbrace> ode F' B \<lbrace>(x2 - x1) >\<^sub>u 0\<rbrace>\<^sub>u"
    by (simp add: a(2) a(3) dI_ge uderiv closure)
  then show ?case
    by (rel_auto')
next
  case (LessEq x1 x2)
  hence a: "`B \<Rightarrow> F' \<turnstile> \<partial>\<^sub>e x1 \<le>\<^sub>u F' \<turnstile> \<partial>\<^sub>e x2`" "differentiable\<^sub>e x1" "differentiable\<^sub>e x2"
    by (auto)
  from a(1) have b: "`B \<Rightarrow> (F' \<turnstile> \<partial>\<^sub>e x2 - F' \<turnstile> \<partial>\<^sub>e x1) \<ge>\<^sub>u 0`"
    by (rel_auto)
  hence "\<lbrace>(x2 - x1) \<ge>\<^sub>u 0\<rbrace> ode F' B \<lbrace>(x2 - x1) \<ge>\<^sub>u 0\<rbrace>\<^sub>u"
    by (simp add: a(2) a(3) dI_ge uderiv closure)
  then show ?case
    by (rel_auto')
next
  case (And p1 p2)
  then show ?case
    by (rel_auto')
next
  case (Or p1 p2)
  then show ?case
    by (rel_auto')
qed

lemma dCut_split:
  fixes e :: "(real, 'c::executable_euclidean_space, 's) hyexpr"
  assumes "\<lbrace>[p]\<^sub>P\<rbrace>ode F' B\<lbrace>[p]\<^sub>P\<rbrace>\<^sub>u" "\<lbrace>[p \<and>\<^sub>P q]\<^sub>P\<rbrace>ode F' (B \<and> [p]\<^sub>P)\<lbrace>[p \<and>\<^sub>P q]\<^sub>P\<rbrace>\<^sub>u"
  shows "\<lbrace>[p \<and>\<^sub>P q]\<^sub>P\<rbrace>ode F' B\<lbrace>[p \<and>\<^sub>P q]\<^sub>P\<rbrace>\<^sub>u"
  by (metis assms dCut hoare_r_weaken_pre(1) hyprop_eval.simps(4) hyprop_pred_def)

end