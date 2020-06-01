section \<open> Differential Induction \<close>

theory utp_hyprog_dinv
  imports 
    utp_hyprog_dL
    utp_hyprog_deriv
begin

lemma cvec_lemma: "\<lparr>cvec\<^sub>v = x, \<dots> = hybs.more s\<rparr> = s\<lparr>cvec\<^sub>v := x\<rparr>"
  by (auto)

find_theorems continuous Deriv.differentiable

lemma derivation_lemma1:
  fixes e :: "('a::ordered_euclidean_space, 'c::executable_euclidean_space, 's) hyexpr"
  assumes "differentiable\<^sub>e e" "(F has_vector_derivative \<lbrakk>F'\<rbrakk>\<^sub>e (F t)) (at t within A)"
  shows "((\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = x, \<dots> = s\<rparr>)) \<circ> F has_vector_derivative \<lbrakk>F' \<turnstile> \<partial>\<^sub>e e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F t, \<dots> = s\<rparr>)) (at t within A)"
  using assms
  apply (rel_auto)
  apply (simp add: frechet_derivative_works)
  apply (rule vector_derivative_diff_chain_within)
   apply blast
  apply (drule_tac x="(F t)" in spec)
  apply (drule_tac x="s" in spec)
  apply (simp add: cvec_lemma has_derivative_at_withinI)
  done

lemma derivation_lemma2:
  assumes "differentiable\<^sub>e e" "t \<in> {0..l}"
  shows "((\<lambda>a. \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = a, \<dots> = s\<rparr>)) has_derivative \<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = x, \<dots> = s\<rparr>)) (at (F t))) (at (F t))"
  using assms
  apply (rel_auto)
  apply (simp add: frechet_derivative_works)
  done

declare [[coercion taut]]

lemma dI_eq:
  fixes e :: "('a::ordered_euclidean_space, 'c::executable_euclidean_space, 's) hyexpr"
  assumes "differentiable\<^sub>e e" "\<^U>(B \<Rightarrow> (F' \<turnstile> \<partial>\<^sub>e e = 0))"
  shows "\<lbrace>e = 0\<rbrace>ode F' B\<lbrace>e = 0\<rbrace>\<^sub>u"
using assms proof (rel_auto')
  fix l :: real and F :: "real \<Rightarrow> 'c" and s :: "'s"
  assume a:
    "\<forall>s. (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) differentiable at (cvec\<^sub>v s)"
    "0 \<le> l"
    "solves F \<lbrakk>F'\<rbrakk>\<^sub>e B s l"
    "\<forall>A. \<lbrakk>B\<rbrakk>\<^sub>e A \<longrightarrow> \<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (A\<lparr>cvec\<^sub>v := x\<rparr>)) (at (cvec\<^sub>v A)) (\<lbrakk>F'\<rbrakk>\<^sub>e (cvec\<^sub>v A)) = 0"
    "\<lbrakk>e\<rbrakk>\<^sub>e \<lparr>cvec\<^sub>v = F 0, \<dots> = s\<rparr> = 0"

  have d0: "\<forall> t\<in>{0..l}. \<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e \<lparr>cvec\<^sub>v = x, \<dots> = s\<rparr>) (at (F t)) (\<lbrakk>F'\<rbrakk>\<^sub>e (F t)) = 0"
  proof
    fix t
    assume "t \<in> {0..l}"
    with a(3) have "\<lbrakk>B\<rbrakk>\<^sub>e \<lparr>cvec\<^sub>v = F t, \<dots> = s\<rparr>"
      by simp
    with a have "\<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F t, \<dots> = s\<rparr>\<lparr>cvec\<^sub>v := x\<rparr>)) (at (cvec\<^sub>v (\<lparr>cvec\<^sub>v = F t, \<dots> = s\<rparr>))) (\<lbrakk>F'\<rbrakk>\<^sub>e (cvec\<^sub>v (\<lparr>cvec\<^sub>v = F t, \<dots> = more\<rparr>))) = 0"
      by (auto)
    thus "\<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e \<lparr>cvec\<^sub>v = x, \<dots> = s\<rparr>) (at (F t)) (\<lbrakk>F'\<rbrakk>\<^sub>e (F t)) = 0"
      by (simp)
  qed

  from a(1) have dE: "\<forall> t\<in>{0..l}. ((\<lambda>a. \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = a, \<dots> = s\<rparr>)) has_derivative \<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = x, \<dots> = s\<rparr>)) (at (F t))) (at (F t))"
    using assms derivation_lemma2 by fastforce 

  have "\<forall>t\<in>{0..l}. ((\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = x, \<dots> = s\<rparr>)) \<circ> F
                      has_vector_derivative 
                    \<lbrakk>F' \<turnstile> \<partial>\<^sub>e e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F t, \<dots> = s\<rparr>)) (at t)"
    using a(3)
    by (simp add: assms(1) derivation_lemma1)

  have "\<forall>s. continuous (at (cvec\<^sub>v s)) (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>))"
    by (simp add: a(1) differentiable_imp_continuous_within)


  hence cont: "continuous_on {0..l} ((\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e \<lparr>cvec\<^sub>v = x, \<dots> = s\<rparr>) \<circ> F)"
    apply (rule_tac continuous_on_compose)
    apply (meson a(3) atLeastAtMost_iff continuous_at_imp_continuous_on has_vector_derivative_continuous)
    apply (auto intro: continuous_at_imp_continuous_on simp add: dE differentiable_imp_continuous_within frechet_derivative_works)
    done  

  from d0 have "\<forall>t\<in>{0..l}. ((\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e \<lparr>cvec\<^sub>v = x, \<dots> = s\<rparr>) \<circ> F has_vector_derivative 0) (at t)"
    by (metis (no_types, lifting) a(3) atLeastAtMost_iff dE has_derivative_at_withinI vector_derivative_diff_chain_within)

  hence "\<forall>t\<in>{0..l}. ((\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = x, \<dots> = s\<rparr>)) \<circ> F has_derivative (\<lambda> x. 0)) (at t)"
    by (simp add: has_vector_derivative_def)

  hence "\<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F l, \<dots> = s\<rparr>) - \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F 0, \<dots> = s\<rparr>) = (\<lambda>x. 0) (l - 0)"
    using mvt_general[of 0 l "(\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = x, \<dots> = s\<rparr>)) \<circ> F" "(\<lambda> _. \<lambda> x. 0)"] cont
    apply (simp add: a(2) less_imp_le comp_def)
    using a(2) antisym_conv2 by blast
  
  thus "\<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F l, \<dots> = s\<rparr>) = 0"
    by (simp add: a(5))
qed

lemma dI_ge:
  fixes e :: "(real, 'c::executable_euclidean_space, 's) hyexpr"
  assumes "differentiable\<^sub>e e" "\<^U>(B \<Rightarrow> 0 \<le> F' \<turnstile> \<partial>\<^sub>e e)"
  shows "\<lbrace>0 \<le> e\<rbrace>ode F' B\<lbrace>0 \<le> e\<rbrace>\<^sub>u" and "\<lbrace>0 < e\<rbrace>ode F' B\<lbrace>0 < e\<rbrace>\<^sub>u"
using assms proof (rel_auto')
  fix l :: real and F :: "real \<Rightarrow> 'c" and s :: "'s"
  assume a:
    "\<forall>s. (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := x\<rparr>)) differentiable at (cvec\<^sub>v s)"
    "0 \<le> l"
    "solves F \<lbrakk>F'\<rbrakk>\<^sub>e B s l"
    "\<forall>A. \<lbrakk>B\<rbrakk>\<^sub>e A \<longrightarrow> \<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (A\<lparr>cvec\<^sub>v := x\<rparr>)) (at (cvec\<^sub>v A)) (\<lbrakk>F'\<rbrakk>\<^sub>e (cvec\<^sub>v A)) \<ge> 0"

  have d0: "\<forall> t\<in>{0..l}. \<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = x, \<dots> = s\<rparr>)) (at (F t)) (\<lbrakk>F'\<rbrakk>\<^sub>e (F t)) \<ge> 0"
  proof
    fix t
    assume "t \<in> {0..l}"
    with a(3) have "\<lbrakk>B\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F t, \<dots> = s\<rparr>)"
      by simp
    with a(4) have "\<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F t, \<dots> = s\<rparr>\<lparr>cvec\<^sub>v := x\<rparr>)) (at (cvec\<^sub>v (\<lparr>cvec\<^sub>v = F t, \<dots> = s\<rparr>))) (\<lbrakk>F'\<rbrakk>\<^sub>e (cvec\<^sub>v (\<lparr>cvec\<^sub>v = F t, \<dots> = s\<rparr>))) \<ge> 0"
      by (auto)
    thus "\<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = x, \<dots> = s\<rparr>)) (at (F t)) (\<lbrakk>F'\<rbrakk>\<^sub>e (F t)) \<ge> 0"
      by (simp)
  qed

  from a(1) have dE: "\<forall> t\<in>{0..l}. ((\<lambda>a. \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = a, \<dots> = s\<rparr>)) has_derivative \<partial> (\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = x, \<dots> = s\<rparr>)) (at (F t))) (at (F t))"
    using assms(1) derivation_lemma2 by fastforce

  hence "\<forall>t\<in>{0..l}. ((\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = x, \<dots> = s\<rparr>)) \<circ> F
                      has_vector_derivative 
                    \<lbrakk>F' \<turnstile> \<partial>\<^sub>e e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F t, \<dots> = s\<rparr>)) (at t)"
    by (simp add: a(3) assms(1) derivation_lemma1)

  hence "\<forall>t\<in>{0..l}. ((\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = x, \<dots> = s\<rparr>)) \<circ> F
                      has_derivative 
                    (\<lambda> x. x *\<^sub>R \<lbrakk>F' \<turnstile>  \<partial>\<^sub>e e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F t, \<dots> = s\<rparr>))) (at t)"
    using has_vector_derivative_def by blast
  hence "\<exists>x\<in>{0..l}. \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F l, \<dots> = s\<rparr>) - \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F 0, \<dots> = s\<rparr>) = l * \<lbrakk>F' \<turnstile>  \<partial>\<^sub>e e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F x, \<dots> = s\<rparr>)"
    using a(2) mvt_very_simple[of 0 l "(\<lambda>x. \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = x, \<dots> = s\<rparr>)) \<circ> F" "\<lambda> t. (\<lambda> x. x *\<^sub>R \<lbrakk>F' \<turnstile>  \<partial>\<^sub>e e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F t, \<dots> = s\<rparr>))"]
    by (simp add: has_derivative_at_withinI)

  then obtain t 
    where "0 \<le> t" "t \<le> l" "\<lbrakk>F' \<turnstile>  \<partial>\<^sub>e e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F t, \<dots> = s\<rparr>) \<ge> 0" "\<lbrakk>F' \<turnstile>  \<partial>\<^sub>e e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F l, \<dots> = s\<rparr>) \<ge> 0"
          "\<lbrakk>e\<rbrakk>\<^sub>e \<lparr>cvec\<^sub>v = F l, \<dots> = s\<rparr> - \<lbrakk>e\<rbrakk>\<^sub>e \<lparr>cvec\<^sub>v = F 0, \<dots> = s\<rparr> = l * \<lbrakk>F' \<turnstile>  \<partial>\<^sub>e e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F t, \<dots> = s\<rparr>)"
    apply (simp add: uexpr_deriv.rep_eq lens_defs)
    using d0 by force

  moreover have "l * \<lbrakk>F' \<turnstile> \<partial>\<^sub>e e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F t, \<dots> = s\<rparr>) \<ge> 0"
    using a(2) calculation(3) by auto

  ultimately show 
    "\<lbrakk>e\<rbrakk>\<^sub>e \<lparr>cvec\<^sub>v = F 0, \<dots> = s\<rparr> \<ge> 0 \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F l, \<dots> = s\<rparr>) \<ge> 0" and 
    "\<lbrakk>e\<rbrakk>\<^sub>e \<lparr>cvec\<^sub>v = F 0, \<dots> = s\<rparr> > 0 \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F l, \<dots> = s\<rparr>) > 0"
    by linarith+

qed

datatype ('c::executable_euclidean_space, 's) hyprop =
  Eq "(real, 'c, 's) hyexpr" "(real, 'c, 's) hyexpr" (infix "=\<^sub>P" 50) |
  Less "(real, 'c, 's) hyexpr" "(real, 'c, 's) hyexpr" (infix "<\<^sub>P" 50) |
  LessEq "(real, 'c, 's) hyexpr" "(real, 'c, 's) hyexpr" (infix "\<le>\<^sub>P" 50) |
  And "('c, 's) hyprop" "('c, 's) hyprop" (infixr "\<and>\<^sub>P" 35) |
  Or "('c, 's) hyprop" "('c, 's) hyprop" (infixr "\<or>\<^sub>P" 30)

abbreviation (input) Greater (infix ">\<^sub>P" 50) where
"Greater x y \<equiv> y <\<^sub>P x"

abbreviation (input) GreaterEq (infix "\<ge>\<^sub>P" 50) where
"GreaterEq x y \<equiv> y \<le>\<^sub>P x"

definition TrueP ("true\<^sub>P") where
"TrueP = Eq \<guillemotleft>0\<guillemotright> \<guillemotleft>0\<guillemotright>"

definition NotEq :: 
  "(real, 'c::executable_euclidean_space, 's) hyexpr \<Rightarrow> (real, 'c, 's) hyexpr \<Rightarrow> ('c, 's) hyprop" (infix "\<noteq>\<^sub>P" 50) where
"NotEq x y = (x <\<^sub>P y \<or>\<^sub>P x >\<^sub>P y)"

fun NotP :: "('c::executable_euclidean_space, 's) hyprop \<Rightarrow> ('c, 's) hyprop" ("\<not>\<^sub>P _" [40] 40) where
"NotP (Eq x y) = NotEq x y" |
"NotP (Less x y) = GreaterEq x y" |
"NotP (LessEq x y) = Greater x y" |
"NotP (And x y) = Or (NotP x) (NotP y)" |
"NotP (Or x y) = And (NotP x) (NotP y)"

definition Implies :: "('c::executable_euclidean_space, 's) hyprop \<Rightarrow> ('c, 's) hyprop \<Rightarrow> ('c, 's) hyprop" (infixr "\<Rightarrow>\<^sub>P" 25) where
"Implies x y = (\<not>\<^sub>P x \<or>\<^sub>P y)"

definition EqEucl :: "('a::executable_euclidean_space, 'c::executable_euclidean_space, 's) hyexpr \<Rightarrow> ('a, 'c, 's) hyexpr \<Rightarrow> ('c, 's) hyprop"
  (infix "=\<^sub>E" 50)
  where "EqEucl e f = foldr (\<and>\<^sub>P) (map (\<lambda> i. bop eucl_nth \<guillemotleft>i\<guillemotright> e =\<^sub>P bop eucl_nth \<guillemotleft>i\<guillemotright> f) [0..<DIM('a::executable_euclidean_space)]) true\<^sub>P"

utp_const Eq Less LessEq And Or Greater GreaterEq NotEq NotP Implies EqEucl

fun hyprop_deriv :: 
  "'c usubst \<Rightarrow> ('c::executable_euclidean_space, 's) hyprop \<Rightarrow> ('c, 's) hyprop" ("(_ \<turnstile> \<partial>\<^sub>P _)" [100, 101] 100) where
"F' \<turnstile> \<partial>\<^sub>P (e =\<^sub>P f) = (F' \<turnstile> \<partial>\<^sub>e e =\<^sub>P F' \<turnstile> \<partial>\<^sub>e f)" |
"F' \<turnstile> \<partial>\<^sub>P (e <\<^sub>P f) = (F' \<turnstile> \<partial>\<^sub>e e \<le>\<^sub>P F' \<turnstile> \<partial>\<^sub>e f)" |
"F' \<turnstile> \<partial>\<^sub>P (e \<le>\<^sub>P f) = (F' \<turnstile> \<partial>\<^sub>e e \<le>\<^sub>P F' \<turnstile> \<partial>\<^sub>e f)" |
"F' \<turnstile> \<partial>\<^sub>P (p \<and>\<^sub>P q) = (F' \<turnstile> \<partial>\<^sub>P p \<and>\<^sub>P F' \<turnstile> \<partial>\<^sub>P q)" |
"F' \<turnstile> \<partial>\<^sub>P (p \<or>\<^sub>P q) = (F' \<turnstile> \<partial>\<^sub>P p \<and>\<^sub>P F' \<turnstile> \<partial>\<^sub>P q)"

utp_const hyprop_deriv

fun hyprop_eval :: "('c::executable_euclidean_space, 's) hyprop \<Rightarrow> ('c, 's) hypred" ("\<lbrakk>_\<rbrakk>\<^sub>P") where
"\<lbrakk>e =\<^sub>P f\<rbrakk>\<^sub>P = (e =\<^sub>u f)" |
"\<lbrakk>e <\<^sub>P f\<rbrakk>\<^sub>P = (e <\<^sub>u f)" |
"\<lbrakk>e \<le>\<^sub>P f\<rbrakk>\<^sub>P = (e \<le>\<^sub>u f)" |
"\<lbrakk>p \<and>\<^sub>P q\<rbrakk>\<^sub>P = (\<lbrakk>p\<rbrakk>\<^sub>P \<and> \<lbrakk>q\<rbrakk>\<^sub>P)" |
"\<lbrakk>p \<or>\<^sub>P q\<rbrakk>\<^sub>P = (\<lbrakk>p\<rbrakk>\<^sub>P \<or> \<lbrakk>q\<rbrakk>\<^sub>P)"

lemma hyprop_eval_TrueP [simp]: "\<lbrakk>true\<^sub>P\<rbrakk>\<^sub>P = true"
  by (simp add: TrueP_def)

lemma hyprop_eval_NotEq [simp]: "\<lbrakk>e \<noteq>\<^sub>P f\<rbrakk>\<^sub>P = (e \<noteq>\<^sub>u f)"
  by (simp add: NotEq_def, rel_auto)

lemma hyprop_eval_NotP [simp]: "\<lbrakk>\<not>\<^sub>P e\<rbrakk>\<^sub>P = (\<not> \<lbrakk>e\<rbrakk>\<^sub>P)"
  by (induct e, simp_all, rel_auto+)

lemma hyprop_eval_Implies [simp]: "\<lbrakk>e \<Rightarrow>\<^sub>P f\<rbrakk>\<^sub>P = (\<lbrakk>e\<rbrakk>\<^sub>P \<Rightarrow> \<lbrakk>f\<rbrakk>\<^sub>P)"
  by (simp add: Implies_def, rel_simp)

lemma uderiv_NotEq [uderiv]:
  "\<lbrakk>F' \<turnstile> \<partial>\<^sub>P (e \<noteq>\<^sub>P f)\<rbrakk>\<^sub>P = ((F' \<turnstile> \<partial>\<^sub>e e) =\<^sub>u (F' \<turnstile> \<partial>\<^sub>e f))"
  by (simp add: NotEq_def, rel_auto)

lemma hyprop_eval_foldr: "\<lbrakk>foldr (\<and>\<^sub>P) xs true\<^sub>P\<rbrakk>\<^sub>P = foldr (\<and>) (map hyprop_eval xs) true"
  by (induct xs, simp_all)

lemma hyprop_eval_deriv_foldr: "\<lbrakk>F' \<turnstile> \<partial>\<^sub>P (foldr (\<and>\<^sub>P) xs true\<^sub>P)\<rbrakk>\<^sub>P = foldr (\<and>) (map (\<lambda> x. \<lbrakk>F' \<turnstile> \<partial>\<^sub>P x\<rbrakk>\<^sub>P) xs) true"
  by (induct xs, simp_all add: TrueP_def)

lemma foldr_uinf:
  "\<lbrakk>foldr (\<squnion>) xs \<bottom>\<rbrakk>\<^sub>e s = foldr (\<and>) (map (\<lambda> x. \<lbrakk>x\<rbrakk>\<^sub>e s) xs) True"
  by (induct xs, rel_auto, simp add: inf_uexpr.rep_eq)

lemma foldr_conj_iff_forall: "foldr (\<and>) xs True = (\<forall> i \<in> set(xs). i)"
  by (induct xs, auto)

lemma exec_eucl_space_eqI:
  fixes x y :: "'a::executable_euclidean_space"
  shows "(\<forall> i\<in>{0..<DIM('a)}. eucl_nth i x = eucl_nth i y) \<Longrightarrow> x = y"
  by (metis Basis_list atLeastLessThan_iff eucl_nth_def eucl_of_list_list_of_eucl euclidean_eqI index_less inner_commute inner_eucl_of_list length_Basis_list length_map list_of_eucl_def order_refl zero_order(1))

lemma uderiv_EqEucl [uderiv]:
  "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow> \<lbrakk>F' \<turnstile> \<partial>\<^sub>P (e =\<^sub>E f)\<rbrakk>\<^sub>P = ((F' \<turnstile> \<partial>\<^sub>e e) =\<^sub>u (F' \<turnstile> \<partial>\<^sub>e f))"
  apply (simp add: EqEucl_def hyprop_eval_deriv_foldr)
  apply (rel_simp, simp add: foldr_uinf)
  apply (simp add: comp_def)
  apply (rel_simp)
  apply (simp add: foldr_conj_iff_forall)
  apply (auto simp add: frechet_derivative_eucl_nth')
  apply (rule exec_eucl_space_eqI)
  apply (simp)
  done

lemma hyprop_eval_EqEucl [simp]: "\<lbrakk>e =\<^sub>E f\<rbrakk>\<^sub>P = (e =\<^sub>u f)"
  apply (simp add: EqEucl_def hyprop_eval_foldr )
  apply (rel_simp, simp add: foldr_uinf comp_def foldr_conj_iff_forall)
  apply (rel_simp)
  apply (auto intro: exec_eucl_space_eqI)
  done

lemma uderiv_NotP [uderiv]:
  "\<lbrakk>F' \<turnstile> \<partial>\<^sub>P (\<not>\<^sub>P e)\<rbrakk>\<^sub>P = undefined"
  apply (induct e) oops \<comment> \<open> Any ideas? \<close>

utp_const hyprop_eval

definition hyprop_pred ("[_]\<^sub>P") where "[p]\<^sub>P = \<lbrakk>p\<rbrakk>\<^sub>P"
              
utp_const hyprop_pred

fun hyprop_differentiable :: "('c::executable_euclidean_space, 's) hyprop \<Rightarrow> bool" ("differentiable\<^sub>P") where
"differentiable\<^sub>P (e =\<^sub>P f) = (differentiable\<^sub>e e \<and> differentiable\<^sub>e f)" |
"differentiable\<^sub>P (e <\<^sub>P f) = (differentiable\<^sub>e e \<and> differentiable\<^sub>e f)" |
"differentiable\<^sub>P (e \<le>\<^sub>P f) = (differentiable\<^sub>e e \<and> differentiable\<^sub>e f)" |
"differentiable\<^sub>P (p \<and>\<^sub>P q) = (differentiable\<^sub>P p \<and> differentiable\<^sub>P q)" |
"differentiable\<^sub>P (p \<or>\<^sub>P q) = (differentiable\<^sub>P p \<and> differentiable\<^sub>P q)"

lemma differentiable_NotEq [simp]: "differentiable\<^sub>P (e \<noteq>\<^sub>P f) = (differentiable\<^sub>e e \<and> differentiable\<^sub>e f)"
  by (auto simp add: NotEq_def)

lemma udifferentiable_foldr:
  "differentiable\<^sub>P (foldr (\<and>\<^sub>P) xs true\<^sub>P) = foldr (\<and>) (map differentiable\<^sub>P xs) True"
  by (induct xs, simp_all add: TrueP_def closure)

lemma udifferentiable_eucl_nth:
  fixes e :: "('a::executable_euclidean_space, _) uexpr"
  assumes "differentiable\<^sub>e e" "k < DIM('a)"
  shows "differentiable\<^sub>e \<^U>(eucl_nth \<guillemotleft>k\<guillemotright> e)"
  using assms
  by (rel_simp, simp add: differentiable_eucl_nth')

lemma foldr_map_True: "foldr (\<and>) (map (\<lambda>x. True) xs) True"
  by (induct xs, simp_all)

lemma udifferentiable_EqEucl [closure]:
  "\<lbrakk> differentiable\<^sub>e e; differentiable\<^sub>e f \<rbrakk> \<Longrightarrow> differentiable\<^sub>P (e =\<^sub>E f)"
  unfolding EqEucl_def
  apply (auto simp add: udifferentiable_foldr comp_def)
  apply (subst map_cong[of _ _ "(\<lambda>x::nat. differentiable\<^sub>e \<^U>(eucl_nth \<guillemotleft>x\<guillemotright> e) \<and> differentiable\<^sub>e \<^U>(eucl_nth \<guillemotleft>x\<guillemotright> f))" "\<lambda> x. True"])
  apply (simp)
   apply (simp add: udifferentiable_eucl_nth)
  apply (simp add:  foldr_map_True)
  done

lemma dInv:
  fixes e :: "(real, 'c::executable_euclidean_space, 's) hyexpr"
  assumes "differentiable\<^sub>P p" "`B \<Rightarrow> \<lbrakk>F' \<turnstile> \<partial>\<^sub>P p\<rbrakk>\<^sub>P`"
  shows "\<lbrace>[p]\<^sub>P\<rbrace>ode F' B\<lbrace>[p]\<^sub>P\<rbrace>\<^sub>u"
using assms proof (simp add: hyprop_pred_def, induct p)
  case (Eq x1 x2)
  hence a: "\<^U>(B \<Rightarrow> F' \<turnstile> \<partial>\<^sub>e x1 = F' \<turnstile> \<partial>\<^sub>e x2)" "differentiable\<^sub>e x1" "differentiable\<^sub>e x2"
    by (auto)
  from a(1) have b: "`B \<Rightarrow> (F' \<turnstile> \<partial>\<^sub>e x1 - F' \<turnstile> \<partial>\<^sub>e x2) = 0`"
    by (rel_auto)
  hence "\<lbrace>(x1 - x2) = 0\<rbrace> ode F' B \<lbrace>(x1 - x2) = 0\<rbrace>\<^sub>u"
    by (simp add: a(2) a(3) dI_eq uderiv closure)
  then show ?case
    by (rel_auto')
next
  case (Less x1 x2)
  hence a: "`B \<Rightarrow> F' \<turnstile> \<partial>\<^sub>e x1 \<le> F' \<turnstile> \<partial>\<^sub>e x2`" "differentiable\<^sub>e x1" "differentiable\<^sub>e x2"
    by (auto)
  from a(1) have b: "`B \<Rightarrow> (F' \<turnstile> \<partial>\<^sub>e x2 - F' \<turnstile> \<partial>\<^sub>e x1) \<ge> 0`"
    by (rel_auto)
  hence "\<lbrace>0 < (x2 - x1)\<rbrace> ode F' B \<lbrace>0 < (x2 - x1)\<rbrace>\<^sub>u"
    by (simp add: a(2) a(3) dI_ge uderiv closure)
  then show ?case
    by (rel_auto')
next
  case (LessEq x1 x2)
  hence a: "`B \<Rightarrow> F' \<turnstile> \<partial>\<^sub>e x1 \<le> F' \<turnstile> \<partial>\<^sub>e x2`" "differentiable\<^sub>e x1" "differentiable\<^sub>e x2"
    by (auto)
  from a(1) have b: "`B \<Rightarrow> (F' \<turnstile> \<partial>\<^sub>e x2 - F' \<turnstile> \<partial>\<^sub>e x1) \<ge> 0`"
    by (rel_auto)
  hence "\<lbrace>0 \<le> (x2 - x1)\<rbrace> ode F' B \<lbrace>0 \<le> (x2 - x1)\<rbrace>\<^sub>u"
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

lemma dInv':
  fixes e :: "(real, 'c::executable_euclidean_space, 's) hyexpr"
  assumes "differentiable\<^sub>P I" "`B \<Rightarrow> \<lbrakk>F' \<turnstile> \<partial>\<^sub>P I\<rbrakk>\<^sub>P`" "`P \<Rightarrow> [I]\<^sub>P`"
  shows "\<lbrace>P\<rbrace>ode F' B\<lbrace>[I]\<^sub>P\<rbrace>\<^sub>u"
  using assms(1) assms(2) assms(3) dInv pre_str_hoare_r by blast

lemma dCut_split:
  fixes e :: "(real, 'c::executable_euclidean_space, 's) hyexpr"
  assumes "\<lbrace>p\<rbrace>ode F' B\<lbrace>p\<rbrace>\<^sub>u" "\<lbrace>q\<rbrace>ode F' (B \<and> p)\<lbrace>q\<rbrace>\<^sub>u"
  shows "\<lbrace>p \<and> q\<rbrace>ode F' B\<lbrace>p \<and> q\<rbrace>\<^sub>u"
  by (meson assms(1) assms(2) dCut hoare_r_conj hoare_r_weaken_pre(1) hoare_r_weaken_pre(2))

text \<open> Differential Induction Tactic \<close>

named_theorems lift_hyprop

text \<open> Algorithm: (1) lift all UTP predicates to syntactic hybrid predicates, (2) apply differential
  induction rule, (3) prove the invariant is differentiable, (4) differentiate the invariant,
  including application of substitutions. \<close>

method dInduct = 
  (simp add: lift_hyprop closure, rule_tac dInv, (simp_all add: hyprop_pred_def)?, simp add: uderiv closure, simp add : uderiv closure usubst)

lemma lift_hyprop_1 [lift_hyprop]: 
  "U(x < y) = [x <\<^sub>P y]\<^sub>P"
  "U(x \<le> y) = [x \<le>\<^sub>P y]\<^sub>P"
  "U(e = f) = [e =\<^sub>E f]\<^sub>P"
  "U([P]\<^sub>P \<and> [Q]\<^sub>P) = [P \<and>\<^sub>P Q]\<^sub>P"
  "U([P]\<^sub>P \<or> [Q]\<^sub>P) = [P \<or>\<^sub>P Q]\<^sub>P"
  by (simp_all add: hyprop_pred_def)

end