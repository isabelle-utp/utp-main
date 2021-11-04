theory Padic_Int_Polynomials
imports Padic_Int_Topology Cring_Poly
begin 

context padic_integers
begin

text\<open>
  This theory states and proves basic lemmas connecting the topology on $\mathbb{Z}_p$ with the
  functions induced by polynomial evaluation over $\mathbb{Z}_p$. This will imply that polynomial 
  evaluation applied to a Cauchy Sequence will always produce a cauchy sequence, which is a key 
  fact in the proof of Hensel's Lemma.
\<close>

type_synonym padic_int_poly = "nat \<Rightarrow> padic_int"

lemma monom_term_car:
  assumes "c \<in> carrier Zp"
  assumes "x \<in> carrier Zp"
  shows "c \<otimes> x[^](n::nat) \<in> carrier Zp"
  using assms  R.nat_pow_closed 
  by (simp add: monoid.nat_pow_closed cring.cring_simprules(5) cring_def ring_def)

text\<open>Univariate polynomial ring over Zp\<close>

abbreviation(input) Zp_x where
"Zp_x \<equiv> UP Zp"

lemma Zp_x_is_UP_cring:
"UP_cring Zp"
  using UP_cring.intro domain_axioms domain_def by auto

lemma Zp_x_is_UP_domain:
"UP_domain Zp"
  by (simp add: UP_domain_def domain_axioms)

lemma Zp_x_domain:
"domain Zp_x "
  by (simp add: UP_domain.UP_domain Zp_x_is_UP_domain)

lemma pow_closed:
  assumes "a \<in> carrier Zp"
  shows "a[^](n::nat) \<in> carrier Zp"
  by (meson domain_axioms domain_def cring_def assms monoid.nat_pow_closed ring_def)

lemma(in ring) pow_zero:
  assumes "(n::nat)>0"
  shows "\<zero>[^] n = \<zero>"
  by (simp add: assms nat_pow_zero)

lemma sum_closed:
  assumes "f \<in> carrier Zp"
  assumes "g \<in> carrier Zp"
  shows "f \<oplus> g \<in>  carrier Zp"
  by (simp add: assms(1) assms(2) cring.cring_simprules(1))

lemma mult_zero:
  assumes "f \<in> carrier Zp"
  shows "f \<otimes> \<zero> = \<zero>"
        "\<zero> \<otimes> f = \<zero>"
   apply (simp add: assms cring.cring_simprules(27))
  by (simp add: assms cring.cring_simprules(26))

lemma monom_poly_is_Zp_continuous:
  assumes "c \<in> carrier Zp"
  assumes "f = monom Zp_x c n"
  shows "is_Zp_continuous (to_fun f)"
  using monomial_is_Zp_continuous assms monom_to_monomial by auto 

lemma degree_0_is_Zp_continuous:
  assumes "f \<in> carrier Zp_x"
  assumes "degree f = 0"
  shows "is_Zp_continuous (to_fun f)"
  using const_to_constant[of "lcf f"] assms constant_is_Zp_continuous ltrm_deg_0 
  by (simp add: cfs_closed)

lemma UP_sum_is_Zp_continuous:
  assumes "a \<in> carrier Zp_x"
  assumes "b \<in> carrier Zp_x"
  assumes "is_Zp_continuous (to_fun a)"
  assumes "is_Zp_continuous (to_fun b)"
  shows "is_Zp_continuous (to_fun (a \<oplus>\<^bsub>Zp_x\<^esub> b))"
  using sum_of_cont_is_cont assms 
  by (simp add: to_fun_Fun_add)

lemma polynomial_is_Zp_continuous:
  assumes "f \<in> carrier Zp_x"
  shows "is_Zp_continuous (to_fun f)"
  apply(rule poly_induct3)
  apply (simp add: assms)
  using UP_sum_is_Zp_continuous apply blast
  using monom_poly_is_Zp_continuous by blast
end 

text\<open>Notation for polynomial function application\<close>

context padic_integers
begin
notation to_fun (infixl\<open>\<bullet>\<close> 70) 
text\<open>Evaluating polynomials in the residue rings\<close>

lemma res_to_fun_monic_monom:
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "a k = b k"
  shows "(monom Zp_x \<one> n \<bullet> a) k = (monom Zp_x \<one> n \<bullet> b) k"
proof(induction n)
  case 0
  then show ?case 
    using UP_cring.to_fun_X_pow Zp_x_is_UP_domain assms(1) assms(2) nat_pow_0 to_fun_one monom_one 
    by presburger   
next
  case (Suc n)
  fix n::nat
  assume IH: "to_fun (monom Zp_x \<one> n) a k = to_fun (monom Zp_x \<one> n) b k"
  show "to_fun (monom Zp_x \<one> (Suc n)) a k = to_fun (monom Zp_x \<one> (Suc n)) b k"    
  proof-
    have LHS0: "(monom Zp_x \<one> (Suc n) \<bullet> a) k = ((monom Zp_x \<one> n \<bullet> a) \<otimes> (X \<bullet> a)) k"
      by (simp add: UP_cring.to_fun_monic_monom Zp_x_is_UP_cring assms(1)) 
    then show ?thesis 
      using assms IH  Zp_x_is_UP_domain
          Zp_continuous_is_Zp_closed 
      by (metis (mono_tags, lifting) R.one_closed X_poly_def monom_closed monom_one_Suc 
          residue_of_prod to_fun_X to_fun_mult)                
  qed
qed

lemma res_to_fun_monom:
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "c \<in> carrier Zp"
  assumes "a k = b k"
  shows "(monom Zp_x c n \<bullet> a) k = (monom Zp_x c n \<bullet> b) k"
  using res_to_fun_monic_monom assms 
  by (smt to_fun_monic_monom to_fun_monom residue_of_prod)

lemma to_fun_res_ltrm: 
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "f \<in> carrier Zp_x"
  assumes "a k = b k"
  shows "((ltrm f)\<bullet>a) k = ((ltrm f)\<bullet>b) k"
  by (simp add: lcf_closed assms(1) assms(2) assms(3) assms(4) res_to_fun_monom)

text\<open>Polynomial application commutes with taking residues\<close>
lemma to_fun_res:
  assumes "f \<in> carrier Zp_x"
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "a k = b k"
  shows "(f\<bullet>a) k = (f\<bullet>b) k"
  apply(rule poly_induct3[of f])
  apply (simp add: assms(1))
  using assms(2) assms(3) to_fun_plus residue_of_sum apply presburger
  using assms(2) assms(3) assms(4) res_to_fun_monom by blast


text\<open>If a and b have equal kth residues, then so do f'(a) and f'(b)\<close>

lemma deriv_res:
  assumes "f \<in> carrier Zp_x"
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "a k = b k"
  shows "(deriv f a) k = (deriv f b) k"
  using assms to_fun_res[of "pderiv f" a b k] 
  by (simp add: pderiv_closed pderiv_eval_deriv)

text\<open>Propositions about evaluation:\<close>


lemma to_fun_monom_plus:
  assumes "a \<in> carrier Zp"
  assumes "g \<in> carrier Zp_x"
  assumes "c \<in> carrier Zp"
  shows "(monom Zp_x a n \<oplus>\<^bsub>Zp_x\<^esub> g)\<bullet>c = a \<otimes> c[^]n \<oplus> (g \<bullet> c)"
  by (simp add: assms(1) assms(2) assms(3) to_fun_monom to_fun_plus)

lemma to_fun_monom_minus:
  assumes "a \<in> carrier Zp"
  assumes "g \<in> carrier Zp_x"
  assumes "c \<in> carrier Zp"
  shows "(monom Zp_x a n \<ominus>\<^bsub>Zp_x\<^esub> g)\<bullet>c = a \<otimes> c[^]n \<ominus> (g \<bullet> c)"
  by (simp add: UP_cring.to_fun_diff Zp_x_is_UP_cring assms(1) assms(2) assms(3) to_fun_monom)

end

end
