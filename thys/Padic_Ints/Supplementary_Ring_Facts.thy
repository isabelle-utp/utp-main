theory Supplementary_Ring_Facts
imports "HOL-Algebra.Ring" 
        "HOL-Algebra.UnivPoly"
        "HOL-Algebra.Subrings"

begin

section\<open>Supplementary Ring Facts\<close>

text\<open>The nonzero elements of a ring.\<close>

definition nonzero :: "('a, 'b) ring_scheme \<Rightarrow> 'a set" where
"nonzero R = {a \<in> carrier R. a \<noteq> \<zero>\<^bsub>R\<^esub>}"


lemma zero_not_in_nonzero:
"\<zero>\<^bsub>R\<^esub> \<notin> nonzero R"
  unfolding nonzero_def by blast 

lemma(in domain) nonzero_memI:
  assumes "a \<in> carrier R"
  assumes "a \<noteq> \<zero>"
  shows "a \<in> nonzero R"
  using assms by(simp add: nonzero_def)

lemma(in domain) nonzero_memE:
  assumes "a \<in> nonzero R"
  shows "a \<in> carrier R" "a \<noteq>\<zero>"
  using assms by(auto simp: nonzero_def)

lemma(in domain) not_nonzero_memE:
  assumes "a \<notin> nonzero R"
  assumes "a \<in> carrier R"
  shows "a = \<zero>"
  using assms 
  by (simp add: nonzero_def)

lemma(in domain) not_nonzero_memI:
  assumes "a = \<zero>"
  shows "a \<notin> nonzero R"
  using assms nonzero_memE(2) by auto

lemma(in domain) nonzero_closed:
  assumes "a \<in> nonzero R"
  shows "a \<in> carrier R"
  using assms 
  by (simp add: nonzero_def)

lemma(in domain) nonzero_mult_in_car:
  assumes "a \<in> nonzero R"
  assumes "b \<in> nonzero R"
  shows "a \<otimes> b \<in> carrier R"
  using assms 
  by (simp add: nonzero_def)

lemma(in domain) nonzero_mult_closed:
  assumes "a \<in> nonzero R"
  assumes "b \<in> nonzero R"
  shows "a \<otimes> b \<in> nonzero R"
  apply(rule nonzero_memI)
  using assms nonzero_memE apply blast
    using assms nonzero_memE 
    by (simp add: integral_iff)    

lemma(in domain) nonzero_one_closed:
"\<one> \<in> nonzero R"
  by (simp add: nonzero_def)

lemma(in domain) one_nonzero:
"\<one> \<in> nonzero R"
  by (simp add: nonzero_one_closed)

lemma(in domain) nat_pow_nonzero:
  assumes "x \<in>nonzero R"
  shows "x[^](n::nat) \<in> nonzero R"
  unfolding nonzero_def 
  apply(induction n)
  using assms integral_iff nonzero_closed zero_not_in_nonzero by auto

lemma(in monoid) Units_int_pow_closed:
  assumes "x \<in> Units G"
  shows "x[^](n::int) \<in> Units G"
  by (metis Units_pow_closed assms int_pow_def2 monoid.Units_inv_Units monoid_axioms)

lemma(in comm_monoid) UnitsI:
  assumes "a \<in> carrier G"
  assumes "b \<in> carrier G"
  assumes "a \<otimes> b = \<one>"
  shows "a \<in> Units G" "b \<in> Units G" 
  unfolding Units_def using comm_monoid_axioms_def assms m_comm[of a b] 
  by auto 

lemma(in comm_monoid) is_invI:
  assumes "a \<in> carrier G"
  assumes "b \<in> carrier G"
  assumes "a \<otimes> b = \<one>"
  shows "inv\<^bsub>G\<^esub> b = a" "inv\<^bsub>G\<^esub> a = b"
  using assms inv_char m_comm 
  by auto

lemma(in ring) ring_in_Units_imp_not_zero:
  assumes "\<one> \<noteq> \<zero>"
  assumes "a \<in> Units R"
  shows "a \<noteq> \<zero>"
  using assms monoid.Units_l_cancel
  by (metis l_null  monoid_axioms one_closed zero_closed)

lemma(in ring) Units_nonzero:
  assumes "u \<in> Units R"
  assumes "\<one>\<^bsub>R\<^esub> \<noteq> \<zero>\<^bsub>R\<^esub>"
  shows "u \<in> nonzero R"
proof-
  have "u \<in>carrier R" 
    using Units_closed assms by auto
  have "u \<noteq>\<zero>" 
    using Units_r_inv_ex assms(1) assms(2) 
    by force 
  thus ?thesis 
    by (simp add: \<open>u \<in> carrier R\<close> nonzero_def)
qed


lemma(in ring) Units_inverse:
  assumes "u \<in> Units R"
  shows "inv u \<in> Units R"
  by (simp add: assms)

lemma(in cring) invI:  
  assumes "x \<in> carrier R"
  assumes "y \<in> carrier R"
  assumes "x \<otimes>\<^bsub>R\<^esub> y = \<one>\<^bsub>R\<^esub>"
  shows "y = inv \<^bsub>R\<^esub> x"
        "x = inv \<^bsub>R\<^esub> y"
  using assms(1) assms(2) assms(3) is_invI 
  by auto 

lemma(in cring) inv_cancelR:
  assumes "x \<in> Units R"
  assumes "y \<in> carrier R"
  assumes "z \<in> carrier R"
  assumes "y = x \<otimes>\<^bsub>R\<^esub> z"
  shows "inv\<^bsub>R\<^esub> x \<otimes>\<^bsub>R\<^esub> y = z"
        "y \<otimes>\<^bsub>R\<^esub> (inv\<^bsub>R\<^esub> x)  = z"
  apply (metis Units_closed assms(1) assms(3) assms(4) cring.cring_simprules(12) 
    is_cring m_assoc monoid.Units_inv_closed monoid.Units_l_inv monoid_axioms)
  by (metis Units_closed assms(1) assms(3) assms(4) m_assoc m_comm monoid.Units_inv_closed 
      monoid.Units_r_inv monoid.r_one monoid_axioms)
   
lemma(in cring) inv_cancelL:
  assumes "x \<in> Units R"
  assumes "y \<in> carrier R"
  assumes "z \<in> carrier R"
  assumes "y = z \<otimes>\<^bsub>R\<^esub> x"
  shows "inv\<^bsub>R\<^esub> x \<otimes>\<^bsub>R\<^esub> y = z"
        "y \<otimes>\<^bsub>R\<^esub> (inv\<^bsub>R\<^esub> x)  = z"
  apply (simp add: Units_closed assms(1) assms(3) assms(4) m_lcomm)
  by (simp add: Units_closed assms(1) assms(3) assms(4) m_assoc)


end
