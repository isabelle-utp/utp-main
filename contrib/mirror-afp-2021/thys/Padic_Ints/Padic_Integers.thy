theory Padic_Integers
  imports Padic_Construction
          Extended_Int
          Supplementary_Ring_Facts
          "HOL-Algebra.Subrings"
          "HOL-Number_Theory.Residues"
          "HOL-Algebra.Multiplicative_Group" 

begin

text\<open>
  In what follows we establish a locale for reasoning about the ring of $p$-adic integers for a 
  fixed prime $p$. We will elaborate on the basic metric properties of $\mathbb{Z}_p$ and construct
  the angular component maps to the residue rings.
\<close>

section\<open>A Locale for $p$-adic Integer Rings\<close>
locale padic_integers =
fixes Zp:: "_ ring" (structure)
fixes p
defines "Zp \<equiv> padic_int p"
assumes prime: "prime p"

sublocale padic_integers < UPZ?: UP Zp "UP Zp"
  by simp

sublocale padic_integers < Zp?:UP_cring Zp "UP Zp"
  unfolding UP_cring_def 
  by(auto simp add: Zp_def padic_int_is_cring prime)

sublocale padic_integers < Zp?:ring Zp
  using Zp_def cring.axioms(1) padic_int_is_cring prime 
  by blast
  
sublocale padic_integers < Zp?:cring Zp
  by (simp add: Zp_def padic_int_is_cring prime)

sublocale padic_integers < Zp?:domain Zp
  by (simp add: Zp_def padic_int_is_domain padic_integers.prime padic_integers_axioms)


context padic_integers
begin 

lemma Zp_defs:
"\<one> = padic_one p"
"\<zero> = padic_zero p"
"carrier Zp = padic_set p"
"(\<otimes>) = padic_mult p"
"(\<oplus>) = padic_add p"
  unfolding Zp_def using padic_int_simps by auto 

end

(*************************************************************************************************)
(*************************************************************************************************)
(***********************)section \<open>Residue Rings\<close>(*************************************)
(*************************************************************************************************)
(*************************************************************************************************) 

lemma(in field) field_inv:
  assumes "a \<in> carrier R"
  assumes "a \<noteq>\<zero>"
  shows "inv\<^bsub>R\<^esub> a \<otimes> a = \<one>"
        "a \<otimes> inv\<^bsub>R\<^esub> a = \<one>"
        "inv \<^bsub>R\<^esub> a \<in> carrier R"
proof-
  have "a \<in> Units R"
    using assms by (simp add: local.field_Units)
  then show "inv\<^bsub>R\<^esub> a \<otimes> a = \<one>" 
    by simp
  show "a \<otimes> inv a = \<one>" 
    using \<open>a \<in> Units R\<close> by auto
  show "inv \<^bsub>R\<^esub> a \<in> carrier R"
    by (simp add: \<open>a \<in> Units R\<close>)
qed

text\<open>$p_residue$ defines the standard projection maps between residue rings:\<close>

definition(in padic_integers) p_residue:: "nat \<Rightarrow> int \<Rightarrow> _" where
"p_residue m n \<equiv> residue (p^m) n"

lemma(in padic_integers) p_residue_alt_def:
"p_residue m n = n mod (p^m)"
  using residue_def 
  by (simp add: p_residue_def)

lemma(in padic_integers) p_residue_range:
"p_residue m n \<in> {0..<p^m}"
  using p_residue_def int_ops(6) prime prime_gt_0_nat 
  by (metis Euclidean_Division.pos_mod_bound Euclidean_Division.pos_mod_sign atLeastLessThan_iff p_residue_alt_def prime_gt_0_int zero_less_power)

lemma(in padic_integers) p_residue_mod:
  assumes "m > k"
  shows "p_residue k (p_residue m n)  = p_residue k n"  
  using assms 
  unfolding p_residue_def residue_def
  by (simp add: le_imp_power_dvd mod_mod_cancel)
  
text\<open>Compatibility of p\_residue with elements of $\mathbb{Z}_p$:\<close>

lemma(in padic_integers) p_residue_padic_int:
  assumes "x \<in> carrier Zp"
  assumes "m \<ge> k"
  shows "p_residue k (x m) = x k"
  using Zp_def assms(1) assms(2) padic_set_res_coherent prime 
  by (simp add: p_residue_def padic_int_simps(5))

text\<open>Definition of residue rings:\<close>

abbreviation(in padic_integers) (input) Zp_res_ring:: "nat \<Rightarrow> _ ring" where
"(Zp_res_ring n) \<equiv> residue_ring (p^n)"

lemma (in padic_integers) p_res_ring_zero:
"\<zero>\<^bsub>Zp_res_ring k\<^esub> = 0"
 by (simp add: residue_ring_def)

lemma (in padic_integers) p_res_ring_one:
  assumes "k > 0"
  shows "\<one>\<^bsub>Zp_res_ring k\<^esub> = 1"
  using assms 
 by (simp add: residue_ring_def)

lemma (in padic_integers) p_res_ring_car:
"carrier (Zp_res_ring k) = {0..<p^k}"
  using residue_ring_def[of "p^k"] 
  by auto

lemma(in padic_integers) p_residue_range':
"p_residue m n \<in> carrier (Zp_res_ring m)"
  using p_residue_range  residue_ring_def prime prime_gt_0_nat p_residue_def 
  by fastforce

text\<open>First residue ring is a field:\<close>

lemma(in padic_integers) p_res_ring_1_field:
"field (Zp_res_ring 1)"
  by (metis int_nat_eq power_one_right prime prime_ge_0_int prime_nat_int_transfer residues_prime.intro residues_prime.is_field)

text\<open>$0^{th}$ residue ring is the zero ring:\<close>

lemma(in padic_integers) p_res_ring_0:
"carrier (Zp_res_ring 0) = {0}" 
  by (simp add:  residue_ring_def) 

lemma(in padic_integers) p_res_ring_0':
  assumes "x \<in> carrier (Zp_res_ring 0)"
  shows "x = 0"
  using p_res_ring_0 assms by blast 

text\<open>If $m>0$ then $Zp\_res\_ring m$ is an instance of the residues locale:\<close>

lemma(in padic_integers) p_residues:
  assumes "m >0"
  shows "residues (p^m)" 
proof-
  have "p^m > 1" 
    using assms 
    by (simp add: prime prime_gt_1_int)    
  then show "residues (p^m)" 
    using less_imp_of_nat_less residues.intro by fastforce 
qed

text\<open>If $m>0$ then $Zp\_res\_ring m$ is a commutative ring:\<close>

lemma(in padic_integers) R_cring:
  assumes "m >0"
  shows "cring (Zp_res_ring m)"
  using p_residues assms residues.cring by auto 

lemma(in padic_integers) R_comm_monoid:
  assumes "m >0"
  shows "comm_monoid (Zp_res_ring m)"
  by (simp add: assms p_residues residues.comm_monoid)

lemma(in padic_integers) zero_rep:
"\<zero> = (\<lambda>m. (p_residue m 0))"  
  unfolding p_residue_def 
  using Zp_defs(2) padic_zero_simp(1) residue_def residue_ring_def by auto

text\<open>The operations on residue rings are just the standard operations on the integers $\mod p^n$. This means that the basic closure properties and algebraic properties of operations on these rings hold for all integers, not just elements of the ring carrier:\<close>

lemma(in padic_integers) residue_add:
  shows "(x \<oplus>\<^bsub>Zp_res_ring k\<^esub> y) = (x + y) mod p^k"
  unfolding residue_ring_def 
  by simp

lemma(in padic_integers) residue_add_closed:
  shows "(x \<oplus>\<^bsub>Zp_res_ring k\<^esub> y) \<in> carrier (Zp_res_ring k)"
    using p_residue_def p_residue_range residue_def residue_ring_def by auto

lemma(in padic_integers) residue_add_closed':
  shows "(x \<oplus>\<^bsub>Zp_res_ring k\<^esub> y) \<in> {0..<p^k}"
  using residue_add_closed residue_ring_def by auto

lemma(in padic_integers) residue_mult:
  shows "(x \<otimes>\<^bsub>Zp_res_ring k\<^esub> y) = (x * y) mod p^k"
  unfolding residue_ring_def 
  by simp

lemma(in padic_integers) residue_mult_closed:
  shows "(x \<otimes>\<^bsub>Zp_res_ring k\<^esub> y) \<in> carrier (Zp_res_ring k)"
  using p_residue_def p_residue_range residue_def residue_ring_def by auto   

lemma(in padic_integers) residue_mult_closed':
  shows "(x \<otimes>\<^bsub>Zp_res_ring k\<^esub> y) \<in> {0..<p^k}"
  using residue_mult_closed residue_ring_def by auto

lemma(in padic_integers) residue_add_assoc:
  shows "(x \<oplus>\<^bsub>Zp_res_ring k\<^esub> y) \<oplus>\<^bsub>Zp_res_ring k\<^esub> z = x \<oplus>\<^bsub>Zp_res_ring k\<^esub> (y \<oplus>\<^bsub>Zp_res_ring k\<^esub> z)"
  using residue_add
  by (simp add: add.commute add.left_commute mod_add_right_eq)

lemma(in padic_integers) residue_mult_comm:
  shows "x \<otimes>\<^bsub>Zp_res_ring k\<^esub> y = y \<otimes>\<^bsub>Zp_res_ring k\<^esub> x"
  using residue_mult
  by (simp add: mult.commute) 

lemma(in padic_integers) residue_mult_assoc:
  shows "(x \<otimes>\<^bsub>Zp_res_ring k\<^esub> y) \<otimes>\<^bsub>Zp_res_ring k\<^esub> z = x \<otimes>\<^bsub>Zp_res_ring k\<^esub> (y \<otimes>\<^bsub>Zp_res_ring k\<^esub> z)"
  using residue_mult 
  by (simp add: mod_mult_left_eq mod_mult_right_eq mult.assoc)

lemma(in padic_integers) residue_add_comm:
  shows "x \<oplus>\<^bsub>Zp_res_ring k\<^esub> y = y \<oplus>\<^bsub>Zp_res_ring k\<^esub> x"
  using residue_add
  by presburger

lemma(in padic_integers) residue_minus_car:
  assumes "y \<in> carrier (Zp_res_ring k)"
  shows "(x \<ominus>\<^bsub>Zp_res_ring k\<^esub> y) = (x - y) mod p^k" 
proof(cases "k = 0")
  case True
  then show ?thesis   
    using residue_ring_def  a_minus_def 
    by(simp add: a_minus_def residue_ring_def)  
next
  case False
    have "(x \<ominus>\<^bsub>Zp_res_ring k\<^esub> y) \<oplus>\<^bsub>Zp_res_ring k\<^esub> y = x \<oplus>\<^bsub>Zp_res_ring k\<^esub> (\<ominus>\<^bsub>Zp_res_ring k\<^esub> y \<oplus>\<^bsub>Zp_res_ring k\<^esub> y)"
      by (simp add: a_minus_def residue_add_assoc)
    then have 0: "(x \<ominus>\<^bsub>Zp_res_ring k\<^esub> y) \<oplus>\<^bsub>Zp_res_ring k\<^esub> y = x mod p^k"
      using assms False 
      by (smt cring.cring_simprules(9) prime residue_add residues.cring residues.res_zero_eq residues_n)
    have 1: "x mod p ^ k = ((x - y) mod p ^ k + y) mod p ^ k"
    proof -
      have f1: "x - y = x + - 1 * y"
        by auto
      have "y + (x + - 1 * y) = x"
        by simp
      then show ?thesis
        using f1 by presburger
    qed
    have "(x \<ominus>\<^bsub>Zp_res_ring k\<^esub> y) \<oplus>\<^bsub>Zp_res_ring k\<^esub> y = (x - y) mod p^k \<oplus>\<^bsub>Zp_res_ring k\<^esub> y"
      using residue_add[of k "(x - y) mod p^k" y] 0 1 
      by linarith
    then show ?thesis using assms residue_add_closed 
      by (metis False a_minus_def cring.cring_simprules(10) cring.cring_simprules(19) 
          prime residues.cring residues.mod_in_carrier residues_n)
qed

lemma(in padic_integers) residue_a_inv:
  shows "\<ominus>\<^bsub>Zp_res_ring k\<^esub> y = \<ominus>\<^bsub>Zp_res_ring k\<^esub> (y mod p^k)" 
proof-
  have "y \<oplus>\<^bsub>Zp_res_ring k\<^esub> (\<ominus>\<^bsub>Zp_res_ring k\<^esub> (y mod p^k)) = (y mod p^k) \<oplus>\<^bsub>Zp_res_ring k\<^esub> (\<ominus>\<^bsub>Zp_res_ring k\<^esub> (y mod p^k)) "
    using residue_minus_car[of "\<ominus>\<^bsub>Zp_res_ring k\<^esub> (y mod p^k)" k y] residue_add 
    by (simp add: mod_add_left_eq)
  then have 0: "y \<oplus>\<^bsub>Zp_res_ring k\<^esub> (\<ominus>\<^bsub>Zp_res_ring k\<^esub> (y mod p^k)) = \<zero>\<^bsub>Zp_res_ring k\<^esub>"
    by (metis cring.cring_simprules(17) p_res_ring_zero padic_integers.p_res_ring_0' 
        padic_integers_axioms prime residue_add_closed residues.cring residues.mod_in_carrier residues_n)    
  have 1: "(\<ominus>\<^bsub>Zp_res_ring k\<^esub> (y mod p^k)) \<oplus>\<^bsub>Zp_res_ring k\<^esub> y = \<zero>\<^bsub>Zp_res_ring k\<^esub>"
    using residue_add_comm 0 by auto 
  have 2: "\<And>x. x \<in> carrier (Zp_res_ring k) \<and> x \<oplus>\<^bsub>Zp_res_ring k\<^esub> y = \<zero>\<^bsub>Zp_res_ring k\<^esub> \<and> y \<oplus>\<^bsub>Zp_res_ring k\<^esub> x = \<zero>\<^bsub>Zp_res_ring k\<^esub> \<Longrightarrow> x = \<ominus>\<^bsub>Zp_res_ring k\<^esub> (y mod p^k)"
    using 0 1 
    by (metis cring.cring_simprules(3) cring.cring_simprules(8) mod_by_1 padic_integers.p_res_ring_0'
        padic_integers.p_res_ring_zero padic_integers_axioms power_0 prime residue_1_prop 
        residue_add_assoc residues.cring residues.mod_in_carrier residues_n)          
  have 3: "carrier (add_monoid (residue_ring (p ^ k))) = carrier (Zp_res_ring k)"
    by simp
  have 4: "(\<otimes>\<^bsub>add_monoid (residue_ring (p ^ k))\<^esub>) = (\<oplus>\<^bsub>Zp_res_ring k\<^esub>)"
    by simp
  have 5: "\<And>x. x \<in> carrier (add_monoid (residue_ring (p ^ k))) \<and>
             x \<otimes>\<^bsub>add_monoid (residue_ring (p ^ k))\<^esub> y = \<one>\<^bsub>add_monoid (residue_ring (p ^ k))\<^esub> \<and> 
            y \<otimes>\<^bsub>add_monoid (residue_ring (p ^ k))\<^esub> x = \<one>\<^bsub>add_monoid (residue_ring (p ^ k))\<^esub>
             \<Longrightarrow> x = \<ominus>\<^bsub>Zp_res_ring k\<^esub> (y mod p^k)"
    using 0 1 2 3 4 
    by simp     
  show ?thesis
    unfolding a_inv_def m_inv_def
    apply(rule the_equality)
    using 1 2 3 4 5    unfolding a_inv_def m_inv_def
     apply (metis (no_types, lifting) "0" "1" cring.cring_simprules(3) mod_by_1 
        monoid.select_convs(2) padic_integers.p_res_ring_zero padic_integers_axioms power_0 prime
        residue_1_prop residue_add_closed residues.cring residues.mod_in_carrier residues_n)
    using 1 2 3 4 5    unfolding a_inv_def m_inv_def
    by blast
qed        

lemma(in padic_integers) residue_a_inv_closed:
"\<ominus>\<^bsub>Zp_res_ring k\<^esub> y \<in> carrier (Zp_res_ring k)" 
  apply(cases "k = 0") 
   apply (metis add.comm_neutral add.commute 
        atLeastLessThanPlusOne_atLeastAtMost_int 
        insert_iff mod_by_1 p_res_ring_car p_res_ring_zero padic_integers.p_res_ring_0 
        padic_integers_axioms power_0 residue_1_prop residue_a_inv)
     by (simp add: prime residues.mod_in_carrier residues.res_neg_eq residues_n)

lemma(in padic_integers) residue_minus:
"(x \<ominus>\<^bsub>Zp_res_ring k\<^esub> y) = (x - y) mod p^k"    
  using residue_minus_car[of "y mod p^k" k x] residue_a_inv[of k y] unfolding a_minus_def 
  by (metis a_minus_def mod_diff_right_eq p_residue_alt_def p_residue_range')

lemma(in padic_integers) residue_minus_closed:
"(x \<ominus>\<^bsub>Zp_res_ring k\<^esub> y) \<in> carrier (Zp_res_ring k)"
  by (simp add: a_minus_def residue_add_closed)

lemma (in padic_integers) residue_plus_zero_r:
"0 \<oplus>\<^bsub>Zp_res_ring k\<^esub> y = y mod p^k"
  by (simp add: residue_add)

lemma (in padic_integers) residue_plus_zero_l:
"y \<oplus>\<^bsub>Zp_res_ring k\<^esub> 0 = y mod p^k"
  by (simp add: residue_add)

lemma (in padic_integers) residue_times_zero_r:
"0 \<otimes>\<^bsub>Zp_res_ring k\<^esub> y = 0"
  by (simp add: residue_mult)

lemma (in padic_integers) residue_times_zero_l:
"y \<otimes>\<^bsub>Zp_res_ring k\<^esub> 0 = 0"
  by (simp add: residue_mult)

lemma (in padic_integers) residue_times_one_r:
"1 \<otimes>\<^bsub>Zp_res_ring k\<^esub> y = y mod p^k"
  by (simp add: residue_mult)

lemma (in padic_integers) residue_times_one_l:
"y \<otimes>\<^bsub>Zp_res_ring k\<^esub> 1 = y mod p^k"
  by (simp add: residue_mult_comm residue_times_one_r)

text\<open>Similarly to the previous lemmas, many identities about taking residues of $p$-adic integers hold even for elements which lie outside the carrier of $\mathbb{Z}_p$:\<close>

lemma (in padic_integers) residue_of_sum:
"(a \<oplus> b) k = (a k) \<oplus>\<^bsub>Zp_res_ring k\<^esub> (b k)"
  using Zp_def residue_ring_def[of "p^k"] Zp_defs(5) padic_add_res 
  by auto

lemma (in padic_integers) residue_of_sum':
 "(a \<oplus> b) k = ((a k) + (b k)) mod p^k"
  using residue_add residue_of_sum by auto

lemma (in padic_integers) residue_closed[simp]:
  assumes "b \<in> carrier Zp"
  shows "b k \<in> carrier (Zp_res_ring k)"
  using Zp_def assms padic_integers.Zp_defs(3) padic_integers_axioms padic_set_res_closed 
  by auto

lemma (in padic_integers) residue_of_diff:
  assumes "b \<in> carrier Zp"
  shows "(a \<ominus> b) k = (a k) \<ominus>\<^bsub>Zp_res_ring k\<^esub> (b k)"
  unfolding a_minus_def 
  using Zp_def add.inv_closed assms(1) padic_a_inv prime residue_of_sum by auto

lemma (in padic_integers) residue_of_prod:
"(a \<otimes> b) k = (a k) \<otimes> \<^bsub>Zp_res_ring k\<^esub> (b k)"
  by (simp add: Zp_defs(4) padic_mult_def)  

lemma (in padic_integers) residue_of_prod':
"(a \<otimes> b) k = ((a k) * (b k)) mod (p^k)"
  by (simp add: residue_mult residue_of_prod)
  
lemma (in padic_integers) residue_of_one:
  assumes "k > 0"
  shows  "\<one> k = \<one>\<^bsub>Zp_res_ring k\<^esub>"
         "\<one> k = 1"
  apply (simp add: Zp_defs(1) assms padic_one_simp(1))
  by (simp add: Zp_def assms padic_int_simps(1) padic_one_simp(1) residue_ring_def)
  
lemma (in padic_integers) residue_of_zero:
  shows  "\<zero> k = \<zero>\<^bsub>Zp_res_ring k\<^esub>"
        "\<zero> k = 0"
  apply (simp add: Zp_defs(2) padic_zero_simp(1))
  by (simp add: p_residue_alt_def zero_rep)

lemma(in padic_integers) Zp_residue_mult_zero:
  assumes  "a k = 0"
  shows "(a \<otimes> b) k = 0" "(b \<otimes> a) k = 0"
  using assms residue_of_prod' 
  by auto 

lemma(in padic_integers) Zp_residue_add_zero:
  assumes "b \<in> carrier Zp"
  assumes "(a:: padic_int) k = 0"
  shows "(a \<oplus> b) k = b k" "(b \<oplus> a) k = b k"
   apply (metis Zp_def assms(1) assms(2) cring.cring_simprules(8) mod_by_1 padic_int_is_cring  power.simps(1) 
        prime residue_add_closed residue_of_sum residue_of_sum' residues.cring residues.res_zero_eq residues_n)
    by (metis Zp_def assms(1) assms(2) cring.cring_simprules(16) mod_by_1 padic_int_is_cring
      power.simps(1) prime residue_add_closed residue_of_sum residue_of_sum' residues.cring 
      residues.res_zero_eq residues_n)

text\<open>P-adic addition and multiplication are globally additive and associative:\<close>

lemma padic_add_assoc0:
assumes "prime p"
shows  "padic_add p (padic_add p x y) z = padic_add p x (padic_add p y z)"
  using assms unfolding padic_add_def
  by (simp add: padic_integers.residue_add_assoc padic_integers_def)

lemma(in padic_integers) add_assoc:
"a \<oplus> b \<oplus> c = a \<oplus> (b \<oplus> c)"
  using padic_add_assoc0[of p a b c] prime Zp_defs by auto 

lemma padic_add_comm0:
assumes "prime p"
shows  "(padic_add p x y)= (padic_add p y x)"
  using assms unfolding padic_add_def
  using padic_integers.residue_add_comm[of p]
  by (simp add: padic_integers_def)

lemma(in padic_integers) add_comm:
"a \<oplus> b = b \<oplus> a"
  using padic_add_comm0[of p a b]  prime Zp_defs by auto 

lemma padic_mult_assoc0:
assumes "prime p"
shows  "padic_mult p (padic_mult p x y) z = padic_mult p x (padic_mult p y z)"
  using assms unfolding padic_mult_def
  by (simp add: padic_integers.residue_mult_assoc padic_integers_def)

lemma(in padic_integers) mult_assoc:
"a \<otimes> b \<otimes> c = a \<otimes> (b \<otimes> c)"
  using padic_mult_assoc0[of p a b c] prime Zp_defs by auto 

lemma padic_mult_comm0:
assumes "prime p"
shows  "(padic_mult p x y)= (padic_mult p y x)"
  using assms unfolding padic_mult_def
  using padic_integers.residue_mult_comm[of p]
  by (simp add: padic_integers_def)

lemma(in padic_integers) mult_comm:
"a \<otimes> b = b \<otimes> a"
  using padic_mult_comm0[of p a b]  prime Zp_defs by auto 

lemma(in padic_integers) mult_zero_l:
"a \<otimes> \<zero> = \<zero>"
proof fix x show "(a \<otimes> \<zero>) x = \<zero> x"
    using Zp_residue_mult_zero[of \<zero> x a]
    by (simp add: residue_of_zero(2))
qed

lemma(in padic_integers) mult_zero_r:
"\<zero> \<otimes> a = \<zero>"
  using mult_zero_l mult_comm by auto 

lemma (in padic_integers) p_residue_ring_car_memI:
  assumes "(m::int) \<ge>0"
  assumes "m < p^k"
  shows "m \<in> carrier (Zp_res_ring k)"
  using residue_ring_def[of "p^k"]  assms(1) assms(2) 
  by auto
  
lemma (in padic_integers) p_residue_ring_car_memE:
  assumes "m \<in> carrier (Zp_res_ring k)"
  shows "m < p^k" "m \<ge> 0"
  using assms residue_ring_def by auto

lemma (in padic_integers) residues_closed:
  assumes "a \<in> carrier Zp"
  shows "a k \<in> carrier (Zp_res_ring k)"
  using Zp_def assms padic_integers.Zp_defs(3) padic_integers_axioms padic_set_res_closed by blast

lemma (in padic_integers) mod_in_carrier:
  "a mod (p^n) \<in> carrier (Zp_res_ring n)"
  using p_residue_alt_def p_residue_range' by auto

lemma (in padic_integers) Zp_residue_a_inv:
  assumes "a \<in> carrier Zp"
  shows "(\<ominus> a) k = \<ominus>\<^bsub>Zp_res_ring k\<^esub> (a k)"
        "(\<ominus> a) k = (- (a k)) mod (p^k)"
  using Zp_def assms padic_a_inv prime apply auto[1]
    using residue_a_inv 
    by (metis Zp_def assms mod_by_1 p_res_ring_zero padic_a_inv padic_integers.prime 
        padic_integers_axioms power_0 residue_1_prop residues.res_neg_eq residues_n)
    
lemma (in padic_integers) residue_of_diff':
  assumes "b \<in> carrier Zp"
  shows "(a \<ominus> b) k = ((a k) - (b k)) mod (p^k)"
  by (simp add: assms residue_minus_car residue_of_diff residues_closed)

lemma (in padic_integers) residue_UnitsI:
  assumes "n \<ge> 1"
  assumes "(k::int) > 0"
  assumes "k < p^n"
  assumes "coprime k p"
  shows "k \<in> Units (Zp_res_ring n)"
  using residues.res_units_eq assms 
  by (metis (mono_tags, lifting) coprime_power_right_iff mem_Collect_eq not_one_le_zero prime residues_n)

lemma (in padic_integers) residue_UnitsE:
  assumes "n \<ge> 1"
  assumes "k \<in> Units (Zp_res_ring n)"
  shows  "coprime k p"
  using residues.res_units_eq assms 
  by (simp add: p_residues)

lemma(in padic_integers) residue_units_nilpotent:
  assumes "m > 0"
  assumes "k = card (Units (Zp_res_ring m))"
  assumes "x \<in> (Units (Zp_res_ring m))"
  shows "x[^]\<^bsub>Zp_res_ring m\<^esub> k = 1"
proof-
  have 0: "group (units_of (Zp_res_ring m))"
    using assms(1) cring_def monoid.units_group padic_integers.R_cring 
          padic_integers_axioms ring_def 
    by blast
  have 1: "finite (Units (Zp_res_ring m))"
    using p_residues assms(1) residues.finite_Units 
    by auto
  have 2: "x[^]\<^bsub>units_of (Zp_res_ring m)\<^esub> (order (units_of (Zp_res_ring m))) = \<one>\<^bsub>units_of (Zp_res_ring m)\<^esub>"
    by (metis "0" assms(3) group.pow_order_eq_1 units_of_carrier)
  then show ?thesis 
    by (metis "1" assms(1) assms(2) assms(3) cring.units_power_order_eq_one
        padic_integers.R_cring padic_integers.p_residues padic_integers_axioms residues.res_one_eq)
qed

lemma (in padic_integers) residue_1_unit:
  assumes "m > 0"
  shows "1 \<in> Units (Zp_res_ring m)"
        "\<one>\<^bsub>Zp_res_ring m\<^esub> \<in> Units (Zp_res_ring m)"
proof-
  have 0: "group (units_of (Zp_res_ring m))"
    using assms(1) cring_def monoid.units_group padic_integers.R_cring 
          padic_integers_axioms ring_def 
    by blast
  have 1: "1 = \<one>\<^bsub>units_of (Zp_res_ring m)\<^esub>"
    by (simp add: residue_ring_def units_of_def)
  have "\<one>\<^bsub>units_of (Zp_res_ring m)\<^esub> \<in> carrier (units_of (Zp_res_ring m))"
    using 0 Group.monoid.intro[of "units_of (Zp_res_ring m)"]
    by (simp add: group.is_monoid)
  then show "1 \<in> Units (Zp_res_ring m)"
    using 1 by (simp add: units_of_carrier)
  then show " \<one>\<^bsub>Zp_res_ring m\<^esub> \<in> Units (Zp_res_ring m) "
    by (simp add: "1" units_of_one)
qed

lemma (in padic_integers) zero_not_in_residue_units:
  assumes "n \<ge> 1"
  shows "(0::int) \<notin>  Units (Zp_res_ring n)"
  using assms p_residues residues.res_units_eq by auto

text\<open>Cardinality bounds on the units of residue rings:\<close>

lemma (in padic_integers) residue_units_card_geq_2:
  assumes "n \<ge>2"
  shows "card (Units (Zp_res_ring n)) \<ge> 2"
proof(cases "p = 2")
  case True
    then have "(3::int) \<in> Units (Zp_res_ring n)"
    proof-
      have "p \<ge>2"
        by (simp add: True)
      then have "p^n \<ge> 2^n"
        using assms 
        by (simp add: True)
      then have "p^n \<ge> 4"
        using assms   power_increasing[of 2 n 2] 
        by (simp add: True)
      then have "(3::int) < p^n"
        by linarith
      then have 0: "(3::int) \<in> carrier (Zp_res_ring n)"
        by (simp add: residue_ring_def)
      have 1: "coprime 3 p"
        by (simp add: True numeral_3_eq_3)
      show ?thesis using residue_UnitsI[of n "3::int"]
        using "1" \<open>3 < p ^ n\<close> assms by linarith        
    qed
    then have 0: "{(1::int), 3} \<subseteq> Units (Zp_res_ring n)"
      using assms padic_integers.residue_1_unit padic_integers_axioms by auto
    have 1: "finite (Units (Zp_res_ring n))"
      using assms padic_integers.p_residues padic_integers_axioms residues.finite_Units by auto
    have 2: "{(1::int),3}\<subseteq>Units (Zp_res_ring n)" 
      using "0" by auto
    have 3: "card {(1::int),3} = 2"
      by simp
    show ?thesis
      using 2 1 
      by (metis "3" card_mono)     
next
    case False
    have "1 \<in> Units (Zp_res_ring n)"
      using assms padic_integers.residue_1_unit padic_integers_axioms by auto
    have "2 \<in> Units (Zp_res_ring n)"
      apply(rule residue_UnitsI)
      using assms apply linarith
        apply simp
    proof-
      show "2 < p^n"
      proof-
        have "p^n > p"
          by (metis One_nat_def assms le_simps(3) numerals(2) power_one_right 
              power_strict_increasing_iff prime prime_gt_1_int)
        then show ?thesis using False  prime prime_gt_1_int[of p]
          by auto           
      qed
      show "coprime 2 p"
        using False 
        by (metis of_nat_numeral prime prime_nat_int_transfer primes_coprime two_is_prime_nat)        
    qed
    then have 0: "{(1::int), 2} \<subseteq> Units (Zp_res_ring n)"
      using \<open>1 \<in> Units (Zp_res_ring n)\<close> by blast
    have 1: "card {(1::int),2} = 2"
      by simp
    then show ?thesis 
      using residues.finite_Units 0 
      by (metis One_nat_def assms card_mono dual_order.trans 
          le_simps(3) one_le_numeral padic_integers.p_residues padic_integers_axioms)
qed

lemma (in padic_integers) residue_ring_card:
"finite (carrier (Zp_res_ring n)) \<and> card (carrier (Zp_res_ring n)) = nat (p^n)"
  using p_res_ring_car[of n] 
  by simp

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

lemma (in padic_integers) residue_of_Units:
  assumes "k > 0"
  assumes "a \<in> Units Zp"
  shows "a k \<in> Units (Zp_res_ring k)"
proof-
  have 0: "a k \<otimes>\<^bsub>Zp_res_ring k\<^esub> (inv \<^bsub>Zp\<^esub> a) k = 1"  
    by (metis R.Units_r_inv assms(1) assms(2) residue_of_one(2) residue_of_prod)
  have 1: "a k \<in> carrier (Zp_res_ring k)"
    by (simp add: R.Units_closed assms(2) residues_closed)
  have 2: "(inv \<^bsub>Zp\<^esub> a) k \<in> carrier (Zp_res_ring k)"
    by (simp add: assms(2) residues_closed)
  show ?thesis using 0 1 2 comm_monoid.UnitsI[of "Zp_res_ring k"]  
    using assms(1) p_residues residues.comm_monoid residues.res_one_eq 
    by presburger
qed  

(*************************************************************************************************)
(*************************************************************************************************)
(**********************)section\<open>$int$ and $nat$ inclusions in $\mathbb{Z}_p$.\<close> (****************************)
(*************************************************************************************************)
(*************************************************************************************************)

lemma(in ring) int_inc_zero:
"[(0::int)]\<cdot> \<one> = \<zero>" 
  by (simp add: add.int_pow_eq_id)

lemma(in ring) int_inc_zero':
  assumes "x \<in> carrier R"
  shows "[(0::int)] \<cdot> x = \<zero>" 
  by (simp add: add.int_pow_eq_id assms)

lemma(in ring) nat_inc_zero:
"[(0::nat)]\<cdot> \<one> = \<zero>" 
  by auto

lemma(in ring) nat_mult_zero:
"[(0::nat)]\<cdot> x = \<zero>" 
  by simp

lemma(in ring) nat_inc_closed:
  fixes n::nat
  shows "[n] \<cdot> \<one> \<in> carrier R"
  by simp

lemma(in ring) nat_mult_closed:
  fixes n::nat
  assumes "x \<in> carrier R"
  shows "[n] \<cdot> x \<in> carrier R"
  by (simp add: assms)

lemma(in ring) int_inc_closed:
  fixes n::int
  shows "[n] \<cdot> \<one> \<in> carrier R"
  by simp

lemma(in ring) int_mult_closed:
  fixes n::int
  assumes "x \<in> carrier R"
  shows "[n] \<cdot> x \<in> carrier R"
  by (simp add: assms)

lemma(in ring) nat_inc_prod:
  fixes n::nat
  fixes m::nat
  shows "[m]\<cdot>([n] \<cdot> \<one>) = [(m*n)]\<cdot>\<one>"
  by (simp add: add.nat_pow_pow mult.commute)

lemma(in ring) nat_inc_prod':
  fixes n::nat
  fixes m::nat
  shows "[(m*n)]\<cdot>\<one> = [m]\<cdot> \<one> \<otimes> ([n] \<cdot> \<one>)"
  by (simp add: add.nat_pow_pow add_pow_rdistr)

lemma(in padic_integers) Zp_nat_inc_zero:
  shows "[(0::nat)] \<cdot> x = \<zero>" 
  by simp

lemma(in padic_integers) Zp_int_inc_zero':
  shows "[(0::int)] \<cdot> x = \<zero>" 
  using Zp_nat_inc_zero[of x]
  unfolding add_pow_def int_pow_def by auto 
  
lemma(in padic_integers) Zp_nat_inc_closed:
  fixes n::nat
  shows "[n] \<cdot> \<one> \<in> carrier Zp"
  by simp

lemma(in padic_integers) Zp_nat_mult_closed:
  fixes n::nat
  assumes "x \<in> carrier Zp"
  shows "[n] \<cdot> x \<in> carrier Zp"
  by (simp add: assms)

lemma(in padic_integers) Zp_int_inc_closed:
  fixes n::int
  shows "[n] \<cdot> \<one> \<in> carrier Zp"
  by simp

lemma(in padic_integers) Zp_int_mult_closed:
  fixes n::int
  assumes "x \<in> carrier Zp"
  shows "[n] \<cdot> x \<in> carrier Zp"
  by (simp add: assms)

text\<open>The following lemmas give a concrete description of the inclusion of integers and natural numbers into $\mathbb{Z}_p$:\<close>

lemma(in padic_integers) Zp_nat_inc_rep:
  fixes n::nat
  shows "[n] \<cdot> \<one> = (\<lambda> m. p_residue m n)" 
  apply(induction n)
   apply (simp add: zero_rep)
proof-
  case (Suc n)
  fix n
  assume A: "[n] \<cdot> \<one> = (\<lambda>m. p_residue m (int n))"
  then have 0: "[Suc n] \<cdot> \<one>  = [n]\<cdot>\<one> \<oplus> \<one>" by auto
  show "[Suc n] \<cdot> \<one> = (\<lambda>m. p_residue m (Suc n))"
  proof fix m
    show "([Suc n] \<cdot> \<one>) m = p_residue m (int (Suc n)) "
    proof(cases "m=0")
      case True
      have 0: "([Suc n] \<cdot> \<one>) m \<in> carrier (Zp_res_ring m)" 
        using Zp_nat_inc_closed padic_set_res_closed 
        by (simp add: residues_closed)        
      then have "([Suc n] \<cdot> \<one>) m = 0"
        using p_res_ring_0 True by blast 
      then show ?thesis 
        by (metis True p_res_ring_0' p_residue_range')        
      next
        case False
        then have R: "residues (p^m)" 
          by (simp add: prime residues_n)
        have "([Suc n] \<cdot> \<one>) m  = ([n]\<cdot>\<one> \<oplus> \<one>) m" 
          by (simp add: "0")         
        then have P0: "([Suc n] \<cdot> \<one>) m  =  p_residue m (int n) \<oplus>\<^bsub>Zp_res_ring m\<^esub> \<one>\<^bsub>Zp_res_ring m\<^esub>" 
          using A False Zp_def padic_add_res padic_one_def Zp_defs(5)
                padic_integers.residue_of_one(1) padic_integers_axioms by auto
        then have P1:"([Suc n] \<cdot> \<one>) m =  p_residue m (int n) \<oplus>\<^bsub>Zp_res_ring m\<^esub> p_residue m (1::int)"
          by (metis R ext p_residue_alt_def residue_add_assoc residue_add_comm residue_plus_zero_r 
              residue_times_one_r residue_times_zero_l residues.res_one_eq)         
        have P2: "p_residue m (int n) \<oplus>\<^bsub>Zp_res_ring m\<^esub> p_residue m 1 = ((int n) mod (p^m)) \<oplus>\<^bsub>Zp_res_ring m\<^esub> 1" 
          using R P0 P1 residue_def residues.res_one_eq 
          by (simp add: residues.res_one_eq p_residue_alt_def)          
        have P3:"((int n) mod (p^m)) \<oplus>\<^bsub>Zp_res_ring m\<^esub> 1 = ((int n) + 1) mod (p^m)" 
          using R residue_ring_def  by (simp add:  mod_add_left_eq) 
        have "p_residue m (int n) \<oplus>\<^bsub>Zp_res_ring m\<^esub> p_residue m 1 = (int (Suc n)) mod (p^m)"
          by (metis P2 P3 add.commute of_nat_Suc p_residue_alt_def residue_add)        
        then show ?thesis
          using False R P1 p_residue_def p_residue_alt_def 
          by auto                            
    qed
  qed
qed

lemma(in padic_integers) Zp_nat_inc_res:
  fixes n::nat
  shows "([n] \<cdot> \<one>) k = n mod (p^k)" 
  using Zp_nat_inc_rep p_residue_def 
  by (simp add: p_residue_alt_def)

lemma(in padic_integers) Zp_int_inc_rep:
  fixes n::int
  shows  "[n] \<cdot> \<one> = (\<lambda> m. p_residue m n )" 
proof(induction n)
  case (nonneg n)
  then show ?case using Zp_nat_inc_rep 
    by (simp add: add_pow_int_ge) 
next
  case (neg n)
  show "\<And>n. [(- int (Suc n))] \<cdot> \<one> = (\<lambda>m. p_residue m (- int (Suc n)))"
  proof
    fix n
    fix m
    show "([(- int (Suc n))] \<cdot> \<one>) m =  p_residue m (- int (Suc n))"
    proof-
      have "[(- int (Suc n))] \<cdot> \<one> = \<ominus> ([(int (Suc n))] \<cdot> \<one>)" 
        using  a_inv_def abelian_group.a_group add_pow_def cring.axioms(1) domain_def 
            negative_zless_0 ring_def R.add.int_pow_neg R.one_closed by blast       
      then have "([(- int (Suc n))] \<cdot> \<one>) m = (\<ominus> ([(int (Suc n))] \<cdot> \<one>)) m" 
        by simp 
      have "\<one> \<in> carrier Zp" 
        using  cring.cring_simprules(6) domain_def by blast 
      have "([(int (Suc n))] \<cdot> \<one>) = ([(Suc n)] \<cdot> \<one>)" 
        by (metis add_pow_def int_pow_int)
      then have "([(int (Suc n))] \<cdot> \<one>) \<in> carrier Zp" using Zp_nat_inc_closed 
        by simp 
      then have P0: "([(- int (Suc n))] \<cdot> \<one>) m =  \<ominus>\<^bsub>Zp_res_ring m\<^esub> (([(int (Suc n))] \<cdot> \<one>) m)"
        using Zp_def prime 
        using \<open>[(- int (Suc n))] \<cdot> \<one> = \<ominus> ([int (Suc n)] \<cdot> \<one>)\<close> padic_integers.Zp_residue_a_inv(1) 
          padic_integers_axioms by auto       
      have "(([(int (Suc n))] \<cdot> \<one>) m) = (p_residue m (Suc n))" 
        using Zp_nat_inc_rep by (simp add: add_pow_int_ge) 
      then have P1: "([(- int (Suc n))] \<cdot> \<one>) m =  \<ominus>\<^bsub>Zp_res_ring m\<^esub>(p_residue m (Suc n))" 
        using P0 by auto
      have  "\<ominus>\<^bsub>Zp_res_ring m\<^esub>(p_residue m (Suc n)) =  p_residue m (- int (Suc n))" 
        proof(cases "m=0")
          case True
          then have 0:"\<ominus>\<^bsub>Zp_res_ring m\<^esub>(p_residue m (Suc n)) =\<ominus>\<^bsub>Zp_res_ring 0\<^esub>(p_residue 0 (Suc n))" 
            by blast 
          then have 1:"\<ominus>\<^bsub>Zp_res_ring m\<^esub>(p_residue m (Suc n)) =\<ominus>\<^bsub>Zp_res_ring 0\<^esub> (p_residue 1 (Suc n))" 
            by (metis p_res_ring_0' residue_a_inv_closed)            
          then have 2:"\<ominus>\<^bsub>Zp_res_ring m\<^esub>(p_residue m (Suc n)) =\<ominus>\<^bsub>Zp_res_ring 0\<^esub> 0" 
            by (metis p_res_ring_0' residue_a_inv_closed)            
          then have 3:"\<ominus>\<^bsub>Zp_res_ring m\<^esub>(p_residue m (Suc n)) =0" 
            using residue_1_prop p_res_ring_0' residue_a_inv_closed by presburger      
          have 4: "p_residue m (- int (Suc n)) \<in> carrier (Zp_res_ring 0)" 
            using p_res_ring_0 True residue_1_zero p_residue_range' by blast            
          then show ?thesis 
            using "3" True residue_1_zero 
            by (simp add: p_res_ring_0')            
        next
          case False
          then have R: "residues (p^m)" 
            using padic_integers.p_residues padic_integers_axioms by blast 
          have "\<ominus>\<^bsub>Zp_res_ring m\<^esub> p_residue m (int (Suc n)) = \<ominus>\<^bsub>Zp_res_ring m\<^esub> (int (Suc n)) mod (p^m) " 
            using R residue_def residues.neg_cong residues.res_neg_eq  p_residue_alt_def 
            by auto            
          then have "\<ominus>\<^bsub>Zp_res_ring m\<^esub> p_residue m (int (Suc n)) = (-(int (Suc n))) mod (p^m)" 
            using R residues.res_neg_eq  by auto 
          then show ?thesis 
            by (simp add: p_residue_alt_def)            
        qed
      then show ?thesis  
        using P1  by linarith 
    qed
  qed
qed

lemma(in padic_integers) Zp_int_inc_res:
  fixes n::int
  shows  "([n] \<cdot> \<one>) k = n mod (p^k)"
  using Zp_int_inc_rep p_residue_def 
  by (simp add: p_residue_alt_def)

abbreviation(in padic_integers)(input) \<p> where
"\<p> \<equiv> [p] \<cdot> \<one>"

lemma(in padic_integers) p_natpow_prod:
"\<p>[^](n::nat) \<otimes> \<p>[^](m::nat) = \<p>[^](n + m)"
  by (simp add: R.nat_pow_mult)
  
lemma(in padic_integers) p_natintpow_prod:
  assumes "(m::int) \<ge> 0"
  shows "\<p>[^](n::nat) \<otimes> \<p>[^]m = \<p>[^](n + m)"
  using p_natpow_prod[of n "nat m"] assms int_pow_def[of Zp \<p> m] int_pow_def[of Zp \<p> "n + m"]
  by (metis (no_types, lifting) int_nat_eq int_pow_int of_nat_add)

lemma(in padic_integers) p_intnatpow_prod:
  assumes "(n::int) \<ge> 0"
  shows "\<p>[^]n \<otimes> \<p>[^](m::nat) = \<p>[^](m + n)"
  using p_natintpow_prod[of n m] assms mult_comm[of "\<p>[^]n" "\<p>[^]m"] 
  by simp

lemma(in padic_integers) p_int_pow_prod:
  assumes "(n::int) \<ge> 0"
  assumes "(m::int) \<ge> 0"
  shows "\<p>[^]n \<otimes> \<p>[^]m = \<p>[^](m + n)"
proof-
  have "nat n + nat m = nat (n + m)"
    using assms 
    by (simp add: nat_add_distrib)
  then have "\<p> [^] (nat n + nat m) = \<p>[^](n + m)"
    using assms 
    by (simp add: \<open>nat n + nat m = nat (n + m)\<close>)
  then show ?thesis   using assms p_natpow_prod[of "nat n" "nat m"]
    by (smt pow_nat)
qed
 
lemma(in padic_integers) p_natpow_prod_Suc:
"\<p> \<otimes> \<p>[^](m::nat) = \<p>[^](Suc m)"
"\<p>[^](m::nat)  \<otimes> \<p> = \<p>[^](Suc m)"
  using R.nat_pow_Suc2  R.nat_pow_Suc by auto 

lemma(in padic_integers) power_residue:
  assumes "a \<in> carrier Zp"
  assumes "k > 0"
  shows "(a[^]\<^bsub>Zp\<^esub> (n::nat)) k = (a k)^n mod (p^k)"
  apply(induction n)
  using p_residues assms(2) residue_of_one(1) residues.one_cong apply auto[1]
  by (simp add: assms(1) mod_mult_left_eq power_commutes residue_of_prod')

(*************************************************************************************************)
(*************************************************************************************************)
(*****************************)  section\<open>The Valuation on $\mathbb{Z}_p$\<close> (**********************************)
(*************************************************************************************************)
(*************************************************************************************************)

  (**********************************************************************)
  (**********************************************************************)
  subsection\<open>The Integer-Valued and Extended Integer-Valued Valuations\<close>
  (**********************************************************************)
  (**********************************************************************)
fun fromeint :: "eint \<Rightarrow> int" where
  "fromeint (eint x) = x"

text\<open>The extended-integer-valued $p$-adic valuation on $\mathbb{Z}_p$:\<close>

definition(in padic_integers) val_Zp  where
"val_Zp = (\<lambda>x. (if (x = \<zero>) then (\<infinity>::eint) else (eint (padic_val p x))))"

text\<open>We also define an integer-valued valuation on the nonzero elements of $\mathbb{Z}_p$, for simplified reasoning\<close>

definition(in padic_integers) ord_Zp where
"ord_Zp = padic_val p"

text\<open>Ord of additive inverse\<close>

lemma(in padic_integers) ord_Zp_of_a_inv:
  assumes "a \<in> nonzero Zp"
  shows "ord_Zp a = ord_Zp (\<ominus>a)" 
  using ord_Zp_def Zp_def assms 
      padic_val_a_inv prime 
    by (simp add: domain.nonzero_memE(1) padic_int_is_domain)

lemma(in padic_integers) val_Zp_of_a_inv:
  assumes "a \<in> carrier Zp"
  shows "val_Zp a = val_Zp (\<ominus>a)" 
  using R.add.inv_eq_1_iff Zp_def assms padic_val_a_inv prime val_Zp_def by auto

text\<open>Ord-based criterion for being nonzero:\<close>

lemma(in padic_integers) ord_of_nonzero:
  assumes "x \<in>carrier Zp"
  assumes "ord_Zp x \<ge>0" 
  shows "x \<noteq> \<zero>"
        "x \<in> nonzero Zp"
proof-
  show "x \<noteq> \<zero>"
  proof
    assume "x = \<zero>"
    then have "ord_Zp x = -1" 
      using ord_Zp_def padic_val_def Zp_def  Zp_defs(2) by auto      
    then show False using assms(2) by auto 
  qed
  then show "x \<in> nonzero Zp" 
    using nonzero_def assms(1) 
    by (simp add: nonzero_def) 
qed

lemma(in padic_integers) not_nonzero_Zp:
  assumes "x \<in> carrier Zp"
  assumes "x \<notin> nonzero Zp"
  shows "x = \<zero>"
  using assms(1) assms(2) nonzero_def by fastforce

lemma(in padic_integers) not_nonzero_Qp:
  assumes "x \<in> carrier Q\<^sub>p"
  assumes "x \<notin> nonzero Q\<^sub>p"
  shows "x = \<zero>\<^bsub>Q\<^sub>p\<^esub>"
  using assms(1) assms(2) nonzero_def by force

text\<open>Relationship between val and ord\<close>

lemma(in padic_integers) val_ord_Zp:
  assumes "a \<noteq> \<zero>"
  shows "val_Zp a = eint (ord_Zp a)" 
  by (simp add: assms ord_Zp_def val_Zp_def) 

lemma(in padic_integers) ord_pos:
  assumes "x \<in> carrier Zp"
  assumes "x \<noteq> \<zero>"
  shows "ord_Zp x \<ge> 0"
proof-
  have "x \<noteq>padic_zero p" 
    using Zp_def assms(2) Zp_defs(2) by auto   
  then have "ord_Zp x = int (LEAST k. x (Suc k) \<noteq> \<zero>\<^bsub>residue_ring (p^Suc k)\<^esub>)"
    using ord_Zp_def padic_val_def by auto  
  then show ?thesis 
    by linarith 
qed

lemma(in padic_integers) val_pos:
  assumes "x \<in> carrier Zp"
  shows "val_Zp x \<ge> 0"
  unfolding val_Zp_def using assms 
  by (metis (full_types) eint_0 eint_ord_simps(1) eint_ord_simps(3) ord_Zp_def ord_pos)
  
text\<open>For passing between nat and int castings of ord\<close>

lemma(in padic_integers) ord_nat:
  assumes "x \<in> carrier Zp"
  assumes "x \<noteq>\<zero>"
  shows "int (nat (ord_Zp x)) = ord_Zp x"
  using ord_pos by (simp add: assms(1) assms(2)) 

lemma(in padic_integers) zero_below_ord:
  assumes "x \<in> carrier Zp"
  assumes "n \<le> ord_Zp x"
  shows  "x n =  0"
proof-
  have "x n =  \<zero>\<^bsub>residue_ring (p^n)\<^esub>" 
    using ord_Zp_def zero_below_val Zp_def assms(1) assms(2) prime  padic_int_simps(5) 
    by auto    
  then show ?thesis using residue_ring_def 
    by simp 
qed

lemma(in padic_integers) zero_below_val_Zp:
  assumes "x \<in> carrier Zp"
  assumes "n \<le> val_Zp x"
  shows  "x n =  0"
  by (metis assms(1) assms(2) eint_ord_simps(1) ord_Zp_def residue_of_zero(2) val_Zp_def zero_below_ord)

lemma(in padic_integers) below_ord_zero:
  assumes "x \<in> carrier Zp"
  assumes "x (Suc n) \<noteq>  0"
  shows  "n \<ge> ord_Zp x"
proof-
  have 0: "x \<in> padic_set p" 
    using Zp_def assms(1)  Zp_defs(3) 
    by auto     
  have 1: "x (Suc n) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc n))\<^esub>" 
    using residue_ring_def assms(2) by auto  
  have "of_nat n \<ge> (padic_val p x )" 
    using 0 1 below_val_zero prime by auto 
  then show ?thesis using ord_Zp_def by auto 
qed

lemma(in padic_integers) below_val_Zp_zero:
  assumes "x \<in> carrier Zp"
  assumes "x (Suc n) \<noteq>  0"
  shows  "n \<ge> val_Zp x"
  by (metis Zp_def assms(1) assms(2) eint_ord_simps(1) padic_integers.below_ord_zero
      padic_integers.residue_of_zero(2) padic_integers.val_ord_Zp padic_integers_axioms)

lemma(in padic_integers) nonzero_imp_ex_nonzero_res:
  assumes "x \<in> carrier Zp"
  assumes "x \<noteq> \<zero>"
  shows "\<exists>k. x (Suc k) \<noteq> 0"
proof-
  have 0: "x 0 = 0"
    using Zp_def assms(1) padic_int_simps(5) padic_set_zero_res prime by auto
  have "\<exists>k. k > 0 \<and> x k \<noteq> 0" 
    apply(rule ccontr) using 0 Zp_defs unfolding padic_zero_def 
    by (metis assms(2) ext neq0_conv)
  then show ?thesis 
    using not0_implies_Suc by blast
qed  

lemma(in padic_integers) ord_suc_nonzero:
  assumes "x \<in> carrier Zp"
  assumes "x \<noteq>\<zero>"
  assumes "ord_Zp x = n"
  shows "x (Suc n) \<noteq> 0"
proof-
  obtain k where k_def: "x (Suc k) \<noteq> 0"
    using assms(1) nonzero_imp_ex_nonzero_res assms(2) by blast   
  then show ?thesis 
  using assms LeastI  nonzero_imp_ex_nonzero_res unfolding ord_Zp_def padic_val_def
    by (metis (mono_tags, lifting) Zp_defs(2) k_def of_nat_eq_iff padic_zero_def padic_zero_simp(1))
qed

lemma(in padic_integers) above_ord_nonzero:
  assumes "x \<in> carrier Zp"
  assumes "x \<noteq>\<zero>"
  assumes "n > ord_Zp x"
  shows "x n \<noteq> 0"
proof-
  have P0: "n \<ge> (Suc (nat (ord_Zp x)))" 
    by (simp add: Suc_le_eq assms(1) assms(2) assms(3) nat_less_iff ord_pos)
  then have P1: "p_residue (Suc (nat (ord_Zp x))) (x n) = x (Suc (nat (ord_Zp x)))" 
    using assms(1) p_residue_padic_int by blast
  then have P2: "p_residue (Suc (nat (ord_Zp x))) (x n) \<noteq> 0" 
    using Zp_def assms(1) assms(2) ord_nat padic_integers.ord_suc_nonzero
      padic_integers_axioms by auto
  then show ?thesis 
    using P0 P1 assms(1) p_residue_padic_int[of x "(Suc (nat (ord_Zp x)))" n] p_residue_def 
    by (metis ord_Zp_def padic_int_simps(2) padic_integers.zero_rep padic_integers_axioms padic_zero_simp(2))
qed

lemma(in padic_integers) ord_Zp_geq:
  assumes "x \<in> carrier Zp"
  assumes "x n = 0"
  assumes "x \<noteq>\<zero>"
  shows "ord_Zp x \<ge> n"
proof(rule ccontr)
  assume "\<not> int n \<le> ord_Zp x"
  then show False using assms 
    using above_ord_nonzero by auto
qed

lemma(in padic_integers) ord_equals:
  assumes "x \<in> carrier Zp"
  assumes "x (Suc n) \<noteq> 0"
  assumes "x n = 0"
  shows "ord_Zp x = n"
  using assms(1) assms(2) assms(3) below_ord_zero ord_Zp_geq residue_of_zero(2) 
  by fastforce

lemma(in padic_integers) ord_Zp_p:
"ord_Zp \<p> = (1::int)"
proof-
  have "ord_Zp \<p> = int 1"
    apply(rule ord_equals[of \<p>])
    using Zp_int_inc_res[of p] prime_gt_1_int prime by auto
  then show ?thesis 
    by simp
qed    
    
lemma(in padic_integers) ord_Zp_one:
"ord_Zp \<one> = 0"
proof-
  have "ord_Zp ([(1::int)]\<cdot>\<one>) = int 0"
    apply(rule ord_equals)
    using Zp_int_inc_res[of 1] prime_gt_1_int prime by auto
  then show ?thesis 
    by simp
qed    

text\<open>ord is multiplicative on nonzero elements of Zp\<close>

lemma(in padic_integers) ord_Zp_mult:
  assumes "x \<in> nonzero Zp"
  assumes "y \<in> nonzero Zp"
  shows "(ord_Zp (x \<otimes>\<^bsub>Zp\<^esub> y)) = (ord_Zp x) + (ord_Zp y)"
  using val_prod[of p x y] prime assms Zp_defs Zp_def nonzero_memE(2) ord_Zp_def 
        nonzero_closed nonzero_memE(2)
  by auto
  
lemma(in padic_integers) ord_Zp_pow:
  assumes "x \<in> nonzero Zp"
  shows "ord_Zp (x[^](n::nat)) = n*(ord_Zp x)"
proof(induction n)
  case 0
  have "x[^](0::nat) = \<one>" 
    using assms(1) nonzero_def by simp
    then show ?case 
    by (simp add: ord_Zp_one)
next
  case (Suc n)
  fix n 
  assume IH: "ord_Zp (x [^] n) = int n * ord_Zp x "
  have N: "(x [^] n) \<in> nonzero Zp"
  proof-
    have "ord_Zp x \<ge> 0"
      using assms 
      by (simp add: nonzero_closed nonzero_memE(2) ord_pos)
      then have "ord_Zp (x [^] n) \<ge> 0"
      using IH assms by simp
    then have 0: "(x [^] n) \<noteq> \<zero>" 
      using ord_of_nonzero(1) by force      
    have 1: "(x [^] n) \<in> carrier Zp" 
     by (simp add: nonzero_closed assms)   
      then show ?thesis
      using "0" not_nonzero_Zp by blast
  qed
  have "x[^](Suc n) = x \<otimes>(x[^]n)" 
    using nonzero_closed assms  R.nat_pow_Suc2 by blast    
  then have "ord_Zp (x[^](Suc n)) =(ord_Zp x) + ord_Zp (x[^]n)"
    using N Zp_def assms padic_integers.ord_Zp_mult padic_integers_axioms by auto
  then have "ord_Zp (x[^](Suc n)) =(ord_Zp x) +(int n * ord_Zp x)" 
    by (simp add: IH)
  then have "ord_Zp (x[^](Suc n)) =(1*(ord_Zp x)) +(int n) * (ord_Zp x)" 
    by simp
  then have "ord_Zp (x[^](Suc n)) =(1+ (int n)) * ord_Zp x" 
    by (simp add: comm_semiring_class.distrib)
  then show "ord_Zp (x[^](Suc n)) = int (Suc n)*ord_Zp x" 
    by simp
qed

lemma(in padic_integers) val_Zp_pow:
  assumes "x \<in> nonzero Zp"
  shows "val_Zp (x[^](n::nat)) = (n*(ord_Zp x))"
  using Zp_def domain.nat_pow_nonzero[of Zp] domain_axioms nonzero_memE assms ord_Zp_def
    padic_integers.ord_Zp_pow padic_integers_axioms val_Zp_def 
    nonzero_memE(2)
  by fastforce

lemma(in padic_integers) val_Zp_pow':
  assumes "x \<in> nonzero Zp"
  shows "val_Zp (x[^](n::nat)) = n*(val_Zp x)"
  by (metis Zp_def assms not_nonzero_memI padic_integers.val_Zp_pow padic_integers.val_ord_Zp padic_integers_axioms times_eint_simps(1))

lemma(in padic_integers) ord_Zp_p_pow:
"ord_Zp (\<p>[^](n::nat)) = n"
  using ord_Zp_pow ord_Zp_p Zp_def Zp_nat_inc_closed ord_of_nonzero(2) padic_integers_axioms int_inc_closed 
        Zp_int_inc_closed by auto

lemma(in padic_integers) ord_Zp_p_int_pow:
  assumes "n \<ge>0"
  shows "ord_Zp (\<p>[^](n::int)) = n"
  by (metis assms int_nat_eq int_pow_int ord_Zp_def ord_Zp_p_pow)

lemma(in padic_integers) val_Zp_p:
"(val_Zp \<p>) = 1"
  using Zp_def ord_Zp_def padic_val_def val_Zp_def  ord_Zp_p Zp_defs(2) one_eint_def
  by auto
 
lemma(in padic_integers) val_Zp_p_pow:
"val_Zp (\<p>[^](n::nat)) = eint n"
proof-
  have "(\<p>[^](n::nat)) \<noteq> \<zero>" 
    by (metis mult_zero_l n_not_Suc_n of_nat_eq_iff ord_Zp_def ord_Zp_p_pow p_natpow_prod_Suc(1))  
  then show ?thesis
    using ord_Zp_p_pow  by (simp add: ord_Zp_def val_Zp_def)
qed

lemma(in padic_integers) p_pow_res:
  assumes "(n::nat) \<ge> m"
  shows "(\<p>[^]n) m = 0"
  by (simp add: assms ord_Zp_p_pow zero_below_ord)

lemma(in padic_integers) p_pow_factor:
  assumes "(n::nat) \<ge> m"
  shows "(h \<otimes> (\<p>[^]n)) m = 0"  "(h \<otimes> (\<p>[^]n)) m = \<zero>\<^bsub>Zp_res_ring n\<^esub>"
  using assms p_pow_res p_res_ring_zero
  by(auto simp: residue_of_zero Zp_residue_mult_zero(2))

  (**********************************************************************)
  (**********************************************************************)
  subsection\<open>The Ultrametric Inequality\<close>
  (**********************************************************************)
  (**********************************************************************)
text\<open>Ultrametric inequality for ord\<close>

lemma(in padic_integers) ord_Zp_ultrametric:
  assumes "x \<in> nonzero Zp"
  assumes "y \<in> nonzero Zp"
  assumes "x \<oplus> y \<in> nonzero Zp"
  shows "ord_Zp (x \<oplus> y) \<ge> min (ord_Zp x) (ord_Zp y)"
  unfolding ord_Zp_def
  using padic_val_ultrametric[of p x y] Zp_defs assms nonzero_memE Zp_def prime 
        nonzero_closed nonzero_memE(2) by auto
  
text\<open>Variants of the ultrametric inequality\<close>

lemma (in padic_integers) ord_Zp_ultrametric_diff:
  assumes "x \<in> nonzero Zp"
  assumes "y \<in> nonzero Zp"
  assumes "x \<noteq> y "
  shows "ord_Zp (x \<ominus> y) \<ge> min (ord_Zp x) (ord_Zp y)"
  using assms ord_Zp_ultrametric[of x "\<ominus> y"]
  unfolding a_minus_def 
  by (metis (no_types, lifting) R.a_transpose_inv R.add.inv_closed R.add.m_closed R.l_neg nonzero_closed ord_Zp_of_a_inv ord_of_nonzero(2) ord_pos)
  
lemma(in padic_integers) ord_Zp_not_equal_imp_notequal:
  assumes "x \<in> nonzero Zp"
  assumes "y \<in> nonzero Zp"
  assumes "ord_Zp x \<noteq> (ord_Zp y)"
  shows "x \<noteq> y" "x \<ominus> y \<noteq>\<zero>" "x \<oplus> y \<noteq>\<zero>" 
  using assms 
  apply blast 
  using nonzero_closed assms(1) assms(2) assms(3) apply auto[1]
  using nonzero_memE assms 
  using R.minus_equality nonzero_closed 
        Zp_def padic_integers.ord_Zp_of_a_inv 
        padic_integers_axioms by auto

lemma(in padic_integers) ord_Zp_ultrametric_eq:
  assumes "x \<in> nonzero Zp"
  assumes "y \<in> nonzero Zp"
  assumes "ord_Zp x > (ord_Zp y)"
  shows "ord_Zp (x \<oplus> y) = ord_Zp y"
proof-
  have 0: "ord_Zp (x \<oplus> y) \<ge> ord_Zp y"
    using assms ord_Zp_not_equal_imp_notequal[of x y]
        ord_Zp_ultrametric[of x y] nonzero_memE not_nonzero_Zp
        nonzero_closed by force
  have 1: "ord_Zp y \<ge> min (ord_Zp(x \<oplus> y)) (ord_Zp x)"
  proof-
    have 0: "x \<oplus> y \<noteq> x"
      using assms nonzero_memE
      by (simp add: nonzero_closed nonzero_memE(2))
    have 1: "x \<oplus> y \<in> nonzero Zp"
      using ord_Zp_not_equal_imp_notequal[of x y] 
            nonzero_closed assms(1) assms(2) assms(3) 
            not_nonzero_Zp by force         
    then show ?thesis 
      using 0 assms(1) assms(2) assms(3) ord_Zp_ultrametric_diff[of "x \<oplus> y" x] 
      by (simp add: R.minus_eq nonzero_closed R.r_neg1 add_comm)         
  qed
  then show ?thesis 
    using 0 assms(3) 
    by linarith
qed

lemma(in padic_integers) ord_Zp_ultrametric_eq':
  assumes "x \<in> nonzero Zp"
  assumes "y \<in> nonzero Zp"
  assumes "ord_Zp x > (ord_Zp y)"
  shows "ord_Zp (x \<ominus> y) = ord_Zp y"
  using assms ord_Zp_ultrametric_eq[of x "\<ominus> y"]
  unfolding a_minus_def 
  by (metis R.add.inv_closed R.add.inv_eq_1_iff nonzero_closed not_nonzero_Zp ord_Zp_of_a_inv)

lemma(in padic_integers) ord_Zp_ultrametric_eq'':
  assumes "x \<in> nonzero Zp"
  assumes "y \<in> nonzero Zp"
  assumes "ord_Zp x > (ord_Zp y)"
  shows "ord_Zp (y \<ominus> x) = ord_Zp y"
  by (metis R.add.inv_closed R.minus_eq 
      nonzero_closed Zp_def add_comm 
      assms(1) assms(2) assms(3)
      ord_Zp_of_a_inv ord_of_nonzero(2) 
      ord_pos padic_integers.ord_Zp_ultrametric_eq padic_integers_axioms)

lemma(in padic_integers) ord_Zp_not_equal_ord_plus_minus:
  assumes "x \<in> nonzero Zp"
  assumes "y \<in> nonzero Zp"
  assumes "ord_Zp x \<noteq> (ord_Zp y)"
  shows "ord_Zp (x \<ominus> y) = ord_Zp (x \<oplus> y)"
  apply(cases "ord_Zp x > ord_Zp y")
  using assms 
  apply (simp add: ord_Zp_ultrametric_eq ord_Zp_ultrametric_eq')
  using assms nonzero_memI
  by (smt add_comm ord_Zp_ultrametric_eq ord_Zp_ultrametric_eq'')

text\<open>val is multiplicative on nonzero elements\<close>

lemma(in padic_integers) val_Zp_mult0:
  assumes "x \<in> carrier Zp"
  assumes "x \<noteq>\<zero>"
  assumes "y \<in> carrier Zp"
  assumes "y \<noteq>\<zero>"
  shows "(val_Zp (x \<otimes>\<^bsub>Zp\<^esub> y)) = (val_Zp x) + (val_Zp y)"
  apply(cases "x \<otimes>\<^bsub>Zp\<^esub> y = \<zero>")
  using assms(1) assms(2) assms(3) assms(4) integral_iff val_ord_Zp ord_Zp_mult nonzero_memI 
  apply (simp add: integral_iff)
  using assms ord_Zp_mult[of x y] val_ord_Zp 
  by (simp add: nonzero_memI)

text\<open>val is multiplicative everywhere\<close>
lemma(in padic_integers) val_Zp_mult:
  assumes "x \<in> carrier Zp"
  assumes "y \<in> carrier Zp"
  shows "(val_Zp (x \<otimes>\<^bsub>Zp\<^esub> y)) = (val_Zp x) + (val_Zp y)"
  using assms(1) assms(2) integral_iff val_ord_Zp ord_Zp_mult nonzero_memI val_Zp_mult0 val_Zp_def 
  by simp
  
lemma(in padic_integers) val_Zp_ultrametric0:
  assumes "x \<in> carrier Zp"
  assumes "x \<noteq>\<zero>"
  assumes "y \<in> carrier Zp"
  assumes "y \<noteq>\<zero>"
  assumes "x \<oplus> y \<noteq> \<zero>"
  shows "min (val_Zp x) (val_Zp y) \<le> val_Zp (x \<oplus> y) "
  apply(cases "x \<oplus> y = \<zero>")
  using assms apply blast
    using assms ord_Zp_ultrametric[of x y] nonzero_memI val_ord_Zp[of x] val_ord_Zp[of y] val_ord_Zp[of "x \<oplus> y"] 
    by simp

text\<open>Unconstrained ultrametric inequality\<close>

lemma(in padic_integers) val_Zp_ultrametric:
  assumes "x \<in> carrier Zp"
  assumes "y \<in> carrier Zp" 
  shows " min (val_Zp x) (val_Zp y) \<le> val_Zp (x \<oplus> y)"
  apply(cases "x = \<zero>")
  apply (simp add: assms(2))
  apply(cases "y = \<zero>")
    apply (simp add: assms(1))
    apply(cases "x \<oplus> y = \<zero>")
      apply (simp add: val_Zp_def)
        using assms val_Zp_ultrametric0[of x y]   
        by simp 
  
text\<open>Variants of the ultrametric inequality\<close>

lemma (in padic_integers) val_Zp_ultrametric_diff:
  assumes "x \<in> carrier Zp"
  assumes "y \<in> carrier Zp" 
  shows "val_Zp (x \<ominus> y) \<ge> min (val_Zp x) (val_Zp y)"
  using assms val_Zp_ultrametric[of x "\<ominus>y"] unfolding a_minus_def
  by (metis R.add.inv_closed R.add.inv_eq_1_iff nonzero_memI ord_Zp_def ord_Zp_of_a_inv val_Zp_def)

lemma(in padic_integers) val_Zp_not_equal_imp_notequal:
  assumes "x \<in> carrier Zp"
  assumes "y \<in> carrier Zp"
  assumes "val_Zp x \<noteq> val_Zp y"
  shows "x \<noteq> y" "x \<ominus> y \<noteq>\<zero>" "x \<oplus> y \<noteq>\<zero>" 
  using assms(3) apply auto[1]
    using assms(1) assms(2) assms(3) R.r_right_minus_eq apply blast
      by (metis  R.add.inv_eq_1_iff assms(1) assms(2) assms(3) R.minus_zero R.minus_equality
          not_nonzero_Zp ord_Zp_def ord_Zp_of_a_inv val_ord_Zp)

lemma(in padic_integers) val_Zp_ultrametric_eq:
  assumes "x \<in> carrier Zp"
  assumes "y \<in> carrier Zp"
  assumes "val_Zp x > val_Zp y"
  shows "val_Zp (x \<oplus> y) = val_Zp y"
  apply(cases "x \<noteq> \<zero> \<and> y \<noteq> \<zero> \<and> x \<noteq> y")   
  using assms ord_Zp_ultrametric_eq[of x y] val_ord_Zp nonzero_memE
    using not_nonzero_memE val_Zp_not_equal_imp_notequal(3) apply force
    unfolding val_Zp_def 
      using assms(2) assms(3) val_Zp_def by force    
  
lemma(in padic_integers) val_Zp_ultrametric_eq':
  assumes "x \<in> carrier Zp"
  assumes "y \<in> carrier Zp"
  assumes "val_Zp x > (val_Zp y)"
  shows "val_Zp (x \<ominus> y) = val_Zp y"
  using assms val_Zp_ultrametric_eq[of x "\<ominus> y"]
  unfolding a_minus_def 
  by (metis R.add.inv_closed R.r_neg val_Zp_not_equal_imp_notequal(3))  

lemma(in padic_integers) val_Zp_ultrametric_eq'':
  assumes "x \<in> carrier Zp"
  assumes "y \<in> carrier Zp"
  assumes "val_Zp x > (val_Zp y)"
  shows "val_Zp (y \<ominus> x) = val_Zp y"
proof- 
  have 0: "y \<ominus> x = \<ominus> (x \<ominus> y)"
    using assms(1,2) unfolding a_minus_def
    by (simp add: R.add.m_comm R.minus_add)
  have 1: "val_Zp (x \<ominus> y) = val_Zp y"
    using assms val_Zp_ultrametric_eq' by blast 
  have 2: "val_Zp (x \<ominus> y) = val_Zp (y \<ominus> x)"
    unfolding 0 unfolding a_minus_def
    by(rule val_Zp_of_a_inv, rule R.ring_simprules, rule assms, rule R.ring_simprules, rule assms)
  show ?thesis using 1 unfolding 2 by blast 
qed

lemma(in padic_integers) val_Zp_not_equal_ord_plus_minus:
  assumes "x \<in> carrier Zp"
  assumes "y \<in> carrier Zp"
  assumes "val_Zp x \<noteq> (val_Zp y)"
  shows "val_Zp (x \<ominus> y) = val_Zp (x \<oplus> y)"
  by (metis R.add.inv_closed R.minus_eq R.r_neg R.r_zero add_comm assms(1) assms(2) assms(3) not_nonzero_Zp ord_Zp_def ord_Zp_not_equal_ord_plus_minus val_Zp_def val_Zp_not_equal_imp_notequal(3))

  (**********************************************************************)
  (**********************************************************************)
  subsection\<open>Units of $\mathbb{Z}_p$\<close>
  (**********************************************************************)
  (**********************************************************************)
text\<open>Elements with valuation 0 in Zp are the units\<close>

lemma(in padic_integers) val_Zp_0_criterion:
  assumes "x \<in> carrier Zp"
  assumes "x 1 \<noteq> 0"
  shows "val_Zp x = 0"
  unfolding val_Zp_def
  using Zp_def assms(1) assms(2) ord_equals padic_set_zero_res prime 
  by (metis One_nat_def Zp_defs(3) of_nat_0 ord_Zp_def residue_of_zero(2) zero_eint_def)

text\<open>Units in Zp have val 0\<close>

lemma(in padic_integers) unit_imp_val_Zp0:
  assumes "x \<in> Units Zp"
  shows "val_Zp x = 0"
  apply(rule val_Zp_0_criterion)
  apply (simp add: R.Units_closed assms)
  using assms residue_of_prod[of x "inv x" 1] residue_of_one(2)[of 1] R.Units_r_inv[of x]
        comm_monoid.UnitsI[of "R 1"]  p_res_ring_1_field
  by (metis le_eq_less_or_eq residue_of_prod residue_times_zero_r zero_le_one zero_neq_one)
  
text\<open>Elements in Zp with ord 0 are units\<close>

lemma(in padic_integers) val_Zp0_imp_unit0:
  assumes "val_Zp x = 0"
  assumes "x \<in> carrier Zp"
  fixes n::nat
  shows "(x (Suc n)) \<in> Units (Zp_res_ring (Suc n))"
  unfolding val_Zp_def
proof-
  have p_res_ring: "residues (p^(Suc n))" 
    using p_residues by blast    
  have "\<And> n. coprime (x (Suc n)) p"
  proof-
    fix n
    show "coprime (x (Suc n)) p"
    proof-
      have "\<not> \<not> coprime (x (Suc n)) p"
      proof
        assume "\<not> coprime (x (Suc n)) p" 
        then have "p dvd (x (Suc n))" using prime 
          by (meson coprime_commute prime_imp_coprime prime_nat_int_transfer) 
        then obtain k where "(x (Suc n)) = k*p"  
          by fastforce 
        then have S:"x (Suc n) mod p = 0" 
          by simp 
        have "x 1 = 0"
        proof-
          have "Suc n \<ge> 1" 
            by simp 
          then have "x 1 = p_residue 1 (x (Suc n))"
            using p_residue_padic_int assms(2) by presburger 
          then show ?thesis using S 
            by (simp add: p_residue_alt_def)            
        qed
        have "x \<noteq>\<zero>" 
        proof-
          have "ord_Zp x \<noteq> ord_Zp \<zero>" 
            using Zp_def ord_Zp_def padic_val_def assms(1)  ord_of_nonzero(1) R.zero_closed
                 Zp_defs(2) val_Zp_def 
            by auto                                
          then show ?thesis 
            by blast 
        qed
        then have "x 1 \<noteq> 0" 
          using assms(1) assms(2)  ord_suc_nonzero 
          unfolding val_Zp_def  
          by (simp add: ord_Zp_def zero_eint_def)                   
        then show False 
          using \<open>x 1 = 0\<close> by blast 
      qed
      then show ?thesis 
        by auto 
    qed
  qed
  then have "\<And> n. coprime (x (Suc n)) (p^(Suc n))"
    by simp 
  then have "coprime (x (Suc n)) (p^(Suc n))"
    by blast 
  then show ?thesis using assms residues.res_units_eq  p_res_ring  
    by (metis (no_types, lifting) mod_pos_pos_trivial p_residue_ring_car_memE(1)
        p_residue_ring_car_memE(2) residues.m_gt_one residues.mod_in_res_units residues_closed)
qed

lemma(in padic_integers) val_Zp0_imp_unit0':
  assumes "val_Zp x = 0"
  assumes "x \<in> carrier Zp"
  assumes "(n::nat) > 0"
  shows "(x n) \<in> Units (Zp_res_ring n)"
  using assms val_Zp0_imp_unit0 gr0_implies_Suc by blast

lemma(in cring) ring_hom_Units_inv:
  assumes "a \<in> Units R"
  assumes "cring S"
  assumes "h \<in> ring_hom R S"
  shows "h (inv a) = inv\<^bsub>S\<^esub> h a" "h a \<in> Units S"
proof-
  have 0:"h (inv a) \<otimes>\<^bsub>S\<^esub> h a = \<one>\<^bsub>S\<^esub>"
    using assms Units_closed Units_inv_closed         
    by (metis (no_types, lifting) Units_l_inv ring_hom_mult ring_hom_one)
  then show 1: "h (inv a) = inv\<^bsub>S\<^esub> h a"
    by (metis Units_closed Units_inv_closed assms(1) assms(2) assms(3) comm_monoid.is_invI(1) cring_def ring_hom_closed)
  show "h a \<in> Units S"
    apply(rule comm_monoid.UnitsI[of S "inv\<^bsub>S\<^esub> h a"]) using 0 1 assms 
    using cring.axioms(2) apply blast
      apply (metis "1" Units_inv_closed assms(1) assms(3) ring_hom_closed)
        apply (meson Units_closed assms(1) assms(3) ring_hom_closed)
    using "0" "1" by auto
qed   

lemma(in padic_integers) val_Zp_0_imp_unit:
  assumes "val_Zp x = 0"
  assumes "x \<in> carrier Zp"
  shows "x \<in> Units Zp"
proof-
  obtain y where y_def: " y= (\<lambda>n. (if n=0 then 0 else (m_inv (Zp_res_ring n) (x n))))"
    by blast 
  have 0:  "\<And>m. m > 0 \<Longrightarrow> y m = inv \<^bsub>Zp_res_ring m\<^esub> (x m)"
    using y_def by auto 
  have 1:  "\<And>m. m > 0 \<Longrightarrow> inv\<^bsub>Zp_res_ring m\<^esub> (x m) \<in> carrier (Zp_res_ring m)"
  proof- fix m::nat  assume A: "m > 0" then show "inv\<^bsub>Zp_res_ring m\<^esub> (x m) \<in> carrier (Zp_res_ring m)"
    using assms val_Zp0_imp_unit0' monoid.Units_inv_closed[of "Zp_res_ring m" "x m"] 
    by (smt One_nat_def Zp_def Zp_defs(2) cring.axioms(1) of_nat_0 ord_Zp_def 
        padic_integers.R_cring padic_integers.ord_suc_nonzero padic_integers.val_Zp_0_criterion padic_integers_axioms padic_val_def ring_def)    
  qed
  have 2: "y \<in> padic_set p"
  proof(rule padic_set_memI)
    show 20: "\<And>m. y m \<in> carrier (residue_ring (p ^ m))"
    proof- fix m show "y m \<in> carrier (residue_ring (p ^ m))"
      apply(cases "m = 0")
      using y_def 0[of m] 1[of m]  
      by(auto simp: residue_ring_def y_def)
    qed
    show "\<And>m n. m < n \<Longrightarrow> residue (p ^ m) (y n) = y m"
    proof- fix m n::nat assume A: "m < n"
      show "residue (p ^ m) (y n) = y m"
      proof(cases "m = 0")
        case True
        then show ?thesis 
          by (simp add: residue_1_zero y_def)        
      next
        case False
        have hom: "residue (p ^ m) \<in> ring_hom (Zp_res_ring n) (Zp_res_ring m)"
          using A False prime residue_hom_p by auto
        have inv: "y n = inv\<^bsub>Zp_res_ring n\<^esub> x n" using A
          by (simp add: False y_def)
        have unit: "x n \<in> Units (Zp_res_ring n)"
          using A False Zp_def assms(1) assms(2) val_Zp0_imp_unit0' prime 
          by (metis gr0I gr_implies_not0)         
        have F0: "residue (p ^ m) (x n) = x m"
          using A Zp_defs(3) assms(2) padic_set_res_coherent prime by auto
        have F1: "residue (p ^ m) (y n) = inv\<^bsub>Zp_res_ring m\<^esub> x m"
          using F0 R_cring A  hom inv unit cring.ring_hom_Units_inv[of "Zp_res_ring n" "x n" "Zp_res_ring m" "residue (p ^ m)"] 
               False 
          by auto
        then show ?thesis 
          by (simp add: False y_def)
      qed
    qed
  qed
  have 3: "y \<otimes> x = \<one>"
  proof
    fix m
    show "(y \<otimes> x) m = \<one> m"
    proof(cases "m=0")
      case True
      then have L: "(y \<otimes> x) m  = 0"  
        using  Zp_def "1" assms(2) Zp_residue_mult_zero(1) y_def 
        by auto        
      have R: "\<one> m = 0" 
        by (simp add: True cring.cring_simprules(6) domain.axioms(1) ord_Zp_one zero_below_ord) 
      then show ?thesis using L R by auto 
      next
        case False        
        have P: "(y \<otimes> x) m = (y m) \<otimes>\<^bsub>residue_ring (p^m)\<^esub> (x m)"
          using Zp_def residue_of_prod by auto   
        have "(y m) \<otimes>\<^bsub>residue_ring (p^m)\<^esub> (x m) = 1"
        proof-
          have "p^m > 1"   
            using False prime prime_gt_1_int by auto  
          then have "residues (p^m)"  
            using less_imp_of_nat_less residues.intro by fastforce 
          have "cring (residue_ring (p^m))" 
            using  residues.cring \<open>residues (p ^ m)\<close> 
            by blast  
          then have M: "monoid (residue_ring (p^m))" 
            using cring_def ring_def by blast 
          have U: "(x m) \<in> Units (residue_ring (p^m))" 
            using False Zp_def assms(1) assms(2) padic_integers.val_Zp0_imp_unit0' padic_integers_axioms by auto                               
          have I: "y m = m_inv (residue_ring (p^m)) (x m)" 
            by (simp add: False y_def)            
          have "(y m) \<otimes>\<^bsub>residue_ring (p^m)\<^esub> (x m) = \<one>\<^bsub>residue_ring (p^m)\<^esub>"
            using M U I by (simp add: monoid.Units_l_inv) 
          then show ?thesis
            using residue_ring_def by simp 
        qed
        then show ?thesis 
          using P Zp_def False residue_of_one(2) by auto          
    qed
  qed
  have 4: "y \<in> carrier Zp"
    using 2 Zp_defs by auto   
  show ?thesis 
    apply(rule R.UnitsI[of y])
    using assms 4 3 by auto 
qed

text\<open>Definition of ord on a fraction is independent of the choice of representatives\<close>

lemma(in padic_integers) ord_Zp_eq_frac:
  assumes "a \<in> nonzero Zp"
  assumes "b \<in> nonzero Zp"
  assumes "c \<in> nonzero Zp"
  assumes "d \<in> nonzero Zp"
  assumes "a \<otimes> d = b \<otimes> c"
  shows "(ord_Zp a) - (ord_Zp b) = (ord_Zp c) - (ord_Zp d)"
proof-
  have "ord_Zp (a \<otimes> d) = ord_Zp (b \<otimes> c)"
    using assms 
    by presburger
  then have "(ord_Zp a) + (ord_Zp  d) = (ord_Zp b) + (ord_Zp c)"
    using assms(1) assms(2) assms(3) assms(4) ord_Zp_mult by metis  
  then show ?thesis 
    by linarith 
qed

lemma(in padic_integers) val_Zp_eq_frac_0:
  assumes "a \<in> nonzero Zp"
  assumes "b \<in> nonzero Zp"
  assumes "c \<in> nonzero Zp"
  assumes "d \<in> nonzero Zp"
  assumes "a \<otimes> d = b \<otimes> c"
  shows "(val_Zp a) - (val_Zp b) = (val_Zp c) - (val_Zp d)"
proof- 
  have 0:"(val_Zp a) - (val_Zp b) = (ord_Zp a) - (ord_Zp b)" 
    using assms nonzero_memE Zp_defs(2) ord_Zp_def val_Zp_def by auto  
  have 1: "(val_Zp c) - (val_Zp d) = (ord_Zp c) - (ord_Zp d)" 
    using assms nonzero_memE   val_ord_Zp[of c] val_ord_Zp[of d]
    by (simp add: nonzero_memE(2))    
  then show ?thesis
    using "0" assms(1) assms(2) assms(3) assms(4) assms(5) ord_Zp_eq_frac 
    by presburger
qed

(*************************************************************************************************)
(*************************************************************************************************)
(*****************)  section\<open>Angular Component Maps on $\mathbb{Z}_p$\<close> (*********************)
(*************************************************************************************************)
(*************************************************************************************************)
text\<open>The angular component map on $\mathbb{Z}_p$ is just the map which normalizes a point $x \in \mathbb{Z}_p$ by mapping it to a point with valuation $0$. It is explicitly defined as the mapping $x \mapsto p^{-ord (p)}*x$ for nonzero $x$, and $0 \mapsto 0$. By composing these maps with reductions mod $p^n$ we get maps which are equal to the standard residue maps on units of $\mathbb{Z}_p$, but in general unequal elsewhere. Both the angular component map and the angular component map mod $p^n$ are homomorpshims from the multiplicative group of units of $\mathbb{Z}_p$ to the multiplicative group of units of the residue rings, and play a key role in first-order model-theoretic formalizations of the $p$-adics (see, for example \cite{10.2307/2274477}, or \cite{Denef1986}).  \<close>


lemma(in cring) int_nat_pow_rep:
"[(k::int)]\<cdot>\<one> [^] (n::nat) = [(k^n)]\<cdot>\<one>"
  apply(induction n)
  by (auto simp: add.int_pow_pow add_pow_rdistr_int mult.commute)
 
lemma(in padic_integers) p_pow_rep0:
  fixes n::nat
  shows "\<p>[^]n = [(p^n)]\<cdot>\<one>"
  using R.int_nat_pow_rep by auto 

lemma(in padic_integers) p_pow_nonzero:
  shows "(\<p>[^](n::nat)) \<in> carrier Zp"
        "(\<p>[^](n::nat)) \<noteq> \<zero>"
  apply simp 
  using Zp_def nat_pow_nonzero domain_axioms nonzero_memE int_inc_closed ord_Zp_p 
        padic_integers.ord_of_nonzero(2) padic_integers_axioms Zp_int_inc_closed 
        nonzero_memE(2) 
  by (metis ord_of_nonzero(2) zero_le_one)

lemma(in padic_integers) p_pow_nonzero':
  shows "(\<p>[^](n::nat)) \<in> nonzero Zp"
  using nonzero_def p_pow_nonzero 
  by (simp add: nonzero_def)

lemma(in padic_integers) p_pow_rep:
  fixes n::nat
  shows "(\<p>[^]n) k = (p^n) mod (p^k)"
  by (simp add: R.int_nat_pow_rep Zp_int_inc_res)
  
lemma(in padic_integers) p_pow_car:
  assumes " (n::int)\<ge> 0"
  shows "(\<p>[^]n) \<in> carrier Zp"
proof-
  have "(\<p>[^]n) = (\<p>[^](nat n))" 
    by (metis assms int_nat_eq int_pow_int) 
  then show ?thesis  
    by simp 
qed

lemma(in padic_integers) p_int_pow_nonzero:
  assumes "(n::int) \<ge>0"
  shows "(\<p>[^]n) \<in> nonzero Zp"
  by (metis assms not_nonzero_Zp ord_Zp_p_int_pow ord_of_nonzero(1) p_pow_car)
 
lemma(in padic_integers) p_nonzero:
  shows "\<p> \<in> nonzero Zp"
  using p_int_pow_nonzero[of 1]
  by (simp add: ord_Zp_p ord_of_nonzero(2))
  
text\<open>Every element of Zp is a unit times a power of p.\<close>

lemma(in padic_integers) residue_factor_unique:
  assumes "k>0"
  assumes "x \<in> carrier Zp"
  assumes "u \<in> carrier (Zp_res_ring k) \<and> (u* p^m) = (x (m+k))"
  shows "u = (THE u. u \<in> carrier (Zp_res_ring k) \<and> (u* p^m) = (x (m+k)))"
proof-
  obtain P where 
    P_def: "P = (\<lambda> u.  u \<in> carrier (Zp_res_ring k) \<and> (u* p^m) = (x (m+k)))"
    by simp
  have 0: "P u" 
    using P_def assms(3) by blast
  have 1: "\<And> v. P v \<Longrightarrow> v = u" 
    by (metis P_def assms(3) mult_cancel_right
        not_prime_0 power_not_zero prime)
  have "u =  (THE u. P u)" 
    by (metis 0 1 the_equality)
  then show ?thesis using P_def 
    by blast
qed

lemma(in padic_integers) residue_factor_exists:
  assumes "m = nat (ord_Zp x)"
  assumes "k > 0"
  assumes "x \<in> carrier Zp"
  assumes "x \<noteq>\<zero>"
  obtains u where "u \<in> carrier (Zp_res_ring k) \<and> (u* p^m) = (x (m+k))"
proof-
  have X0: "(x (m+k)) \<in> carrier (Zp_res_ring (m+k)) " 
    using Zp_def assms(3) padic_set_res_closed residues_closed 
    by blast    
  then have X1: "(x (m+k)) \<ge> 0" 
    using p_residues  assms(2) residues.res_carrier_eq  by simp
  then have X2: "(x (m+k)) > 0"  
    using assms(1) assms(2) assms(3) assms(4) above_ord_nonzero 
    by (metis add.right_neutral add_cancel_right_right 
        add_gr_0 int_nat_eq less_add_same_cancel1 
        less_imp_of_nat_less not_gr_zero of_nat_0_less_iff of_nat_add ord_pos)
  have 0: "x m = 0" 
    using  Zp_def assms(1) assms(3) zero_below_val  ord_nat zero_below_ord[of x m] 
           assms(4) ord_Zp_def by auto
  then have 1: "x (m +k) mod p^m = 0" 
    using assms(2) assms(3) p_residue_padic_int residue_def 
    by (simp add: p_residue_alt_def)
  then have "\<exists> u.  u*(p^m) = (x (m+k))" 
    by auto
 then obtain u where U0: " u*(p^m) = (x (m+k))" 
   by blast
  have I: "(p^m) > 0  " 
    using prime 
    by (simp add: prime_gt_0_int)
  then have U1: "(u* p^m) = (x (m+k))" 
    by (simp add: U0)
  have U2: "u \<ge> 0" 
    using I U1 X1 
    by (metis U0 less_imp_triv mult.right_neutral mult_less_cancel_left
        of_nat_zero_less_power_iff power.simps(1) times_int_code(1))
  have X3: "(x (m+k)) < p^(m+k)" 
    using assms(3) X0  p_residues assms(2) residues.res_carrier_eq by auto
  have U3: "u < p^k" 
  proof(rule ccontr)
    assume "\<not> u < (p ^ k)"
    then have "(p^k) \<le> u" 
      by simp
    then have " (p^k * p^m) \<le> u*(p^m)" 
      using I by simp
    then have "p^(m + k) \<le> (x (m+k))" 
      by (simp add: U0 add.commute semiring_normalization_rules(26))
    then show False 
      using X3 by linarith
  qed
  then have "u \<in> carrier (Zp_res_ring k)" 
    using assms(2)  p_residues residues.res_carrier_eq U3 U2 by auto
  then show ?thesis using U1  that by blast
qed

definition(in padic_integers) normalizer where 
"normalizer m x = (\<lambda>k. if (k=0) then 0 else (THE u. u \<in> carrier (Zp_res_ring k) \<and> (u* p^m) = (x (m + k)) ) )"

definition(in padic_integers) ac_Zp where 
"ac_Zp x = normalizer (nat (ord_Zp x)) x"

lemma(in padic_integers) ac_Zp_equation:
  assumes "x \<in> carrier Zp"
  assumes "x \<noteq>\<zero>"
  assumes "k > 0"
  assumes "m = nat (ord_Zp x)"
  shows "(ac_Zp x k) \<in> carrier (Zp_res_ring k) \<and> (ac_Zp x k)*(p^m) = (x (m+k))" 
proof-
  have K0: "k >0" 
    using assms nat_neq_iff by blast
  have KM: "m+ k > m" 
    using assms(3) assms(4) by linarith
  obtain u where U0: "u \<in> carrier (Zp_res_ring k) \<and> (u* p^m) = (x (m+k))"
    using assms(1) assms(2) assms(3) assms(4) residue_factor_exists by blast
  have RHS: "ac_Zp x k = (THE u. u \<in> carrier (Zp_res_ring k) \<and> u*(p^m) = (x (m+k)))" 
  proof-
    have K: "k \<noteq>0" 
      by (simp add: K0)
    have "ac_Zp x k = normalizer (nat (ord_Zp x)) x k" 
      using ac_Zp_def by presburger
    then have "ac_Zp x k = normalizer m x k" 
      using assms by blast
    then show "ac_Zp x k = (THE u. u \<in> carrier (Zp_res_ring k) \<and> (u* p^m) = (x (m + k)) ) "
     using K unfolding normalizer_def p_residue_def  
     by simp   
  qed
  have LHS:"u = (THE u. u \<in> carrier (Zp_res_ring k) \<and> u*(p^m) = (x (m+k)))" 
    using assms U0 K0 assms(1) residue_factor_unique[of k x u m] by metis    
  then have "u = ac_Zp x k" 
    by (simp add: RHS)
  then show ?thesis using U0 by auto  
qed

lemma(in padic_integers) ac_Zp_res:
  assumes "m >k"
  assumes "x \<in> carrier Zp"
  assumes "x \<noteq>\<zero>"
  shows "p_residue k (ac_Zp x m) = (ac_Zp x k)"
proof(cases "k =0")
  case True
  then show ?thesis 
    unfolding ac_Zp_def normalizer_def 
    by (meson p_res_ring_0' p_residue_range')
next
  case False
  obtain n where n_def: "n = nat (ord_Zp x)"
    by blast 
  have K0: "k >0" using False by simp
  obtain uk where Uk0: "uk = (ac_Zp x k)" 
    by simp
  obtain um where Um0: "um = (ac_Zp x m)" 
    by simp
  have Uk1: "uk \<in> carrier (Zp_res_ring k) \<and> uk*(p^n) = (x (n+k))" 
    using K0 Uk0 ac_Zp_equation assms(2) assms(3) n_def by metis 
  have Um1: "um \<in> carrier (Zp_res_ring m) \<and> um*(p^n) = (x (n+m))" 
    using Uk1 Um0 ac_Zp_equation assms(1) assms(3) n_def assms(2) 
    by (metis neq0_conv not_less0) 
  have "um mod (p^k) = uk"
  proof-
    have "(x (n+m)) mod (p^(n + k)) = (x (n+k))"
      using assms(1) assms(3) p_residue_padic_int p_residue_def n_def
      by (simp add: assms(2) p_residue_alt_def)
    then have "(p^(n + k)) dvd (x (n+m)) - (x (n+k))" 
      by (metis dvd_minus_mod)
    then obtain d where "(x (n+m)) - (x (n+k)) = (p^(n+k))*d" 
      using dvd_def by blast
    then have "((um*(p^n)) - (uk*(p^n))) =  p^(n+k)*d" 
      using Uk1 Um1 by auto
    then have "((um - uk)*(p^n)) =  p^(n+k)*d"
      by (simp add: left_diff_distrib)
    then have "((um - uk)*(p^n)) =  ((p^k)*d)*(p^n)" 
      by (simp add: power_add)
    then have "(um - uk) =  ((p^k)*d)" 
      using prime by auto
    then have "um mod p^k = uk mod p^k" 
      by (simp add: mod_eq_dvd_iff)
    then show ?thesis  using Uk1  
      by (metis mod_pos_pos_trivial p_residue_ring_car_memE(1) p_residue_ring_car_memE(2))      
  qed
  then show ?thesis 
    by (simp add: Uk0 Um0 p_residue_alt_def)
qed

lemma(in padic_integers) ac_Zp_in_Zp:
  assumes "x \<in> carrier Zp"
  assumes "x \<noteq>\<zero>"
  shows "ac_Zp x \<in> carrier Zp"
proof-
  have "ac_Zp x \<in> padic_set p"
  proof(rule padic_set_memI)
    show "\<And>m. ac_Zp x m \<in> carrier (residue_ring (p ^ m))"
    proof- 
      fix m
      show "ac_Zp x m \<in> carrier (residue_ring (p ^ m))"
      proof(cases "m = 0")
        case True
        then have "ac_Zp x m = 0" 
          unfolding ac_Zp_def normalizer_def by auto           
        then show ?thesis 
          by (simp add: True residue_ring_def)
      next
        case False
        then have "m>0" 
          by blast
        then show ?thesis 
          using ac_Zp_equation 
          by (metis assms(1) assms(2))
      qed
    qed
    show "\<And>m n. m < n \<Longrightarrow> residue (p ^ m) (ac_Zp x n) = ac_Zp x m"
      using ac_Zp_res 
      by (simp add: assms(1) assms(2) p_residue_def)
  qed
  then show ?thesis 
    by (simp add: Zp_defs(3))    
qed

lemma(in padic_integers) ac_Zp_is_Unit:
  assumes "x \<in> carrier Zp"
  assumes "x \<noteq>\<zero>"
  shows "ac_Zp x \<in> Units Zp"
proof(rule val_Zp_0_imp_unit)
  show "ac_Zp x \<in> carrier Zp" 
    by (simp add: ac_Zp_in_Zp assms(1) assms(2))   
  obtain m where M: "m = nat (ord_Zp x)"
    by blast
  have AC1: "(ac_Zp x 1)*(p^m) = (x (m+1))"
    using M ac_Zp_equation assms(1) assms(2) 
    by (metis One_nat_def lessI)
  have "(x (m+1)) \<noteq>0" 
    using M assms 
    by (metis Suc_eq_plus1 Suc_le_eq nat_int nat_mono nat_neq_iff ord_Zp_geq)
  then have "(ac_Zp x 1) \<noteq> 0" 
    using AC1 by auto
  then show "val_Zp (ac_Zp x) = 0"
    using \<open>ac_Zp x \<in> carrier Zp\<close> val_Zp_0_criterion 
    by blast 
qed

text\<open>The typical defining equation for the angular component map.\<close>

lemma(in padic_integers) ac_Zp_factors_x:
  assumes "x \<in> carrier Zp"
  assumes "x \<noteq>\<zero>"
  shows "x = (\<p>[^](nat (ord_Zp x))) \<otimes> (ac_Zp x)" "x = (\<p>[^](ord_Zp x)) \<otimes> (ac_Zp x)"
proof-
  show "x = (\<p>[^](nat (ord_Zp x)))\<otimes> (ac_Zp x)"
  proof
    fix k
    show "x k = ((\<p>[^](nat (ord_Zp x))) \<otimes> (ac_Zp x)) k"
    proof(cases "k=0")
      case True
      then show ?thesis 
        using Zp_def Zp_defs(3) Zp_residue_mult_zero(1) ac_Zp_in_Zp
          assms(1) assms(2) mult_comm padic_set_zero_res prime by auto                 
    next
      case False
      show ?thesis
      proof(cases "k \<le> ord_Zp x")
      case True
      have 0: "x k = 0" 
        using True assms(1) zero_below_ord by blast
      have 1: "(\<p>[^](nat (ord_Zp x))) k = 0" 
        using True assms(1) assms(2) ord_Zp_p_pow ord_nat p_pow_nonzero(1) zero_below_ord 
        by presburger        
      have "((\<p>[^](nat (ord_Zp x))) \<otimes> (ac_Zp x)) k = (\<p>[^](nat (ord_Zp x))) k * (ac_Zp x) k mod p^k" 
        using Zp_def padic_mult_res residue_ring_def 
        using residue_of_prod' by blast
      then have "((\<p>[^](nat (ord_Zp x))) \<otimes> (ac_Zp x)) k = 0" 
        by (simp add: "1")       
      then show ?thesis using 0 
        by metis 
      next
      case False
      obtain n where N: "n = nat (ord_Zp x)" 
        by metis 
      obtain m where M0: "k = n + m" 
        using False N le_Suc_ex ord_Zp_def by fastforce
      have M1: "m >0" 
        using M0 False N assms(1) assms(2) ord_nat 
        by (metis Nat.add_0_right gr0I le_refl less_eq_int_code(1) 
            nat_eq_iff2 neq0_conv of_nat_eq_0_iff of_nat_mono)
      have E1: "(ac_Zp x m)*(p^n) = (x k)" 
        using M0 M1 N ac_Zp_equation assms(1) assms(2) by blast
      have E2: "(ac_Zp x k)*(p^n) = (x (n + k))" 
        using M0 M1 N ac_Zp_equation assms(1) assms(2) add_gr_0 
        by presburger
      have E3: "((ac_Zp x k) mod (p^k))*((p^n) mod p^k) mod (p^k) = (x (n + k)) mod (p^k)"
        by (metis E2 mod_mult_left_eq mod_mult_right_eq)
      have E4: "((ac_Zp x k) mod (p^k))*(p^n) mod (p^k) = (x k)" 
        using E2 assms(1) le_add2 mod_mult_left_eq p_residue_padic_int p_residue_def 
        by (metis Zp_int_inc_rep Zp_int_inc_res)
        
      have E5: "(ac_Zp x k)*((p^n) mod p^k) mod (p^k) = (x k)" 
        using E2 assms(1) p_residue_padic_int p_residue_def by (metis E3 E4 mod_mult_left_eq)
      have E6: "(ac_Zp x k) \<otimes>\<^bsub>(Zp_res_ring k)\<^esub> ((p^n) mod p^k)  = (x k)" 
        using E5 M0 M1 p_residues  residues.res_mult_eq by auto
      have E7: " ((p^n) mod p^k) \<otimes>\<^bsub>(Zp_res_ring k)\<^esub>(ac_Zp x k)   = (x k)" 
        by (simp add: E6 residue_mult_comm)
      have E8: "((\<p>[^](nat (ord_Zp x))) k) \<otimes>\<^bsub>(Zp_res_ring k)\<^esub> (ac_Zp x k) = (x k)" 
        using E7 N p_pow_rep 
        by metis 
      then show ?thesis 
        by (simp add: residue_of_prod)
      qed
    qed
  qed
  then show "x = (\<p>[^](ord_Zp x)) \<otimes> (ac_Zp x)"
    by (metis assms(1) assms(2) int_pow_int ord_nat)
qed

lemma(in padic_integers) ac_Zp_factors':
  assumes "x \<in> nonzero Zp"
  shows "x = [p] \<cdot> \<one> [^] ord_Zp x \<otimes> ac_Zp x"
  using assms nonzero_memE 
  by (simp add: nonzero_closed nonzero_memE(2) ac_Zp_factors_x(2)) 

lemma(in padic_integers) ac_Zp_mult:
  assumes "x \<in> nonzero Zp"
  assumes "y \<in> nonzero Zp"
  shows "ac_Zp (x \<otimes> y) = (ac_Zp x) \<otimes> (ac_Zp y)"
proof-
  have P0: "x = (\<p>[^](nat (ord_Zp x))) \<otimes> (ac_Zp x)"
    using  nonzero_memE ac_Zp_factors_x assms(1) 
    by (simp add: nonzero_closed nonzero_memE(2))   
  have P1: "y = (\<p>[^](nat (ord_Zp y))) \<otimes> (ac_Zp y)"
    using  nonzero_memE ac_Zp_factors_x assms(2) 
    by (simp add: nonzero_closed nonzero_memE(2))

  have "x \<otimes> y = (\<p>[^](nat (ord_Zp (x \<otimes> y)))) \<otimes> (ac_Zp (x \<otimes> y))"
  proof-
    have "x \<otimes> y \<in> nonzero Zp"
      by (simp add:  assms(1) assms(2) nonzero_mult_closed)
        then show ?thesis 
      using nonzero_closed nonzero_memE(2) Zp_def 
        padic_integers.ac_Zp_factors_x(1) padic_integers_axioms 
      by blast    
  qed
  then have "x \<otimes> y =  (\<p>[^](nat ((ord_Zp x) + (ord_Zp y)))) \<otimes> (ac_Zp (x \<otimes> y))"
    using assms ord_Zp_mult[of x y]   
    by (simp add: Zp_def)
  then have "x \<otimes> y =  (\<p>[^]((nat (ord_Zp x)) + nat (ord_Zp y))) \<otimes> (ac_Zp (x \<otimes> y))"
    using nonzero_closed nonzero_memE(2) assms(1) assms(2) 
          nat_add_distrib ord_pos by auto    
  then have "x \<otimes> y =  (\<p>[^](nat (ord_Zp x))) \<otimes> (\<p>[^](nat(ord_Zp y))) \<otimes> (ac_Zp (x \<otimes> y))"
    using p_natpow_prod 
    by metis 
  then have P2: "(\<p>[^](nat (ord_Zp x))) \<otimes> (\<p>[^](nat(ord_Zp y))) \<otimes> (ac_Zp (x \<otimes> y))
            = ((\<p>[^](nat (ord_Zp x))) \<otimes> (ac_Zp x)) \<otimes> ((\<p>[^](nat (ord_Zp y))) \<otimes> (ac_Zp y))"
    using P0 P1 
    by metis   
  have "(\<p>[^](nat (ord_Zp x))) \<otimes> (\<p>[^](nat(ord_Zp y))) \<otimes> (ac_Zp (x \<otimes> y))
            = ((\<p>[^](nat (ord_Zp x))) \<otimes> ((\<p>[^](nat (ord_Zp y))) \<otimes> (ac_Zp x)) \<otimes> (ac_Zp y))"
    by (metis P0 P1 Zp_def \<open>x \<otimes> y = [p] \<cdot> \<one> [^] nat (ord_Zp x) \<otimes> [p] \<cdot> \<one> [^] nat (ord_Zp y) \<otimes> ac_Zp (x \<otimes> y)\<close>
        mult_comm padic_integers.mult_assoc padic_integers_axioms)   
  then have "((\<p>[^](nat (ord_Zp x))) \<otimes> (\<p>[^](nat(ord_Zp y)))) \<otimes> (ac_Zp (x \<otimes> y))
            =((\<p>[^](nat (ord_Zp x))) \<otimes> (\<p>[^](nat(ord_Zp y)))) \<otimes> ((ac_Zp x) \<otimes> (ac_Zp y))"
    using Zp_def mult_assoc by auto    
  then show ?thesis 
    by (metis (no_types, lifting) R.m_closed
        \<open>x \<otimes> y = [p] \<cdot> \<one> [^] nat (ord_Zp x) \<otimes> [p] \<cdot> \<one> [^] nat (ord_Zp y) \<otimes> ac_Zp (x \<otimes> y)\<close> 
        ac_Zp_in_Zp assms(1) assms(2) integral_iff m_lcancel
        nonzero_closed nonzero_memE(2) p_pow_nonzero(1)) 
qed

lemma(in padic_integers) ac_Zp_one:
"ac_Zp \<one> = \<one>"
  by (metis R.one_closed Zp_def ac_Zp_factors_x(2) int_pow_0 ord_Zp_one padic_integers.ac_Zp_in_Zp padic_integers_axioms padic_one_id prime zero_not_one)

lemma(in padic_integers) ac_Zp_inv:
  assumes "x \<in> Units Zp"
  shows "ac_Zp (inv\<^bsub>Zp\<^esub> x) = inv\<^bsub>Zp\<^esub> (ac_Zp x)"
proof-
  have "x \<otimes> (inv\<^bsub>Zp\<^esub> x) = \<one>"
    using assms by simp
  then have "(ac_Zp x) \<otimes> (ac_Zp (inv\<^bsub>Zp\<^esub> x)) = ac_Zp \<one>"
    using ac_Zp_mult[of x "(inv x)"] R.Units_nonzero
          assms zero_not_one by auto
  then show ?thesis  
    using R.invI(2)[of "(ac_Zp x)" "(ac_Zp (inv\<^bsub>Zp\<^esub> x))"] assms ac_Zp_in_Zp ac_Zp_one 
    by (metis (no_types, lifting) R.Units_closed R.Units_inv_closed 
        R.Units_r_inv integral_iff R.inv_unique ac_Zp_is_Unit)
qed

lemma(in padic_integers) ac_Zp_of_Unit:
  assumes "val_Zp x = 0"
  assumes "x \<in> carrier Zp"
  shows "ac_Zp x = x"
  using assms unfolding val_Zp_def 
  by (metis R.one_closed Zp_def ac_Zp_factors_x(2) ac_Zp_one eint.inject infinity_ne_i0 mult_assoc
      ord_Zp_def ord_Zp_one padic_integers.ac_Zp_in_Zp padic_integers_axioms padic_one_id prime zero_eint_def zero_not_one)
  
lemma(in padic_integers) ac_Zp_p:
"(ac_Zp \<p>) = \<one>"
proof-
  have 0: "\<p> = \<p> [^] nat (ord_Zp \<p>) \<otimes> ac_Zp \<p>"
    using ac_Zp_factors_x[of \<p>]  ord_Zp_p ord_of_nonzero(1) 
    by auto    
  have 1: "\<p> [^] nat (ord_Zp \<p>) = \<p>"
    by (metis One_nat_def nat_1 ord_Zp_p p_pow_rep0 power_one_right)
  then have 2: "\<p> = \<p> \<otimes> ac_Zp \<p>"
    using "0" by presburger
  have "ac_Zp \<p> \<in> carrier Zp"
    using ac_Zp_in_Zp[of \<p>] 
    by (simp add: ord_Zp_p ord_of_nonzero(1))      
  then show ?thesis 
    by (metis "1" "2" m_lcancel R.one_closed R.r_one 
        Zp_int_inc_closed p_pow_nonzero(2))
qed

lemma(in padic_integers) ac_Zp_p_nat_pow:
"(ac_Zp (\<p> [^] (n::nat))) = \<one>"
  apply(induction n)
   apply (simp add: ac_Zp_one)
      using ac_Zp_mult ac_Zp_p int_nat_pow_rep nat_pow_Suc2 R.nat_pow_one
        R.one_closed p_natpow_prod_Suc(1) p_nonzero p_pow_nonzero' p_pow_rep0
      by auto 

text\<open>Facts for reasoning about integer powers in an arbitrary commutative monoid:\<close>

lemma(in monoid) int_pow_add: 
  fixes n::int 
  fixes m::int
  assumes "a \<in> Units G"
  shows "a [^] (n + m) = (a [^] n) \<otimes> (a [^] m)"
proof-
  have 0: "group (units_of G)"
    by (simp add: units_group)
  have 1: "a \<in> carrier (units_of G)"
    by (simp add: assms units_of_carrier)
  have "\<And>n::int. a [^] n = a [^]\<^bsub>units_of G\<^esub> n"
  proof- fix k::int  show "a [^] k = a [^]\<^bsub>units_of G\<^esub> k" using 1 assms units_of_pow
    by (metis Units_pow_closed int_pow_def nat_pow_def units_of_inv units_of_pow)
  qed
  have 2: "a [^]\<^bsub>units_of G\<^esub> (n + m) = (a [^]\<^bsub>units_of G\<^esub> n) \<otimes>\<^bsub>units_of G\<^esub> (a [^]\<^bsub>units_of G\<^esub> m)"
    by (simp add: "1" group.int_pow_mult units_group)
  show ?thesis using 0 1 2 
    by (simp add: \<open>\<And>n. a [^] n = a [^]\<^bsub>units_of G\<^esub> n\<close> units_of_mult)
qed

lemma(in monoid)  int_pow_unit_closed: 
  fixes n::int 
  assumes "a \<in> Units G"
  shows "a[^] n \<in> Units G"
  apply(cases "n \<ge> 0")
  using units_of_def[of G] units_group Units_inv_Units[of a] 
        Units_pow_closed[of "inv a"] Units_pow_closed[of a]
  apply (metis assms pow_nat)
    using units_of_def[of G] units_group Units_inv_Units[of a] 
        Units_pow_closed[of "inv a"] Units_pow_closed[of a]
    by (simp add: assms int_pow_def nat_pow_def)

lemma(in monoid)  nat_pow_of_inv: 
  fixes n::nat 
  assumes "a \<in> Units G"
  shows "inv a[^] n = inv (a[^] n)"
  by (metis (no_types, hide_lams) Units_inv_Units Units_inv_closed Units_inv_inv Units_pow_closed
      Units_r_inv assms inv_unique' nat_pow_closed nat_pow_one pow_mult_distrib)
    
lemma(in monoid)  int_pow_of_inv:
  fixes n::int
  assumes "a \<in> Units G"
  shows "inv a[^] n = inv  (a[^] n)"
  apply(cases "n \<ge>0")
  apply (metis assms nat_pow_of_inv pow_nat)
    by (metis assms int_pow_def2 nat_pow_of_inv)

lemma(in monoid)  int_pow_inv: 
  fixes n::int 
  assumes "a \<in> Units G"
  shows "a[^] -n = inv  a[^] n"
  apply(cases "n =0")
  apply simp
    apply(cases "n > 0")
    using int_pow_def2[of G a "-n"] int_pow_of_inv
    apply (simp add: assms)
      using assms int_pow_def2[of G a "-n"] int_pow_def2[of G a "n"] int_pow_def2[of G "inv a"]
        int_pow_of_inv[of a n] Units_inv_Units[of a] Units_inv_inv Units_pow_closed[of a]
      by (metis linorder_not_less nat_0_iff nat_eq_iff2 nat_zero_as_int neg_0_less_iff_less)

lemma(in monoid)  int_pow_inv': 
  fixes n::int 
  assumes "a \<in> Units G"
  shows "a[^] -n = inv  (a[^] n)"
  by (simp add: assms int_pow_inv int_pow_of_inv)

lemma(in comm_monoid) inv_of_prod:
  assumes "a \<in> Units G"
  assumes "b \<in> Units G"
  shows "inv (a \<otimes>  b) = (inv  a) \<otimes> (inv  b)"
  by (metis Units_m_closed assms(1) assms(2) comm_monoid.m_comm comm_monoid_axioms  
      group.inv_mult_group monoid.Units_inv_closed monoid_axioms units_group 
      units_of_carrier units_of_inv units_of_mult)


(*************************************************************************************************)
(*************************************************************************************************)
(************)section\<open>Behaviour of $val\_Zp$ and $ord\_Zp$ on Natural Numbers and Integers\<close> (***********)
(*************************************************************************************************)
(*************************************************************************************************)

text\<open>If f and g have an equal residue at k, then they differ by a multiple of $p^k$.\<close>
lemma(in padic_integers) eq_residue_mod:
  assumes "f \<in> carrier Zp"
  assumes "g \<in> carrier Zp"
  assumes "f k = g k"
  shows "\<exists>h. h \<in> carrier Zp \<and> f = g \<oplus> (\<p>[^]k)\<otimes>h"
proof(cases "f = g")
  case True
  then show ?thesis 
    using Zp_int_inc_zero' assms(1) by auto 
next
  case False
    have "(f \<ominus> g) k = 0"
      using assms 
      by (metis  R.r_right_minus_eq residue_of_diff residue_of_zero(2))
    then have "ord_Zp (f \<ominus> g) \<ge> k"
      using False assms 
      by (simp add: ord_Zp_geq)
    then obtain m::int where m_def: "m \<ge> 0 \<and> ord_Zp (f \<ominus> g) = k + m"
      using zle_iff_zadd by auto
    have "f \<ominus> g = \<p>[^](k + m) \<otimes> ac_Zp (f \<ominus> g)" 
      using ac_Zp_factors_x(2)[of "f \<ominus> g"] False m_def assms(1) assms(2) by auto
    then have 0: "f \<ominus> g = \<p>[^]k \<otimes> \<p> [^] m \<otimes> ac_Zp (f \<ominus> g)" 
      by (simp add: Zp_def m_def padic_integers.p_natintpow_prod padic_integers_axioms)
    have "\<p>[^]k \<otimes> \<p> [^] m \<otimes> ac_Zp (f \<ominus> g) \<in> carrier Zp"
      using assms "0" by auto
    then have "f = g \<oplus> \<p>[^]k \<otimes> \<p> [^] m \<otimes> ac_Zp (f \<ominus> g)"
      using 0 assms R.ring_simprules  
      by simp 
    then show ?thesis using mult_assoc
      by (metis "0" False R.m_closed R.r_right_minus_eq \<open>[p] \<cdot> \<one> [^] k \<otimes> [p] \<cdot> \<one> [^] m \<otimes> ac_Zp (f \<ominus> g) \<in> carrier Zp\<close> ac_Zp_in_Zp assms(1) assms(2) m_def p_pow_car)
qed

lemma(in padic_integers) eq_residue_mod':
  assumes "f \<in> carrier Zp"
  assumes "g \<in> carrier Zp"
  assumes "f k = g k"
  obtains h where  "h \<in> carrier Zp \<and> f = g \<oplus> (\<p>[^]k)\<otimes>h"
  using assms eq_residue_mod by meson 

text\<open>Valuations of integers which do not divide $p$:\<close>

lemma(in padic_integers) ord_Zp_p_nat_unit:
  assumes "(n::nat) mod p \<noteq> 0"
  shows "ord_Zp ([n]\<cdot>\<one>) = 0"
  using ord_equals[of "[n]\<cdot>\<one>" "0::nat"]
  by (simp add: Zp_nat_inc_res assms)  
 
lemma(in padic_integers) val_Zp_p_nat_unit:
  assumes "(n::nat) mod p \<noteq> 0"
  shows "val_Zp ([n]\<cdot>\<one>) = 0"
  unfolding val_Zp_def 
  using assms ord_Zp_def ord_Zp_p_nat_unit ord_of_nonzero(1) zero_eint_def by auto  

lemma(in padic_integers) nat_unit:
  assumes "(n::nat) mod p \<noteq> 0"
  shows "([n]\<cdot>\<one>) \<in> Units Zp "
  using Zp_nat_mult_closed  val_Zp_p_nat_unit  
  by (simp add: assms val_Zp_0_imp_unit ord_Zp_p_nat_unit)  

lemma(in padic_integers) ord_Zp_p_int_unit:
  assumes "(n::int) mod p \<noteq> 0"
  shows "ord_Zp ([n]\<cdot>\<one>) = 0"
  by (metis One_nat_def Zp_int_inc_closed Zp_int_inc_res assms mod_by_1 of_nat_0 ord_equals power_0 power_one_right)

lemma(in padic_integers) val_Zp_p_int_unit:
  assumes "(n::int) mod p \<noteq> 0"
  shows "val_Zp ([n]\<cdot>\<one>) = 0"
  unfolding val_Zp_def 
  using assms ord_Zp_def ord_Zp_p_int_unit ord_of_nonzero(1) zero_eint_def by auto  

lemma(in padic_integers) int_unit:
  assumes "(n::int) mod p \<noteq> 0"
  shows "([n]\<cdot>\<one>) \<in> Units Zp "
  by (simp add: assms val_Zp_0_imp_unit val_Zp_p_int_unit)

lemma(in padic_integers) int_decomp_ord:
  assumes "n = l*(p^k)"
  assumes "l mod p \<noteq> 0"
  shows "ord_Zp ([n]\<cdot>\<one>) = k"
proof-
  have 0: "n = l * (p^k)"
    using assms(1) 
    by simp
  then have "(l * (p ^ k) mod (p ^ (Suc k))) \<noteq> 0"
    using Zp_def Zp_nat_inc_zero assms(2) p_nonzero nonzero_memE
      padic_integers_axioms R.int_inc_zero nonzero_memE(2) by auto   
   then have 3: "(l * p ^ k) mod  (p ^ (Suc k)) \<noteq> 0"
     by presburger
  show ?thesis 
    using "0" "3" Zp_int_inc_res ord_equals by auto
qed

lemma(in padic_integers) int_decomp_val:
  assumes "n = l*(p^k)"
  assumes "l mod p \<noteq> 0"
  shows "val_Zp ([n]\<cdot>\<one>) = k"
  using Zp_def assms(1) assms(2) R.int_inc_closed ord_of_nonzero(1) int_decomp_ord padic_integers_axioms val_ord_Zp 
  by auto

text\<open>$\mathbb{Z}_p$ has characteristic zero:\<close>

lemma(in padic_integers) Zp_char_0:
  assumes "(n::int) > 0"
  shows "[n]\<cdot>\<one> \<noteq> \<zero>"
proof-
  have "prime (nat p)"
    using prime prime_nat_iff_prime 
    by blast
  then obtain l0 k where 0: "nat n = l0*((nat p)^k) \<and> \<not> (nat p) dvd l0 "
    using prime assms prime_power_canonical[of "nat p" "nat n"] 
    by auto
  obtain l where l_def: "l = int l0"
    by blast 
  have 1: "n = l*(p^k) \<and> \<not> p dvd l "
    using 0 l_def 
    by (smt assms int_dvd_int_iff int_nat_eq of_nat_mult of_nat_power prime prime_gt_0_int)
  show ?thesis 
    apply(cases "l = 1") 
    using 1 p_pow_nonzero(2) p_pow_rep0 apply auto[1]
    using 1 by (simp add: dvd_eq_mod_eq_0 int_decomp_ord ord_of_nonzero(1))
qed    

lemma(in padic_integers) Zp_char_0':
  assumes "(n::nat) > 0"
  shows "[n]\<cdot>\<one> \<noteq> \<zero>"
proof-
  have "[n]\<cdot>\<one> = [(int n)]\<cdot>\<one>"
    using assms 
    by (simp add: add_pow_def int_pow_int)
  then show ?thesis using assms Zp_char_0[of "int n"]
    by simp
qed

lemma (in domain) not_eq_diff_nonzero:
  assumes "a \<noteq> b"
  assumes "a \<in> carrier R"
  assumes "b \<in>carrier R"
  shows "a \<ominus> b \<in> nonzero R" 
  by (simp add: nonzero_def assms(1) assms(2) assms(3))

lemma (in domain) minus_a_inv:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  shows "a \<ominus> b = \<ominus> (b \<ominus> a)"
  by (simp add: add.inv_mult_group assms(1) assms(2) minus_eq)

lemma(in ring) plus_diff_simp:
  assumes "a \<in> carrier R"
  assumes "b \<in> carrier R"
  assumes "c \<in> carrier R"
  assumes  "X = a \<ominus> b"
  assumes "Y = c \<ominus> a"
  shows "X \<oplus> Y = c \<ominus> b"
  using assms 
  unfolding a_minus_def 
  using ring_simprules 
  by (simp add: r_neg r_neg2)

lemma (in padic_integers) Zp_residue_eq:
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "val_Zp (a \<ominus> b) > k"
  shows "(a k) = (b k)" 
proof-
  have 0: "(a \<ominus> b) k = a k \<ominus>\<^bsub>Zp_res_ring k\<^esub> b k"
    using assms 
    by (simp add: residue_of_diff)
  have 1: "(a \<ominus> b) k = 0"
    using assms zero_below_val 
    by (smt R.minus_closed Zp_def eint_ord_simps(2) padic_integers.p_res_ring_zero 
        padic_integers.residue_of_zero(1) padic_integers.val_ord_Zp padic_integers.zero_below_ord padic_integers_axioms)    
  show ?thesis
    apply(cases "k = 0")
    apply (metis assms(1) assms(2) p_res_ring_0' residues_closed)
    using 0 1 assms  p_residues R_cring Zp_def assms(1) assms(2) cring_def padic_set_res_closed 
           residues.res_zero_eq ring.r_right_minus_eq
  by (metis Zp_defs(3) linorder_neqE_nat not_less0 p_res_ring_zero)
qed

lemma (in padic_integers) Zp_residue_eq2:
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "(a k) = (b k)" 
  assumes "a \<noteq> b"
  shows "val_Zp (a \<ominus> b) \<ge> k"
proof-
  have "(a \<ominus> b) k = 0"
    using assms residue_of_diff 
    by (simp add: Zp_def padic_integers.residue_of_diff' padic_integers_axioms)
  then show ?thesis 
    using assms(1) assms(2) ord_Zp_def ord_Zp_geq val_Zp_def by auto 
qed

lemma (in padic_integers) equal_val_Zp:
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "c \<in> carrier Zp"
  assumes "val_Zp a = val_Zp b"
  assumes "val_Zp (c \<ominus> a) > val_Zp b"
  shows "val_Zp c = val_Zp b"
proof-
  have 0: "val_Zp c = val_Zp (c \<ominus> a \<oplus> a)"
    using assms 
    by (simp add: R.l_neg R.minus_eq add_assoc)  
  have "val_Zp c \<ge> min (val_Zp (c \<ominus> a)) (val_Zp a)"
    using val_Zp_ultrametric[of "(c \<ominus> a)" a]  assms(1)
          assms(3) ord_Zp_ultrametric_eq'' 
    by (simp add: "0")      
  then have 1: "val_Zp c \<ge> (val_Zp a)"
    by (metis assms(4) assms(5) dual_order.order_iff_strict less_le_trans min_le_iff_disj)  
  have  "val_Zp c = (val_Zp a)"
  proof(rule ccontr)
    assume A: "val_Zp c \<noteq> val_Zp a"
    then have 0: "val_Zp c > val_Zp a"
      using 1 A by auto       
    then have "val_Zp (c \<oplus> (a \<ominus> c)) \<ge> min (val_Zp c) (val_Zp (a \<ominus> c))"
      by (simp add: assms(1) assms(3) val_Zp_ultrametric)      
    then have 1: "val_Zp a \<ge> min (val_Zp c) (val_Zp (a \<ominus> c))"
      using assms(1) assms(3) assms(4) assms(5) val_Zp_ultrametric_eq' 0 by auto           
    have 2: "val_Zp (a \<ominus> c) > val_Zp a"
      using "0" assms(1) assms(3) assms(4) assms(5) 
        val_Zp_ultrametric_eq' by auto
    then have "val_Zp a > val_Zp a"
      using 0 1 2 val_Zp_of_a_inv 
      by (metis assms(1) assms(3) assms(4) assms(5) val_Zp_ultrametric_eq')      
    then show False 
      by blast
  qed
  then show ?thesis 
    using assms(4) 
    by simp   
qed

lemma (in padic_integers) equal_val_Zp':
  assumes "a \<in> carrier Zp"
  assumes "b \<in> carrier Zp"
  assumes "c \<in> carrier Zp"
  assumes "val_Zp a = val_Zp b"
  assumes "val_Zp c > val_Zp b"
  shows "val_Zp (a \<oplus> c) = val_Zp b"
proof-
  have 0: "val_Zp b < val_Zp (a \<oplus> c \<ominus> a)"
    by (simp add: R.minus_eq nonzero_closed R.r_neg1 add_comm assms(1) assms(3) assms(5))
  have 1: "val_Zp a \<noteq> val_Zp (\<ominus> c)"
    using assms(3) assms(4) assms(5) 
    by (metis eq_iff not_less val_Zp_of_a_inv)
  then show ?thesis
    by (meson "0" R.semiring_axioms assms(1) assms(2) assms(3) assms(4) equal_val_Zp semiring.semiring_simprules(1))
qed

lemma (in padic_integers) val_Zp_of_minus:
  assumes "a \<in> carrier Zp"
  shows "val_Zp a = val_Zp (\<ominus> a)"
  using assms not_nonzero_Zp ord_Zp_def ord_Zp_of_a_inv val_Zp_def 
  by auto
   
end
