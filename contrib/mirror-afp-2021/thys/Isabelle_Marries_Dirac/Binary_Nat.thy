(* 
Authors: 
  Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk 
  Hanna Lachnitt, TU Wien, lachnitt@student.tuwien.ac.at
*)

section \<open>Binary Representation of Natural Numbers\<close>

theory Binary_Nat
imports
  HOL.Nat
  HOL.List
  Basics
begin 


primrec bin_rep_aux:: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "bin_rep_aux 0 m = [m]"
| "bin_rep_aux (Suc n) m = m div 2^n # bin_rep_aux n (m mod 2^n)"

lemma length_of_bin_rep_aux:
  fixes n m:: nat
  assumes "m < 2^n"
  shows "length (bin_rep_aux n m) = n+1" 
  using assms
proof(induction n arbitrary: m)
  case 0
  then show "length (bin_rep_aux 0 m) = 0 + 1" by simp
next
  case (Suc n)
  assume a0:"\<And>m. m < 2^n \<Longrightarrow> length (bin_rep_aux n m) = n + 1" and "m < 2^(Suc n)"
  then show "length (bin_rep_aux (Suc n) m) = Suc n + 1" 
    using a0 by simp
qed

lemma bin_rep_aux_neq_nil:
  fixes n m:: nat
  shows "bin_rep_aux n m \<noteq> []" 
  using bin_rep_aux.simps by (metis list.distinct(1) old.nat.exhaust)

lemma last_of_bin_rep_aux:
  fixes n m:: nat 
  assumes "m < 2^n" and "m \<ge> 0"
  shows "last (bin_rep_aux n m) = 0"
  using assms
proof(induction n arbitrary: m)
  case 0
  assume "m < 2^0" and "m \<ge> 0"
  then show "last (bin_rep_aux 0 m) = 0" by simp
next
  case (Suc n)
  assume a0:"\<And>m. m < 2^n \<Longrightarrow> m \<ge> 0 \<Longrightarrow> last (bin_rep_aux n m) = 0" and "m < 2^(Suc n)"
and "m \<ge> 0"
  then show "last (bin_rep_aux (Suc n) m) = 0" 
    using bin_rep_aux_neq_nil by simp
qed

lemma mod_mod_power_cancel:
  fixes m n p:: nat
  assumes "m \<le> n"
  shows "p mod 2^n mod 2^m = p mod 2^m" 
  using assms by (simp add: dvd_power_le mod_mod_cancel)
    
lemma bin_rep_aux_index:
  fixes n m i:: nat
  assumes "n \<ge> 1" and "m < 2^n" and "m \<ge> 0" and "i \<le> n"
  shows "bin_rep_aux n m ! i = (m mod 2^(n-i)) div 2^(n-1-i)"
  using assms
proof(induction n arbitrary: m i rule: nat_induct_at_least)
  case base
  assume "m < 2^1" and "i \<le> 1"
  then show "bin_rep_aux 1 m ! i = m mod 2^(1-i) div 2^(1-1-i)" 
    using bin_rep_aux.simps
    by (metis One_nat_def base.prems(2) diff_is_0_eq' diff_zero div_by_1 le_Suc_eq le_numeral_extra(3) 
nth_Cons' power_0 unique_euclidean_semiring_numeral_class.mod_less)
next
  case (Suc n)
  assume a0:"\<And>m i. m < 2^n \<Longrightarrow> m \<ge> 0 \<Longrightarrow> i \<le> n \<Longrightarrow> bin_rep_aux n m ! i = m mod 2 ^ (n-i) div 2^(n-1-i)"
and a1:"m < 2^(Suc n)" and a2:"i \<le> Suc n" and a3:"m \<ge> 0"
  then show "bin_rep_aux (Suc n) m ! i = m mod 2^(Suc n - i) div 2^(Suc n - 1 - i)"
  proof-
    have "bin_rep_aux (Suc n) m = m div 2^n # bin_rep_aux n (m mod 2^n)" by simp
    then have f0:"bin_rep_aux (Suc n) m ! i = (m div 2^n # bin_rep_aux n (m mod 2^n)) ! i" by simp
    then have "bin_rep_aux (Suc n) m ! i = m div 2^n" if "i = 0" using that by simp
    then have f1:"bin_rep_aux (Suc n) m ! i = m mod 2^(Suc n - i) div 2^(Suc n - 1 - i)" if "i = 0"
    proof-
      have "m mod 2^(Suc n - i) = m" 
        using that a1 by (simp add: Suc.prems(2))
      then have "m mod 2^(Suc n - i) div 2^(Suc n - 1 - i) = m div 2^n" 
        using that by simp
      thus ?thesis by (simp add: that)
    qed
    then have "bin_rep_aux (Suc n) m ! i = bin_rep_aux n (m mod 2^n) ! (i-1)" if "i \<ge> 1"
      using that f0 by simp
    then have f2:"bin_rep_aux (Suc n) m ! i = ((m mod 2^n) mod 2^(n - (i - 1))) div 2^(n - 1 - (i - 1))" if "i \<ge> 1"
      using that a0 a1 a2 a3 Suc.prems(2) by simp
    then have f3:"bin_rep_aux (Suc n) m ! i = ((m mod 2^n) mod 2^(Suc n - i)) div 2^(Suc n - 1 - i)" if "i \<ge> 1"
      using that by simp
    then have "bin_rep_aux (Suc n) m ! i = m mod 2^(Suc n - i) div 2^(Suc n - 1 - i)" if "i \<ge> 1" 
    proof-
      have "Suc n - i \<le> n" using that by simp
      then have "m mod 2^n mod 2^(Suc n - i) = m mod 2^(Suc n - i)" 
        using mod_mod_power_cancel[of "Suc n - i" "n" "m"] by simp
      thus ?thesis 
        using that f3 by simp
    qed
    thus ?thesis using f1 f2
      using linorder_not_less by blast
  qed
qed

lemma bin_rep_aux_coeff:
  fixes n m i:: nat
  assumes "m < 2^n" and "i \<le> n" and "m \<ge> 0"
  shows "bin_rep_aux n m ! i = 0 \<or> bin_rep_aux n m ! i = 1"
  using assms
proof(induction n arbitrary: m i)
  case 0
  assume "m < 2^0" and "i \<le> 0" and "m \<ge> 0"
  then show "bin_rep_aux 0 m ! i = 0 \<or> bin_rep_aux 0 m ! i = 1" by simp
next
  case (Suc n)
  assume a0:"\<And>m i. m < 2 ^ n \<Longrightarrow> i \<le> n \<Longrightarrow> m \<ge> 0 \<Longrightarrow> bin_rep_aux n m ! i = 0 \<or> bin_rep_aux n m ! i = 1" 
and a1:"m < 2^Suc n" and a2:"i \<le> Suc n" and a3:"m \<ge> 0"
  then show "bin_rep_aux (Suc n) m ! i = 0 \<or> bin_rep_aux (Suc n) m ! i = 1"
  proof-
    have "bin_rep_aux (Suc n) m ! i = (m div 2^n # bin_rep_aux n (m mod 2^n)) ! i" by simp
    moreover have "\<dots> = bin_rep_aux n (m mod 2^n) ! (i - 1)" if "i \<ge> 1"
      using that by simp
    moreover have "m mod 2^n < 2^n" by simp
    ultimately have "bin_rep_aux (Suc n) m ! i = 0 \<or> bin_rep_aux (Suc n) m ! i = 1" if "i\<ge>1"
      using that a0[of "m mod 2^n" "i-1"] a2 by simp
    moreover have "m div 2^n = 0 \<or> m div 2^n = 1" 
      using a1 a3 less_mult_imp_div_less by(simp add: less_2_cases)
    ultimately show ?thesis by (simp add: nth_Cons')
  qed
qed

definition bin_rep:: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
"bin_rep n m = butlast (bin_rep_aux n m)"

lemma length_of_bin_rep:
  fixes n m:: nat
  assumes "m < 2^n"
  shows "length (bin_rep n m) = n"
  using assms length_of_bin_rep_aux bin_rep_def by simp

lemma bin_rep_coeff:
  fixes n m i:: nat
  assumes "m < 2^n" and "i < n" and "m \<ge> 0"
  shows "bin_rep n m ! i = 0 \<or> bin_rep n m ! i = 1" 
  using assms bin_rep_def bin_rep_aux_coeff length_of_bin_rep by(simp add: nth_butlast)

lemma bin_rep_index:
  fixes n m i:: nat
  assumes "n \<ge> 1" and "m < 2^n" and "i < n" and "m \<ge> 0"
  shows "bin_rep n m ! i = (m mod 2^(n-i)) div 2^(n-1-i)"
proof-
  have "bin_rep n m ! i = bin_rep_aux n m ! i"
    using bin_rep_def length_of_bin_rep nth_butlast assms(3)
    by (simp add: nth_butlast assms(2))
  thus ?thesis
    using assms bin_rep_aux_index by simp
qed

lemma bin_rep_eq:
  fixes n m:: nat 
  assumes "n \<ge> 1" and "m \<ge> 0" and "m < 2^n" and "m \<ge> 0"
  shows "m = (\<Sum>i<n. bin_rep n m ! i * 2^(n-1-i))"
proof-
  {
    fix i:: nat
    assume "i < n"
    then have "bin_rep n m ! i * 2^(n-1-i) = (m mod 2^(n-i)) div 2^(n-1-i) * 2^(n-1-i)"
      using assms bin_rep_index by simp
    moreover have "\<dots> = m mod 2^(n-i) - m mod 2^(n-i) mod 2^(n-1-i)"
      by (simp add: minus_mod_eq_div_mult)
    moreover have "\<dots> = int(m mod 2^(n-i)) - m mod 2^(n-i) mod 2^(n-1-i)" 
      using mod_less_eq_dividend of_nat_diff by blast
    moreover have "\<dots> = int(m mod 2^(n-i)) - m mod 2^(n-1-i)" 
      using mod_mod_power_cancel[of "n-1-i" "n-i"] by (simp add: dvd_power_le mod_mod_cancel)
    ultimately have "bin_rep n m ! i * 2^(n-1-i) = int (m mod 2^(n-i)) - m mod 2^(n-1-i)" 
      by presburger
  }
  then have f0:"(\<Sum>i<n. bin_rep n m ! i * 2^(n-1-i)) = (\<Sum>i<n. int (m mod 2^(n-i)) - m mod 2^(n-1-i))" 
    by auto
  thus ?thesis
  proof-
     have "(\<Sum>i<n. int ((m::nat) mod 2^(n - i)) - (m mod 2^(n - 1 - i))) = 
          (\<Sum>i<n. ( m mod 2^(n - i))) -  (\<Sum>i<n. int (m mod 2^(n - 1 - i)))" 
      using sum_subtractf[of "(\<lambda>i. (m mod 2^(n-i)))::nat\<Rightarrow>nat" "(\<lambda>i. (m mod 2^(n-1-i)))::nat\<Rightarrow>nat" "{..<(n::nat)}"] 
      by auto
    moreover have "\<dots> = m mod 2^n + (\<Sum>i\<in>{1..<n}. (m mod 2^(n-i))) - (\<Sum>i<n-1. int (m mod 2^(n-1-i)))- m mod 2^0" 
      using sum.atLeast_Suc_atMost sum.lessThan_Suc assms(1) 
      by (smt One_nat_def Suc_le_eq diff_self_eq_0 le_add_diff_inverse lessThan_atLeast0 minus_nat.diff_0 
          plus_1_eq_Suc sum.atLeast_Suc_lessThan)
    moreover have "\<dots> = m mod 2^n + (\<Sum>i<n-1. m mod 2^(n-i-1)) - (\<Sum>i<n-1. int ( m mod 2^(n-1-i))) - m mod 2^0" 
      apply (auto simp add: sum_of_index_diff[of "\<lambda>i. m mod 2 ^ (n - 1 - i)" "1" "n-1"])
      by (smt One_nat_def assms(1) le_add_diff_inverse lessThan_atLeast0 plus_1_eq_Suc sum.cong sum.shift_bounds_Suc_ivl)
    moreover have "\<dots> = m mod 2^n - m mod 2^0" by simp
    moreover have "\<dots> = m" using assms by auto
    ultimately show "m = (\<Sum>i<n. bin_rep n m ! i * 2^(n-1-i))"
      using assms f0 by linarith
  qed
qed

lemma bin_rep_index_0:
  fixes n m:: nat
  assumes "m < 2^n" and "k > n"
  shows "(bin_rep k m) ! 0 = 0"
proof-
  have "m < 2^(k-1)" 
    using assms by(smt Suc_diff_1 Suc_leI gr0I le_trans less_or_eq_imp_le linorder_neqE_nat not_less 
one_less_numeral_iff power_strict_increasing semiring_norm(76))
  then have f:"m div 2^(k-1) = 0" 
    by auto
  have "k \<ge> 1" 
    using assms(2) by simp
  moreover have "bin_rep_aux k m = (m div 2^(k-1)) # (bin_rep_aux (k-1) (m mod 2^(k-1)))"
    using bin_rep_aux.simps(2) by(metis Suc_diff_1 assms(2) diff_0_eq_0 neq0_conv zero_less_diff)
  moreover have "bin_rep k m = butlast ((m div 2^(k-1)) # (bin_rep_aux (k-1) (m mod 2^(k-1))))" 
    using bin_rep_def by (simp add: calculation(2))
  moreover have "\<dots> = butlast (0 # (bin_rep_aux (k-1) (m mod 2^(k-1))))" 
    using f by simp
  moreover have "\<dots> = 0 # butlast (bin_rep_aux (k-1) (m mod 2^(k-1)))" 
    by(simp add: bin_rep_aux_neq_nil)
  ultimately show ?thesis 
    by simp
qed

lemma bin_rep_index_0_geq:
  fixes n m:: nat
  assumes "m \<ge> 2^n" and "m < 2^(n+1)"
  shows "bin_rep (n+1) m ! 0 = 1"
proof-
  have "bin_rep (Suc n) m =  butlast (bin_rep_aux (Suc n) m)" 
    using bin_rep_def by simp
  moreover have "\<dots> = butlast (1 # (bin_rep_aux n (m mod 2^n)))" 
    using assms bin_rep_aux_def by simp
  moreover have "\<dots> = 1 # butlast (bin_rep_aux n (m mod 2^n))"
    by (simp add: bin_rep_aux_neq_nil)
  ultimately show ?thesis
    by (simp add: bin_rep_aux_neq_nil)
qed

end