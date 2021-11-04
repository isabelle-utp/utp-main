(*
  Author: Jose Divasón
  Email:  jose.divason@unirioja.es
*)

section \<open>Definition of Smith normal form in HOL Analysis\<close>

theory Smith_Normal_Form
  imports   
    Hermite.Hermite   
begin


subsection \<open>Definitions\<close>

text\<open>Definition of diagonal matrix\<close>

definition "isDiagonal_upt_k A k = (\<forall> a b. (to_nat a \<noteq> to_nat b \<and> (to_nat a < k \<or> (to_nat b < k))) \<longrightarrow> A $ a $ b = 0)"
definition "isDiagonal A = (\<forall> a b. to_nat a \<noteq> to_nat b \<longrightarrow> A $ a $ b = 0)"

lemma isDiagonal_intro:
  fixes A::"'a::{zero}^'cols::mod_type^'rows::mod_type"
  assumes "\<And>a::'rows. \<And>b::'cols. to_nat a = to_nat b"
  shows "isDiagonal A"
  using assms
  unfolding isDiagonal_def by auto

text\<open>Definition of Smith normal form up to position k. The element $A_{k-1,k-1}$ 
does not need to divide $A_{k,k}$ and $A_{k,k}$ could have non-zero entries above and below.\<close>

  definition "Smith_normal_form_upt_k A k = 
  (
    (\<forall>a b. to_nat a = to_nat b \<and> to_nat a + 1 < k \<and> to_nat b + 1< k \<longrightarrow> A $ a $ b dvd A $ (a+1) $ (b+1))
    \<and> isDiagonal_upt_k A k
  )"

definition "Smith_normal_form A = 
  (
    (\<forall>a b. to_nat a = to_nat b \<and> to_nat a + 1 < nrows A \<and> to_nat b + 1 < ncols A \<longrightarrow> A $ a $ b dvd A $ (a+1) $ (b+1))
    \<and> isDiagonal A    
  )"

subsection \<open>Basic properties\<close>

lemma Smith_normal_form_min: 
  "Smith_normal_form A = Smith_normal_form_upt_k A (min (nrows A) (ncols A))"
  unfolding Smith_normal_form_def Smith_normal_form_upt_k_def nrows_def ncols_def 
  unfolding isDiagonal_upt_k_def isDiagonal_def
  by (auto, smt Suc_le_eq le_trans less_le min.boundedI not_less_eq_eq suc_not_zero 
      to_nat_less_card to_nat_plus_one_less_card')


lemma Smith_normal_form_upt_k_0[simp]: "Smith_normal_form_upt_k A 0" 
  unfolding Smith_normal_form_upt_k_def 
  unfolding isDiagonal_upt_k_def isDiagonal_def
  by auto

lemma Smith_normal_form_upt_k_intro:
  assumes "(\<And>a b. to_nat a = to_nat b \<and> to_nat a + 1 < k \<and> to_nat b + 1< k \<Longrightarrow> A $ a $ b dvd A $ (a+1) $ (b+1))"
  and "(\<And>a b. (to_nat a \<noteq> to_nat b \<and> (to_nat a < k \<or> (to_nat b < k))) \<Longrightarrow> A $ a $ b = 0)"
shows "Smith_normal_form_upt_k A k"
  unfolding Smith_normal_form_upt_k_def 
  unfolding isDiagonal_upt_k_def isDiagonal_def using assms by simp

lemma Smith_normal_form_upt_k_intro_alt:
  assumes "(\<And>a b. to_nat a = to_nat b \<and> to_nat a + 1 < k \<and> to_nat b + 1 < k \<Longrightarrow> A $ a $ b dvd A $ (a+1) $ (b+1))"
  and "isDiagonal_upt_k A k"
  shows "Smith_normal_form_upt_k A k"
  using assms 
  unfolding Smith_normal_form_upt_k_def by auto 

lemma Smith_normal_form_upt_k_condition1:
  fixes A::"'a::{bezout_ring}^'cols::mod_type^'rows::mod_type"
  assumes "Smith_normal_form_upt_k A k" 
  and "to_nat a = to_nat b" and " to_nat a + 1 < k" and "to_nat b + 1 < k "
  shows "A $ a $ b dvd A $ (a+1) $ (b+1)"          
  using assms unfolding Smith_normal_form_upt_k_def by auto


lemma Smith_normal_form_upt_k_condition2:
  fixes A::"'a::{bezout_ring}^'cols::mod_type^'rows::mod_type"
  assumes "Smith_normal_form_upt_k A k" 
  and "to_nat a \<noteq> to_nat b" and "(to_nat a < k \<or> to_nat b < k)"
  shows "((A $ a) $ b) = 0"
  using assms unfolding Smith_normal_form_upt_k_def
  unfolding isDiagonal_upt_k_def isDiagonal_def by auto


lemma Smith_normal_form_upt_k1_intro:
  fixes A::"'a::{bezout_ring}^'cols::mod_type^'rows::mod_type"
  assumes s: "Smith_normal_form_upt_k A k" 
  and cond1: "A $ from_nat (k - 1) $ from_nat (k-1) dvd A $ (from_nat k) $ (from_nat k)"
  and cond2a: "\<forall>a. to_nat a > k \<longrightarrow> A $ a $ from_nat k = 0"
  and cond2b: "\<forall>b. to_nat b > k \<longrightarrow> A $ from_nat k $ b = 0"
shows "Smith_normal_form_upt_k A (Suc k)"
proof (rule Smith_normal_form_upt_k_intro)
  fix a::'rows and b::'cols 
  assume a: "to_nat a \<noteq> to_nat b \<and> (to_nat a < Suc k \<or> to_nat b < Suc k)"
  show "A $ a $ b = 0" 
    by (metis Smith_normal_form_upt_k_condition2 a 
        assms(1) cond2a cond2b from_nat_to_nat_id less_SucE nat_neq_iff)
next
  fix a::'rows and b::'cols 
  assume a: "to_nat a = to_nat b \<and> to_nat a + 1 < Suc k \<and> to_nat b + 1 < Suc k"
  show "A $ a $ b dvd A $ (a + 1) $ (b + 1)"
    by (metis (mono_tags, lifting) Smith_normal_form_upt_k_condition1 a add_diff_cancel_right' cond1
        from_nat_suc from_nat_to_nat_id less_SucE s)
qed

lemma Smith_normal_form_upt_k1_intro_diagonal:
  fixes A::"'a::{bezout_ring}^'cols::mod_type^'rows::mod_type"
  assumes s: "Smith_normal_form_upt_k A k" 
  and d: "isDiagonal A"
  and cond1: "A $ from_nat (k - 1) $ from_nat (k-1) dvd A $ (from_nat k) $ (from_nat k)"
shows "Smith_normal_form_upt_k A (Suc k)"
proof (rule Smith_normal_form_upt_k_intro)
  fix a::'rows and b::'cols 
  assume a: "to_nat a = to_nat b \<and> to_nat a + 1 < Suc k \<and> to_nat b + 1 < Suc k"
  show "A $ a $ b dvd A $ (a + 1) $ (b + 1)"
    by (metis (mono_tags, lifting) Smith_normal_form_upt_k_condition1 a 
        add_diff_cancel_right' cond1 from_nat_suc from_nat_to_nat_id less_SucE s)    
next
  show "\<And>a b. to_nat a \<noteq> to_nat b \<and> (to_nat a < Suc k \<or> to_nat b < Suc k) \<Longrightarrow> A $ a $ b = 0"
    using d isDiagonal_def by blast
qed


end