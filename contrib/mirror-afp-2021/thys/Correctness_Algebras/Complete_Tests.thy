(* Title:      Complete Tests
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Complete Tests\<close>

theory Complete_Tests

imports Tests

begin

class complete_tests = tests + Sup + Inf +
  assumes sup_test: "test_set A \<longrightarrow> Sup A = --Sup A"
  assumes sup_upper: "test_set A \<and> x \<in> A \<longrightarrow> x \<le> Sup A"
  assumes sup_least: "test_set A \<and> (\<forall>x\<in>A . x \<le> -y) \<longrightarrow> Sup A \<le> -y"
begin

lemma Sup_isotone:
  "test_set B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> Sup A \<le> Sup B"
  by (metis sup_least sup_test sup_upper test_set_closed subset_eq)

lemma mult_right_dist_sup:
  assumes "test_set A"
    shows "Sup A * -p = Sup { x * -p | x . x \<in> A }"
proof -
  have 1: "test_set { x * -p | x . x \<in> A }"
    by (simp add: assms mult_right_dist_test_set)
  have 2: "Sup { x * -p | x . x \<in> A } \<le> Sup A * -p"
    by (smt (verit, del_insts) assms mem_Collect_eq tests_dual.sub_sup_left_isotone sub_mult_closed sup_test sup_least sup_upper test_set_def)
  have "\<forall>x\<in>A . x \<le> --(--Sup { x * -p | x . x \<in> A } \<squnion> --p)"
  proof
    fix x
    assume 3: "x \<in> A"
    hence "x * -p \<squnion> --p \<le> Sup { x * -p | x . x \<in> A } \<squnion> --p"
      using 1 by (smt (verit, del_insts) assms mem_Collect_eq tests_dual.sub_inf_left_isotone sub_mult_closed sup_upper test_set_def sup_test)
    thus "x \<le> --(--Sup { x * -p | x . x \<in> A } \<squnion> --p)"
      using 1 3 by (smt (z3) assms tests_dual.inf_closed sub_comm test_set_def sup_test sub_mult_closed tests_dual.sba_dual.shunting_right tests_dual.sba_dual.sub_sup_left_isotone tests_dual.inf_absorb tests_dual.inf_less_eq_cases_3)
  qed
  hence "Sup A \<le> --(--Sup { x * -p | x . x \<in> A } \<squnion> --p)"
    by (simp add: assms sup_least)
  hence "Sup A * -p \<le> Sup { x * -p | x . x \<in> A }"
    using 1 by (smt (z3) assms sup_test tests_dual.sba_dual.shunting tests_dual.sub_commutative tests_dual.sub_sup_closed tests_dual.sub_sup_demorgan)
  thus ?thesis
    using 1 2 by (smt (z3) assms sup_test tests_dual.sba_dual.sub_sup_closed tests_dual.antisymmetric tests_dual.inf_demorgan tests_dual.inf_idempotent)
qed

lemma mult_left_dist_sup:
  assumes "test_set A"
  shows "-p * Sup A = Sup { -p * x | x . x \<in> A }"
proof -
  have 1: "Sup A * -p = Sup { x * -p | x . x \<in> A }"
    by (simp add: assms mult_right_dist_sup)
  have 2: "-p * Sup A = Sup A * -p"
    by (metis assms sub_comm sup_test)
  have "{ -p * x | x . x \<in> A } = { x * -p | x . x \<in> A }"
    by (metis assms test_set_def tests_dual.sub_commutative)
  thus ?thesis
    using 1 2 by simp
qed

definition Sum :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "Sum f \<equiv> Sup { f n | n::nat . True }"

lemma Sum_test:
  "test_seq t \<Longrightarrow> Sum t = --Sum t"
  using Sum_def sup_test test_seq_test_set by auto

lemma Sum_upper:
  "test_seq t \<Longrightarrow> t x \<le> Sum t"
  using Sum_def sup_upper test_seq_test_set by auto

lemma Sum_least:
  "test_seq t \<Longrightarrow> (\<forall>n . t n \<le> -p) \<Longrightarrow> Sum t \<le> -p"
  using Sum_def sup_least test_seq_test_set by force

lemma mult_right_dist_Sum:
  "test_seq t \<Longrightarrow> (\<forall>n . t n * -p \<le> -q) \<Longrightarrow> Sum t * -p \<le> -q"
  by (smt (verit, del_insts) CollectD Sum_def sup_least sup_test test_seq_test_set test_set_def tests_dual.sba_dual.shunting_right tests_dual.sba_dual.sub_sup_closed)

lemma mult_left_dist_Sum:
  "test_seq t \<Longrightarrow> (\<forall>n . -p * t n \<le> -q) \<Longrightarrow> -p * Sum t \<le> -q"
  by (smt (verit, del_insts) Sum_def mem_Collect_eq mult_left_dist_sup sub_mult_closed sup_least test_seq_test_set test_set_def)

lemma pSum_below_Sum:
  "test_seq t \<Longrightarrow> pSum t m \<le> Sum t"
  using Sum_test Sum_upper nat_test_def pSum_below_sum test_seq_def mult_right_dist_Sum by auto

lemma pSum_sup:
  assumes "test_seq t"
    shows "pSum t m = Sup { t i | i . i \<in> {..<m} }"
proof -
  have 1: "test_set { t i | i . i \<in> {..<m} }"
    using assms test_seq_test_set test_set_def by auto
  have "\<forall>y\<in>{ t i | i . i \<in> {..<m} } . y \<le> --pSum t m"
    using assms pSum_test pSum_upper by force
  hence 2: "Sup { t i | i . i \<in> {..<m} } \<le> --pSum t m"
    using 1 by (simp add: sup_least)
  have "pSum t m \<le> Sup { t i | i . i \<in> {..<m} }"
  proof (induct m)
    case 0
    show ?case
      by (smt (verit, ccfv_SIG) Collect_empty_eq empty_iff lessThan_0 pSum.simps(1) sup_test test_set_def tests_dual.top_greatest)
  next
    case (Suc n)
    have 4: "test_set {t i |i. i \<in> {..<n}}"
      using assms test_seq_def test_set_def by auto
    have 5: "test_set {t i |i. i < Suc n}"
      using assms test_seq_def test_set_def by force
    hence 6: "Sup {t i |i. i < Suc n} = --Sup {t i |i. i < Suc n}"
      using sup_test by auto
    hence "\<forall>x\<in>{t i |i. i \<in> {..<n}} . x \<le> --Sup {t i |i. i < Suc n}"
      using 5 less_Suc_eq sup_upper by fastforce
    hence 7: "Sup {t i |i. i \<in> {..<n}} \<le> --Sup {t i |i. i < Suc n}"
      using 4 by (simp add: sup_least)
    have "t n \<in> {t i |i. i < Suc n}"
      by auto
    hence "t n \<le> Sup {t i |i. i < Suc n}"
      using 5 by (simp add: sup_upper)
    hence "pSum t n \<squnion> t n \<le> Sup {t i |i. i <Suc n}"
      using Suc 4 6 7 by (smt assms tests_dual.greatest_lower_bound test_seq_def pSum_test tests_dual.sba_dual.transitive sup_test)
    thus ?case
      by simp
  qed
  thus ?thesis
    using 1 2 by (smt assms tests_dual.antisymmetric sup_test pSum_test)
qed

definition Prod :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "Prod f \<equiv> Inf { f n | n::nat . True }"

lemma Sum_range:
  "Sum f = Sup (range f)"
  by (simp add: Sum_def image_def)

lemma Prod_range:
  "Prod f = Inf (range f)"
  by (simp add: Prod_def image_def)

end

end

