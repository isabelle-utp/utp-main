(* Title:      Tests
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Tests\<close>

theory Tests

imports Subset_Boolean_Algebras.Subset_Boolean_Algebras Base

begin

context subset_boolean_algebra_extended
begin

sublocale sba_dual: subset_boolean_algebra_extended where uminus = uminus and sup = inf and minus = "\<lambda>x y . -(-x \<sqinter> y)" and inf = sup and bot = top and less_eq = greater_eq and less = greater and top = bot
  apply unfold_locales
  apply (simp add: inf_associative)
  apply (simp add: inf_commutative)
  using inf_cases_2 apply simp
  using inf_closed apply simp
  apply simp
  apply simp
  using sub_sup_closed sub_sup_demorgan apply simp
  apply simp
  apply (simp add: inf_commutative less_eq_inf)
  by (metis inf_commutative inf_idempotent inf_left_dist_sup sub_less_def sup_absorb sup_right_zero top_double_complement)

lemma strict_leq_def:
  "-x < -y \<longleftrightarrow> -x \<le> -y \<and> \<not> (-y \<le> -x)"
  by (simp add: sba_dual.sba_dual.sub_less_def sba_dual.sba_dual.sub_less_eq_def)

lemma one_def:
  "top = -bot"
  by simp

end

class tests = times + uminus + one + ord + sup + bot +
  assumes sub_assoc: "-x * (-y * -z) = (-x * -y) * -z"
  assumes sub_comm: "-x * -y = -y * -x"
  assumes sub_compl: "-x = -(--x * -y) * -(--x * --y)"
  assumes sub_mult_closed: "-x * -y = --(-x * -y)"
  assumes the_bot_def: "bot = (THE x . (\<forall>y . x = -y * --y))" (* define without imposing uniqueness *)
  assumes one_def: "1 = - bot"
  assumes sup_def: "-x \<squnion> -y = -(--x * --y)"
  assumes leq_def: "-x \<le> -y \<longleftrightarrow> -x * -y = -x"
  assumes strict_leq_def: "-x < -y \<longleftrightarrow> -x \<le> -y \<and> \<not> (-y \<le> -x)"
begin

sublocale tests_dual: subset_boolean_algebra_extended where uminus = uminus and sup = times and minus = "\<lambda>x y . -(-x * y)" and inf = sup and bot = 1 and less_eq = greater_eq and less = greater and top = bot
  apply unfold_locales
  apply (simp add: sub_assoc)
  apply (simp add: sub_comm)
  apply (simp add: sub_compl)
  using sub_mult_closed apply simp
  apply (simp add: the_bot_def)
  apply (simp add: one_def the_bot_def)
  apply (simp add: sup_def)
  apply simp
  apply (simp add: leq_def sub_comm)
  by (simp add: leq_def strict_leq_def sub_comm)

sublocale sba: subset_boolean_algebra_extended where uminus = uminus and sup = sup and minus = "\<lambda>x y . -(-x \<squnion> y)" and inf = times and bot = bot and less_eq = less_eq and less = less and top = 1 ..

text \<open>sets and sequences of tests\<close>

definition test_set :: "'a set \<Rightarrow> bool"
  where "test_set A \<equiv> \<forall>x\<in>A . x = --x"

lemma mult_left_dist_test_set:
  "test_set A \<Longrightarrow> test_set { -p * x | x . x \<in> A }"
  by (smt mem_Collect_eq sub_mult_closed test_set_def)

lemma mult_right_dist_test_set:
  "test_set A \<Longrightarrow> test_set { x * -p | x . x \<in> A }"
  by (smt mem_Collect_eq sub_mult_closed test_set_def)

lemma sup_left_dist_test_set:
  "test_set A \<Longrightarrow> test_set { -p \<squnion> x | x . x \<in> A }"
  by (smt mem_Collect_eq tests_dual.sba_dual.sub_sup_closed test_set_def)

lemma sup_right_dist_test_set:
  "test_set A \<Longrightarrow> test_set { x \<squnion> -p | x . x \<in> A }"
  by (smt mem_Collect_eq tests_dual.sba_dual.sub_sup_closed test_set_def)

lemma test_set_closed:
  "A \<subseteq> B \<Longrightarrow> test_set B \<Longrightarrow> test_set A"
  using test_set_def by auto

definition test_seq :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "test_seq t \<equiv> \<forall>n . t n = --t n"

lemma test_seq_test_set:
  "test_seq t \<Longrightarrow> test_set { t n | n::nat . True }"
  using test_seq_def test_set_def by auto

definition nat_test :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool"
  where "nat_test t s \<equiv> (\<forall>n . t n = --t n) \<and> s = --s \<and> (\<forall>n . t n \<le> s) \<and> (\<forall>x y . (\<forall>n . t n * -x \<le> -y) \<longrightarrow> s * -x \<le> -y)"

lemma nat_test_seq:
  "nat_test t s \<Longrightarrow> test_seq t"
  by (simp add: nat_test_def test_seq_def)

primrec pSum :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"
  where "pSum f 0 = bot"
      | "pSum f (Suc m) = pSum f m \<squnion> f m"

lemma pSum_test:
  "test_seq t \<Longrightarrow> pSum t m = --(pSum t m)"
  apply (induct m)
  apply simp
  by (smt pSum.simps(2) tests_dual.sba_dual.sub_sup_closed test_seq_def)

lemma pSum_test_nat:
  "nat_test t s \<Longrightarrow> pSum t m = --(pSum t m)"
  by (metis nat_test_seq pSum_test)

lemma pSum_upper:
  "test_seq t \<Longrightarrow> i<m \<Longrightarrow> t i \<le> pSum t m"
proof (induct m)
  show "test_seq t \<Longrightarrow> i<0 \<Longrightarrow> t i \<le> pSum t 0"
    by (smt less_zeroE)
next
  fix n
  assume "test_seq t \<Longrightarrow> i<n \<Longrightarrow> t i \<le> pSum t n"
  hence "test_seq t \<Longrightarrow> i<n \<Longrightarrow> t i \<le> pSum t (Suc n)"
    by (smt (z3) pSum.simps(2) pSum_test tests_dual.sba_dual.upper_bound_left tests_dual.transitive test_seq_def)
  thus "test_seq t \<Longrightarrow> i<Suc n \<Longrightarrow> t i \<le> pSum t (Suc n)"
    by (metis less_Suc_eq pSum.simps(2) pSum_test tests_dual.sba_dual.upper_bound_right test_seq_def)
qed

lemma pSum_below:
  "test_seq t \<Longrightarrow> (\<forall>m<k . t m * -p \<le> -q) \<Longrightarrow> pSum t k * -p \<le> -q"
  apply (induct k)
  apply (simp add: tests_dual.top_greatest)
  by (smt (verit, ccfv_threshold) tests_dual.sup_right_dist_inf pSum.simps(2) pSum_test test_seq_def sub_mult_closed less_Suc_eq tests_dual.sba_dual.sub_associative tests_dual.sba_dual.sub_less_eq_def)

lemma pSum_below_nat:
  "nat_test t s \<Longrightarrow> (\<forall>m<k . t m * -p \<le> -q) \<Longrightarrow> pSum t k * -p \<le> -q"
  by (simp add: nat_test_seq pSum_below)

lemma pSum_below_sum:
  "nat_test t s \<Longrightarrow> pSum t x \<le> s"
  by (smt (verit, ccfv_threshold) tests_dual.sup_right_unit nat_test_def one_def pSum_below_nat pSum_test_nat)

lemma ascending_chain_sup_left:
  "ascending_chain t \<Longrightarrow> test_seq t \<Longrightarrow> ascending_chain (\<lambda>n . -p \<squnion> t n) \<and> test_seq (\<lambda>n . -p \<squnion> t n)"
  by (smt (z3) ord.ascending_chain_def tests_dual.sba_dual.sub_sup_closed tests_dual.sba_dual.sub_sup_right_isotone test_seq_def)

lemma ascending_chain_sup_right:
  "ascending_chain t \<Longrightarrow> test_seq t \<Longrightarrow> ascending_chain (\<lambda>n . t n \<squnion> -p) \<and> test_seq (\<lambda>n . t n \<squnion> -p)"
  by (smt ascending_chain_def tests_dual.sba_dual.sub_sup_closed tests_dual.sba_dual.sub_sup_left_isotone test_seq_def)

lemma ascending_chain_mult_left:
  "ascending_chain t \<Longrightarrow> test_seq t \<Longrightarrow> ascending_chain (\<lambda>n . -p * t n) \<and> test_seq (\<lambda>n . -p * t n)"
  by (smt (z3) ascending_chain_def sub_mult_closed tests_dual.sba_dual.reflexive tests_dual.sup_isotone test_seq_def)

lemma ascending_chain_mult_right:
  "ascending_chain t \<Longrightarrow> test_seq t \<Longrightarrow> ascending_chain (\<lambda>n . t n * -p) \<and> test_seq (\<lambda>n . t n * -p)"
  by (smt (z3) ascending_chain_def sub_mult_closed tests_dual.sba_dual.reflexive tests_dual.sup_isotone test_seq_def)

lemma descending_chain_sup_left:
  "descending_chain t \<Longrightarrow> test_seq t \<Longrightarrow> descending_chain (\<lambda>n . -p \<squnion> t n) \<and> test_seq (\<lambda>n . -p \<squnion> t n)"
  by (smt descending_chain_def tests_dual.sba_dual.sub_sup_closed tests_dual.sba_dual.sub_sup_right_isotone test_seq_def)

lemma descending_chain_sup_right:
  "descending_chain t \<Longrightarrow> test_seq t \<Longrightarrow> descending_chain (\<lambda>n . t n \<squnion> -p) \<and> test_seq (\<lambda>n . t n \<squnion> -p)"
  by (smt descending_chain_def tests_dual.sba_dual.sub_sup_closed tests_dual.sba_dual.sub_sup_left_isotone test_seq_def)

lemma descending_chain_mult_left:
  "descending_chain t \<Longrightarrow> test_seq t \<Longrightarrow> descending_chain (\<lambda>n . -p * t n) \<and> test_seq (\<lambda>n . -p * t n)"
  by (smt (z3) descending_chain_def sub_mult_closed tests_dual.sba_dual.reflexive tests_dual.sup_isotone test_seq_def)

lemma descending_chain_mult_right:
  "descending_chain t \<Longrightarrow> test_seq t \<Longrightarrow> descending_chain (\<lambda>n . t n * -p) \<and> test_seq (\<lambda>n . t n * -p)"
  by (smt (z3) descending_chain_def sub_mult_closed tests_dual.sba_dual.reflexive tests_dual.sup_isotone test_seq_def)

end

end

