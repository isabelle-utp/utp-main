header {* Extra numeric properties *}

theory Number_extra
  imports
    Real
    "~~/src/HOL/ex/Sqrt"
begin

subsection {* Non-zero naturals *}

definition Nats1 :: "'a :: linordered_semidom set" ("\<nat>\<^sub>1") where
"Nats1 = {n \<in> Nats. n \<ge> 1}"

lemma Nats1_1 [simp]: "1 \<in> \<nat>\<^sub>1"
  by (simp add: Nats1_def)

lemma Nats1_add [simp]:
  "\<lbrakk> a \<in> \<nat>\<^sub>1; b \<in> \<nat>\<^sub>1 \<rbrakk> \<Longrightarrow> a + b \<in> \<nat>\<^sub>1"
  apply (auto simp add: Nats1_def)
  apply (metis add.commute add_le_cancel_right less_add_one linear not_less order_trans)
done

lemma Nats1_mult [simp]:
  "\<lbrakk> a \<in> \<nat>\<^sub>1; b \<in> \<nat>\<^sub>1 \<rbrakk> \<Longrightarrow> a * b \<in> \<nat>\<^sub>1"
  apply (auto simp add: Nats1_def)
  apply (metis comm_monoid_mult_class.mult_1 dual_order.trans mult_right_mono zero_le_one)
done

lemma Nats1_numeral [simp]:
  "numeral(a) \<in> \<nat>\<^sub>1"
  by (simp add: Nats1_def)

lemma Nats1_cases [cases set: Nats1]:
  "\<lbrakk> x \<in> \<nat>\<^sub>1; \<And> n. \<lbrakk> x = of_nat n; n \<ge> 1 \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (auto simp add: Nats1_def)
  apply (erule Nats_cases)
  apply (metis One_nat_def of_nat_1 of_nat_le_iff)
done

subsection {* Numeric subsets *}

lemma Nats1_diff_Nats [simp]: "\<nat>\<^sub>1 \<noteq> \<nat>"
  by (metis Nats1_cases Nats_0 not_one_le_zero of_nat_eq_0_iff)

lemma Nats1_psub_Nats [simp]: "\<nat>\<^sub>1 \<subset> \<nat>"
  by (metis (erased, lifting) Nats1_def Nats1_diff_Nats mem_Collect_eq psubsetI subset_iff)

lemma Nats_diff_Ints [simp]: "(\<nat>::'a::linordered_idom set) \<noteq> \<int>"
proof -
  have "-1 \<in> \<int>"
    by (auto)
  moreover have "-1 \<notin> (\<nat>::'a set)"
    by (metis Nats_cases abs_minus_cancel abs_of_nat abs_one one_neq_neg_one)
  ultimately show ?thesis
    by metis
qed

lemma Nats_psub_Ints [simp]: "(\<nat>::'a::linordered_idom set) \<subset> \<int>"
  by (auto elim:Nats_cases Ints_cases simp add: Nats_diff_Ints)

text {* The following property helps to prove that rationals are not all integers *}

lemma int_2n_not_1: "(2 * (n :: int)) \<noteq> 1"
  by presburger

lemma Ints_floor_transfer: "\<lbrakk> x \<in> Ints; y \<in> Ints \<rbrakk> \<Longrightarrow> x = y \<longleftrightarrow> floor x = floor y"
  by (metis Ints_cases floor_of_int)

lemma Ints_floor_mult [simp]:
  "\<lbrakk> x \<in> Ints; y \<in> Ints \<rbrakk> \<Longrightarrow> floor (x * y) = floor(x) * floor(y)"
  by (metis Ints_cases floor_of_int of_int_mult)

lemma Ints_2n_not_1:
  "(n::'a::floor_ceiling) \<in> Ints \<Longrightarrow> (2 * n) \<noteq> 1"
  apply (auto)
  apply (subgoal_tac "2 * n \<in> \<int>")
  apply (subgoal_tac "2 \<in> (\<int> :: real set)")
  apply (simp add: Ints_floor_transfer)
  apply (metis Ints_cases floor_add_of_int floor_of_int int_2n_not_1 mult_2)
  apply (metis Ints_def of_int_numeral range_eqI)
  apply (metis Ints_1)
done

lemma half_not_int: "(1/2 :: 'a :: floor_ceiling) \<notin> \<int>"
  using Ints_2n_not_1 by fastforce

lemma Int_diff_Rat [simp]: "(\<int>::'a::floor_ceiling set) \<noteq> \<rat>"
proof -
  have "1/2 \<notin> (\<int>::'a::floor_ceiling set)"
    by (metis half_not_int)
  moreover have "1/2 \<in> (\<rat>::'a::floor_ceiling set)"
    by (metis Rats_number_of divide_minus1 divide_zero_left inverse_eq_divide nonzero_Rats_inverse numeral_neq_neg_numeral)
  ultimately show ?thesis
    by blast
qed

lemma Ints_psub_Rats [simp]: "(\<int> :: 'a::floor_ceiling set) \<subset> \<rat>"
  by (auto elim!:Rats_cases Ints_cases simp add: Int_diff_Rat)

lemma Reals_UNIV [simp]:
  "(\<real> :: real set) = UNIV"
  by (simp add: Reals_def)

lemma Rat_diff_Real [simp]: "(\<rat> :: real set) \<noteq> \<real>"
proof -
  have "sqrt(2) \<notin> \<rat>"
    by (metis sqrt_2_not_rat)
  moreover have "sqrt(2) \<in> \<real>"
    by (metis Reals_UNIV UNIV_I)
  ultimately show ?thesis
    by (auto)
qed

lemma Rats_psub_Reals [simp]: "(\<rat> :: real set) \<subset> \<real>"
  by (auto, metis Rat_diff_Real Reals_UNIV)
end