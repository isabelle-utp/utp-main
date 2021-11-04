section\<open>Antichains\<close>

(*<*)
theory Antichain
  imports
    Auxiliary
begin
(*>*)

definition incomparable where
  "incomparable A = (\<forall>x \<in> A. \<forall>y \<in> A. x \<noteq> y \<longrightarrow> \<not> x < y \<and> \<not> y < x)"

lemma incomparable_empty[simp, intro]: "incomparable {}"
  unfolding incomparable_def by auto

typedef (overloaded) 'a :: order antichain =
  "{A :: 'a set. finite A \<and> incomparable A}"
  morphisms set_antichain antichain
  by auto

setup_lifting type_definition_antichain

lift_definition member_antichain :: "'a :: order \<Rightarrow> 'a antichain \<Rightarrow> bool" ("(_/ \<in>\<^sub>A _)" [51, 51] 50) is "Set.member" .

abbreviation not_member_antichain :: "'a :: order \<Rightarrow> 'a antichain \<Rightarrow> bool" ("(_/ \<notin>\<^sub>A _)" [51, 51] 50) where
  "x \<notin>\<^sub>A A \<equiv> \<not> x \<in>\<^sub>A A"

lift_definition empty_antichain :: "'a :: order antichain" ("{}\<^sub>A") is "{}" by simp

lemma mem_antichain_nonempty[simp]: "s \<in>\<^sub>A A \<Longrightarrow> A \<noteq> {}\<^sub>A"
  by transfer auto

definition "minimal_antichain A = {x \<in> A. \<not>(\<exists>y \<in> A. y < x)}"

lemma in_minimal_antichain: "x \<in> minimal_antichain A \<longleftrightarrow> x \<in> A \<and> \<not>(\<exists>y \<in> A. y < x)"
  unfolding minimal_antichain_def by auto

lemma in_antichain_minimal_antichain[simp]: "finite M \<Longrightarrow> x \<in>\<^sub>A antichain (minimal_antichain M) \<longleftrightarrow> x \<in> minimal_antichain M"
  apply (clarsimp simp: minimal_antichain_def member_antichain.rep_eq)
  apply (intro conjI iffI)
    apply (subst (asm) antichain_inverse)
     apply (simp add: incomparable_def)
    apply simp
   apply (subst (asm) antichain_inverse)
    apply (simp add: incomparable_def)
   apply simp
  apply (subst antichain_inverse)
   apply (simp add: incomparable_def)
  apply simp
  done

lemma incomparable_minimal_antichain[simp]: "incomparable (minimal_antichain A)"
  unfolding incomparable_def minimal_antichain_def
  by auto

lemma finite_minimal_antichain[simp]: "finite A \<Longrightarrow> finite (minimal_antichain A)"
  unfolding minimal_antichain_def by auto

lemma finite_set_antichain[simp, intro]: "finite (set_antichain A)"
  by transfer auto

lemma minimal_antichain_subset: "minimal_antichain A \<subseteq> A"
  unfolding minimal_antichain_def by auto

lift_definition frontier :: "'t :: order zmultiset \<Rightarrow> 't antichain" is
  "\<lambda>M. minimal_antichain {t. zcount M t > 0}"
  by (auto simp: finite_subset[OF minimal_antichain_subset finite_zcount_pos])

lemma member_frontier_pos_zmset: "t \<in>\<^sub>A frontier M \<Longrightarrow> 0 < zcount M t"
  by (simp add: frontier_def in_minimal_antichain)

lemma frontier_comparable_False[simp]: "x \<in>\<^sub>A frontier M \<Longrightarrow> y \<in>\<^sub>A frontier M \<Longrightarrow> x < y \<Longrightarrow> False"
  by transfer (auto simp: minimal_antichain_def)

lemma minimal_antichain_idempotent[simp]: "minimal_antichain (minimal_antichain A) = minimal_antichain A"
  by (auto simp: minimal_antichain_def)

instantiation antichain :: (order) minus begin
lift_definition minus_antichain :: "'a antichain \<Rightarrow> 'a antichain \<Rightarrow> 'a antichain" is "(-)"
  by (auto simp: incomparable_def)
instance ..
end

instantiation antichain :: (order) plus begin
lift_definition plus_antichain :: "'a antichain \<Rightarrow> 'a antichain \<Rightarrow> 'a antichain" is "\<lambda>M N. minimal_antichain (M \<union> N)"
  by (auto simp: incomparable_def minimal_antichain_def)
instance ..
end

lemma antichain_add_commute: "(M :: 'a :: order antichain) + N = N + M"
  by transfer (auto simp: incomparable_def sup_commute)


lift_definition filter_antichain :: "('a :: order \<Rightarrow> bool) \<Rightarrow> 'a antichain \<Rightarrow> 'a antichain" is "Set.filter"
  by (auto simp: incomparable_def)

syntax (ASCII)
  "_ACCollect" :: "pttrn \<Rightarrow> 'a :: order antichain \<Rightarrow> bool \<Rightarrow> 'a antichain" ("(1{_ :\<^sub>A _./ _})")
syntax
  "_ACCollect" :: "pttrn \<Rightarrow> 'a :: order antichain \<Rightarrow> bool \<Rightarrow> 'a antichain" ("(1{_ \<in>\<^sub>A _./ _})")
translations
  "{x \<in>\<^sub>A M. P}" == "CONST filter_antichain (\<lambda>x. P) M"


declare empty_antichain.rep_eq[simp]

lemma minimal_antichain_empty[simp]: "minimal_antichain {} = {}"
  by (simp add: minimal_antichain_def)

lemma minimal_antichain_singleton[simp]: "minimal_antichain {x::_ ::order} = {x}"
  by (auto simp: minimal_antichain_def)

lemma minimal_antichain_nonempty:
  "finite A \<Longrightarrow> (t::_::order) \<in> A \<Longrightarrow> minimal_antichain A \<noteq> {}"
  by (auto simp: minimal_antichain_def dest: order_finite_set_exists_foundation[of _ t])

lemma minimal_antichain_member:
  "finite A \<Longrightarrow> (t::_::order) \<in> A \<Longrightarrow> \<exists>t'. t' \<in> minimal_antichain A \<and> t' \<le> t"
  by (auto simp: minimal_antichain_def dest: order_finite_set_exists_foundation[of _ t])

lemma minimal_antichain_union: "minimal_antichain ((A::(_ :: order) set) \<union> B) \<subseteq> minimal_antichain (minimal_antichain A \<union> minimal_antichain B)"
  by (auto simp: minimal_antichain_def)

lemma ac_Diff_iff: "c \<in>\<^sub>A A - B \<longleftrightarrow> c \<in>\<^sub>A A \<and> c \<notin>\<^sub>A B"
  by transfer simp

lemma ac_DiffD2: "c \<in>\<^sub>A A - B \<Longrightarrow> c \<in>\<^sub>A B \<Longrightarrow> P"
  by transfer simp

lemma ac_notin_Diff: "\<not> x \<in>\<^sub>A A - B \<Longrightarrow> \<not> x \<in>\<^sub>A A \<or> x \<in>\<^sub>A B"
  by transfer simp

lemma ac_eq_iff: "A = B \<longleftrightarrow> (\<forall>x. x \<in>\<^sub>A A \<longleftrightarrow> x \<in>\<^sub>A B)"
  by transfer auto

lemma antichain_obtain_foundation:
  assumes   "t \<in>\<^sub>A M"
  obtains s where "s \<in>\<^sub>A M \<and> s \<le> t \<and> (\<forall>u. u\<in>\<^sub>AM \<longrightarrow> \<not> u < s)"
  using assms unfolding member_antichain.rep_eq
  by - (rule order_finite_set_obtain_foundation[of "set_antichain M" t]; auto)

lemma set_antichain1[simp]: "x \<in> set_antichain X \<Longrightarrow> x \<in>\<^sub>A X"
  by transfer simp

lemma set_antichain2[simp]: "x \<in>\<^sub>A X \<Longrightarrow> x \<in> set_antichain X"
  by transfer simp

(*<*)
end
(*>*)