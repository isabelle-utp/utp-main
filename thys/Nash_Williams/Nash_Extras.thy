section \<open>The Pointwise Less-Than Relation Between Two Sets\<close>

theory Nash_Extras
  imports "HOL-Library.Ramsey" "HOL-Library.Countable_Set"

begin

definition less_sets :: "['a::order set, 'a::order set] \<Rightarrow> bool" (infixr "\<lless>" 50)
    where "A \<lless> B \<equiv> \<forall>x\<in>A. \<forall>y\<in>B. x < y"

lemma less_setsD: "\<lbrakk>A \<lless> B; a \<in> A; b \<in> B\<rbrakk> \<Longrightarrow> a < b"
  by (auto simp: less_sets_def)

lemma less_sets_irrefl [simp]: "A \<lless> A \<longleftrightarrow> A = {}"
  by (auto simp: less_sets_def)

lemma less_sets_trans: "\<lbrakk>A \<lless> B; B \<lless> C; B \<noteq> {}\<rbrakk> \<Longrightarrow> A \<lless> C"
  unfolding less_sets_def using less_trans by blast

lemma less_sets_weaken1: "\<lbrakk>A' \<lless> B; A \<subseteq> A'\<rbrakk> \<Longrightarrow> A \<lless> B"
  by (auto simp: less_sets_def)

lemma less_sets_weaken2: "\<lbrakk>A \<lless> B'; B \<subseteq> B'\<rbrakk> \<Longrightarrow> A \<lless> B"
  by (auto simp: less_sets_def)

lemma less_sets_imp_disjnt: "A \<lless> B \<Longrightarrow> disjnt A B"
  by (auto simp: less_sets_def disjnt_def)

lemma less_sets_UN1: "less_sets (\<Union>\<A>) B \<longleftrightarrow> (\<forall>A\<in>\<A>. A \<lless> B)"
  by (auto simp: less_sets_def)

lemma less_sets_UN2: "less_sets A (\<Union> \<B>) \<longleftrightarrow> (\<forall>B\<in>\<B>. A \<lless> B)"
  by (auto simp: less_sets_def)

lemma less_sets_Un1: "less_sets (A \<union> A') B \<longleftrightarrow> A \<lless> B \<and> A' \<lless> B"
  by (auto simp: less_sets_def)

lemma less_sets_Un2: "less_sets A (B \<union> B') \<longleftrightarrow> A \<lless> B \<and> A \<lless> B'"
  by (auto simp: less_sets_def)

lemma strict_sorted_imp_less_sets:
  "strict_sorted (as @ bs) \<Longrightarrow> (list.set as) \<lless> (list.set bs)"
  by (simp add: less_sets_def sorted_wrt_append strict_sorted_sorted_wrt)

lemma Sup_nat_less_sets_singleton:
  fixes n::nat
  assumes "Sup T < n" "finite T"
  shows "less_sets T {n}"
  using assms Max_less_iff
  by (auto simp: Sup_nat_def less_sets_def split: if_split_asm)
  
end



