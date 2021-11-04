section \<open>Library additions\<close>

theory Library_Additions
  imports "ZFC_in_HOL.Ordinal_Exp" "HOL-Library.Ramsey" "Nash_Williams.Nash_Williams"

begin

lemma finite_enumerate_Diff_singleton:
  fixes S :: "'a::wellorder set"
  assumes "finite S" and i: "i < card S" "enumerate S i < x"
  shows "enumerate (S - {x}) i = enumerate S i"
  using i
proof (induction i)
  case 0
  have "(LEAST i. i \<in> S \<and> i\<noteq>x) = (LEAST i. i \<in> S)"
  proof (rule Least_equality)
    have "\<exists>t. t \<in> S \<and> t\<noteq>x"
      using 0 \<open>finite S\<close> finite_enumerate_in_set by blast
    then show "(LEAST i. i \<in> S) \<in> S \<and> (LEAST i. i \<in> S) \<noteq> x"
      by (metis "0.prems"(2) LeastI enumerate_0 not_less_Least)
  qed (simp add: Least_le)
  then show ?case
    by (auto simp: enumerate_0)
next
  case (Suc i)
  then have x: "enumerate S i < x"
    by (meson enumerate_step finite_enumerate_step less_trans)
  have cardSx: "Suc i < card (S - {x})" and "i < card S"
    using Suc \<open>finite S\<close> card_Diff_singleton_if finite_enumerate_Ex by fastforce+
  have "(LEAST s. s \<in> S \<and> s\<noteq>x \<and> enumerate (S - {x}) i < s) = (LEAST s. s \<in> S \<and> enumerate S i < s)"
       (is "_ = ?r")
  proof (intro Least_equality conjI)
    show "?r \<in> S"
      by (metis (lifting) LeastI Suc.prems(1) assms(1) finite_enumerate_in_set finite_enumerate_step)
    show "?r \<noteq> x"
      using Suc.prems not_less_Least [of _ "\<lambda>t. t \<in> S \<and> enumerate S i < t"] 
       \<open>finite S\<close> finite_enumerate_in_set finite_enumerate_step by blast
    show "enumerate (S - {x}) i < ?r"
      by (metis (full_types) Suc.IH Suc.prems(1) \<open>i < card S\<close> enumerate_Suc'' enumerate_step finite_enumerate_Suc'' finite_enumerate_step x)
    show "\<And>y. y \<in> S \<and> y \<noteq> x \<and> enumerate (S - {x}) i < y \<Longrightarrow> ?r \<le> y"
      by (simp add: Least_le Suc.IH \<open>i < card S\<close> x)
  qed
  then show ?case
    using Suc assms by (simp add: finite_enumerate_Suc'' cardSx)
qed

lemma hd_lex: "\<lbrakk>hd ms < hd ns; length ms = length ns; ns \<noteq> []\<rbrakk> \<Longrightarrow> (ms, ns) \<in> lex less_than"
  by (metis hd_Cons_tl length_0_conv less_than_iff lexord_cons_cons lexord_lex)

lemma sorted_hd_le:
  assumes "sorted xs" "x \<in> list.set xs"
  shows "hd xs \<le> x"
  using assms by (induction xs) (auto simp: less_imp_le)

lemma sorted_le_last:
  assumes "sorted xs" "x \<in> list.set xs"
  shows "x \<le> last xs"
  using assms by (induction xs) (auto simp: less_imp_le)

lemma hd_list_of:
  assumes "finite A" "A \<noteq> {}"
  shows "hd (sorted_list_of_set A) = Min A" 
proof (rule antisym)
  have "Min A \<in> A"
    by (simp add: assms)
  then show "hd (sorted_list_of_set A) \<le> Min A"
    by (simp add: sorted_hd_le \<open>finite A\<close>)
next
  show "Min A \<le> hd (sorted_list_of_set A)"
    by (metis Min_le assms hd_in_set set_sorted_list_of_set sorted_list_of_set_eq_Nil_iff)
qed

lemma sorted_hd_le_last:
  assumes "sorted xs" "xs \<noteq> []"
  shows "hd xs \<le> last xs"
  using assms by (simp add: sorted_hd_le)

lemma sorted_list_of_set_set_of [simp]: "strict_sorted l \<Longrightarrow> sorted_list_of_set (list.set l) = l"
  by (simp add: strict_sorted_equal)

lemma range_strict_mono_ext:
  fixes f::"nat \<Rightarrow> 'a::linorder"
  assumes eq: "range f = range g"
      and sm: "strict_mono f" "strict_mono g"
    shows "f = g"
proof
  fix n
  show "f n = g n"
  proof (induction n rule: less_induct)
    case (less n)
    obtain x y where xy: "f n = g y" "f x = g n"
      by (metis eq imageE rangeI)
    then have "n = y"
      by (metis (no_types) less.IH neq_iff sm strict_mono_less xy)
    then show ?case using xy by auto
  qed
qed

subsection \<open>Other material\<close>

definition strict_mono_sets :: "['a::order set, 'a::order \<Rightarrow> 'b::order set] \<Rightarrow> bool" where
  "strict_mono_sets A f \<equiv> \<forall>x\<in>A. \<forall>y\<in>A. x < y \<longrightarrow> less_sets (f x) (f y)"

lemma strict_mono_setsD:
  assumes "strict_mono_sets A f" "x < y" "x \<in> A" "y \<in> A"
  shows "less_sets (f x) (f y)"
  using assms by (auto simp: strict_mono_sets_def)

lemma strict_mono_on_o: "\<lbrakk>strict_mono_on r A; strict_mono_on s B; s ` B \<subseteq> A\<rbrakk> \<Longrightarrow> strict_mono_on (r \<circ> s) B"
  by (auto simp: image_subset_iff strict_mono_on_def)

lemma strict_mono_sets_imp_disjoint:
  fixes A :: "'a::linorder set"
  assumes "strict_mono_sets A f"
  shows "pairwise (\<lambda>x y. disjnt (f x) (f y)) A"
  using assms unfolding strict_mono_sets_def pairwise_def
  by (meson antisym_conv3 disjnt_sym less_sets_imp_disjnt)

lemma strict_mono_sets_subset:
  assumes "strict_mono_sets B f" "A \<subseteq> B"
  shows "strict_mono_sets A f"
  using assms by (auto simp: strict_mono_sets_def)

lemma strict_mono_less_sets_Min:
  assumes "strict_mono_sets I f" "finite I" "I \<noteq> {}"
  shows "less_sets (f (Min I)) (\<Union> (f ` (I - {Min I})))"
  using assms by (simp add: strict_mono_sets_def less_sets_UN2 dual_order.strict_iff_order)

lemma pair_less_iff1 [simp]: "((x,y), (x,z)) \<in> pair_less \<longleftrightarrow> y<z"
  by (simp add: pair_less_def)

lemma infinite_finite_Inter:
  assumes "finite \<A>" "\<A>\<noteq>{}" "\<And>A. A \<in> \<A> \<Longrightarrow> infinite A"
    and "\<And>A B. \<lbrakk>A \<in> \<A>; B \<in> \<A>\<rbrakk> \<Longrightarrow> A \<inter> B \<in> \<A>"
  shows "infinite (\<Inter>\<A>)"
  by (simp add: assms finite_Inf_in)

lemma atLeast_less_sets: "\<lbrakk>less_sets A {x}; B \<subseteq> {x..}\<rbrakk> \<Longrightarrow> less_sets A B"
  by (force simp: less_sets_def subset_iff)



subsection \<open>The list-of function\<close>

lemma sorted_list_of_set_insert_cons:
  assumes "finite A" "less_sets {a} A"
  shows "sorted_list_of_set (insert a A) = a # sorted_list_of_set A"
proof -
  have "strict_sorted (a # sorted_list_of_set A)"
    using assms less_setsD by auto
  moreover have "list.set (a # sorted_list_of_set A) = insert a A"
    using assms by force
  moreover have "length (a # sorted_list_of_set A) = card (insert a A)"
    using assms card_insert_if less_setsD by fastforce
  ultimately show ?thesis
    by (metis \<open>finite A\<close> finite_insert sorted_list_of_set_unique)
qed

lemma sorted_list_of_set_Un:
  assumes AB: "less_sets A B" and fin: "finite A" "finite B"
  shows "sorted_list_of_set (A \<union> B) = sorted_list_of_set A @ sorted_list_of_set B"
proof -
  have "strict_sorted (sorted_list_of_set A @ sorted_list_of_set B)"
    using AB unfolding less_sets_def
    by (metis fin set_sorted_list_of_set sorted_wrt_append strict_sorted_list_of_set strict_sorted_sorted_wrt)
  moreover have "card A + card B = card (A \<union> B)"
    using less_sets_imp_disjnt [OF AB]
    by (simp add: assms card_Un_disjoint disjnt_def)
  ultimately show ?thesis
    by (simp add: assms strict_sorted_equal)
qed

lemma sorted_list_of_set_UN_lessThan:
  fixes k::nat
  assumes sm: "strict_mono_sets {..<k} A" and "\<And>i. i < k \<Longrightarrow> finite (A i)"
  shows "sorted_list_of_set (\<Union>i<k. A i) = concat (map (sorted_list_of_set \<circ> A) (sorted_list_of_set {..<k}))"
  using assms
proof (induction k)
  case 0
  then show ?case
    by auto
next
  case (Suc k)
  have ls: "less_sets (\<Union> (A ` {..<k})) (A k)"
    using sm Suc.prems(1) strict_mono_setsD by (force simp: less_sets_UN1)
  have "sorted_list_of_set (\<Union> (A ` {..<Suc k})) = sorted_list_of_set (\<Union> (A ` {..<k}) \<union> A k)"
    by (simp add: Un_commute lessThan_Suc)
  also have "\<dots> = sorted_list_of_set (\<Union> (A ` {..<k})) @ sorted_list_of_set (A k)"
    by (rule sorted_list_of_set_Un) (auto simp: Suc.prems ls)
  also have "\<dots> = concat (map (sorted_list_of_set \<circ> A) (sorted_list_of_set {..<k})) @ sorted_list_of_set (A k)"
    using Suc strict_mono_sets_def by fastforce
  also have "\<dots> = concat (map (sorted_list_of_set \<circ> A) (sorted_list_of_set {..<Suc k}))"
    using strict_mono_sets_def by fastforce
  finally show ?case .
qed

lemma sorted_list_of_set_UN_atMost:
  fixes k::nat
  assumes "strict_mono_sets {..k} A" and "\<And>i. i \<le> k \<Longrightarrow> finite (A i)"
  shows "sorted_list_of_set (\<Union>i\<le>k. A i) = concat (map (sorted_list_of_set \<circ> A) (sorted_list_of_set {..k}))"
  by (metis assms lessThan_Suc_atMost less_Suc_eq_le sorted_list_of_set_UN_lessThan)

subsection \<open>Monotonic enumeration of a countably infinite set\<close>

abbreviation "enum \<equiv> enumerate"

text \<open>Could be generalised to infinite countable sets of any type\<close>
lemma nat_infinite_iff:
  fixes N :: "nat set"
  shows "infinite N \<longleftrightarrow> (\<exists>f::nat\<Rightarrow>nat. N = range f \<and> strict_mono f)"
proof safe
  assume "infinite N"
  then show "\<exists>f. N = range (f::nat \<Rightarrow> nat) \<and> strict_mono f"
    by (metis bij_betw_imp_surj_on bij_enumerate enumerate_mono strict_mono_def)
next
  fix f :: "nat \<Rightarrow> nat"
  assume "strict_mono f" and "N = range f" and "finite (range f)"
  then show False
    using range_inj_infinite strict_mono_imp_inj_on by blast
qed

lemma enum_works:
  fixes N :: "nat set"
  assumes "infinite N"
  shows "N = range (enum N) \<and> strict_mono (enum N)"
  by (metis assms bij_betw_imp_surj_on bij_enumerate enumerate_mono strict_monoI)

lemma range_enum: "range (enum N) = N" and strict_mono_enum: "strict_mono (enum N)"
  if "infinite N" for N :: "nat set"
  using enum_works [OF that] by auto

lemma enum_0_eq_Inf:
  fixes N :: "nat set"
  assumes "infinite N"
  shows "enum N 0 = Inf N"
proof -
  have "enum N 0 \<in> N"
    using assms range_enum by auto
  moreover have "\<And>x. x \<in> N \<Longrightarrow> enum N 0 \<le> x"
    by (metis (mono_tags, hide_lams) assms imageE le0 less_mono_imp_le_mono range_enum strict_monoD strict_mono_enum)
  ultimately show ?thesis
    by (metis cInf_eq_minimum)
qed

lemma enum_works_finite:
  fixes N :: "nat set"
  assumes "finite N"
  shows "N = enum N ` {..<card N} \<and> strict_mono_on (enum N) {..<card N}"
  using assms
  by (metis bij_betw_imp_surj_on finite_bij_enumerate finite_enumerate_mono lessThan_iff strict_mono_onI)

lemma enum_obtain_index_finite:
  fixes N :: "nat set"
  assumes "x \<in> N" "finite N" 
  obtains i where "i < card N" "x = enum N i"
  by (metis \<open>x \<in> N\<close> \<open>finite N\<close> enum_works_finite imageE lessThan_iff)

lemma enum_0_eq_Inf_finite:
  fixes N :: "nat set"
  assumes "finite N" "N \<noteq> {}"
  shows "enum N 0 = Inf N"
proof -
  have "enum N 0 \<in> N"
    by (metis Nat.neq0_conv assms empty_is_image enum_works_finite image_eqI lessThan_empty_iff lessThan_iff)
  moreover have "enum N 0 \<le> x" if "x \<in> N" for x
  proof -
    obtain i where "i < card N" "x = enum N i"
      by (metis \<open>x \<in> N\<close> \<open>finite N\<close> enum_obtain_index_finite)
    with assms show ?thesis
      by (metis Nat.neq0_conv finite_enumerate_mono less_or_eq_imp_le)
  qed
  ultimately show ?thesis
    by (metis cInf_eq_minimum)
qed

lemma greaterThan_less_enum:
  fixes N :: "nat set"
  assumes "N \<subseteq> {x<..}" "infinite N"
  shows "x < enum N i"
  using assms range_enum by fastforce

lemma atLeast_le_enum:
  fixes N :: "nat set"
  assumes "N \<subseteq> {x..}" "infinite N"
  shows "x \<le> enum N i"
  using assms range_enum by fastforce

lemma less_sets_empty1 [simp]: "less_sets {} A" and less_sets_empty2 [simp]: "less_sets A {}"
  by (simp_all add: less_sets_def)

lemma less_sets_singleton1 [simp]: "less_sets {a} A \<longleftrightarrow> (\<forall>x\<in>A. a < x)" 
  and less_sets_singleton2 [simp]: "less_sets A {a} \<longleftrightarrow> (\<forall>x\<in>A. x < a)"
  by (simp_all add: less_sets_def)

lemma less_sets_atMost [simp]: "less_sets {..a} A \<longleftrightarrow> (\<forall>x\<in>A. a < x)" 
  and less_sets_alLeast [simp]: "less_sets A {a..} \<longleftrightarrow> (\<forall>x\<in>A. x < a)"
  by (auto simp: less_sets_def)

lemma less_sets_imp_strict_mono_sets:
  assumes "\<And>i. less_sets (A i) (A (Suc i))" "\<And>i. i>0 \<Longrightarrow> A i \<noteq> {}"
  shows "strict_mono_sets UNIV A"
proof (clarsimp simp: strict_mono_sets_def)
  fix i j::nat
  assume "i < j"
  then show "less_sets (A i) (A j)"
  proof (induction "j-i" arbitrary: i j)
    case (Suc x)
    then show ?case
      by (metis Suc_diff_Suc Suc_inject Suc_mono assms less_Suc_eq less_sets_trans zero_less_Suc)
  qed auto
qed

lemma less_sets_Suc_Max:  
  assumes "finite A"
  shows "less_sets A {Suc (Max A)..}"
proof (cases "A = {}")
  case False
  then show ?thesis
    by (simp add: assms less_Suc_eq_le)
qed auto

lemma infinite_nat_greaterThan:
  fixes m::nat
  assumes "infinite N"
  shows "infinite (N \<inter> {m<..})"
proof -
  have "N \<subseteq> -{m<..} \<union> (N \<inter> {m<..})"
    by blast
  moreover have "finite (-{m<..})"
    by simp
  ultimately show ?thesis
    using assms finite_subset by blast
qed

end

    

