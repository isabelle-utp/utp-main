
text \<open>Authors: Anthony Bordg and Lawrence Paulson,
with some contributions from Wenda Li\<close>

theory Topological_Space
  imports Complex_Main
          "Jacobson_Basic_Algebra.Set_Theory"
          Set_Extras

begin

section \<open>Topological Spaces\<close>

locale topological_space = fixes S :: "'a set" and is_open :: "'a set \<Rightarrow> bool"
  assumes open_space [simp, intro]: "is_open S" and open_empty [simp, intro]: "is_open {}"
    and open_imp_subset: "is_open U \<Longrightarrow> U \<subseteq> S"
    and open_inter [intro]: "\<lbrakk>is_open U; is_open V\<rbrakk> \<Longrightarrow> is_open (U \<inter> V)"
    and open_union [intro]: "\<And>F::('a set) set. (\<And>x. x \<in> F \<Longrightarrow> is_open x) \<Longrightarrow> is_open (\<Union>x\<in>F. x)"

begin

definition is_closed :: "'a set \<Rightarrow> bool"
  where "is_closed U \<equiv> U \<subseteq> S \<and> is_open (S - U)"

definition neighborhoods:: "'a \<Rightarrow> ('a set) set"
  where "neighborhoods x \<equiv> {U. is_open U \<and> x \<in> U}"

text \<open>Note that by a neighborhood we mean what some authors call an open neighborhood.\<close>

lemma open_union' [intro]: "\<And>F::('a set) set. (\<And>x. x \<in> F \<Longrightarrow> is_open x) \<Longrightarrow> is_open (\<Union>F)"
  using open_union by auto

lemma open_preimage_identity [simp]: "is_open B \<Longrightarrow> identity S \<^sup>\<inverse> S B = B"
  by (metis inf.orderE open_imp_subset preimage_identity_self)


definition is_connected:: "bool" where
"is_connected \<equiv> \<not> (\<exists>U V. is_open U \<and> is_open V \<and> (U \<noteq> {}) \<and> (V \<noteq> {}) \<and> (U \<inter> V = {}) \<and> (U \<union> V = S))"

definition is_hausdorff:: "bool" where
"is_hausdorff \<equiv>
\<forall>x y. (x \<in> S \<and> y \<in> S \<and> x \<noteq> y) \<longrightarrow> (\<exists>U V. U \<in> neighborhoods x \<and> V \<in> neighborhoods y \<and> U \<inter> V = {})"

end (* topological_space *)

text \<open>T2 spaces are also known as Hausdorff spaces.\<close>

locale t2_space = topological_space +
  assumes hausdorff: "is_hausdorff"


subsection \<open>Topological Basis\<close>

inductive generated_topology :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool"
    for S :: "'a set" and B :: "'a set set"
  where
    UNIV: "generated_topology S B S"
  | Int: "generated_topology S B (U \<inter> V)"
            if "generated_topology S B U" and "generated_topology S B V"
  | UN: "generated_topology S B (\<Union>K)" if "(\<And>U. U \<in> K \<Longrightarrow> generated_topology S B U)"
  | Basis: "generated_topology S B b" if "b \<in> B \<and> b \<subseteq> S"

lemma generated_topology_empty [simp]: "generated_topology S B {}"
  by (metis UN Union_empty empty_iff)

lemma generated_topology_subset: "generated_topology S B U \<Longrightarrow> U \<subseteq> S"
  by (induct rule:generated_topology.induct) auto

lemma generated_topology_is_topology:
  fixes S:: "'a set" and B:: "'a set set"
  shows "topological_space S (generated_topology S B)"
  by (simp add: Int UN UNIV generated_topology_subset topological_space_def)


subsection \<open>Covers\<close>

locale cover_of_subset =
  fixes X:: "'a set" and U:: "'a set" and index:: "real set" and cover:: "real \<Rightarrow> 'a set"
(* We use real instead of index::"'b set" otherwise we get some troubles with locale sheaf_of_rings
in Comm_Ring_Theory.thy *)
  assumes is_subset: "U \<subseteq> X" and are_subsets: "\<And>i. i \<in> index \<Longrightarrow> cover i \<subseteq> X"
and covering: "U \<subseteq> (\<Union>i\<in>index. cover i)"
begin

lemma
  assumes "x \<in> U"
  shows "\<exists>i\<in>index. x \<in> cover i"
  using assms covering by auto

definition select_index:: "'a \<Rightarrow> real"
  where "select_index x \<equiv> SOME i. i \<in> index \<and> x \<in> cover i"

lemma cover_of_select_index:
  assumes "x \<in> U"
  shows "x \<in> cover (select_index x)"
  using assms by (metis (mono_tags, lifting) UN_iff covering select_index_def someI_ex subset_iff)

lemma select_index_belongs:
  assumes "x \<in> U"
  shows "select_index x \<in> index"
  using assms by (metis (full_types, lifting) UN_iff covering in_mono select_index_def tfl_some)

end (* cover_of_subset *)

locale open_cover_of_subset = topological_space X is_open + cover_of_subset X U I C
  for X and is_open and U and I and C +
  assumes are_open_subspaces: "\<And>i. i\<in>I \<Longrightarrow> is_open (C i)"
begin

lemma cover_of_select_index_is_open:
  assumes "x \<in> U"
  shows "is_open (C (select_index x))"
  using assms by (simp add: are_open_subspaces select_index_belongs)

end (* open_cover_of_subset *)

locale open_cover_of_open_subset = open_cover_of_subset X is_open U I C
  for X and is_open and U and I and C +
  assumes is_open_subset: "is_open U"


subsection \<open>Induced Topology\<close>

locale ind_topology = topological_space X is_open for X and is_open +
  fixes S:: "'a set"
  assumes is_subset: "S \<subseteq> X"
begin

definition ind_is_open:: "'a set \<Rightarrow> bool"
  where "ind_is_open U \<equiv> U \<subseteq> S \<and> (\<exists>V. V \<subseteq> X \<and> is_open V \<and> U = S \<inter> V)"

lemma ind_is_open_S [iff]: "ind_is_open S"
    by (metis ind_is_open_def inf.orderE is_subset open_space order_refl)

lemma ind_is_open_empty [iff]: "ind_is_open {}"
    using ind_is_open_def by auto

lemma ind_space_is_top_space:
  shows "topological_space S (ind_is_open)"
proof
  fix U V
  assume "ind_is_open U" then obtain UX where "UX \<subseteq> X" "is_open UX" "U = S \<inter> UX"
    using ind_is_open_def by auto
  moreover
  assume "ind_is_open V" then obtain VX where "VX \<subseteq> X" "is_open VX" "V = S \<inter> VX"
    using ind_is_open_def by auto
  ultimately have "is_open (UX \<inter> VX) \<and> (U \<inter> V = S \<inter> (UX \<inter> VX))" using open_inter by auto
  then show "ind_is_open (U \<inter> V)"
    by (metis \<open>UX \<subseteq> X\<close> ind_is_open_def le_infI1 subset_refl)
next
  fix F
  assume F: "\<And>x. x \<in> F \<Longrightarrow> ind_is_open x"
  obtain F' where F': "\<And>x. x \<in> F \<and> ind_is_open x \<Longrightarrow> is_open (F' x) \<and> x = S \<inter> (F' x)"
    using ind_is_open_def by metis
  have "is_open (\<Union> (F' ` F))"
    by (metis (mono_tags, lifting) F F' imageE image_ident open_union)
  moreover
  have "(\<Union>x\<in>F. x) = S \<inter> \<Union> (F' ` F)"
    using F' \<open>\<And>x. x \<in> F \<Longrightarrow> ind_is_open x\<close> by fastforce
  ultimately show "ind_is_open (\<Union>x\<in>F. x)"
    by (metis ind_is_open_def inf_sup_ord(1) open_imp_subset)
next
  show "\<And>U. ind_is_open U \<Longrightarrow> U \<subseteq> S"
    by (simp add: ind_is_open_def)
qed auto

lemma is_open_from_ind_is_open:
  assumes "is_open S" and "ind_is_open U"
  shows "is_open U"
  using assms open_inter ind_is_open_def is_subset by auto

lemma open_cover_from_ind_open_cover:
  assumes "is_open S" and "open_cover_of_open_subset S ind_is_open U I C"
  shows "open_cover_of_open_subset X is_open U I C"
proof
  show "is_open U"
    using assms is_open_from_ind_is_open open_cover_of_open_subset.is_open_subset by blast
  show "\<And>i. i \<in> I \<Longrightarrow> is_open (C i)"
    using assms is_open_from_ind_is_open open_cover_of_open_subset_def open_cover_of_subset.are_open_subspaces by blast
  show "\<And>i. i \<in> I \<Longrightarrow> C i \<subseteq> X"
    using assms(2) is_subset
    by (meson cover_of_subset_def open_cover_of_open_subset_def open_cover_of_subset_def subset_trans)
  show "U \<subseteq> X"
    by (simp add: \<open>is_open U\<close> open_imp_subset)
  show "U \<subseteq> \<Union> (C ` I)"
    by (meson assms(2) cover_of_subset_def open_cover_of_open_subset_def open_cover_of_subset_def)
qed

end (* induced topology *)

lemma (in topological_space) ind_topology_is_open_self [iff]: "ind_topology S is_open S"
  by (simp add: ind_topology_axioms_def ind_topology_def topological_space_axioms)

lemma (in topological_space) ind_topology_is_open_empty [iff]: "ind_topology S is_open {}"
  by (simp add: ind_topology_axioms_def ind_topology_def topological_space_axioms)

lemma (in topological_space) ind_is_open_iff_open:
  shows "ind_topology.ind_is_open S is_open S U \<longleftrightarrow> is_open U \<and> U \<subseteq> S"
  by (metis ind_topology.ind_is_open_def ind_topology_is_open_self inf.absorb_iff2)

subsection \<open>Continuous Maps\<close>

locale continuous_map = source: topological_space S is_open + target: topological_space S' is_open'
+ map f S S'
  for S and is_open and S' and is_open' and f +
  assumes is_continuous: "\<And>U. is_open' U \<Longrightarrow> is_open (f\<^sup>\<inverse> S U)"
begin

lemma open_cover_of_open_subset_from_target_to_source:
  assumes "open_cover_of_open_subset S' is_open' U I C"
  shows "open_cover_of_open_subset S is_open (f\<^sup>\<inverse> S U) I (\<lambda>i. f\<^sup>\<inverse> S (C i))"
proof
  show "f \<^sup>\<inverse> S U \<subseteq> S" by simp
  show "f \<^sup>\<inverse> S (C i) \<subseteq> S" if "i \<in> I" for i
    using that by simp
  show "is_open (f \<^sup>\<inverse> S U)"
    by (meson assms is_continuous open_cover_of_open_subset.is_open_subset)
  show "\<And>i. i \<in> I \<Longrightarrow> is_open (f \<^sup>\<inverse> S (C i))"
    by (meson assms is_continuous open_cover_of_open_subset_def open_cover_of_subset.are_open_subspaces)
  show "f \<^sup>\<inverse> S U \<subseteq> (\<Union>i\<in>I. f \<^sup>\<inverse> S (C i))"
    using assms unfolding open_cover_of_open_subset_def cover_of_subset_def open_cover_of_subset_def
    by blast
qed

end (* continuous map *)


subsection \<open>Homeomorphisms\<close>

text \<open>The topological isomorphisms between topological spaces are called homeomorphisms.\<close>

locale homeomorphism =
  continuous_map + bijective_map f S S' +
  continuous_map S' is_open' S is_open "inverse_map f S S'"

lemma (in topological_space) id_is_homeomorphism:
  shows "homeomorphism S is_open S is_open (identity S)"
proof
  show "inverse_map (identity S) S S \<in> S \<rightarrow>\<^sub>E S"
    by (simp add: inv_into_into inverse_map_def)
qed (auto simp: open_inter bij_betwI')


subsection \<open>Topological Filters\<close> (* Imported from HOL.Topological_Spaces *)

definition (in topological_space) nhds :: "'a \<Rightarrow> 'a filter"
  where "nhds a = (INF S\<in>{S. is_open S \<and> a \<in> S}. principal S)"

abbreviation (in topological_space)
  tendsto :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b filter \<Rightarrow> bool"  (infixr "\<longlongrightarrow>" 55)
  where "(f \<longlongrightarrow> l) F \<equiv> filterlim f (nhds l) F"

definition (in t2_space) Lim :: "'f filter \<Rightarrow> ('f \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "Lim A f = (THE l. (f \<longlongrightarrow> l) A)"

end
