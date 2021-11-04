(* Title: Group_Divisible_Designs.thy
   Author: Chelsea Edmonds
*)

section \<open>Group Divisible Designs\<close>
text \<open>Definitions in this section taken from the handbook \cite{colbournHandbookCombinatorialDesigns2007}
and Stinson \cite{stinsonCombinatorialDesignsConstructions2004}\<close>
theory Group_Divisible_Designs imports Resolvable_Designs
begin

subsection \<open>Group design\<close>
text \<open>We define a group design to have an additional paramater $G$ which is a partition on the point 
set $V$. This is not defined in the handbook, but is a precursor to GDD's without index constraints\<close>

locale group_design = proper_design + 
  fixes groups :: "'a set set" ("\<G>")
  assumes group_partitions: "partition_on \<V> \<G>"
  assumes groups_size: "card \<G> > 1" 
begin

lemma groups_not_empty: "\<G> \<noteq> {}"
  using groups_size by auto

lemma num_groups_lt_points: "card \<G> \<le> \<v>"
  by (simp add: partition_on_le_set_elements finite_sets group_partitions) 

lemma groups_disjoint: "disjoint \<G>"
  using group_partitions partition_onD2 by auto

lemma groups_disjoint_pairwise: "G1 \<in> \<G> \<Longrightarrow> G2 \<in> \<G> \<Longrightarrow> G1 \<noteq> G2 \<Longrightarrow> disjnt G1 G2"
  using group_partitions partition_onD2 pairwiseD by fastforce 

lemma point_in_one_group: "x \<in> G1 \<Longrightarrow> G1 \<in> \<G> \<Longrightarrow> G2 \<in> \<G> \<Longrightarrow> G1 \<noteq> G2 \<Longrightarrow> x \<notin> G2"
  using groups_disjoint_pairwise by (simp add: disjnt_iff) 

lemma point_has_unique_group: "x \<in> \<V> \<Longrightarrow> \<exists>!G. x \<in> G \<and> G \<in> \<G>"
  using partition_on_partition_on_unique group_partitions
  by fastforce 

lemma rep_number_point_group_one: 
  assumes "x \<in> \<V>"
  shows  "card {g \<in> \<G> . x \<in> g} = 1" 
proof -
  obtain g' where "g' \<in> \<G>" and "x \<in> g'"
    using assms point_has_unique_group by blast 
  then have "{g \<in> \<G> . x \<in> g} = {g'}"
    using  group_partitions partition_onD4 by force 
  thus ?thesis
    by simp 
qed

lemma point_in_group: "G \<in> \<G> \<Longrightarrow> x \<in> G \<Longrightarrow> x \<in> \<V>"
  using group_partitions partition_onD1 by auto 

lemma point_subset_in_group: "G \<in> \<G> \<Longrightarrow> ps \<subseteq> G \<Longrightarrow> ps \<subseteq> \<V>"
  using point_in_group by auto

lemma group_subset_point_subset: "G \<in> \<G> \<Longrightarrow> G' \<subseteq> G \<Longrightarrow> ps \<subseteq> G' \<Longrightarrow> ps \<subseteq> \<V>"
  using point_subset_in_group by auto

lemma groups_finite: "finite \<G>"
  using finite_elements finite_sets group_partitions by auto

lemma group_elements_finite: "G \<in> \<G> \<Longrightarrow> finite G"
  using groups_finite finite_sets group_partitions
  by (meson finite_subset point_in_group subset_iff)

lemma v_equals_sum_group_sizes: "\<v> = (\<Sum>G \<in> \<G>. card G)"
  using group_partitions groups_disjoint partition_onD1 card_Union_disjoint group_elements_finite 
  by fastforce 

lemma gdd_min_v: "\<v> \<ge> 2"
proof - 
  have assm: "card \<G> \<ge> 2" using groups_size by simp
  then have "\<And> G . G \<in> \<G> \<Longrightarrow> G \<noteq> {}" using partition_onD3 group_partitions by auto
  then have "\<And> G . G \<in> \<G> \<Longrightarrow> card G \<ge> 1"
    using group_elements_finite card_0_eq by fastforce 
  then have " (\<Sum>G \<in> \<G>. card G) \<ge> 2" using assm
    using sum_mono by force 
  thus ?thesis using v_equals_sum_group_sizes
    by linarith 
qed

lemma min_group_size: "G \<in> \<G> \<Longrightarrow> card G \<ge> 1"
  using partition_onD3 group_partitions
  using group_elements_finite not_le_imp_less by fastforce  

lemma group_size_lt_v: 
  assumes "G \<in> \<G>"
  shows "card G < \<v>"
proof - 
  have "(\<Sum>G' \<in> \<G>. card G') = \<v>" using gdd_min_v v_equals_sum_group_sizes
    by linarith 
  then have split_sum: "card G + (\<Sum>G' \<in> (\<G> - {G}). card G') = \<v>" using assms sum.remove
    by (metis groups_finite v_equals_sum_group_sizes) 
  have "card (\<G> - {G}) \<ge> 1" using groups_size
    by (simp add: assms groups_finite)
  then obtain G' where gin: "G' \<in> (\<G> - {G})"
    by (meson elem_exists_non_empty_set less_le_trans less_numeral_extra(1)) 
  then have "card G' \<ge> 1" using min_group_size by auto 
  then have "(\<Sum>G' \<in> (\<G> - {G}). card G') \<ge> 1"
    by (metis gin finite_Diff groups_finite leI less_one sum_eq_0_iff) 
  thus ?thesis using split_sum
    by linarith
qed

subsubsection \<open>Group Type\<close>

text \<open>GDD's have a "type", which is defined by a sequence of group sizes $g_i$, and the number 
of groups of that size $a_i$: $g_1^{a_1}g2^{a_2}...g_n^{a_n}$\<close>
definition group_sizes :: "nat set" where
"group_sizes \<equiv> {card G | G . G \<in> \<G>}"

definition groups_of_size :: "nat \<Rightarrow> nat" where
"groups_of_size g \<equiv> card { G \<in> \<G> . card G = g }"

definition group_type :: "(nat \<times> nat) set" where
"group_type \<equiv> {(g, groups_of_size g) | g . g \<in> group_sizes }"

lemma group_sizes_min: "x \<in> group_sizes \<Longrightarrow> x \<ge> 1 " 
  unfolding group_sizes_def using min_group_size group_size_lt_v by auto 

lemma group_sizes_max: "x \<in> group_sizes \<Longrightarrow> x < \<v> " 
  unfolding group_sizes_def using min_group_size group_size_lt_v by auto 

lemma group_size_implies_group_existance: "x \<in> group_sizes \<Longrightarrow> \<exists>G. G \<in> \<G> \<and> card G = x"
  unfolding group_sizes_def by auto

lemma groups_of_size_zero: "groups_of_size 0 = 0"
proof -
  have empty: "{G \<in> \<G> . card G = 0} = {}" using min_group_size
    by fastforce 
  thus ?thesis unfolding groups_of_size_def
    by (simp add: empty) 
qed

lemma groups_of_size_max: 
  assumes "g \<ge> \<v>"
  shows "groups_of_size g = 0"
proof -
  have "{G \<in> \<G> . card G = g} = {}" using group_size_lt_v assms by fastforce 
  thus ?thesis unfolding groups_of_size_def
    by (simp add: \<open>{G \<in> \<G>. card G = g} = {}\<close>) 
qed

lemma group_type_contained_sizes: "(g, a) \<in> group_type \<Longrightarrow> g \<in> group_sizes" 
  unfolding group_type_def by simp

lemma group_type_contained_count: "(g, a) \<in> group_type \<Longrightarrow> card {G \<in> \<G> . card G = g} = a"
  unfolding group_type_def groups_of_size_def by simp

lemma group_card_in_sizes: "g \<in> \<G> \<Longrightarrow> card g \<in> group_sizes"
  unfolding group_sizes_def by auto

lemma group_card_non_zero_groups_of_size_min: 
  assumes "g \<in> \<G>"
  assumes "card g = a"
  shows "groups_of_size a \<ge> 1"
proof - 
  have "g \<in> {G \<in> \<G> . card G = a}" using assms by simp
  then have "{G \<in> \<G> . card G = a} \<noteq> {}" by auto
  then have "card {G \<in> \<G> . card G = a} \<noteq> 0"
    by (simp add: groups_finite) 
  thus ?thesis unfolding groups_of_size_def by simp 
qed

lemma elem_in_group_sizes_min_of_size: 
  assumes "a \<in> group_sizes"
  shows "groups_of_size a \<ge> 1"
  using assms group_card_non_zero_groups_of_size_min group_size_implies_group_existance by blast

lemma group_card_non_zero_groups_of_size_max: 
  shows "groups_of_size a \<le> \<v>"
proof -
  have "{G \<in> \<G> . card G = a} \<subseteq> \<G>" by simp
  then have "card {G \<in> \<G> . card G = a} \<le> card \<G>"
    by (simp add: card_mono groups_finite)
  thus ?thesis
    using groups_of_size_def num_groups_lt_points by auto 
qed

lemma group_card_in_type: "g \<in> \<G> \<Longrightarrow> \<exists> x . (card g, x) \<in> group_type \<and> x \<ge> 1"
  unfolding group_type_def using group_card_non_zero_groups_of_size_min
  by (simp add: group_card_in_sizes)

lemma partition_groups_on_size: "partition_on \<G> {{ G \<in> \<G> . card G = g } | g . g \<in> group_sizes}"
proof (intro partition_onI, auto)
  fix g
  assume a1: "g \<in> group_sizes"
  assume " \<forall>x. x \<in> \<G> \<longrightarrow> card x \<noteq> g"
  then show False using a1 group_size_implies_group_existance by auto 
next
  fix x
  assume "x \<in> \<G>"
  then show "\<exists>xa. (\<exists>g. xa = {G \<in> \<G>. card G = g} \<and> g \<in> group_sizes) \<and> x \<in> xa"
    using  group_card_in_sizes by auto 
qed

lemma group_size_partition_covers_points: "\<Union>(\<Union>{{ G \<in> \<G> . card G = g } | g . g \<in> group_sizes}) = \<V>"
  by (metis (no_types, lifting) group_partitions partition_groups_on_size partition_onD1)

lemma groups_of_size_alt_def_count: "groups_of_size g = count {# card G . G \<in># mset_set \<G> #} g" 
proof -
  have a: "groups_of_size g =  card { G \<in> \<G> . card G = g }" unfolding groups_of_size_def by simp
  then have "groups_of_size g =  size {# G \<in># (mset_set \<G>) . card G = g #}"
    using groups_finite by auto 
  then have size_repr: "groups_of_size g =  size {# x \<in># {# card G . G \<in># mset_set \<G> #} . x = g #}"
    using groups_finite by (simp add: filter_mset_image_mset)
  have "group_sizes = set_mset ({# card G . G \<in># mset_set \<G> #})" 
    using group_sizes_def groups_finite by auto 
  thus ?thesis using size_repr by (simp add: count_size_set_repr) 
qed

lemma v_sum_type_rep: "\<v> = (\<Sum> g \<in> group_sizes . g * (groups_of_size g))"
proof -
  have gs: "set_mset {# card G . G \<in># mset_set \<G> #} = group_sizes" 
    unfolding group_sizes_def using groups_finite by auto 
  have "\<v> = card (\<Union>(\<Union>{{ G \<in> \<G> . card G = g } | g . g \<in> group_sizes}))"
    using group_size_partition_covers_points by simp
  have v1: "\<v> = (\<Sum>x \<in># {# card G . G \<in># mset_set \<G> #}. x)"
    by (simp add: sum_unfold_sum_mset v_equals_sum_group_sizes)
  then have "\<v> = (\<Sum>x \<in> set_mset {# card G . G \<in># mset_set \<G> #} . x * (count {# card G . G \<in># mset_set \<G> #} x))" 
    using mset_set_size_card_count by (simp add: v1)
  thus ?thesis using gs groups_of_size_alt_def_count by auto 
qed

end

subsubsection \<open>Uniform Group designs\<close>
text \<open>A group design requiring all groups are the same size\<close>
locale uniform_group_design = group_design + 
  fixes u_group_size :: nat ("\<m>")
  assumes uniform_groups: "G \<in> \<G> \<Longrightarrow> card G = \<m>"

begin

lemma m_positive: "\<m> \<ge> 1"
proof -
  obtain G where "G \<in> \<G>" using groups_size elem_exists_non_empty_set gr_implies_not_zero by blast 
  thus ?thesis using uniform_groups min_group_size by fastforce
qed

lemma uniform_groups_alt: " \<forall> G \<in> \<G> . card G = \<m>"
  using uniform_groups by blast 

lemma uniform_groups_group_sizes: "group_sizes = {\<m>}"
  using design_points_nempty group_card_in_sizes group_size_implies_group_existance 
    point_has_unique_group uniform_groups_alt by force

lemma uniform_groups_group_size_singleton: "is_singleton (group_sizes)"
  using uniform_groups_group_sizes by auto

lemma set_filter_eq_P_forall:"\<forall> x \<in> X . P x \<Longrightarrow> Set.filter P X = X"
  by (simp add: Collect_conj_eq Int_absorb2 Set.filter_def subsetI)

lemma uniform_groups_groups_of_size_m: "groups_of_size \<m> = card \<G>"
proof(simp add: groups_of_size_def)
  have "{G \<in> \<G>. card G = \<m>} = \<G>" using uniform_groups_alt set_filter_eq_P_forall by auto
  thus "card {G \<in> \<G>. card G = \<m>} = card \<G>" by simp
qed

lemma uniform_groups_of_size_not_m: "x \<noteq> \<m> \<Longrightarrow> groups_of_size x = 0"
  by (simp add: groups_of_size_def card_eq_0_iff uniform_groups)

end

subsection \<open>GDD\<close>
text \<open>A GDD extends a group design with an additional index parameter.
Each pair of elements must occur either \Lambda times if in diff groups, or 0 times if in the same 
group\<close>

locale GDD = group_design + 
  fixes index :: int ("\<Lambda>")
  assumes index_ge_1: "\<Lambda> \<ge> 1"
  assumes index_together: "G \<in> \<G> \<Longrightarrow> x \<in> G \<Longrightarrow> y \<in> G \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<B> index {x, y} = 0"
  assumes index_distinct: "G1 \<in> \<G> \<Longrightarrow> G2 \<in> \<G> \<Longrightarrow> G1 \<noteq> G2 \<Longrightarrow> x \<in> G1 \<Longrightarrow> y \<in> G2 \<Longrightarrow> 
    \<B> index {x, y} = \<Lambda>"
begin

lemma points_sep_groups_ne: "G1 \<in> \<G> \<Longrightarrow> G2 \<in> \<G> \<Longrightarrow> G1 \<noteq> G2 \<Longrightarrow> x \<in> G1 \<Longrightarrow> y \<in> G2 \<Longrightarrow> x \<noteq> y"
  by (meson point_in_one_group)

lemma index_together_alt_ss: "ps \<subseteq> G \<Longrightarrow> G \<in> \<G> \<Longrightarrow> card ps = 2 \<Longrightarrow> \<B> index ps = 0"
  using index_together by (metis card_2_iff insert_subset) 

lemma index_distinct_alt_ss: "ps \<subseteq> \<V> \<Longrightarrow> card ps = 2 \<Longrightarrow> (\<And> G . G \<in> \<G> \<Longrightarrow> \<not> ps \<subseteq> G) \<Longrightarrow> 
    \<B> index ps = \<Lambda>"
  using index_distinct by (metis card_2_iff empty_subsetI insert_subset point_has_unique_group) 

lemma gdd_index_options: "ps \<subseteq> \<V> \<Longrightarrow> card ps = 2 \<Longrightarrow> \<B> index ps = 0 \<or> \<B> index ps = \<Lambda>"
  using index_distinct_alt_ss index_together_alt_ss by blast

lemma index_zero_implies_same_group: "ps \<subseteq> \<V> \<Longrightarrow> card ps = 2 \<Longrightarrow> \<B> index ps = 0 \<Longrightarrow> 
    \<exists> G \<in> \<G> . ps \<subseteq> G" using index_distinct_alt_ss gr_implies_not_zero
  by (metis index_ge_1 less_one of_nat_0 of_nat_1 of_nat_le_0_iff)

lemma index_zero_implies_same_group_unique: "ps \<subseteq> \<V> \<Longrightarrow> card ps = 2 \<Longrightarrow> \<B> index ps = 0 \<Longrightarrow> 
    \<exists>! G \<in> \<G> . ps \<subseteq> G" 
  by (meson GDD.index_zero_implies_same_group GDD_axioms card_2_iff' group_design.point_in_one_group 
      group_design_axioms in_mono)

lemma index_not_zero_impl_diff_group: "ps \<subseteq> \<V> \<Longrightarrow> card ps = 2 \<Longrightarrow> \<B> index ps = \<Lambda> \<Longrightarrow>  
    (\<And> G . G \<in> \<G> \<Longrightarrow> \<not> ps \<subseteq> G)"
  using index_ge_1 index_together_alt_ss by auto

lemma index_zero_implies_one_group: 
  assumes "ps \<subseteq> \<V>" 
  and "card ps = 2" 
  and "\<B> index ps = 0" 
  shows "size {#b \<in>#  mset_set \<G> . ps \<subseteq> b#} = 1"
proof -
  obtain G where ging: "G \<in> \<G>" and psin: "ps \<subseteq> G" 
    using index_zero_implies_same_group groups_size assms by blast
  then have unique: "\<And> G2 . G2 \<in> \<G> \<Longrightarrow> G \<noteq> G2 \<Longrightarrow> \<not> ps \<subseteq> G2" 
    using index_zero_implies_same_group_unique by (metis assms) 
  have "\<And> G'. G' \<in> \<G> \<longleftrightarrow> G' \<in># mset_set \<G>"
    by (simp add: groups_finite) 
  then have eq_mset: "{#b \<in>#  mset_set \<G> . ps \<subseteq> b#} = mset_set {b \<in> \<G> . ps \<subseteq> b}"
    using filter_mset_mset_set groups_finite by blast 
  then have "{b \<in> \<G> . ps \<subseteq> b} = {G}" using unique psin
    by (smt Collect_cong ging singleton_conv)
  thus ?thesis by (simp add: eq_mset) 
qed

lemma index_distinct_group_num_alt_def: "ps \<subseteq> \<V> \<Longrightarrow> card ps = 2 \<Longrightarrow> 
    size {#b \<in>#  mset_set \<G> . ps \<subseteq> b#} = 0 \<Longrightarrow> \<B> index ps = \<Lambda>"
  by (metis gdd_index_options index_zero_implies_one_group numeral_One zero_neq_numeral)

lemma index_non_zero_implies_no_group: 
  assumes "ps \<subseteq> \<V>" 
    and  "card ps = 2" 
    and "\<B> index ps = \<Lambda>" 
  shows "size {#b \<in>#  mset_set \<G> . ps \<subseteq> b#} = 0"
proof -
  have "\<And> G . G \<in> \<G> \<Longrightarrow>  \<not> ps \<subseteq> G" using index_not_zero_impl_diff_group assms by simp
  then have "{#b \<in>#  mset_set \<G> . ps \<subseteq> b#} = {#}"
    using filter_mset_empty_if_finite_and_filter_set_empty by force
  thus ?thesis by simp
qed

lemma gdd_index_non_zero_iff: "ps \<subseteq> \<V> \<Longrightarrow> card ps = 2 \<Longrightarrow> 
    \<B> index ps = \<Lambda> \<longleftrightarrow> size {#b \<in>#  mset_set \<G> . ps \<subseteq> b#} = 0"
  using index_non_zero_implies_no_group index_distinct_group_num_alt_def by auto

lemma gdd_index_zero_iff: "ps \<subseteq> \<V> \<Longrightarrow> card ps = 2 \<Longrightarrow> 
    \<B> index ps = 0 \<longleftrightarrow> size {#b \<in>#  mset_set \<G> . ps \<subseteq> b#} = 1"
  apply (auto simp add: index_zero_implies_one_group)
  by (metis GDD.gdd_index_options GDD_axioms index_non_zero_implies_no_group old.nat.distinct(2))

lemma points_index_upper_bound: "ps \<subseteq> \<V> \<Longrightarrow> card ps = 2 \<Longrightarrow> \<B> index ps \<le> \<Lambda>"
  using gdd_index_options index_ge_1
  by (metis int_one_le_iff_zero_less le_refl of_nat_0 of_nat_0_le_iff of_nat_le_iff zero_less_imp_eq_int) 

lemma index_1_imp_mult_1: 
  assumes "\<Lambda> = 1"
  assumes "bl \<in># \<B>"
  assumes "card bl \<ge> 2"
  shows "multiplicity bl = 1"
proof (rule ccontr)
  assume "\<not> (multiplicity bl = 1)"
  then have "multiplicity bl \<noteq> 1" and "multiplicity bl \<noteq> 0" using assms by simp_all 
  then have m: "multiplicity bl \<ge> 2" by linarith
  obtain ps where ps: "ps \<subseteq> bl \<and> card ps = 2"
    using nat_int_comparison(3) obtain_subset_with_card_n by (metis assms(3))  
  then have "\<B> index ps \<ge> 2"
    using m points_index_count_min ps by blast
  then show False using assms index_distinct ps antisym_conv2 not_numeral_less_zero 
      numeral_le_one_iff points_index_ps_nin semiring_norm(69) zero_neq_numeral
    by (metis gdd_index_options int_int_eq int_ops(2))
qed

lemma simple_if_block_size_gt_2:
  assumes "\<And> bl . card bl \<ge> 2"
  assumes "\<Lambda> = 1"
  shows "simple_design \<V> \<B>"
  using index_1_imp_mult_1 assms apply (unfold_locales)
  by (metis card.empty not_numeral_le_zero) 

end

subsubsection \<open>Sub types of GDD's\<close>

text \<open>In literature, a GDD is usually defined in a number of different ways, 
including factors such as block size limitations\<close>
locale K_\<Lambda>_GDD = K_block_design + GDD

locale k_\<Lambda>_GDD = block_design + GDD

sublocale k_\<Lambda>_GDD \<subseteq> K_\<Lambda>_GDD \<V> \<B> "{\<k>}" \<G> \<Lambda>
  by (unfold_locales)

locale K_GDD = K_\<Lambda>_GDD \<V> \<B> \<K> \<G> 1 
  for point_set ("\<V>") and block_collection ("\<B>") and sizes ("\<K>") and groups ("\<G>")

locale k_GDD = k_\<Lambda>_GDD \<V> \<B> \<k> \<G> 1 
  for point_set ("\<V>") and block_collection ("\<B>") and u_block_size ("\<k>") and groups ("\<G>")

sublocale k_GDD \<subseteq> K_GDD \<V> \<B> "{\<k>}" \<G>
  by (unfold_locales)

lemma (in K_GDD) multiplicity_1:  "bl \<in># \<B> \<Longrightarrow> card bl \<ge> 2 \<Longrightarrow> multiplicity bl = 1"
  using index_1_imp_mult_1 by simp

locale RGDD = GDD + resolvable_design

subsection \<open>GDD and PBD Constructions\<close>
text \<open>GDD's are commonly studied alongside PBD's (pairwise balanced designs). Many constructions
have been developed for designs to create a GDD from a PBD and vice versa. In particular, 
Wilsons Construction is a well known construction, which is formalised in this section. It
should be noted that many of the more basic constructions in this section are often stated without
proof/all the necessary assumptions in textbooks/course notes.\<close>

context GDD
begin

subsubsection \<open>GDD Delete Point construction\<close>
lemma delete_point_index_zero: 
  assumes "G \<in> {g - {x} |g. g \<in> \<G> \<and> g \<noteq> {x}}"
  and "y \<in> G" and "z \<in> G" and "z\<noteq> y"
shows "(del_point_blocks x) index {y, z} = 0"
proof -
  have "y \<noteq> x" using assms(1) assms(2) by blast 
  have "z \<noteq> x" using assms(1) assms(3) by blast 
  obtain G' where ing: "G' \<in> \<G>" and ss: "G \<subseteq> G'"
    using assms(1) by auto
  have "{y, z} \<subseteq> G" by (simp add: assms(2) assms(3)) 
  then have "{y, z} \<subseteq> \<V>"
    by (meson ss ing group_subset_point_subset) 
  then have "{y, z} \<subseteq> (del_point x)"
    using \<open>y \<noteq> x\<close> \<open>z \<noteq> x\<close> del_point_def by fastforce 
  thus ?thesis using delete_point_index_eq index_together
    by (metis assms(2) assms(3) assms(4) in_mono ing ss) 
qed

lemma delete_point_index: 
  assumes "G1 \<in> {g - {x} |g. g \<in> \<G> \<and> g \<noteq> {x}}"
  assumes "G2 \<in> {g - {x} |g. g \<in> \<G> \<and> g \<noteq> {x}}"
  assumes "G1 \<noteq> G2" and "y \<in> G1" and "z \<in> G2"
  shows "del_point_blocks x index {y, z} = \<Lambda>"
proof -
  have "y \<noteq> x" using assms by blast 
  have "z \<noteq> x" using assms by blast 
  obtain G1' where ing1: "G1' \<in> \<G>" and t1: "G1 = G1' - {x}"
    using assms(1) by auto
  obtain G2' where ing2: "G2' \<in> \<G>" and t2: "G2 = G2' - {x}"
    using assms(2) by auto
  then have ss1: "G1 \<subseteq> G1'" and ss2: "G2 \<subseteq> G2'" using t1 by auto
  then have "{y, z} \<subseteq> \<V>" using ing1 ing2 ss1 ss2 assms(4) assms(5)
    by (metis empty_subsetI insert_absorb insert_subset point_in_group) 
  then have "{y, z} \<subseteq> del_point x"
    using \<open>y \<noteq> x\<close> \<open>z \<noteq> x\<close> del_point_def by auto 
  then have indx: "del_point_blocks x index {y, z} = \<B> index {y, z}" 
    using delete_point_index_eq by auto
  have "G1' \<noteq> G2'" using assms t1 t2 by fastforce 
  thus ?thesis using index_distinct
    using indx assms(4) assms(5) ing1 ing2 t1 t2 by auto 
qed

lemma delete_point_group_size: 
  assumes "{x} \<in> \<G> \<Longrightarrow> card \<G> > 2" 
  shows "1 < card {g - {x} |g. g \<in> \<G> \<and> g \<noteq> {x}}"
proof (cases "{x} \<in> \<G>")
  case True
  then have "\<And> g . g \<in> (\<G> - {{x}}) \<Longrightarrow> x \<notin> g"
    by (meson disjnt_insert1 groups_disjoint pairwise_alt)
  then have simpg: "\<And> g . g \<in> (\<G> - {{x}}) \<Longrightarrow> g - {x} = g"
    by simp 
  have "{g - {x} |g. g \<in> \<G> \<and> g \<noteq> {x}} = {g - {x} |g. (g \<in> \<G> - {{x}})}" using True
    by force 
  then have "{g - {x} |g. g \<in> \<G> \<and> g \<noteq> {x}} = {g |g. (g \<in> \<G> - {{x}})}" using simpg 
    by (smt (verit) Collect_cong)
  then have eq: "{g - {x} |g. g \<in> \<G> \<and> g \<noteq> {x}} =  \<G> - {{x}}" using set_self_img_compr by blast
  have "card (\<G> - {{x}}) = card \<G> - 1" using True
    by (simp add: groups_finite) 
  then show ?thesis using True assms eq diff_is_0_eq' by force 
next
  case False
  then have "\<And>g' y. {x} \<notin> \<G> \<Longrightarrow> g' \<in> \<G> \<Longrightarrow> y \<in> \<G> \<Longrightarrow> g' - {x} = y - {x} \<Longrightarrow> g' = y" 
    by (metis all_not_in_conv insert_Diff_single insert_absorb insert_iff points_sep_groups_ne)
  then have inj: "inj_on (\<lambda> g . g - {x}) \<G>" by (simp add: inj_onI False) 
  have "{g - {x} |g. g \<in> \<G> \<and> g \<noteq> {x}} = {g - {x} |g. g \<in> \<G>}" using False by auto
  then have "card {g - {x} |g. g \<in> \<G> \<and> g \<noteq> {x}} = card \<G>" using inj groups_finite card_image
    by (auto simp add: card_image setcompr_eq_image) 
  then show ?thesis using groups_size by presburger 
qed

lemma GDD_by_deleting_point: 
  assumes "\<And>bl. bl \<in># \<B> \<Longrightarrow> x \<in> bl \<Longrightarrow> 2 \<le> card bl"
  assumes "{x} \<in> \<G> \<Longrightarrow> card \<G> > 2"
  shows "GDD (del_point x) (del_point_blocks x) {g - {x} | g . g \<in> \<G> \<and> g \<noteq> {x}} \<Lambda>"
proof -
  interpret pd: proper_design "del_point x" "del_point_blocks x"
    using delete_point_proper assms by blast
  show ?thesis using delete_point_index_zero delete_point_index assms delete_point_group_size
    by(unfold_locales) (simp_all add: partition_on_remove_pt group_partitions index_ge_1 del_point_def)
qed

end

context K_GDD begin 

subsubsection \<open>PBD construction from GDD\<close>
text \<open>Two well known PBD constructions involve taking a GDD and either combining the groups and
blocks to form a new block collection, or by adjoining a point\<close>

text \<open>First prove that combining the groups and block set results in a constant index\<close>
lemma kgdd1_points_index_group_block: 
  assumes "ps \<subseteq> \<V>"
  and "card ps = 2"
  shows "(\<B> + mset_set \<G>) index ps = 1"
proof -
  have index1: "(\<And> G . G \<in> \<G> \<Longrightarrow> \<not> ps \<subseteq> G) \<Longrightarrow> \<B> index ps = 1"
    using index_distinct_alt_ss assms by fastforce 
  have groups1: "\<B> index ps = 0 \<Longrightarrow> size {#b \<in>#  mset_set \<G> . ps \<subseteq> b#} = 1"  
    using index_zero_implies_one_group assms by simp 
  then have "(\<B> + mset_set \<G>) index ps = size (filter_mset ((\<subseteq>) ps) (\<B> + mset_set \<G>))" 
    by (simp add: points_index_def)
  thus ?thesis using index1 groups1 gdd_index_non_zero_iff gdd_index_zero_iff assms 
      gdd_index_options points_index_def filter_union_mset union_commute
    by (smt (z3) empty_neutral(1) less_irrefl_nat nonempty_has_size of_nat_1_eq_iff) 
qed

text \<open>Combining blocks and the group set forms a PBD\<close>
lemma combine_block_groups_pairwise: "pairwise_balance \<V> (\<B> + mset_set \<G>) 1"
proof -
  let ?B = "\<B> + mset_set \<G>"
  have ss: "\<And> G. G \<in> \<G> \<Longrightarrow> G \<subseteq> \<V>"
    by (simp add: point_in_group subsetI)
  have "\<And> G. G \<in> \<G> \<Longrightarrow> G \<noteq> {}" using group_partitions
    using partition_onD3 by auto 
  then interpret inc: design \<V> ?B 
  proof (unfold_locales)
    show "\<And>b. (\<And>G. G \<in> \<G> \<Longrightarrow> G \<noteq> {}) \<Longrightarrow> b \<in># \<B> + mset_set \<G> \<Longrightarrow> b \<subseteq> \<V>"
      by (metis finite_set_mset_mset_set groups_finite ss union_iff wellformed)
    show "(\<And>G. G \<in> \<G> \<Longrightarrow> G \<noteq> {}) \<Longrightarrow> finite \<V>" by (simp add: finite_sets)
    show "\<And>bl. (\<And>G. G \<in> \<G> \<Longrightarrow> G \<noteq> {}) \<Longrightarrow> bl \<in># \<B> + mset_set \<G> \<Longrightarrow> bl \<noteq> {}"
      using blocks_nempty groups_finite by auto
  qed
  show ?thesis proof (unfold_locales)
    show "inc.\<b> \<noteq> 0" using b_positive by auto
    show "(1 ::int) \<le> 2" by simp
    show "2 \<le> inc.\<v>" by (simp add: gdd_min_v)
    then show "\<And>ps. ps \<subseteq> \<V> \<Longrightarrow> int (card ps) = 2 \<Longrightarrow> int ((\<B> + mset_set \<G>) index ps) = 1" 
      using kgdd1_points_index_group_block by simp
  qed
qed

lemma combine_block_groups_PBD:
  assumes "\<And> G. G \<in> \<G> \<Longrightarrow> card G \<in> \<K>"
  assumes "\<And> k . k \<in> \<K> \<Longrightarrow> k \<ge> 2"
  shows "PBD \<V> (\<B> + mset_set \<G>) \<K>"
proof -
  let ?B = "\<B> + mset_set \<G>"
  interpret inc: pairwise_balance \<V> ?B 1 using combine_block_groups_pairwise by simp
  show ?thesis using assms block_sizes groups_finite positive_ints 
    by (unfold_locales) auto
qed

text \<open>Prove adjoining a point to each group set results in a constant points index\<close>
lemma kgdd1_index_adjoin_group_block:
  assumes "x \<notin> \<V>"
  assumes "ps \<subseteq> insert x \<V>"
  assumes "card ps = 2"
  shows "(\<B> + mset_set {insert x g |g. g \<in> \<G>}) index ps = 1"
proof -
  have "inj_on ((insert) x) \<G>"
    by (meson assms(1) inj_onI insert_ident point_in_group) 
  then have eq: "mset_set {insert x g |g. g \<in> \<G>} = {# insert x g . g \<in># mset_set \<G>#}"
    by (simp add: image_mset_mset_set setcompr_eq_image)
  thus ?thesis 
  proof (cases "x \<in> ps")
    case True
    then obtain y where y_ps: "ps = {x, y}" using assms(3)
      by (metis card_2_iff doubleton_eq_iff insertE singletonD)
    then have ynex: "y \<noteq> x" using assms by fastforce 
    have yinv: "y \<in> \<V>"
      using assms(2) y_ps ynex by auto 
    have all_g: "\<And> g. g \<in># (mset_set {insert x g |g. g \<in> \<G>}) \<Longrightarrow> x \<in> g"
      using eq by force
    have iff: "\<And> g . g \<in> \<G> \<Longrightarrow> y \<in> (insert x g) \<longleftrightarrow> y \<in> g" using ynex by simp 
    have b: "\<B> index ps = 0"
      using True assms(1) points_index_ps_nin by fastforce 
    then have "(\<B> + mset_set {insert x g |g. g \<in> \<G>}) index ps = 
        (mset_set {insert x g |g. g \<in> \<G>}) index ps"
      using eq by (simp add: point_index_distrib)
    also have  "... = (mset_set {insert x g |g. g \<in> \<G>}) rep y" using points_index_pair_rep_num
      by (metis (no_types, lifting) all_g y_ps) 
    also have 0: "... = card {b \<in> {insert x g |g. g \<in> \<G>} . y \<in> b}" 
      by (simp add: groups_finite rep_number_on_set_def)
    also have 1: "... = card {insert x g |g. g \<in> \<G> \<and> y \<in> insert x g}"
      by (smt (verit) Collect_cong mem_Collect_eq)
    also have 2: " ... = card {insert x g |g. g \<in> \<G> \<and> y \<in> g}" 
      using iff by metis 
    also have "... = card {g \<in> \<G> . y \<in> g}" using 1 2 0 empty_iff eq groups_finite ynex insert_iff
      by (metis points_index_block_image_add_eq points_index_single_rep_num rep_number_on_set_def)  
    finally have "(\<B> + mset_set {insert x g |g. g \<in> \<G>}) index ps = 1" 
      using rep_number_point_group_one yinv by simp 
    then show ?thesis
      by simp 
  next
    case False
    then have v: "ps \<subseteq> \<V>" using assms(2) by auto 
    then have "(\<B> + mset_set {insert x g |g. g \<in> \<G>}) index ps = (\<B> + mset_set \<G>) index ps"
      using eq by (simp add: points_index_block_image_add_eq False point_index_distrib) 
    then show ?thesis using v assms kgdd1_points_index_group_block by simp
  qed
qed

lemma pairwise_by_adjoining_point: 
  assumes "x \<notin> \<V>"
  shows "pairwise_balance (add_point x) (\<B> + mset_set { insert x g | g. g \<in> \<G>}) 1"
proof -
  let ?B = "\<B> + mset_set { insert x g | g. g \<in> \<G>}"
  let ?V = "add_point x"
  have vdef: "?V = \<V> \<union> {x}" using add_point_def by simp
  show ?thesis unfolding add_point_def using finite_sets b_positive 
  proof (unfold_locales, simp_all)
    have "\<And> G. G \<in> \<G> \<Longrightarrow> insert x G \<subseteq> ?V"
      by (simp add: point_in_group subsetI vdef)
    then have "\<And> G. G \<in># (mset_set { insert x g | g. g \<in> \<G>}) \<Longrightarrow> G \<subseteq> ?V"
      by (smt (verit, del_insts) elem_mset_set empty_iff infinite_set_mset_mset_set mem_Collect_eq)
    then show "\<And>b. b \<in># \<B> \<or> b \<in># mset_set {insert x g |g. g \<in> \<G>} \<Longrightarrow> b \<subseteq> insert x \<V>" 
      using wellformed add_point_def by fastforce
  next 
    have "\<And> G. G \<in> \<G> \<Longrightarrow> insert x G \<noteq> {}" using group_partitions
      using partition_onD3 by auto 
    then have gnempty: "\<And> G. G \<in># (mset_set { insert x g | g. g \<in> \<G>}) \<Longrightarrow> G \<noteq> {}"
      by (smt (verit, del_insts) elem_mset_set empty_iff infinite_set_mset_mset_set mem_Collect_eq)
    then show "\<And>bl. bl \<in># \<B> \<or> bl \<in># mset_set {insert x g |g. g \<in> \<G>} \<Longrightarrow> bl \<noteq> {}" 
      using blocks_nempty by auto
  next
    have "card \<V> \<ge> 2" using gdd_min_v by simp 
    then have "card (insert x \<V>) \<ge> 2"
      by (meson card_insert_le dual_order.trans finite_sets) 
    then show "2 \<le> int (card (insert x \<V>))" by auto
  next
    show "\<And>ps. ps \<subseteq> insert x \<V> \<Longrightarrow>
          card ps = 2 \<Longrightarrow> (\<B> + mset_set {insert x g |g. g \<in> \<G>}) index ps = Suc 0" 
      using kgdd1_index_adjoin_group_block by (simp add: assms) 
  qed
qed

lemma PBD_by_adjoining_point: 
  assumes "x \<notin> \<V>"
  assumes "\<And> k . k \<in> \<K> \<Longrightarrow> k \<ge> 2"
  shows "PBD (add_point x) (\<B> + mset_set { insert x g | g. g \<in> \<G>}) (\<K> \<union> {(card g) + 1 | g . g \<in> \<G>})"
proof -
  let ?B = "\<B> + mset_set { insert x g | g. g \<in> \<G>}"
  let ?V = "(add_point x)"
  interpret inc: pairwise_balance ?V ?B 1 using pairwise_by_adjoining_point assms by auto 
  show ?thesis using  block_sizes positive_ints proof (unfold_locales)
    have xg: "\<And> g. g \<in> \<G> \<Longrightarrow> x \<notin> g"
      using assms point_in_group by auto 
    have "\<And> bl . bl \<in># \<B> \<Longrightarrow> card bl \<in> \<K>" by (simp add: block_sizes) 
    have "\<And> bl . bl \<in># mset_set {insert x g |g. g \<in> \<G>} \<Longrightarrow> bl \<in> {insert x g | g . g \<in> \<G>}"
      by (simp add: groups_finite) 
    then have "\<And> bl . bl \<in># mset_set {insert x g |g. g \<in> \<G>} \<Longrightarrow> 
      card bl \<in>  {int (card g + 1) |g. g \<in> \<G>}" 
    proof -
      fix bl 
      assume "bl \<in># mset_set {insert x g |g. g \<in> \<G>}"
      then have "bl \<in> {insert x g | g . g \<in> \<G>}" by (simp add: groups_finite)
      then obtain g where gin: "g \<in> \<G>" and i: "bl = insert x g" by auto 
      thus "card bl \<in>  {int (card g + 1) |g. g \<in> \<G>}"
        using gin group_elements_finite i xg by auto
    qed
    then show "\<And>bl. bl \<in># \<B> + mset_set {insert x g |g. g \<in> \<G>} \<Longrightarrow> 
        int (card bl) \<in> \<K> \<union> {int (card g + 1) |g. g \<in> \<G>}"
      using  UnI1 UnI2 block_sizes union_iff by (smt (z3) mem_Collect_eq)
    show "\<And>x. x \<in> \<K> \<union> {int (card g + 1) |g. g \<in> \<G>} \<Longrightarrow> 0 < x" 
      using min_group_size positive_ints by auto
    show "\<And>k.  k \<in> \<K> \<union> {int (card g + 1) |g. g \<in> \<G>} \<Longrightarrow> 2 \<le> k" 
      using min_group_size positive_ints assms by fastforce
  qed
qed

subsubsection \<open>Wilson's Construction\<close>
text \<open>Wilson's construction involves the combination of multiple k-GDD's. This proof was
based of Stinson \cite{stinsonCombinatorialDesignsConstructions2004}\<close>

lemma wilsons_construction_proper: 
  assumes "card I = w"
  assumes "w > 0"
  assumes "\<And> n. n \<in> \<K>' \<Longrightarrow> n \<ge> 2"
  assumes "\<And> B . B \<in># \<B> \<Longrightarrow> K_GDD (B \<times> I) (f B) \<K>' {{x} \<times> I |x . x \<in> B }"
  shows "proper_design (\<V> \<times> I) (\<Sum>B \<in># \<B>. (f B))" (is "proper_design ?Y ?B")
proof (unfold_locales, simp_all)
  show "\<And>b. \<exists>x\<in>#\<B>. b \<in># f x \<Longrightarrow> b \<subseteq> \<V> \<times> I"
  proof -
    fix b
    assume "\<exists>x\<in>#\<B>. b \<in># f x"
    then obtain B where "B \<in># \<B>" and "b \<in># (f B)" by auto
    then interpret kgdd: K_GDD "(B \<times> I)" "(f B)" \<K>' "{{x} \<times> I |x . x \<in> B }" using assms by auto
    show "b \<subseteq> \<V> \<times> I" using kgdd.wellformed
      using \<open>B \<in># \<B>\<close> \<open>b \<in># f B\<close> wellformed by fastforce 
  qed
  show "finite (\<V> \<times> I)" using finite_sets assms bot_nat_0.not_eq_extremum card.infinite by blast 
  show "\<And>bl. \<exists>x\<in>#\<B>. bl \<in># f x \<Longrightarrow> bl \<noteq> {}"
  proof -
    fix bl
    assume "\<exists>x\<in>#\<B>. bl \<in># f x"
    then obtain B where "B \<in># \<B>" and "bl \<in># (f B)" by auto
    then interpret kgdd: K_GDD "(B \<times> I)" "(f B)" \<K>' "{{x} \<times> I |x . x \<in> B }" using assms by auto
    show "bl \<noteq> {}" using kgdd.blocks_nempty by (simp add: \<open>bl \<in># f B\<close>) 
  qed
  show "\<exists>i\<in>#\<B>. f i \<noteq> {#}"
  proof -
    obtain B where "B \<in># \<B>"
      using design_blocks_nempty by auto 
    then interpret kgdd: K_GDD "(B \<times> I)" "(f B)" \<K>' "{{x} \<times> I |x . x \<in> B }" using assms by auto
    have "f B \<noteq> {#}" using kgdd.design_blocks_nempty by simp 
    then show "\<exists>i\<in>#\<B>. f i \<noteq> {#}" using \<open>B \<in># \<B>\<close> by auto 
  qed
qed

lemma pair_construction_block_sizes: 
  assumes "K_GDD (B \<times> I) (f B) \<K>' {{x} \<times> I |x . x \<in> B }"
  assumes "B \<in># \<B>"
  assumes "b \<in># (f B)"
  shows "card b \<in> \<K>'"
proof -
  interpret bkgdd: K_GDD "(B \<times> I)" "(f B)" \<K>' "{{x} \<times> I |x . x \<in> B }"
    using assms by simp
  show "card b \<in> \<K>'" using bkgdd.block_sizes by (simp add:assms) 
qed

lemma wilsons_construction_index_0: 
  assumes "\<And> B . B \<in># \<B> \<Longrightarrow> K_GDD (B \<times> I) (f B) \<K>' {{x} \<times> I |x . x \<in> B }"
  assumes "G \<in> {GG \<times> I |GG. GG \<in> \<G>}"
  assumes "X \<in> G" 
  assumes "Y \<in> G" 
  assumes "X \<noteq> Y"
  shows "(\<Sum>\<^sub># (image_mset f \<B>)) index {X, Y} = 0"
proof -
  obtain G' where gi: "G = G' \<times> I" and ging: "G' \<in> \<G>" using assms by auto
  obtain x y ix iy where xpair: "X = (x, ix)" and ypair: "Y = (y, iy)" using assms by auto
  then have ixin: "ix \<in> I" and xing: "x \<in> G'" using assms gi by auto 
  have iyin: "iy \<in> I" and ying: "y \<in> G'" using assms ypair gi by auto
  have ne_index_0: "x \<noteq> y \<Longrightarrow> \<B> index {x, y} = 0" 
    using ying xing index_together ging by simp
  have "\<And> B. B \<in># \<B> \<Longrightarrow> (f B) index {(x, ix), (y, iy)} = 0" 
  proof -
    fix B
    assume assm: "B \<in># \<B>"
    then interpret kgdd: K_GDD "(B \<times> I)" "(f B)" \<K>' "{{x} \<times> I |x . x \<in> B }" using assms by simp
    have not_ss_0: "\<not> ({(x, ix), (y, iy)} \<subseteq> (B \<times> I)) \<Longrightarrow> (f B) index {(x, ix), (y, iy)} = 0"
      by (metis kgdd.points_index_ps_nin) 
    have "x \<noteq> y \<Longrightarrow> \<not> {x, y} \<subseteq> B" using ne_index_0 assm points_index_0_left_imp by auto 
    then have "x \<noteq> y \<Longrightarrow> \<not> ({(x, ix), (y, iy)} \<subseteq> (B \<times> I))" using assms
      by (meson empty_subsetI insert_subset mem_Sigma_iff)
    then have nexy: "x \<noteq> y \<Longrightarrow> (f B) index {(x, ix), (y, iy)} = 0" using not_ss_0 by simp
    have "x = y \<Longrightarrow> ({(x, ix), (y, iy)} \<subseteq> (B \<times> I)) \<Longrightarrow> (f B) index {(x, ix), (y, iy)} = 0"
    proof -
      assume eq: "x = y"
      assume "({(x, ix), (y, iy)} \<subseteq> (B \<times> I))"
      then obtain g where "g \<in> {{x} \<times> I |x . x \<in> B }" and "(x, ix) \<in> g" and "(y, ix) \<in> g"
        using eq  by auto 
      then show ?thesis using kgdd.index_together
        by (smt (verit, best) SigmaD1 SigmaD2 SigmaI assms(4) assms(5) gi mem_Collect_eq xpair ypair)
    qed
    then show "(f B) index {(x, ix), (y, iy)} = 0" using not_ss_0 nexy by auto
  qed
  then have "\<And> B. B \<in># (image_mset f \<B>) \<Longrightarrow> B index {(x, ix), (y, iy)} = 0" by auto
  then show "(\<Sum>\<^sub># (image_mset f \<B>)) index {X, Y} = 0" 
    by (simp add: points_index_sum xpair ypair)
qed

lemma wilsons_construction_index_1: 
  assumes "\<And> B . B \<in># \<B> \<Longrightarrow> K_GDD (B \<times> I) (f B) \<K>' {{x} \<times> I |x . x \<in> B }"
  assumes "G1 \<in> {G \<times> I |G. G \<in> \<G>}"
  assumes "G2 \<in> {G \<times> I |G. G \<in> \<G>}"
  assumes "G1 \<noteq> G2"
  and "(x, ix) \<in> G1" and "(y, iy) \<in> G2" 
  shows "(\<Sum>\<^sub># (image_mset f \<B>)) index {(x, ix), (y, iy)} = (1 ::int)"
proof -
  obtain G1' where gi1: "G1 = G1' \<times> I" and ging1: "G1' \<in> \<G>" using assms by auto
  obtain G2' where gi2: "G2 = G2' \<times> I" and ging2: "G2' \<in> \<G>" using assms by auto
  have xing: "x \<in> G1'" using assms gi1 by simp
  have ying: "y \<in> G2'" using assms gi2 by simp
  have gne: "G1' \<noteq> G2'" using assms gi1 gi2 by auto
  then have xyne: "x \<noteq> y" using xing ying ging1 ging2 point_in_one_group by blast
  have "\<exists>! bl . bl \<in># \<B> \<and> {x, y} \<subseteq> bl" using index_distinct points_index_one_unique_block
    by (metis ging1 ging2 gne of_nat_1_eq_iff xing ying) 
  then obtain bl where blinb:"bl \<in># \<B>" and xyblss: "{x, y} \<subseteq> bl" by auto 
  then have "\<And> b . b \<in># \<B> - {#bl#} \<Longrightarrow> \<not> {x, y} \<subseteq> b" using points_index_one_not_unique_block
    by (metis ging1 ging2 gne index_distinct int_ops(2) nat_int_comparison(1) xing ying) 
  then have not_ss: "\<And> b . b \<in># \<B> - {#bl#} \<Longrightarrow> \<not> ({(x, ix), (y, iy)} \<subseteq> (b \<times> I))" using assms
    by (meson SigmaD1 empty_subsetI insert_subset)
  then have pi0: "\<And> b . b \<in># \<B> - {#bl#} \<Longrightarrow> (f b) index {(x, ix), (y, iy)}  = 0"
  proof -
    fix b
    assume assm: "b \<in># \<B> - {#bl#}"
    then have "b \<in># \<B>" by (meson in_diffD) 
    then interpret kgdd: K_GDD "(b \<times> I)" "(f b)" \<K>' "{{x} \<times> I |x . x \<in> b }" using assms by simp
    show "(f b) index {(x, ix), (y, iy)} = 0"
      using assm not_ss by (metis kgdd.points_index_ps_nin) 
  qed
  let ?G = "{{x} \<times> I |x . x \<in> bl }"
  interpret bkgdd: K_GDD "(bl \<times> I)" "(f bl)" \<K>' ?G using assms blinb by simp
  obtain g1 g2 where xing1: "(x, ix) \<in> g1" and ying2: "(y, iy) \<in> g2" and g1g: "g1 \<in> ?G" 
      and g2g: "g2 \<in> ?G" using assms(5) assms(6) gi1 gi2
    by (metis (no_types, lifting) bkgdd.point_has_unique_group insert_subset mem_Sigma_iff xyblss) 
  then have "g1 \<noteq> g2" using xyne by blast 
  then have pi1: "(f bl) index {(x, ix), (y, iy)} = 1" 
    using bkgdd.index_distinct xing1 ying2 g1g g2g by simp
  have "(\<Sum>\<^sub># (image_mset f \<B>)) index {(x, ix), (y, iy)} = 
      (\<Sum>B \<in># \<B>. (f B) index {(x, ix), (y, iy)} )" 
    by (simp add: points_index_sum)
  then have "(\<Sum>\<^sub># (image_mset f \<B>)) index {(x, ix), (y, iy)} = 
      (\<Sum>B \<in># (\<B> - {#bl#}). (f B) index {(x, ix), (y, iy)}) + (f bl) index {(x, ix), (y, iy)}"
    by (metis (no_types, lifting) add.commute blinb insert_DiffM sum_mset.insert) 
  thus ?thesis using pi0 pi1 by simp
qed

theorem Wilsons_Construction:
  assumes "card I = w"
  assumes "w > 0"
  assumes "\<And> n. n \<in> \<K>' \<Longrightarrow> n \<ge> 2"
  assumes "\<And> B . B \<in># \<B> \<Longrightarrow> K_GDD (B \<times> I) (f B) \<K>' {{x} \<times> I |x . x \<in> B }"
  shows "K_GDD (\<V> \<times> I) (\<Sum>B \<in># \<B>. (f B)) \<K>' {G \<times> I | G . G \<in> \<G>}"
proof -
  let ?Y = "\<V> \<times> I" and ?H = "{G \<times> I | G . G \<in> \<G>}" and ?B = "\<Sum>B \<in># \<B>. (f B)"
  interpret pd: proper_design ?Y ?B using wilsons_construction_proper assms by auto
  have "\<And> bl . bl \<in># (\<Sum>B \<in># \<B>. (f B)) \<Longrightarrow> card bl \<in> \<K>'"  
    using assms pair_construction_block_sizes by blast 
  then interpret kdes: K_block_design ?Y ?B \<K>' 
    using assms(3) by (unfold_locales) (simp_all,fastforce)
  interpret gdd: GDD ?Y ?B ?H "1:: int" 
  proof (unfold_locales)
    show "partition_on (\<V> \<times> I) {G \<times> I |G. G \<in> \<G>}" 
      using assms groups_not_empty design_points_nempty group_partitions
      by (simp add: partition_on_cart_prod) 
    have "inj_on (\<lambda> G. G \<times> I) \<G>"
      using inj_on_def pd.design_points_nempty by auto 
    then have "card {G \<times> I |G. G \<in> \<G>} = card \<G>" using card_image by (simp add: Setcompr_eq_image) 
    then show "1 < card {G \<times> I |G. G \<in> \<G>}" using groups_size by linarith 
    show "(1::int) \<le> 1" by simp
    have gdd_fact: "\<And> B . B \<in># \<B> \<Longrightarrow> K_GDD (B \<times> I) (f B) \<K>' {{x} \<times> I |x . x \<in> B }" 
      using assms by simp
    show "\<And>G X Y. G \<in> {GG \<times> I |GG. GG \<in> \<G>} \<Longrightarrow> X \<in> G \<Longrightarrow> Y \<in> G \<Longrightarrow> X \<noteq> Y 
        \<Longrightarrow> (\<Sum>\<^sub># (image_mset f \<B>)) index {X, Y} = 0"
      using wilsons_construction_index_0[OF assms(4)] by auto
    show "\<And>G1 G2 X Y. G1 \<in> {G \<times> I |G. G \<in> \<G>} \<Longrightarrow> G2 \<in> {G \<times> I |G. G \<in> \<G>} 
      \<Longrightarrow> G1 \<noteq> G2 \<Longrightarrow> X \<in> G1 \<Longrightarrow> Y \<in> G2 \<Longrightarrow> ((\<Sum>\<^sub># (image_mset f \<B>)) index {X, Y}) = (1 ::int)"
      using wilsons_construction_index_1[OF assms(4)] by blast 
  qed
  show ?thesis by (unfold_locales)
qed

end

context pairwise_balance
begin

lemma PBD_by_deleting_point: 
  assumes "\<v> > 2"
  assumes "\<And> bl . bl \<in># \<B> \<Longrightarrow> card bl \<ge> 2"
  shows "pairwise_balance (del_point x) (del_point_blocks x) \<Lambda>"
proof (cases "x \<in> \<V>")
  case True
  interpret des: design "del_point x" "del_point_blocks x"
    using delete_point_design assms by blast 
  show ?thesis using assms design_blocks_nempty del_point_def del_point_blocks_def
  proof (unfold_locales, simp_all)
    show "2 < \<v> \<Longrightarrow> (\<And>bl. bl \<in># \<B> \<Longrightarrow> 2 \<le> card bl) \<Longrightarrow> 2 \<le> int (card (\<V> - {x}))"
      using card_Diff_singleton_if diff_diff_cancel diff_le_mono2 finite_sets less_one
      by (metis int_ops(3) less_nat_zero_code nat_le_linear verit_comp_simplify1(3) zle_int)
    have "\<And> ps . ps  \<subseteq> \<V> - {x} \<Longrightarrow> ps \<subseteq> \<V>" by auto
    then show "\<And>ps. ps \<subseteq> \<V> - {x} \<Longrightarrow> card ps = 2  \<Longrightarrow> {#bl - {x}. bl \<in># \<B>#} index ps = \<Lambda>"
      using delete_point_index_eq del_point_def del_point_blocks_def by simp
  qed
next
  case False
  then show ?thesis
    by (simp add: del_invalid_point del_invalid_point_blocks pairwise_balance_axioms)
qed
end

context k_GDD
begin

lemma bibd_from_kGDD:
  assumes "\<k> > 1"
  assumes "\<And> g. g \<in> \<G> \<Longrightarrow> card g = \<k> - 1"
  assumes " x \<notin> \<V>"
  shows "bibd (add_point x) (\<B> + mset_set { insert x g | g. g \<in> \<G>}) (\<k>) 1"
proof - 
  have "({\<k>} \<union> {(card g) + 1 | g . g \<in> \<G>}) = {\<k>}"
    using assms(2) by fastforce 
  then interpret pbd: PBD "(add_point x)" "\<B> + mset_set { insert x g | g. g \<in> \<G>}" "{\<k>}"
    using PBD_by_adjoining_point assms sys_block_sizes_obtain_bl add_point_def
    by (smt (verit, best) Collect_cong sys_block_sizes_uniform uniform_alt_def_all) 
  show ?thesis using assms pbd.block_sizes block_size_lt_v finite_sets add_point_def
    by (unfold_locales) (simp_all)
qed

end

context PBD 
begin

lemma pbd_points_index1: "ps \<subseteq> \<V> \<Longrightarrow> card ps = 2 \<Longrightarrow> \<B> index ps = 1"
  using balanced by (metis int_eq_iff_numeral of_nat_1_eq_iff) 

lemma pbd_index1_points_imply_unique_block: 
  assumes "b1 \<in># \<B>" and "b2 \<in># \<B>" and "b1 \<noteq> b2"
  assumes "x \<noteq> y" and "{x, y} \<subseteq> b1" and "x \<in> b2" 
  shows "y \<notin> b2"
proof (rule ccontr)
  let ?ps = "{# b \<in># \<B> . {x, y} \<subseteq> b#}"
  assume "\<not> y \<notin> b2"
  then have a: "y \<in> b2" by linarith
  then have "{x, y} \<subseteq> b2"
    by (simp add: assms(6)) 
  then have "b1 \<in># ?ps" and "b2 \<in># ?ps" using assms by auto
  then have ss: "{#b1, b2#} \<subseteq># ?ps" using assms
    by (metis insert_noteq_member mset_add mset_subset_eq_add_mset_cancel single_subset_iff) 
  have "size {#b1, b2#} = 2" using assms by auto
  then have ge2: "size ?ps \<ge> 2" using assms ss by (metis size_mset_mono) 
  have pair: "card {x, y} = 2" using assms by auto
  have "{x, y} \<subseteq> \<V>" using assms wellformed by auto
  then have "\<B> index {x, y} = 1" using pbd_points_index1 pair by simp
  then show False using points_index_def ge2
    by (metis numeral_le_one_iff semiring_norm(69)) 
qed

lemma strong_delete_point_groups_index_zero: 
  assumes "G \<in> {b - {x} |b. b \<in># \<B> \<and> x \<in> b}"
  assumes "xa \<in> G" and "y \<in> G" and "xa \<noteq> y"
  shows "(str_del_point_blocks x) index {xa, y} = 0"
proof (auto simp add: points_index_0_iff str_del_point_blocks_def)
  fix b
  assume a1: "b \<in># \<B>" and a2: "x \<notin> b" and a3: "xa \<in> b" and a4: "y \<in> b"
  obtain b' where "G = b' - {x}" and "b' \<in># \<B>" and  "x \<in> b'" using assms by blast
  then show False using a1 a2 a3 a4 assms pbd_index1_points_imply_unique_block
    by fastforce 
qed

lemma strong_delete_point_groups_index_one: 
  assumes "G1 \<in> {b - {x} |b. b \<in># \<B> \<and> x \<in> b}"
  assumes "G2 \<in> {b - {x} |b. b \<in># \<B> \<and> x \<in> b}"
  assumes "G1 \<noteq> G2" and "xa \<in> G1" and "y \<in> G2"
  shows  "(str_del_point_blocks x) index {xa, y} = 1"
proof -
  obtain b1 where gb1: "G1 = b1 - {x}" and b1in: "b1 \<in># \<B>" and xin1: "x \<in> b1" using assms by blast
  obtain b2 where gb2: "G2 = b2 - {x}" and b2in: "b2 \<in># \<B>" and xin2:"x \<in> b2" using assms by blast
  have bneq: "b1 \<noteq> b2 " using assms(3) gb1 gb2 by auto
  have "xa \<noteq> y" using gb1 b1in xin1 gb2 b2in xin2 assms(3) assms(4) assms(5) insert_subset
    by (smt (verit, best) Diff_eq_empty_iff Diff_iff empty_Diff insertCI pbd_index1_points_imply_unique_block) 
  then have pair: "card {xa, y} = 2" by simp 
  have inv: "{xa, y} \<subseteq> \<V>" using gb1 b1in gb2 b2in assms(4) assms(5)
    by (metis Diff_cancel Diff_subset insert_Diff insert_subset wellformed) 
  have "{# bl \<in># \<B> . x \<in> bl#} index {xa, y} = 0"
  proof (auto simp add: points_index_0_iff)
    fix b assume a1: "b \<in># \<B>" and a2: "x \<in> b" and a3: "xa \<in> b" and a4: "y \<in> b"
    then have yxss: "{y, x} \<subseteq> b2"
      using assms(5) gb2 xin2 by blast 
    have "{xa, x} \<subseteq> b1"
      using assms(4) gb1 xin1 by auto 
    then have "xa \<notin> b2" using pbd_index1_points_imply_unique_block
      by (metis DiffE assms(4) b1in b2in bneq gb1 singletonI xin2) 
    then have "b2 \<noteq> b" using a3 by auto 
    then show False using pbd_index1_points_imply_unique_block
      by (metis DiffD2 yxss a1 a2 a4 assms(5) b2in gb2 insertI1) 
  qed
  then have "(str_del_point_blocks x) index {xa, y} = \<B> index {xa, y}" 
    by (metis multiset_partition plus_nat.add_0 point_index_distrib str_del_point_blocks_def) 
  thus ?thesis using pbd_points_index1 pair inv by fastforce
qed

lemma blocks_with_x_partition: 
  assumes "x \<in> \<V>"
  shows "partition_on (\<V> - {x}) {b - {x} |b. b \<in># \<B> \<and> x \<in> b}"
proof (intro partition_onI )
  have gtt: "\<And> bl. bl \<in># \<B> \<Longrightarrow> card bl \<ge> 2" using block_size_gt_t
    by (simp add: block_sizes nat_int_comparison(3)) 
  show "\<And>p. p \<in> {b - {x} |b. b \<in># \<B> \<and> x \<in> b} \<Longrightarrow> p \<noteq> {}"
  proof -
    fix p assume "p \<in> {b - {x} |b. b \<in># \<B> \<and> x \<in> b}"
    then obtain b where ptx: "p = b - {x}" and "b \<in># \<B>" and xinb: "x \<in> b" by blast
    then have ge2: "card b \<ge> 2" using gtt by (simp add: nat_int_comparison(3)) 
    then have "finite b" by (metis card.infinite not_numeral_le_zero) 
    then have "card p = card b - 1" using xinb ptx by simp
    then have "card p \<ge> 1" using ge2 by linarith
    thus "p \<noteq> {}" by auto
  qed
  show "\<Union> {b - {x} |b. b \<in># \<B> \<and> x \<in> b} = \<V> - {x}"
  proof (intro subset_antisym subsetI)
    fix xa
    assume "xa \<in> \<Union> {b - {x} |b. b \<in># \<B> \<and> x \<in> b}" 
    then obtain b where "xa \<in> b" and "b \<in># \<B>" and "x \<in> b" and "xa \<noteq> x" by auto
    then show "xa \<in> \<V> - {x}" using wf_invalid_point by blast 
  next 
    fix xa
    assume a: "xa \<in> \<V> - {x}"
    then have nex: "xa \<noteq> x" by simp
    then have pair: "card {xa, x} = 2" by simp 
    have "{xa, x} \<subseteq> \<V>" using a assms by auto 
    then have "card {b \<in> design_support . {xa, x} \<subseteq> b} = 1" 
      using balanced points_index_simple_def pbd_points_index1 assms by (metis pair) 
    then obtain b where des: "b \<in> design_support" and ss: "{xa, x} \<subseteq> b"
      by (metis (no_types, lifting) card_1_singletonE mem_Collect_eq singletonI)
    then show "xa \<in> \<Union> {b - {x} |b. b \<in># \<B> \<and> x \<in> b}"
      using des ss nex design_support_def by auto
  qed
  show "\<And>p p'. p \<in> {b - {x} |b. b \<in># \<B> \<and> x \<in> b} \<Longrightarrow> p' \<in> {b - {x} |b. b \<in># \<B> \<and> x \<in> b} \<Longrightarrow> 
    p \<noteq> p' \<Longrightarrow> p \<inter> p' = {}" 
  proof -
    fix p p'
    assume p1: "p \<in> {b - {x} |b. b \<in># \<B> \<and> x \<in> b}" and p2: "p' \<in> {b - {x} |b. b \<in># \<B> \<and> x \<in> b}" 
      and pne: "p \<noteq> p'"
    then obtain b where b1: "p = b - {x}" and b1in:"b \<in># \<B>" and xinb1:"x \<in> b" by blast 
    then obtain b' where b2: "p' = b' - {x}" and b2in: "b' \<in># \<B>" and xinb2: "x \<in> b'"
      using p2 by blast
    then have "b \<noteq> b'" using pne b1 by auto
    then have "\<And> y. y \<in> b \<Longrightarrow> y \<noteq> x \<Longrightarrow> y \<notin> b'" 
      using b1in b2in xinb1 xinb2 pbd_index1_points_imply_unique_block
      by (meson empty_subsetI insert_subset) 
    then have "\<And> y. y \<in> p \<Longrightarrow> y \<notin> p'"
      by (metis Diff_iff b1 b2 insertI1) 
    then show "p \<inter> p' = {}" using disjoint_iff by auto
  qed
qed

lemma KGDD_by_deleting_point:
  assumes "x \<in> \<V>"
  assumes "\<B> rep x < \<b>"
  assumes "\<B> rep x > 1" 
  shows "K_GDD (del_point x) (str_del_point_blocks x) \<K> { b - {x} | b . b \<in># \<B> \<and> x \<in> b}"
proof -
  have "\<And> bl. bl \<in># \<B> \<Longrightarrow> card bl \<ge> 2" using block_size_gt_t 
    by (simp add: block_sizes nat_int_comparison(3))
  then interpret des: proper_design "(del_point x)" "(str_del_point_blocks x)" 
    using strong_delete_point_proper assms by blast
  show ?thesis using blocks_with_x_partition strong_delete_point_groups_index_zero 
      strong_delete_point_groups_index_one str_del_point_blocks_def del_point_def
  proof (unfold_locales, simp_all add: block_sizes positive_ints assms) 
    have ge1: "card {b . b \<in># \<B> \<and> x \<in> b} > 1" 
      using assms(3) replication_num_simple_def design_support_def by auto
    have fin: "finite {b . b \<in># \<B> \<and> x \<in> b}" by simp 
    have inj: "inj_on (\<lambda> b . b - {x}) {b . b \<in># \<B> \<and> x \<in> b}" 
      using assms(2) inj_on_def mem_Collect_eq by auto 
    then have "card {b - {x} |b. b \<in># \<B> \<and> x \<in> b} = card {b . b \<in># \<B> \<and> x \<in> b}" 
      using card_image fin by (simp add: inj card_image setcompr_eq_image)
    then show "Suc 0 < card {b - {x} |b. b \<in># \<B> \<and> x \<in> b}" using ge1
      by presburger 
  qed
qed

lemma card_singletons_eq: "card {{a} | a . a \<in> A} = card A"
  by (simp add: card_image Setcompr_eq_image)

lemma KGDD_from_PBD: "K_GDD \<V> \<B> \<K> {{x} | x . x \<in> \<V>}"
proof (unfold_locales,auto simp add: Setcompr_eq_image partition_on_singletons)
  have "card ((\<lambda>x. {x}) ` \<V>) \<ge> 2" using t_lt_order card_singletons_eq
    by (metis Collect_mem_eq nat_leq_as_int of_nat_numeral setcompr_eq_image) 
  then show "Suc 0 < card ((\<lambda>x. {x}) ` \<V>)" by linarith
  show "\<And>xa xb. xa \<in> \<V> \<Longrightarrow> xb \<in> \<V> \<Longrightarrow> \<B> index {xa, xb} \<noteq> Suc 0 \<Longrightarrow> xa = xb"
  proof (rule ccontr)
    fix xa xb
    assume ain: "xa \<in> \<V>" and bin: "xb \<in> \<V>" and ne1: "\<B> index {xa, xb} \<noteq> Suc 0"
    assume "xa \<noteq> xb"
    then have "card {xa, xb} = 2" by auto
    then have "\<B> index {xa, xb} = 1"
      by (simp add: ain bin pbd_points_index1) 
    thus False using ne1 by linarith
  qed 
qed

end

context bibd
begin
lemma kGDD_from_bibd:
  assumes "\<Lambda> = 1"
  assumes "x \<in> \<V>"
  shows "k_GDD (del_point x) (str_del_point_blocks x) \<k> { b - {x} | b . b \<in># \<B> \<and> x \<in> b}"
proof -
  interpret pbd: PBD \<V> \<B> "{\<k>}" using assms
    using PBD.intro \<Lambda>_PBD_axioms by auto 
  have lt: "\<B> rep x < \<b>" using block_num_gt_rep
    by (simp add: assms(2)) 
  have "\<B> rep x > 1" using r_ge_two assms by simp
  then interpret kgdd: K_GDD "(del_point x)" "str_del_point_blocks x" 
    "{\<k>}" "{ b - {x} | b . b \<in># \<B> \<and> x \<in> b}"
    using pbd.KGDD_by_deleting_point lt assms by blast 
  show ?thesis using del_point_def str_del_point_blocks_def by (unfold_locales) (simp_all)
qed

end
end