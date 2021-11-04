theory Design_Basics imports Main Multisets_Extras "HOL-Library.Disjoint_Sets"
begin

section \<open>Design Theory Basics\<close>
text \<open>All definitions in this section reference the handbook of combinatorial designs
 \cite{colbournHandbookCombinatorialDesigns2007}\<close>

subsection \<open>Initial setup\<close>

text \<open>Enable coercion of nats to ints to aid with reasoning on design properties\<close>
declare [[coercion_enabled]]
declare [[coercion "of_nat :: nat \<Rightarrow> int"]]

subsection \<open>Incidence System\<close>

text \<open>An incidence system is defined to be a wellformed set system. i.e. each block is a subset
of the base point set. Alternatively, an incidence system can be looked at as the point set
and an incidence relation which indicates if they are in the same block\<close>

locale incidence_system = 
  fixes point_set :: "'a set" ("\<V>")
  fixes block_collection :: "'a set multiset" ("\<B>")
  assumes wellformed: "b \<in># \<B> \<Longrightarrow> b \<subseteq> \<V>"
begin

definition "\<I> \<equiv> { (x, b) . b \<in># \<B> \<and> x \<in> b}" (* incidence relation *)

definition incident :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
"incident p b \<equiv> (p, b) \<in> \<I>"

text \<open>Defines common notation used to indicate number of points ($v$) and number of blocks ($b$)\<close>
abbreviation "\<v> \<equiv> int (card \<V>)"

abbreviation "\<b> \<equiv> int (size \<B>)"

text \<open>Basic incidence lemmas\<close>

lemma incidence_alt_def: 
  assumes "p \<in> \<V>"
  assumes "b \<in># \<B>"
  shows "incident p b \<longleftrightarrow> p \<in> b"
  by (auto simp add: incident_def \<I>_def assms)

lemma wf_invalid_point: "x \<notin> \<V> \<Longrightarrow> b \<in># \<B> \<Longrightarrow> x \<notin> b"
  using wellformed by auto

lemma block_set_nempty_imp_block_ex: "\<B> \<noteq> {#} \<Longrightarrow> \<exists> bl . bl \<in># \<B>"
  by auto

text \<open>Abbreviations for all incidence systems\<close>
abbreviation multiplicity :: "'a set \<Rightarrow> nat" where
"multiplicity b \<equiv> count \<B> b"

abbreviation incomplete_block :: "'a set \<Rightarrow> bool" where
"incomplete_block bl \<equiv> card bl < card \<V> \<and> bl \<in># \<B>"

lemma incomplete_alt_size: "incomplete_block bl \<Longrightarrow> card bl < \<v>" 
  by simp

lemma incomplete_alt_in: "incomplete_block bl \<Longrightarrow> bl \<in># \<B>"
  by simp

lemma incomplete_alt_imp[intro]: "card bl < \<v> \<Longrightarrow> bl \<in># \<B> \<Longrightarrow> incomplete_block bl"
  by simp

definition design_support :: "'a set set" where
"design_support \<equiv> set_mset \<B>"

end

subsection \<open>Finite Incidence Systems\<close>

text \<open>These simply require the point set to be finite.
As multisets are only defined to be finite, it is implied that the block set must be finite already\<close>

locale finite_incidence_system = incidence_system + 
  assumes finite_sets: "finite \<V>"
begin

lemma finite_blocks: "b \<in># \<B> \<Longrightarrow> finite b"
  using wellformed finite_sets finite_subset by blast 

lemma mset_points_distinct: "distinct_mset (mset_set \<V>)"
  using finite_sets by (simp add: distinct_mset_def)

lemma mset_points_distinct_diff_one: "distinct_mset (mset_set (\<V> - {x}))"
  by (meson count_mset_set_le_one distinct_mset_count_less_1)

lemma finite_design_support: "finite (design_support)"
  using design_support_def by auto 

lemma block_size_lt_order: "bl \<in># \<B> \<Longrightarrow> card bl \<le> card \<V>"
  using wellformed by (simp add: card_mono finite_sets)  

end

subsection \<open>Designs\<close>

text \<open>There are many varied definitions of a design in literature. However, the most
commonly accepted definition is a finite point set, $V$ and collection of blocks $B$, where
no block in $B$ can be empty\<close>
locale design = finite_incidence_system +
  assumes blocks_nempty: "bl \<in># \<B> \<Longrightarrow> bl \<noteq> {}"
begin

lemma wf_design: "design \<V> \<B>"  by intro_locales

lemma wf_design_iff: "bl \<in># \<B> \<Longrightarrow> design \<V> \<B> \<longleftrightarrow> (bl \<subseteq> \<V> \<and> finite \<V> \<and> bl \<noteq> {})"
  using blocks_nempty wellformed finite_sets
  by (simp add: wf_design) 

text \<open>Reasoning on non empty properties and non zero parameters\<close>
lemma blocks_nempty_alt: "\<forall> bl \<in># \<B>. bl \<noteq> {}"
  using blocks_nempty by auto

lemma block_set_nempty_imp_points: "\<B> \<noteq> {#} \<Longrightarrow> \<V> \<noteq> {}"
  using wf_design wf_design_iff by auto

lemma b_non_zero_imp_v_non_zero: "\<b> > 0 \<Longrightarrow> \<v> > 0"
  using block_set_nempty_imp_points finite_sets by fastforce

lemma v_eq0_imp_b_eq_0: "\<v> = 0 \<Longrightarrow> \<b> = 0"
  using b_non_zero_imp_v_non_zero by auto

text \<open>Size lemmas\<close>
lemma block_size_lt_v: "bl \<in># \<B> \<Longrightarrow> card bl \<le> \<v>"
  by (simp add: card_mono finite_sets wellformed)

lemma block_size_gt_0: "bl \<in># \<B> \<Longrightarrow> card bl > 0"
  using finite_sets blocks_nempty finite_blocks by fastforce

lemma design_cart_product_size: "size ((mset_set \<V>) \<times># \<B>) = \<v> * \<b>"
  by (simp add: size_cartesian_product) 

end

text \<open>Intro rules for design locale\<close>

lemma wf_design_implies: 
  assumes "(\<And> b . b \<in># \<B> \<Longrightarrow> b \<subseteq> V)"
  assumes "\<And> b . b \<in># \<B> \<Longrightarrow> b \<noteq> {}"
  assumes "finite V"
  assumes "\<B> \<noteq> {#}"
  assumes "V \<noteq> {}"
  shows "design V \<B>"
  using assms by (unfold_locales) simp_all

lemma (in incidence_system) finite_sysI[intro]: "finite \<V> \<Longrightarrow> finite_incidence_system \<V> \<B>"
  by (unfold_locales) simp_all

lemma (in finite_incidence_system) designI[intro]: "(\<And> b. b \<in># \<B> \<Longrightarrow> b \<noteq> {}) \<Longrightarrow> \<B> \<noteq> {#}
     \<Longrightarrow> \<V> \<noteq> {} \<Longrightarrow> design \<V> \<B>"
  by (unfold_locales) simp_all

subsection \<open>Core Property Definitions\<close>

subsubsection \<open>Replication Number\<close>

text \<open>The replication number for a point is the number of blocks that point is incident with\<close>

definition point_replication_number :: "'a set multiset \<Rightarrow> 'a \<Rightarrow> int" (infix "rep" 75) where
"B rep x \<equiv> size {#b \<in># B . x \<in> b#}"

lemma max_point_rep: "B rep x \<le> size B"
  using size_filter_mset_lesseq by (simp add: point_replication_number_def)

lemma rep_number_g0_exists: 
  assumes "B rep x > 0" 
  obtains b where "b \<in># B" and "x \<in> b"
proof -
  have "size {#b \<in># B . x \<in> b#} > 0" using assms point_replication_number_def
    by (metis of_nat_0_less_iff)
  thus ?thesis
    by (metis filter_mset_empty_conv nonempty_has_size that) 
qed

lemma rep_number_on_set_def: "finite B \<Longrightarrow> (mset_set B) rep x = card {b \<in> B . x \<in> b}"
  by (simp add: point_replication_number_def)

lemma point_rep_number_split[simp]: "(A + B) rep x = A rep x + B rep x"
  by (simp add: point_replication_number_def)

lemma point_rep_singleton_val [simp]: "x \<in> b \<Longrightarrow> {#b#} rep x = 1"
  by (simp add: point_replication_number_def)

lemma point_rep_singleton_inval [simp]: "x \<notin> b \<Longrightarrow> {#b#} rep x = 0"
  by (simp add: point_replication_number_def)

context incidence_system
begin

lemma point_rep_number_alt_def: "\<B> rep x = size {# b \<in># \<B> . x \<in> b#}"
  by (simp add: point_replication_number_def)

lemma rep_number_non_zero_system_point: " \<B> rep x > 0 \<Longrightarrow> x \<in> \<V>"
  using rep_number_g0_exists wellformed
  by (metis wf_invalid_point) 

lemma point_rep_non_existance [simp]: "x \<notin> \<V> \<Longrightarrow> \<B> rep x = 0"
  using wf_invalid_point by (simp add:  point_replication_number_def filter_mset_empty_conv) 

lemma point_rep_number_inv: "size {# b \<in># \<B> . x \<notin> b #} = \<b> - (\<B> rep x)"
proof -
  have "\<b> = size {# b \<in># \<B> . x \<notin> b #} + size {# b \<in># \<B> . x \<in> b #}"
    using multiset_partition by (metis add.commute size_union)  
  thus ?thesis by (simp add: point_replication_number_def) 
qed

lemma point_rep_num_inv_non_empty: "(\<B> rep x) < \<b> \<Longrightarrow> \<B> \<noteq> {#} \<Longrightarrow> {# b \<in># \<B> . x \<notin> b #} \<noteq> {#}"
  by (metis diff_zero point_replication_number_def size_empty size_filter_neg verit_comp_simplify1(1))

end

subsubsection \<open>Point Index\<close>

text \<open>The point index of a subset of points in a design, is the number of times those points 
occur together in a block of the design\<close>
definition points_index :: "'a set multiset \<Rightarrow> 'a set \<Rightarrow> nat" (infix "index" 75) where
"B index ps \<equiv> size {#b \<in># B . ps \<subseteq> b#}"

lemma points_index_empty [simp]: "{#} index ps = 0"
  by (simp add: points_index_def)

lemma point_index_distrib: "(B1 + B2) index ps =  B1 index ps + B2 index ps"
  by (simp add: points_index_def)

lemma point_index_diff: "B1 index ps = (B1 + B2) index ps - B2 index ps"
  by (simp add: points_index_def)

lemma points_index_singleton: "{#b#} index ps = 1 \<longleftrightarrow> ps \<subseteq> b"
  by (simp add: points_index_def)

lemma points_index_singleton_zero: "\<not> (ps \<subseteq> b) \<Longrightarrow> {#b#} index ps = 0"
  by (simp add: points_index_def)

lemma points_index_sum: "(\<Sum>\<^sub># B ) index ps = (\<Sum>b \<in># B . (b index ps))"
  using points_index_empty by (induction B) (auto simp add: point_index_distrib)

lemma points_index_block_image_add_eq: 
  assumes "x \<notin> ps"
  assumes "B index ps = l"
  shows "{# insert x b . b \<in># B#} index ps = l"
  using points_index_def by (metis (no_types, lifting) assms filter_mset_cong 
      image_mset_filter_swap2 points_index_def size_image_mset subset_insert)

lemma points_index_on_set_def [simp]: 
  assumes "finite B"
  shows "(mset_set B) index ps = card {b \<in> B. ps \<subseteq> b}"
  by (simp add: points_index_def assms)

lemma points_index_single_rep_num: "B index {x} = B rep x"
  by (simp add: points_index_def point_replication_number_def)

lemma points_index_pair_rep_num: 
  assumes "\<And> b. b \<in># B \<Longrightarrow> x \<in> b"
  shows "B index {x, y} = B rep y"
  using point_replication_number_def points_index_def
  by (metis assms empty_subsetI filter_mset_cong insert_subset)

lemma points_index_0_left_imp: 
  assumes "B index ps = 0"
  assumes "b \<in># B"
  shows "\<not> (ps \<subseteq> b)"
proof (rule ccontr)
  assume "\<not> \<not> ps \<subseteq> b"
  then have a: "ps \<subseteq> b" by auto
  then have "b \<in># {#bl \<in># B . ps \<subseteq> bl#}" by (simp add: assms(2)) 
  thus False by (metis assms(1) count_greater_eq_Suc_zero_iff count_size_set_repr not_less_eq_eq 
        points_index_def size_filter_mset_lesseq) 
qed

lemma points_index_0_right_imp: 
  assumes "\<And> b . b \<in># B \<Longrightarrow> (\<not> ps \<subseteq> b)"
  shows "B index ps = 0"
  using assms by (simp add: filter_mset_empty_conv points_index_def)

lemma points_index_0_iff: "B index ps = 0 \<longleftrightarrow> (\<forall> b. b \<in># B \<longrightarrow> (\<not> ps \<subseteq> b))"
  using points_index_0_left_imp points_index_0_right_imp by metis

lemma points_index_gt0_impl_existance: 
  assumes "B index ps > 0"
  shows "(\<exists> bl . (bl \<in># B \<and> ps \<subseteq> bl))"
proof -
  have "size {#bl \<in># B . ps \<subseteq> bl#} > 0"
    by (metis assms points_index_def)
  then obtain bl where "bl \<in># B" and "ps \<subseteq> bl"
    by (metis filter_mset_empty_conv nonempty_has_size) 
  thus ?thesis by auto
qed

lemma points_index_one_unique: 
  assumes "B index ps = 1"
  assumes "bl \<in># B" and "ps \<subseteq> bl" and "bl' \<in># B" and "ps \<subseteq> bl'"
  shows "bl = bl'"
proof (rule ccontr)
  assume assm: "bl \<noteq> bl'"
  then have bl1: "bl \<in># {#bl \<in># B . ps \<subseteq> bl#}" using assms by simp
  then have bl2: "bl'\<in># {#bl \<in># B . ps \<subseteq> bl#}" using assms by simp
  then have "{#bl, bl'#} \<subseteq># {#bl \<in># B . ps \<subseteq> bl#}" using assms by (metis bl1 bl2 points_index_def
        add_mset_subseteq_single_iff assm mset_subset_eq_single size_single subseteq_mset_size_eql) 
  then have "size {#bl \<in># B . ps \<subseteq> bl#} \<ge> 2" using size_mset_mono by fastforce 
  thus False using assms by (metis numeral_le_one_iff points_index_def semiring_norm(69))
qed

lemma points_index_one_unique_block: 
  assumes "B index ps = 1"
  shows "\<exists>! bl . (bl \<in># B \<and> ps \<subseteq> bl)"
  using assms points_index_gt0_impl_existance points_index_one_unique
  by (metis zero_less_one) 

lemma points_index_one_not_unique_block: 
  assumes "B index ps = 1"
  assumes "ps \<subseteq> bl"
  assumes "bl \<in># B"
  assumes "bl' \<in># B - {#bl#}"
  shows "\<not> ps \<subseteq> bl'"
proof - 
  have "B = (B - {#bl#}) + {#bl#}" by (simp add: assms(3)) 
  then have "(B - {#bl#}) index ps = B index ps - {#bl#} index ps"
    by (metis point_index_diff) 
  then have "(B - {#bl#}) index ps = 0" using assms points_index_singleton
    by (metis diff_self_eq_0) 
  thus ?thesis using assms(4) points_index_0_left_imp by auto
qed

lemma (in incidence_system) points_index_alt_def: "\<B> index ps = size {#b \<in># \<B> . ps \<subseteq> b#}"
  by (simp add: points_index_def)

lemma (in incidence_system) points_index_ps_nin: "\<not> (ps \<subseteq> \<V>) \<Longrightarrow> \<B> index ps = 0"
  using points_index_alt_def filter_mset_empty_conv in_mono size_empty subsetI wf_invalid_point
  by metis 

lemma (in incidence_system) points_index_count_bl: 
    "multiplicity bl \<ge> n \<Longrightarrow> ps \<subseteq> bl \<Longrightarrow> count {#bl \<in># \<B> . ps \<subseteq> bl#} bl \<ge> n"
  by simp

lemma (in finite_incidence_system) points_index_zero: 
  assumes "card ps > card \<V>" 
  shows "\<B> index ps = 0"
proof -
  have "\<And> b. b \<in># \<B> \<Longrightarrow> card ps > card b" 
    using block_size_lt_order card_subset_not_gt_card finite_sets assms by fastforce 
  then have "{#b \<in># \<B> . ps \<subseteq> b#} = {#}"
    by (simp add: card_subset_not_gt_card filter_mset_empty_conv finite_blocks)
  thus ?thesis using points_index_alt_def by simp
qed

lemma (in design) points_index_subset: 
    "x \<subseteq># {#bl \<in># \<B> . ps \<subseteq> bl#} \<Longrightarrow> ps \<subseteq> \<V> \<Longrightarrow> (\<B> index ps) \<ge> (size x)"
  by (simp add: points_index_def size_mset_mono)

lemma (in design) points_index_count_min: "multiplicity bl \<ge> n \<Longrightarrow> ps \<subseteq> bl \<Longrightarrow> \<B> index ps \<ge> n"
  using points_index_alt_def set_count_size_min by (metis filter_mset.rep_eq) 

subsubsection \<open>Intersection Number\<close>

text \<open>The intersection number of two blocks is the size of the intersection of those blocks. i.e. 
the number of points which occur in both blocks\<close>
definition intersection_number :: "'a set \<Rightarrow> 'a set \<Rightarrow> int" (infix "|\<inter>|" 70) where
"b1 |\<inter>| b2 \<equiv> card (b1 \<inter> b2)"

lemma intersection_num_non_neg: "b1 |\<inter>| b2 \<ge> 0"
  by (simp add: intersection_number_def)

lemma intersection_number_empty_iff: 
  assumes "finite b1"
  shows "b1 \<inter> b2 = {} \<longleftrightarrow> b1 |\<inter>| b2 = 0"
  by (simp add: intersection_number_def assms)

lemma intersect_num_commute: "b1 |\<inter>| b2 = b2 |\<inter>| b1"
  by (simp add: inf_commute intersection_number_def) 

definition n_intersect_number :: "'a set \<Rightarrow> nat\<Rightarrow> 'a set \<Rightarrow> int" where
"n_intersect_number b1 n b2 \<equiv> card { x \<in> Pow (b1 \<inter> b2) . card x = n}"

notation n_intersect_number ("(_ |\<inter>|\<^sub>_ _)" [52, 51, 52] 50)

lemma n_intersect_num_subset_def: "b1 |\<inter>|\<^sub>n b2 = card {x . x \<subseteq> b1 \<inter> b2 \<and> card x = n}"
  using n_intersect_number_def by auto

lemma n_inter_num_one: "finite b1 \<Longrightarrow> finite b2 \<Longrightarrow> b1 |\<inter>|\<^sub>1 b2 = b1 |\<inter>| b2"
  using n_intersect_number_def intersection_number_def card_Pow_filter_one
  by (metis (full_types) finite_Int) 

lemma n_inter_num_choose: "finite b1 \<Longrightarrow> finite b2 \<Longrightarrow> b1 |\<inter>|\<^sub>n b2 = (card (b1 \<inter> b2) choose n)" 
  using n_subsets n_intersect_num_subset_def
  by (metis (full_types) finite_Int) 

lemma set_filter_single: "x \<in> A \<Longrightarrow> {a \<in> A . a = x} = {x}"
  by auto 

lemma (in design) n_inter_num_zero: 
  assumes "b1 \<in># \<B>" and "b2 \<in># \<B>"
  shows "b1 |\<inter>|\<^sub>0 b2 = 1"
proof -
  have empty: "\<And>x . finite x \<Longrightarrow> card x = 0 \<Longrightarrow> x = {}"
    by simp
  have empt_in: "{} \<in> Pow (b1 \<inter> b2)" by simp
  have "finite (b1 \<inter> b2)" using finite_blocks assms by simp
  then have "\<And> x . x \<in> Pow (b1 \<inter> b2) \<Longrightarrow> finite x" by (meson PowD finite_subset) 
  then have "{x \<in> Pow (b1 \<inter> b2) . card x = 0} = {x \<in> Pow (b1 \<inter> b2) . x = {}}" 
    using empty by (metis card.empty)
  then have "{x \<in> Pow (b1 \<inter> b2) . card x = 0} = {{}}" 
    by (simp add: empt_in set_filter_single Collect_conv_if)
  thus ?thesis by (simp add: n_intersect_number_def)
qed

lemma (in design) n_inter_num_choose_design: "b1 \<in># \<B> \<Longrightarrow> b2 \<in># \<B> 
    \<Longrightarrow> b1 |\<inter>|\<^sub>n b2 = (card (b1 \<inter> b2) choose n) "
  using finite_blocks by (simp add: n_inter_num_choose)

lemma (in design) n_inter_num_choose_design_inter: "b1 \<in># \<B> \<Longrightarrow> b2 \<in># \<B> 
    \<Longrightarrow> b1 |\<inter>|\<^sub>n b2 = (nat (b1 |\<inter>| b2) choose n) "
  using finite_blocks by (simp add: n_inter_num_choose intersection_number_def)

subsection \<open>Incidence System Set Property Definitions\<close>
context incidence_system
begin

text \<open>The set of replication numbers for all points of design\<close>
definition replication_numbers :: "int set" where
"replication_numbers \<equiv> {\<B> rep x | x . x \<in> \<V>}"

lemma replication_numbers_non_empty: 
  assumes "\<V> \<noteq> {}"
  shows "replication_numbers \<noteq> {}"
  by (simp add: assms replication_numbers_def) 

lemma obtain_point_with_rep: "r \<in> replication_numbers \<Longrightarrow> \<exists> x. x \<in> \<V> \<and> \<B> rep x = r"
  using replication_numbers_def by auto

lemma point_rep_number_in_set: "x \<in> \<V> \<Longrightarrow> (\<B> rep x) \<in> replication_numbers"
  by (auto simp add: replication_numbers_def)

lemma (in finite_incidence_system) replication_numbers_finite: "finite replication_numbers"
  using finite_sets by (simp add: replication_numbers_def)

text \<open>The set of all block sizes in a system\<close>

definition sys_block_sizes :: "int set" where
"sys_block_sizes \<equiv> { (int (card bl)) | bl. bl \<in># \<B>}"

lemma block_sizes_non_empty_set: 
  assumes "\<B> \<noteq> {#}"
  shows "sys_block_sizes \<noteq> {}"
by (simp add: sys_block_sizes_def assms)

lemma finite_block_sizes: "finite (sys_block_sizes)"
  by (simp add: sys_block_sizes_def)

lemma block_sizes_non_empty: 
  assumes "\<B> \<noteq> {#}"
  shows "card (sys_block_sizes) > 0"
  using finite_block_sizes block_sizes_non_empty_set
  by (simp add: assms card_gt_0_iff) 

lemma sys_block_sizes_in: "bl \<in># \<B> \<Longrightarrow> card bl \<in> sys_block_sizes"
  unfolding sys_block_sizes_def by auto 

lemma sys_block_sizes_obtain_bl: "x \<in> sys_block_sizes  \<Longrightarrow> (\<exists> bl \<in># \<B>. int (card bl) = x)"
  by (auto simp add: sys_block_sizes_def)

text \<open>The set of all possible intersection numbers in a system.\<close>

definition intersection_numbers :: "int set" where
"intersection_numbers \<equiv> { b1 |\<inter>| b2 | b1 b2 . b1 \<in># \<B> \<and> b2 \<in># (\<B> - {#b1#})}"

lemma obtain_blocks_intersect_num: "n \<in> intersection_numbers \<Longrightarrow> 
  \<exists> b1 b2. b1 \<in># \<B> \<and> b2 \<in># (\<B> - {#b1#}) \<and>  b1 |\<inter>| b2 = n"
  by (auto simp add: intersection_numbers_def)

lemma intersect_num_in_set: "b1 \<in># \<B> \<Longrightarrow> b2 \<in># (\<B> - {#b1#}) \<Longrightarrow> b1 |\<inter>| b2 \<in> intersection_numbers"
  by (auto simp add: intersection_numbers_def)

text \<open>The set of all possible point indices\<close>
definition point_indices :: "int \<Rightarrow> int set" where
"point_indices t \<equiv> {\<B> index ps | ps. int (card ps) = t \<and> ps \<subseteq> \<V>}"

lemma point_indices_elem_in: "ps \<subseteq> \<V> \<Longrightarrow> card ps = t \<Longrightarrow> \<B> index ps \<in> point_indices t"
  by (auto simp add: point_indices_def)

lemma point_indices_alt_def: "point_indices t = { \<B> index ps | ps. int (card ps) = t \<and> ps \<subseteq> \<V>}"
  by (simp add: point_indices_def)

end

subsection \<open>Basic Constructions on designs\<close>

text \<open>This section defines some of the most common universal constructions found in design theory
involving only a single design\<close>

subsubsection \<open>Design Complements\<close>

context incidence_system
begin

text \<open>The complement of a block are all the points in the design not in that block. 
The complement of a design is therefore the original point sets, and set of all block complements\<close>
definition block_complement:: "'a set \<Rightarrow> 'a set" ("_\<^sup>c" [56] 55) where
"block_complement b \<equiv> \<V> - b"

definition complement_blocks :: "'a set multiset" ("(\<B>\<^sup>C)")where
"complement_blocks \<equiv> {# bl\<^sup>c . bl \<in># \<B> #}" 

lemma block_complement_elem_iff: 
  assumes "ps \<subseteq> \<V>"
  shows "ps \<subseteq> bl\<^sup>c \<longleftrightarrow> (\<forall> x \<in> ps. x \<notin> bl)"
  using assms block_complement_def by (auto)

lemma block_complement_inter_empty: "bl1\<^sup>c = bl2 \<Longrightarrow> bl1 \<inter> bl2 = {}"
  using block_complement_def by auto

lemma block_complement_inv: 
  assumes "bl \<in># \<B>"
  assumes "bl\<^sup>c = bl2"
  shows "bl2\<^sup>c = bl"
  by (metis Diff_Diff_Int assms(1) assms(2) block_complement_def inf.absorb_iff2 wellformed)

lemma block_complement_subset_points: "ps \<subseteq> (bl\<^sup>c) \<Longrightarrow> ps \<subseteq> \<V>"
  using block_complement_def by blast

lemma obtain_comp_block_orig: 
  assumes "bl1 \<in># \<B>\<^sup>C"
  obtains bl2 where "bl2 \<in># \<B>" and "bl1 = bl2\<^sup>c"
  using wellformed assms by (auto simp add: complement_blocks_def)

lemma complement_same_b [simp]: "size \<B>\<^sup>C = size \<B>"
  by (simp add: complement_blocks_def)

lemma block_comp_elem_alt_left: "x \<in> bl \<Longrightarrow> ps \<subseteq> bl\<^sup>c \<Longrightarrow> x \<notin> ps"
  by (auto simp add: block_complement_def block_complement_elem_iff)

lemma block_comp_elem_alt_right: "ps \<subseteq> \<V> \<Longrightarrow> (\<And> x . x \<in> ps \<Longrightarrow> x \<notin> bl) \<Longrightarrow> ps \<subseteq> bl\<^sup>c"
  by (auto simp add: block_complement_elem_iff)

lemma complement_index:
  assumes "ps \<subseteq> \<V>"
  shows "\<B>\<^sup>C index ps = size {# b \<in># \<B> . (\<forall> x \<in> ps . x \<notin> b) #}"
proof -
  have "\<B>\<^sup>C index ps =  size {# b \<in># {# bl\<^sup>c . bl \<in># \<B>#}. ps \<subseteq> b #}"
    by (simp add: complement_blocks_def points_index_def) 
  then have "\<B>\<^sup>C index ps = size {# bl\<^sup>c | bl \<in># \<B> . ps \<subseteq> bl\<^sup>c #}"
    by (metis image_mset_filter_swap)
  thus ?thesis using assms by (simp add: block_complement_elem_iff)
qed

lemma complement_index_2:
  assumes "{x, y} \<subseteq> \<V>"
  shows "\<B>\<^sup>C index {x, y} = size {# b \<in># \<B> . x \<notin> b \<and> y \<notin> b #}"
proof -
  have a: "\<And> b. b \<in># \<B> \<Longrightarrow> \<forall> x' \<in> {x, y} . x' \<notin> b \<Longrightarrow> x \<notin> b \<and> y \<notin> b"
    by simp 
  have "\<And> b. b \<in># \<B> \<Longrightarrow> x \<notin> b \<and> y \<notin> b \<Longrightarrow> \<forall> x' \<in> {x, y} . x' \<notin> b "
    by simp 
  thus ?thesis using assms a complement_index
    by (smt (verit) filter_mset_cong) 
qed

lemma complement_rep_number: 
  assumes "x \<in> \<V>" and "\<B> rep x = r" 
  shows  "\<B>\<^sup>C rep x = \<b> - r"
proof - 
  have r: "size {#b \<in># \<B> . x \<in> b#} = r" using assms by (simp add: point_replication_number_def)
  then have a: "\<And> b . b \<in># \<B> \<Longrightarrow> x \<in> b \<Longrightarrow> x \<notin> b\<^sup>c"
    by (simp add: block_complement_def)
  have "\<And> b . b \<in># \<B> \<Longrightarrow> x \<notin> b \<Longrightarrow> x \<in> b\<^sup>c"
    by (simp add: assms(1) block_complement_def) 
  then have alt: "(image_mset block_complement \<B>) rep x = size {#b \<in># \<B> . x \<notin> b#}" 
    using a filter_mset_cong image_mset_filter_swap2 point_replication_number_def
    by (smt (verit, ccfv_SIG) size_image_mset) 
  have "\<b> = size {#b \<in># \<B> . x \<in> b#} + size {#b \<in># \<B> . x \<notin> b#}"
    by (metis multiset_partition size_union) 
  thus ?thesis using alt
    by (simp add: r complement_blocks_def)
qed

lemma complement_blocks_wf: "bl \<in># \<B>\<^sup>C \<Longrightarrow> bl \<subseteq> \<V>"
  by (auto simp add: complement_blocks_def block_complement_def)

lemma complement_wf [intro]: "incidence_system \<V> \<B>\<^sup>C"
  using complement_blocks_wf by (unfold_locales)

interpretation sys_complement: incidence_system "\<V>" "\<B>\<^sup>C"
  using complement_wf by simp 
end

context finite_incidence_system
begin
lemma block_complement_size: "b \<subseteq> \<V> \<Longrightarrow> card (b\<^sup>c) = card \<V> - card b"
  by (simp add: block_complement_def card_Diff_subset finite_subset card_mono of_nat_diff finite_sets)  

lemma block_comp_incomplete: "incomplete_block bl \<Longrightarrow> card (bl\<^sup>c) > 0"
  using block_complement_size by (simp add: wellformed) 

lemma  block_comp_incomplete_nempty: "incomplete_block bl \<Longrightarrow> bl\<^sup>c \<noteq> {}"
  using wellformed block_complement_def finite_blocks
  by (auto simp add: block_complement_size block_comp_incomplete card_subset_not_gt_card)

lemma incomplete_block_proper_subset: "incomplete_block bl \<Longrightarrow> bl \<subset> \<V>"
  using wellformed by fastforce

lemma complement_finite: "finite_incidence_system \<V> \<B>\<^sup>C"
  using complement_wf finite_sets by (simp add: incidence_system.finite_sysI) 

interpretation comp_fin: finite_incidence_system \<V> "\<B>\<^sup>C"
  using complement_finite by simp 

end

context design
begin
lemma (in design) complement_design: 
  assumes "\<And> bl . bl \<in># \<B> \<Longrightarrow> incomplete_block bl" 
  shows "design \<V> (\<B>\<^sup>C)"
proof -
  interpret fin: finite_incidence_system \<V> "\<B>\<^sup>C" using complement_finite by simp
  show ?thesis using assms block_comp_incomplete_nempty wellformed 
    by (unfold_locales) (auto simp add: complement_blocks_def)
qed

end
subsubsection \<open>Multiples\<close>
text \<open>An easy way to construct new set systems is to simply multiply the block collection by some 
constant\<close>

context incidence_system 
begin

abbreviation multiple_blocks :: "nat \<Rightarrow> 'a set multiset" where
"multiple_blocks n \<equiv> repeat_mset n \<B>"

lemma multiple_block_in_original: "b \<in># multiple_blocks n \<Longrightarrow> b \<in># \<B>"
  by (simp add: elem_in_repeat_in_original) 

lemma multiple_block_in: "n > 0 \<Longrightarrow> b \<in># \<B> \<Longrightarrow>  b \<in># multiple_blocks n"
  by (simp add: elem_in_original_in_repeat)

lemma multiple_blocks_gt: "n > 0 \<Longrightarrow> size (multiple_blocks n) \<ge> size \<B>" 
  by (simp)

lemma block_original_count_le: "n > 0 \<Longrightarrow> count \<B> b \<le> count (multiple_blocks n) b"
  using count_repeat_mset by simp 

lemma multiple_blocks_sub: "n > 0 \<Longrightarrow> \<B> \<subseteq># (multiple_blocks n)"
  by (simp add: mset_subset_eqI block_original_count_le) 

lemma multiple_1_same: "multiple_blocks 1 = \<B>"
  by simp

lemma multiple_unfold_1: "multiple_blocks (Suc n) = (multiple_blocks n) + \<B>"
  by simp

lemma multiple_point_rep_num: "(multiple_blocks n) rep x = (\<B> rep x) * n"
proof (induction n)
  case 0
  then show ?case by (simp add: point_replication_number_def)
next
  case (Suc n)
  then have "multiple_blocks (Suc n) rep x = \<B> rep x * n + (\<B> rep x)"
    using Suc.IH Suc.prems by (simp add: union_commute point_replication_number_def)
  then show ?case
    by (simp add: int_distrib(2)) 
qed

lemma multiple_point_index: "(multiple_blocks n) index ps = (\<B> index ps) * n"
  by (induction n) (auto simp add: points_index_def)

lemma repeat_mset_block_point_rel: "\<And>b x. b \<in># multiple_blocks  n \<Longrightarrow> x \<in> b \<Longrightarrow> x \<in> \<V>"
  by (induction n) (auto, meson subset_iff wellformed)

lemma multiple_is_wellformed: "incidence_system \<V> (multiple_blocks n)"
  using repeat_mset_subset_in wellformed repeat_mset_block_point_rel by (unfold_locales) (auto)

lemma  multiple_blocks_num [simp]: "size (multiple_blocks n) = n*\<b>"
  by simp

interpretation mult_sys: incidence_system \<V> "(multiple_blocks n)"
  by (simp add: multiple_is_wellformed)

lemma multiple_block_multiplicity [simp]: "mult_sys.multiplicity n bl = (multiplicity bl) * n"
  by (simp)

lemma multiple_block_sizes_same: 
  assumes "n > 0" 
  shows "sys_block_sizes = mult_sys.sys_block_sizes n"
proof -
  have def: "mult_sys.sys_block_sizes n = {card bl | bl. bl \<in># (multiple_blocks n)}"
    by (simp add: mult_sys.sys_block_sizes_def) 
  then have eq: "\<And> bl. bl \<in># (multiple_blocks n) \<longleftrightarrow> bl \<in># \<B>"
    using assms multiple_block_in multiple_block_in_original by blast 
  thus ?thesis using def by (simp add: sys_block_sizes_def eq)
qed 

end

context finite_incidence_system
begin

lemma multiple_is_finite: "finite_incidence_system \<V> (multiple_blocks n)"
  using multiple_is_wellformed finite_sets by (unfold_locales) (auto simp add: incidence_system_def)

end

context design
begin

lemma multiple_is_design: "design \<V> (multiple_blocks n)"
proof -
  interpret fis: finite_incidence_system \<V> "multiple_blocks n" using multiple_is_finite by simp
  show ?thesis using blocks_nempty
    by (unfold_locales) (auto simp add: elem_in_repeat_in_original repeat_mset_not_empty)
qed

end

subsection \<open>Simple Designs\<close>

text \<open>Simple designs are those in which the multiplicity of each block is at most one. 
In other words, the block collection is a set. This can significantly ease reasoning.\<close>

locale simple_incidence_system = incidence_system + 
  assumes simple [simp]: "bl \<in># \<B> \<Longrightarrow> multiplicity bl = 1"

begin 

lemma simple_alt_def_all: "\<forall> bl \<in># \<B> . multiplicity bl = 1"
  using simple by auto
  
lemma simple_blocks_eq_sup: "mset_set (design_support) = \<B>"
  using distinct_mset_def simple design_support_def by (metis distinct_mset_set_mset_ident) 

lemma simple_block_size_eq_card: "\<b> = card (design_support)"
  by (metis simple_blocks_eq_sup size_mset_set)

lemma points_index_simple_def: "\<B> index ps = card {b \<in> design_support . ps \<subseteq> b}"
  using design_support_def points_index_def card_size_filter_eq simple_blocks_eq_sup
  by (metis finite_set_mset) 

lemma replication_num_simple_def: "\<B> rep x = card {b \<in> design_support . x \<in> b}"
  using design_support_def point_replication_number_def card_size_filter_eq simple_blocks_eq_sup
  by (metis finite_set_mset) 

end

locale simple_design = design + simple_incidence_system

text \<open>Additional reasoning about when something is not simple\<close>
context incidence_system
begin
lemma simple_not_multiplicity: "b \<in># \<B> \<Longrightarrow> multiplicity  b > 1 \<Longrightarrow> \<not> simple_incidence_system \<V> \<B>"
  using simple_incidence_system_def simple_incidence_system_axioms_def by (metis nat_neq_iff) 

lemma multiple_not_simple: 
  assumes "n > 1"
  assumes "\<B> \<noteq> {#}"
  shows "\<not> simple_incidence_system \<V> (multiple_blocks n)"
proof (rule ccontr, simp)
  assume "simple_incidence_system \<V> (multiple_blocks n)"
  then have "\<And> bl. bl \<in># \<B> \<Longrightarrow> count (multiple_blocks n) bl = 1"
    using assms(1) elem_in_original_in_repeat
    by (metis not_gr_zero not_less_zero simple_incidence_system.simple)
  thus False using assms by auto 
qed

end

subsection \<open>Proper Designs\<close>
text \<open>Many types of designs rely on parameter conditions that only make sense for non-empty designs. 
i.e. designs with at least one block, and therefore given well-formed condition, at least one point. 
To this end we define the notion of a "proper" design\<close>

locale proper_design = design + 
  assumes b_non_zero: "\<b> \<noteq> 0"
begin

lemma is_proper: "proper_design \<V> \<B>" by intro_locales

lemma v_non_zero: "\<v> > 0"
  using b_non_zero v_eq0_imp_b_eq_0 by auto

lemma b_positive: "\<b> > 0" using b_non_zero
  by (simp add: nonempty_has_size)

lemma design_points_nempty: "\<V> \<noteq> {}"
  using v_non_zero by auto 

lemma design_blocks_nempty: "\<B> \<noteq> {#}"
  using b_non_zero by auto

end

text \<open>Intro rules for a proper design\<close>
lemma (in design) proper_designI[intro]: "\<b> \<noteq> 0 \<Longrightarrow> proper_design \<V> \<B>"
  by (unfold_locales) simp

lemma proper_designII[intro]: 
  assumes "design V B" and "B \<noteq> {#}" 
  shows "proper_design V B"
proof -
  interpret des: design V B using assms by simp
  show ?thesis using assms by unfold_locales simp
qed

text \<open>Reasoning on construction closure for proper designs\<close>
context proper_design
begin

lemma multiple_proper_design: 
  assumes "n > 0"
  shows "proper_design \<V> (multiple_blocks n)"
  using multiple_is_design assms design_blocks_nempty multiple_block_in
  by (metis block_set_nempty_imp_block_ex empty_iff proper_designII set_mset_empty) 

lemma complement_proper_design: 
  assumes "\<And> bl . bl \<in># \<B> \<Longrightarrow> incomplete_block bl"
  shows "proper_design \<V> \<B>\<^sup>C"
proof -
  interpret des: design \<V> "\<B>\<^sup>C"
    by (simp add: assms complement_design)  
  show ?thesis using b_non_zero by (unfold_locales) auto
qed

end
end