theory Design_Operations imports Design_Basics
begin

section \<open>Design Operations\<close>
text \<open>Incidence systems have a number of very typical computational operations
which can be used for constructions in design theory. Definitions in this section are based off
the handbook of combinatorial designs, hypergraph theory \cite{bergeHypergraphsCombinatoricsFinite1989}, 
and the GAP design theory library \cite{soicherDesignsGroupsComputing2013}\<close>

subsection \<open>Incidence system definitions\<close>

context incidence_system
begin

text \<open>The basic add point operation only affects the point set of a design\<close>
definition add_point :: "'a \<Rightarrow> 'a set" where
"add_point p \<equiv> insert p \<V>"

lemma add_existing_point [simp]: "p \<in> \<V> \<Longrightarrow> add_point p = \<V>"
  using add_point_def by fastforce

lemma add_point_wf: "incidence_system (add_point p) \<B>"
  using wf_invalid_point add_point_def by (unfold_locales) (auto)

text \<open>An extension of the basic add point operation also adds the point to a given set of blocks\<close>
definition add_point_to_blocks :: "'a \<Rightarrow> 'a set set \<Rightarrow> 'a set multiset" where
"add_point_to_blocks p bs \<equiv> {# (insert p b) | b \<in># \<B> . b \<in> bs#} + {# b \<in># \<B> . b \<notin> bs#}"

lemma add_point_blocks_blocks_alt: "add_point_to_blocks p bs = 
    image_mset (insert p) (filter_mset (\<lambda> b . b \<in> bs) \<B>) + (filter_mset (\<lambda> b . b \<notin> bs) \<B>)"
  using add_point_to_blocks_def by simp

lemma add_point_existing_blocks: 
  assumes "(\<And> bl . bl \<in> bs \<Longrightarrow> p \<in> bl)" 
  shows "add_point_to_blocks p bs = \<B>"
proof (simp add: add_point_to_blocks_def)
  have "image_mset (insert p) {#b \<in># \<B>. b \<in> bs#} = {#b \<in># \<B>. b \<in> bs#}" using assms
    by (simp add: image_filter_cong insert_absorb) 
  thus "image_mset (insert p) {#b \<in># \<B>. b \<in> bs#} + {#b \<in># \<B>. b \<notin> bs#} = \<B>" 
    using multiset_partition by simp 
qed

lemma add_new_point_rep_number: 
  assumes "p \<notin> \<V>"
  shows "(add_point_to_blocks p bs) rep p = size {#b \<in># \<B> . b \<in> bs#}"
proof -
  have "\<And> b. b \<in># \<B> \<Longrightarrow> b \<notin> bs \<Longrightarrow> p \<notin> b"
    by (simp add: assms wf_invalid_point) 
  then have zero: "{# b \<in># \<B> . b \<notin> bs#} rep p = 0"
    by (simp add: filter_mset_empty_conv point_replication_number_def)
  have "(add_point_to_blocks p bs) rep p = {# (insert p b) | b \<in># \<B> . b \<in> bs#} rep p + {# b \<in># \<B> . b \<notin> bs#} rep p"
    by (simp add: add_point_to_blocks_def)
  then have eq: "(add_point_to_blocks p bs) rep p = {# (insert p b) | b \<in># \<B> . b \<in> bs#} rep p"
    using zero by simp
  have "\<And> bl . bl \<in># {# (insert p b) | b \<in># \<B> . b \<in> bs#} \<Longrightarrow> p \<in> bl" by auto
  then have "{# (insert p b) | b \<in># \<B> . b \<in> bs#} rep p = size {# (insert p b) | b \<in># \<B> . b \<in> bs#}"
    using point_replication_number_def by (metis filter_mset_True filter_mset_cong) 
  thus ?thesis by (simp add: eq) 
qed

lemma add_point_blocks_wf: "incidence_system (add_point p) (add_point_to_blocks p bs)"
  by (unfold_locales) (auto simp add: add_point_def wf_invalid_point add_point_to_blocks_def)

text \<open>Basic (weak) delete point operation removes a point from both the point set and from any 
blocks that contain it to maintain wellformed property\<close>
definition del_point :: "'a \<Rightarrow> 'a set" where
"del_point p \<equiv> \<V> - {p}" 

definition del_point_blocks:: "'a \<Rightarrow> 'a set multiset" where
"del_point_blocks p \<equiv> {# (bl - {p}) . bl \<in># \<B> #}"

lemma del_point_block_count: "size (del_point_blocks p) = size \<B>"
  by (simp add: del_point_blocks_def)

lemma remove_invalid_point_block: "p \<notin> \<V> \<Longrightarrow> bl \<in># \<B> \<Longrightarrow> bl - {p} = bl"
  using wf_invalid_point by blast

lemma del_invalid_point: "p \<notin> \<V> \<Longrightarrow> (del_point p) = \<V>"
  by (simp add: del_point_def)

lemma del_invalid_point_blocks: "p \<notin> \<V> \<Longrightarrow> (del_point_blocks p) = \<B>"
  using del_invalid_point
  by (auto simp add: remove_invalid_point_block del_point_blocks_def) 

lemma delete_point_p_not_in_bl_blocks: "(\<And> bl. bl \<in># \<B> \<Longrightarrow> p \<notin> bl) \<Longrightarrow> (del_point_blocks p) = \<B>"
  by (simp add: del_point_blocks_def)

lemma delete_point_blocks_wf: "b \<in># (del_point_blocks p) \<Longrightarrow> b \<subseteq> \<V> - {p}"
  unfolding del_point_blocks_def using wellformed by auto

lemma delete_point_blocks_sub: 
  assumes "b \<in># (del_point_blocks p)" 
  obtains bl where "bl \<in># \<B> \<and> b \<subseteq> bl"
  using assms by (auto simp add: del_point_blocks_def)

lemma delete_point_split_blocks: "del_point_blocks p = 
  {# bl \<in>#\<B> . p \<notin> bl#} + {# bl - {p} | bl \<in># \<B> . p \<in> bl#}"
proof -
  have sm: "\<And> bl . p \<notin> bl \<Longrightarrow> bl - {p} = bl" by simp 
  have "del_point_blocks p = {# (bl - {p}) . bl \<in># \<B> #}" by (simp add: del_point_blocks_def)
  also have "... = {# (bl - {p}) | bl \<in># \<B> . p \<notin> bl #} + {# (bl - {p}) | bl \<in># \<B> . p \<in> bl #}"
    using multiset_partition by (metis image_mset_union union_commute) 
  finally have "del_point_blocks p = {#bl | bl \<in># \<B> . p \<notin> bl#} + 
      {# (bl - {p}) | bl \<in># \<B> . p \<in> bl #}"
    using sm mem_Collect_eq
    by (metis (mono_tags, lifting) Multiset.set_mset_filter  multiset.map_cong) 
  thus ?thesis by simp
qed

lemma delete_point_index_eq: 
  assumes "ps \<subseteq> (del_point p)"
  shows "(del_point_blocks p) index ps = \<B> index ps"
proof -
  have eq: "filter_mset ((\<subseteq>) ps) {#bl - {p}. bl \<in># \<B>#} = 
      image_mset (\<lambda> b . b - {p}) (filter_mset (\<lambda> b. ps \<subseteq> b - {p}) \<B>)"
    using filter_mset_image_mset by blast
  have "p \<notin> ps" using assms del_point_def by blast 
  then have "\<And> bl . ps \<subseteq> bl \<longleftrightarrow> ps \<subseteq> bl - {p}" by blast
  then have "((filter_mset (\<lambda> b. ps \<subseteq> b - {p}) \<B>)) = (filter_mset (\<lambda> b . ps \<subseteq> b) \<B>)" by auto 
  then have "size (image_mset (\<lambda> b . b - {p}) (filter_mset (\<lambda> b. ps \<subseteq> b - {p}) \<B>)) 
      = \<B> index ps" 
    by (simp add: points_index_def) 
  thus ?thesis using eq
    by (simp add: del_point_blocks_def points_index_def) 
qed

lemma delete_point_wf: "incidence_system (del_point p) (del_point_blocks p)"
  using delete_point_blocks_wf del_point_def by (unfold_locales) auto

text \<open>The concept of a strong delete point comes from hypergraph theory. When a point is deleted, 
any blocks containing it are also deleted\<close>
definition str_del_point_blocks :: "'a \<Rightarrow> 'a set multiset" where
"str_del_point_blocks p \<equiv> {# bl \<in># \<B> . p \<notin> bl#}"

lemma str_del_point_blocks_alt: "str_del_point_blocks p = \<B> - {# bl \<in># \<B> . p \<in> bl#}"  
  using add_diff_cancel_left' multiset_partition by (metis str_del_point_blocks_def) 

lemma delete_point_strong_block_in:  "p \<notin> bl \<Longrightarrow> bl \<in># \<B>  \<Longrightarrow> bl \<in># str_del_point_blocks p"
  by (simp add: str_del_point_blocks_def)

lemma delete_point_strong_block_not_in: "p \<in> bl \<Longrightarrow> bl \<notin># (str_del_point_blocks) p"
  by (simp add: str_del_point_blocks_def)

lemma delete_point_strong_block_in_iff: "bl \<in># \<B> \<Longrightarrow> bl \<in># str_del_point_blocks p \<longleftrightarrow> p \<notin> bl"
  using delete_point_strong_block_in delete_point_strong_block_not_in
  by (simp add: str_del_point_blocks_def)

lemma delete_point_strong_block_subset: "str_del_point_blocks p \<subseteq># \<B>"
  by (simp add: str_del_point_blocks_def)

lemma delete_point_strong_block_in_orig: "bl \<in># str_del_point_blocks p \<Longrightarrow> bl \<in># \<B>"
  using delete_point_strong_block_subset by (metis mset_subset_eqD) 

lemma delete_invalid_pt_strong_eq: "p \<notin> \<V> \<Longrightarrow> \<B> = str_del_point_blocks p"
  unfolding str_del_point_blocks_def using wf_invalid_point empty_iff
  by (metis Multiset.diff_cancel filter_mset_eq_conv set_mset_empty subset_mset.order_refl)

lemma strong_del_point_index_alt: 
  assumes "ps \<subseteq> (del_point p)"
  shows "(str_del_point_blocks p) index ps = 
    \<B> index ps - {# bl \<in># \<B> . p \<in> bl#} index ps"
  using str_del_point_blocks_alt points_index_def
  by (metis filter_diff_mset multiset_filter_mono multiset_filter_subset  size_Diff_submset)

lemma strong_del_point_incidence_wf: "incidence_system (del_point p) (str_del_point_blocks p)"
  using wellformed str_del_point_blocks_def del_point_def by (unfold_locales) auto

text \<open>Add block operation\<close>

definition add_block :: "'a set \<Rightarrow> 'a set multiset" where 
"add_block b \<equiv> \<B> + {#b#}"

lemma add_block_alt: "add_block b = add_mset b \<B>"
  by (simp add: add_block_def)

lemma add_block_rep_number_in: 
  assumes "x \<in> b"
  shows "(add_block b) rep x = \<B> rep x + 1"
proof -
  have "(add_block b) = {#b#} + \<B>" by (simp add: add_block_def) 
  then have split: "(add_block b) rep x = {#b#} rep x + \<B> rep x"
    by (metis point_rep_number_split)
  have "{#b#} rep x = 1" using assms by simp
  thus ?thesis using split by auto
qed

lemma add_block_rep_number_not_in: "x \<notin> b \<Longrightarrow> (add_block b) rep x = \<B> rep x"
  using point_rep_number_split add_block_alt point_rep_singleton_inval
  by (metis add.right_neutral union_mset_add_mset_right)

lemma add_block_index_in: 
  assumes "ps \<subseteq> b"
  shows "(add_block b) index ps = \<B> index ps + 1"
proof -
  have "(add_block b) = {#b#} + \<B>" by (simp add: add_block_def) 
  then have split: "(add_block b) index ps = {#b#} index ps + \<B> index ps"
    by (metis point_index_distrib)
  have "{#b#} index ps = 1" using assms points_index_singleton by auto
  thus ?thesis using split by simp
qed

lemma add_block_index_not_in: "\<not> (ps \<subseteq> b) \<Longrightarrow> (add_block b) index ps = \<B> index ps"
  using point_index_distrib points_index_singleton_zero
  by (metis add.right_neutral add_block_def)

text \<open>Note the add block incidence system is defined slightly differently then textbook 
definitions due to the modification to the point set. This ensures the operation is closed, 
where otherwise a condition that $b \subseteq \mathcal{V}$ would be required.\<close>
lemma add_block_wf: "incidence_system (\<V> \<union> b) (add_block b)"
  using wellformed add_block_def by (unfold_locales) auto

lemma add_block_wf_cond: "b \<subseteq> \<V> \<Longrightarrow> incidence_system \<V> (add_block b)"
  using add_block_wf by (metis sup.order_iff) 

text \<open>Delete block removes a block from the block set. The point set is unchanged\<close>
definition del_block :: "'a set \<Rightarrow> 'a set multiset" where
"del_block b \<equiv> \<B> - {#b#}"

lemma delete_block_subset: "(del_block b) \<subseteq># \<B>"
  by (simp add: del_block_def)

lemma delete_invalid_block_eq: "b \<notin># \<B> \<Longrightarrow> del_block b = \<B>"
  by (simp add: del_block_def)

lemma delete_block_wf: "incidence_system \<V> (del_block b)"
  by (unfold_locales) (simp add: del_block_def in_diffD wellformed) 

text \<open>The strong delete block operation effectively deletes the block, as well as 
all points in that block\<close>
definition str_del_block :: "'a set \<Rightarrow> 'a set multiset" where
"str_del_block b \<equiv> {# bl - b | bl \<in># \<B> . bl \<noteq> b #}"

lemma strong_del_block_alt_def: "str_del_block b = {# bl - b . bl \<in># removeAll_mset b \<B> #}"
  by (simp add: filter_mset_neq str_del_block_def)

lemma strong_del_block_wf: "incidence_system (\<V> - b) (str_del_block b)"
  using wf_invalid_point str_del_block_def by (unfold_locales) auto

lemma str_del_block_del_point: 
  assumes "{x} \<notin># \<B>"
  shows "str_del_block {x} = (del_point_blocks x)"
proof -
  have neqx: "\<And> bl. bl \<in># \<B> \<Longrightarrow> bl \<noteq> {x}" using assms by auto
  have "str_del_block {x} = {# bl - {x} | bl \<in># \<B> . bl \<noteq> {x} #}" by (simp add: str_del_block_def)
  then have "str_del_block {x} = {# bl - {x} . bl \<in># \<B> #}" using assms neqx
    by (simp add: filter_mset_cong) 
  thus ?thesis by (simp add: del_point_blocks_def)
qed

subsection \<open>Incidence System Interpretations\<close>
text \<open>It is easy to interpret all operations as incidence systems in there own right. 
These can then be used to prove local properties on the new constructions, as well 
as reason on interactions between different operation sequences\<close>

interpretation add_point_sys: incidence_system "add_point p" "\<B>"
  using add_point_wf by simp

lemma add_point_sys_rep_numbers: "add_point_sys.replication_numbers p = 
    replication_numbers \<union> {\<B> rep p}"
  using add_point_sys.replication_numbers_def replication_numbers_def add_point_def by auto

interpretation del_point_sys: incidence_system "del_point p" "del_point_blocks p"
  using delete_point_wf by auto

interpretation add_block_sys: incidence_system "\<V> \<union> bl" "add_block bl"
  using add_block_wf by simp

interpretation del_block_sys: incidence_system "\<V>" "del_block bl"
  using delete_block_wf by simp 

lemma add_del_block_inv: 
  assumes "bl \<subseteq> \<V>"
  shows "add_block_sys.del_block bl bl = \<B>"
  using add_block_sys.del_block_def add_block_def by simp

lemma del_add_block_inv: "bl \<in># \<B> \<Longrightarrow> del_block_sys.add_block bl bl = \<B>"
  using del_block_sys.add_block_def del_block_def wellformed by fastforce

lemma del_invalid_add_block_eq: "bl \<notin># \<B> \<Longrightarrow> del_block_sys.add_block bl bl = add_block bl"
  using del_block_sys.add_block_def by (simp add: delete_invalid_block_eq) 

lemma add_delete_point_inv: 
  assumes "p \<notin> \<V>"
  shows "add_point_sys.del_point p p = \<V>"
proof -
  have "(add_point_sys.del_point p p) = (insert p \<V>) - {p}"
    using add_point_sys.del_point_def del_block_sys.add_point_def by auto 
  thus ?thesis 
    by (simp add: assms) 
qed
end

subsection \<open>Operation Closure for Designs\<close>

context finite_incidence_system 
begin

lemma add_point_finite: "finite_incidence_system (add_point p) \<B>"
  using add_point_wf finite_sets add_point_def 
  by (unfold_locales) (simp_all add: incidence_system_def)

lemma add_point_to_blocks_finite: "finite_incidence_system (add_point p) (add_point_to_blocks p bs)"
  using add_point_blocks_wf add_point_finite finite_incidence_system.finite_sets 
    incidence_system.finite_sysI by blast

lemma delete_point_finite: 
    "finite_incidence_system (del_point p) (del_point_blocks p)"
  using finite_sets delete_point_wf 
  by (unfold_locales) (simp_all add: incidence_system_def del_point_def)

lemma del_point_order: 
  assumes "p \<in> \<V>"
  shows "card (del_point p) = \<v> - 1"
proof -
  have vg0: "card \<V> > 0" using assms finite_sets card_gt_0_iff by auto 
  then have "card (del_point p) = card \<V> - 1" using assms del_point_def
    by (metis card_Diff_singleton finite_sets)
  thus ?thesis
    using vg0 by linarith 
qed

lemma strong_del_point_finite:"finite_incidence_system (del_point p) (str_del_point_blocks p)"
  using strong_del_point_incidence_wf del_point_def
  by (intro_locales) (simp_all add: finite_incidence_system_axioms_def finite_sets)

lemma add_block_fin: "finite b \<Longrightarrow> finite_incidence_system (\<V> \<union> b) (add_block b)"
  using wf_invalid_point finite_sets add_block_def by (unfold_locales) auto

lemma add_block_fin_cond: "b \<subseteq> \<V> \<Longrightarrow> finite_incidence_system \<V> (add_block b)"
  using add_block_wf_cond finite_incidence_system_axioms.intro finite_sets
  by (intro_locales) (simp_all)

lemma delete_block_fin_incidence_sys: "finite_incidence_system \<V> (del_block b)"
  using delete_block_wf finite_sets by (unfold_locales) (simp_all add: incidence_system_def)

lemma strong_del_block_fin: "finite_incidence_system (\<V> - b) (str_del_block b)"
  using strong_del_block_wf finite_sets finite_incidence_system_axioms_def by (intro_locales) auto

end

context design
begin
lemma add_point_design: "design (add_point p) \<B>"
  using add_point_wf finite_sets blocks_nempty add_point_def
  by (unfold_locales) (auto simp add: incidence_system_def)

lemma delete_point_design: 
  assumes "(\<And> bl . bl \<in># \<B> \<Longrightarrow> p \<in> bl \<Longrightarrow> card bl \<ge> 2)"
  shows "design (del_point p) (del_point_blocks p)"
proof (cases "p \<in> \<V>")
  case True
  interpret fis: finite_incidence_system "(del_point p)" "(del_point_blocks p)" 
    using delete_point_finite by simp
  show ?thesis 
  proof (unfold_locales)
    show "\<And>bl. bl \<in># (del_point_blocks p) \<Longrightarrow> bl \<noteq> {}" using assms del_point_def 
    proof -
      fix bl 
      assume "bl \<in>#(del_point_blocks p)"
      then obtain bl' where block: "bl' \<in># \<B>" and rem: "bl = bl' - {p}" 
        by (auto simp add: del_point_blocks_def)
      then have eq: "p \<notin> bl' \<Longrightarrow> bl \<noteq> {}" using block blocks_nempty by (simp add: rem) 
      have "p \<in> bl' \<Longrightarrow> card bl \<ge> 1" using rem finite_blocks block assms block by fastforce  
      then show "bl \<noteq> {}" using  eq assms by fastforce 
    qed 
  qed
next
  case False
  then show ?thesis using del_invalid_point del_invalid_point_blocks
    by (simp add: wf_design) 
qed

lemma strong_del_point_design: "design (del_point p) (str_del_point_blocks p)"
proof -
  interpret fin: finite_incidence_system "(del_point p)" "(str_del_point_blocks p)"
    using strong_del_point_finite by simp
  show ?thesis using wf_design wf_design_iff del_point_def str_del_point_blocks_def 
    by (unfold_locales) (auto)
qed

lemma add_block_design: 
  assumes "finite bl" 
  assumes "bl \<noteq> {}" 
  shows "design (\<V> \<union> bl) (add_block bl)"
proof - 
  interpret fin: finite_incidence_system "(\<V> \<union> bl)" "(add_block bl)" 
    using add_block_fin assms by simp
  show ?thesis using blocks_nempty assms add_block_def by (unfold_locales) auto
qed

lemma add_block_design_cond: 
  assumes "bl \<subseteq> \<V>" and "bl \<noteq> {}"
  shows "design \<V> (add_block bl)"
proof -
  interpret fin: finite_incidence_system "\<V>" "(add_block bl)" 
    using add_block_fin_cond assms by simp
  show ?thesis using blocks_nempty assms add_block_def by (unfold_locales) auto
qed

lemma delete_block_design: "design \<V> (del_block bl)"
proof -
  interpret fin: finite_incidence_system \<V> "(del_block bl)" 
    using delete_block_fin_incidence_sys by simp
  have "\<And> b . b \<in># (del_block bl) \<Longrightarrow> b \<noteq> {}"
    using blocks_nempty delete_block_subset by blast  
  then show ?thesis by (unfold_locales) (simp_all)
qed

lemma strong_del_block_des: 
  assumes "\<And> bl . bl \<in># \<B> \<Longrightarrow> \<not> (bl \<subset> b)"
  shows "design (\<V> - b) (str_del_block b)"
proof -
  interpret fin: finite_incidence_system "\<V> - b" "(str_del_block b)"
    using strong_del_block_fin by simp
  show ?thesis using assms str_del_block_def by (unfold_locales) auto
qed

end

context proper_design
begin
lemma delete_point_proper: 
  assumes "\<And>bl. bl \<in># \<B> \<Longrightarrow> p \<in> bl \<Longrightarrow> 2 \<le> card bl"
  shows "proper_design (del_point p) (del_point_blocks p)"
proof -
  interpret des: design "del_point p" "del_point_blocks p"
    using delete_point_design assms by blast 
  show ?thesis using design_blocks_nempty del_point_def del_point_blocks_def 
    by (unfold_locales) simp
qed

lemma strong_delete_point_proper: 
  assumes "\<And>bl. bl \<in># \<B> \<Longrightarrow> p \<in> bl \<Longrightarrow> 2 \<le> card bl"
  assumes "\<B> rep p < \<b>"
  shows "proper_design (del_point p) (str_del_point_blocks p)"
proof -
  interpret des: design "del_point p" "str_del_point_blocks p"
    using strong_del_point_design assms by blast 
  show ?thesis using assms design_blocks_nempty point_rep_num_inv_non_empty 
    str_del_point_blocks_def del_point_def by (unfold_locales) simp
qed

end

subsection \<open>Combining Set Systems\<close>
text \<open>Similar to multiple, another way to construct a new set system is to combine two existing ones.
We introduce a new locale enabling us to reason on two different incidence systems\<close>
locale two_set_systems = sys1: incidence_system \<V> \<B> + sys2: incidence_system \<V>' \<B>'
  for \<V> :: "('a set)" and \<B> and \<V>' :: "('a set)" and \<B>'
begin 

abbreviation "combine_points \<equiv> \<V> \<union> \<V>'" 

notation combine_points ("\<V>\<^sup>+")

abbreviation "combine_blocks \<equiv> \<B> + \<B>'"

notation combine_blocks ("\<B>\<^sup>+")

sublocale combine_sys: incidence_system "\<V>\<^sup>+" "\<B>\<^sup>+"
  using sys1.wellformed sys2.wellformed by (unfold_locales) auto

lemma combine_points_index: "\<B>\<^sup>+ index ps = \<B> index ps  + \<B>' index ps"
  by (simp add: point_index_distrib)

lemma combine_rep_number: "\<B>\<^sup>+ rep x = \<B> rep x + \<B>' rep x"
  by (simp add: point_replication_number_def)

lemma combine_multiple1: "\<V> = \<V>' \<Longrightarrow> \<B> = \<B>' \<Longrightarrow> \<B>\<^sup>+ = sys1.multiple_blocks 2"
  by auto

lemma combine_multiple2: "\<V> = \<V>' \<Longrightarrow> \<B> = \<B>' \<Longrightarrow> \<B>\<^sup>+ = sys2.multiple_blocks 2"
  by auto

lemma combine_multiplicity: "combine_sys.multiplicity b = sys1.multiplicity b + sys2.multiplicity b"
  by simp

lemma combine_block_sizes: "combine_sys.sys_block_sizes = 
    sys1.sys_block_sizes \<union> sys2.sys_block_sizes"
  using sys1.sys_block_sizes_def sys2.sys_block_sizes_def combine_sys.sys_block_sizes_def by (auto)

end

locale two_fin_set_systems = two_set_systems \<V> \<B> \<V>' \<B>' + sys1: finite_incidence_system \<V> \<B> + 
  sys2: finite_incidence_system \<V>' \<B>' for \<V> \<B> \<V>' \<B>'
begin
  

sublocale combine_fin_sys: finite_incidence_system "\<V>\<^sup>+" "\<B>\<^sup>+"
  using sys1.finite_sets sys2.finite_sets by (unfold_locales) (simp)

lemma combine_order: "card (\<V>\<^sup>+) \<ge> card \<V>"
  by (meson Un_upper1 card_mono combine_fin_sys.finite_sets)

lemma  combine_order_2: "card (\<V>\<^sup>+) \<ge> card \<V>'"
  by (meson Un_upper2 card_mono combine_fin_sys.finite_sets) 

end

locale two_designs = two_fin_set_systems \<V> \<B> \<V>' \<B>' + des1: design \<V> \<B> + 
  des2: design \<V>' \<B>' for \<V> \<B> \<V>' \<B>'
begin

sublocale combine_des: design "\<V>\<^sup>+" "\<B>\<^sup>+"
  apply (unfold_locales)
  using des1.blocks_nempty_alt des2.blocks_nempty_alt by fastforce

end

locale two_designs_proper = two_designs + 
  assumes blocks_nempty: "\<B> \<noteq> {#} \<or> \<B>' \<noteq> {#}"
begin

lemma des1_is_proper: "\<B> \<noteq> {#} \<Longrightarrow> proper_design \<V> \<B>"
  by (unfold_locales) (simp)

lemma des2_is_proper: "\<B>' \<noteq> {#} \<Longrightarrow> proper_design \<V>' \<B>'"
  by (unfold_locales) (simp)

lemma min_one_proper_design: "proper_design \<V> \<B> \<or> proper_design \<V>' \<B>'"
  using blocks_nempty des1_is_proper des2_is_proper by (unfold_locales, blast)

sublocale combine_proper_des: proper_design "\<V>\<^sup>+" "\<B>\<^sup>+"
  apply (unfold_locales)
  by (metis blocks_nempty of_nat_0_eq_iff size_eq_0_iff_empty subset_mset.zero_eq_add_iff_both_eq_0)
end

end