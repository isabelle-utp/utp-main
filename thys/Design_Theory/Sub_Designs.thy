(* Title: Sub_Designs.thy 
   Author: Chelsea Edmonds
*)

section \<open>Sub-designs\<close>
text \<open>Sub designs are a relationship between two designs using the subset and submultiset relations
This theory defines the concept at the incidence system level, before extending to defining on 
well defined designs\<close>

theory Sub_Designs imports Design_Operations
begin

subsection \<open>Sub-system and Sub-design Locales\<close>
locale sub_set_system = incidence_system \<V> \<B> 
  for "\<U>" and "\<A>" and "\<V>" and "\<B>" + 
  assumes points_subset: "\<U> \<subseteq> \<V>"
  assumes blocks_subset: "\<A> \<subseteq># \<B>"
begin

lemma sub_points: "x \<in> \<U> \<Longrightarrow> x \<in> \<V>"
  using points_subset by auto 

lemma sub_blocks: "bl \<in># \<A> \<Longrightarrow> bl \<in># \<B>"
  using blocks_subset by auto

lemma sub_blocks_count: "count \<A> b \<le> count \<B> b"
  by (simp add: mset_subset_eq_count blocks_subset)

end

locale sub_incidence_system = sub_set_system + ins: incidence_system \<U> \<A>

locale sub_design = sub_incidence_system + des: design \<V> \<B>
begin 

lemma sub_non_empty_blocks: "A \<in># \<A> \<Longrightarrow> A \<noteq> {}"
  using des.blocks_nempty sub_blocks by simp 

sublocale sub_des: design \<U> \<A>
  using des.finite_sets finite_subset points_subset sub_non_empty_blocks 
  by (unfold_locales) (auto)

end

locale proper_sub_set_system = incidence_system \<V> \<B> 
  for "\<U>" and "\<A>" and "\<V>" and "\<B>" + 
  assumes points_psubset: "\<U> \<subset> \<V>"
  assumes blocks_subset: "\<A> \<subseteq># \<B>"
begin

lemma point_sets_ne: "\<U> \<noteq> \<V>"
  using points_psubset by auto

end

sublocale proper_sub_set_system \<subseteq> sub_set_system 
  using points_psubset blocks_subset by (unfold_locales) simp_all

context sub_set_system
begin

lemma sub_is_proper: "\<U> \<noteq> \<V> \<Longrightarrow> proper_sub_set_system \<U> \<A> \<V> \<B>"
  using blocks_subset incidence_system_axioms
  by (simp add: points_subset proper_sub_set_system.intro proper_sub_set_system_axioms_def psubsetI)

end

locale proper_sub_incidence_system = proper_sub_set_system + ins: incidence_system \<U> \<A>

sublocale proper_sub_incidence_system \<subseteq> sub_incidence_system 
  by (unfold_locales)

context sub_incidence_system
begin
lemma sub_is_proper: "\<U> \<noteq> \<V> \<Longrightarrow> proper_sub_incidence_system \<U> \<A> \<V> \<B>"
  by (simp add: ins.incidence_system_axioms proper_sub_incidence_system_def sub_is_proper)

end

locale proper_sub_design = proper_sub_incidence_system + des: design \<V> \<B>

sublocale proper_sub_design \<subseteq> sub_design
  by (unfold_locales)

context sub_design
begin
lemma sub_is_proper: "\<U> \<noteq> \<V> \<Longrightarrow> proper_sub_design \<U> \<A> \<V> \<B>"
  by (simp add: des.wf_design proper_sub_design.intro sub_is_proper)

end

lemma ss_proper_implies_sub [intro]: "proper_sub_set_system \<U> \<A> \<V> \<B> \<Longrightarrow> sub_set_system \<U> \<A> \<V> \<B>"
  using proper_sub_set_system.axioms(1) proper_sub_set_system.blocks_subset psubsetE
  by (metis proper_sub_set_system.points_psubset sub_set_system.intro sub_set_system_axioms_def)

lemma sub_ssI [intro!]: "incidence_system \<V> \<B> \<Longrightarrow> \<U> \<subseteq> \<V> \<Longrightarrow> \<A> \<subseteq># \<B> \<Longrightarrow> sub_set_system \<U> \<A> \<V> \<B>"
  using incidence_system_def subset_iff 
  by (unfold_locales) (simp_all add: incidence_system.wellformed)

lemma sub_ss_equality: 
  assumes "sub_set_system \<U> \<A> \<V> \<B>"
    and "sub_set_system \<V> \<B> \<U> \<A>"
  shows "\<U> = \<V>" and "\<A> = \<B>"
  using assms(1) assms(2) sub_set_system.points_subset apply blast
  by (meson assms(1) assms(2) sub_set_system.blocks_subset subset_mset.eq_iff)

subsection \<open>Reasoning on Sub-designs\<close>

subsubsection \<open>Reasoning on Incidence Sys property relationships\<close>

context sub_incidence_system
begin

lemma sub_sys_block_sizes: "ins.sys_block_sizes \<subseteq> sys_block_sizes"
  by (auto simp add: sys_block_sizes_def ins.sys_block_sizes_def blocks_subset sub_blocks)

lemma sub_point_rep_number_le: "x \<in> \<U> \<Longrightarrow> \<A> rep x \<le> \<B> rep x"
  by (simp add: point_replication_number_def blocks_subset multiset_filter_mono size_mset_mono)

lemma sub_point_index_le: "ps \<subseteq> \<U> \<Longrightarrow> \<A> index ps \<le> \<B> index ps"
  by (simp add: points_index_def blocks_subset multiset_filter_mono size_mset_mono)

lemma sub_sys_intersection_numbers: "ins.intersection_numbers \<subseteq> intersection_numbers"
  apply (auto simp add: intersection_numbers_def ins.intersection_numbers_def)
  by (metis blocks_subset insert_DiffM insert_subset_eq_iff)

end

subsubsection \<open>Reasoning on Incidence Sys/Design operations\<close>
context incidence_system
begin

lemma sub_set_sysI[intro]: "\<U> \<subseteq> \<V> \<Longrightarrow> \<A> \<subseteq># \<B> \<Longrightarrow> sub_set_system \<U> \<A> \<V> \<B>"
  by (simp add: sub_ssI incidence_system_axioms) 

lemma sub_inc_sysI[intro]: "incidence_system \<U> \<A> \<Longrightarrow> \<U> \<subseteq> \<V> \<Longrightarrow> \<A> \<subseteq># \<B> \<Longrightarrow> 
    sub_incidence_system \<U> \<A> \<V> \<B>"
  by (simp add: sub_incidence_system.intro sub_set_sysI)

lemma multiple_orig_sub_system: 
  assumes "n > 0"
  shows "sub_incidence_system \<V> \<B> \<V> (multiple_blocks n)"
  using multiple_block_in_original wellformed multiple_blocks_sub assms 
  by (unfold_locales) simp_all

lemma add_point_sub_sys: "sub_incidence_system \<V> \<B> (add_point p) \<B>"
  using add_point_wf add_point_def
  by (simp add: sub_ssI subset_insertI incidence_system_axioms sub_incidence_system.intro) 

lemma strong_del_point_sub_sys: "sub_incidence_system (del_point p) (str_del_point_blocks p) \<V> \<B> "
  using strong_del_point_incidence_wf wf_invalid_point del_point_def str_del_point_blocks_def 
  by (unfold_locales) (auto)

lemma add_block_sub_sys: "sub_incidence_system \<V> \<B> (\<V> \<union> b) (add_block b)"
  using add_block_wf wf_invalid_point add_block_def by (unfold_locales) (auto)

lemma delete_block_sub_sys: "sub_incidence_system \<V> (del_block b)  \<V> \<B> "
  using delete_block_wf delete_block_subset incidence_system_def by (unfold_locales, auto)
                       
end

lemma (in two_set_systems) combine_sub_sys: "sub_incidence_system \<V> \<B> \<V>\<^sup>+ \<B>\<^sup>+"
  by (unfold_locales) (simp_all)

lemma (in two_set_systems) combine_sub_sys_alt: "sub_incidence_system \<V>' \<B>' \<V>\<^sup>+ \<B>\<^sup>+"
  by (unfold_locales) (simp_all)

context design
begin

lemma sub_designI [intro]: "design \<U> \<A> \<Longrightarrow> sub_incidence_system \<U> \<A> \<V> \<B> \<Longrightarrow> sub_design \<U> \<A> \<V> \<B>"
  by (simp add: sub_design.intro wf_design)

lemma sub_designII [intro]: "design \<U> \<A> \<Longrightarrow> sub_incidence_system \<V> \<B> \<U> \<A> \<Longrightarrow> sub_design \<V> \<B> \<U> \<A>"
  by (simp add: sub_design_def)

lemma multiple_orig_sub_des: 
  assumes "n > 0"
  shows "sub_design \<V> \<B> \<V> (multiple_blocks n)"
  using multiple_is_design assms multiple_orig_sub_system by (simp add: sub_design.intro) 

lemma add_point_sub_des: "sub_design \<V> \<B> (add_point p) \<B>"
  using add_point_design add_point_sub_sys sub_design.intro by fastforce 

lemma strong_del_point_sub_des: "sub_design (del_point p) (str_del_point_blocks p) \<V> \<B> "
  using strong_del_point_sub_sys sub_design.intro wf_design by blast 

lemma add_block_sub_des: "finite b \<Longrightarrow> b \<noteq> {} \<Longrightarrow> sub_design \<V> \<B> (\<V> \<union> b) (add_block b)"
  using add_block_sub_sys add_block_design sub_designII by fastforce

lemma delete_block_sub_des: "sub_design \<V> (del_block b) \<V> \<B> "
  using delete_block_design delete_block_sub_sys sub_designI by auto 

end

lemma (in two_designs) combine_sub_des: "sub_design \<V> \<B> \<V>\<^sup>+ \<B>\<^sup>+"
  by (unfold_locales) (simp_all)

lemma (in two_designs) combine_sub_des_alt: "sub_design \<V>' \<B>' \<V>\<^sup>+ \<B>\<^sup>+"
  by (unfold_locales) (simp_all)

end