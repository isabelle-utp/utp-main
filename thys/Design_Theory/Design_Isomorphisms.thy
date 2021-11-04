(* Title: Design_Isomorphisms
   Author: Chelsea Edmonds 
*)

section \<open>Design Isomorphisms\<close>

theory Design_Isomorphisms imports Design_Basics Sub_Designs
begin

subsection \<open>Images of Set Systems\<close>

text \<open>We loosely define the concept of taking the "image" of a set system, as done in isomorphisms. 
Note that this is not based off mathematical theory, but is for ease of notation\<close>
definition blocks_image :: "'a set multiset \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b set multiset" where
"blocks_image B f \<equiv> image_mset ((`) f) B"

lemma image_block_set_constant_size: "size (B) = size (blocks_image B f)"
  by (simp add: blocks_image_def)

lemma (in incidence_system) image_set_system_wellformed: 
  "incidence_system (f ` \<V>) (blocks_image \<B> f)"
  by (unfold_locales, auto simp add: blocks_image_def) (meson image_eqI wf_invalid_point)

lemma (in finite_incidence_system) image_set_system_finite: 
  "finite_incidence_system (f ` \<V>) (blocks_image \<B> f)"
  using image_set_system_wellformed finite_sets 
  by (intro_locales) (simp_all add: blocks_image_def finite_incidence_system_axioms.intro)

subsection \<open>Incidence System Isomorphisms\<close>

text \<open>Isomorphism's are defined by the Handbook of Combinatorial Designs 
\cite{colbournHandbookCombinatorialDesigns2007}\<close>

locale incidence_system_isomorphism = source: incidence_system \<V> \<B> + target: incidence_system \<V>' \<B>'
  for "\<V>" and "\<B>" and "\<V>'" and "\<B>'" + fixes bij_map ("\<pi>")
  assumes bij: "bij_betw \<pi> \<V> \<V>'"
  assumes block_img: "image_mset ((`) \<pi>) \<B> = \<B>'"
begin

lemma iso_eq_order: "card \<V> = card \<V>'"
  using bij bij_betw_same_card by auto

lemma iso_eq_block_num: "size \<B> = size \<B>'"
  using block_img by (metis size_image_mset) 

lemma iso_block_img_alt_rep: "{# \<pi> ` bl . bl \<in># \<B>#} = \<B>'"
  using block_img by simp

lemma inv_iso_block_img: "image_mset ((`) (inv_into \<V> \<pi>)) \<B>' = \<B>"
proof - 
  have "\<And> x. x \<in> \<V> \<Longrightarrow> ((inv_into \<V> \<pi>) \<circ> \<pi>) x = x"
    using bij bij_betw_inv_into_left comp_apply by fastforce  
  then have "\<And> bl x . bl \<in># \<B> \<Longrightarrow> x \<in> bl  \<Longrightarrow> ((inv_into \<V> \<pi>) \<circ> \<pi>) x = x" 
    using source.wellformed by blast
  then have img: "\<And> bl . bl \<in># \<B> \<Longrightarrow> image ((inv_into \<V> \<pi>) \<circ> \<pi>) bl = bl"
    by simp 
  have "image_mset ((`) (inv_into \<V> \<pi>)) \<B>' = image_mset ((`) (inv_into \<V> \<pi>)) (image_mset ((`) \<pi>) \<B>)" 
    using block_img by simp
  then have "image_mset ((`) (inv_into \<V> \<pi>)) \<B>' = image_mset ((`) ((inv_into \<V> \<pi>) \<circ> \<pi>)) \<B>"
    by (metis (no_types, hide_lams) comp_apply image_comp multiset.map_comp multiset.map_cong0)
  thus ?thesis using img by simp
qed

lemma inverse_incidence_sys_iso: "incidence_system_isomorphism \<V>' \<B>' \<V> \<B> (inv_into \<V> \<pi>)"
  using bij bij_betw_inv_into inv_iso_block_img by (unfold_locales) simp

lemma iso_points_map: "\<pi> ` \<V> = \<V>'"
  using bij by (simp add: bij_betw_imp_surj_on)

lemma iso_points_inv_map: "(inv_into \<V> \<pi>) `  \<V>' = \<V>"
  using incidence_system_isomorphism.iso_points_map inverse_incidence_sys_iso by blast

lemma iso_points_ss_card: 
  assumes "ps \<subseteq> \<V>"
  shows "card ps = card (\<pi> ` ps)"
  using assms bij bij_betw_same_card bij_betw_subset by blast

lemma iso_block_in: "bl \<in># \<B> \<Longrightarrow> (\<pi> ` bl) \<in># \<B>'"
  using iso_block_img_alt_rep
  by (metis image_eqI in_image_mset)

lemma iso_inv_block_in: "x \<in># \<B>' \<Longrightarrow> x \<in> (`) \<pi> ` set_mset \<B>"
  by (metis block_img in_image_mset)

lemma iso_img_block_orig_exists: "x \<in># \<B>' \<Longrightarrow> \<exists> bl . bl \<in># \<B> \<and> x = \<pi> ` bl"
  using iso_inv_block_in by blast

lemma iso_blocks_map_inj: "x \<in># \<B> \<Longrightarrow> y \<in># \<B> \<Longrightarrow> \<pi> ` x = \<pi> ` y \<Longrightarrow> x = y"
  using image_inv_into_cancel incidence_system.wellformed iso_points_inv_map iso_points_map
  by (metis (no_types, lifting) source.incidence_system_axioms subset_image_iff)

lemma iso_bij_betwn_block_sets: "bij_betw ((`) \<pi>) (set_mset \<B>) (set_mset \<B>')"
  apply ( simp add: bij_betw_def inj_on_def)
  using iso_block_in iso_inv_block_in iso_blocks_map_inj by auto 

lemma iso_bij_betwn_block_sets_inv: "bij_betw ((`) (inv_into \<V> \<pi>)) (set_mset \<B>') (set_mset \<B>)"
  using incidence_system_isomorphism.iso_bij_betwn_block_sets inverse_incidence_sys_iso by blast 

lemma iso_bij_betw_individual_blocks: "bl \<in># \<B> \<Longrightarrow> bij_betw \<pi> bl (\<pi> ` bl)"
  using bij bij_betw_subset source.wellformed by blast 

lemma iso_bij_betw_individual_blocks_inv: "bl \<in># \<B> \<Longrightarrow> bij_betw (inv_into \<V> \<pi>) (\<pi> ` bl) bl"
  using bij bij_betw_subset source.wellformed bij_betw_inv_into_subset by fastforce 

lemma iso_bij_betw_individual_blocks_inv_alt: 
    "bl \<in># \<B>' \<Longrightarrow> bij_betw (inv_into \<V> \<pi>) bl ((inv_into \<V> \<pi>) ` bl)"
  using incidence_system_isomorphism.iso_bij_betw_individual_blocks inverse_incidence_sys_iso
  by blast 
  
lemma iso_inv_block_in_alt:  "(\<pi> ` bl) \<in># \<B>' \<Longrightarrow> bl \<subseteq> \<V> \<Longrightarrow> bl \<in># \<B>"
  using image_eqI image_inv_into_cancel inv_iso_block_img iso_points_inv_map
  by (metis (no_types, lifting) iso_points_map multiset.set_map subset_image_iff)

lemma iso_img_block_not_in: 
  assumes "x \<notin># \<B>"
  assumes "x \<subseteq> \<V>"
  shows "(\<pi> ` x) \<notin># \<B>'"
proof (rule ccontr)
  assume a: "\<not> \<pi> ` x \<notin># \<B>'"
  then have a: "\<pi> ` x \<in># \<B>'" by simp
  then have "\<And> y . y \<in> (\<pi> ` x) \<Longrightarrow> (inv_into \<V> \<pi>) y \<in> \<V>"
    using target.wf_invalid_point iso_points_inv_map by auto 
  then have "((`) (inv_into \<V> \<pi>)) (\<pi> ` x) \<in># \<B>" 
    using iso_bij_betwn_block_sets_inv by (meson a bij_betw_apply) 
  thus False
    using a assms(1) assms(2) iso_inv_block_in_alt by blast 
qed

lemma iso_block_multiplicity:
  assumes  "bl \<subseteq> \<V>" 
  shows "source.multiplicity bl = target.multiplicity (\<pi> ` bl)"
proof (cases "bl \<in># \<B>")
  case True
  have "inj_on ((`) \<pi>) (set_mset \<B>)"
    using bij_betw_imp_inj_on iso_bij_betwn_block_sets by auto 
  then have "count \<B> bl = count \<B>' (\<pi> ` bl)" 
    using count_image_mset_le_count_inj_on count_image_mset_ge_count True block_img inv_into_f_f 
      less_le_not_le order.not_eq_order_implies_strict by metis  
  thus ?thesis by simp
next
  case False
  have s_mult: "source.multiplicity bl = 0"
    by (simp add: False count_eq_zero_iff) 
  then have "target.multiplicity (\<pi> ` bl) = 0"
    using False count_inI iso_inv_block_in_alt
    by (metis assms) 
  thus ?thesis
    using s_mult by simp
qed

lemma iso_point_in_block_img_iff: "p \<in> \<V> \<Longrightarrow> bl \<in># \<B> \<Longrightarrow> p \<in> bl \<longleftrightarrow> (\<pi> p) \<in> (\<pi> ` bl)"
  by (metis bij bij_betw_imp_surj_on iso_bij_betw_individual_blocks_inv bij_betw_inv_into_left imageI)

lemma iso_point_subset_block_iff: "p \<subseteq> \<V> \<Longrightarrow> bl \<in># \<B> \<Longrightarrow> p \<subseteq> bl \<longleftrightarrow> (\<pi> ` p) \<subseteq> (\<pi> ` bl)"
  apply auto
  using image_subset_iff iso_point_in_block_img_iff subset_iff by metis

lemma iso_is_image_block: "\<B>' = blocks_image \<B> \<pi>"
  unfolding blocks_image_def by (simp add: block_img iso_points_map)

end

subsection \<open>Design Isomorphisms\<close>
text \<open>Apply the concept of isomorphisms to designs only\<close>

locale design_isomorphism = incidence_system_isomorphism \<V> \<B> \<V>' \<B>' \<pi> + source: design \<V> \<B> + 
  target: design \<V>' \<B>' for \<V> and \<B> and \<V>' and \<B>' and bij_map ("\<pi>")
  
context design_isomorphism
begin

lemma inverse_design_isomorphism: "design_isomorphism \<V>' \<B>' \<V> \<B> (inv_into \<V> \<pi>)"
  using inverse_incidence_sys_iso source.wf_design target.wf_design
  by (simp add: design_isomorphism.intro) 

end

subsubsection \<open>Isomorphism Operation\<close>
text \<open>Define the concept of isomorphic designs outside the scope of locale\<close>

definition isomorphic_designs (infixl "\<cong>\<^sub>D" 50) where
"\<D> \<cong>\<^sub>D \<D>' \<longleftrightarrow> (\<exists> \<pi> . design_isomorphism (fst \<D>) (snd \<D>) (fst \<D>') (snd \<D>') \<pi>)"

lemma isomorphic_designs_symmetric: "(\<V>, \<B>) \<cong>\<^sub>D (\<V>', \<B>') \<Longrightarrow> (\<V>', \<B>') \<cong>\<^sub>D (\<V>, \<B>)"
  using isomorphic_designs_def design_isomorphism.inverse_design_isomorphism
  by metis

lemma isomorphic_designs_implies_bij: "(\<V>, \<B>) \<cong>\<^sub>D (\<V>', \<B>') \<Longrightarrow> \<exists> \<pi> . bij_betw \<pi> \<V> \<V>'"
  using incidence_system_isomorphism.bij isomorphic_designs_def
  by (metis design_isomorphism.axioms(1) fst_conv)

lemma isomorphic_designs_implies_block_map: "(\<V>, \<B>) \<cong>\<^sub>D (\<V>', \<B>') \<Longrightarrow> \<exists> \<pi> . image_mset ((`) \<pi>) \<B> = \<B>'"
  using incidence_system_isomorphism.block_img isomorphic_designs_def
  using design_isomorphism.axioms(1) by fastforce

context design
begin 

lemma isomorphic_designsI [intro]: "design \<V>' \<B>' \<Longrightarrow> bij_betw \<pi> \<V> \<V>' \<Longrightarrow> image_mset ((`) \<pi>) \<B> = \<B>' 
    \<Longrightarrow> (\<V>, \<B>) \<cong>\<^sub>D (\<V>', \<B>')"
  using design_isomorphism.intro isomorphic_designs_def wf_design image_set_system_wellformed
  by (metis bij_betw_imp_surj_on blocks_image_def fst_conv incidence_system_axioms 
      incidence_system_isomorphism.intro incidence_system_isomorphism_axioms_def snd_conv)

lemma eq_designs_isomorphic: 
  assumes "\<V> = \<V>'"
  assumes "\<B> = \<B>'"
  shows "(\<V>, \<B>) \<cong>\<^sub>D (\<V>', \<B>')" 
proof -
  interpret d1: design \<V> \<B> using assms
    using wf_design by auto 
  interpret d2: design \<V>' \<B>' using assms
    using wf_design by blast 
  have "design_isomorphism \<V> \<B> \<V>' \<B>' id" using assms by (unfold_locales) simp_all
  thus ?thesis unfolding isomorphic_designs_def by auto
qed

end

context design_isomorphism
begin

subsubsection \<open>Design Properties/Operations under Isomorphism\<close>

lemma design_iso_point_rep_num_eq: 
  assumes "p \<in> \<V>"
  shows "\<B> rep p = \<B>' rep (\<pi> p)"
proof -
  have "{#b \<in># \<B> . p \<in> b#} = {#b \<in># \<B> . \<pi> p \<in> \<pi> ` b#}" 
    using assms filter_mset_cong iso_point_in_block_img_iff assms by force
  then have "{#b \<in># \<B>' . \<pi> p \<in> b#} = image_mset ((`) \<pi>) {#b \<in># \<B> . p \<in> b#}"
    by (simp add: image_mset_filter_swap block_img)
  thus ?thesis
    by (simp add: point_replication_number_def) 
qed

lemma design_iso_rep_numbers_eq: "source.replication_numbers = target.replication_numbers"
  apply (simp add: source.replication_numbers_def target.replication_numbers_def)
  using  design_iso_point_rep_num_eq design_isomorphism.design_iso_point_rep_num_eq iso_points_map
  by (metis (no_types, hide_lams) imageI inverse_design_isomorphism iso_points_inv_map)

lemma design_iso_block_size_eq: "bl \<in># \<B> \<Longrightarrow> card bl = card (\<pi> ` bl)"
  using card_image_le finite_subset_image image_inv_into_cancel
  by (metis iso_points_inv_map iso_points_map le_antisym source.finite_blocks source.wellformed)
  
lemma design_iso_block_sizes_eq: "source.sys_block_sizes = target.sys_block_sizes"
  apply (simp add: source.sys_block_sizes_def target.sys_block_sizes_def)
  by (metis (no_types, hide_lams) design_iso_block_size_eq iso_block_in iso_img_block_orig_exists) 

lemma design_iso_points_index_eq: 
  assumes "ps \<subseteq> \<V>" 
  shows "\<B> index ps = \<B>' index (\<pi> ` ps)"
proof - 
  have "\<And> b . b \<in># \<B> \<Longrightarrow> ((ps \<subseteq> b) = ((\<pi> ` ps) \<subseteq> \<pi> ` b))" 
    using iso_point_subset_block_iff assms by blast
  then have "{#b \<in># \<B> . ps \<subseteq> b#} = {#b \<in># \<B> . (\<pi> ` ps) \<subseteq> (\<pi> ` b)#}" 
    using assms filter_mset_cong by force  
  then have "{#b \<in># \<B>' . \<pi> ` ps \<subseteq> b#} = image_mset ((`) \<pi>) {#b \<in># \<B> . ps \<subseteq> b#}"
    by (simp add: image_mset_filter_swap block_img)
  thus ?thesis
    by (simp add: points_index_def)
qed

lemma design_iso_points_indices_imp: 
  assumes "x \<in> source.point_indices t"
  shows "x \<in> target.point_indices t"
proof - 
  obtain ps where t: "card ps = t" and ss: "ps \<subseteq> \<V>" and x: "\<B> index ps = x" using assms
    by (auto simp add: source.point_indices_def)
  then have x_val: "x = \<B>' index (\<pi> ` ps)" using design_iso_points_index_eq by auto
  have x_img: " (\<pi> ` ps) \<subseteq> \<V>'" 
    using ss bij iso_points_map by fastforce 
  then have "card (\<pi> ` ps) = t" using t ss iso_points_ss_card by auto
  then show ?thesis using target.point_indices_elem_in x_img x_val by blast 
qed

lemma design_iso_points_indices_eq: "source.point_indices t = target.point_indices t"
  using inverse_design_isomorphism design_isomorphism.design_iso_points_indices_imp
    design_iso_points_indices_imp by blast 

lemma design_iso_block_intersect_num_eq: 
  assumes "b1 \<in># \<B>"
  assumes "b2 \<in># \<B>"
  shows "b1 |\<inter>| b2 = (\<pi> ` b1) |\<inter>| (\<pi> ` b2)"
proof -
  have split: "\<pi> ` (b1 \<inter> b2) = (\<pi> ` b1) \<inter> (\<pi> ` b2)" using assms bij bij_betw_inter_subsets
    by (metis source.wellformed) 
  thus ?thesis using source.wellformed
    by (simp add: intersection_number_def iso_points_ss_card split assms(2) inf.coboundedI2) 
qed

lemma design_iso_inter_numbers_imp: 
  assumes "x \<in> source.intersection_numbers" 
  shows "x \<in> target.intersection_numbers"
proof - 
  obtain b1 b2 where 1: "b1 \<in># \<B>" and 2: "b2 \<in># (remove1_mset b1 \<B>)" and xval: "x = b1 |\<inter>| b2" 
    using assms by (auto simp add: source.intersection_numbers_def)
  then have pi1: "\<pi> ` b1 \<in># \<B>'" by (simp add: iso_block_in)
  have pi2: "\<pi> ` b2 \<in># (remove1_mset (\<pi> ` b1) \<B>')" using iso_block_in 2
    by (metis (no_types, lifting) "1" block_img image_mset_remove1_mset_if in_remove1_mset_neq 
        iso_blocks_map_inj more_than_one_mset_mset_diff multiset.set_map)
  have "x = (\<pi> ` b1) |\<inter>| (\<pi> ` b2)" using 1 2 design_iso_block_intersect_num_eq
    by (metis in_diffD xval)
  then have "x \<in> {b1 |\<inter>| b2 | b1 b2 . b1 \<in># \<B>' \<and> b2 \<in># (\<B>' - {#b1#})}" 
    using pi1 pi2 by blast
  then show ?thesis by (simp add: target.intersection_numbers_def) 
qed

lemma design_iso_intersection_numbers: "source.intersection_numbers = target.intersection_numbers"
  using inverse_design_isomorphism design_isomorphism.design_iso_inter_numbers_imp 
      design_iso_inter_numbers_imp by blast

lemma design_iso_n_intersect_num: 
  assumes "b1 \<in># \<B>" 
  assumes "b2 \<in># \<B>" 
  shows "b1 |\<inter>|\<^sub>n b2 = ((\<pi> ` b1) |\<inter>|\<^sub>n (\<pi> ` b2))"
proof -
  let ?A = "{x . x \<subseteq> b1 \<and> x \<subseteq> b2 \<and> card x = n}"
  let ?B = "{y . y \<subseteq> (\<pi> ` b1) \<and> y \<subseteq> (\<pi> ` b2) \<and> card y = n}"
  have b1v: "b1 \<subseteq> \<V>"  by (simp add: assms(1) source.wellformed) 
  have b2v: "b2 \<subseteq> \<V>"  by (simp add: assms(2) source.wellformed) 
  then have "\<And>x y . x \<subseteq> b1 \<Longrightarrow> x \<subseteq> b2 \<Longrightarrow> y \<subseteq> b1 \<Longrightarrow> y \<subseteq> b2 \<Longrightarrow>  \<pi> ` x = \<pi> ` y \<Longrightarrow> x = y"
    using b1v bij by (metis bij_betw_imp_surj_on bij_betw_inv_into_subset dual_order.trans)
  then have inj: "inj_on ((`) \<pi>) ?A" by (simp add: inj_on_def)
  have eqcard: "\<And>xa. xa \<subseteq> b1 \<Longrightarrow> xa \<subseteq> b2 \<Longrightarrow> card (\<pi> ` xa) = card xa" using b1v b2v bij
    using iso_points_ss_card by auto 
  have surj: "\<And>x. x \<subseteq> \<pi> ` b1 \<Longrightarrow> x \<subseteq> \<pi> ` b2  \<Longrightarrow> 
                x \<in> {(\<pi> ` xa) | xa . xa \<subseteq> b1 \<and> xa \<subseteq> b2 \<and> card xa = card x}"
  proof - 
    fix x
    assume x1: "x \<subseteq> \<pi> ` b1" and x2: "x \<subseteq> \<pi> ` b2" 
    then obtain xa where eq_x: "\<pi> ` xa = x" and ss: "xa \<subseteq> \<V>"
      by (metis b1v dual_order.trans subset_imageE)
    then have f1: "xa \<subseteq> b1" by (simp add: x1 assms(1) iso_point_subset_block_iff) 
    then have f2: "xa \<subseteq> b2" by (simp add: eq_x ss assms(2) iso_point_subset_block_iff x2) 
    then have f3: "card xa = card x" using bij by (simp add: eq_x ss iso_points_ss_card)
    then show "x \<in> {(\<pi> ` xa) | xa . xa \<subseteq> b1 \<and> xa \<subseteq> b2 \<and> card xa = card x}" 
      using f1 f2 f3 \<open>\<pi> ` xa = x\<close> by auto
  qed
  have "bij_betw ( (`) \<pi>) ?A ?B"
  proof (auto simp add: bij_betw_def)
    show "inj_on ((`) \<pi>) {x. x \<subseteq> b1 \<and> x \<subseteq> b2 \<and> card x = n}" using inj by simp
    show "\<And>xa. xa \<subseteq> b1 \<Longrightarrow> xa \<subseteq> b2 \<Longrightarrow> n = card xa \<Longrightarrow> card (\<pi> ` xa) = card xa" 
      using eqcard by simp
    show "\<And>x. x \<subseteq> \<pi> ` b1 \<Longrightarrow> x \<subseteq> \<pi> ` b2 \<Longrightarrow> n = card x \<Longrightarrow> 
            x \<in> (`) \<pi> ` {xa. xa \<subseteq> b1 \<and> xa \<subseteq> b2 \<and> card xa = card x}" 
      using surj by (simp add: setcompr_eq_image)
  qed
  thus ?thesis
    using bij_betw_same_card by (auto simp add: n_intersect_number_def)
qed

lemma subdesign_iso_implies:
  assumes "sub_set_system V B \<V> \<B>"
  shows "sub_set_system (\<pi> ` V) (blocks_image B \<pi>) \<V>' \<B>'"
proof (unfold_locales)
  show "\<pi> ` V \<subseteq> \<V>'" 
    by (metis assms image_mono iso_points_map sub_set_system.points_subset) 
  show "blocks_image B \<pi> \<subseteq># \<B>'"
    by (metis assms block_img blocks_image_def image_mset_subseteq_mono sub_set_system.blocks_subset) 
qed

lemma subdesign_image_is_design: 
  assumes "sub_set_system V B \<V> \<B>"
  assumes "design V B"
  shows "design (\<pi> ` V) (blocks_image B \<pi>)"
proof -
  interpret fin: finite_incidence_system "(\<pi> ` V)" "(blocks_image B \<pi>)" using assms(2)
    by (simp add: design.axioms(1) finite_incidence_system.image_set_system_finite)
  interpret des: sub_design V B \<V> \<B> using assms design.wf_design_iff
    by (unfold_locales, auto simp add: sub_set_system.points_subset sub_set_system.blocks_subset)
  have bl_img: "blocks_image B \<pi> \<subseteq># \<B>'"
    by (simp add: blocks_image_def des.blocks_subset image_mset_subseteq_mono iso_is_image_block)  
  then show ?thesis 
  proof (unfold_locales, auto)
    show "{} \<in># blocks_image B \<pi> \<Longrightarrow> False" 
      using assms subdesign_iso_implies target.blocks_nempty bl_img by auto
  qed
qed

lemma sub_design_isomorphism: 
  assumes "sub_set_system V B \<V> \<B>"
  assumes "design V B"
  shows "design_isomorphism V B (\<pi> ` V) (blocks_image B \<pi>) \<pi>"
proof -
  interpret design "(\<pi> ` V)" "(blocks_image B \<pi>)"
    by (simp add: assms(1) assms(2) subdesign_image_is_design)
  interpret des: design V B by fact
  show ?thesis
  proof (unfold_locales)
    show "bij_betw \<pi> V (\<pi> ` V)" using bij
      by (metis assms(1) bij_betw_subset sub_set_system.points_subset) 
    show "image_mset ((`) \<pi>) B = blocks_image B \<pi>" by (simp add: blocks_image_def)
  qed
qed

end
end