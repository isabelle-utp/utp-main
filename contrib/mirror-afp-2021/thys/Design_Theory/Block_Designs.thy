(* Title: Block_Designs.thy
   Author: Chelsea Edmonds
*)

section \<open>Block and Balanced Designs\<close>
text \<open>We define a selection of the many different types of block and balanced designs, building up 
to properties required for defining a BIBD, in addition to several base generalisations\<close> 

theory Block_Designs imports Design_Operations
begin

subsection \<open>Block Designs\<close>
text \<open>A block design is a design where all blocks have the same size.\<close>

subsubsection \<open>K Block Designs\<close> 
text \<open>An important generalisation of a typical block design is the $\mathcal{K}$ block design, 
where all blocks must have a size $x$ where $x \in \mathcal{K}$\<close>
locale K_block_design = proper_design +
  fixes sizes :: "int set" ("\<K>")
  assumes block_sizes: "bl \<in># \<B> \<Longrightarrow> (int (card bl)) \<in> \<K>"
  assumes positive_ints: "x \<in> \<K> \<Longrightarrow> x > 0"
begin

lemma sys_block_size_subset: "sys_block_sizes \<subseteq> \<K>"
  using block_sizes sys_block_sizes_obtain_bl by blast

end

subsubsection\<open>Uniform Block Design\<close>
text \<open>The typical uniform block design is defined below\<close>
locale block_design = proper_design + 
  fixes u_block_size :: int ("\<k>")
  assumes uniform [simp]: "bl \<in># \<B> \<Longrightarrow> card bl = \<k>"
begin

lemma k_non_zero: "\<k> \<ge> 1"
proof -
  obtain bl where bl_in: "bl \<in># \<B>"
    using design_blocks_nempty by auto 
  then have "int (card bl) \<ge> 1" using block_size_gt_0
    by (metis less_not_refl less_one not_le_imp_less of_nat_1 of_nat_less_iff) 
  thus ?thesis by (simp add: bl_in)
qed

lemma uniform_alt_def_all: "\<forall> bl \<in># \<B> .card bl = \<k>"
  using uniform by auto 

lemma uniform_unfold_point_set: "bl \<in># \<B> \<Longrightarrow> card {p \<in> \<V>. p \<in> bl} = \<k>"
  using uniform wellformed by (simp add: Collect_conj_eq inf.absorb_iff2) 

lemma uniform_unfold_point_set_mset: "bl \<in># \<B> \<Longrightarrow> size {#p \<in># mset_set \<V>. p \<in> bl #} = \<k>"
  using uniform_unfold_point_set by (simp add: finite_sets) 

lemma sys_block_sizes_uniform [simp]:  "sys_block_sizes  = {\<k>}"
proof -
  have "sys_block_sizes = {bs . \<exists> bl . bs = card bl \<and> bl\<in># \<B>}" by (simp add: sys_block_sizes_def)
  then have "sys_block_sizes  = {bs . bs = \<k>}" using uniform uniform_unfold_point_set 
      b_positive block_set_nempty_imp_block_ex
    by (smt (verit, best) Collect_cong design_blocks_nempty)
  thus ?thesis by auto
qed

lemma sys_block_sizes_uniform_single: "is_singleton (sys_block_sizes)"
  by simp

lemma uniform_size_incomp: "\<k> \<le> \<v> - 1 \<Longrightarrow> bl \<in># \<B> \<Longrightarrow> incomplete_block bl"
  using uniform k_non_zero of_nat_less_iff zle_diff1_eq by metis

lemma uniform_complement_block_size:
  assumes "bl \<in># \<B>\<^sup>C"
  shows "card bl = \<v> - \<k>"
proof -
  obtain bl' where bl_assm: "bl = bl'\<^sup>c \<and> bl' \<in># \<B>" 
    using wellformed assms by (auto simp add: complement_blocks_def)
  then have "int (card bl') = \<k>" by simp
  thus ?thesis using bl_assm block_complement_size wellformed
    by (simp add: block_size_lt_order of_nat_diff) 
qed

lemma uniform_complement[intro]: 
  assumes "\<k> \<le> \<v> - 1"
  shows "block_design \<V> \<B>\<^sup>C (\<v> - \<k>)"
proof - 
  interpret des: proper_design \<V> "\<B>\<^sup>C" 
    using  uniform_size_incomp assms complement_proper_design by auto 
  show ?thesis using assms uniform_complement_block_size by (unfold_locales) (simp)
qed

lemma block_size_lt_v: "\<k> \<le> \<v>"
  using v_non_zero block_size_lt_v design_blocks_nempty uniform by auto 

end

lemma (in proper_design) block_designI[intro]: "(\<And> bl . bl \<in># \<B> \<Longrightarrow> card bl = k) 
  \<Longrightarrow> block_design \<V> \<B> k"
  by (unfold_locales) (auto)

context block_design 
begin

lemma block_design_multiple: "n > 0 \<Longrightarrow> block_design \<V> (multiple_blocks n) \<k>"
  using elem_in_repeat_in_original multiple_proper_design proper_design.block_designI 
  by (metis block_set_nempty_imp_block_ex design_blocks_nempty int_int_eq uniform_alt_def_all) 

end
text \<open>A uniform block design is clearly a type of $K$\_block\_design with a singleton $K$ set\<close>
sublocale block_design \<subseteq> K_block_design \<V> \<B> "{\<k>}"
  using k_non_zero uniform by unfold_locales simp_all

subsubsection \<open>Incomplete Designs\<close>
text \<open>An incomplete design is a design where $k < v$, i.e. no block is equal to the point set\<close>
locale incomplete_design = block_design + 
  assumes incomplete: "\<k> < \<v>"

begin

lemma incomplete_imp_incomp_block: "bl \<in># \<B> \<Longrightarrow> incomplete_block bl"
  using incomplete uniform uniform_size_incomp by fastforce  

lemma incomplete_imp_proper_subset: "bl \<in># \<B> \<Longrightarrow> bl \<subset> \<V>"
  by (simp add: incomplete_block_proper_subset incomplete_imp_incomp_block wellformed)
end

lemma (in block_design) incomplete_designI[intro]: "\<k> < \<v> \<Longrightarrow> incomplete_design \<V> \<B> \<k>"
  by unfold_locales auto

context incomplete_design
begin

lemma multiple_incomplete: "n > 0 \<Longrightarrow> incomplete_design \<V> (multiple_blocks n) \<k>"
  using block_design_multiple incomplete by (simp add: block_design.incomplete_designI) 

lemma complement_incomplete: "incomplete_design \<V> (\<B>\<^sup>C) (\<v> - \<k>)"
proof -
  have "\<v> - \<k> < \<v>" using v_non_zero k_non_zero by linarith
  thus ?thesis using uniform_complement incomplete incomplete_designI
    by (simp add: block_design.incomplete_designI) 
qed

end

subsection \<open>Balanced Designs\<close>
text \<open>t-wise balance is a design with the property that all point subsets of size $t$ occur in 
$\lambda_t$ blocks\<close>

locale t_wise_balance = proper_design + 
  fixes grouping :: int ("\<t>") and index :: int ("\<Lambda>\<^sub>t")
  assumes t_non_zero: "\<t> \<ge> 1"
  assumes t_lt_order: "\<t> \<le> \<v>"
  assumes balanced [simp]: "ps \<subseteq> \<V> \<Longrightarrow> card ps = \<t> \<Longrightarrow> \<B> index ps = \<Lambda>\<^sub>t"
begin

lemma balanced_alt_def_all: "\<forall> ps \<subseteq> \<V> . card ps = \<t> \<longrightarrow> \<B> index ps = \<Lambda>\<^sub>t"
  using balanced by auto

end

lemma (in proper_design) t_wise_balanceI[intro]: "\<t> \<le> \<v> \<Longrightarrow> \<t> \<ge> 1 \<Longrightarrow> 
  (\<And> ps . ps \<subseteq> \<V> \<Longrightarrow> card ps = \<t>  \<Longrightarrow> \<B> index ps = \<Lambda>\<^sub>t) \<Longrightarrow> t_wise_balance \<V> \<B> \<t> \<Lambda>\<^sub>t"
  by (unfold_locales) auto

context t_wise_balance
begin

lemma obtain_t_subset_points:
  obtains T where "T \<subseteq> \<V>" "card T = \<t>" "finite T"
  using obtain_subset_with_card_int_n design_points_nempty t_lt_order t_non_zero finite_sets
  by (metis (no_types, hide_lams) dual_order.strict_trans2 not_le_imp_less of_nat_1 of_nat_less_0_iff) 

lemma multiple_t_wise_balance_index [simp]:
  assumes "ps \<subseteq> \<V>"
  assumes "card ps = \<t>"
  shows "(multiple_blocks n) index ps = \<Lambda>\<^sub>t * n"
  using multiple_point_index balanced assms by fastforce 

lemma multiple_t_wise_balance: 
  assumes "n > 0" 
  shows "t_wise_balance \<V> (multiple_blocks n) \<t> (\<Lambda>\<^sub>t * n)"
proof - 
  interpret des: proper_design \<V> "(multiple_blocks n)" by (simp add: assms multiple_proper_design)  
  show ?thesis using t_non_zero t_lt_order multiple_t_wise_balance_index 
    by (unfold_locales) (simp_all)
qed

lemma twise_set_pair_index: "ps \<subseteq> \<V> \<Longrightarrow> ps2 \<subseteq> \<V> \<Longrightarrow> ps \<noteq> ps2 \<Longrightarrow> card ps = \<t> \<Longrightarrow> card ps2 = \<t> 
  \<Longrightarrow> \<B> index ps = \<B> index ps2"
  using balanced by (metis of_nat_eq_iff) 

lemma t_wise_balance_alt: "ps \<subseteq> \<V> \<Longrightarrow> card ps = \<t> \<Longrightarrow> \<B> index ps = l2 
  \<Longrightarrow> (\<And> ps . ps \<subseteq> \<V> \<Longrightarrow> card ps = \<t> \<Longrightarrow> \<B> index ps = l2)"
  using twise_set_pair_index by blast

lemma index_ge_zero: "\<Lambda>\<^sub>t \<ge> 0"
proof -
  obtain ps where "ps \<subseteq> \<V> \<and> card ps = \<t>" using t_non_zero t_lt_order obtain_subset_with_card_n
    by (metis dual_order.trans of_nat_le_iff zero_le_imp_eq_int zero_le_one)
  thus ?thesis
    using balanced_alt_def_all of_nat_0_le_iff by blast
qed

lemma index_1_imp_mult_1 [simp]: 
  assumes "\<Lambda>\<^sub>t = 1"
  assumes "bl \<in># \<B>"
  assumes "card bl \<ge> \<t>"
  shows "multiplicity bl = 1"
proof (rule ccontr)
  assume "\<not> (multiplicity bl = 1)"
  then have not: "multiplicity bl \<noteq> 1" by simp
  have "multiplicity bl \<noteq> 0" using assms by simp 
  then have m: "multiplicity bl \<ge> 2" using not by linarith
  obtain ps where ps: "ps \<subseteq> bl \<and> card ps = \<t>"
    using assms obtain_t_subset_points
    by (metis obtain_subset_with_card_int_n of_nat_0_le_iff) 
  then have "\<B> index ps \<ge> 2"
    using m points_index_count_min ps by blast
  then show False using balanced ps antisym_conv2 not_numeral_less_zero numeral_le_one_iff 
      points_index_ps_nin semiring_norm(69) zero_neq_numeral
    by (metis assms(1) int_int_eq int_ops(2)) 
qed

end

subsubsection \<open>Sub-types of t-wise balance\<close>

text \<open>Pairwise balance is when $t = 2$. These are commonly of interest\<close>
locale pairwise_balance = t_wise_balance \<V> \<B> 2 \<Lambda> 
  for point_set ("\<V>") and block_collection ("\<B>") and index ("\<Lambda>")

text \<open>We can combine the balance properties with $K$\_block design to define tBD's 
(t-wise balanced designs), and PBD's (pairwise balanced designs)\<close>

locale tBD = t_wise_balance + K_block_design +
  assumes block_size_gt_t: "k \<in> \<K> \<Longrightarrow> k \<ge> \<t>"

locale \<Lambda>_PBD = pairwise_balance + K_block_design + 
  assumes block_size_gt_t: "k \<in> \<K> \<Longrightarrow> k \<ge> 2"

sublocale \<Lambda>_PBD \<subseteq> tBD \<V> \<B> 2 \<Lambda> \<K>
  using t_lt_order block_size_gt_t by (unfold_locales) (simp_all)

locale PBD = \<Lambda>_PBD \<V> \<B> 1 \<K> for point_set ("\<V>") and block_collection ("\<B>") and sizes ("\<K>")
begin
lemma multiplicity_is_1:
  assumes "bl \<in># \<B>"
  shows "multiplicity bl = 1"
  using block_size_gt_t index_1_imp_mult_1 by (simp add: assms block_sizes) 

end

sublocale PBD \<subseteq> simple_design
  using multiplicity_is_1 by (unfold_locales)

text \<open>PBD's are often only used in the case where $k$ is uniform, defined here.\<close>
locale k_\<Lambda>_PBD = pairwise_balance + block_design + 
  assumes block_size_t: "2 \<le> \<k>"

sublocale k_\<Lambda>_PBD \<subseteq> \<Lambda>_PBD \<V> \<B> \<Lambda> "{\<k>}"
  using k_non_zero uniform block_size_t by(unfold_locales) (simp_all)

locale k_PBD = k_\<Lambda>_PBD \<V> \<B> 1 \<k> for point_set ("\<V>") and block_collection ("\<B>") and u_block_size ("\<k>")

sublocale k_PBD \<subseteq> PBD \<V> \<B> "{\<k>}"
  using  block_size_t by (unfold_locales, simp_all)

subsubsection \<open>Covering and Packing Designs\<close>
text \<open>Covering and packing designs involve a looser balance restriction. Upper/lower bounds
are placed on the points index, instead of a strict equality\<close>

text \<open>A t-covering design is a relaxed version of a tBD, where, for all point subsets of size t, 
a lower bound is put on the points index\<close>
locale t_covering_design = block_design +
  fixes grouping :: int ("\<t>")
  fixes min_index :: int ("\<Lambda>\<^sub>t")
  assumes covering: "ps \<subseteq> \<V> \<Longrightarrow> card ps = \<t> \<Longrightarrow> \<B> index ps \<ge> \<Lambda>\<^sub>t" 
  assumes block_size_t: "\<t> \<le> \<k>"
  assumes t_non_zero: "\<t> \<ge> 1"
begin

lemma covering_alt_def_all: "\<forall> ps \<subseteq> \<V> . card ps = \<t> \<longrightarrow> \<B> index ps \<ge> \<Lambda>\<^sub>t"
  using covering by auto

end

lemma (in block_design) t_covering_designI [intro]: "t \<le> \<k> \<Longrightarrow> t \<ge> 1 \<Longrightarrow> 
  (\<And> ps. ps \<subseteq> \<V> \<Longrightarrow> card ps = t \<Longrightarrow> \<B> index ps \<ge> \<Lambda>\<^sub>t) \<Longrightarrow> t_covering_design \<V> \<B> \<k> t \<Lambda>\<^sub>t"
  by (unfold_locales) simp_all

text \<open>A t-packing design is a relaxed version of a tBD, where, for all point subsets of size t, 
an upper bound is put on the points index\<close>
locale t_packing_design = block_design + 
  fixes grouping :: int ("\<t>")
  fixes min_index :: int ("\<Lambda>\<^sub>t")
  assumes packing: "ps \<subseteq> \<V> \<Longrightarrow> card ps = \<t> \<Longrightarrow> \<B> index ps \<le> \<Lambda>\<^sub>t"
  assumes block_size_t: "\<t> \<le> \<k>"
  assumes t_non_zero: "\<t> \<ge> 1"
begin

lemma packing_alt_def_all: "\<forall> ps \<subseteq> \<V> . card ps = \<t> \<longrightarrow> \<B> index ps \<le> \<Lambda>\<^sub>t"
  using packing by auto

end

lemma (in block_design) t_packing_designI [intro]: "t \<le> \<k> \<Longrightarrow> t \<ge> 1 \<Longrightarrow> 
  (\<And> ps . ps \<subseteq> \<V> \<Longrightarrow> card ps = t \<Longrightarrow> \<B> index ps \<le> \<Lambda>\<^sub>t) \<Longrightarrow> t_packing_design \<V> \<B> \<k> t \<Lambda>\<^sub>t"
  by (unfold_locales) simp_all

lemma packing_covering_imp_balance: 
  assumes "t_packing_design V B k t \<Lambda>\<^sub>t" 
  assumes "t_covering_design V B k t \<Lambda>\<^sub>t" 
  shows "t_wise_balance V B t \<Lambda>\<^sub>t"
proof -
  from assms interpret des: proper_design V B 
    using block_design.axioms(1) t_covering_design.axioms(1) by blast
  show ?thesis 
  proof (unfold_locales)
    show "1 \<le> t" using assms by (simp add: t_packing_design.t_non_zero)
    show "t \<le> des.\<v>" using block_design.block_size_lt_v t_packing_design.axioms(1) 
      by (metis assms(1) dual_order.trans t_packing_design.block_size_t)
    show "\<And>ps. ps \<subseteq> V \<Longrightarrow> card ps = t \<Longrightarrow> B index ps = \<Lambda>\<^sub>t" 
      using t_packing_design.packing t_covering_design.covering by (metis assms dual_order.antisym) 
  qed
qed

subsection \<open>Constant Replication Design\<close>
text \<open>When the replication number for all points in a design is constant, it is the 
design replication number.\<close>
locale constant_rep_design = proper_design +
  fixes design_rep_number :: int ("\<r>")
  assumes rep_number [simp]: "x \<in> \<V> \<Longrightarrow>  \<B> rep x = \<r>" 

begin

lemma rep_number_alt_def_all: "\<forall> x \<in> \<V>. \<B> rep x = \<r>"
  by (simp)

lemma rep_number_unfold_set: "x \<in> \<V> \<Longrightarrow> size {#bl \<in># \<B> . x \<in> bl#} = \<r>"
  using rep_number by (simp add: point_replication_number_def)

lemma rep_numbers_constant [simp]: "replication_numbers  = {\<r>}"
  unfolding replication_numbers_def using rep_number design_points_nempty Collect_cong finite.cases 
    finite_sets insertCI singleton_conv
  by (smt (verit, ccfv_threshold) fst_conv snd_conv) 

lemma replication_number_single: "is_singleton (replication_numbers)"
  using is_singleton_the_elem by simp

lemma constant_rep_point_pair: "x1 \<in> \<V> \<Longrightarrow> x2 \<in> \<V> \<Longrightarrow> x1 \<noteq> x2 \<Longrightarrow> \<B> rep x1 = \<B> rep x2"
  using rep_number by auto

lemma constant_rep_alt: "x1 \<in> \<V> \<Longrightarrow> \<B> rep x1 = r2 \<Longrightarrow> (\<And> x . x \<in> \<V> \<Longrightarrow> \<B> rep x = r2)"
  by (simp)

lemma constant_rep_point_not_0:
  assumes "x \<in> \<V>" 
  shows "\<B> rep x \<noteq> 0"
proof (rule ccontr)
  assume "\<not> \<B> rep x \<noteq> 0"
  then have "\<And> x . x \<in> \<V> \<Longrightarrow> \<B> rep x = 0" using rep_number assms by auto
  then have "\<And> x . x \<in> \<V> \<Longrightarrow>  size {#bl \<in># \<B> . x \<in> bl#} = 0" 
    by (simp add: point_replication_number_def)
  then show False using design_blocks_nempty wf_design wf_design_iff wf_invalid_point
    by (metis ex_in_conv filter_mset_empty_conv multiset_nonemptyE size_eq_0_iff_empty)
qed

lemma rep_not_zero: "\<r> \<noteq> 0"
  using rep_number constant_rep_point_not_0 design_points_nempty by auto 

lemma r_gzero: "\<r> > 0"
  using point_replication_number_def rep_number constant_rep_design.rep_not_zero
  by (metis constant_rep_design.intro constant_rep_design_axioms.intro leI of_nat_less_0_iff 
      proper_design_axioms verit_la_disequality) 

lemma r_lt_eq_b: "\<r> \<le> \<b>"
  using rep_number max_point_rep
  by (metis all_not_in_conv design_points_nempty) 

lemma complement_rep_number: 
  assumes "\<And> bl . bl \<in># \<B> \<Longrightarrow> incomplete_block bl"
  shows "constant_rep_design \<V> \<B>\<^sup>C (\<b> - \<r>)"
proof - 
  interpret d: proper_design \<V> "(\<B>\<^sup>C)" using complement_proper_design
    by (simp add: assms) 
  show ?thesis using complement_rep_number rep_number by (unfold_locales) simp
qed

lemma multiple_rep_number: 
  assumes "n > 0"
  shows "constant_rep_design \<V> (multiple_blocks n) (\<r> * n)"
proof - 
  interpret d: proper_design \<V> "(multiple_blocks n)" using multiple_proper_design
    by (simp add: assms) 
  show ?thesis using multiple_point_rep_num by (unfold_locales) (simp_all)
qed
end

lemma (in proper_design) constant_rep_designI [intro]: "(\<And> x . x \<in> \<V> \<Longrightarrow> \<B> rep x = \<r>) 
    \<Longrightarrow> constant_rep_design \<V> \<B> \<r>"
  by unfold_locales auto

subsection \<open>T-designs\<close>
text \<open>All the before mentioned designs build up to the concept of a t-design, which has uniform 
block size and is t-wise balanced. We limit $t$ to be less than $k$, so the balance condition has 
relevance\<close>
locale t_design = incomplete_design + t_wise_balance + 
  assumes block_size_t: "\<t> \<le> \<k>"
begin

lemma point_indices_balanced: "point_indices \<t> = {\<Lambda>\<^sub>t}" 
proof -
  have "point_indices \<t> = {i . \<exists> ps . i = \<B> index ps \<and> int (card ps) = \<t> \<and> ps \<subseteq> \<V>}"
    by (simp add: point_indices_def) 
  then have "point_indices  \<t> = {i . i = \<Lambda>\<^sub>t}" using balanced Collect_cong obtain_t_subset_points 
     by smt 
  thus ?thesis by auto
qed

lemma point_indices_singleton: "is_singleton (point_indices \<t>)"
  using point_indices_balanced is_singleton_the_elem by simp

end

lemma t_designI [intro]: 
  assumes "incomplete_design V B k"
  assumes "t_wise_balance V B t \<Lambda>\<^sub>t"
  assumes "t \<le> k"
  shows "t_design V B k t \<Lambda>\<^sub>t"
  by (simp add: assms(1) assms(2) assms(3) t_design.intro t_design_axioms.intro)

sublocale t_design \<subseteq> t_covering_design \<V> \<B> \<k> \<t> \<Lambda>\<^sub>t
  using t_non_zero by (unfold_locales) (auto simp add: block_size_t)

sublocale t_design \<subseteq> t_packing_design \<V> \<B> \<k> \<t> \<Lambda>\<^sub>t
  using t_non_zero by (unfold_locales) (auto simp add: block_size_t)

lemma t_design_pack_cov [intro]: 
  assumes "k < card V"
  assumes "t_covering_design V B k t \<Lambda>\<^sub>t"
  assumes "t_packing_design V B k t \<Lambda>\<^sub>t"
  shows "t_design V B k t \<Lambda>\<^sub>t"
proof -
  from assms interpret id: incomplete_design V B k
    using block_design.incomplete_designI t_packing_design.axioms(1)
    by (metis of_nat_less_iff) 
  from assms interpret balance: t_wise_balance V B t \<Lambda>\<^sub>t 
    using packing_covering_imp_balance by blast 
  show ?thesis using assms(3) 
    by (unfold_locales) (simp_all add: t_packing_design.block_size_t)
qed

sublocale t_design \<subseteq> tBD \<V> \<B> \<t> \<Lambda>\<^sub>t "{\<k>}"
  using uniform k_non_zero block_size_t by (unfold_locales) simp_all

context t_design 
begin

lemma multiple_t_design: "n > 0 \<Longrightarrow> t_design \<V> (multiple_blocks n) \<k> \<t> (\<Lambda>\<^sub>t * n)"
  using multiple_t_wise_balance multiple_incomplete block_size_t by (simp add: t_designI)

lemma t_design_min_v: "\<v> > 1"
  using k_non_zero incomplete by simp

end

subsection \<open>Steiner Systems\<close>

text \<open>Steiner systems are a special type of t-design where $\Lambda_t = 1$\<close>
locale steiner_system = t_design \<V> \<B> \<k> \<t> 1 
  for point_set ("\<V>") and block_collection ("\<B>") and u_block_size ("\<k>") and grouping ("\<t>")

begin

lemma block_multiplicity [simp]: 
  assumes "bl \<in># \<B>"
  shows "multiplicity bl = 1"
  by (simp add: assms block_size_t)

end

sublocale steiner_system \<subseteq> simple_design
  by unfold_locales (simp)

lemma (in t_design) steiner_systemI[intro]: "\<Lambda>\<^sub>t = 1 \<Longrightarrow> steiner_system \<V> \<B> \<k> \<t>"
  using t_non_zero t_lt_order block_size_t
  by unfold_locales auto

subsection \<open>Combining block designs\<close>
text \<open>We define some closure properties for various block designs under the combine operator.
This is done using locales to reason on multiple instances of the same type of design, building 
on what was presented in the design operations theory\<close>

locale two_t_wise_eq_points = two_designs_proper \<V> \<B> \<V> \<B>' + des1: t_wise_balance \<V> \<B> \<t> \<Lambda>\<^sub>t + 
  des2: t_wise_balance \<V> \<B>' \<t> \<Lambda>\<^sub>t' for \<V> \<B> \<t> \<Lambda>\<^sub>t \<B>' \<Lambda>\<^sub>t'
begin

lemma combine_t_wise_balance_index: "ps \<subseteq> \<V> \<Longrightarrow> card ps = \<t> \<Longrightarrow> \<B>\<^sup>+ index ps = (\<Lambda>\<^sub>t + \<Lambda>\<^sub>t')"
  using des1.balanced des2.balanced by (simp add: combine_points_index)

lemma combine_t_wise_balance: "t_wise_balance \<V>\<^sup>+ \<B>\<^sup>+ \<t> (\<Lambda>\<^sub>t + \<Lambda>\<^sub>t')"
proof (unfold_locales, simp add: des1.t_non_zero)
  have "card \<V>\<^sup>+  \<ge> card \<V>" by simp 
  then show "\<t> \<le> card (\<V>\<^sup>+)" using des1.t_lt_order by linarith 
  show "\<And>ps. ps \<subseteq> \<V>\<^sup>+ \<Longrightarrow> card ps = \<t> \<Longrightarrow> (\<B>\<^sup>+ index ps) = \<Lambda>\<^sub>t + \<Lambda>\<^sub>t'" 
    using combine_t_wise_balance_index by blast 
qed

sublocale combine_t_wise_des: t_wise_balance "\<V>\<^sup>+" "\<B>\<^sup>+" "\<t>" "(\<Lambda>\<^sub>t + \<Lambda>\<^sub>t')"
  using combine_t_wise_balance by auto

end

locale two_k_block_designs = two_designs_proper \<V> \<B> \<V>' \<B>' + des1: block_design \<V> \<B> \<k> + 
  des2: block_design \<V>' \<B>' \<k> for \<V> \<B> \<k> \<V>' \<B>'
begin

lemma block_design_combine: "block_design \<V>\<^sup>+ \<B>\<^sup>+ \<k>"
  using des1.uniform des2.uniform by (unfold_locales) (auto)

sublocale combine_block_des: block_design "\<V>\<^sup>+" "\<B>\<^sup>+" "\<k>"
  using block_design_combine by simp

end

locale two_rep_designs_eq_points = two_designs_proper \<V> \<B> \<V> \<B>' + des1: constant_rep_design \<V> \<B> \<r> + 
  des2: constant_rep_design \<V> \<B>' \<r>' for \<V> \<B> \<r> \<B>' \<r>' 
begin

lemma combine_rep_number: "constant_rep_design \<V>\<^sup>+ \<B>\<^sup>+ (\<r> + \<r>')"
  using combine_rep_number des1.rep_number des2.rep_number by (unfold_locales) (simp)

sublocale combine_const_rep: constant_rep_design "\<V>\<^sup>+" "\<B>\<^sup>+" "(\<r> + \<r>')"
  using combine_rep_number by simp

end

locale two_incomplete_designs = two_k_block_designs \<V> \<B> \<k> \<V>' \<B>' + des1: incomplete_design \<V> \<B> \<k> + 
  des2: incomplete_design \<V>' \<B>' \<k> for \<V> \<B> \<k> \<V>' \<B>'
begin

lemma combine_is_incomplete: "incomplete_design \<V>\<^sup>+ \<B>\<^sup>+ \<k>"
  using combine_order des1.incomplete des2.incomplete by (unfold_locales) (simp)

sublocale combine_incomplete: incomplete_design "\<V>\<^sup>+" "\<B>\<^sup>+" "\<k>"
  using combine_is_incomplete by simp
end

locale two_t_designs_eq_points = two_incomplete_designs \<V> \<B> \<k> \<V> \<B>' 
  + two_t_wise_eq_points \<V> \<B> \<t> \<Lambda>\<^sub>t \<B>' \<Lambda>\<^sub>t' + des1: t_design \<V> \<B> \<k> \<t> \<Lambda>\<^sub>t + 
  des2: t_design \<V> \<B>' \<k> \<t> \<Lambda>\<^sub>t' for \<V> \<B> \<k> \<B>' \<t> \<Lambda>\<^sub>t \<Lambda>\<^sub>t'
begin

lemma combine_is_t_des: "t_design \<V>\<^sup>+ \<B>\<^sup>+ \<k> \<t> (\<Lambda>\<^sub>t + \<Lambda>\<^sub>t')"
  using des1.block_size_t des2.block_size_t by (unfold_locales)

sublocale combine_t_des: t_design "\<V>\<^sup>+" "\<B>\<^sup>+" "\<k>" "\<t>" "(\<Lambda>\<^sub>t + \<Lambda>\<^sub>t')"
  using combine_is_t_des by blast

end
end