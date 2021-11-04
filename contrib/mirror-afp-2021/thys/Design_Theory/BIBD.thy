(* Title: BIBD 
   Author: Chelsea Edmonds
*)

theory BIBD imports Block_Designs
begin 

section \<open>BIBD's\<close>
text \<open>BIBD's are perhaps the most commonly studied type of design in combinatorial design theory,
and usually the first type of design explored in a design theory course. 
These designs are a type of t-design, where $t = 2$\<close>

subsection \<open>BIBD Basics\<close>
locale bibd = t_design \<V> \<B> \<k> 2 \<Lambda> 
  for point_set ("\<V>") and block_collection ("\<B>") 
    and u_block_size ("\<k>") and index ("\<Lambda>")

begin

lemma min_block_size_2: "\<k> \<ge> 2" 
  using block_size_t by simp

lemma points_index_pair: "y \<in> \<V> \<Longrightarrow> x \<in> \<V> \<Longrightarrow> x \<noteq> y \<Longrightarrow>  size ({# bl \<in># \<B> . {x, y} \<subseteq> bl#}) = \<Lambda>"
  using balanced card_2_iff empty_subsetI insert_subset points_index_def
  by (metis of_nat_numeral)

lemma index_one_empty_rm_blv [simp]:
  assumes "\<Lambda> = 1" and " blv \<in># \<B>" and "p \<subseteq> blv" and "card p = 2" 
  shows "{#bl \<in># remove1_mset blv \<B> . p \<subseteq> bl#} = {#}"
proof -
  have blv_in: "blv \<in># filter_mset ((\<subseteq>) p) \<B>"
    using assms by simp
  have "p \<subseteq> \<V>" using assms wellformed by auto
  then have "size (filter_mset ((\<subseteq>) p) \<B>) = 1" 
    using balanced assms by (simp add: points_index_def)
  then show ?thesis using blv_in filter_diff_mset filter_single_mset
    by (metis (no_types, lifting) add_mset_eq_single assms(3) insert_DiffM size_1_singleton_mset) 
qed 

lemma index_one_alt_bl_not_exist:
  assumes "\<Lambda> = 1" and " blv \<in># \<B>" and "p \<subseteq> blv" and "card p = 2" 
  shows" \<And> bl. bl \<in># remove1_mset blv \<B> \<Longrightarrow> \<not> (p \<subseteq> bl) "
  using index_one_empty_rm_blv
  by (metis assms(1) assms(2) assms(3) assms(4) filter_mset_empty_conv)

subsection \<open>Necessary Conditions for Existence\<close>

text \<open>The necessary conditions on the existence of a $(v, k, \lambda)$-bibd are one of the 
fundamental first theorems on designs. Proofs based off MATH3301 lecture notes \cite{HerkeLectureNotes2016}
 and Stinson \cite{stinsonCombinatorialDesignsConstructions2004}\<close>

lemma necess_cond_1_rhs: 
  assumes "x \<in> \<V>"
  shows "size ({# p \<in># (mset_set (\<V> - {x}) \<times># {# bl \<in># \<B> . x \<in> bl #}). fst p \<in> snd p#}) = \<Lambda> * (\<v>- 1)"
proof -
  let ?M = "mset_set (\<V> - {x})"
  let ?B = "{# bl \<in># \<B> . x \<in> bl #}"
  have m_distinct: "distinct_mset ?M" using assms mset_points_distinct_diff_one by simp
  have y_point: "\<And> y . y \<in># ?M \<Longrightarrow> y \<in> \<V>" using assms
    by (simp add: finite_sets) 
  have b_contents: "\<And> bl. bl \<in># ?B \<Longrightarrow> x \<in> bl" using assms by auto
  have "\<And> y. y \<in># ?M \<Longrightarrow> y \<noteq> x" using assms
    by (simp add: finite_sets) 
  then have "\<And> y .y \<in># ?M \<Longrightarrow> size ({# bl \<in># ?B . {x, y} \<subseteq> bl#}) = nat \<Lambda>" 
    using points_index_pair filter_filter_mset_ss_member y_point assms finite_sets index_ge_zero 
    by (metis nat_0_le nat_int_comparison(1))
  then have  "\<And> y .y \<in># ?M \<Longrightarrow> size ({# bl \<in># ?B . x \<in> bl \<and> y \<in> bl#}) = nat \<Lambda>"
    by auto
  then have bl_set_size: "\<And> y . y \<in># ?M \<Longrightarrow> size ({# bl \<in># ?B .  y \<in> bl#}) = nat \<Lambda>" 
    using b_contents by (metis (no_types, lifting) filter_mset_cong) 
  then have final_size: "size (\<Sum>p\<in>#?M . ({#p#} \<times># {#bl \<in># ?B. p \<in> bl#})) = size (?M) * (nat \<Lambda>)" 
    using m_distinct size_Union_distinct_cart_prod_filter bl_set_size index_ge_zero by blast  
  have "size ?M = \<v> - 1" using v_non_zero
    by (simp add: assms(1) finite_sets) 
  thus ?thesis using final_size 
    by (simp add: set_break_down_left index_ge_zero) 
qed

lemma necess_cond_1_lhs: 
  assumes "x \<in> \<V>"
  shows "size ({# p \<in># (mset_set (\<V> - {x}) \<times># {# bl \<in># \<B> . x \<in> bl #}). fst p \<in> snd p#}) 
      = (\<B> rep x) * (\<k> - 1)" 
    (is "size ({# p \<in># (?M \<times># ?B). fst p \<in> snd p#}) = (\<B> rep x) * (\<k> - 1) ")
proof -
  have "\<And> y. y \<in># ?M \<Longrightarrow> y \<noteq> x" using assms
    by (simp add: finite_sets)
  have distinct_m: "distinct_mset ?M" using assms mset_points_distinct_diff_one by simp
  have finite_M: "finite (\<V> - {x})" using finite_sets by auto
  have block_choices: "size ?B = \<B> rep x"
    by (simp add: assms(1) point_replication_number_def)
  have bl_size: "\<forall> bl \<in># ?B. card {p \<in> \<V> . p \<in> bl } = \<k> " using uniform_unfold_point_set by simp
  have x_in_set: "\<forall> bl \<in># ?B . {x} \<subseteq> {p \<in> \<V>. p \<in> bl}" using assms by auto
  then have "\<forall> bl \<in># ?B. card {p \<in> (\<V> - {x}) . p \<in> bl } = card ({p \<in> \<V> . p \<in> bl } - {x})" 
    by (simp add: set_filter_diff_card)
  then have "\<forall> bl \<in># ?B. card {p \<in> (\<V> - {x}) . p \<in> bl } = \<k> - 1" 
    using bl_size x_in_set card_Diff_subset finite_sets k_non_zero by auto
  then have "\<And> bl . bl \<in># ?B \<Longrightarrow> size {#p \<in># ?M . p \<in> bl#} = nat (\<k> - 1)" 
    using assms finite_M card_size_filter_eq by auto
  then have "size (\<Sum>bl\<in>#?B. ( {# p \<in># ?M . p \<in> bl #} \<times># {#bl#})) = size (?B) * nat (\<k> - 1)" 
    using distinct_m size_Union_distinct_cart_prod_filter2 by blast
  thus ?thesis using block_choices k_non_zero by (simp add: set_break_down_right)
qed

lemma r_constant: "x \<in> \<V> \<Longrightarrow> (\<B> rep x) * (\<k> -1) = \<Lambda> * (\<v> - 1)"
  using necess_cond_1_rhs necess_cond_1_lhs design_points_nempty by force

lemma replication_number_value:
  assumes "x \<in> \<V>"
  shows "(\<B> rep x) = \<Lambda> * (\<v> - 1) div (\<k> - 1)"
  using min_block_size_2 r_constant assms diff_gt_0_iff_gt diff_self zle_diff1_eq numeral_le_one_iff
  by (metis less_int_code(1) linorder_neqE_linordered_idom nonzero_mult_div_cancel_right semiring_norm(69))
  
lemma r_constant_alt: "\<forall> x \<in> \<V>. \<B> rep x = \<Lambda> * (\<v> - 1) div (\<k> - 1)"
  using r_constant replication_number_value by blast 

end 

text \<open>Using the first necessary condition, it is possible to show that a bibd has 
a constant replication number\<close>

sublocale bibd \<subseteq> constant_rep_design \<V> \<B>  "(\<Lambda> * (\<v> - 1) div (\<k> - 1))"
  using r_constant_alt by (unfold_locales) simp_all

lemma (in t_design) bibdI [intro]: "\<t> = 2 \<Longrightarrow> bibd \<V> \<B> \<k> \<Lambda>\<^sub>t"
  using t_lt_order block_size_t by (unfold_locales) (simp_all)

context bibd
begin

abbreviation "\<r> \<equiv> (\<Lambda> * (\<v> - 1) div (\<k> - 1))"

lemma necessary_condition_one: 
  shows "\<r> * (\<k> - 1) = \<Lambda> * (\<v> - 1)"
  using necess_cond_1_rhs necess_cond_1_lhs design_points_nempty rep_number by auto

lemma bibd_point_occ_rep: 
  assumes "x \<in> bl"
  assumes "bl \<in># \<B>"
  shows  "(\<B> - {#bl#}) rep x = \<r> - 1"
proof -
  have xin: "x \<in> \<V>" using assms wf_invalid_point by blast
  then have rep: "size {# blk \<in># \<B>. x \<in> blk #} = \<r>" using rep_number_unfold_set by simp
  have "(\<B> - {#bl#}) rep x = size {# blk \<in># (\<B> - {#bl#}). x \<in> blk #}" 
    by (simp add: point_replication_number_def)
  then have "(\<B> - {#bl#}) rep x = size {# blk \<in># \<B>. x \<in> blk #} - 1"
    by (simp add: assms size_Diff_singleton) 
  then show ?thesis using assms rep r_gzero by simp
qed 

lemma necess_cond_2_lhs: "size {# x \<in># (mset_set \<V> \<times># \<B>) . (fst x) \<in> (snd x)  #} = \<v> * \<r>" 
proof -
  let ?M = "mset_set \<V>"
  have "\<And> p . p \<in># ?M \<Longrightarrow> size ({# bl \<in># \<B> . p \<in> bl #}) = nat (\<r>)"
    using finite_sets rep_number_unfold_set r_gzero nat_eq_iff2 by auto 
  then have "size (\<Sum>p\<in>#?M. ({#p#} \<times># {#bl \<in># \<B>. p \<in> bl#})) = size ?M * nat (\<r>)" 
    using mset_points_distinct size_Union_distinct_cart_prod_filter by blast
  thus ?thesis using r_gzero
    by (simp add: set_break_down_left)  
qed

lemma necess_cond_2_rhs: "size {# x \<in># (mset_set \<V> \<times># \<B>) . (fst x) \<in> (snd x)  #} = \<b>*\<k>" 
  (is "size {# x \<in># (?M \<times># ?B). (fst x) \<in> (snd x)  #} = \<b>*\<k>")
proof -
  have "\<And> bl . bl \<in># ?B \<Longrightarrow> size ({# p \<in># ?M . p \<in> bl #}) = nat \<k>" 
    using uniform k_non_zero uniform_unfold_point_set_mset by fastforce
  then have "size (\<Sum>bl\<in>#?B. ( {# p \<in># ?M . p \<in> bl #} \<times># {#bl#})) = size (?B) * (nat \<k>)" 
    using mset_points_distinct size_Union_distinct_cart_prod_filter2 by blast
  thus ?thesis using k_non_zero by (simp add: set_break_down_right)
qed

lemma necessary_condition_two:
  shows "\<v> * \<r> = \<b> * \<k>"
  using necess_cond_2_lhs necess_cond_2_rhs by simp

theorem admissability_conditions:
"\<r> * (\<k> - 1) = \<Lambda> * (\<v> - 1)"
"\<v> * \<r> = \<b> * \<k>"
  using necessary_condition_one necessary_condition_two by auto

subsubsection \<open>BIBD Param Relationships\<close>

lemma bibd_block_number: "\<b> = \<Lambda> * \<v> * (\<v> - 1) div (\<k> * (\<k>-1))"
proof -
  have "\<b> * \<k> = (\<v> * \<r>)" using necessary_condition_two by simp
  then have k_dvd: "\<k> dvd (\<v> * \<r>)" by (metis dvd_triv_right) 
  then have "\<b> = (\<v> * \<r>) div \<k>" using necessary_condition_two min_block_size_2 by auto
  then have "\<b> = (\<v> * ((\<Lambda> * (\<v> - 1) div (\<k> - 1)))) div \<k>" by simp
  then have "\<b> = (\<v> * \<Lambda> * (\<v> - 1)) div ((\<k> - 1)* \<k>)" using necessary_condition_one 
      necessary_condition_two dvd_div_div_eq_mult dvd_div_eq_0_iff
    by (smt (z3) dvd_triv_right mult.assoc mult.commute mult.left_commute mult_eq_0_iff ) 
  then show ?thesis by (simp add: mult.commute) 
qed

lemma symmetric_condition_1: "\<Lambda> * (\<v> - 1) = \<k> * (\<k> - 1) \<Longrightarrow> \<b> = \<v> \<and> \<r> = \<k>"
  using b_non_zero bibd_block_number mult_eq_0_iff necessary_condition_two necessary_condition_one 
  by auto

lemma index_lt_replication: "\<Lambda> < \<r>"
proof -
  have 1: "\<r> * (\<k> - 1) = \<Lambda> * (\<v> - 1)" using admissability_conditions by simp
  have lhsnot0: "\<r> * (\<k> - 1) \<noteq> 0"
    using no_zero_divisors rep_not_zero zdiv_eq_0_iff by blast 
  then have rhsnot0: "\<Lambda> * (\<v> - 1) \<noteq> 0" using 1 by simp 
  have "\<k> - 1 < \<v> - 1" using incomplete b_non_zero bibd_block_number not_less_eq by fastforce 
  thus ?thesis using 1 lhsnot0 rhsnot0
    by (smt (verit, best) k_non_zero mult_le_less_imp_less r_gzero) 
qed

lemma index_not_zero: "\<Lambda> \<ge> 1"
  using index_ge_zero index_lt_replication int_one_le_iff_zero_less by fastforce 

lemma r_ge_two: "\<r> \<ge> 2"
  using index_lt_replication index_not_zero by linarith

lemma block_num_gt_rep: "\<b> > \<r>"
proof -
  have fact: "\<b> * \<k> = \<v> * \<r>" using admissability_conditions by auto
  have lhsnot0: "\<b> * \<k> \<noteq> 0" using k_non_zero b_non_zero by auto 
  then have rhsnot0: "\<v> * \<r> \<noteq> 0" using fact by simp
  then show ?thesis using incomplete lhsnot0
    using complement_rep_number constant_rep_design.r_gzero incomplete_imp_incomp_block by fastforce 
qed

lemma bibd_subset_occ: 
  assumes "x \<subseteq> bl" and "bl \<in># \<B>" and "card x = 2"
  shows "size {# blk \<in># (\<B> - {#bl#}). x \<subseteq> blk #} = \<Lambda> - 1"
proof - 
  have index: "size {# blk \<in># \<B>. x \<subseteq> blk #} = \<Lambda>" using points_index_def balanced assms
    by (metis (full_types) of_nat_numeral subset_eq wf_invalid_point) 
  then have "size {# blk \<in># (\<B> - {#bl#}). x \<subseteq> blk #} = size {# blk \<in># \<B>. x \<subseteq> blk #} - 1" 
    by (simp add: assms size_Diff_singleton) 
  then show ?thesis using assms index_not_zero index by simp
qed

lemma necess_cond_one_param_balance: "\<b> > \<v> \<Longrightarrow> \<r> > \<k>"
  using necessary_condition_two
  by (smt mult_nonneg_nonneg nonzero_mult_div_cancel_right of_nat_0_le_iff r_gzero zdiv_mono2)

subsection \<open>Constructing New bibd's\<close>
text \<open>There are many constructions on bibd's to establish new bibds (or other types of designs). 
This section demonstrates this using both existing constructions, and by defining new constructions.\<close>
subsubsection \<open>BIBD Complement, Multiple, Combine\<close>

lemma comp_params_index_pair:
  assumes "{x, y} \<subseteq> \<V>"
  assumes "x \<noteq> y"
  shows "\<B>\<^sup>C index {x, y} = \<b> + \<Lambda> - 2*\<r>"
proof -
  have xin: "x \<in> \<V>" and yin: "y \<in> \<V>" using assms by auto
  have ge: "2*\<r> \<ge> \<Lambda>" using index_lt_replication
    using r_gzero by linarith 
  have "size {# b \<in># \<B> . x \<in> b \<and> y \<in> b#} =  \<Lambda>" using points_index_pair assms by simp
  then have lambda: "size {# b \<in># \<B> . x \<in> b \<and> y \<in> b#} = nat \<Lambda>" 
    using index_ge_zero by auto 
  have "\<B>\<^sup>C index {x, y} = size {# b \<in># \<B> . x \<notin> b \<and> y \<notin> b #}" 
    using complement_index_2 assms by simp
  also have "\<dots> = size \<B> - (size {# b \<in># \<B> . \<not> (x \<notin> b \<and> y \<notin> b) #})" 
    using size_filter_neg by blast
  also have "... = size \<B> - (size {# b \<in># \<B> . x \<in> b \<or> y \<in> b#})" by auto
  also have "... = \<b> - (size {# b \<in># \<B> . x \<in> b \<or> y \<in> b#})" by (simp add: of_nat_diff)
  also have "... = \<b> - (size {# b \<in># \<B> . x \<in> b#} +  
    size {# b \<in># \<B> . y \<in> b#} -  size {# b \<in># \<B> . x \<in> b \<and> y \<in> b#})" 
    by (simp add: mset_size_partition_dep) 
  also have "... = \<b> - (nat \<r> + nat \<r> - nat (\<Lambda>))" using rep_number_unfold_set lambda xin yin
    by (metis (no_types, lifting) nat_int)
  finally have "\<B>\<^sup>C index {x, y} = \<b> - (2*\<r> - \<Lambda>)"
    using index_ge_zero index_lt_replication by linarith
  thus ?thesis using ge diff_diff_right by simp  
qed

lemma complement_bibd_index: 
  assumes "ps \<subseteq> \<V>"
  assumes "card ps = 2"
  shows "\<B>\<^sup>C index ps = \<b> + \<Lambda> - 2*\<r>"
proof -
  obtain x y where set: "ps = {x, y}" using b_non_zero bibd_block_number diff_is_0_eq incomplete 
    mult_0_right nat_less_le design_points_nempty assms by (metis card_2_iff) 
  then have "x \<noteq> y" using assms by auto 
  thus ?thesis using comp_params_index_pair assms
    by (simp add: set)
qed

lemma complement_bibd: 
  assumes "\<k> \<le> \<v> - 2" 
  shows "bibd \<V> \<B>\<^sup>C (\<v> - \<k>) (\<b> + \<Lambda> - 2*\<r>)"
proof -
  interpret des: incomplete_design \<V> "\<B>\<^sup>C" "(\<v> - \<k>)" 
    using assms complement_incomplete by blast
  show ?thesis proof (unfold_locales, simp_all)
    show "2 \<le> des.\<v>" using assms block_size_t by linarith 
    show "\<And>ps. ps \<subseteq> \<V> \<Longrightarrow> card ps = 2 \<Longrightarrow> 
      \<B>\<^sup>C index ps = \<b> + \<Lambda> - 2 * (\<Lambda> * (des.\<v> - 1) div (\<k> - 1))" 
      using complement_bibd_index by simp
    show "2 \<le> des.\<v> - \<k>" using assms block_size_t by linarith 
  qed
qed

lemma multiple_bibd: "n > 0 \<Longrightarrow> bibd \<V> (multiple_blocks n) \<k> (\<Lambda> * n)"
  using multiple_t_design by (simp add: bibd_def)  

end 

locale two_bibd_eq_points = two_t_designs_eq_points \<V> \<B> \<k> \<B>' 2 \<Lambda> \<Lambda>'
  + des1: bibd \<V> \<B> \<k> \<Lambda> + des2: bibd \<V> \<B>' \<k> \<Lambda>' for \<V> \<B> \<k> \<B>' \<Lambda> \<Lambda>'
begin

lemma combine_is_bibd: "bibd \<V>\<^sup>+ \<B>\<^sup>+ \<k> (\<Lambda> + \<Lambda>')"
  by (unfold_locales)

sublocale combine_bibd: bibd "\<V>\<^sup>+" "\<B>\<^sup>+" "\<k>" "(\<Lambda> + \<Lambda>')"
  by (unfold_locales)

end 

subsubsection \<open>Derived Designs\<close>
text \<open>A derived bibd takes a block from a valid bibd as the new point sets, and the intersection 
of that block with other blocks as it's block set\<close>

locale bibd_block_transformations = bibd + 
  fixes block :: "'a set" ("bl")
  assumes valid_block: "bl \<in># \<B>"
begin

definition derived_blocks :: "'a set multiset" ("(\<B>\<^sup>D)") where 
"\<B>\<^sup>D \<equiv> {# bl \<inter> b . b \<in># (\<B> - {#bl#}) #}"

lemma derive_define_flip: "{# b \<inter> bl . b \<in># (\<B> - {#bl#}) #} = \<B>\<^sup>D"
  by (simp add: derived_blocks_def inf_sup_aci(1))

lemma derived_points_order: "card bl = \<k>"
  using uniform valid_block by simp

lemma derived_block_num: "bl \<in># \<B> \<Longrightarrow> size \<B>\<^sup>D = \<b> - 1"
  apply (simp add: derived_blocks_def size_remove1_mset_If valid_block)
  using valid_block int_ops(6) by fastforce

lemma derived_is_wellformed:  "b \<in># \<B>\<^sup>D \<Longrightarrow> b \<subseteq> bl"
  by (simp add: derived_blocks_def valid_block) (auto)

lemma derived_point_subset_orig: "ps \<subseteq> bl \<Longrightarrow> ps \<subset> \<V>"
  by (simp add: valid_block incomplete_imp_proper_subset subset_psubset_trans) 

lemma derived_obtain_orig_block: 
  assumes "b \<in># \<B>\<^sup>D"
  obtains b2 where "b = b2 \<inter> bl" and "b2 \<in># remove1_mset bl \<B>"
  using assms derived_blocks_def by auto

sublocale derived_incidence_sys: incidence_system "bl" "\<B>\<^sup>D"
  using derived_is_wellformed valid_block by (unfold_locales) (auto)

sublocale derived_fin_incidence_system: finite_incidence_system "bl" "\<B>\<^sup>D"
  using valid_block finite_blocks by (unfold_locales) simp_all

lemma derived_blocks_nempty:
  assumes "\<And> b .b \<in># remove1_mset bl \<B> \<Longrightarrow> bl |\<inter>| b > 0"
  assumes "bld \<in># \<B>\<^sup>D"
  shows "bld \<noteq> {}"
proof -
  obtain bl2 where inter: "bld = bl2 \<inter> bl" and member: "bl2 \<in># remove1_mset bl \<B>" 
    using assms derived_obtain_orig_block by blast
  then have "bl |\<inter>| bl2 > 0" using assms(1) by blast
  thus ?thesis using intersection_number_empty_iff finite_blocks valid_block
    by (metis Int_commute dual_order.irrefl inter) 
qed

lemma derived_is_design:
  assumes "\<And> b. b \<in># remove1_mset bl \<B> \<Longrightarrow> bl |\<inter>| b > 0"
  shows "design bl \<B>\<^sup>D"
proof -
  interpret fin: finite_incidence_system "bl" "\<B>\<^sup>D"
    by (unfold_locales)
  show ?thesis using assms derived_blocks_nempty by (unfold_locales) simp
qed

lemma derived_is_proper: 
  assumes "\<And> b. b \<in># remove1_mset bl \<B> \<Longrightarrow> bl |\<inter>| b > 0"
  shows "proper_design bl \<B>\<^sup>D"
proof -
  interpret des: design "bl" "\<B>\<^sup>D" 
    using derived_is_design assms by fastforce 
  have "\<b> - 1 > 1" using block_num_gt_rep r_ge_two by linarith  
  then show ?thesis by (unfold_locales) (simp add: derived_block_num valid_block)
qed


subsubsection \<open>Residual Designs\<close>
text \<open>Similar to derived designs, a residual design takes the complement of a block bl as it's new
point set, and the complement of all other blocks with respect to bl.\<close>

definition residual_blocks :: "'a set multiset" ("(\<B>\<^sup>R)") where
"\<B>\<^sup>R \<equiv> {# b - bl . b \<in># (\<B> - {#bl#}) #}" 

lemma residual_order: "card (bl\<^sup>c) = \<v> - \<k>" 
  apply (simp add: valid_block wellformed block_complement_size)
  using block_size_lt_v derived_points_order by auto

lemma residual_block_num: "size (\<B>\<^sup>R) = \<b> - 1"
  using b_positive by (simp add: residual_blocks_def size_remove1_mset_If valid_block int_ops(6))

lemma residual_obtain_orig_block: 
  assumes "b \<in># \<B>\<^sup>R"
  obtains bl2 where "b = bl2 - bl" and "bl2 \<in># remove1_mset bl \<B>"
  using assms residual_blocks_def by auto

lemma residual_blocks_ss: assumes "b \<in># \<B>\<^sup>R" shows "b \<subseteq> \<V>"
proof -
  have "b \<subseteq> (bl\<^sup>c)" using residual_obtain_orig_block
    by (metis Diff_mono assms block_complement_def in_diffD order_refl wellformed)
  thus ?thesis
    using block_complement_subset_points by auto 
qed

lemma residual_blocks_exclude: "b \<in># \<B>\<^sup>R \<Longrightarrow> x \<in> b \<Longrightarrow> x \<notin> bl"
  using residual_obtain_orig_block by auto

lemma residual_is_wellformed:  "b \<in># \<B>\<^sup>R \<Longrightarrow> b \<subseteq> (bl\<^sup>c)"
  apply (auto simp add: residual_blocks_def)
  by (metis DiffI block_complement_def in_diffD wf_invalid_point) 

sublocale residual_incidence_sys: incidence_system "bl\<^sup>c" "\<B>\<^sup>R"
  using residual_is_wellformed by (unfold_locales)

lemma residual_is_finite: "finite (bl\<^sup>c)"
  by (simp add: block_complement_def finite_sets)

sublocale residual_fin_incidence_sys: finite_incidence_system "bl\<^sup>c" "\<B>\<^sup>R"
  using residual_is_finite by (unfold_locales) 

lemma residual_blocks_nempty:
  assumes "bld \<in># \<B>\<^sup>R"
  assumes "multiplicity bl = 1" 
  shows "bld \<noteq> {}"
proof -
  obtain bl2 where inter: "bld = bl2 - bl" and member: "bl2 \<in># remove1_mset bl \<B>" 
    using assms residual_blocks_def by auto 
  then have ne: "bl2 \<noteq> bl" using assms
    by (metis count_eq_zero_iff in_diff_count less_one union_single_eq_member)
  have "card bl2 = card bl" using uniform valid_block member
    by (metis in_diffD of_nat_eq_iff)  
  then have "card (bl2 - bl) > 0" 
    using finite_blocks member uniform set_card_diff_ge_zero valid_block by (metis in_diffD ne) 
  thus ?thesis using inter by fastforce 
qed

lemma residual_is_design: "multiplicity bl = 1 \<Longrightarrow> design (bl\<^sup>c) \<B>\<^sup>R"
  using residual_blocks_nempty by (unfold_locales)

lemma residual_is_proper: 
  assumes "multiplicity bl = 1" 
  shows "proper_design (bl\<^sup>c) \<B>\<^sup>R"
proof -
  interpret des: design "bl\<^sup>c" "\<B>\<^sup>R" using residual_is_design assms by blast 
  have "\<b> - 1 > 1" using r_ge_two block_num_gt_rep by linarith 
  then show ?thesis using residual_block_num by (unfold_locales) auto
qed

end

subsection \<open>Symmetric BIBD's\<close>
text \<open>Symmetric bibd's are those where the order of the design equals the number of blocks\<close>

locale symmetric_bibd = bibd + 
  assumes symmetric: "\<b> = \<v>"
begin

lemma rep_value_sym: "\<r> = \<k>"
  using b_non_zero local.symmetric necessary_condition_two by auto

lemma symmetric_condition_2: "\<Lambda> * (\<v> - 1) = \<k> * (\<k> - 1)"
  using necessary_condition_one rep_value_sym by auto

lemma sym_design_vk_gt_kl: 
  assumes "\<k> \<ge> \<Lambda> + 2"
  shows "\<v> - \<k> > \<k> - \<Lambda>"
proof (rule ccontr)
  assume "\<not> (\<v> - \<k> > \<k> - \<Lambda>)"
  then have "\<v> \<le> 2 * \<k> - \<Lambda>"
    by linarith
  then have "\<v> - 1 \<le> 2 * \<k> - \<Lambda> - 1" by linarith
  then have "\<Lambda>* (\<v> - 1) \<le> \<Lambda>*( 2 * \<k> - \<Lambda> - 1)"
    using index_ge_zero mult_le_cancel_left by fastforce 
  then have "\<k> * (\<k> - 1) \<le> \<Lambda>*( 2 * \<k> - \<Lambda> - 1)"
    by (simp add: symmetric_condition_2)
  then have "\<k> * (\<k> - 1) - \<Lambda>*( 2 * \<k> - \<Lambda> - 1) \<le> 0" by linarith
  then have "(\<k> - \<Lambda>)*(\<k> - \<Lambda> - 1) \<le> 0"
    by (simp add: mult.commute right_diff_distrib')
  then have "\<k> = \<Lambda> \<or> \<k> = \<Lambda> + 1"
    using mult_le_0_iff by force
  thus False using assms
    by simp 
qed

end 

context bibd
begin

lemma symmetric_bibdI: "\<b> = \<v> \<Longrightarrow> symmetric_bibd \<V> \<B> \<k> \<Lambda>"
  by unfold_locales simp

lemma symmetric_bibdII: "\<Lambda> * (\<v> - 1) = \<k> * (\<k> - 1) \<Longrightarrow> symmetric_bibd \<V> \<B> \<k> \<Lambda>"
  using symmetric_condition_1 by unfold_locales blast 

lemma symmetric_not_admissable: "\<Lambda> * (\<v> - 1) \<noteq> \<k> * (\<k> - 1) \<Longrightarrow> \<not> symmetric_bibd \<V> \<B> \<k> \<Lambda>"
  using symmetric_bibd.symmetric_condition_2 by blast 
end

context symmetric_bibd
begin

subsubsection \<open>Intersection Property on Symmetric BIBDs\<close>
text \<open>Below is a proof of an important property on symmetric BIBD's regarding the equivalence
of intersection numbers and the design index. This is an intuitive counting proof, and involved
significantly more work in a formal environment. Based of Lecture Note \cite{HerkeLectureNotes2016}\<close>

lemma intersect_mult_set_eq_block:
  assumes "blv \<in># \<B>"
  shows "p \<in># \<Sum>\<^sub>#{# mset_set (bl \<inter> blv) .bl \<in># (\<B> - {#blv#})#} \<longleftrightarrow> p \<in> blv"
proof (auto, simp add: assms finite_blocks)
  assume assm: "p \<in> blv"
  then have "(\<B> - {#blv#}) rep p > 0" using bibd_point_occ_rep r_ge_two assms by auto 
  then obtain bl where "bl \<in># (\<B> - {#blv#}) \<and> p \<in> bl" using assms rep_number_g0_exists by metis
  then show "\<exists>x\<in>#remove1_mset blv \<B>. p \<in># mset_set (x \<inter> blv)" 
    using assms assm finite_blocks by auto 
qed

lemma intersect_mult_set_block_subset_iff:
  assumes "blv \<in># \<B>"
  assumes "p \<in># \<Sum>\<^sub>#{# mset_set {y .y \<subseteq> blv \<inter> b2 \<and> card y = 2} .b2 \<in># (\<B> - {#blv#})#}"
  shows "p \<subseteq> blv"
proof (rule subsetI)
  fix x
  assume asm: "x \<in> p"
  obtain b2 where "p \<in># mset_set {y . y \<subseteq> blv \<inter> b2 \<and> card y = 2} \<and> b2 \<in>#(\<B> - {#blv#})" 
    using assms by blast
  then have "p \<subseteq> blv \<inter> b2"
    by (metis (no_types, lifting) elem_mset_set equals0D infinite_set_mset_mset_set mem_Collect_eq) 
  thus "x \<in> blv" using asm by auto
qed

lemma intersect_mult_set_block_subset_card:
  assumes "blv \<in># \<B>"
  assumes "p \<in># \<Sum>\<^sub>#{# mset_set {y .y \<subseteq> blv \<inter> b2 \<and> card y = 2} .b2 \<in># (\<B> - {#blv#})#}"
  shows "card p = 2"
proof -
  obtain b2 where "p \<in># mset_set {y . y \<subseteq> blv \<inter> b2 \<and> card y = 2} \<and> b2 \<in>#(\<B> - {#blv#})" 
    using assms by blast
  thus ?thesis
    by (metis (mono_tags, lifting) elem_mset_set equals0D infinite_set_mset_mset_set mem_Collect_eq) 
qed

lemma intersect_mult_set_block_with_point_exists: 
  assumes "blv \<in># \<B>" and  "p \<subseteq> blv" and "\<Lambda> \<ge> 2" and "card p = 2"
  shows "\<exists>x\<in>#remove1_mset blv \<B>. p \<in># mset_set {y. y \<subseteq> blv \<and> y \<subseteq> x \<and> card y = 2}"
proof -
  have "size {#b \<in># \<B> . p \<subseteq> b#} = \<Lambda>" using points_index_def assms 
    by (metis balanced_alt_def_all dual_order.trans of_nat_numeral wellformed) 
  then have "size {#bl \<in># (\<B> - {#blv#}) . p \<subseteq> bl#} \<ge> 1"  
    using assms by (simp add: size_Diff_singleton)
  then obtain bl where "bl \<in># (\<B> - {#blv#}) \<and> p \<subseteq> bl" using assms filter_mset_empty_conv
     by (metis diff_diff_cancel diff_is_0_eq' le_numeral_extra(4) size_empty zero_neq_one) 
  thus ?thesis 
    using assms finite_blocks by auto 
qed

lemma intersect_mult_set_block_subset_iff_2:
  assumes "blv \<in># \<B>" and  "p \<subseteq> blv" and "\<Lambda> \<ge> 2" and "card p = 2"
  shows "p \<in># \<Sum>\<^sub>#{# mset_set {y .y \<subseteq> blv \<inter> b2 \<and> card y = 2} .b2 \<in># (\<B> - {#blv#})#}"
  by (auto simp add: intersect_mult_set_block_with_point_exists assms)

lemma sym_sum_mset_inter_sets_count: 
  assumes "blv \<in># \<B>"
  assumes "p \<in> blv"
  shows "count (\<Sum>\<^sub>#{# mset_set (bl \<inter> blv) .bl \<in># (\<B> - {#blv#})#}) p = \<r> - 1" 
    (is "count (\<Sum>\<^sub>#?M) p = \<r> - 1")
proof -
  have size_inter: "size {# mset_set (bl \<inter> blv) | bl  \<in># (\<B> - {#blv#}) . p \<in> bl#} = \<r> - 1"
    using bibd_point_occ_rep point_replication_number_def
    by (metis assms(1) assms(2) size_image_mset)  
  have inter_finite: "\<forall> bl \<in># (\<B> - {#blv#}) . finite (bl \<inter> blv)"
    by (simp add: assms(1) finite_blocks)
  have "\<And> bl . bl \<in># (\<B> - {#blv#}) \<Longrightarrow> p \<in> bl \<longrightarrow> count (mset_set (bl \<inter> blv)) p = 1"
    using assms count_mset_set(1) inter_finite by simp 
  then have "\<And> bl . bl \<in># {#b1 \<in>#(\<B> - {#blv#}) . p \<in> b1#} \<Longrightarrow> count (mset_set (bl \<inter> blv)) p = 1"
    by (metis (full_types) count_eq_zero_iff count_filter_mset) 
  then have pin: "\<And> P. P \<in># {# mset_set (bl \<inter> blv) | bl \<in># (\<B> - {#blv#}) . p \<in> bl#} 
      \<Longrightarrow> count P p = 1" by blast
  have "?M = {# mset_set (bl \<inter> blv) | bl \<in># (\<B> - {#blv#}) . p \<in> bl#} 
      + {# mset_set (bl \<inter> blv) | bl \<in># (\<B> - {#blv#}) . p \<notin> bl#}"
    by (metis image_mset_union multiset_partition) 
  then have "count (\<Sum>\<^sub>#?M) p = size {# mset_set (bl \<inter> blv) | bl \<in># (\<B> - {#blv#}) . p \<in> bl#} " 
    using pin by (auto simp add: count_sum_mset)
  then show ?thesis using size_inter by linarith   
qed

lemma sym_sum_mset_inter_sets_size: 
  assumes "blv \<in># \<B>"
  shows "size (\<Sum>\<^sub>#{# mset_set (bl \<inter> blv) .bl \<in># (\<B> - {#blv#})#}) = \<k> * (\<r> - 1)" 
    (is "size (\<Sum>\<^sub>#?M) = \<k>* (\<r> - 1)")
proof - 
  have eq: "set_mset (\<Sum>\<^sub>#{# mset_set (bl \<inter> blv) .bl \<in># (\<B> - {#blv#})#}) = blv" 
    using intersect_mult_set_eq_block assms by auto
  then have k: "card (set_mset (\<Sum>\<^sub>#?M)) = \<k>"
    by (simp add: assms)
  have "\<And> p. p \<in># (\<Sum>\<^sub>#?M) \<Longrightarrow> count (\<Sum>\<^sub>#?M) p = \<r> - 1" 
    using sym_sum_mset_inter_sets_count assms eq by blast 
  thus ?thesis using k size_multiset_int_count by metis
qed

lemma sym_sum_inter_num: 
  assumes "b1 \<in># \<B>" 
  shows "(\<Sum>b2 \<in>#(\<B> - {#b1#}). b1 |\<inter>| b2) = \<k>* (\<r> - 1)"
proof -
  have "(\<Sum>b2 \<in>#(\<B> - {#b1#}). b1 |\<inter>| b2) = (\<Sum>b2 \<in>#(\<B> - {#b1#}). size (mset_set (b1 \<inter> b2)))" 
    by (simp add: intersection_number_def)
  also have "... = size (\<Sum>\<^sub>#{#mset_set (b1 \<inter> bl). bl \<in># (\<B> - {#b1#})#})"
    by (auto simp add: size_big_union_sum) 
  also have "... =  size (\<Sum>\<^sub>#{#mset_set (bl \<inter> b1). bl \<in># (\<B> - {#b1#})#})"
    by (metis Int_commute) 
  finally have "(\<Sum>b2 \<in>#(\<B> - {#b1#}). b1 |\<inter>| b2) = \<k> * (\<r> - 1)" 
    using sym_sum_mset_inter_sets_size assms by auto
  then show ?thesis by simp
qed

lemma choose_two_int: 
  assumes " x \<ge> 0" 
  shows "nat (x :: int) choose 2 = ((x ::int) * ( x - 1)) div 2 " 
  using choose_two assms dvd_div_mult_self even_numeral int_nat_eq mult_cancel_right2 mult_eq_0_iff 
    mult_nonneg_nonneg nat_diff_distrib' nat_mult_distrib nat_one_as_int 
    numeral_Bit0_div_2 numerals(1) of_nat_numeral zdiv_int by (smt (verit)) (* Slow *)

lemma sym_sum_mset_inter2_sets_count: 
  assumes "blv \<in># \<B>"
  assumes "p \<subseteq> blv"
  assumes "card p = 2"
  shows "count (\<Sum>\<^sub>#{#mset_set {y .y \<subseteq> blv \<inter> b2 \<and> card y = 2}. b2 \<in># (\<B> - {#blv#})#}) p = \<Lambda> - 1" 
    (is "count (\<Sum>\<^sub>#?M) p = \<Lambda> - 1")
proof -
  have size_inter: "size {# mset_set {y .y \<subseteq> blv \<inter> b2 \<and> card y = 2} | b2 \<in># (\<B> - {#blv#}) . p \<subseteq> b2#} 
      = \<Lambda> - 1"
    using bibd_subset_occ assms by simp
  have "\<forall> b2 \<in># (\<B> - {#blv#}) . p \<subseteq> b2 \<longrightarrow> count (mset_set{y .y \<subseteq> blv \<inter> b2 \<and> card y = 2}) p = 1"
    using assms(2) count_mset_set(1) assms(3) by (auto simp add: assms(1) finite_blocks)
  then have "\<forall> bl \<in># {#b1 \<in>#(\<B> - {#blv#}) . p \<subseteq> b1#}. 
      count (mset_set {y .y \<subseteq> blv \<inter> bl \<and> card y = 2}) p = 1"
    using count_eq_zero_iff count_filter_mset by (metis (no_types, lifting)) 
  then have pin: "\<forall> P \<in># {# mset_set {y .y \<subseteq> blv \<inter> b2 \<and> card y = 2} | b2 \<in># (\<B> - {#blv#}) . p \<subseteq> b2#}. 
      count P p = 1"
    using count_eq_zero_iff count_filter_mset by blast
  have "?M = {# mset_set {y .y \<subseteq> blv \<inter> b2 \<and> card y = 2} | b2 \<in># (\<B> - {#blv#}) . p \<subseteq> b2#} + 
              {# mset_set {y .y \<subseteq> blv \<inter> b2 \<and> card y = 2} | b2 \<in># (\<B> - {#blv#}) . \<not> (p \<subseteq> b2)#}" 
    by (metis image_mset_union multiset_partition) 
  then have "count (\<Sum>\<^sub>#?M) p = 
      size {# mset_set {y .y \<subseteq> blv \<inter> b2 \<and> card y = 2} | b2 \<in># (\<B> - {#blv#}) . p \<subseteq> b2#}" 
    using pin by (auto simp add: count_sum_mset)
  then show ?thesis using size_inter by linarith  
qed

lemma sym_sum_mset_inter2_sets_size: 
  assumes "blv \<in># \<B>"
  shows "size (\<Sum>\<^sub>#{#mset_set {y .y \<subseteq> blv \<inter> b2 \<and> card y = 2}. b2 \<in># (\<B> - {#blv#})#}) = 
    ((nat \<k>) choose 2) * (\<Lambda> -1)" 
    (is "size (\<Sum>\<^sub>#?M) = ((nat \<k>) choose 2) * (\<Lambda> -1)")
proof (cases "\<Lambda> = 1")
  case True
  have empty: "\<And> b2 . b2 \<in># remove1_mset blv \<B> \<Longrightarrow> {y .y \<subseteq> blv \<and> y \<subseteq> b2 \<and> card y = 2} = {}" 
    using index_one_alt_bl_not_exist assms True by blast
  then show ?thesis using sum_mset.neutral True by (simp add: empty)
next
  case False
  then have index_min: "\<Lambda> \<ge> 2" using index_not_zero by linarith 
  have subset_card: "\<And> x . x \<in># (\<Sum>\<^sub>#?M) \<Longrightarrow> card x = 2"
  proof -
    fix x
    assume a: "x \<in># (\<Sum>\<^sub>#?M)"
    then obtain b2 where "x \<in># mset_set {y . y \<subseteq> blv \<inter> b2 \<and> card y = 2} \<and> b2 \<in>#(\<B> - {#blv#})" 
      by blast
    thus "card x = 2" using mem_Collect_eq
      by (metis (mono_tags, lifting) elem_mset_set equals0D infinite_set_mset_mset_set)
  qed
  have eq: "set_mset (\<Sum>\<^sub>#?M) = {bl . bl \<subseteq> blv \<and> card bl = 2}" 
  proof
    show "set_mset (\<Sum>\<^sub>#?M) \<subseteq> {bl . bl \<subseteq> blv \<and> card bl = 2}"
      using subset_card intersect_mult_set_block_subset_iff assms by blast
    show "{bl . bl \<subseteq> blv \<and> card bl = 2} \<subseteq> set_mset (\<Sum>\<^sub>#?M)"
      using intersect_mult_set_block_subset_iff_2 assms index_min by blast
  qed
  have "card blv = (nat \<k>)" using uniform assms by (metis nat_int) 
  then have k: "card (set_mset (\<Sum>\<^sub>#?M)) = ((nat \<k>) choose 2)" using eq n_subsets
    by (simp add: n_subsets assms finite_blocks) 
  thus ?thesis using k size_multiset_int_count sym_sum_mset_inter2_sets_count assms eq subset_card
    by (metis (no_types, lifting) intersect_mult_set_block_subset_iff)
qed

lemma sum_choose_two_inter_num: 
  assumes "b1 \<in># \<B>" 
  shows "(\<Sum>b2 \<in># (\<B> - {#b1#}). (nat (b1 |\<inter>| b2) choose 2)) = ((\<Lambda> * (\<Lambda> - 1) div 2)) * (\<v> -1)"
proof - 
  have div_fact: "2 dvd (\<Lambda> * (\<Lambda> - 1))"by simp
  have div_fact_2: "2 dvd (\<Lambda> * (\<v> - 1))" using symmetric_condition_2 by simp
  have "(\<Sum>b2 \<in># (\<B> - {#b1#}). (nat (b1 |\<inter>| b2) choose 2)) = (\<Sum>b2 \<in># (\<B> - {#b1#}). nat (b1 |\<inter>|\<^sub>2 b2 ))" 
    using n_inter_num_choose_design_inter assms by (simp add: in_diffD)
  then have sum_fact: "(\<Sum>b2 \<in># (\<B> - {#b1#}).(nat (b1 |\<inter>| b2) choose 2)) 
      = ((nat \<k>) choose 2) * (\<Lambda> -1)" 
    using assms sym_sum_mset_inter2_sets_size 
    by (auto simp add: size_big_union_sum n_intersect_num_subset_def)
  have "((nat \<k>) choose 2) * (\<Lambda> -1) = ((\<Lambda> * (\<v> - 1) div 2)) * (\<Lambda> -1)" 
    using choose_two_int symmetric_condition_2 k_non_zero by auto 
  then have "((nat \<k>) choose 2) * (\<Lambda> -1) = ((\<Lambda> * (\<Lambda> - 1) div 2)) * (\<v> -1)" 
    using div_fact div_fact_2 by (smt div_mult_swap mult.assoc mult.commute) 
  then show ?thesis using sum_fact by simp
qed

lemma sym_sum_inter_num_sq: 
  assumes "b1 \<in># \<B>" 
  shows "(\<Sum>bl \<in># (remove1_mset b1 \<B>). (b1 |\<inter>| bl)^2) = \<Lambda>^2 * ( \<v> - 1)"
proof - 
  have dvd: "2 dvd (( \<v> - 1) * (\<Lambda> * (\<Lambda> - 1)))" by simp
  have a: "(\<Sum>b2 \<in>#(\<B> - {#b1#}). int (nat (b1 |\<inter>| b2) choose 2)) = 
            (\<Sum>bl \<in># (remove1_mset b1 \<B>).  ((b1 |\<inter>| bl) *  ((b1 |\<inter>| bl) - 1)) div 2)" 
    using choose_two_int by (simp add: intersection_num_non_neg)
  have b: "(\<Sum>b2 \<in>#(\<B> - {#b1#}). int (nat (b1 |\<inter>| b2) choose 2)) = 
              (\<Sum>b2 \<in>#(\<B> - {#b1#}). (nat (b1 |\<inter>| b2) choose 2))" by simp
  have "(\<Sum>b2 \<in>#(\<B> - {#b1#}). (nat (b1 |\<inter>| b2) choose 2)) = ((\<Lambda> * (\<Lambda> - 1)) div 2) * ( \<v> - 1)" 
    using sum_choose_two_inter_num assms by blast 
  then have start: "(\<Sum>bl \<in># (remove1_mset b1 \<B>). ((b1 |\<inter>| bl) *  ((b1 |\<inter>| bl) - 1)) div 2) 
                        = ((\<Lambda> * (\<Lambda> - 1)) div 2) * (\<v> - 1)"
    using a b by linarith
  have sum_dvd: "2 dvd (\<Sum>bl \<in># (remove1_mset b1 \<B>). (b1 |\<inter>| bl) *  ((b1 |\<inter>| bl) - 1))"
    by (simp add: sum_mset_dvd) 
  then have "(\<Sum>bl \<in># (remove1_mset b1 \<B>). (b1 |\<inter>| bl) * ((b1 |\<inter>| bl) - 1)) div 2 
      = (\<v> - 1) * ((\<Lambda> * (\<Lambda> - 1)) div 2)" 
    using start by (simp add: sum_mset_distrib_div_if_dvd)
  then have "(\<Sum>bl \<in># (remove1_mset b1 \<B>). (b1 |\<inter>| bl)^2) 
      - (\<Sum>bl \<in># (remove1_mset b1 \<B>). (b1 |\<inter>| bl)) = ((\<v> - 1) * (\<Lambda> * (\<Lambda> - 1)))"
    using sum_dvd dvd 
    by (simp add: dvd_div_eq_iff  div_mult_swap int_distrib(4) power2_eq_square sum_mset_add_diff)
  then have "(\<Sum>bl \<in># (remove1_mset b1 \<B>). (b1 |\<inter>| bl)^2) - (\<Lambda> * (\<v> - 1)) = ((\<v> - 1) * (\<Lambda> * (\<Lambda> - 1)))" 
    using sym_sum_inter_num assms rep_value_sym symmetric_condition_2 by auto 
  then have "(\<Sum>bl \<in># (remove1_mset b1 \<B>). (b1 |\<inter>| bl)^2) = (\<Lambda> * (\<v> - 1)) * (\<Lambda> - 1) + (\<Lambda> * (\<v> - 1))"
    using diff_eq_eq by fastforce 
  then have "(\<Sum>bl \<in># (remove1_mset b1 \<B>). (b1 |\<inter>| bl)^2) = (\<Lambda> * (\<v> - 1)) * (\<Lambda> - 1 + 1)" 
    using int_distrib(2) by (metis mult_numeral_1_right numeral_One)
  thus ?thesis by (simp add: power2_eq_square)
qed

lemma sym_sum_inter_num_to_zero: 
  assumes "b1 \<in># \<B>" 
  shows "(\<Sum>bl \<in># (remove1_mset b1 \<B>). ((b1 |\<inter>| bl) - \<Lambda>)^2) = 0"
proof -
  have rm1_size: "size (remove1_mset b1 \<B>) = \<v> - 1" using assms b_non_zero int_ops(6) 
    by (auto simp add: symmetric size_remove1_mset_If)
  have "\<And> bl . bl \<in># (remove1_mset b1 \<B>) \<Longrightarrow> ((b1 |\<inter>| bl) - \<Lambda>)^2 = 
        (((b1 |\<inter>| bl)^2) - (2 * \<Lambda> * (b1 |\<inter>| bl)) + (\<Lambda>^2))"
    by (simp add: power2_diff)
  then have "(\<Sum>bl \<in># (remove1_mset b1 \<B>). ((b1 |\<inter>| bl) - \<Lambda>)^2) = 
              (\<Sum>bl \<in># (remove1_mset b1 \<B>). (((b1 |\<inter>| bl)^2) - (2 * \<Lambda> * (b1 |\<inter>| bl)) + (\<Lambda>^2)))"
    using sum_over_fun_eq by auto
  also have "... = \<Lambda>^2 * (\<v> - 1) - 2 * \<Lambda> * (\<Sum>bl \<in># (remove1_mset b1 \<B>). ((b1 |\<inter>| bl))) 
      + (\<v> - 1) * (\<Lambda>^2)"
    using sym_sum_inter_num_sq rm1_size 
    by (simp add: assms sum_mset.distrib  sum_mset_add_diff sum_mset_distrib_left) 
  finally have "(\<Sum>bl \<in># (remove1_mset b1 \<B>). ((b1 |\<inter>| bl) - \<Lambda>)^2) = 0"
    using rep_value_sym symmetric_condition_2 sym_sum_inter_num assms 
    by (auto simp add: power2_eq_square)
  thus ?thesis by simp
qed

theorem sym_block_intersections_index [simp]: 
  assumes "b1 \<in># \<B>"
  assumes "b2 \<in># (\<B> - {#b1#})"
  shows "b1 |\<inter>| b2 = \<Lambda>"
proof - 
  have pos: "\<And> bl . ((b1 |\<inter>| bl) - \<Lambda>)^2 \<ge> 0" by simp
  have "(\<Sum>bl \<in># (remove1_mset b1 \<B>). ((b1 |\<inter>| bl) - \<Lambda>)^2) = 0" 
    using sym_sum_inter_num_to_zero assms by simp
  then have "\<And> bl.  bl \<in> set_mset (remove1_mset b1 \<B>) \<Longrightarrow> ((b1 |\<inter>| bl) - \<Lambda>)^2 = 0" 
    using sum_mset_0_iff_ge_0 pos by (metis (no_types, lifting)) 
  thus ?thesis
    using assms(2) by auto 
qed

subsubsection \<open>Symmetric BIBD is Simple\<close>

lemma sym_block_mult_one [simp]:
  assumes "bl \<in># \<B>"
  shows "multiplicity bl = 1"
proof (rule ccontr)
  assume "\<not> (multiplicity bl = 1)"
  then have not: "multiplicity bl \<noteq> 1" by simp
  have "multiplicity bl \<noteq> 0" using assms
    by simp 
  then have m: "multiplicity bl \<ge> 2" using not by linarith
  then have blleft: "bl \<in># (\<B> - {#bl#})"
    using in_diff_count by fastforce
  have "bl |\<inter>| bl = \<k>" using k_non_zero assms
    by (simp add: intersection_number_def) 
  then have keql: "\<k> = \<Lambda>" using sym_block_intersections_index blleft assms by simp
  then have "\<v> = \<k>"
    using keql index_lt_replication rep_value_sym block_size_lt_v diffs0_imp_equal k_non_zero zero_diff by linarith 
  then show False using incomplete
    by simp
qed

end 

sublocale symmetric_bibd \<subseteq> simple_design
  by unfold_locales simp

subsubsection \<open>Residual/Derived Sym BIBD Constructions\<close>
text \<open>Using the intersect result, we can reason further on residual and derived designs. 
Proofs based off lecture notes \cite{HerkeLectureNotes2016}\<close>

locale symmetric_bibd_block_transformations = symmetric_bibd + bibd_block_transformations
begin 

lemma derived_block_size [simp]: 
  assumes "b \<in># \<B>\<^sup>D"
  shows "card b = \<Lambda>"
proof -
  obtain bl2 where set: "bl2 \<in># remove1_mset bl \<B>" and inter: "b = bl2 \<inter> bl" 
    using derived_blocks_def assms by (meson derived_obtain_orig_block) 
  then have "card b = bl2 |\<inter>| bl"
    by (simp add: intersection_number_def) 
  thus ?thesis using sym_block_intersections_index
    using set intersect_num_commute valid_block by fastforce
qed

lemma derived_points_index [simp]: 
  assumes "ps \<subseteq> bl"
  assumes "card ps = 2"
  shows "\<B>\<^sup>D index  ps = \<Lambda> - 1"
proof -
  have b_in: "\<And> b . b \<in># (remove1_mset bl \<B>) \<Longrightarrow> ps \<subseteq> b \<Longrightarrow> ps \<subseteq> b \<inter> bl"
    using assms by blast 
  then have orig: "ps \<subseteq> \<V>"
    using valid_block assms wellformed by blast
  then have lam: "size {# b \<in># \<B> . ps \<subseteq> b #} = \<Lambda>" using balanced
    by (simp add: assms(2)  points_index_def) 
  then have "size {# b \<in># remove1_mset bl \<B> . ps \<subseteq> b #} = size {# b \<in># \<B> . ps \<subseteq> b #} - 1"
    using assms valid_block by (simp add: size_Diff_submset)
  then have "size {# b \<in># remove1_mset bl \<B> . ps \<subseteq> b #} = \<Lambda> - 1" 
    using lam index_not_zero by linarith 
  then have "size  {# bl \<inter> b |  b \<in># (remove1_mset bl \<B>) . ps \<subseteq> bl \<inter> b #} = \<Lambda> - 1" 
    using b_in by (metis (no_types, lifting) Int_subset_iff filter_mset_cong size_image_mset)
  then have "size {# x \<in># {# bl \<inter> b . b \<in># (remove1_mset bl \<B>) #} . ps \<subseteq> x #} = \<Lambda> - 1"
    by (metis image_mset_filter_swap) 
  then have "size {# x \<in># \<B>\<^sup>D . ps \<subseteq> x #} = \<Lambda> - 1" by (simp add: derived_blocks_def)
  thus ?thesis by (simp add: points_index_def)
qed

lemma sym_derive_design_bibd: 
  assumes "\<Lambda> > 1"
  shows "bibd bl \<B>\<^sup>D \<Lambda> (\<Lambda> - 1)"
proof -
  interpret des: proper_design bl "\<B>\<^sup>D" using derived_is_proper assms valid_block by auto 
  have "\<Lambda> < \<k>" using index_lt_replication rep_value_sym by linarith 
  then show ?thesis using derived_block_size assms derived_points_index derived_points_order
    by (unfold_locales) (simp_all)
qed

lemma residual_block_size [simp]: 
  assumes "b \<in># \<B>\<^sup>R"
  shows "card b = \<k> - \<Lambda>"
proof -
  obtain bl2 where sub: "b = bl2 - bl" and mem: "bl2 \<in># remove1_mset bl \<B>" 
    using assms residual_blocks_def by auto 
  then have "card b = card bl2 - card (bl2 \<inter> bl)"
    using card_Diff_subset_Int valid_block finite_blocks
    by (simp add: card_Diff_subset_Int)  
  then have "card b = card bl2 - bl2 |\<inter>| bl" 
    using intersection_number_def finite_blocks card_inter_lt_single
    by (metis assms derived_fin_incidence_system.finite_sets finite_Diff2 of_nat_diff 
        residual_fin_incidence_sys.finite_blocks sub)
  thus ?thesis using sym_block_intersections_index uniform
    by (metis valid_block in_diffD intersect_num_commute mem)
qed

lemma residual_index [simp]: 
  assumes "ps \<subseteq> bl\<^sup>c"
  assumes "card ps = 2"
  shows  "(\<B>\<^sup>R) index ps = \<Lambda>"
proof - 
  have a: "\<And> b . (b \<in># remove1_mset bl \<B> \<Longrightarrow> ps \<subseteq> b \<Longrightarrow>  ps \<subseteq> (b - bl))" using assms
    by (smt DiffI block_comp_elem_alt_left in_diffD subset_eq wellformed) 
  have b: "\<And> b . (b \<in># remove1_mset bl \<B> \<Longrightarrow>  ps \<subseteq> (b - bl) \<Longrightarrow>  ps \<subseteq> b)"
    by auto 
  have not_ss: "\<not> (ps \<subseteq> bl)" using set_diff_non_empty_not_subset blocks_nempty t_non_zero assms 
    block_complement_def by fastforce 
  have "\<B>\<^sup>R index ps = size {# x \<in># {# b - bl . b \<in># (remove1_mset bl \<B>) #} . ps \<subseteq> x #}" 
    using assms valid_block by (simp add: points_index_def residual_blocks_def)
  also have "... = size  {# b - bl |  b \<in># (remove1_mset bl \<B>) . ps \<subseteq> b - bl #} "
    by (metis image_mset_filter_swap)
  finally have "\<B>\<^sup>R index ps = size  {#  b \<in># (remove1_mset bl \<B>) . ps \<subseteq> b #} " using a b
    by (metis (no_types, lifting) filter_mset_cong size_image_mset)
  thus ?thesis 
    using balanced not_ss assms points_index_alt_def block_complement_subset_points by auto 
qed

lemma sym_residual_design_bibd: 
  assumes "\<k> \<ge> \<Lambda> + 2"
  shows "bibd (bl\<^sup>c) \<B>\<^sup>R (\<k> - \<Lambda>) \<Lambda>"
proof -
  interpret des: proper_design "bl\<^sup>c" "\<B>\<^sup>R" 
    using residual_is_proper assms(1) valid_block sym_block_mult_one by fastforce
  show ?thesis using residual_block_size assms sym_design_vk_gt_kl residual_order residual_index 
    by(unfold_locales) simp_all
qed

end

subsection \<open>BIBD's and Other Block Designs\<close>
text \<open>BIBD's are closely related to other block designs by indirect inheritance\<close>

sublocale bibd \<subseteq> k_\<Lambda>_PBD \<V> \<B> \<Lambda> \<k>
  using block_size_gt_t by (unfold_locales) simp_all

lemma incomplete_PBD_is_bibd: 
  assumes "k < card V" and "k_\<Lambda>_PBD V B \<Lambda> k" 
  shows "bibd V B k \<Lambda>"
proof -
  interpret inc: incomplete_design V B k using assms 
    by (auto simp add: block_design.incomplete_designI k_\<Lambda>_PBD.axioms(2))
  interpret pairwise_balance: pairwise_balance V B \<Lambda> using assms
    by (auto simp add: k_\<Lambda>_PBD.axioms(1))
  show ?thesis using assms k_\<Lambda>_PBD.block_size_t by (unfold_locales) (simp_all)
qed

lemma (in bibd) bibd_to_pbdI[intro]: 
  assumes "\<Lambda> = 1" 
  shows "k_PBD \<V> \<B> \<k>"
proof -
  interpret pbd: k_\<Lambda>_PBD \<V> \<B> \<Lambda> \<k>
    by (simp add: k_\<Lambda>_PBD_axioms)
  show ?thesis using assms by (unfold_locales) (simp_all add: t_lt_order min_block_size_2)
qed

locale incomplete_PBD = incomplete_design + k_\<Lambda>_PBD

sublocale incomplete_PBD \<subseteq> bibd
  using block_size_t by (unfold_locales) simp

end