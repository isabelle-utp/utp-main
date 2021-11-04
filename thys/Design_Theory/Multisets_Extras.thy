(* Title: Multisets_Extras
   Author: Chelsea Edmonds
*)

section \<open>Micellanious Helper Functions on Sets and Multisets\<close>

theory Multisets_Extras imports Main "HOL-Library.Multiset" "Card_Partitions.Set_Partition"
"Nested_Multisets_Ordinals.Multiset_More" "HOL-Library.Disjoint_Sets"
begin

subsection \<open>Set Theory Extras\<close>

text \<open>A number of extra helper lemmas for reasoning on sets (finite) required for Design Theory 
proofs\<close>

lemma card_Pow_filter_one: 
  assumes "finite A" 
  shows "card {x \<in> Pow A . card x = 1}  = card (A)"
  using assms 
proof (induct rule: finite_induct)
  case empty
  then show ?case by auto 
next
  case (insert x F)
  have "Pow (insert x F) = Pow F \<union> insert x ` Pow F"
    by (simp add: Pow_insert) 
  then have split: "{y \<in> Pow (insert x F) . card y = 1} = 
      {y \<in> (Pow F) . card y = 1} \<union> {y \<in> (insert x ` Pow F) . card y = 1}"
    by blast 
  have "\<And> y . y \<in> (insert x ` Pow F) \<Longrightarrow> finite y"
    using finite_subset insert.hyps(1) by fastforce 
  then have single: "\<And> y . y \<in> (insert x ` Pow F) \<Longrightarrow> card y = 1 \<Longrightarrow> y = {x}"
    by (metis card_1_singletonE empty_iff image_iff insertCI insertE) 
  then have "card {y \<in> (insert x ` Pow F) . card y = 1} = 1"
    using empty_iff imageI is_singletonI is_singletonI' is_singleton_altdef (* LONG *)
    by (metis (full_types, lifting) Collect_empty_eq_bot Pow_bottom bot_empty_eq  mem_Collect_eq)  
  then have " {y \<in> (insert x ` Pow F) . card y = 1} = {{x}}"
    using single card_1_singletonE card_eq_0_iff
    by (smt empty_Collect_eq mem_Collect_eq singletonD zero_neq_one) 
  then have split2:"{y \<in> Pow (insert x F) . card y = 1} = {y \<in> (Pow F) . card y = 1} \<union> {{x}}" 
    using split by simp
  then show ?case 
  proof (cases "x \<in> F")
    case True
    then show ?thesis using insert.hyps(2) by auto
  next
    case False
    then have "{y \<in> (Pow F) . card y = 1} \<inter> {{x}} = {}" by blast
    then have fact:"card {y \<in> Pow (insert x F) . card y = 1} = 
        card {y \<in> (Pow F) . card y = 1} + card {{x}}" 
      using split2 card_Un_disjoint insert.hyps(1) by auto 
    have "card (insert x F) = card F + 1" 
      using False card_insert_disjoint by (metis Suc_eq_plus1 insert.hyps(1)) 
    then show ?thesis using fact insert.hyps(3) by auto
  qed
qed

lemma elem_exists_non_empty_set:
  assumes "card A > 0"
  obtains x where "x \<in> A"
  using assms card_gt_0_iff by fastforce

lemma set_self_img_compr: "{a | a . a \<in> A} = A"
  by blast 

lemma card_subset_not_gt_card: "finite A \<Longrightarrow> card ps > card A \<Longrightarrow> \<not> (ps \<subseteq> A)"
  using card_mono leD by auto

lemma card_inter_lt_single: "finite A \<Longrightarrow> finite B \<Longrightarrow> card (A \<inter> B) \<le> card A"
  by (simp add: card_mono)

lemma set_diff_non_empty_not_subset: 
  assumes "A \<subseteq> (B - C)"
  assumes "C \<noteq> {}"
  assumes "A \<noteq> {}" 
  assumes "B \<noteq> {}"
  shows " \<not> (A \<subseteq> C)"
proof (rule ccontr)
  assume " \<not> \<not> (A \<subseteq> C)"
  then have a: "\<And> x . x \<in> A \<Longrightarrow> x \<in> C" by blast
  thus False using a assms by blast 
qed

lemma set_card_diff_ge_zero: "finite A \<Longrightarrow> finite B \<Longrightarrow> A \<noteq> B \<Longrightarrow> card A = card B \<Longrightarrow> 
    card (A - B) > 0"
  by (meson Diff_eq_empty_iff card_0_eq card_subset_eq finite_Diff neq0_conv)

lemma set_filter_diff: "{a \<in> A . P a } - {x} = {a \<in> (A - {x}) . (P a )}"
  by (auto)

lemma set_filter_diff_card: "card ({a \<in> A . P a } - {x}) = card {a \<in> (A - {x}) . (P a )}"
  by (simp add: set_filter_diff)

lemma obtain_subset_with_card_int_n:
  assumes "(n ::int) \<le> of_nat (card S)"
  assumes "(n ::int) \<ge> 0"
  obtains T where "T \<subseteq> S" "of_nat (card T) = (n ::int)" "finite T"
  using obtain_subset_with_card_n assms
  by (metis nonneg_int_cases of_nat_le_iff)

lemma transform_filter_img_empty_rm: 
  assumes "\<And> g . g \<in> G \<Longrightarrow> g \<noteq> {}"
  shows "{g - {x} | g. g \<in> G \<and> g \<noteq> {x}} = {g - {x} | g. g \<in> G } - {{}}"
proof -
  let ?f = "\<lambda> g . g - {x}"
  have "\<And> g . g \<in> G \<Longrightarrow> g \<noteq> {x} \<longleftrightarrow> ?f g \<noteq> {}" using assms
    by (metis Diff_cancel Diff_empty Diff_insert0 insert_Diff) 
  thus ?thesis by auto
qed

lemma bij_betw_inter_subsets: "bij_betw f A B \<Longrightarrow> a1 \<subseteq> A \<Longrightarrow> a2 \<subseteq> A 
    \<Longrightarrow> f ` (a1 \<inter> a2) = (f ` a1) \<inter> (f ` a2)"
  by (meson bij_betw_imp_inj_on inj_on_image_Int)

text\<open>Partition related set theory lemmas\<close>

lemma partition_on_remove_pt: 
  assumes "partition_on A G"
  shows "partition_on (A - {x}) {g - {x} | g. g \<in> G \<and> g \<noteq> {x}}"
proof (intro partition_onI) 
  show "\<And>p. p \<in> {g - {x} |g. g \<in> G \<and> g \<noteq> {x}} \<Longrightarrow> p \<noteq> {}"
    using assms partition_onD3 subset_singletonD by force
  let ?f =  "(\<lambda> g . g - {x})"
  have un_img: "\<Union>({?f g | g. g \<in> G }) = ?f (\<Union> G)" by blast
  have empty: "\<Union> {g - {x} |g. g \<in> G \<and> g \<noteq> {x}} = \<Union>({g - {x} | g. g \<in> G } - {{}})"
    by blast 
  then have "\<Union>({g - {x} | g. g \<in> G } - {{}}) = \<Union>({g - {x} | g. g \<in> G })" by blast
  then show " \<Union> {g - {x} |g. g \<in> G \<and> g \<noteq> {x}} = A - {x}" using partition_onD1 assms un_img
    by (metis empty) 
  then show "\<And>p p'.
       p \<in> {g - {x} |g. g \<in> G \<and> g \<noteq> {x}} \<Longrightarrow>
       p' \<in> {g - {x} |g. g \<in> G \<and> g \<noteq> {x}} \<Longrightarrow> p \<noteq> p' \<Longrightarrow> p \<inter> p' = {}"
  proof -
    fix p1 p2
    assume p1: "p1 \<in> {g - {x} |g. g \<in> G \<and> g \<noteq> {x}}" 
       and p2: "p2 \<in> {g - {x} |g. g \<in> G \<and> g \<noteq> {x}}"
       and ne: "p1 \<noteq> p2"
    obtain p1' p2' where orig1: "p1 = p1' - {x}" and orig2: "p2 = p2' - {x}" 
       and origne: "p1' \<noteq> p2'" and ne1: "p1' \<noteq> {x}" and ne2:"p2' \<noteq> {x}" and ing1: "p1' \<in> G" 
       and ing2: "p2' \<in> G"
      using p1 p2 using mem_Collect_eq ne by blast 
    then have "p1' \<inter> p2' = {}" using assms partition_onD2 ing1 ing2 origne disjointD by blast
    thus "p1 \<inter> p2 = {}" using orig1 orig2 by blast
  qed
qed

lemma partition_on_cart_prod:
  assumes "card I > 0"
  assumes "A \<noteq> {}"
  assumes "G \<noteq> {}"
  assumes "partition_on A G"
  shows "partition_on (A \<times> I) {g \<times> I |g. g \<in> G}"
proof (intro partition_onI)
  show "\<And>p. p \<in> {g \<times> I |g. g \<in> G} \<Longrightarrow> p \<noteq> {}"
    using assms(1) assms(4) partition_onD3 by fastforce
  show "\<Union> {g \<times> I |g. g \<in> G} = A \<times> I"
    by (metis Setcompr_eq_image Sigma_Union assms(4) partition_onD1)
  show "\<And>p p'. p \<in> {g \<times> I |g. g \<in> G} \<Longrightarrow> p' \<in> {g \<times> I |g. g \<in> G} \<Longrightarrow> p \<noteq> p' \<Longrightarrow> p \<inter> p' = {}"
    by (smt (verit, best) Sigma_Int_distrib1 Sigma_empty1 assms(4) mem_Collect_eq partition_onE)
qed

subsection \<open>Multiset Helpers\<close>

text \<open>Generic Size, count and card helpers\<close>

lemma count_size_set_repr: "size {# x \<in># A . x = g#} = count A g"
  by (simp add: filter_eq_replicate_mset) 

lemma mset_nempty_set_nempty: "A \<noteq> {#} \<longleftrightarrow> (set_mset A) \<noteq> {}"
  by simp

lemma mset_size_ne0_set_card: "size A > 0 \<Longrightarrow> card (set_mset A) > 0"
  using mset_nempty_set_nempty by fastforce 

lemma set_count_size_min: "count A a \<ge> n \<Longrightarrow> size A \<ge> n"
  by (metis (full_types) count_le_replicate_mset_subset_eq size_mset_mono size_replicate_mset)

lemma card_size_filter_eq: "finite A \<Longrightarrow>  card {a \<in> A . P a} = size {#a \<in># mset_set A . P a#}"
  by simp

lemma size_multiset_int_count:
  assumes "of_nat (card (set_mset A)) = (ca :: int)"
  assumes "\<And>p. p \<in># A \<Longrightarrow> of_nat (count A p) = (ca2 :: int)"
  shows "of_nat (size A) =  ((ca :: int) * ca2)"
proof -
  have "size A = (\<Sum> p \<in> (set_mset A) . count A p)" using size_multiset_overloaded_eq by auto
  then have "of_nat (size A) = (\<Sum> p \<in> (set_mset A) . ca2)" using assms by simp
  thus ?thesis using assms(1) by auto 
qed

lemma mset_union_size: "size (A \<union># B) = size (A) + size (B - A)"
  by (simp add: sup_subset_mset_def) 

lemma mset_union_size_inter: "size (A \<union># B) = size (A) + size B - size (A \<inter># B)"
  by (metis diff_add_inverse2 size_Un_Int) 

text \<open>Lemmas for repeat\_mset\<close>

lemma repeat_mset_size [simp]: "size (repeat_mset n A) = n * size A"
  by (induction n) auto

lemma repeat_mset_subset_in:
  assumes "\<And> a . a \<in># A \<Longrightarrow> a \<subseteq> B"
  assumes "X \<in># repeat_mset n A"
  assumes "x \<in> X"
  shows " x \<in> B"
  using assms by (induction n) auto

lemma repeat_mset_not_empty: "n > 0 \<Longrightarrow> A \<noteq> {#} \<Longrightarrow> repeat_mset n A \<noteq> {#}"
  by (induction n) auto

lemma elem_in_repeat_in_original: "a \<in># repeat_mset n A \<Longrightarrow> a \<in># A"
  by (metis count_inI count_repeat_mset in_countE mult.commute mult_zero_left nat.distinct(1))

lemma elem_in_original_in_repeat: "n > 0 \<Longrightarrow> a \<in># A \<Longrightarrow> a \<in># repeat_mset n A"
  by (metis (full_types) Suc_pred repeat_mset.simps(2) union_iff)

text \<open>Lemmas on image and filter for multisets\<close>

lemma multiset_add_filter_size: "size {# a \<in># (A1 + A2) . P a #} = size {# a \<in># A1 . P a #} + 
    size {# a \<in># A2 . P a #}" 
  by simp

lemma size_filter_neg: "size {#a \<in># A . P a #} = size A - size {# a \<in># A . \<not> P a #}"
  using size_filter_mset_lesseq size_union union_filter_mset_complement
  by (metis ordered_cancel_comm_monoid_diff_class.le_imp_diff_is_add) 

lemma filter_filter_mset_cond_simp: 
  assumes "\<And> a . P a \<Longrightarrow> Q a"
  shows "filter_mset P A = filter_mset P (filter_mset Q A)"
proof -
  have "filter_mset P (filter_mset Q A) = filter_mset (\<lambda> a. Q a \<and> P a) A" 
    by (simp add: filter_filter_mset)
  thus ?thesis using assms
    by (metis (mono_tags, lifting) filter_mset_cong)
qed

lemma filter_filter_mset_ss_member: "filter_mset (\<lambda> a . {x, y} \<subseteq> a) A = 
  filter_mset (\<lambda> a . {x, y} \<subseteq> a) (filter_mset (\<lambda> a . x \<in> a) A)"
proof - 
  have filter: "filter_mset (\<lambda> a . {x, y} \<subseteq> a) (filter_mset (\<lambda> a . x \<in> a) A) = 
    filter_mset (\<lambda> a . x \<in> a \<and> {x, y} \<subseteq> a) A" by (simp add: filter_filter_mset)
  have "\<And> a. {x, y} \<subseteq> a \<Longrightarrow> x \<in> a" by simp
  thus ?thesis using filter by auto
qed

lemma multiset_image_do_nothing: "(\<And> x .x \<in># A \<Longrightarrow> f x = x) \<Longrightarrow> image_mset f A = A"
  by (induct A) auto

lemma set_mset_filter: "set_mset {# f a . a \<in># A #} = {f a | a. a \<in># A}"
  by (simp add: Setcompr_eq_image)  

lemma mset_exists_imply: "x \<in># {# f a . a \<in># A #} \<Longrightarrow> \<exists> y \<in># A . x = f y"
  by auto

lemma filter_mset_image_mset:
  "filter_mset P (image_mset f A) = image_mset f (filter_mset (\<lambda>x. P (f x)) A)"
  by (induction A) auto

lemma mset_bunion_filter: "{# a \<in># A . P a \<or> Q a #} = {# a \<in># A . P a #} \<union># {# a \<in># A . Q a #}" 
  by (rule multiset_eqI) simp

lemma mset_inter_filter: "{# a \<in># A . P a \<and> Q a #} = {# a \<in># A . P a #} \<inter># {# a \<in># A . Q a #}" 
  by (rule multiset_eqI) simp

lemma image_image_mset: "image_mset (\<lambda> x . f x) (image_mset (\<lambda> y . g y) A) = 
    image_mset (\<lambda> x. f (g x)) A"
  by simp

text \<open>Big Union over multiset helpers\<close>

lemma mset_big_union_obtain: 
  assumes "x \<in># \<Sum>\<^sub># A"
  obtains a where "a \<in># A" and "x \<in># a"
  using assms by blast

lemma size_big_union_sum: "size (\<Sum>\<^sub># (M :: 'a multiset multiset)) = (\<Sum>x \<in>#M . size x)"
  by (induct M) auto

text \<open>Cartesian Product on Multisets\<close>

lemma size_cartesian_product_singleton [simp]: "size ({#a#} \<times># B) = size B" 
  by (simp add: Times_mset_single_left)  

lemma size_cartesian_product_singleton_right [simp]: "size (A \<times># {#b#}) = size A"
  by (simp add: Times_mset_single_right)

lemma size_cartesian_product_empty [simp]: "size (A \<times># {#}) = 0"
  by simp

lemma size_add_elem_step_eq: 
  assumes "size (A \<times># B) = size A * size B" 
  shows "size (add_mset x A \<times># B) = size (add_mset x A) * size B"
proof -
  have "(add_mset x A \<times># B) = A \<times># B + {#x#} \<times># B"
    by (metis Sigma_mset_plus_distrib1 add_mset_add_single) 
  then have "size (add_mset x A \<times># B) = size (A \<times># B) + size B" by auto
  also have "... = size A * size B + size B"
    by (simp add: assms)
  finally have "size (add_mset x A \<times># B) = (size A + 1) * size B"
    by auto
  thus ?thesis by simp
qed

lemma size_cartesian_product: "size (A \<times># B) = size A * size B"
  by (induct A) (simp_all add: size_add_elem_step_eq)

lemma cart_prod_distinct_mset:
  assumes assm1: "distinct_mset A"
  assumes assm2: "distinct_mset B"
  shows "distinct_mset (A \<times># B)"
  unfolding distinct_mset_count_less_1
proof (rule allI)
  fix x
  have count_mult: "count (A \<times># B) x = count A (fst x) * count B (snd x)" 
    using count_Sigma_mset by (metis prod.exhaust_sel) 
  then have "count A (fst x) * count B (snd x) \<le> 1" using assm1 assm2 
    unfolding distinct_mset_count_less_1 using mult_le_one by blast 
  thus "count (A \<times># B) x \<le> 1" using count_mult by simp
qed

lemma cart_product_single_intersect: "x1 \<noteq> x2 \<Longrightarrow> ({#x1#} \<times># A) \<inter># ({#x2#} \<times># B) = {#}"
  using multiset_inter_single by fastforce

lemma size_union_distinct_cart_prod: "x1 \<noteq> x2 \<Longrightarrow> size (({#x1#} \<times># A) \<union># ({#x2#} \<times># B)) = 
    size ({#x1#} \<times># A) + size ({#x2#} \<times># B)"
  by (simp add: cart_product_single_intersect size_Un_disjoint) 

lemma size_Union_distinct_cart_prod: "distinct_mset M \<Longrightarrow> 
    size (\<Sum>p\<in>#M. ({#p#} \<times># B)) = size (M) * size (B)"
  by (induction M) auto

lemma size_Union_distinct_cart_prod_filter: "distinct_mset M \<Longrightarrow> 
    (\<And> p . p \<in># M \<Longrightarrow> size ({# b \<in># B . P p b #}) = c) \<Longrightarrow> 
    size (\<Sum>p\<in>#M. ({#p#} \<times># {# b \<in># B . P p b #})) = size (M) * c"
  by (induction M) auto

lemma size_Union_distinct_cart_prod_filter2: "distinct_mset V \<Longrightarrow> 
    (\<And> b . b \<in># B \<Longrightarrow> size ({# v \<in># V . P v b #}) = c) \<Longrightarrow> 
    size (\<Sum>b\<in>#B. ( {# v \<in># V . P v b #} \<times># {#b#})) = size (B) * c"
  by (induction B) auto

lemma cart_product_add_1: "(add_mset a A) \<times># B = ({#a#} \<times># B) + (A \<times># B)"
  by (metis Sigma_mset_plus_distrib1 add_mset_add_single union_commute)

lemma cart_product_add_1_filter: "{#m \<in># ((add_mset a M) \<times># N) . P m #} = 
    {#m \<in># (M \<times># N) . P m #} + {#m \<in># ({#a#} \<times>#  N) . P m #}"
  unfolding add_mset_add_single [of a M] Sigma_mset_plus_distrib1
  by (simp add: Times_mset_single_left)

lemma cart_product_add_1_filter2: "{#m \<in># (M \<times># (add_mset b N)) . P m #} = 
    {#m \<in># (M \<times># N) . P m #} + {#m \<in># (M \<times>#  {#b#}) . P m #}"
  unfolding add_mset_add_single [of b N] Sigma_mset_plus_distrib1
  by (metis Times_insert_left Times_mset_single_right add_mset_add_single filter_union_mset)

lemma cart_prod_singleton_right_gen: 
  assumes "\<And> x . x \<in># (A \<times># {#b#}) \<Longrightarrow> P x \<longleftrightarrow> Q (fst x)"
  shows "{#x \<in># (A \<times># {#b#}). P x#} = {# a \<in># A . Q a#} \<times># {#b#}"
  using assms
proof (induction A)
  case empty
  then show ?case by simp
next
  case (add x A)
  have "add_mset x A \<times># {#b#} = add_mset (x, b) (A \<times># {#b#})"
    by (simp add: Times_mset_single_right) 
  then have lhs: "filter_mset P (add_mset x A \<times># {#b#}) = filter_mset P (A \<times># {#b#}) + 
    filter_mset P {#(x, b)#}" by simp
  have rhs: "filter_mset Q (add_mset x A) \<times># {#b#} = filter_mset Q A \<times># {#b#} + 
    filter_mset Q {#x#} \<times># {#b#}"
    by (metis Sigma_mset_plus_distrib1 add_mset_add_single filter_union_mset)
  have "filter_mset P {#(x, b)#} = filter_mset Q {#x#} \<times># {#b#}"
    using add.prems by fastforce
  then show ?case using lhs rhs add.IH add.prems by force 
qed

lemma cart_prod_singleton_left_gen: 
  assumes "\<And> x . x \<in># ({#a#} \<times># B) \<Longrightarrow> P x \<longleftrightarrow> Q (snd x)"
  shows "{#x \<in># ({#a#} \<times># B). P x#} = {#a#} \<times># {#b \<in># B . Q b#}"
  using assms
proof (induction B)
  case empty
  then show ?case by simp
next
  case (add x B)
  have lhs: "filter_mset P ({#a#} \<times># add_mset x B) = filter_mset P ({#a#} \<times># B) + 
    filter_mset P {#(a, x)#}"
    by (simp add: cart_product_add_1_filter2) 
  have rhs: "{#a#} \<times># filter_mset Q (add_mset x B) = {#a#} \<times># filter_mset Q B + 
    {#a#} \<times># filter_mset Q {#x#}"
    using add_mset_add_single filter_union_mset by (metis Times_mset_single_left image_mset_union) 
  have "filter_mset P {#(a, x)#} = {#a#} \<times># filter_mset Q {#x#}"
    using add.prems by fastforce
  then show ?case using lhs rhs add.IH add.prems by force 
qed

lemma cart_product_singleton_left: "{#m \<in># ({#a#} \<times>#  N) . fst m \<in> snd m #} = 
  ({#a#} \<times># {# n \<in># N . a \<in> n #})" (is "?A = ?B")
proof -
  have stmt: "\<And>m. m \<in># ({#a#} \<times># N) \<Longrightarrow> fst m \<in> snd m \<longleftrightarrow> a \<in> snd m"
    by (simp add: mem_Times_mset_iff)
  thus ?thesis by (metis (no_types, lifting) Sigma_mset_cong stmt cart_prod_singleton_left_gen)
qed

lemma cart_product_singleton_right: "{#m \<in># (N \<times># {#b#}) . fst m \<in> snd m #} = 
  ({# n \<in># N . n \<in> b #} \<times># {# b #})" (is "?A = ?B")
proof - 
  have stmt: "\<And>m. m \<in># (N \<times># {#b#}) \<Longrightarrow> fst m \<in> snd m \<longleftrightarrow> fst m \<in>b"
    by (simp add: mem_Times_mset_iff)
  thus ?thesis by (metis (no_types, lifting) Sigma_mset_cong stmt cart_prod_singleton_right_gen)
qed

lemma cart_product_add_1_filter_eq: "{#m \<in># ((add_mset a M) \<times># N) . (fst m \<in> snd m) #} = 
    {#m \<in># (M \<times># N) . (fst m \<in> snd m) #} + ({#a#} \<times># {# n \<in># N . a \<in> n #})"
  unfolding add_mset_add_single [of a M] Sigma_mset_plus_distrib1
  using cart_product_singleton_left cart_product_add_1_filter by fastforce 

lemma cart_product_add_1_filter_eq_mirror: "{#m \<in># M \<times># (add_mset b N) . (fst m \<in> snd m) #} = 
    {#m \<in># (M \<times># N) . (fst m \<in> snd m) #} + ({# n \<in># M . n \<in> b #} \<times># {#b#})"
  unfolding add_mset_add_single [of b N] Sigma_mset_plus_distrib1 (* longish *)
  by (metis (no_types) add_mset_add_single cart_product_add_1_filter2 cart_product_singleton_right) 

lemma set_break_down_left:
  shows "{# m \<in># (M \<times># N) . (fst m) \<in> (snd m)  #} = (\<Sum>m\<in>#M. ({#m#} \<times># {#n \<in># N. m \<in> n#}))"
  by (induction M) (auto simp add: cart_product_add_1_filter_eq)

lemma set_break_down_right:
  shows "{# x \<in># M \<times># N . (fst x) \<in> (snd x)  #} = (\<Sum>n\<in>#N. ({#m \<in># M. m \<in> n#} \<times># {#n#}))"
  by (induction N) (auto simp add: cart_product_add_1_filter_eq_mirror)

text \<open>Reasoning on sums of elements over multisets\<close>

lemma sum_over_fun_eq: 
  assumes "\<And> x . x \<in># A \<Longrightarrow> f x = g x" 
  shows "(\<Sum>x \<in># A . f(x)) = (\<Sum> x \<in># A . g (x))"
  using assms by auto

context ring_1
begin

lemma sum_mset_add_diff: "(\<Sum> x \<in># A. f x - g x) = (\<Sum> x \<in># A . f x) -  (\<Sum> x \<in># A . g x)"
  by (induction A) (auto simp add: algebra_simps)

end

context ordered_ring
begin

lemma sum_mset_ge0:"(\<And> x . f x \<ge> 0) \<Longrightarrow> (\<Sum> x \<in># A. f x ) \<ge> 0"
proof (induction A)
  case empty
  then show ?case by simp
next
  case (add x A)
  then have hyp2: "0 \<le> sum_mset (image_mset f A)" by blast
  then have " sum_mset (image_mset f (add_mset x A)) =  sum_mset (image_mset f  A) + f x"
    by (simp add: add_commute) 
  then show ?case
    by (simp add: add.IH add.prems)
qed

lemma sum_order_add_mset: "(\<And> x . f x \<ge> 0) \<Longrightarrow> (\<Sum> x \<in># A. f x ) \<le> (\<Sum> x \<in># add_mset a A. f x )"
  by simp

lemma sum_mset_0_left: "(\<And> x . f x \<ge> 0) \<Longrightarrow> (\<Sum> x \<in># A. f x ) = 0 \<Longrightarrow> (\<forall> x \<in># A .f x = 0)"
  apply (induction A)
   apply auto
    using local.add_nonneg_eq_0_iff sum_mset_ge0 apply blast
  by (metis local.antisym local.sum_mset.insert sum_mset_ge0 sum_order_add_mset)

lemma sum_mset_0_iff_ge_0:
  assumes "(\<And> x . f x \<ge> 0)"
  shows "(\<Sum> x \<in># A. f x ) = 0 \<longleftrightarrow> (\<forall> x \<in> set_mset A .f x = 0)"
  using sum_mset_0_left assms by auto 

end

lemma mset_set_size_card_count: "(\<Sum>x \<in># A. x) = (\<Sum>x \<in> set_mset A . x * (count A x))"
proof (induction A)
  case empty
  then show ?case by simp
next
  case (add y A)
  have lhs: "(\<Sum>x\<in>#add_mset y A. x) = (\<Sum>x\<in># A. x) + y" by simp
  have rhs: "(\<Sum>x\<in>set_mset (add_mset y A). x * count (add_mset y A) x) = 
      (\<Sum>x\<in>(insert y (set_mset A)) . x * count (add_mset y A) x)"
    by simp 
  then show ?case 
  proof (cases "y \<in># A")
    case True
    have x_val: "\<And> x . x \<in> (insert y (set_mset A)) \<Longrightarrow> x \<noteq> y \<Longrightarrow> 
        x* count (add_mset y A) x = x * (count A x)" 
      by auto 
    have y_count: "count (add_mset y A) y = 1 + count A y" 
      using True count_inI by fastforce
    then have "(\<Sum>x\<in>set_mset (add_mset y A). x * count (add_mset y A) x) = 
        (y * (count (add_mset y A) y)) + (\<Sum>x\<in>(set_mset A) - {y}. x * count A x)" 
      using x_val finite_set_mset sum.cong sum.insert rhs
      by (smt DiffD1 Diff_insert_absorb insert_absorb mk_disjoint_insert sum.insert_remove) 
    then have s1: "(\<Sum>x\<in>set_mset (add_mset y A). x * count (add_mset y A) x) = 
        y + y * (count A y) + (\<Sum>x\<in>(set_mset A) - {y}. x * count A x)" 
      using y_count by simp
    then have "(\<Sum>x\<in>set_mset (add_mset y A). x * count (add_mset y A) x) = 
        y + (\<Sum>x\<in>insert y ((set_mset A) - {y} ) . x * count A x)" 
      by (simp add: sum.insert_remove) 
    then have "(\<Sum>x\<in>set_mset (add_mset y A). x * count (add_mset y A) x) = 
        y + (\<Sum>x\<in>(set_mset A) . x * count A x)"
      by (simp add:  True insert_absorb)
    then show ?thesis using lhs add.IH
      by linarith 
  next
    case False
    have x_val: "\<And> x . x \<in> set_mset A \<Longrightarrow> x* count (add_mset y A) x = x * (count A x)" 
      using False by auto 
    have y_count: "count (add_mset y A) y = 1" using False count_inI by fastforce
    have lhs: "(\<Sum>x\<in>#add_mset y A. x) = (\<Sum>x\<in># A. x) + y" by simp
    have "(\<Sum>x\<in>set_mset (add_mset y A). x * count (add_mset y A) x) = 
        (y * count (add_mset y A) y) + (\<Sum>x\<in>set_mset A. x * count A x)" 
      using x_val rhs by (metis (no_types, lifting) False finite_set_mset sum.cong sum.insert) 
    then have "(\<Sum>x\<in>set_mset (add_mset y A). x * count (add_mset y A) x) = 
        y + (\<Sum>x\<in>set_mset A. x * count A x)" 
      using y_count by simp 
    then show ?thesis using lhs add.IH by linarith 
  qed
qed

subsection \<open>Partitions on Multisets\<close>

text \<open>A partition on a multiset A is a multiset of multisets, where the sum over P equals A and the 
empty multiset is not in the partition. Based off set partition definition. 
We note that unlike set partitions, there is no requirement for elements in the multisets to be 
distinct due to the definition of union on multisets \cite{benderPartitionsMultisets1974}\<close>

lemma mset_size_partition_dep: "size {# a \<in># A . P a \<or> Q a #} = 
    size {# a \<in># A . P a #} +  size {# a \<in># A . Q a #} -  size {# a \<in># A . P a \<and> Q a #}"
  by (simp add: mset_bunion_filter mset_inter_filter mset_union_size_inter) 

definition partition_on_mset :: "'a multiset \<Rightarrow> 'a multiset multiset \<Rightarrow> bool" where
"partition_on_mset A P \<longleftrightarrow> \<Sum>\<^sub>#P = A \<and> {#} \<notin># P"

lemma partition_on_msetI [intro]: "\<Sum>\<^sub>#P = A \<Longrightarrow> {#} \<notin># P \<Longrightarrow> partition_on_mset A P"
  by (simp add: partition_on_mset_def)

lemma partition_on_msetD1: "partition_on_mset A P \<Longrightarrow> \<Sum>\<^sub>#P = A"
  by (simp add: partition_on_mset_def)

lemma partition_on_msetD2: "partition_on_mset A P \<Longrightarrow> {#} \<notin>#  P"
  by (simp add: partition_on_mset_def)

lemma partition_on_mset_empty: "partition_on_mset {#} P \<longleftrightarrow> P = {#}"
  unfolding partition_on_mset_def
  using multiset_nonemptyE by fastforce

lemma partition_on_mset_all: "A \<noteq> {#} \<Longrightarrow> partition_on_mset A {#A #}"
  by (simp add: partition_on_mset_def)

lemma partition_on_mset_singletons: "partition_on_mset A (image_mset (\<lambda> x . {#x#}) A)"
  by (auto simp: partition_on_mset_def)

lemma partition_on_mset_not_empty: "A \<noteq> {#} \<Longrightarrow> partition_on_mset A P \<Longrightarrow> P \<noteq> {#}"
  by (auto simp: partition_on_mset_def)

lemma partition_on_msetI2: "\<Sum>\<^sub>#P = A \<Longrightarrow> (\<And> p . p \<in># P \<Longrightarrow> p \<noteq> {#}) \<Longrightarrow> partition_on_mset A P"
  by (auto simp: partition_on_mset_def)

lemma partition_on_mset_elems: "partition_on_mset A P \<Longrightarrow> p1 \<in># P \<Longrightarrow> x \<in># p1 \<Longrightarrow> x \<in># A"
  by (auto simp: partition_on_mset_def)

lemma partition_on_mset_sum_size_eq: "partition_on_mset A P \<Longrightarrow> (\<Sum>x \<in># P. size x) = size A"
  by (metis partition_on_msetD1 size_big_union_sum)

lemma partition_on_mset_card: assumes "partition_on_mset A P" shows " size P \<le> size A"
proof (rule ccontr)
  assume "\<not> size P \<le> size A"
  then have a: "size P > size A" by simp
  have "\<And> x . x \<in># P \<Longrightarrow> size x > 0" using partition_on_msetD2
    using assms nonempty_has_size by auto 
  then have " (\<Sum>x \<in># P. size x) \<ge> size P"
    by (metis leI less_one not_less_zero size_eq_sum_mset sum_mset_mono) 
  thus False using a partition_on_mset_sum_size_eq
    using assms by fastforce 
qed

lemma partition_on_mset_count_eq: "partition_on_mset A P \<Longrightarrow> a \<in># A \<Longrightarrow> 
    (\<Sum>x \<in># P. count x a) = count A a"
  by (metis count_sum_mset partition_on_msetD1)

lemma partition_on_mset_subsets: "partition_on_mset A P \<Longrightarrow> x \<in># P \<Longrightarrow> x \<subseteq># A"
  by (auto simp add: partition_on_mset_def)

lemma partition_on_mset_distinct: 
  assumes "partition_on_mset A P"
  assumes "distinct_mset A"
  shows "distinct_mset P"
proof (rule ccontr)
  assume "\<not> distinct_mset P"
  then obtain p1 where count: "count P p1 \<ge> 2"
    by (metis Suc_1 distinct_mset_count_less_1 less_Suc_eq_le not_less_eq) 
  then have cge: "\<And> x . x \<in># p1 \<Longrightarrow> (\<Sum>p \<in># P. count p x ) \<ge> 2"
    by (smt count_greater_eq_one_iff count_sum_mset_if_1_0 dual_order.trans sum_mset_mono zero_le)
  have elem_in: "\<And> x . x \<in># p1 \<Longrightarrow> x \<in># A" using partition_on_mset_elems
    by (metis count assms(1) count_eq_zero_iff not_numeral_le_zero) 
  have "\<And> x . x \<in># A \<Longrightarrow> count A x = 1" using assms
    by (simp add: distinct_mset_def) 
  thus False 
    using assms partition_on_mset_count_eq cge elem_in count_inI local.count multiset_nonemptyE
    by (metis (mono_tags) not_numeral_le_zero numeral_One numeral_le_iff partition_on_mset_def semiring_norm(69)) 
qed

lemma partition_on_mset_distinct_disjoint: 
  assumes "partition_on_mset A P"
  assumes "distinct_mset A"
  assumes "p1 \<in># P"
  assumes "p2 \<in># P - {#p1#}"
  shows "p1 \<inter># p2 = {#}"
  using Diff_eq_empty_iff_mset assms diff_add_zero distinct_mset_add multiset_inter_assoc sum_mset.remove
  by (smt partition_on_msetD1 subset_mset.inf.absorb_iff2 subset_mset.le_add_same_cancel1 subset_mset.le_iff_inf)

lemma partition_on_mset_diff: 
  assumes "partition_on_mset A P"
  assumes "Q \<subseteq>#P"
  shows "partition_on_mset (A - \<Sum>\<^sub>#Q) (P - Q)"
  using assms partition_on_mset_def
  by (smt diff_union_cancelL subset_mset.add_diff_inverse sum_mset.union union_iff)

lemma sigma_over_set_partition_count: 
  assumes "finite A"
  assumes "partition_on A P"
  assumes "x \<in># \<Sum>\<^sub># (mset_set (mset_set ` P))"
  shows "count (\<Sum>\<^sub># (mset_set (mset_set ` P))) x = 1" 
proof - 
  have disj: "disjoint P" using assms partition_onD2 by auto 
  then obtain p where  pin: "p \<in># mset_set (mset_set ` P)" and xin: "x \<in># p"
    using assms by blast 
  then have "count (mset_set (mset_set ` P)) p = 1"
    by (meson count_eq_zero_iff count_mset_set') 
  then have filter: "\<And> p' . p' \<in># ((mset_set (mset_set` P)) - {#p#}) \<Longrightarrow> p \<noteq> p'"
    using count_eq_zero_iff count_single by fastforce  
  have zero: "\<And> p'. p' \<in># mset_set (mset_set ` P) \<Longrightarrow> p' \<noteq> p \<Longrightarrow> count p' x = 0"
  proof (rule ccontr)
    fix p' 
    assume assm: "p' \<in># mset_set (mset_set ` P)" and ne: "p' \<noteq> p"  and n0: "count p' x \<noteq> 0"
    then have xin2: "x \<in># p'"  by auto 
    obtain p1 p2 where p1in: "p1 \<in> P" and p2in: "p2 \<in> P" and  p1eq: "mset_set p1 = p" 
        and p2eq: "mset_set p2 = p'" using assm assms(1) assms(2) pin 
      by (metis (no_types, lifting) elem_mset_set finite_elements finite_imageI image_iff)
    have origne: "p1 \<noteq> p2" using ne p1eq p2eq by auto 
    have "p1 = p2" using partition_onD4 xin xin2
      by (metis assms(2) count_eq_zero_iff count_mset_set' p1eq p1in p2eq p2in) 
    then show False using origne by simp
  qed
  have one: "count p x = 1" using pin xin assms count_eq_zero_iff count_greater_eq_one_iff
    by (metis count_mset_set(3) count_mset_set_le_one image_iff le_antisym) 
  then have "count (\<Sum>\<^sub># (mset_set (mset_set ` P))) x = 
      (\<Sum>p' \<in># (mset_set (mset_set ` P)) . count p' x)" 
    using count_sum_mset by auto
  also have "... = (count p x) + (\<Sum>p' \<in># ((mset_set (mset_set ` P)) - {#p#}) . count p' x)"
    by (metis (mono_tags, lifting) insert_DiffM pin sum_mset.insert)  
  also have "... = 1 + (\<Sum>p' \<in># ((mset_set (mset_set ` P)) - {#p#}) . count p' x)"
    using one by presburger 
  finally have "count (\<Sum>\<^sub># (mset_set (mset_set ` P))) x = 
      1 + (\<Sum>p' \<in># ((mset_set (mset_set ` P)) - {#p#}) . 0)" 
    using zero filter by (metis (mono_tags, lifting) in_diffD sum_over_fun_eq) 
  then show "count (\<Sum>\<^sub># (mset_set (mset_set ` P))) x = 1" by simp
qed

lemma partition_on_mset_set: 
  assumes "finite A"
  assumes "partition_on A P"
  shows "partition_on_mset (mset_set A) (mset_set (image (\<lambda> x. mset_set x) P))"
proof (intro partition_on_msetI)
  have partd1: "\<Union>P = A" using assms partition_onD1 by auto 
  have imp: "\<And>x. x \<in># \<Sum>\<^sub># (mset_set (mset_set ` P)) \<Longrightarrow> x \<in># mset_set A"
  proof -
    fix x
    assume "x \<in># \<Sum>\<^sub># (mset_set (mset_set ` P))"
    then obtain p where "p \<in> (mset_set ` P)" and xin: "x \<in># p"
      by (metis elem_mset_set equals0D infinite_set_mset_mset_set mset_big_union_obtain) 
    then have "set_mset p \<in> P"
      by (metis empty_iff finite_set_mset_mset_set image_iff infinite_set_mset_mset_set) 
    then show "x \<in># mset_set A"
      using partd1 xin assms(1) by auto  
  qed
  have imp2: "\<And>x . x \<in># mset_set A \<Longrightarrow> x \<in># \<Sum>\<^sub># (mset_set (mset_set ` P))" 
  proof -
    fix x
    assume "x \<in># mset_set A"
    then have "x \<in> A" by (simp add: assms(1)) 
    then obtain p where "p \<in> P" and "x \<in> p" using assms(2) using partd1 by blast
    then obtain p' where "p' \<in> (mset_set ` P)" and "p' = mset_set p" by blast 
    thus "x \<in># \<Sum>\<^sub># (mset_set (mset_set ` P))" using assms \<open>p \<in> P\<close> \<open>x \<in> p\<close> finite_elements partd1
      by (metis Sup_upper finite_imageI finite_set_mset_mset_set in_Union_mset_iff rev_finite_subset) 
  qed
  have a1: "\<And> x . x \<in># mset_set A \<Longrightarrow> count (mset_set A) x = 1"
    using assms(1) by fastforce 
  then show "\<Sum>\<^sub># (mset_set (mset_set ` P)) = mset_set A"  using imp imp2 a1 
    by (metis assms(1) assms(2) count_eq_zero_iff multiset_eqI sigma_over_set_partition_count)
  have "\<And> p. p \<in> P \<Longrightarrow>  p \<noteq> {} " using assms partition_onD3 by auto 
  then have "\<And> p. p \<in> P \<Longrightarrow>  mset_set p \<noteq> {#}" using mset_set_empty_iff
    by (metis Union_upper assms(1) partd1 rev_finite_subset) 
  then show "{#} \<notin># mset_set (mset_set ` P)"
    by (metis elem_mset_set equals0D image_iff infinite_set_mset_mset_set) 
qed

lemma partition_on_mset_distinct_inter: 
  assumes "partition_on_mset A P"
  assumes "distinct_mset A"
  assumes "p1 \<in># P" and "p2 \<in># P" and "p1 \<noteq> p2"
  shows "p1 \<inter># p2 = {#}"
  by (metis assms in_remove1_mset_neq partition_on_mset_distinct_disjoint)

lemma partition_on_set_mset_distinct: 
  assumes "partition_on_mset A P"
  assumes "distinct_mset A"
  assumes "p \<in># image_mset set_mset P" 
  assumes "p' \<in># image_mset set_mset P"
  assumes "p \<noteq> p'"
  shows "p \<inter> p' = {}"
proof -
  obtain p1 where p1in: "p1 \<in># P" and p1eq: "set_mset p1 = p" using assms(3)
    by blast 
  obtain p2 where p2in: "p2 \<in># P" and p2eq: "set_mset p2 = p'" using assms(4) by blast
  have "distinct_mset P" using assms partition_on_mset_distinct by blast 
  then have "p1 \<noteq> p2" using assms using p1eq p2eq by fastforce 
  then have "p1 \<inter># p2 = {#}" using partition_on_mset_distinct_inter
    using assms(1) assms(2) p1in p2in by auto 
  thus ?thesis using p1eq p2eq
    by (metis set_mset_empty set_mset_inter) 
qed

lemma partition_on_set_mset:
  assumes "partition_on_mset A P"
  assumes "distinct_mset A"
  shows "partition_on (set_mset A) (set_mset (image_mset set_mset P))"
proof (intro partition_onI)
  show "\<And>p. p \<in># image_mset set_mset P \<Longrightarrow> p \<noteq> {}"
    using assms(1) partition_on_msetD2 by fastforce 
next
  have "\<And> x . x \<in> set_mset A \<Longrightarrow> x \<in> \<Union> (set_mset (image_mset set_mset P))"
    by (metis Union_iff assms(1) image_eqI mset_big_union_obtain partition_on_msetD1 set_image_mset) 
  then show "\<Union> (set_mset (image_mset set_mset P)) = set_mset A" 
    using set_eqI' partition_on_mset_elems assms by auto
  show "\<And>p p'. p \<in># image_mset set_mset P \<Longrightarrow> p' \<in># image_mset set_mset P \<Longrightarrow> 
      p \<noteq> p' \<Longrightarrow> p \<inter> p' = {}"
    using partition_on_set_mset_distinct assms by fastforce
qed

lemma partition_on_mset_eq_imp_eq_carrier:
  assumes "partition_on_mset A P"
  assumes "partition_on_mset B P"
  shows "A = B"
  using assms partition_on_msetD1 by auto 

lemma partition_on_mset_add_single:
  assumes "partition_on_mset A P"
  shows "partition_on_mset (add_mset a A) (add_mset {#a#} P)"
  using assms by (auto simp: partition_on_mset_def)

lemma partition_on_mset_add_part:
  assumes "partition_on_mset A P"
  assumes "X \<noteq> {#}"
  assumes "A + X = A'"
  shows "partition_on_mset A' (add_mset X P)"
  using assms by (auto simp: partition_on_mset_def)

lemma partition_on_mset_add:
  assumes "partition_on_mset A P"
  assumes "X \<in># P"
  assumes "add_mset a X = X'"
  shows "partition_on_mset (add_mset a A) (add_mset X' (P - {#X#}))"
  using add_mset_add_single assms empty_not_add_mset mset_subset_eq_single partition_on_mset_all
  by (smt partition_on_mset_def subset_mset.add_diff_inverse sum_mset.add_mset sum_mset.remove union_iff union_mset_add_mset_left)

lemma partition_on_mset_elem_exists_part:
  assumes "partition_on_mset A P"
  assumes "x \<in># A" 
  obtains p where "p \<in># P" and "x \<in># p"
  using assms in_Union_mset_iff partition_on_msetD2 partition_on_msetI
  by (metis partition_on_mset_eq_imp_eq_carrier)

lemma partition_on_mset_combine: 
  assumes "partition_on_mset A P"
  assumes "partition_on_mset B Q"
  shows "partition_on_mset (A + B) (P + Q)"
  unfolding partition_on_mset_def
  using assms partition_on_msetD1 partition_on_msetD2 by auto

lemma partition_on_mset_split: 
  assumes "partition_on_mset A (P + Q)"
  shows "partition_on_mset (\<Sum>\<^sub>#P) P"
  using  partition_on_mset_def partition_on_msetD2 assms by fastforce 
end