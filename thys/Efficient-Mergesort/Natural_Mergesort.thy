(* Author: Christian Sternagel *)

theory Natural_Mergesort
  imports "HOL-Data_Structures.Sorting"
begin

subsection \<open>Auxiliary Results\<close>

lemma C_merge_adj':
  "C_merge_adj xss \<le> length (concat xss)"
proof (induct xss rule: C_merge_adj.induct)
  case (3 xs ys zss)
  then show ?case using C_merge_ub [of xs ys] by simp
qed simp_all

lemma length_concat_merge_adj:
  "length (concat (merge_adj xss)) = length (concat xss)"
  by (induct xss rule: merge_adj.induct) (simp_all add: length_merge)

lemma C_merge_all':
  "C_merge_all xss \<le> length (concat xss) * \<lceil>log 2 (length xss)\<rceil>"
proof (induction xss rule: C_merge_all.induct)
  case (3 xs ys zss)
  let ?xss = "xs # ys # zss"
  let ?m = "length (concat ?xss)"

  have *: "\<lceil>log 2 (real n + 2)\<rceil> = \<lceil>log 2 (Suc n div 2 + 1)\<rceil> + 1" for n :: nat
    using ceiling_log2_div2 [of "n + 2"] by (simp add: algebra_simps)

  have "C_merge_all ?xss = C_merge_adj ?xss + C_merge_all (merge_adj ?xss)" by simp
  also have "\<dots> \<le> ?m + C_merge_all (merge_adj ?xss)"
    using C_merge_adj' [of ?xss] by auto
  also have "\<dots> \<le> ?m + length (concat (merge_adj ?xss)) * \<lceil>log 2 (length (merge_adj ?xss))\<rceil>"
    using "3.IH" by simp
  also have "\<dots> = ?m + ?m * \<lceil>log 2 (length (merge_adj ?xss))\<rceil>"
    by (simp only: length_concat_merge_adj)
  also have "\<dots> \<le> ?m * \<lceil>log 2 (length ?xss)\<rceil>"
    by (auto simp: * algebra_simps)
  finally show ?case by simp
qed simp_all


subsection \<open>Definition of Natural Mergesort\<close>

text \<open>
  Partition input into ascending and descending subsequences.
  (The latter are reverted on the fly.)
\<close>
fun runs :: "('a::linorder) list \<Rightarrow> 'a list list" and
    asc :: "'a \<Rightarrow> ('a list \<Rightarrow> 'a list) \<Rightarrow> 'a list \<Rightarrow> 'a list list" and
    desc :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list"
  where
    "runs (a # b # xs) = (if a > b then desc b [a] xs else asc b ((#) a) xs)"
  | "runs [x] = [[x]]"
  | "runs [] = []"
  | "asc a as (b # bs) = (if \<not> a > b then asc b (as \<circ> (#) a) bs else as [a] # runs (b # bs))"
  | "asc a as [] = [as [a]]"
  | "desc a as (b # bs) = (if a > b then desc b (a # as) bs else (a # as) # runs (b # bs))"
  | "desc a as [] = [a # as]"

definition nmsort :: "('a::linorder) list \<Rightarrow> 'a list"
  where
    "nmsort xs = merge_all (runs xs)"


subsection \<open>Functional Correctness\<close>

definition "ascP f = (\<forall>xs ys. f (xs @ ys) = f xs @ ys)"

lemma ascP_Cons [simp]: "ascP ((#) x)" by (simp add: ascP_def)

lemma ascP_comp_Cons [simp]: "ascP f \<Longrightarrow> ascP (f \<circ> (#) x)"
  by (auto simp: ascP_def simp flip: append_Cons)

lemma ascP_simp [simp]:
  assumes "ascP f"
  shows "f [x] = f [] @ [x]"
  using assms [unfolded ascP_def, THEN spec, THEN spec, of "[]" "[x]"] by simp

lemma
  shows mset_runs: "\<Sum>\<^sub># (image_mset mset (mset (runs xs))) = mset xs"
    and mset_asc: "ascP f \<Longrightarrow> \<Sum>\<^sub># (image_mset mset (mset (asc x f ys))) = {#x#} + mset (f []) + mset ys"
    and mset_desc: "\<Sum>\<^sub># (image_mset mset (mset (desc x xs ys))) = {#x#} + mset xs + mset ys"
  by (induct xs and x f ys and x xs ys rule: runs_asc_desc.induct) auto

lemma mset_nmsort:
  "mset (nmsort xs) = mset xs"
  by (auto simp: mset_merge_all nmsort_def mset_runs)

lemma
  shows sorted_runs: "\<forall>x\<in>set (runs xs). sorted x"
    and sorted_asc: "ascP f \<Longrightarrow> sorted (f []) \<Longrightarrow> \<forall>x\<in>set (f []). x \<le> a \<Longrightarrow> \<forall>x\<in>set (asc a f ys). sorted x"
    and sorted_desc: "sorted xs \<Longrightarrow> \<forall>x\<in>set xs. a \<le> x \<Longrightarrow> \<forall>x\<in>set (desc a xs ys). sorted x"
  by (induct xs and a f ys and a xs ys rule: runs_asc_desc.induct)
    (auto simp: sorted_append not_less dest: order_trans, fastforce)

lemma sorted_nmsort:
  "sorted (nmsort xs)"
  by (auto intro: sorted_merge_all simp: nmsort_def sorted_runs)


subsection \<open>Running Time Analysis\<close>

fun C_runs :: "('a::linorder) list \<Rightarrow> nat" and
    C_asc :: "('a::linorder) \<Rightarrow> 'a list \<Rightarrow> nat" and
    C_desc :: "('a::linorder) \<Rightarrow> 'a list \<Rightarrow> nat"
  where
    "C_runs (a # b # xs) = 1 + (if a > b then C_desc b xs else C_asc b xs)"
  | "C_runs xs = 0"
  | "C_asc a (b # bs) = 1 + (if \<not> a > b then C_asc b bs else C_runs (b # bs))"
  | "C_asc a [] = 0"
  | "C_desc a (b # bs) = 1 + (if a > b then C_desc b bs else C_runs (b # bs))"
  | "C_desc a [] = 0"

fun C_nmsort :: "('a::linorder) list \<Rightarrow> nat"
  where
    "C_nmsort xs = C_runs xs + C_merge_all (runs xs)"

lemma
  fixes a :: "'a::linorder" and xs ys :: "'a list"
  shows C_runs: "C_runs xs \<le> length xs - 1"
    and C_asc: "C_asc a ys \<le> length ys"
    and C_desc: "C_desc a ys \<le> length ys"
  by (induct xs and a ys and a ys rule: C_runs_C_asc_C_desc.induct) auto

lemma
  shows length_runs: "length (runs xs) \<le> length xs"
    and length_asc: "ascP f \<Longrightarrow> length (asc a f ys) \<le> 1 + length ys"
    and length_desc: "length (desc a xs ys) \<le> 1 + length ys"
  by (induct xs and a f ys and a xs ys rule: runs_asc_desc.induct) auto

lemma
  shows length_concat_runs [simp]: "length (concat (runs xs)) = length xs"
    and length_concat_asc: "ascP f \<Longrightarrow> length (concat (asc a f ys)) = 1 + length (f []) + length ys"
    and length_concat_desc: "length (concat (desc a xs ys)) = 1 + length xs + length ys"
  by (induct xs and a f ys and a xs ys rule: runs_asc_desc.induct) auto

lemma log2_mono:
  "x > 0 \<Longrightarrow> x \<le> y \<Longrightarrow> log 2 x \<le> log 2 y"
  by auto

lemma
  shows runs_ne: "xs \<noteq> [] \<Longrightarrow> runs xs \<noteq> []"
    and "ascP f \<Longrightarrow> asc a f ys \<noteq> []"
    and "desc a xs ys \<noteq> []"
  by (induct xs and a f ys and a xs ys rule: runs_asc_desc.induct) simp_all

lemma C_nmsort:
  assumes [simp]: "length xs = n"
  shows "C_nmsort xs \<le> n + n * \<lceil>log 2 n\<rceil>"
proof -
  have [simp]: "xs = [] \<longleftrightarrow> length xs = 0" by blast
  have "int (C_merge_all (runs xs)) \<le> int n * \<lceil>log 2 (length (runs xs))\<rceil>"
    using C_merge_all' [of "runs xs"] by simp
  also have "\<dots> \<le> int n * \<lceil>log 2 n\<rceil>"
    using length_runs [of xs]
    by (cases n) (auto intro!: runs_ne mult_mono ceiling_mono log2_mono)
  finally have "int (C_merge_all (runs xs)) \<le> int n * \<lceil>log 2 n\<rceil>" .
  moreover have "C_runs xs \<le> n" using C_runs [of xs] by auto
  ultimately show ?thesis by (auto intro: add_mono)
qed

end
