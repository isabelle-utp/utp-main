(*
  File:         WB_Sort.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Author:       Maximilian Wuttke, Saarland University
  Maintainer:   Mathias Fleury, JKU

Correctness proof contributed by Maximilian Wuttke *)
theory WB_Sort
  imports Refine_Imperative_HOL.IICF "HOL-Library.Rewrite" Duplicate_Free_Multiset
begin

text \<open>This a complete copy-paste of the IsaFoL version because sharing is too hard.\<close>


text \<open>Every element between \<^term>\<open>lo\<close> and \<^term>\<open>hi\<close> can be chosen as pivot element.\<close>
definition choose_pivot :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat nres\<close> where
  \<open>choose_pivot _ _ _ lo hi = SPEC(\<lambda>k. k \<ge> lo \<and> k \<le> hi)\<close>

text \<open>The element at index \<open>p\<close> partitions the subarray \<open>lo..hi\<close>. This means that every element \<close>
definition isPartition_wrt :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>isPartition_wrt R xs lo hi p \<equiv> (\<forall> i. i \<ge> lo \<and> i < p \<longrightarrow> R (xs!i) (xs!p)) \<and> (\<forall> j. j > p \<and> j \<le> hi \<longrightarrow> R (xs!p) (xs!j))\<close>

lemma isPartition_wrtI:
  \<open>(\<And> i. \<lbrakk>i \<ge> lo; i < p\<rbrakk> \<Longrightarrow> R (xs!i) (xs!p)) \<Longrightarrow> (\<And> j. \<lbrakk>j > p; j \<le> hi\<rbrakk> \<Longrightarrow> R (xs!p) (xs!j)) \<Longrightarrow> isPartition_wrt R xs lo hi p\<close>
  by (simp add: isPartition_wrt_def)

definition isPartition :: \<open>'a :: order list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>isPartition xs lo hi p \<equiv> isPartition_wrt (\<le>) xs lo hi p\<close>

abbreviation isPartition_map :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>isPartition_map R h xs i j k \<equiv> isPartition_wrt (\<lambda>a b. R (h a) (h b)) xs i j k\<close>

lemma isPartition_map_def':
  \<open>lo \<le> p \<Longrightarrow> p \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow> isPartition_map R h xs lo hi p = isPartition_wrt R (map h xs) lo hi p\<close>
  by (auto simp add: isPartition_wrt_def conjI)


text \<open>Example: 6 is the pivot element (with index 4); \<^term>\<open>7\<close> is equal to the \<^term>\<open>length xs - 1\<close>.\<close>
lemma \<open>isPartition [0,5,3,4,6,9,8,10::nat] 0 7 4\<close>
  by (auto simp add: isPartition_def isPartition_wrt_def nth_Cons')



definition sublist :: \<open>'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list\<close> where
\<open>sublist xs i j \<equiv> take (Suc j - i) (drop i xs)\<close>

(*take from HashMap *)
lemma take_Suc0:
  "l\<noteq>[] \<Longrightarrow> take (Suc 0) l = [l!0]"
  "0 < length l \<Longrightarrow> take (Suc 0) l = [l!0]"
  "Suc n \<le> length l \<Longrightarrow> take (Suc 0) l = [l!0]"
  by (cases l, auto)+

lemma sublist_single: \<open>i < length xs \<Longrightarrow> sublist xs i i = [xs!i]\<close>
  by (cases xs) (auto simp add: sublist_def take_Suc0)

lemma insert_eq: \<open>insert a b = b \<union> {a}\<close>
  by auto

lemma sublist_nth: \<open>\<lbrakk>lo \<le> hi; hi < length xs; k+lo \<le> hi\<rbrakk> \<Longrightarrow> (sublist xs lo hi)!k = xs!(lo+k)\<close>
  by (simp add: sublist_def)

lemma sublist_length: \<open>\<lbrakk>i \<le> j; j < length xs\<rbrakk> \<Longrightarrow> length (sublist xs i j) = 1 + j - i\<close>
  by (simp add: sublist_def)

lemma sublist_not_empty: \<open>\<lbrakk>i \<le> j; j < length xs; xs \<noteq> []\<rbrakk> \<Longrightarrow> sublist xs i j \<noteq> []\<close>
  apply simp
  apply (rewrite List.length_greater_0_conv[symmetric])
  apply (rewrite sublist_length)
  by auto



lemma sublist_app: \<open>\<lbrakk>i1 \<le> i2; i2 \<le> i3\<rbrakk> \<Longrightarrow> sublist xs i1 i2 @ sublist xs (Suc i2) i3 = sublist xs i1 i3\<close>
  unfolding sublist_def
  by (smt Suc_eq_plus1_left Suc_le_mono append.assoc le_SucI le_add_diff_inverse le_trans same_append_eq take_add)

definition sorted_sublist_wrt :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>sorted_sublist_wrt R xs lo hi = sorted_wrt R (sublist xs lo hi)\<close>

definition sorted_sublist :: \<open>'a :: linorder list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>sorted_sublist xs lo hi = sorted_sublist_wrt (\<le>) xs lo hi\<close>

abbreviation sorted_sublist_map :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>sorted_sublist_map R h xs lo hi \<equiv> sorted_sublist_wrt (\<lambda>a b. R (h a) (h b)) xs lo hi\<close>

lemma sorted_sublist_map_def':
  \<open>lo < length xs \<Longrightarrow> sorted_sublist_map R h xs lo hi \<equiv> sorted_sublist_wrt R (map h xs) lo hi\<close>
  apply (simp add: sorted_sublist_wrt_def)
  by (simp add: drop_map sorted_wrt_map sublist_def take_map)

lemma sorted_sublist_wrt_refl: \<open>i < length xs \<Longrightarrow> sorted_sublist_wrt R xs i i\<close>
  by (auto simp add: sorted_sublist_wrt_def sublist_single)

lemma sorted_sublist_refl: \<open>i < length xs \<Longrightarrow> sorted_sublist xs i i\<close>
  by (auto simp add: sorted_sublist_def sorted_sublist_wrt_refl)

lemma sublist_map: \<open>sublist (map f xs) i j = map f (sublist xs i j)\<close>
  apply (auto simp add: sublist_def)
  by (simp add: drop_map take_map)


lemma take_set: \<open>j \<le> length xs \<Longrightarrow> x \<in> set (take j xs) \<equiv> (\<exists> k. k < j \<and> xs!k = x)\<close>
  apply (induction xs)
   apply simp
  by (meson in_set_conv_iff less_le_trans)

lemma drop_set: \<open>j \<le> length xs \<Longrightarrow> x \<in> set (drop j xs) \<equiv> (\<exists>k. j\<le>k\<and>k<length xs \<and> xs!k=x)\<close>
  by (smt Misc.in_set_drop_conv_nth) (* lemma found by sledgehammer *)

lemma sublist_el: \<open>i \<le> j \<Longrightarrow> j < length xs \<Longrightarrow> x \<in> set (sublist xs i j) \<equiv> (\<exists> k. k < Suc j-i \<and> xs!(i+k)=x)\<close>
  by (auto simp add: take_set sublist_def)

lemma sublist_el': \<open>i \<le> j \<Longrightarrow> j < length xs \<Longrightarrow> x \<in> set (sublist xs i j) \<equiv> (\<exists> k. i\<le>k\<and>k\<le>j \<and> xs!k=x)\<close>
  apply (subst sublist_el, assumption, assumption)
  by (smt Groups.add_ac(2) le_add1 le_add_diff_inverse less_Suc_eq less_diff_conv nat_less_le order_refl)


lemma sublist_lt: \<open>hi < lo \<Longrightarrow> sublist xs lo hi = []\<close>
  by (auto simp add: sublist_def)

lemma nat_le_eq_or_lt: \<open>(a :: nat) \<le> b = (a = b \<or> a < b)\<close>
  by linarith


lemma sorted_sublist_wrt_le: \<open>hi \<le> lo \<Longrightarrow> hi < length xs \<Longrightarrow> sorted_sublist_wrt R xs lo hi\<close>
  apply (auto simp add: nat_le_eq_or_lt)
  unfolding sorted_sublist_wrt_def
  subgoal apply (rewrite sublist_single) by auto
  subgoal by (auto simp add: sublist_lt)
  done

text \<open>Elements in a sorted sublists are actually sorted\<close>
lemma sorted_sublist_wrt_nth_le:
  assumes \<open>sorted_sublist_wrt R xs lo hi\<close> and \<open>lo \<le> hi\<close> and \<open>hi < length xs\<close> and
    \<open>lo \<le> i\<close> and \<open>i < j\<close> and \<open>j \<le> hi\<close>
  shows \<open>R (xs!i) (xs!j)\<close>
proof -
  have A: \<open>lo < length xs\<close> using assms(2) assms(3) by linarith
  obtain i' where I: \<open>i = lo + i'\<close> using assms(4) le_Suc_ex by auto
  obtain j' where J: \<open>j = lo + j'\<close> by (meson assms(4) assms(5) dual_order.trans le_iff_add less_imp_le_nat)
  show ?thesis
    using assms(1) apply (simp add: sorted_sublist_wrt_def I J)
    apply (rewrite sublist_nth[symmetric, where k=i', where lo=lo, where hi=hi])
    using assms apply auto subgoal using I by linarith
    apply (rewrite sublist_nth[symmetric, where k=j', where lo=lo, where hi=hi])
    using assms apply auto subgoal using J by linarith
    apply (rule sorted_wrt_nth_less)
    apply auto
    subgoal using I J nat_add_left_cancel_less by blast
    subgoal apply (simp add: sublist_length) using J by linarith
    done
qed

text \<open>We can make the assumption \<^term>\<open>i < j\<close> weaker if we have a reflexivie relation.\<close>
lemma sorted_sublist_wrt_nth_le':
  assumes ref: \<open>\<And> x. R x x\<close>
    and \<open>sorted_sublist_wrt R xs lo hi\<close> and \<open>lo \<le> hi\<close> and \<open>hi < length xs\<close>
    and \<open>lo \<le> i\<close> and \<open>i \<le> j\<close> and \<open>j \<le> hi\<close>
  shows \<open>R (xs!i) (xs!j)\<close>
proof -
  have \<open>i < j \<or> i = j\<close> using \<open>i \<le> j\<close> by linarith
  then consider (a) \<open>i < j\<close> |
                (b) \<open>i = j\<close> by blast
  then show ?thesis
  proof cases
    case a
    then show ?thesis
      using assms(2-5,7) sorted_sublist_wrt_nth_le by blast
  next
    case b
    then show ?thesis
      by (simp add: ref)
  qed
qed



(*
lemma sorted_sublist_map_nth_le:
  assumes \<open>sorted_sublist_map R h xs lo hi\<close> and \<open>lo \<le> hi\<close> and \<open>hi < length xs\<close> and
    \<open>lo \<le> i\<close> and \<open>i < j\<close> and \<open>j \<le> hi\<close>
  shows \<open>R (h (xs!i)) (h (xs!j))\<close>
proof -
  show ?thesis
    using assms by (rule sorted_sublist_wrt_nth_le)
qed
*)



lemma sorted_sublist_le: \<open>hi \<le> lo \<Longrightarrow> hi < length xs \<Longrightarrow> sorted_sublist xs lo hi\<close>
  by (auto simp add: sorted_sublist_def sorted_sublist_wrt_le)

lemma sorted_sublist_map_le: \<open>hi \<le> lo \<Longrightarrow> hi < length xs \<Longrightarrow> sorted_sublist_map R h xs lo hi\<close>
  by (auto simp add: sorted_sublist_wrt_le)

lemma sublist_cons: \<open>lo < hi \<Longrightarrow> hi < length xs \<Longrightarrow> sublist xs lo hi = xs!lo # sublist xs (Suc lo) hi\<close>
  by (metis Cons_eq_appendI append_self_conv2 less_imp_le_nat less_or_eq_imp_le less_trans
      sublist_app sublist_single)

lemma sorted_sublist_wrt_cons':
  \<open>sorted_sublist_wrt R xs (lo+1) hi \<Longrightarrow> lo \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow> (\<forall>j. lo<j\<and>j\<le>hi \<longrightarrow> R (xs!lo) (xs!j)) \<Longrightarrow> sorted_sublist_wrt R xs lo hi\<close>
  apply (auto simp add: nat_le_eq_or_lt sorted_sublist_wrt_def)
  apply (auto 5 4 simp add: sublist_cons sublist_el less_diff_conv add.commute[of _ lo]
      dest: Suc_lessI sublist_single)
  done

lemma sorted_sublist_wrt_cons:
  assumes trans: \<open>(\<And> x y z. \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z)\<close> and
    \<open>sorted_sublist_wrt R xs (lo+1) hi\<close> and
    \<open>lo \<le> hi\<close> and \<open>hi < length xs \<close> and \<open>R (xs!lo) (xs!(lo+1))\<close>
  shows \<open>sorted_sublist_wrt R xs lo hi\<close>
proof -
  show ?thesis
    apply (rule sorted_sublist_wrt_cons') using assms apply auto
    subgoal premises assms' for j
    proof -
      have A: \<open>j=lo+1 \<or> j>lo+1\<close> using assms'(5) by linarith
      show ?thesis
        using A proof
        assume A: \<open>j=lo+1\<close> show ?thesis
          by (simp add: A assms')
      next
        assume A: \<open>j>lo+1\<close> show ?thesis
          apply (rule trans)
          apply (rule assms(5))
          apply (rule sorted_sublist_wrt_nth_le[OF assms(2), where i=\<open>lo+1\<close>, where j=j])
          subgoal using A assms'(6) by linarith
          subgoal using assms'(3) less_imp_diff_less by blast
          subgoal using assms'(5) by auto
          subgoal using A by linarith
          subgoal by (simp add: assms'(6))
          done
      qed
    qed
    done
qed

lemma sorted_sublist_map_cons:
  \<open>(\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)) \<Longrightarrow>
    sorted_sublist_map R h xs (lo+1) hi \<Longrightarrow> lo \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow> R (h (xs!lo)) (h (xs!(lo+1))) \<Longrightarrow> sorted_sublist_map R h xs lo hi\<close>
  by (blast intro: sorted_sublist_wrt_cons)


lemma sublist_snoc: \<open>lo < hi \<Longrightarrow> hi < length xs \<Longrightarrow> sublist xs lo hi = sublist xs lo (hi-1) @ [xs!hi]\<close>
  apply (simp add: sublist_def)
proof -
  assume a1: "lo < hi"
  assume "hi < length xs"
  then have "take lo xs @ take (Suc hi - lo) (drop lo xs) = (take lo xs @ take (hi - lo) (drop lo xs)) @ [xs ! hi]"
    using a1 by (metis (no_types) Suc_diff_le add_Suc_right hd_drop_conv_nth le_add_diff_inverse less_imp_le_nat take_add take_hd_drop)
  then show "take (Suc hi - lo) (drop lo xs) = take (hi - lo) (drop lo xs) @ [xs ! hi]"
    by simp
qed

lemma sorted_sublist_wrt_snoc':
  \<open>sorted_sublist_wrt R xs lo (hi-1) \<Longrightarrow> lo \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow> (\<forall>j. lo\<le>j\<and>j<hi \<longrightarrow> R (xs!j) (xs!hi)) \<Longrightarrow> sorted_sublist_wrt R xs lo hi\<close>
  apply (simp add: sorted_sublist_wrt_def)
  apply (auto simp add: nat_le_eq_or_lt)
  subgoal by (simp add: sublist_single)
  by (auto simp add: sublist_snoc sublist_el sorted_wrt_append add.commute[of lo] less_diff_conv
      simp: leI simp flip:nat_le_eq_or_lt)


lemma sorted_sublist_wrt_snoc:
  assumes trans: \<open>(\<And> x y z. \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z)\<close> and
    \<open>sorted_sublist_wrt R xs lo (hi-1)\<close> and
    \<open>lo \<le> hi\<close> and \<open>hi < length xs\<close> and \<open>(R (xs!(hi-1)) (xs!hi))\<close>
  shows \<open>sorted_sublist_wrt R xs lo hi\<close>
proof -
  show ?thesis
    apply (rule sorted_sublist_wrt_snoc') using assms apply auto
    subgoal premises assms' for j
    proof -
      have A: \<open>j=hi-1 \<or> j<hi-1\<close> using assms'(6) by linarith
      show ?thesis
        using A proof
        assume A: \<open>j=hi-1\<close> show ?thesis
          by (simp add: A assms')
      next
        assume A: \<open>j<hi-1\<close> show ?thesis
          apply (rule trans)
           apply (rule sorted_sublist_wrt_nth_le[OF assms(2), where i=j, where j=\<open>hi-1\<close>])
               prefer 6
               apply (rule assms(5))
              apply auto
          subgoal using A assms'(5) by linarith
          subgoal using assms'(3) less_imp_diff_less by blast
          subgoal using assms'(5) by auto
          subgoal using A by linarith
          done
      qed
    qed
    done
qed

lemma sublist_split: \<open>lo \<le> hi \<Longrightarrow> lo < p \<Longrightarrow> p < hi \<Longrightarrow> hi < length xs \<Longrightarrow> sublist xs lo p @ sublist xs (p+1) hi = sublist xs lo hi\<close>
  by (simp add: sublist_app)

lemma sublist_split_part: \<open>lo \<le> hi \<Longrightarrow> lo < p \<Longrightarrow> p < hi \<Longrightarrow> hi < length xs \<Longrightarrow> sublist xs lo (p-1) @ xs!p # sublist xs (p+1) hi = sublist xs lo hi\<close>
  by (auto simp add: sublist_split[symmetric] sublist_snoc[where xs=xs,where lo=lo,where hi=p])


text \<open>A property for partitions (we always assume that \<^term>\<open>R\<close> is transitive.\<close>
lemma isPartition_wrt_trans:
\<open>(\<And> x y z. \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z) \<Longrightarrow>
  isPartition_wrt R xs lo hi p \<Longrightarrow>
  (\<forall>i j. lo \<le> i \<and> i < p \<and> p < j \<and> j \<le> hi \<longrightarrow> R (xs!i) (xs!j))\<close>
  by (auto simp add: isPartition_wrt_def)

lemma isPartition_map_trans:
\<open>(\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)) \<Longrightarrow>
  hi < length xs \<Longrightarrow>
  isPartition_map R h xs lo hi p \<Longrightarrow>
  (\<forall>i j. lo \<le> i \<and> i < p \<and> p < j \<and> j \<le> hi \<longrightarrow> R (h (xs!i)) (h (xs!j)))\<close>
  by (auto simp add: isPartition_wrt_def)


lemma merge_sorted_wrt_partitions_between':
  \<open>lo \<le> hi \<Longrightarrow> lo < p \<Longrightarrow> p < hi \<Longrightarrow> hi < length xs \<Longrightarrow>
    isPartition_wrt R xs lo hi p \<Longrightarrow>
    sorted_sublist_wrt R xs lo (p-1) \<Longrightarrow> sorted_sublist_wrt R xs (p+1) hi \<Longrightarrow>
    (\<forall>i j. lo \<le> i \<and> i < p \<and> p < j \<and> j \<le> hi \<longrightarrow> R (xs!i) (xs!j)) \<Longrightarrow>
    sorted_sublist_wrt R xs lo hi\<close>
  apply (auto simp add: isPartition_def isPartition_wrt_def sorted_sublist_def sorted_sublist_wrt_def sublist_map)
  apply (simp add: sublist_split_part[symmetric])
  apply (auto simp add: List.sorted_wrt_append)
  subgoal by (auto simp add: sublist_el)
  subgoal by (auto simp add: sublist_el)
  subgoal by (auto simp add: sublist_el')
  done

lemma merge_sorted_wrt_partitions_between:
  \<open>(\<And> x y z. \<lbrakk>R x y; R y z\<rbrakk> \<Longrightarrow> R x z) \<Longrightarrow>
    isPartition_wrt R xs lo hi p \<Longrightarrow>
    sorted_sublist_wrt R xs lo (p-1) \<Longrightarrow> sorted_sublist_wrt R xs (p+1) hi \<Longrightarrow>
    lo \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow> lo < p \<Longrightarrow> p < hi \<Longrightarrow> hi < length xs \<Longrightarrow>
    sorted_sublist_wrt R xs lo hi\<close>
  by (simp add: merge_sorted_wrt_partitions_between' isPartition_wrt_trans)


(*
lemma merge_sorted_map_partitions_between:
  \<open>(\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)) \<Longrightarrow>
    isPartition_map R h xs lo hi p \<Longrightarrow>
    sorted_sublist_map R h xs lo (p-1) \<Longrightarrow> sorted_sublist_map R h xs (p+1) hi \<Longrightarrow>
    lo \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow> lo < p \<Longrightarrow> p < hi \<Longrightarrow> hi < length xs \<Longrightarrow>
    sorted_sublist_map R h xs lo hi\<close>
  by (simp add: merge_sorted_wrt_partitions_between' isPartition_map_trans)
*)




text \<open>The main theorem to merge sorted lists\<close>
lemma merge_sorted_wrt_partitions:
  \<open>isPartition_wrt R xs lo hi p \<Longrightarrow>
    sorted_sublist_wrt R xs lo (p - Suc 0) \<Longrightarrow> sorted_sublist_wrt R xs (Suc p) hi \<Longrightarrow>
    lo \<le> hi \<Longrightarrow> lo \<le> p \<Longrightarrow> p \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow>
    (\<forall>i j. lo \<le> i \<and> i < p \<and> p < j \<and> j \<le> hi \<longrightarrow> R (xs!i) (xs!j)) \<Longrightarrow>
    sorted_sublist_wrt R xs lo hi\<close>
  subgoal premises assms
  proof -
    have C: \<open>lo=p\<and>p=hi \<or> lo=p\<and>p<hi \<or> lo<p\<and>p=hi \<or> lo<p\<and>p<hi\<close>
      using assms by linarith
    show ?thesis
      using C apply auto
      subgoal \<comment> \<open>lo=p=hi\<close>
        apply (rule sorted_sublist_wrt_refl)
        using assms by auto
      subgoal \<comment> \<open>lo=p<hi\<close>
        using assms by (simp add: isPartition_def isPartition_wrt_def sorted_sublist_wrt_cons')
      subgoal \<comment> \<open>lo<p=hi\<close>
        using assms by (simp add: isPartition_def isPartition_wrt_def sorted_sublist_wrt_snoc')
      subgoal \<comment> \<open>lo<p<hi\<close>
        using assms
        apply (rewrite merge_sorted_wrt_partitions_between'[where p=p])
        by auto
      done
  qed
  done

theorem merge_sorted_map_partitions:
  \<open>(\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)) \<Longrightarrow>
    isPartition_map R h xs lo hi p \<Longrightarrow>
    sorted_sublist_map R h xs lo (p - Suc 0) \<Longrightarrow> sorted_sublist_map R h xs (Suc p) hi \<Longrightarrow>
    lo \<le> hi \<Longrightarrow> lo \<le> p \<Longrightarrow> p \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow>
    sorted_sublist_map R h xs lo hi\<close>
  apply (rule merge_sorted_wrt_partitions) apply auto
  by (simp add: merge_sorted_wrt_partitions isPartition_map_trans)


lemma partition_wrt_extend:
  \<open>isPartition_wrt R xs lo' hi' p \<Longrightarrow>
  hi < length xs \<Longrightarrow>
  lo \<le> lo' \<Longrightarrow> lo' \<le> hi \<Longrightarrow> hi' \<le> hi \<Longrightarrow>
  lo' \<le> p \<Longrightarrow> p \<le> hi' \<Longrightarrow>
  (\<And> i. lo\<le>i \<Longrightarrow> i <lo' \<Longrightarrow> R (xs!i) (xs!p)) \<Longrightarrow>
  (\<And> j. hi'<j \<Longrightarrow> j\<le>hi \<Longrightarrow> R (xs!p) (xs!j)) \<Longrightarrow>
  isPartition_wrt R xs lo hi p\<close>
  unfolding isPartition_wrt_def
  apply (intro conjI)
  subgoal
    by (force simp: not_le)
  subgoal
    using leI by blast
  done

lemma partition_map_extend:
  \<open>isPartition_map R h xs lo' hi' p \<Longrightarrow>
  hi < length xs \<Longrightarrow>
  lo \<le> lo' \<Longrightarrow> lo' \<le> hi \<Longrightarrow> hi' \<le> hi \<Longrightarrow>
  lo' \<le> p \<Longrightarrow> p \<le> hi' \<Longrightarrow>
  (\<And> i. lo\<le>i \<Longrightarrow> i <lo' \<Longrightarrow> R (h (xs!i)) (h (xs!p))) \<Longrightarrow>
  (\<And> j. hi'<j \<Longrightarrow> j\<le>hi \<Longrightarrow> R (h (xs!p)) (h (xs!j))) \<Longrightarrow>
  isPartition_map R h xs lo hi p\<close>
  by (auto simp add: partition_wrt_extend)


lemma isPartition_empty:
  \<open>(\<And> j. \<lbrakk>lo < j; j \<le> hi\<rbrakk> \<Longrightarrow> R (xs ! lo) (xs ! j)) \<Longrightarrow>
  isPartition_wrt R xs lo hi lo\<close>
  by (auto simp add: isPartition_wrt_def)



lemma take_ext:
  \<open>(\<forall>i<k. xs'!i=xs!i) \<Longrightarrow>
  k < length xs \<Longrightarrow> k < length xs' \<Longrightarrow>
  take k xs' = take k xs\<close>
  by (simp add: nth_take_lemma)

lemma drop_ext':
  \<open>(\<forall>i. i\<ge>k \<and> i<length xs \<longrightarrow> xs'!i=xs!i) \<Longrightarrow>
   0<k \<Longrightarrow> xs\<noteq>[] \<Longrightarrow> \<comment> \<open>These corner cases will be dealt with in the next lemma\<close>
   length xs'=length xs \<Longrightarrow>
   drop k xs' = drop k xs\<close>
  apply (rewrite in \<open>drop _ \<hole> = _\<close> List.rev_rev_ident[symmetric])
  apply (rewrite in \<open>_ = drop _ \<hole>\<close> List.rev_rev_ident[symmetric])
  apply (rewrite in \<open>\<hole> = _\<close> List.drop_rev)
  apply (rewrite in \<open>_ = \<hole>\<close> List.drop_rev)
  apply simp
  apply (rule take_ext)
  by (auto simp add: rev_nth)

lemma drop_ext:
\<open>(\<forall>i. i\<ge>k \<and> i<length xs \<longrightarrow> xs'!i=xs!i) \<Longrightarrow>
   length xs'=length xs \<Longrightarrow>
   drop k xs' = drop k xs\<close>
  apply (cases xs)
   apply auto
  apply (cases k)
  subgoal  by (simp add: nth_equalityI)
  subgoal apply (rule drop_ext') by auto
  done


lemma sublist_ext':
  \<open>(\<forall>i. lo\<le>i\<and>i\<le>hi \<longrightarrow> xs'!i=xs!i) \<Longrightarrow>
   length xs' = length xs \<Longrightarrow>
   lo \<le> hi \<Longrightarrow> Suc hi < length xs \<Longrightarrow>
   sublist xs' lo hi = sublist xs lo hi\<close>
  apply (simp add: sublist_def)
  apply (rule take_ext)
  by auto


lemma lt_Suc: \<open>(a < b) = (Suc a = b \<or> Suc a < b)\<close>
  by auto

lemma sublist_until_end_eq_drop: \<open>Suc hi = length xs \<Longrightarrow> sublist xs lo hi = drop lo xs\<close>
  by (simp add: sublist_def)

lemma sublist_ext:
  \<open>(\<forall>i. lo\<le>i\<and>i\<le>hi \<longrightarrow> xs'!i=xs!i) \<Longrightarrow>
   length xs' = length xs \<Longrightarrow>
   lo \<le> hi \<Longrightarrow> hi < length xs \<Longrightarrow>
   sublist xs' lo hi = sublist xs lo hi\<close>
  apply (auto simp add: lt_Suc[where a=hi])
  subgoal by (auto simp add: sublist_until_end_eq_drop drop_ext)
  subgoal by (auto simp add: sublist_ext')
  done

lemma sorted_wrt_lower_sublist_still_sorted:
  assumes \<open>sorted_sublist_wrt R xs lo (lo' - Suc 0)\<close> and
    \<open>lo \<le> lo'\<close> and \<open>lo' < length xs\<close> and
    \<open>(\<forall> i. lo\<le>i\<and>i<lo' \<longrightarrow> xs'!i=xs!i)\<close> and \<open>length xs' = length xs\<close>
  shows \<open>sorted_sublist_wrt R xs' lo (lo' - Suc 0)\<close>
proof -
  have l: \<open>lo < lo' - 1 \<or> lo \<ge> lo'-1\<close>
    by linarith
  show ?thesis
    using l apply auto
    subgoal \<comment> \<open>lo < lo' - 1\<close>
      apply (auto simp add: sorted_sublist_wrt_def)
      apply (rewrite sublist_ext[where xs=xs])
      using assms by (auto simp add: sorted_sublist_wrt_def)
    subgoal \<comment> \<open>lo >= lo' - 1\<close>
      using assms by (auto simp add: sorted_sublist_wrt_le)
    done
qed

lemma sorted_map_lower_sublist_still_sorted:
  assumes \<open>sorted_sublist_map R h xs lo (lo' - Suc 0)\<close> and
    \<open>lo \<le> lo'\<close> and \<open>lo' < length xs\<close> and
    \<open>(\<forall> i. lo\<le>i\<and>i<lo' \<longrightarrow> xs'!i=xs!i)\<close> and \<open>length xs' = length xs\<close>
  shows \<open>sorted_sublist_map R h xs' lo (lo' - Suc 0)\<close>
  using assms by (rule sorted_wrt_lower_sublist_still_sorted)

lemma sorted_wrt_upper_sublist_still_sorted:
  assumes \<open>sorted_sublist_wrt R xs (hi'+1) hi\<close> and
    \<open>lo \<le> lo'\<close> and \<open>hi < length xs\<close> and
    \<open>\<forall> j. hi'<j\<and>j\<le>hi \<longrightarrow> xs'!j=xs!j\<close> and \<open>length xs' = length xs\<close>
  shows \<open>sorted_sublist_wrt R xs' (hi'+1) hi\<close>
proof -
  have l: \<open>hi' + 1 < hi \<or> hi' + 1 \<ge> hi\<close>
    by linarith
  show ?thesis
    using l apply auto
    subgoal \<comment> \<open>hi' + 1 < h\<close>
      apply (auto simp add: sorted_sublist_wrt_def)
      apply (rewrite sublist_ext[where xs=xs])
      using assms by (auto simp add: sorted_sublist_wrt_def)
    subgoal \<comment> \<open>\<^term>\<open>hi' + 1 \<ge> hi\<close>\<close>
      using assms by (auto simp add: sorted_sublist_wrt_le)
    done
qed

lemma sorted_map_upper_sublist_still_sorted:
  assumes \<open>sorted_sublist_map R h xs (hi'+1) hi\<close> and
    \<open>lo \<le> lo'\<close> and \<open>hi < length xs\<close> and
    \<open>\<forall> j. hi'<j\<and>j\<le>hi \<longrightarrow> xs'!j=xs!j\<close> and \<open>length xs' = length xs\<close>
  shows \<open>sorted_sublist_map R h xs' (hi'+1) hi\<close>
  using assms by (rule sorted_wrt_upper_sublist_still_sorted)







text \<open>The specification of the partition function\<close>
definition partition_spec :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>partition_spec R h xs lo hi xs' p \<equiv>
    mset xs' = mset xs \<and> \<comment> \<open>The list is a permutation\<close>
    isPartition_map R h xs' lo hi p \<and> \<comment> \<open>We have a valid partition on the resulting list\<close>
    lo \<le> p \<and> p \<le> hi \<and> \<comment> \<open>The partition index is in bounds\<close>
    (\<forall> i. i<lo \<longrightarrow> xs'!i=xs!i) \<and> (\<forall> i. hi<i\<and>i<length xs' \<longrightarrow> xs'!i=xs!i)\<close> \<comment> \<open>Everything else is unchanged.\<close>

lemma in_set_take_conv_nth:
  \<open>x \<in> set (take n xs) \<longleftrightarrow> (\<exists>m<min n (length xs). xs ! m = x)\<close>
  by (metis in_set_conv_nth length_take min.commute min.strict_boundedE nth_take)

lemma mset_drop_upto: \<open>mset (drop a N) = {#N!i. i \<in># mset_set {a..<length N}#}\<close>
proof (induction N arbitrary: a)
  case Nil
  then show ?case by simp
next
  case (Cons c N)
  have upt: \<open>{0..<Suc (length N)} = insert 0 {1..<Suc (length N)}\<close>
    by auto
  then have H: \<open>mset_set {0..<Suc (length N)} = add_mset 0 (mset_set {1..<Suc (length N)})\<close>
    unfolding upt by auto
  have mset_case_Suc: \<open>{#case x of 0 \<Rightarrow> c | Suc x \<Rightarrow> N ! x . x \<in># mset_set {Suc a..<Suc b}#} =
    {#N ! (x-1) . x \<in># mset_set {Suc a..<Suc b}#}\<close> for a b
    by (rule image_mset_cong) (auto split: nat.splits)
  have Suc_Suc: \<open>{Suc a..<Suc b} = Suc ` {a..<b}\<close> for a b
    by auto
  then have mset_set_Suc_Suc: \<open>mset_set {Suc a..<Suc b} = {#Suc n. n \<in># mset_set {a..<b}#}\<close> for a b
    unfolding Suc_Suc by (subst image_mset_mset_set[symmetric]) auto
  have *: \<open>{#N ! (x-Suc 0) . x \<in># mset_set {Suc a..<Suc b}#} = {#N ! x . x \<in># mset_set {a..<b}#}\<close>
    for a b
    by (auto simp add: mset_set_Suc_Suc multiset.map_comp comp_def)
  show ?case
    apply (cases a)
    using Cons[of 0] Cons by (auto simp: nth_Cons drop_Cons H mset_case_Suc *)
qed

(* Actually, I only need that \<open>set (sublist xs' lo hi) = set (sublist xs lo hi)\<close> *)
lemma mathias:
  assumes
        Perm: \<open>mset xs' = mset xs\<close>
    and I: \<open>lo\<le>i\<close> \<open>i\<le>hi\<close> \<open>xs'!i=x\<close>
    and Bounds: \<open>hi < length xs\<close>
    and Fix: \<open>\<And> i. i<lo \<Longrightarrow> xs'!i = xs!i\<close> \<open>\<And> j. \<lbrakk>hi<j; j<length xs\<rbrakk> \<Longrightarrow> xs'!j = xs!j\<close>
  shows \<open>\<exists>j. lo\<le>j\<and>j\<le>hi \<and> xs!j = x\<close>
proof -
  define xs1 xs2 xs3 xs1' xs2' xs3' where
     \<open>xs1 = take lo xs\<close> and
     \<open>xs2 = take (Suc hi - lo) (drop lo xs)\<close> and
     \<open>xs3 = drop (Suc hi) xs\<close> and
     \<open>xs1' = take lo xs'\<close> and
     \<open>xs2' = take (Suc hi - lo) (drop lo xs')\<close> and
     \<open>xs3' = drop (Suc hi) xs'\<close>
  have [simp]: \<open>length xs' = length xs\<close>
    using Perm by (auto dest: mset_eq_length)
  have [simp]: \<open>mset xs1 = mset xs1'\<close>
    using Fix(1) unfolding xs1_def xs1'_def
    by (metis Perm le_cases mset_eq_length nth_take_lemma take_all)
  have [simp]: \<open>mset xs3 = mset xs3'\<close>
    using Fix(2) unfolding xs3_def xs3'_def mset_drop_upto
    by (auto intro: image_mset_cong)
  have \<open>xs = xs1 @ xs2 @ xs3\<close> \<open>xs' = xs1' @ xs2' @ xs3'\<close>
    using I unfolding xs1_def xs2_def xs3_def xs1'_def xs2'_def xs3'_def
    by (metis append.assoc append_take_drop_id le_SucI le_add_diff_inverse order_trans take_add)+
  moreover have \<open>xs ! i = xs2 ! (i - lo)\<close> \<open>i \<ge> length xs1\<close>
    using I Bounds unfolding xs2_def xs1_def by (auto simp: nth_take min_def)
  moreover have  \<open>x \<in> set xs2'\<close>
    using I Bounds unfolding xs2'_def
    by (auto simp: in_set_take_conv_nth
       intro!: exI[of _ \<open>i - lo\<close>])
  ultimately have \<open>x \<in> set xs2\<close>
    using Perm I by (auto dest: mset_eq_setD)
  then obtain j where \<open>xs ! (lo + j) = x\<close> \<open>j \<le> hi - lo\<close>
    unfolding in_set_conv_nth xs2_def
    by auto
  then show ?thesis
    using Bounds I
    by (auto intro: exI[of _ \<open>lo+j\<close>])
qed


text \<open>If we fix the left and right rest of two permutated lists, then the sublists are also permutations.\<close>
text \<open>But we only need that the sets are equal.\<close>
lemma mset_sublist_incl:
  assumes Perm: \<open>mset xs' = mset xs\<close>
    and Fix: \<open>\<And> i. i<lo \<Longrightarrow> xs'!i = xs!i\<close> \<open>\<And> j. \<lbrakk>hi<j; j<length xs\<rbrakk> \<Longrightarrow> xs'!j = xs!j\<close>
    and bounds: \<open>lo \<le> hi\<close> \<open>hi < length xs\<close>
  shows \<open>set (sublist xs' lo hi) \<subseteq> set (sublist xs lo hi)\<close>
proof
  fix x
  assume \<open>x \<in> set (sublist xs' lo hi)\<close>
  then have \<open>\<exists>i. lo\<le>i\<and>i\<le>hi \<and> xs'!i=x\<close>
    by (metis assms(1) bounds(1) bounds(2) size_mset sublist_el')
  then obtain i where I: \<open>lo\<le>i\<close> \<open>i\<le>hi\<close> \<open>xs'!i=x\<close> by blast
  have \<open>\<exists>j. lo\<le>j\<and>j\<le>hi \<and> xs!j=x\<close>
    using Perm I bounds(2) Fix by (rule mathias, auto)
  then show \<open>x \<in> set (sublist xs lo hi)\<close>
    by (simp add: bounds(1) bounds(2) sublist_el')
qed


lemma mset_sublist_eq:
  assumes \<open>mset xs' = mset xs\<close>
    and \<open>\<And> i. i<lo \<Longrightarrow> xs'!i = xs!i\<close>
    and \<open>\<And> j. \<lbrakk>hi<j; j<length xs\<rbrakk> \<Longrightarrow> xs'!j = xs!j\<close>
    and bounds: \<open>lo \<le> hi\<close> \<open>hi < length xs\<close>
  shows \<open>set (sublist xs' lo hi) = set (sublist xs lo hi)\<close>
proof
  show \<open>set (sublist xs' lo hi) \<subseteq> set (sublist xs lo hi)\<close>
    apply (rule mset_sublist_incl)
    using assms by auto
  show \<open>set (sublist xs lo hi) \<subseteq> set (sublist xs' lo hi)\<close>
    by (rule mset_sublist_incl) (metis assms size_mset)+
qed



text \<open>Our abstract recursive quicksort procedure. We abstract over a partition procedure.\<close>
definition quicksort :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<times> nat \<times> 'a list \<Rightarrow> 'a list nres\<close> where
\<open>quicksort R h = (\<lambda>(lo,hi,xs0). do {
  RECT (\<lambda>f (lo,hi,xs). do {
      ASSERT(lo \<le> hi \<and> hi < length xs \<and> mset xs = mset xs0); \<comment> \<open>Premise for a partition function\<close>
      (xs, p) \<leftarrow> SPEC(uncurry (partition_spec R h xs lo hi)); \<comment> \<open>Abstract partition function\<close>
      ASSERT(mset xs = mset xs0);
      xs \<leftarrow> (if p-1\<le>lo then RETURN xs else f (lo, p-1, xs));
      ASSERT(mset xs = mset xs0);
      if hi\<le>p+1 then RETURN xs else f (p+1, hi, xs)
    }) (lo,hi,xs0)
  })\<close>

text \<open>As premise for quicksor, we only need that the indices are ok.\<close>
definition quicksort_pre :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow>  nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
  \<open>quicksort_pre R h xs0 lo hi xs \<equiv> lo \<le> hi \<and> hi < length xs \<and> mset xs = mset xs0\<close>

definition quicksort_post :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
  \<open>quicksort_post R h lo hi xs xs' \<equiv>
    mset xs' = mset xs \<and>
    sorted_sublist_map R h xs' lo hi \<and>
    (\<forall> i. i<lo \<longrightarrow> xs'!i = xs!i) \<and>
    (\<forall> j. hi<j\<and>j<length xs \<longrightarrow> xs'!j = xs!j)\<close>

text \<open>Convert Pure to HOL\<close>
lemma quicksort_postI:
  \<open>\<lbrakk>mset xs' = mset xs; sorted_sublist_map R h xs' lo hi; (\<And> i. \<lbrakk>i<lo\<rbrakk> \<Longrightarrow> xs'!i = xs!i); (\<And> j. \<lbrakk>hi<j; j<length xs\<rbrakk> \<Longrightarrow> xs'!j = xs!j)\<rbrakk> \<Longrightarrow> quicksort_post R h lo hi xs xs'\<close>
  by (auto simp add: quicksort_post_def)


text \<open>The first case for the correctness proof of (abstract) quicksort: We assume that we called the partition function, and we have \<^term>\<open>p-1\<le>lo\<close> and \<^term>\<open>hi\<le>p+1\<close>.\<close>
lemma quicksort_correct_case1:
  assumes trans: \<open>\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and lin: \<open>\<And>x y. x \<noteq> y \<Longrightarrow> R (h x) (h y) \<or> R (h y) (h x)\<close>
    and pre: \<open>quicksort_pre R h xs0 lo hi xs\<close>
    and part: \<open>partition_spec R h xs lo hi xs' p\<close>
    and ifs: \<open>p-1 \<le> lo\<close> \<open>hi \<le> p+1\<close>
  shows \<open>quicksort_post R h lo hi xs xs'\<close>
proof -
  text \<open>First boilerplate code step: 'unfold' the HOL definitions in the assumptions and convert them to Pure\<close>
  have pre: \<open>lo \<le> hi\<close> \<open>hi < length xs\<close>
    using pre by (auto simp add: quicksort_pre_def)
(*
  have part_perm: \<open>set (sublist xs' lo hi) = set (sublist xs lo hi)\<close>
    using part partition_spec_set_sublist pre(1) pre(2) by blast
*)
  have part: \<open>mset xs' = mset xs\<close> True
    \<open>isPartition_map R h xs' lo hi p\<close> \<open>lo \<le> p\<close> \<open>p \<le> hi\<close>
    \<open>\<And> i. i<lo \<Longrightarrow> xs'!i=xs!i\<close> \<open>\<And> i. \<lbrakk>hi<i; i<length xs'\<rbrakk> \<Longrightarrow> xs'!i=xs!i\<close>
    using part by (auto simp add: partition_spec_def)


  have sorted_lower: \<open>sorted_sublist_map R h xs' lo (p - Suc 0)\<close>
  proof -
    show ?thesis
      apply (rule sorted_sublist_wrt_le)
      subgoal using ifs(1) by auto
      subgoal using ifs(1) mset_eq_length part(1) pre(1) pre(2) by fastforce
      done
  qed

  have sorted_upper: \<open>sorted_sublist_map R h xs' (Suc p) hi\<close>
  proof -
    show ?thesis
      apply (rule sorted_sublist_wrt_le)
      subgoal using ifs(2) by auto
      subgoal using ifs(1) mset_eq_length part(1) pre(1) pre(2) by fastforce
      done
  qed

  have sorted_middle: \<open>sorted_sublist_map R h xs' lo hi\<close>
  proof -
    show ?thesis
      apply (rule merge_sorted_map_partitions[where p=p])
      subgoal by (rule trans)
      subgoal by (rule part)
      subgoal by (rule sorted_lower)
      subgoal by (rule sorted_upper)
      subgoal using pre(1) by auto
      subgoal by (simp add: part(4))
      subgoal by (simp add: part(5))
      subgoal by (metis part(1) pre(2) size_mset)
      done
  qed

  show ?thesis
  proof (intro quicksort_postI)
    show \<open>mset xs' = mset xs\<close>
      by (simp add: part(1))
  next
    show \<open>sorted_sublist_map R h xs' lo hi\<close>
      by (rule sorted_middle)
  next
      show \<open>\<And>i. i < lo \<Longrightarrow> xs' ! i = xs ! i\<close>
      using part(6) by blast
  next
    show \<open>\<And>j. \<lbrakk>hi < j; j < length xs\<rbrakk> \<Longrightarrow> xs' ! j = xs ! j\<close>
      by (metis part(1) part(7) size_mset)
  qed
qed


text \<open>In the second case, we have to show that the precondition still holds for (p+1, hi, x') after the partition.\<close>
lemma quicksort_correct_case2:
  assumes
        pre: \<open>quicksort_pre R h xs0 lo hi xs\<close>
    and part: \<open>partition_spec R h xs lo hi xs' p\<close>
    and ifs: \<open>\<not> hi \<le> p + 1\<close>
  shows \<open>quicksort_pre R h xs0 (Suc p) hi xs'\<close>
proof -
  text \<open>First boilerplate code step: 'unfold' the HOL definitions in the assumptions and convert them to Pure\<close>
  have pre: \<open>lo \<le> hi\<close> \<open>hi < length xs\<close> \<open>mset xs = mset xs0\<close>
    using pre by (auto simp add: quicksort_pre_def)
  have part: \<open>mset xs' = mset xs\<close> True
    \<open>isPartition_map R h xs' lo hi p\<close> \<open>lo \<le> p\<close> \<open>p \<le> hi\<close>
    \<open>\<And> i. i<lo \<Longrightarrow> xs'!i=xs!i\<close> \<open>\<And> i. \<lbrakk>hi<i; i<length xs'\<rbrakk> \<Longrightarrow> xs'!i=xs!i\<close>
    using part by (auto simp add: partition_spec_def)
  show ?thesis
    unfolding quicksort_pre_def
  proof (intro conjI)
    show \<open>Suc p \<le> hi\<close>
      using ifs by linarith
    show \<open>hi < length xs'\<close>
      by (metis part(1) pre(2) size_mset)
    show \<open>mset xs' = mset xs0\<close>
      using pre(3) part(1) by (auto dest: mset_eq_setD)
  qed
qed



lemma quicksort_post_set:
  assumes \<open>quicksort_post R h lo hi xs xs'\<close>
    and bounds: \<open>lo \<le> hi\<close> \<open>hi < length xs\<close>
  shows \<open>set (sublist xs' lo hi) = set (sublist xs lo hi)\<close>
proof -
  have \<open>mset xs' = mset xs\<close> \<open>\<And> i. i<lo \<Longrightarrow> xs'!i = xs!i\<close> \<open>\<And> j. \<lbrakk>hi<j; j<length xs\<rbrakk> \<Longrightarrow> xs'!j = xs!j\<close>
    using assms by (auto simp add: quicksort_post_def)
  then show ?thesis
    using bounds by (rule mset_sublist_eq, auto)
qed


text \<open>In the third case, we have run quicksort recursively on (p+1, hi, xs') after the partition, with hi<=p+1 and p-1<=lo.\<close>
lemma quicksort_correct_case3:
  assumes trans: \<open>\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and lin: \<open>\<And>x y. x \<noteq> y \<Longrightarrow> R (h x) (h y) \<or> R (h y) (h x)\<close>
    and pre: \<open>quicksort_pre R h xs0 lo hi xs\<close>
    and part: \<open>partition_spec R h xs lo hi xs' p\<close>
    and ifs: \<open>p - Suc 0 \<le> lo\<close> \<open>\<not> hi \<le> Suc p\<close>
    and IH1': \<open>quicksort_post R h (Suc p) hi xs' xs''\<close>
  shows \<open>quicksort_post R h lo hi xs xs''\<close>
proof -
  text \<open>First boilerplate code step: 'unfold' the HOL definitions in the assumptions and convert them to Pure\<close>
  have pre: \<open>lo \<le> hi\<close> \<open>hi < length xs\<close> \<open>mset xs = mset xs0\<close>
    using pre by (auto simp add: quicksort_pre_def)
  have part: \<open>mset xs' = mset xs\<close> True
    \<open>isPartition_map R h xs' lo hi p\<close> \<open>lo \<le> p\<close> \<open>p \<le> hi\<close>
    \<open>\<And> i. i<lo \<Longrightarrow> xs'!i=xs!i\<close> \<open>\<And> i. \<lbrakk>hi<i; i<length xs'\<rbrakk> \<Longrightarrow> xs'!i=xs!i\<close>
    using part by (auto simp add: partition_spec_def)
  have IH1: \<open>mset xs'' = mset xs'\<close> \<open>sorted_sublist_map R h xs'' (Suc p) hi\<close>
      \<open>\<And> i. i<Suc p \<Longrightarrow> xs'' ! i = xs' ! i\<close> \<open>\<And> j. \<lbrakk>hi < j; j < length xs'\<rbrakk> \<Longrightarrow> xs'' ! j = xs' ! j\<close>
    using IH1' by (auto simp add: quicksort_post_def)
  note IH1_perm = quicksort_post_set[OF IH1']

  have still_partition: \<open>isPartition_map R h xs'' lo hi p\<close>
  proof(intro isPartition_wrtI)
    fix i assume \<open>lo \<le> i\<close> \<open>i < p\<close>
    show \<open>R (h (xs'' ! i)) (h (xs'' ! p))\<close>
      text \<open>This holds because this part hasn't changed\<close>
      using IH1(3) \<open>i < p\<close> \<open>lo \<le> i\<close> isPartition_wrt_def part(3) by fastforce
    next
      fix j assume \<open>p < j\<close> \<open>j \<le> hi\<close>
      text \<open>Obtain the position \<^term>\<open>posJ\<close> where \<^term>\<open>xs''!j\<close> was stored in \<^term>\<open>xs'\<close>.\<close>
      have \<open>xs''!j \<in> set (sublist xs'' (Suc p) hi)\<close>
        by (metis IH1(1) Suc_leI \<open>j \<le> hi\<close> \<open>p < j\<close> less_le_trans mset_eq_length part(1) pre(2) sublist_el')
      then have \<open>xs''!j \<in> set (sublist xs' (Suc p) hi)\<close>
        by (metis IH1_perm ifs(2) nat_le_linear part(1) pre(2) size_mset)
      then have \<open>\<exists> posJ. Suc p\<le>posJ\<and>posJ\<le>hi \<and> xs''!j = xs'!posJ\<close>
        by (metis Suc_leI \<open>j \<le> hi\<close> \<open>p < j\<close> less_le_trans part(1) pre(2) size_mset sublist_el')
      then obtain posJ :: nat where PosJ: \<open>Suc p\<le>posJ\<close> \<open>posJ\<le>hi\<close> \<open>xs''!j = xs'!posJ\<close> by blast

      then show \<open>R (h (xs'' ! p)) (h (xs'' ! j))\<close>
        by (metis IH1(3) Suc_le_lessD isPartition_wrt_def lessI part(3))
  qed

  have sorted_lower: \<open>sorted_sublist_map R h xs'' lo (p - Suc 0)\<close>
  proof -
    show ?thesis
      apply (rule sorted_sublist_wrt_le)
      subgoal by (simp add: ifs(1))
      subgoal using IH1(1) mset_eq_length part(1) part(5) pre(2) by fastforce
      done
  qed

  note sorted_upper = IH1(2)

  have sorted_middle: \<open>sorted_sublist_map R h xs'' lo hi\<close>
  proof -
    show ?thesis
      apply (rule merge_sorted_map_partitions[where p=p])
      subgoal by (rule trans)
      subgoal by (rule still_partition)
      subgoal by (rule sorted_lower)
      subgoal by (rule sorted_upper)
      subgoal using pre(1) by auto
      subgoal by (simp add: part(4))
      subgoal by (simp add: part(5))
      subgoal by (metis IH1(1) part(1) pre(2) size_mset)
      done
  qed


  show ?thesis
  proof (intro quicksort_postI)
    show \<open>mset xs'' = mset xs\<close>
      using part(1) IH1(1) by auto \<comment> \<open>I was faster than sledgehammer :-)\<close>
  next
    show \<open>sorted_sublist_map R h xs'' lo hi\<close>
      by (rule sorted_middle)
  next
    show \<open>\<And>i. i < lo \<Longrightarrow> xs'' ! i = xs ! i\<close>
      using IH1(3) le_SucI part(4) part(6) by auto
  next show \<open>\<And>j. hi < j \<Longrightarrow> j < length xs \<Longrightarrow> xs'' ! j = xs ! j\<close>
      by (metis IH1(4) part(1) part(7) size_mset)
  qed
qed


text \<open>In the 4th case, we have to show that the premise holds for \<^term>\<open>(lo,p-1,xs')\<close>, in case \<^term>\<open>\<not>p-1\<le>lo\<close>\<close>
text \<open>Analogous to case 2.\<close>
lemma quicksort_correct_case4:
  assumes
        pre: \<open>quicksort_pre R h xs0 lo hi xs\<close>
    and part: \<open>partition_spec R h xs lo hi xs' p\<close>
    and ifs: \<open>\<not> p - Suc 0 \<le> lo \<close>
  shows \<open>quicksort_pre R h xs0 lo (p-Suc 0) xs'\<close>
proof -
  text \<open>First boilerplate code step: 'unfold' the HOL definitions in the assumptions and convert them to Pure\<close>
  have pre: \<open>lo \<le> hi\<close> \<open>hi < length xs\<close> \<open>mset xs0 = mset xs\<close>
    using pre by (auto simp add: quicksort_pre_def)
  have part: \<open>mset xs' = mset xs\<close> True
    \<open>isPartition_map R h xs' lo hi p\<close> \<open>lo \<le> p\<close> \<open>p \<le> hi\<close>
    \<open>\<And> i. i<lo \<Longrightarrow> xs'!i=xs!i\<close> \<open>\<And> i. \<lbrakk>hi<i; i<length xs'\<rbrakk> \<Longrightarrow> xs'!i=xs!i\<close>
    using part by (auto simp add: partition_spec_def)

  show ?thesis
    unfolding quicksort_pre_def
  proof (intro conjI)
    show \<open>lo \<le> p - Suc 0\<close>
      using ifs by linarith
    show \<open>p - Suc 0 < length xs'\<close>
      using mset_eq_length part(1) part(5) pre(2) by fastforce
    show \<open>mset xs' = mset xs0\<close>
      using pre(3) part(1) by (auto dest: mset_eq_setD)
  qed
qed


text \<open>In the 5th case, we have run quicksort recursively on (lo, p-1, xs').\<close>
lemma quicksort_correct_case5:
  assumes trans: \<open>\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and lin: \<open>\<And>x y. x \<noteq> y \<Longrightarrow> R (h x) (h y) \<or> R (h y) (h x)\<close>
    and pre: \<open>quicksort_pre R h xs0 lo hi xs\<close>
    and part: \<open>partition_spec R h xs lo hi xs' p\<close>
    and ifs:  \<open>\<not> p - Suc 0 \<le> lo\<close> \<open>hi \<le> Suc p\<close>
    and IH1': \<open>quicksort_post R h lo (p - Suc 0) xs' xs''\<close>
  shows \<open>quicksort_post R h lo hi xs xs''\<close>
proof -
  text \<open>First boilerplate code step: 'unfold' the HOL definitions in the assumptions and convert them to Pure\<close>
  have pre: \<open>lo \<le> hi\<close> \<open>hi < length xs\<close>
    using pre by (auto simp add: quicksort_pre_def)
  have part: \<open>mset xs' = mset xs\<close> True
    \<open>isPartition_map R h xs' lo hi p\<close> \<open>lo \<le> p\<close> \<open>p \<le> hi\<close>
    \<open>\<And> i. i<lo \<Longrightarrow> xs'!i=xs!i\<close> \<open>\<And> i. \<lbrakk>hi<i; i<length xs'\<rbrakk> \<Longrightarrow> xs'!i=xs!i\<close>
    using part by (auto simp add: partition_spec_def)
  have IH1: \<open>mset xs'' = mset xs'\<close> \<open>sorted_sublist_map R h xs'' lo (p - Suc 0)\<close>
    \<open>\<And> i. i<lo \<Longrightarrow> xs''!i = xs'!i\<close> \<open>\<And> j. \<lbrakk>p-Suc 0<j; j<length xs'\<rbrakk> \<Longrightarrow> xs''!j = xs'!j\<close>
    using IH1' by (auto simp add: quicksort_post_def)
  note IH1_perm = quicksort_post_set[OF IH1']


 have still_partition: \<open>isPartition_map R h xs'' lo hi p\<close>
  proof(intro isPartition_wrtI)
    fix i assume \<open>lo \<le> i\<close> \<open>i < p\<close>
      text \<open>Obtain the position \<^term>\<open>posI\<close> where \<^term>\<open>xs''!i\<close> was stored in \<^term>\<open>xs'\<close>.\<close>
      have \<open>xs''!i \<in> set (sublist xs'' lo (p-Suc 0))\<close>
        by (metis (no_types, lifting) IH1(1) Suc_leI Suc_pred \<open>i < p\<close> \<open>lo \<le> i\<close> le_less_trans less_imp_diff_less mset_eq_length not_le not_less_zero part(1) part(5) pre(2) sublist_el')
      then have \<open>xs''!i \<in> set (sublist xs' lo (p-Suc 0))\<close>
        by (metis IH1_perm ifs(1) le_less_trans less_imp_diff_less mset_eq_length nat_le_linear part(1) part(5) pre(2))
      then have \<open>\<exists> posI. lo\<le>posI\<and>posI\<le>p-Suc 0 \<and> xs''!i = xs'!posI\<close>
      proof - \<comment> \<open>sledgehammer\<close>
        have "p - Suc 0 < length xs"
          by (meson diff_le_self le_less_trans part(5) pre(2))
        then show ?thesis
          by (metis (no_types) \<open>xs'' ! i \<in> set (sublist xs' lo (p - Suc 0))\<close> ifs(1) mset_eq_length nat_le_linear part(1) sublist_el')
      qed
      then obtain posI :: nat where PosI: \<open>lo\<le>posI\<close> \<open>posI\<le>p-Suc 0\<close> \<open>xs''!i = xs'!posI\<close> by blast
      then show \<open>R (h (xs'' ! i)) (h (xs'' ! p))\<close>
        by (metis (no_types, lifting) IH1(4) \<open>i < p\<close> diff_Suc_less isPartition_wrt_def le_less_trans mset_eq_length not_le not_less_eq part(1) part(3) part(5) pre(2) zero_less_Suc)
    next
      fix j assume \<open>p < j\<close> \<open>j \<le> hi\<close>
      then show \<open>R (h (xs'' ! p)) (h (xs'' ! j))\<close>
      text \<open>This holds because this part hasn't changed\<close>
      by (smt IH1(4) add_diff_cancel_left' add_diff_inverse_nat diff_Suc_eq_diff_pred diff_le_self ifs(1) isPartition_wrt_def le_less_Suc_eq less_le_trans mset_eq_length nat_less_le part(1) part(3) part(4) plus_1_eq_Suc pre(2))
  qed


  note sorted_lower = IH1(2)

  have sorted_upper: \<open>sorted_sublist_map R h xs'' (Suc p) hi\<close>
  proof -
    show ?thesis
      apply (rule sorted_sublist_wrt_le)
      subgoal by (simp add: ifs(2))
      subgoal using IH1(1) mset_eq_length part(1) part(5) pre(2) by fastforce
      done
  qed


  have sorted_middle: \<open>sorted_sublist_map R h xs'' lo hi\<close>
  proof -
    show ?thesis
      apply (rule merge_sorted_map_partitions[where p=p])
      subgoal by (rule trans)
      subgoal by (rule still_partition)
      subgoal by (rule sorted_lower)
      subgoal by (rule sorted_upper)
      subgoal using pre(1) by auto
      subgoal by (simp add: part(4))
      subgoal by (simp add: part(5))
      subgoal by (metis IH1(1) part(1) pre(2) size_mset)
      done
  qed


  show ?thesis
  proof (intro quicksort_postI)
    show \<open>mset xs'' = mset xs\<close>
      by (simp add: IH1(1) part(1))
  next
    show \<open>sorted_sublist_map R h xs'' lo hi\<close>
      by (rule sorted_middle)
  next
    show \<open>\<And>i. i < lo \<Longrightarrow> xs'' ! i = xs ! i\<close>
      by (simp add: IH1(3) part(6))
  next
    show \<open>\<And>j. hi < j \<Longrightarrow> j < length xs \<Longrightarrow> xs'' ! j = xs ! j\<close>
      by (metis IH1(4) diff_le_self dual_order.strict_trans2 mset_eq_length part(1) part(5) part(7))
  qed
qed


text \<open>In the 6th case, we have run quicksort recursively on (lo, p-1, xs'). We show the precondition on the second call on (p+1, hi, xs'')\<close>
lemma quicksort_correct_case6:
  assumes
        pre: \<open>quicksort_pre R h xs0 lo hi xs\<close>
    and part: \<open>partition_spec R h xs lo hi xs' p\<close>
    and ifs:  \<open>\<not> p - Suc 0 \<le> lo\<close> \<open>\<not> hi \<le> Suc p\<close>
    and IH1: \<open>quicksort_post R h lo (p - Suc 0) xs' xs''\<close>
  shows \<open>quicksort_pre R h xs0 (Suc p) hi xs''\<close>
proof -
  text \<open>First boilerplate code step: 'unfold' the HOL definitions in the assumptions and convert them to Pure\<close>
  have pre: \<open>lo \<le> hi\<close> \<open>hi < length xs\<close> \<open>mset xs0 = mset xs\<close>
    using pre by (auto simp add: quicksort_pre_def)
  have part: \<open>mset xs' = mset xs\<close> True
    \<open>isPartition_map R h xs' lo hi p\<close> \<open>lo \<le> p\<close> \<open>p \<le> hi\<close>
    \<open>\<And> i. i<lo \<Longrightarrow> xs'!i=xs!i\<close> \<open>\<And> i. \<lbrakk>hi<i; i<length xs'\<rbrakk> \<Longrightarrow> xs'!i=xs!i\<close>
    using part by (auto simp add: partition_spec_def)
  have IH1: \<open>mset xs'' = mset xs'\<close> \<open>sorted_sublist_map R h xs'' lo (p - Suc 0)\<close>
    \<open>\<And> i. i<lo \<Longrightarrow> xs''!i = xs'!i\<close> \<open>\<And> j. \<lbrakk>p-Suc 0<j; j<length xs'\<rbrakk> \<Longrightarrow> xs''!j = xs'!j\<close>
    using IH1 by (auto simp add: quicksort_post_def)

  show ?thesis
    unfolding quicksort_pre_def
  proof (intro conjI)
    show \<open>Suc p \<le> hi\<close>
      using ifs(2) by linarith
    show \<open>hi < length xs''\<close>
      using IH1(1) mset_eq_length part(1) pre(2) by fastforce
    show \<open>mset xs'' = mset xs0\<close>
      using pre(3) part(1) IH1(1) by (auto dest: mset_eq_setD)
  qed
qed


text \<open>In the 7th (and last) case, we have run quicksort recursively on (lo, p-1, xs'). We show the postcondition on the second call on (p+1, hi, xs'')\<close>
lemma quicksort_correct_case7:
  assumes trans: \<open>\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and lin: \<open>\<And>x y. x \<noteq> y \<Longrightarrow> R (h x) (h y) \<or> R (h y) (h x)\<close>
    and pre: \<open>quicksort_pre R h xs0 lo hi xs\<close>
    and part: \<open>partition_spec R h xs lo hi xs' p\<close>
    and ifs:  \<open>\<not> p - Suc 0 \<le> lo\<close> \<open>\<not> hi \<le> Suc p\<close>
    and IH1': \<open>quicksort_post R h lo (p - Suc 0) xs' xs''\<close>
    and IH2': \<open>quicksort_post R h (Suc p) hi xs'' xs'''\<close>
  shows \<open>quicksort_post R h lo hi xs xs'''\<close>
proof -
  text \<open>First boilerplate code step: 'unfold' the HOL definitions in the assumptions and convert them to Pure\<close>
  have pre: \<open>lo \<le> hi\<close> \<open>hi < length xs\<close>
    using pre by (auto simp add: quicksort_pre_def)
  have part: \<open>mset xs' = mset xs\<close> True
    \<open>isPartition_map R h xs' lo hi p\<close> \<open>lo \<le> p\<close> \<open>p \<le> hi\<close>
    \<open>\<And> i. i<lo \<Longrightarrow> xs'!i=xs!i\<close> \<open>\<And> i. \<lbrakk>hi<i; i<length xs'\<rbrakk> \<Longrightarrow> xs'!i=xs!i\<close>
    using part by (auto simp add: partition_spec_def)
  have IH1: \<open>mset xs'' = mset xs'\<close> \<open>sorted_sublist_map R h xs'' lo (p - Suc 0)\<close>
    \<open>\<And> i. i<lo \<Longrightarrow> xs''!i = xs'!i\<close> \<open>\<And> j. \<lbrakk>p-Suc 0<j; j<length xs'\<rbrakk> \<Longrightarrow> xs''!j = xs'!j\<close>
    using IH1' by (auto simp add: quicksort_post_def)
  note IH1_perm = quicksort_post_set[OF IH1']
  have IH2: \<open>mset xs''' = mset xs''\<close> \<open>sorted_sublist_map R h xs''' (Suc p) hi\<close>
    \<open>\<And> i. i<Suc p \<Longrightarrow> xs'''!i = xs''!i\<close> \<open>\<And> j. \<lbrakk>hi<j; j<length xs''\<rbrakk> \<Longrightarrow> xs'''!j = xs''!j\<close>
    using IH2' by (auto simp add: quicksort_post_def)
  note IH2_perm = quicksort_post_set[OF IH2']


  text \<open>We still have a partition after the first call (same as in case 5)\<close>
  have still_partition1: \<open>isPartition_map R h xs'' lo hi p\<close>
  proof(intro isPartition_wrtI)
    fix i assume \<open>lo \<le> i\<close> \<open>i < p\<close>
      text \<open>Obtain the position \<^term>\<open>posI\<close> where \<^term>\<open>xs''!i\<close> was stored in \<^term>\<open>xs'\<close>.\<close>
      have \<open>xs''!i \<in> set (sublist xs'' lo (p-Suc 0))\<close>
        by (metis (no_types, lifting) IH1(1) Suc_leI Suc_pred \<open>i < p\<close> \<open>lo \<le> i\<close> le_less_trans less_imp_diff_less mset_eq_length not_le not_less_zero part(1) part(5) pre(2) sublist_el')
      then have \<open>xs''!i \<in> set (sublist xs' lo (p-Suc 0))\<close>
        by (metis IH1_perm ifs(1) le_less_trans less_imp_diff_less mset_eq_length nat_le_linear part(1) part(5) pre(2))
      then have \<open>\<exists> posI. lo\<le>posI\<and>posI\<le>p-Suc 0 \<and> xs''!i = xs'!posI\<close>
      proof - \<comment> \<open>sledgehammer\<close>
        have "p - Suc 0 < length xs"
          by (meson diff_le_self le_less_trans part(5) pre(2))
        then show ?thesis
          by (metis (no_types) \<open>xs'' ! i \<in> set (sublist xs' lo (p - Suc 0))\<close> ifs(1) mset_eq_length nat_le_linear part(1) sublist_el')
      qed
      then obtain posI :: nat where PosI: \<open>lo\<le>posI\<close> \<open>posI\<le>p-Suc 0\<close> \<open>xs''!i = xs'!posI\<close> by blast
      then show \<open>R (h (xs'' ! i)) (h (xs'' ! p))\<close>
        by (metis (no_types, lifting) IH1(4) \<open>i < p\<close> diff_Suc_less isPartition_wrt_def le_less_trans mset_eq_length not_le not_less_eq part(1) part(3) part(5) pre(2) zero_less_Suc)
    next
      fix j assume \<open>p < j\<close> \<open>j \<le> hi\<close>
      then show \<open>R (h (xs'' ! p)) (h (xs'' ! j))\<close>
      text \<open>This holds because this part hasn't changed\<close>
      by (smt IH1(4) add_diff_cancel_left' add_diff_inverse_nat diff_Suc_eq_diff_pred diff_le_self ifs(1) isPartition_wrt_def le_less_Suc_eq less_le_trans mset_eq_length nat_less_le part(1) part(3) part(4) plus_1_eq_Suc pre(2))
  qed


  text \<open>We still have a partition after the second call (similar as in case 3)\<close>
  have still_partition2: \<open>isPartition_map R h xs''' lo hi p\<close>
  proof(intro isPartition_wrtI)
    fix i assume \<open>lo \<le> i\<close> \<open>i < p\<close>
    show \<open>R (h (xs''' ! i)) (h (xs''' ! p))\<close>
      text \<open>This holds because this part hasn't changed\<close>
      using IH2(3) \<open>i < p\<close> \<open>lo \<le> i\<close> isPartition_wrt_def still_partition1 by fastforce
    next
      fix j assume \<open>p < j\<close> \<open>j \<le> hi\<close>
      text \<open>Obtain the position \<^term>\<open>posJ\<close> where \<^term>\<open>xs'''!j\<close> was stored in \<^term>\<open>xs'''\<close>.\<close>
      have \<open>xs'''!j \<in> set (sublist xs''' (Suc p) hi)\<close>
        by (metis IH1(1) IH2(1) Suc_leI \<open>j \<le> hi\<close> \<open>p < j\<close> ifs(2) nat_le_linear part(1) pre(2) size_mset sublist_el')
      then have \<open>xs'''!j \<in> set (sublist xs'' (Suc p) hi)\<close>
        by (metis IH1(1) IH2_perm ifs(2) mset_eq_length nat_le_linear part(1) pre(2))
      then have \<open>\<exists> posJ. Suc p\<le>posJ\<and>posJ\<le>hi \<and> xs'''!j = xs''!posJ\<close>
        by (metis IH1(1) ifs(2) mset_eq_length nat_le_linear part(1) pre(2) sublist_el')
      then obtain posJ :: nat where PosJ: \<open>Suc p\<le>posJ\<close> \<open>posJ\<le>hi\<close> \<open>xs'''!j = xs''!posJ\<close> by blast

      then show \<open>R (h (xs''' ! p)) (h (xs''' ! j))\<close>
      proof - \<comment> \<open>sledgehammer\<close>
        have "\<forall>n na as p. (p (as ! na::'a) (as ! posJ) \<or> posJ \<le> na) \<or> \<not> isPartition_wrt p as n hi na"
          by (metis (no_types) PosJ(2) isPartition_wrt_def not_less)
        then show ?thesis
          by (metis IH2(3) PosJ(1) PosJ(3) lessI not_less_eq_eq still_partition1)
      qed
  qed


  text \<open>We have that the lower part is sorted after the first recursive call\<close>
  note sorted_lower1 = IH1(2)

  text \<open>We show that it is still sorted after the second call.\<close>
  have sorted_lower2: \<open>sorted_sublist_map R h xs''' lo (p-Suc 0)\<close>
  proof -
    show ?thesis
      using sorted_lower1 apply (rule sorted_wrt_lower_sublist_still_sorted)
      subgoal by (rule part)
      subgoal
        using IH1(1) mset_eq_length part(1) part(5) pre(2) by fastforce
      subgoal
        by (simp add: IH2(3))
      subgoal
        by (metis IH2(1) size_mset)
      done
  qed

  text \<open>The second IH gives us the the upper list is sorted after the second recursive call\<close>
  note sorted_upper2 = IH2(2)

  text \<open>Finally, we have to show that the entire list is sorted after the second recursive call.\<close>
  have sorted_middle: \<open>sorted_sublist_map R h xs''' lo hi\<close>
  proof -
    show ?thesis
      apply (rule merge_sorted_map_partitions[where p=p])
      subgoal by (rule trans)
      subgoal by (rule still_partition2)
      subgoal by (rule sorted_lower2)
      subgoal by (rule sorted_upper2)
      subgoal using pre(1) by auto
      subgoal by (simp add: part(4))
      subgoal by (simp add: part(5))
      subgoal by (metis IH1(1) IH2(1) part(1) pre(2) size_mset)
      done
  qed

  show ?thesis
  proof (intro quicksort_postI)
    show \<open>mset xs''' = mset xs\<close>
      by (simp add: IH1(1) IH2(1) part(1))
  next
    show \<open>sorted_sublist_map R h xs''' lo hi\<close>
      by (rule sorted_middle)
  next
    show \<open>\<And>i. i < lo \<Longrightarrow> xs''' ! i = xs ! i\<close>
      using IH1(3) IH2(3) part(4) part(6) by auto
  next
    show \<open>\<And>j. hi < j \<Longrightarrow> j < length xs \<Longrightarrow> xs''' ! j = xs ! j\<close>
      by (metis IH1(1) IH1(4) IH2(4) diff_le_self ifs(2) le_SucI less_le_trans nat_le_eq_or_lt not_less part(1) part(7) size_mset)
  qed

qed



text \<open>We can now show the correctness of the abstract quicksort procedure, using the refinement framework and the above case lemmas.\<close>
lemma quicksort_correct:
  assumes trans: \<open>\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and lin: \<open>\<And>x y. x \<noteq> y \<Longrightarrow> R (h x) (h y) \<or> R (h y) (h x)\<close>
     and Pre: \<open>lo0 \<le> hi0\<close> \<open>hi0 < length xs0\<close>
  shows \<open>quicksort R h (lo0,hi0,xs0) \<le> \<Down> Id (SPEC(\<lambda>xs. quicksort_post R h lo0 hi0 xs0 xs))\<close>
proof -
  have wf: \<open>wf (measure (\<lambda>(lo, hi, xs). Suc hi - lo))\<close>
    by auto
  define pre where \<open>pre = (\<lambda>(lo,hi,xs). quicksort_pre R h xs0 lo hi xs)\<close>
  define post where \<open>post = (\<lambda>(lo,hi,xs). quicksort_post R h lo hi xs)\<close>
  have pre: \<open>pre (lo0,hi0,xs0)\<close>
    unfolding quicksort_pre_def pre_def by (simp add: Pre)

  text \<open>We first generalize the goal a over all states.\<close>
  have \<open>WB_Sort.quicksort R h (lo0,hi0,xs0) \<le> \<Down> Id (SPEC (post (lo0,hi0,xs0)))\<close>
    unfolding quicksort_def prod.case
    apply (rule RECT_rule)
       apply (refine_mono)
      apply (rule wf)
    apply (rule pre)
    subgoal premises IH for f x
      apply (refine_vcg ASSERT_leI)
      unfolding pre_def post_def

      subgoal \<comment> \<open>First premise (assertion) for partition\<close>
        using IH(2) by (simp add: quicksort_pre_def pre_def)
      subgoal \<comment> \<open>Second premise (assertion) for partition\<close>
        using IH(2) by (simp add: quicksort_pre_def pre_def)
      subgoal
        using IH(2) by (auto simp add: quicksort_pre_def pre_def dest: mset_eq_setD)

	text \<open>Termination case: \<^term>\<open>(p-1 \<le> lo')\<close> and \<^term>\<open>(hi' \<le> p+1)\<close>; directly show postcondition\<close>
      subgoal unfolding partition_spec_def by (auto dest: mset_eq_setD)
      subgoal \<comment> \<open>Postcondition (after partition)\<close>
        apply -
        using IH(2) unfolding pre_def apply (simp, elim conjE, split prod.splits)
        using trans lin apply (rule quicksort_correct_case1) by auto

      text \<open>Case \<^term>\<open>(p-1 \<le> lo')\<close> and \<^term>\<open>(hi' < p+1)\<close> (Only second recursive call)\<close>
      subgoal
        apply (rule IH(1)[THEN order_trans])

        text \<open>Show that the invariant holds for the second recursive call\<close>
        subgoal
          using IH(2) unfolding pre_def apply (simp, elim conjE, split prod.splits)
          apply (rule quicksort_correct_case2) by auto

        text \<open>Wellfoundness (easy)\<close>
        subgoal by (auto simp add: quicksort_pre_def partition_spec_def)

        text \<open>Show that the postcondition holds\<close>
        subgoal
          apply (simp add: Misc.subset_Collect_conv post_def, intro allI impI, elim conjE)
          using trans lin apply (rule quicksort_correct_case3)
          using IH(2) unfolding pre_def by auto
        done

      text \<open>Case: At least the first recursive call\<close>
      subgoal
        apply (rule IH(1)[THEN order_trans])

        text \<open>Show that the precondition holds for the first recursive call\<close>
        subgoal
          using IH(2) unfolding pre_def post_def apply (simp, elim conjE, split prod.splits) apply auto
          apply (rule quicksort_correct_case4) by auto

        text \<open>Wellfoundness for first recursive call (easy)\<close>
        subgoal by (auto simp add: quicksort_pre_def partition_spec_def)

        text \<open>Simplify some refinement suff...\<close>
        apply (simp add: Misc.subset_Collect_conv ASSERT_leI, intro allI impI conjI, elim conjE)
        apply (rule ASSERT_leI)
        apply (simp_all add: Misc.subset_Collect_conv ASSERT_leI)
        subgoal unfolding quicksort_post_def pre_def post_def by (auto dest: mset_eq_setD)
        text \<open>Only the first recursive call: show postcondition\<close>
        subgoal
          using trans lin apply (rule quicksort_correct_case5)
          using IH(2) unfolding pre_def post_def by auto

        apply (rule ASSERT_leI)
        subgoal unfolding quicksort_post_def pre_def post_def by (auto dest: mset_eq_setD)

        text \<open>Both recursive calls.\<close>
        subgoal
          apply (rule IH(1)[THEN order_trans])

          text \<open>Show precondition for second recursive call (after the first call)\<close>
          subgoal
            unfolding pre_def post_def
            apply auto
            apply (rule quicksort_correct_case6)
            using IH(2) unfolding pre_def post_def  by auto

          text \<open>Wellfoundedness for second recursive call (easy)\<close>
          subgoal by (auto simp add: quicksort_pre_def partition_spec_def)

          text \<open>Show that the postcondition holds (after both recursive calls)\<close>
          subgoal
            apply (simp add: Misc.subset_Collect_conv, intro allI impI, elim conjE)
            using trans lin apply (rule quicksort_correct_case7)
            using IH(2) unfolding pre_def post_def by auto
          done
        done
      done
    done

  text \<open>Finally, apply the generalized lemma to show the thesis.\<close>
  then show ?thesis unfolding post_def  by auto
qed



(* TODO: Show that our (abstract) partition satisifies the specification *)


definition partition_main_inv :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> (nat\<times>nat\<times>'a list) \<Rightarrow> bool\<close> where
  \<open>partition_main_inv R h lo hi xs0 p \<equiv>
    case p of (i,j,xs) \<Rightarrow>
    j < length xs \<and> j \<le> hi \<and> i < length xs \<and> lo \<le> i \<and> i \<le> j \<and> mset xs = mset xs0 \<and>
    (\<forall>k. k \<ge> lo \<and> k < i \<longrightarrow> R (h (xs!k)) (h (xs!hi))) \<and> \<comment> \<open>All elements from \<^term>\<open>lo\<close> to \<^term>\<open>i-1\<close> are smaller than the pivot\<close>
    (\<forall>k. k \<ge> i \<and> k < j \<longrightarrow>  R (h (xs!hi)) (h (xs!k))) \<and> \<comment> \<open>All elements from \<^term>\<open>i\<close> to \<^term>\<open>j-1\<close> are greater than the pivot\<close>
    (\<forall>k. k < lo \<longrightarrow> xs!k = xs0!k) \<and> \<comment> \<open>Everything below \<^term>\<open>lo\<close> is unchanged\<close>
    (\<forall>k. k \<ge> j \<and> k < length xs \<longrightarrow> xs!k = xs0!k) \<comment> \<open>All elements from \<^term>\<open>j\<close> are unchanged (including everyting above \<^term>\<open>hi\<close>)\<close>
  \<close>

text \<open>The main part of the partition function. The pivot is assumed to be the last element. This is
exactly the "Lomuto partition scheme" partition function from Wikipedia.\<close>
definition partition_main :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) nres\<close> where
  \<open>partition_main R h lo hi xs0 = do {
    ASSERT(hi < length xs0);
    pivot \<leftarrow> RETURN (h (xs0 ! hi));
    (i,j,xs) \<leftarrow> WHILE\<^sub>T\<^bsup>partition_main_inv R h lo hi xs0\<^esup> \<comment> \<open>We loop from \<^term>\<open>j=lo\<close> to \<^term>\<open>j=hi-1\<close>.\<close>
      (\<lambda>(i,j,xs). j < hi)
      (\<lambda>(i,j,xs). do {
        ASSERT(i < length xs \<and> j < length xs);
      	if R (h (xs!j)) pivot
      	then RETURN (i+1, j+1, swap xs i j)
      	else RETURN (i,   j+1, xs)
      })
      (lo, lo, xs0); \<comment> \<open>i and j are both initialized to lo\<close>
    ASSERT(i < length xs \<and> j = hi \<and> lo \<le> i \<and> hi < length xs \<and> mset xs = mset xs0);
    RETURN (swap xs i hi, i)
  }\<close>

(*
definition partition_spec :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>partition_spec R h xs lo hi xs' p \<equiv>
    mset xs' = mset xs \<and> \<comment> \<open>The list is a permutation\<close>
    isPartition_map R h xs' lo hi p \<and> \<comment> \<open>We have a valid partition on the resulting list\<close>
    lo \<le> p \<and> p \<le> hi \<and> \<comment> \<open>The partition index is in bounds\<close>
    (\<forall> i. i<lo \<longrightarrow> xs'!i=xs!i) \<and> (\<forall> i. hi<i\<and>i<length xs' \<longrightarrow> xs'!i=xs!i)\<close> \<comment> \<open>Everything else is unchanged.\<close>
*)

lemma partition_main_correct:
  assumes bounds: \<open>hi < length xs\<close> \<open>lo \<le> hi\<close> and
    trans: \<open>\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and lin: \<open>\<And>x y. R (h x) (h y) \<or> R (h y) (h x)\<close>
  shows \<open>partition_main R h lo hi xs \<le> SPEC(\<lambda>(xs', p). mset xs = mset xs' \<and>
     lo \<le> p \<and> p \<le> hi \<and> isPartition_map R h xs' lo hi p \<and> (\<forall> i. i<lo \<longrightarrow> xs'!i=xs!i) \<and> (\<forall> i. hi<i\<and>i<length xs' \<longrightarrow> xs'!i=xs!i))\<close>
proof -
  have K: \<open>b \<le> hi - Suc n \<Longrightarrow> n > 0 \<Longrightarrow> Suc n \<le> hi \<Longrightarrow> Suc b \<le> hi - n\<close> for b hi n
    by auto
  have L: \<open>~ R (h x) (h y) \<Longrightarrow> R (h y) (h x)\<close> for x y \<comment> \<open>Corollary of linearity\<close>
    using assms by blast
  have M: \<open>a < Suc b \<equiv> a = b \<or> a < b\<close> for a b
    by linarith
  have N: \<open>(a::nat) \<le> b \<equiv> a = b \<or> a < b\<close> for a b
    by arith

  show ?thesis
    unfolding partition_main_def choose_pivot_def
    apply (refine_vcg WHILEIT_rule[where R = \<open>measure(\<lambda>(i,j,xs). hi-j)\<close>])
    subgoal using assms by blast \<comment> \<open>We feed our assumption to the assertion\<close>
    subgoal by auto \<comment> \<open>WF\<close>
    subgoal \<comment> \<open>Invariant holds before the first iteration\<close>
      unfolding partition_main_inv_def
      using assms apply simp by linarith
    subgoal unfolding partition_main_inv_def by simp
    subgoal unfolding partition_main_inv_def by simp
    subgoal
      unfolding partition_main_inv_def
      apply (auto dest: mset_eq_length)
      done
    subgoal unfolding partition_main_inv_def by (auto dest: mset_eq_length)
    subgoal
      unfolding partition_main_inv_def apply (auto dest: mset_eq_length)
      by (metis L M mset_eq_length nat_le_eq_or_lt)

    subgoal unfolding partition_main_inv_def by simp \<comment> \<open>assertions, etc\<close>
    subgoal unfolding partition_main_inv_def by simp
    subgoal unfolding partition_main_inv_def by (auto dest: mset_eq_length)
    subgoal unfolding partition_main_inv_def by simp
    subgoal unfolding partition_main_inv_def by (auto dest: mset_eq_length)
    subgoal unfolding partition_main_inv_def by (auto dest: mset_eq_length)
    subgoal unfolding partition_main_inv_def by (auto dest: mset_eq_length)
    subgoal unfolding partition_main_inv_def by simp
    subgoal unfolding partition_main_inv_def by simp

    subgoal \<comment> \<open>After the last iteration, we have a partitioning! :-)\<close>
      unfolding partition_main_inv_def by (auto simp add: isPartition_wrt_def)
    subgoal \<comment> \<open>And the lower out-of-bounds parts of the list haven't been changed\<close>
      unfolding partition_main_inv_def by auto
    subgoal \<comment> \<open>And the upper out-of-bounds parts of the list haven't been changed\<close>
      unfolding partition_main_inv_def by auto
    done
qed


definition partition_between :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) nres\<close> where
  \<open>partition_between R h lo hi xs0 = do {
    ASSERT(hi < length xs0 \<and> lo \<le> hi);
    k \<leftarrow> choose_pivot R h xs0 lo hi; \<comment> \<open>choice of pivot\<close>
    ASSERT(k < length xs0);
    xs \<leftarrow> RETURN (swap xs0 k hi); \<comment> \<open>move the pivot to the last position, before we start the actual loop\<close>
    ASSERT(length xs = length xs0);
    partition_main R h lo hi xs
  }\<close>


lemma partition_between_correct:
  assumes \<open>hi < length xs\<close> and \<open>lo \<le> hi\<close> and
  \<open>\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and \<open>\<And>x y. R (h x) (h y) \<or> R (h y) (h x)\<close>
  shows \<open>partition_between R h lo hi xs \<le> SPEC(uncurry (partition_spec R h xs lo hi))\<close>
proof -
  have K: \<open>b \<le> hi - Suc n \<Longrightarrow> n > 0 \<Longrightarrow> Suc n \<le> hi \<Longrightarrow> Suc b \<le> hi - n\<close> for b hi n
    by auto
  show ?thesis
    unfolding partition_between_def choose_pivot_def
    apply (refine_vcg partition_main_correct)
    using assms apply (auto dest: mset_eq_length simp add: partition_spec_def)
    by (metis dual_order.strict_trans2 less_imp_not_eq2 mset_eq_length swap_nth)
qed



text \<open>We use the median of the first, the middle, and the last element.\<close>
definition choose_pivot3 where
  \<open>choose_pivot3 R h xs lo (hi::nat) = do {
    ASSERT(lo < length xs);
    ASSERT(hi < length xs);
    let k' = (hi - lo) div 2;
    let k = lo + k';
    ASSERT(k < length xs);
    let start = h (xs ! lo);
    let mid = h (xs ! k);
    let end = h (xs ! hi);
    if (R start mid \<and> R mid end) \<or> (R end mid \<and> R mid start) then RETURN k
    else if (R start end \<and> R end mid) \<or> (R mid end \<and> R end start) then RETURN hi
    else RETURN lo
}\<close>

\<comment> \<open>We only have to show that this procedure yields a valid index between \<open>lo\<close> and \<open>hi\<close>.\<close>
lemma choose_pivot3_choose_pivot:
  assumes \<open>lo < length xs\<close> \<open>hi < length xs\<close> \<open>hi \<ge> lo\<close>
  shows \<open>choose_pivot3 R h xs lo hi \<le> \<Down> Id (choose_pivot R h xs lo hi)\<close>
  unfolding choose_pivot3_def choose_pivot_def
  using assms by (auto intro!: ASSERT_leI simp: Let_def)

text \<open>The refined partion function: We use the above pivot function and fold instead of non-deterministic iteration.\<close>
definition partition_between_ref
  :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) nres\<close>
where
  \<open>partition_between_ref R h lo hi xs0 = do {
    ASSERT(hi < length xs0 \<and> hi < length xs0 \<and> lo \<le> hi);
    k \<leftarrow> choose_pivot3 R h xs0 lo hi; \<comment> \<open>choice of pivot\<close>
    ASSERT(k < length xs0);
    xs \<leftarrow> RETURN (swap xs0 k hi); \<comment> \<open>move the pivot to the last position, before we start the actual loop\<close>
    ASSERT(length xs = length xs0);
    partition_main R h lo hi xs
  }\<close>


lemma partition_main_ref':
  \<open>partition_main R h lo hi xs
    \<le> \<Down> ((\<lambda> a b c d. Id) a b c d) (partition_main R h lo hi xs)\<close>
  by auto


(*TODO already exists somewhere*)
lemma Down_id_eq:
  \<open>\<Down>Id x = x\<close>
  by auto

lemma partition_between_ref_partition_between:
  \<open>partition_between_ref R h lo hi xs \<le> (partition_between R h lo hi xs)\<close>
proof -
  have swap: \<open>(swap xs k hi, swap xs ka hi) \<in> Id\<close> if \<open>k = ka\<close>
    for k ka
    using that by auto
  have [refine0]: \<open>(h (xsa ! hi), h (xsaa ! hi)) \<in> Id\<close>
    if \<open>(xsa, xsaa) \<in> Id\<close>
    for xsa xsaa
    using that by auto

  show ?thesis
    apply (subst (2) Down_id_eq[symmetric])
    unfolding partition_between_ref_def
      partition_between_def
      OP_def
    apply (refine_vcg choose_pivot3_choose_pivot swap partition_main_correct)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    by (auto intro: Refine_Basic.Id_refine dest: mset_eq_length)
qed

text \<open>Technical lemma for sepref\<close>

lemma partition_between_ref_partition_between':
  \<open>(uncurry2 (partition_between_ref R h), uncurry2 (partition_between R h)) \<in>
    (nat_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r nat_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
    (auto intro: partition_between_ref_partition_between)

text \<open>Example instantiation for pivot\<close>
definition choose_pivot3_impl where
  \<open>choose_pivot3_impl = choose_pivot3 (\<le>) id\<close>


lemma partition_between_ref_correct:
  assumes trans: \<open>\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and lin: \<open>\<And>x y. R (h x) (h y) \<or> R (h y) (h x)\<close>
    and bounds: \<open>hi < length xs\<close> \<open>lo \<le> hi\<close>
  shows \<open>partition_between_ref R h lo hi xs \<le> SPEC (uncurry (partition_spec R h xs lo hi))\<close>
proof -
  show ?thesis
    apply (rule partition_between_ref_partition_between[THEN order_trans])
    using bounds apply (rule partition_between_correct[where h=h])
    subgoal by (rule trans)
    subgoal by (rule lin)
    done
qed


text \<open>Refined quicksort algorithm: We use the refined partition function.\<close>
definition quicksort_ref :: \<open>_ \<Rightarrow> _ \<Rightarrow> nat \<times> nat \<times> 'a list \<Rightarrow> 'a list nres\<close> where
\<open>quicksort_ref R h = (\<lambda>(lo,hi,xs0).
  do {
  RECT (\<lambda>f (lo,hi,xs). do {
      ASSERT(lo \<le> hi \<and> hi < length xs0 \<and> mset xs = mset xs0);
      (xs, p) \<leftarrow> partition_between_ref R h lo hi xs; \<comment> \<open>This is the refined partition function. Note that we need the premises (trans,lin,bounds) here.\<close>
      ASSERT(mset xs = mset xs0 \<and> p \<ge> lo \<and> p < length xs0);
      xs \<leftarrow> (if p-1\<le>lo then RETURN xs else f (lo, p-1, xs));
      ASSERT(mset xs = mset xs0);
      if hi\<le>p+1 then RETURN xs else f (p+1, hi, xs)
    }) (lo,hi,xs0)
  })\<close>


(*TODO share*)
lemma fref_to_Down_curry2:
  \<open>(uncurry2 f, uncurry2 g) \<in> [P]\<^sub>f A \<rightarrow> \<langle>B\<rangle>nres_rel \<Longrightarrow>
     (\<And>x x' y y' z z'. P ((x', y'), z') \<Longrightarrow> (((x, y), z), ((x', y'), z')) \<in> A\<Longrightarrow>
         f x y z \<le> \<Down> B (g x' y' z'))\<close>
  unfolding fref_def uncurry_def nres_rel_def
  by auto

lemma fref_to_Down_curry:
  \<open>(f, g) \<in> [P]\<^sub>f A \<rightarrow> \<langle>B\<rangle>nres_rel \<Longrightarrow>
     (\<And>x x' . P x' \<Longrightarrow> (x, x') \<in> A\<Longrightarrow>
         f x  \<le> \<Down> B (g x'))\<close>
  unfolding fref_def uncurry_def nres_rel_def
  by auto



lemma quicksort_ref_quicksort:
  assumes bounds: \<open>hi < length xs\<close> \<open>lo \<le> hi\<close> and
    trans: \<open>\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and lin: \<open>\<And>x y. R (h x) (h y) \<or> R (h y) (h x)\<close>
  shows \<open>quicksort_ref R h x0 \<le> \<Down> Id (quicksort R h x0)\<close>
proof -
  have wf: \<open>wf (measure (\<lambda>(lo, hi, xs). Suc hi - lo))\<close>
    by auto
  have pre: \<open>x0 = x0' \<Longrightarrow> (x0, x0') \<in> Id \<times>\<^sub>r Id \<times>\<^sub>r \<langle>Id\<rangle>list_rel\<close> for x0 x0' :: \<open>nat \<times> nat \<times> 'b list\<close>
    by auto
  have [refine0]: \<open>(x1e = x1d) \<Longrightarrow> (x1e,x1d) \<in> Id\<close> for x1e x1d :: \<open>'b list\<close>
    by auto

  show ?thesis
    unfolding quicksort_def quicksort_ref_def
    apply (refine_vcg pre partition_between_ref_partition_between'[THEN fref_to_Down_curry2])

    text \<open>First assertion (premise for partition)\<close>
    subgoal
      by auto
    text \<open>First assertion (premise for partition)\<close>
    subgoal
      by auto
    subgoal
      by (auto dest: mset_eq_length)
    subgoal
      by (auto dest: mset_eq_length mset_eq_setD)

    text \<open>Correctness of the concrete partition function\<close>
    subgoal
      apply (simp, rule partition_between_ref_correct)
      subgoal by (rule trans)
      subgoal by (rule lin)
      subgoal by auto \<comment> \<open>first premise\<close>
      subgoal by auto \<comment> \<open>second premise\<close>
      done
    subgoal
      by (auto dest: mset_eq_length mset_eq_setD)
    subgoal by (auto simp: partition_spec_def isPartition_wrt_def)
    subgoal by (auto simp: partition_spec_def isPartition_wrt_def dest: mset_eq_length)
    subgoal
      by (auto dest: mset_eq_length mset_eq_setD)
    subgoal
      by (auto dest: mset_eq_length mset_eq_setD)
    subgoal
      by (auto dest: mset_eq_length mset_eq_setD)
    subgoal
      by (auto dest: mset_eq_length mset_eq_setD)

    by simp+
qed

\<comment> \<open>Sort the entire list\<close>
definition full_quicksort where
  \<open>full_quicksort R h xs \<equiv> if xs = [] then RETURN xs else quicksort R h (0, length xs - 1, xs)\<close>

definition full_quicksort_ref where
  \<open>full_quicksort_ref R h xs \<equiv>
    if List.null xs then RETURN xs
    else quicksort_ref R h (0, length xs - 1, xs)\<close>

definition full_quicksort_impl :: \<open>nat list \<Rightarrow> nat list nres\<close> where
  \<open>full_quicksort_impl xs = full_quicksort_ref (\<le>) id xs\<close>

lemma full_quicksort_ref_full_quicksort:
  assumes trans: \<open>\<And> x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and lin: \<open>\<And>x y. R (h x) (h y) \<or> R (h y) (h x)\<close>
  shows \<open>(full_quicksort_ref R h, full_quicksort R h) \<in>
          \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle> \<langle>Id\<rangle>list_rel\<rangle>nres_rel\<close>
proof -
  show ?thesis
    unfolding full_quicksort_ref_def full_quicksort_def
    apply (intro frefI nres_relI)
    apply (auto intro!: quicksort_ref_quicksort[unfolded Down_id_eq] simp: List.null_def)
    subgoal by (rule trans)
    subgoal using lin by blast
    done
qed


lemma sublist_entire:
  \<open>sublist xs 0 (length xs - 1) = xs\<close>
  by (simp add: sublist_def)


lemma sorted_sublist_wrt_entire:
  assumes \<open>sorted_sublist_wrt R xs 0 (length xs - 1)\<close>
  shows \<open>sorted_wrt R xs\<close>
proof -
  have \<open>sorted_wrt R (sublist xs 0 (length xs - 1))\<close>
    using assms by (simp add: sorted_sublist_wrt_def )
  then show ?thesis
    by (metis sublist_entire)
qed

lemma sorted_sublist_map_entire:
  assumes \<open>sorted_sublist_map R h xs 0 (length xs - 1)\<close>
  shows \<open>sorted_wrt (\<lambda> x y. R (h x) (h y)) xs\<close>
proof -
  show ?thesis
    using assms by (rule sorted_sublist_wrt_entire)
qed


text \<open>Final correctness lemma\<close>
theorem full_quicksort_correct_sorted:
  assumes
    trans: \<open>\<And>x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and lin: \<open>\<And>x y. x \<noteq> y \<Longrightarrow> R (h x) (h y) \<or> R (h y) (h x)\<close>
  shows \<open>full_quicksort R h xs \<le> \<Down> Id (SPEC(\<lambda>xs'. mset xs' = mset xs \<and> sorted_wrt (\<lambda> x y. R (h x) (h y)) xs'))\<close>
proof -
  show ?thesis
    unfolding full_quicksort_def
    apply (refine_vcg)
    subgoal by simp \<comment> \<open>case xs=[]\<close>
    subgoal by simp \<comment> \<open>case xs=[]\<close>

    apply (rule quicksort_correct[THEN order_trans])
    subgoal by (rule trans)
    subgoal by (rule lin)
    subgoal by linarith
    subgoal by simp

    apply (simp add: Misc.subset_Collect_conv, intro allI impI conjI)
    subgoal
      by (auto simp add: quicksort_post_def)
    subgoal
      apply (rule sorted_sublist_map_entire)
      by (auto simp add: quicksort_post_def dest: mset_eq_length)
    done
qed

lemma full_quicksort_correct:
  assumes
    trans: \<open>\<And>x y z. \<lbrakk>R (h x) (h y); R (h y) (h z)\<rbrakk> \<Longrightarrow> R (h x) (h z)\<close> and
    lin: \<open>\<And>x y. R (h x) (h y) \<or> R (h y) (h x)\<close>
  shows \<open>full_quicksort R h xs \<le> \<Down> Id (SPEC(\<lambda>xs'. mset xs' = mset xs))\<close>
  by (rule order_trans[OF full_quicksort_correct_sorted])
    (use assms in auto)

end
