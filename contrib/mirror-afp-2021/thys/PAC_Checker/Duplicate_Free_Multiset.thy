(*
  File:         Duplicate_Free_Multiset.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory Duplicate_Free_Multiset
imports Nested_Multisets_Ordinals.Multiset_More
begin


section \<open>Duplicate Free Multisets\<close>

(* TODO Move Multiset_More *)
lemma remove_diff_multiset[simp]: \<open>x13 \<notin># A \<Longrightarrow> A - add_mset x13 B = A - B\<close>
  by (metis diff_intersect_left_idem inter_add_right1)


text \<open>Duplicate free multisets are isomorphic to finite sets, but it can be useful to reason about
  duplication to speak about intermediate execution steps in the refinements.
\<close>
lemma distinct_mset_remdups_mset_id: \<open>distinct_mset C \<Longrightarrow> remdups_mset C = C\<close>
  by (induction C)  auto

lemma notin_add_mset_remdups_mset:
  \<open>a \<notin># A \<Longrightarrow> add_mset a (remdups_mset A) = remdups_mset (add_mset a A)\<close>
  by auto

lemma distinct_mset_image_mset:
  \<open>distinct_mset (image_mset f (mset xs)) \<longleftrightarrow> distinct (map f xs)\<close>
  apply (subst mset_map[symmetric])
  apply (subst distinct_mset_mset_distinct)
  ..

lemma distinct_mset_mono: \<open>D' \<subseteq># D \<Longrightarrow> distinct_mset D \<Longrightarrow> distinct_mset D'\<close>
  by (metis distinct_mset_union subset_mset.le_iff_add)

lemma distinct_mset_mono_strict: \<open>D' \<subset># D \<Longrightarrow> distinct_mset D \<Longrightarrow> distinct_mset D'\<close>
  using distinct_mset_mono by auto

lemma distinct_set_mset_eq_iff:
  assumes \<open>distinct_mset M\<close> \<open>distinct_mset N\<close>
  shows \<open>set_mset M = set_mset N \<longleftrightarrow> M = N\<close>
  using assms distinct_mset_set_mset_ident by fastforce

lemma distinct_mset_union2:
  \<open>distinct_mset (A + B) \<Longrightarrow> distinct_mset B\<close>
  using distinct_mset_union[of B A]
  by (auto simp: ac_simps)

lemma distinct_mset_mset_set: \<open>distinct_mset (mset_set A)\<close>
  unfolding distinct_mset_def count_mset_set_if by (auto simp: not_in_iff)

lemma distinct_mset_inter_remdups_mset:
  assumes dist: \<open>distinct_mset A\<close>
  shows \<open>A \<inter># remdups_mset B = A \<inter># B\<close>
proof -
  have [simp]: \<open>A' \<inter># remove1_mset a (remdups_mset Aa) = A' \<inter># Aa\<close>
    if
      \<open>A' \<inter># remdups_mset Aa = A' \<inter># Aa\<close> and
      \<open>a \<notin># A'\<close> and
      \<open>a \<in># Aa\<close>
    for A' Aa :: \<open>'a multiset\<close> and a
  by (metis insert_DiffM inter_add_right1 set_mset_remdups_mset that)

  show ?thesis
    using dist
    apply (induction A)
    subgoal by auto
     subgoal for a A'
       by (cases \<open>a \<in># B\<close>)
         (use multi_member_split[of a \<open>B\<close>]  multi_member_split[of a \<open>A\<close>] in
           \<open>auto simp: mset_set.insert_remove\<close>)
    done
qed

lemma finite_mset_set_inter:
  \<open>finite A \<Longrightarrow> finite B \<Longrightarrow> mset_set (A \<inter> B) = mset_set A \<inter># mset_set B\<close>
  apply (induction A rule: finite_induct)
  subgoal by auto
  subgoal for a A
    by (cases \<open>a \<in> B\<close>; cases \<open>a \<in># mset_set B\<close>)
      (use multi_member_split[of a \<open>mset_set B\<close>] in
        \<open>auto simp: mset_set.insert_remove\<close>)
  done

lemma removeAll_notin: \<open>a \<notin># A \<Longrightarrow> removeAll_mset a A = A\<close>
  using count_inI by force

lemma same_mset_distinct_iff:
  \<open>mset M = mset M' \<Longrightarrow> distinct M \<longleftrightarrow> distinct M'\<close>
  by (auto simp: distinct_mset_mset_distinct[symmetric] simp del: distinct_mset_mset_distinct)


subsection \<open>More Lists\<close>
lemma in_set_conv_iff:
  \<open>x \<in> set (take n xs) \<longleftrightarrow> (\<exists>i < n. i < length xs \<and> xs ! i = x)\<close>
  apply (induction n)
  subgoal by auto
  subgoal for n
    apply (cases \<open>Suc n < length xs\<close>)
    subgoal by (auto simp: take_Suc_conv_app_nth less_Suc_eq dest: in_set_takeD)
    subgoal
      apply (cases \<open>n < length xs\<close>)
      subgoal
        apply (auto simp: in_set_conv_nth)
        by (rename_tac i, rule_tac x=i in exI; auto; fail)+
      subgoal
        apply (auto simp: take_Suc_conv_app_nth dest: in_set_takeD)
        by (rename_tac i, rule_tac x=i in exI; auto; fail)+
      done
    done
  done

lemma in_set_take_conv_nth:
  \<open>x \<in> set (take n xs) \<longleftrightarrow> (\<exists>m<min n (length xs). xs ! m = x)\<close>
  by (metis in_set_conv_nth length_take min.commute min.strict_boundedE nth_take)

lemma in_set_remove1D:
  \<open>a \<in> set (remove1 x xs) \<Longrightarrow> a \<in> set xs\<close>
  by (meson notin_set_remove1)


subsection \<open>Generic Multiset\<close>

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
    by (auto simp add: mset_set_Suc_Suc)
  show ?case
    apply (cases a)
    using Cons[of 0] Cons by (auto simp: nth_Cons drop_Cons H mset_case_Suc *)
qed


subsection \<open>Other\<close>

text \<open>I believe this should be added to the simplifier by default...\<close>
lemma Collect_eq_comp': \<open> {(x, y). P x y} O {(c, a). c = f a} = {(x, a). P x (f a)}\<close>
  by auto

end
