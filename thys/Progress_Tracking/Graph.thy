section\<open>Multigraphs with Partially Ordered Weights\<close>

(*<*)
theory Graph
  imports "HOL-Library.Sublist" Antichain
begin
(*>*)

abbreviation (input) FROM where
  "FROM \<equiv> \<lambda>(s, l, t). s"

abbreviation (input) LBL where
  "LBL \<equiv> \<lambda>(s, l, t). l"

abbreviation (input) TO where
  "TO \<equiv> \<lambda>(s, l, t). t"

notation subseq (infix "\<preceq>" 50)

locale graph =
  fixes weights :: "'vtx :: finite \<Rightarrow> 'vtx \<Rightarrow> 'lbl :: {order, monoid_add} antichain"
  assumes zero_le[simp]: "0 \<le> (s::'lbl)"
    and plus_mono: "(s1::'lbl) \<le> s2 \<Longrightarrow> s3 \<le> s4 \<Longrightarrow> s1 + s3 \<le> s2 + s4"
    and summary_self: "weights loc loc = {}\<^sub>A"
begin

lemma le_plus: "(s::'lbl) \<le> s + s'" "(s'::'lbl) \<le> s + s'"
  by (intro plus_mono[of s s 0 s', simplified] plus_mono[of 0 s s' s', simplified])+

subsection\<open>Paths\<close>

inductive path :: "'vtx \<Rightarrow> 'vtx \<Rightarrow> ('vtx \<times> 'lbl \<times> 'vtx) list \<Rightarrow> bool" where
  path0: "l1 = l2 \<Longrightarrow> path l1 l2 []"
| path: "path l1 l2 xs \<Longrightarrow> lbl \<in>\<^sub>A weights l2 l3 \<Longrightarrow> path l1 l3 (xs @ [(l2, lbl, l3)])"

inductive_cases path0E: "path l1 l2 []"
inductive_cases path_AppendE: "path l1 l3 (xs @ [(l2,s,l2')])"

lemma path_trans: "path l1 l2 xs \<Longrightarrow> path l2 l3 ys \<Longrightarrow> path l1 l3 (xs @ ys)"
  by (rotate_tac, induct l2 l3 ys rule: path.induct)
    (auto intro: path.path simp flip: append_assoc)

lemma path_take_from: "path l1 l2 xs \<Longrightarrow> m < length xs \<Longrightarrow> FROM (xs ! m) = l2' \<Longrightarrow> path l1 l2' (take m xs)"
proof (induct l1 l2 xs rule: path.induct)
  case (path l1 l2 xs lbl l3)
  then show ?case
    apply (unfold take_append)
    apply simp
    apply (cases "l2=l2'")
     apply (metis linorder_not_less nth_append take_all)
    apply (metis case_prod_conv less_Suc_eq nth_append nth_append_length)
    done
qed simp

lemma path_take_to: "path l1 l2 xs \<Longrightarrow> m < length xs \<Longrightarrow> TO (xs ! m) = l2' \<Longrightarrow> path l1 l2' (take (m+1) xs)"
proof (induct l1 l2 xs rule: path.induct)
  case (path l1 l2 xs lbl l3)
  then show ?case
    apply (cases "m < length xs")
     apply (simp add: nth_append)
    apply clarsimp
    apply (metis case_prod_conv less_antisym nth_append_length path.path)
    done
qed simp

lemma path_determines_loc: "path l1 l2 xs \<Longrightarrow> path l1 l3 xs \<Longrightarrow> l2 = l3"
  by (induct l1 l2 xs rule: path.induct) (auto elim: path.cases)

lemma path_first_loc: "path loc loc' xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> FROM (xs ! 0) = loc"
proof (induct rule: path.induct)
  case (path l1 l2 xs lbl l3)
  then show ?case
    by (auto elim: path0E simp: nth_append)
qed simp

lemma path_to_eq_from: "path loc1 loc2 xs \<Longrightarrow> i + 1 < length xs \<Longrightarrow> FROM (xs ! (i+1)) = TO (xs ! i)"
proof (induct rule: path.induct)
  case (path l1 l2 xs lbl l3)
  then show ?case
    apply (cases "i + 1 < length xs")
     apply (simp add: nth_append)
    apply (simp add: nth_append)
    apply (metis add.commute drop_eq_Nil hd_drop_conv_nth id_take_nth_drop linorder_not_less path_determines_loc path_take_to plus_1_eq_Suc take_hd_drop)
    done
qed simp

lemma path_singleton[intro, simp]: "s \<in>\<^sub>A weights l1 l2 \<Longrightarrow> path l1 l2 [(l1,s,l2)]"
  by (subst path.simps) (auto simp: path.intros)

lemma path_appendE: "path l1 l3 (xs @ ys) \<Longrightarrow> \<exists>l2. path l2 l3 ys \<and> path l1 l2 xs"
proof (induct l1 l3 "xs@ys" arbitrary: xs ys rule: path.induct)
  case (path0 l1 l2)
  then show ?case by (auto intro: path.intros)
next
  case (path l1 l2 xs lbl l3 xs' ys')
  from path(1,3-) show ?case
    apply -
    apply (subst (asm) append_eq_append_conv2[of xs "[(l2,lbl,l3)]" xs' ys'])
    apply (elim exE conjE disjE)
    subgoal for us
      using path(2)[of xs' us]
      by (auto intro: path.intros)
    subgoal for us
      by (cases "us=[]") (auto intro: path.intros simp: Cons_eq_append_conv)
    done
qed

lemma path_replace_prefix:
  "path l1 l3 (xs @ zs) \<Longrightarrow> path l1 l2 ys \<Longrightarrow> path l1 l2 xs \<Longrightarrow> path l1 l3 (ys @ zs)"
  by (drule path_appendE) (auto elim!: path_trans dest: path_determines_loc)

lemma drop_subseq: "n \<le> length xs \<Longrightarrow> drop n xs \<preceq> xs"
  by (auto simp: suffix_def intro!: exI[of _ "take n xs"])

lemma take_subseq[simp, intro]: "take n xs \<preceq> xs"
  by (induct xs) auto

lemma map_take_subseq[simp, intro]: "map f (take n xs) \<preceq> map f xs"
  by (rule subseq_map, induct xs) auto

lemma path_distinct:
  "path l1 l2 xs \<Longrightarrow> \<exists>xs'. distinct xs' \<and> path l1 l2 xs' \<and> map LBL xs' \<preceq> map LBL xs"
proof (induct rule: path.induct)
  case (path0 l1 l2)
  then show ?case
    by (intro exI[of _ "[]"]) (auto intro: path.intros)
next
  case (path l1 l2 xs lbl l3)
  then obtain xs' where ih: "path l1 l2 xs'" "distinct xs'" "map LBL xs' \<preceq> map LBL xs"
    by blast
  then show ?case
  proof (cases "(l2, lbl, l3) \<in> set xs'")
    case True
    then obtain m where m: "m < length xs'" "xs' ! m = (l2, lbl, l3)"
      unfolding in_set_conv_nth by blast
    from m ih have "path l1 l2 (take m xs')"
      by (auto intro: path_take_from)
    with m ih path show ?thesis
      apply (intro exI[of _ "take m xs' @ [(l2, lbl, l3)]"])
      apply (rule conjI)
       apply (metis distinct_take take_Suc_conv_app_nth)
      apply (rule conjI)
       apply (rule path.intros)
        apply simp
       apply simp
      apply simp
      apply (metis ih(3) subseq_order.order.trans take_map take_subseq)
      done
  next
    case False
    with ih path(3) show ?thesis
      by (auto intro!: exI[of _ "xs' @ [(l2, lbl, l3)]"] intro: path.intros)
  qed
qed

lemma path_edge: "(l1', lbl, l2') \<in> set xs \<Longrightarrow> path l1 l2 xs \<Longrightarrow> lbl \<in>\<^sub>A weights l1' l2'"
  by (rotate_tac, induct rule: path.induct) auto

subsection\<open>Path Weights\<close>

abbreviation sum_weights :: "'lbl list \<Rightarrow> 'lbl" where
  "sum_weights xs \<equiv> foldr (+) xs 0"
abbreviation "sum_path_weights xs \<equiv> sum_weights (map LBL xs)"

definition "path_weightp l1 l2 s \<equiv> (\<exists>xs. path l1 l2 xs \<and> s = sum_path_weights xs)"

lemma sum_not_less_zero[simp, dest]: "(s::'lbl) < 0 \<Longrightarrow> False"
  by (simp add: less_le_not_le)

lemma sum_le_zero[simp]: "(s::'lbl) \<le> 0 \<longleftrightarrow> s = 0"
  by (simp add: eq_iff)

lemma sum_le_zeroD[dest]: "(x::'lbl) \<le> 0 \<Longrightarrow> x = 0"
  by simp

lemma foldr_plus_mono: "(n::'lbl) \<le> m \<Longrightarrow> foldr (+) xs n \<le> foldr (+) xs m"
  by (induct xs) (auto simp: plus_mono)

lemma sum_weights_append:
  "sum_weights (ys @ xs) = sum_weights ys + sum_weights xs"
  by (induct ys) (auto simp: add.assoc)

lemma sum_summary_prepend_le: "sum_path_weights ys \<le> sum_path_weights xs \<Longrightarrow> sum_path_weights (zs @ ys) \<le> sum_path_weights (zs @ xs)"
  by (induct zs arbitrary: xs ys) (auto intro: plus_mono)

lemma sum_summary_append_le: "sum_path_weights ys \<le> sum_path_weights xs \<Longrightarrow> sum_path_weights (ys @ zs) \<le> sum_path_weights (xs @ zs)"
proof (induct zs arbitrary: xs ys)
  case (Cons a zs)
  then show ?case
    by (metis plus_mono map_append order_refl sum_weights_append)
qed simp

lemma foldr_plus_zero_le: "foldr (+) xs (0::'lbl) \<le> foldr (+) xs a"
  by (induct xs) (simp_all add: plus_mono)

lemma subseq_sum_weights_le:
  assumes "xs \<preceq> ys"
  shows "sum_weights xs \<le> sum_weights ys"
  using assms
proof (induct rule: list_emb.induct)
  case (list_emb_Nil ys)
  then show ?case by auto
next
  case (list_emb_Cons xs ys y)
  then show ?case by (auto elim!: order_trans simp: le_plus)
next
  case (list_emb_Cons2 x y xs ys)
  then show ?case by (auto elim!: order_trans simp: plus_mono)
qed

lemma subseq_sum_path_weights_le:
  "map LBL xs \<preceq> map LBL ys \<Longrightarrow> sum_path_weights xs \<le> sum_path_weights ys"
  by (rule subseq_sum_weights_le)

lemma sum_path_weights_take_le[simp, intro]: "sum_path_weights (take i xs) \<le> sum_path_weights xs"
  by (auto intro!: subseq_sum_path_weights_le)

lemma sum_weights_append_singleton:
  "sum_weights (xs @ [x]) = sum_weights xs + x"
  by (induct xs) (simp_all add: add.assoc)

lemma sum_path_weights_append_singleton:
  "sum_path_weights (xs @ [(l,x,l')]) = sum_path_weights xs + x"
  by (induct xs) (simp_all add: add.assoc)

lemma path_weightp_ex_path:
  "path_weightp l1 l2 s \<Longrightarrow> \<exists>xs.
  (let s' = sum_path_weights xs in s' \<le> s \<and> path_weightp l1 l2 s' \<and> distinct xs \<and>
  (\<forall>(l1,s,l2) \<in> set xs. s \<in>\<^sub>A weights l1 l2))"
  unfolding path_weightp_def
  apply (erule exE conjE)+
  apply (drule path_distinct)
  apply (erule exE conjE)+
  subgoal for xs xs'
    apply (rule exI[of _ xs'])
    apply (auto simp: Let_def dest!: path_edge intro: subseq_sum_path_weights_le)
    done
  done

lemma finite_set_summaries:
  "finite ((\<lambda>((l1,l2),s). (l1,s,l2)) ` (Sigma UNIV (\<lambda>(l1,l2). set_antichain (weights l1 l2))))"
  by force

lemma finite_summaries: "finite {xs. distinct xs \<and> (\<forall>(l1, s, l2) \<in> set xs. s \<in>\<^sub>A weights l1 l2)}"
  apply (rule finite_subset[OF _ finite_distinct_bounded[of "((\<lambda>((l1,l2),s). (l1,s,l2)) ` (Sigma UNIV (\<lambda>(l1,l2). set_antichain (weights l1 l2))))"]])
   apply (force simp: finite_set_summaries)+
  done

lemma finite_minimal_antichain_path_weightp:
  "finite (minimal_antichain {x. path_weightp l1 l2 x})"
  apply (rule finite_surj[OF finite_summaries, where f = sum_path_weights])
  apply (clarsimp simp: minimal_antichain_def image_iff dest!: path_weightp_ex_path)
  apply (fastforce simp: Let_def)
  done

(* antichain of summaries along cycles-less paths (cycle-less = no edge repeated) *)
lift_definition path_weight :: "'vtx \<Rightarrow> 'vtx \<Rightarrow> 'lbl antichain"
  is "\<lambda>l1 l2. minimal_antichain {x. path_weightp l1 l2 x}"
  using finite_minimal_antichain_path_weightp
  by auto

definition "reachable l1 l2 \<equiv> path_weight l1 l2 \<noteq> {}\<^sub>A"

lemma in_path_weight: "s \<in>\<^sub>A path_weight loc1 loc2 \<longleftrightarrow> s \<in> minimal_antichain {s. path_weightp loc1 loc2 s}"
  by transfer simp

lemma path_weight_refl[simp]: "0 \<in>\<^sub>A path_weight loc loc"
proof -
  have *: "path loc loc []"
    by (simp add: path0)
  then have "0 = sum_path_weights []" by auto
  with * have "path_weightp loc loc 0"
    using path_weightp_def by blast
  then show ?thesis
    by (auto simp: in_path_weight in_minimal_antichain)
qed

lemma zero_in_minimal_antichain[simp]: "(0::'lbl) \<in> S \<Longrightarrow> 0 \<in> minimal_antichain S"
  by (auto simp: in_minimal_antichain intro: sum_not_less_zero)

definition "path_weightp_distinct l1 l2 s \<equiv> (\<exists>xs. distinct xs \<and> path l1 l2 xs \<and> s = sum_path_weights xs)"

lemma minimal_antichain_path_weightp_distinct:
  "minimal_antichain {xs. path_weightp l1 l2 xs} = minimal_antichain {xs. path_weightp_distinct l1 l2 xs}"
  unfolding path_weightp_def path_weightp_distinct_def minimal_antichain_def
  apply safe
     apply clarsimp
     apply (metis path_distinct order.strict_iff_order subseq_sum_path_weights_le)
    apply (blast+) [2]
  apply clarsimp
  apply (metis (no_types, lifting) le_less_trans path_distinct subseq_sum_weights_le)
  done

lemma finite_path_weightp_distinct[simp, intro]: "finite {xs. path_weightp_distinct l1 l2 xs}"
  unfolding path_weightp_distinct_def
  apply (rule finite_subset[where B = "sum_path_weights ` {xs. distinct xs \<and> path l1 l2 xs}"])
   apply clarsimp
  apply (rule finite_imageI)
  apply (rule finite_subset[OF _ finite_summaries])
  apply (clarsimp simp: path_edge)
  done

lemma path_weightp_distinct_nonempty:
  "{xs. path_weightp l1 l2 xs} \<noteq> {} \<longleftrightarrow> {xs. path_weightp_distinct l1 l2 xs} \<noteq> {}"
  by (auto dest: path_distinct simp: path_weightp_def path_weightp_distinct_def)

lemma path_weightp_distinct_member:
  "s \<in> {s. path_weightp l1 l2 s} \<Longrightarrow> \<exists>u. u \<in> {s. path_weightp_distinct l1 l2 s} \<and> u \<le> s"
  apply (clarsimp simp: path_weightp_def path_weightp_distinct_def)
  apply (drule path_distinct)
  apply (auto dest: subseq_sum_path_weights_le)
  done

lemma minimal_antichain_path_weightp_member:
  "s \<in> {xs. path_weightp l1 l2 xs} \<Longrightarrow> \<exists>u. u \<in> minimal_antichain {xs. path_weightp l1 l2 xs} \<and> u \<le> s"
proof -
  assume "s \<in> {xs. path_weightp l1 l2 xs}"
  then obtain u where u: "u \<in> {s. path_weightp_distinct l1 l2 s} \<and> u \<le> s"
    using path_weightp_distinct_member by blast
  have finite: "finite {xs. path_weightp_distinct l1 l2 xs}" ..
  from u finite obtain v where "v \<in> minimal_antichain {xs. path_weightp_distinct l1 l2 xs} \<and> v \<le> u"
    by atomize_elim (auto intro: minimal_antichain_member)
  with u show ?thesis
    by (auto simp: minimal_antichain_path_weightp_distinct)
qed

lemma path_path_weight: "path l1 l2 xs \<Longrightarrow> \<exists>s. s \<in>\<^sub>A path_weight l1 l2 \<and> s \<le> sum_path_weights xs"
proof -
  assume "path l1 l2 xs"
  then have "sum_path_weights xs \<in> {x. path_weightp l1 l2 x}"
    by (auto simp: path_weightp_def)
  then obtain u where "u \<in> minimal_antichain {x. path_weightp l1 l2 x} \<and> u \<le> sum_path_weights xs"
    apply atomize_elim
    apply (drule minimal_antichain_path_weightp_member)
    apply auto
    done
  then show ?thesis
    by transfer auto
qed

lemma path_weight_conv_path:
  "s \<in>\<^sub>A path_weight l1 l2 \<Longrightarrow> \<exists>xs. path l1 l2 xs \<and> s = sum_path_weights xs \<and> (\<forall>ys. path l1 l2 ys \<longrightarrow> \<not> sum_path_weights ys < sum_path_weights xs)"
  by transfer (auto simp: in_minimal_antichain path_weightp_def)

abbreviation "optimal_path loc1 loc2 xs \<equiv> path loc1 loc2 xs \<and>
   (\<forall>ys. path loc1 loc2 ys \<longrightarrow> \<not> sum_path_weights ys < sum_path_weights xs)"

lemma path_weight_path: "s \<in>\<^sub>A path_weight loc1 loc2 \<Longrightarrow>
  (\<And>xs. optimal_path loc1 loc2 xs \<Longrightarrow> distinct xs \<Longrightarrow> sum_path_weights xs = s \<Longrightarrow> P) \<Longrightarrow> P"
  apply atomize_elim
  apply transfer
  apply (clarsimp simp: in_minimal_antichain path_weightp_def)
  apply (drule path_distinct)
  apply (erule exE)
  subgoal for loc1 loc2 xs xs'
    apply (rule exI[of _ xs'])
    apply safe
    using order.strict_iff_order subseq_sum_path_weights_le apply metis
    using less_le subseq_sum_path_weights_le apply fastforce
    done
  done

lemma path_weight_elem_trans:
  "s \<in>\<^sub>A path_weight l1 l2 \<Longrightarrow> s' \<in>\<^sub>A path_weight l2 l3 \<Longrightarrow> \<exists>u. u \<in>\<^sub>A path_weight l1 l3 \<and> u \<le> s + s'"
proof -
  assume ps1: "s  \<in>\<^sub>A path_weight l1 l2"
  assume ps2: "s' \<in>\<^sub>A path_weight l2 l3"
  from ps1 obtain xs where path1: "path l1 l2 xs" "s = sum_path_weights xs"
    by (auto intro: path_weight_path)
  from ps2 obtain ys where path2: "path l2 l3 ys" "s' = sum_path_weights ys"
    by (auto intro: path_weight_path)
  from path1(1) path2(1) have "path l1 l3 (xs @ ys)"
    by (rule path_trans)
  with path1(2) path2(2) have "s + s' \<in> {s. path_weightp l1 l3 s}"
    by (auto simp: path_weightp_def sum_weights_append[symmetric])
  then show "\<exists>u. u \<in>\<^sub>A path_weight l1 l3 \<and> u \<le> s + s'"
    by transfer (simp add: minimal_antichain_path_weightp_member)
qed

end

(*<*)
end
(*>*)