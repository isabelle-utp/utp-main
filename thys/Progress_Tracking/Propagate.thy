section \<open>Local Progress Propagation\label{sec:propagate}\<close>

(*<*)
theory Propagate
  imports
    Graph
begin
(*>*)

subsection \<open>Specification\<close>

record (overloaded) ('loc, 't) configuration =
  c_work :: "'loc \<Rightarrow> 't zmultiset" (* worklists with not-yet-applied updates *)
  c_pts  :: "'loc \<Rightarrow> 't zmultiset" (* tracked point-stamps *)
  c_imp  :: "'loc \<Rightarrow> 't zmultiset" (* alive point-stamps ("implications") *)

type_synonym ('loc, 't) computation = "('loc, 't) configuration stream"

locale dataflow_topology = flow?: graph summary
  for summary :: "'loc \<Rightarrow> 'loc :: finite \<Rightarrow> 'sum :: {order, monoid_add} antichain" +
  fixes results_in :: "'t :: order \<Rightarrow> 'sum \<Rightarrow> 't"
  assumes results_in_zero: "results_in t 0 = t"
    and results_in_mono_raw: "t1 \<le> t2 \<Longrightarrow> s1 \<le> s2 \<Longrightarrow> results_in t1 s1 \<le> results_in t2 s2"
    and followed_by_summary: "results_in (results_in t s1) s2 = results_in t (s1 + s2)"
    and no_zero_cycle: "path loc loc xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> s = sum_path_weights xs \<Longrightarrow> t < results_in t s"
begin

lemma results_in_mono:
  "t1 \<le> t2 \<Longrightarrow> results_in t1 s \<le> results_in t2 s"
  "s1 \<le> s2 \<Longrightarrow> results_in t s1 \<le> results_in t s2"
  using results_in_mono_raw by auto

abbreviation "path_summary \<equiv> path_weight"
abbreviation followed_by :: "'sum \<Rightarrow> 'sum \<Rightarrow> 'sum" where
  "followed_by \<equiv> plus"

definition safe :: "('loc, 't) configuration \<Rightarrow> bool" where
  "safe c \<equiv> \<forall>loc1 loc2 t s. zcount (c_pts c loc1) t > 0 \<and> s \<in>\<^sub>A path_summary loc1 loc2
                \<longrightarrow> (\<exists>t'\<le>results_in t s. t' \<in>\<^sub>A frontier (c_imp c loc2))"

text \<open>Implications are always non-negative.\<close>
definition inv_implications_nonneg where
  "inv_implications_nonneg c = (\<forall>loc t. zcount (c_imp c loc) t \<ge> 0)"

abbreviation "unchanged f c0 c1 \<equiv> f c1 = f c0"

abbreviation zmset_frontier where
  "zmset_frontier M \<equiv> zmset_of (mset_set (set_antichain (frontier M)))"

definition init_config where
  "init_config c \<equiv> \<forall>loc.
      c_imp c loc = {#}\<^sub>z \<and>
      c_work c loc = zmset_frontier (c_pts c loc)"


definition after_summary :: "'t zmultiset \<Rightarrow> 'sum antichain \<Rightarrow> 't zmultiset" where
  "after_summary M S \<equiv> (\<Sum>s \<in> set_antichain S. image_zmset (\<lambda>t. results_in t s) M)"

abbreviation frontier_changes :: "'t zmultiset \<Rightarrow> 't zmultiset \<Rightarrow> 't zmultiset" where
  "frontier_changes M N \<equiv> zmset_frontier M - zmset_frontier N"

definition next_change_multiplicity' :: "('loc, 't) configuration \<Rightarrow> ('loc, 't) configuration \<Rightarrow> 'loc \<Rightarrow> 't \<Rightarrow> int \<Rightarrow> bool" where
  "next_change_multiplicity' c0 c1 loc t n \<equiv>
    \<comment> \<open>n is the non-zero change in pointstamps at loc for timestamp t\<close>
     n \<noteq> 0 \<and>
    \<comment> \<open>change can only happen at timestamps not in advance of implication-frontier\<close>
     (\<exists>t'. t' \<in>\<^sub>A frontier (c_imp c0 loc) \<and> t' \<le> t) \<and>
       \<comment> \<open>at loc, t is added to pointstamps n times\<close>
     c1 = c0\<lparr>c_pts := (c_pts c0)(loc := update_zmultiset (c_pts c0 loc) t n),
       \<comment> \<open>worklist at loc is adjusted by frontier changes\<close>
             c_work := (c_work c0)(loc := c_work c0 loc +
                frontier_changes (update_zmultiset (c_pts c0 loc) t n) (c_pts c0 loc))\<rparr>"

abbreviation next_change_multiplicity :: "('loc, 't) configuration \<Rightarrow> ('loc, 't) configuration \<Rightarrow> bool" where
  "next_change_multiplicity c0 c1 \<equiv> \<exists>loc t n. next_change_multiplicity' c0 c1 loc t n"

lemma cm_unchanged_worklist:
  assumes "next_change_multiplicity' c0 c1 loc t n"
    and   "loc' \<noteq> loc"
  shows   "c_work c1 loc' = c_work c0 loc'"
  using assms unfolding next_change_multiplicity'_def
  by auto

definition next_propagate' :: "('loc, 't) configuration \<Rightarrow> ('loc, 't) configuration \<Rightarrow> 'loc \<Rightarrow> 't \<Rightarrow> bool" where
  "next_propagate' c0 c1 loc t \<equiv>
    \<comment> \<open>t is a least timestamp of all worklist entries\<close>
      (t \<in>#\<^sub>z c_work c0 loc \<and>
      (\<forall>t' loc'. t' \<in>#\<^sub>z c_work c0 loc' \<longrightarrow> \<not> t' < t) \<and>
      c1 = c0\<lparr>c_imp := (c_imp c0)(loc := c_imp c0 loc + {#t' \<in>#\<^sub>z c_work c0 loc. t' = t#}),
              c_work := (\<lambda>loc'.
                  \<comment> \<open>worklist entries for t are removed from loc's worklist\<close>
                    if loc' = loc then {#t' \<in>#\<^sub>z c_work c0 loc'. t' \<noteq> t#}
                  \<comment> \<open>worklists at other locations change by the loc's frontier change after adding summaries\<close>
                    else c_work c0 loc'
                           + after_summary
                               (frontier_changes (c_imp c0 loc + {#t' \<in>#\<^sub>z c_work c0 loc. t' = t#}) (c_imp c0 loc))
                               (summary loc loc'))\<rparr>)"

abbreviation next_propagate :: "('loc, 't :: order) configuration \<Rightarrow> ('loc, 't) configuration \<Rightarrow> bool" where
  "next_propagate c0 c1 \<equiv> \<exists>loc t. next_propagate' c0 c1 loc t"

definition "next'" where
  "next' c0 c1 = (next_propagate c0 c1 \<or> next_change_multiplicity c0 c1 \<or> c1 = c0)"

abbreviation "next" where
  "next s \<equiv> next' (shd s) (shd (stl s))"

abbreviation cm_valid where
  "cm_valid \<equiv> nxt (\<lambda>s. next_change_multiplicity (shd s) (shd (stl s))) impl
                (\<lambda>s. next_change_multiplicity (shd s) (shd (stl s))) or nxt (holds (\<lambda>c. (\<forall>l. c_work c l = {#}\<^sub>z)))"

definition spec :: "('loc, 't :: order) computation \<Rightarrow> bool" where
  "spec \<equiv> holds init_config aand alw next"

lemma next'_inv[consumes 1, case_names next_change_multiplicity next_propagate next_finish_init]:
  assumes "next' c0 c1" "P c0"
    and   "\<And>loc t n. P c0 \<Longrightarrow> next_change_multiplicity' c0 c1 loc t n \<Longrightarrow> P c1"
    and   "\<And>loc t. P c0 \<Longrightarrow> next_propagate' c0 c1 loc t \<Longrightarrow> P c1"
  shows   "P c1"
  using assms unfolding next'_def by auto

subsection\<open>Auxiliary\<close>

lemma next_change_multiplicity'_unique:
  assumes "n \<noteq> 0"
    and   "\<exists>t'. t' \<in>\<^sub>A frontier (c_imp c loc) \<and> t' \<le> t"
  shows   "\<exists>!c'. next_change_multiplicity' c c' loc t n"
proof -
  let ?pointstamps' = "(c_pts c)(loc := update_zmultiset (c_pts c loc) t n)"
  let ?worklist' = "\<lambda>loc'. c_work c loc' + frontier_changes (?pointstamps' loc') (c_pts c loc')"
  let ?c' = "c\<lparr>c_pts := ?pointstamps', c_work := ?worklist'\<rparr>"
  from assms have "next_change_multiplicity' c ?c' loc t n"
    by (auto simp: next_change_multiplicity'_def intro!: configuration.equality)
  then show ?thesis
    by (rule ex1I[of _ ?c'])
      (auto  simp: next_change_multiplicity'_def intro!: configuration.equality)
qed

lemma frontier_change_zmset_frontier:
  assumes "t \<in>\<^sub>A frontier M1 - frontier M0"
  shows   "zcount (zmset_frontier M1) t = 1 \<and> zcount (zmset_frontier M0) t = 0"
  using assms by (clarsimp simp: ac_Diff_iff) (simp add: member_antichain.rep_eq)

lemma frontier_empty[simp]: "frontier {#}\<^sub>z = {}\<^sub>A"
  by transfer' simp

lemma zmset_frontier_empty[simp]: "zmset_frontier {#}\<^sub>z = {#}\<^sub>z"
  by simp

lemma after_summary_empty[simp]: "after_summary {#}\<^sub>z S = {#}\<^sub>z"
  by (simp add: after_summary_def)

lemma after_summary_empty_summary[simp]: "after_summary M {}\<^sub>A = {#}\<^sub>z"
  by (simp add: after_summary_def)

lemma mem_frontier_diff:
  assumes "t \<in>\<^sub>A frontier M - frontier N"
  shows   "zcount (frontier_changes M N) t = 1"
proof -
  note assms
  then have t: "t \<in>\<^sub>A frontier M" "t \<notin>\<^sub>A frontier N"
    using ac_Diff_iff by blast+
  from t(1) have "zcount (zmset_frontier M) t = 1"
    by (simp add: member_antichain.rep_eq)
  moreover from t(2) have "zcount (zmset_frontier N) t = 0"
    by (simp add: member_antichain.rep_eq)
  ultimately show "zcount (frontier_changes M N) t = 1"
    by simp
qed

lemma mem_frontier_diff':
  assumes "t \<in>\<^sub>A frontier N - frontier M"
  shows   "zcount (frontier_changes M N) t = -1"
proof -
  note assms
  then have t: "t \<in>\<^sub>A frontier N" "t \<notin>\<^sub>A frontier M"
    using ac_Diff_iff by blast+
  from t(2) have "zcount (zmset_frontier M) t = 0"
    by (simp add: member_antichain.rep_eq)
  moreover from t(1) have "zcount (zmset_frontier N) t = 1"
    by (simp add: member_antichain.rep_eq)
  ultimately show "zcount (frontier_changes M N) t = -1"
    by simp
qed

lemma not_mem_frontier_diff:
  assumes "t \<notin>\<^sub>A frontier M - frontier N"
    and   "t \<notin>\<^sub>A frontier N - frontier M"
  shows   "zcount (frontier_changes M N) t = 0"
proof -
  { assume M: "t \<in>\<^sub>A frontier M"
    with assms have N: "t \<in>\<^sub>A frontier N"
      by (auto dest: ac_notin_Diff)
    from M N have "zcount (zmset_frontier M) t = 1" "zcount (zmset_frontier N) t = 1"
      by (simp_all add: member_antichain.rep_eq)
    then have "zcount (frontier_changes M N) t = 0"
      by simp
  }
  moreover
  { assume M: "t \<notin>\<^sub>A frontier M"
    with assms have N: "t \<notin>\<^sub>A frontier N"
      by (auto dest: ac_notin_Diff)
    from M N have "zcount (zmset_frontier M) t = 0" "zcount (zmset_frontier N) t = 0"
      by (simp_all add: member_antichain.rep_eq)
    then have "zcount (frontier_changes M N) t = 0"
      by simp
  }
  ultimately show "zcount (frontier_changes M N) t = 0"
    by blast
qed

lemma mset_neg_after_summary: "mset_neg M = {#} \<Longrightarrow> mset_neg (after_summary M S) = {#}"
  by (auto intro: mset_neg_image_zmset mset_neg_sum_set simp: after_summary_def)

\<comment> \<open>Changes in loc's frontier are reflected in the worklist of loc'.\<close>
lemma next_p_frontier_change:
  assumes "next_propagate' c0 c1 loc t"
    and "summary loc loc' \<noteq> {}\<^sub>A"
  shows "c_work c1 loc' =
         c_work c0 loc'
          + after_summary
              (frontier_changes (c_imp c1 loc) (c_imp c0 loc))
              (summary loc loc')"
  using assms by (auto simp: summary_self next_propagate'_def intro!: configuration.equality)

lemma after_summary_union: "after_summary (M + N) S = after_summary M S + after_summary N S"
  by (simp add: sum.distrib after_summary_def)


subsection\<open>Invariants\<close>

subsubsection\<open>Invariant: @{term inv_imps_work_sum}\<close>

\<comment> \<open>Get timestamps in frontiers of loc's predecessor locations, apply respective summaries and
    return union of results.\<close>
abbreviation union_frontiers :: "('loc, 't) configuration \<Rightarrow> 'loc \<Rightarrow> 't zmultiset" where
  "union_frontiers c loc \<equiv>
    (\<Sum>loc'\<in>UNIV. after_summary (zmset_frontier (c_imp c loc')) (summary loc' loc))"

\<comment> \<open>Implications + worklist is equal to the frontiers of pointstamps and all preceding nodes
    (after accounting for summaries).\<close>
definition inv_imps_work_sum :: "('loc, 't) configuration \<Rightarrow> bool" where
  "inv_imps_work_sum c \<equiv>
    \<forall>loc. c_imp c loc + c_work c loc
        = zmset_frontier (c_pts c loc) + union_frontiers c loc"

\<comment> \<open>Version with zcount is easier to reason with\<close>
definition inv_imps_work_sum_zcount :: "('loc, 't) configuration \<Rightarrow> bool" where
  "inv_imps_work_sum_zcount c \<equiv>
    \<forall>loc t. zcount (c_imp c loc + c_work c loc) t
          = zcount (zmset_frontier (c_pts c loc) + union_frontiers c loc) t"

lemma inv_imps_work_sum_zcount: "inv_imps_work_sum c \<longleftrightarrow> inv_imps_work_sum_zcount c"
  unfolding inv_imps_work_sum_zcount_def inv_imps_work_sum_def
  by (simp add: zmultiset_eq_iff)


lemma union_frontiers_nonneg: "0 \<le> zcount (union_frontiers c loc) t"
  apply (subst zcount_sum)
  apply (rule sum_nonneg)
  apply simp
  apply (rule mset_neg_zcount_nonneg)
  apply (rule mset_neg_after_summary)
  apply simp
  done

lemma next_p_union_frontier_change:
  assumes "next_propagate' c0 c1 loc t"
    and "summary loc loc' \<noteq> {}\<^sub>A"
  shows "union_frontiers c1 loc' =
         union_frontiers c0 loc'
          + after_summary
              (frontier_changes (c_imp c1 loc) (c_imp c0 loc))
              (summary loc loc')"
  using assms
  apply (subst zmultiset_eq_iff)
  apply (rule allI)
  subgoal for x
    apply (simp del: zcount_of_mset image_zmset_Diff)
    apply (subst (1 2) zcount_sum)
    apply (rule Sum_eq_pick_changed_elem[of UNIV loc])
       apply simp
      apply simp
    subgoal
      apply (subst zcount_union[symmetric])
      apply (subst after_summary_union[symmetric])
      apply simp
      done
    apply (auto simp: next_propagate'_def)
    done
  done

\<comment> \<open>@{term init_config} satisfies @{term inv_imps_work_sum}\<close>
lemma init_imp_inv_imps_work_sum: "init_config c \<Longrightarrow> inv_imps_work_sum c"
  by (simp add: inv_imps_work_sum_def init_config_def)

\<comment> \<open>CM preserves @{term inv_imps_work_sum}\<close>
lemma cm_preserves_inv_imps_work_sum:
  assumes "next_change_multiplicity' c0 c1 loc t n"
    and   "inv_imps_work_sum c0"
  shows   "inv_imps_work_sum c1"
proof -
  \<comment> \<open>Given CM at loc, t, we show result for loc', t'\<close>
  { fix loc t loc' t' n
    assume cm': "next_change_multiplicity' c0 c1 loc t n"
    note cm = this[unfolded next_change_multiplicity'_def]
    from cm have unchanged_imps: "unchanged c_imp c0 c1"
      by simp
    assume "inv_imps_work_sum c0"
    then have iiws': "inv_imps_work_sum_zcount c0"
      by (simp add: inv_imps_work_sum_zcount)
    note iiws = iiws'[unfolded inv_imps_work_sum_zcount_def, THEN spec2]
    have unchanged_union: "union_frontiers c1 locX = union_frontiers c0 locX" for locX
      using unchanged_imps by (auto intro: sum.cong)
        \<comment> \<open>For locations other than loc nothing changes.\<close>
    { assume loc: "loc' \<noteq> loc"
      note iiws = iiws'[unfolded inv_imps_work_sum_zcount_def, THEN spec2, of loc' t']
      from loc cm have unchanged_worklist:
        "zcount (c_work c1 loc') t' = zcount (c_work c0 loc') t'"
        by simp
      from loc cm have unchanged_frontier:
        "zcount (zmset_frontier (c_pts c1 loc')) t'
       = zcount (zmset_frontier (c_pts c0       loc')) t'"
        by simp
      with loc have
        "zcount (c_imp c1 loc' + c_work c1 loc') t'
            = zcount (zmset_frontier (c_pts c1 loc')
                + union_frontiers c1 loc') t'"
        apply (subst (1 2) zcount_union)
        unfolding
          unchanged_imps
          unchanged_union
          unchanged_frontier
          unchanged_worklist
        apply (subst (1 2) zcount_union[symmetric])
        apply (rule iiws)
        done
    }
    moreover
      \<comment> \<open>For pointstamps at location loc we make a case distinction on whether their "status" in
          the frontier has changed.\<close>
    { assume loc: "loc' = loc"
      note iiws = iiws'[unfolded inv_imps_work_sum_zcount_def, simplified, THEN spec, of loc, simplified]
        \<comment> \<open>If t appeared in the frontier\<close>
      { assume t': "t' \<in>\<^sub>A frontier (c_pts c1 loc) - frontier (c_pts c0 loc)"
        note t'[THEN mem_frontier_diff]
          \<comment> \<open>then the worklist at t increased by 1\<close>
        then have "zcount (c_work c1 loc) t' = zcount (c_work c0 loc) t' + 1"
          using cm by auto
            \<comment> \<open>and the frontier at t increased by 1\<close>
        moreover
        have "zcount (zmset_frontier (c_pts c1 loc)) t'
              = zcount (zmset_frontier (c_pts c0 loc)) t' + 1"
          using t'[THEN frontier_change_zmset_frontier] by simp
            \<comment> \<open>and the sum didn't change\<close>
        moreover note unchanged_union
          \<comment> \<open>hence, the invariant is preserved.\<close>
        ultimately have
          "zcount (c_imp c1 loc + c_work c1 loc) t'
            = zcount (zmset_frontier (c_pts c1 loc)
              + union_frontiers c1 loc) t'"
          using iiws unchanged_imps by simp
      }
      moreover
        \<comment> \<open>If t disappeared from the frontier\<close>
      { assume t': "t' \<in>\<^sub>A frontier (c_pts c0 loc) - frontier (c_pts c1 loc)"
        note t'[THEN mem_frontier_diff']
          \<comment> \<open>then the worklist at t decreased by 1\<close>
        then have "zcount (c_work c1 loc) t' = zcount (c_work c0 loc) t' - 1"
          using cm by (auto simp: ac_Diff_iff)
            \<comment> \<open>and the frontier at t decreased by 1\<close>
        moreover
        have "zcount (zmset_frontier (c_pts c1 loc)) t'
              = zcount (zmset_frontier (c_pts c0 loc)) t' - 1"
          using t'[THEN frontier_change_zmset_frontier] by simp
            \<comment> \<open>and the sum didn't change\<close>
        moreover note unchanged_union
          \<comment> \<open>hence, the invariant is preserved.\<close>
        ultimately have
          "zcount (c_imp c1 loc + c_work c1 loc) t'
            = zcount (zmset_frontier (c_pts c1 loc)
              + union_frontiers c1 loc) t'"
          using iiws unchanged_imps by simp
      }
      moreover
        \<comment> \<open>If t's multiplicity in the frontier didn't change\<close>
      { assume a1: "\<not> t' \<in>\<^sub>A frontier (c_pts c1 loc) - frontier (c_pts c0 loc)"
        assume a2: "\<not> t' \<in>\<^sub>A frontier (c_pts c0 loc) - frontier (c_pts c1 loc)"
        from a1 a2 have "zcount (frontier_changes (c_pts c1 loc) (c_pts c0 loc)) t' = 0"
          by (intro not_mem_frontier_diff)
            \<comment> \<open>then the worklist at t didn't change\<close>
        with cm have "zcount (c_work c1 loc) t' = zcount (c_work c0 loc) t'"
          by (auto simp: ac_Diff_iff)
            \<comment> \<open>and the frontier at t didn't change\<close>
        moreover
        have "zcount (zmset_frontier (c_pts c1 loc)) t'
            = zcount (zmset_frontier (c_pts c0 loc)) t'"
          using a1 a2
          apply (clarsimp simp: member_antichain.rep_eq dest!: ac_notin_Diff)
          apply (metis ac_Diff_iff count_mset_set(1) count_mset_set(3) finite_set_antichain member_antichain.rep_eq)
          done
            \<comment> \<open>and the sum didn't change\<close>
        moreover note unchanged_union
          \<comment> \<open>hence, the invariant is preserved.\<close>
        ultimately have
          "zcount (c_imp c1 loc + c_work c1 loc) t'
            = zcount (zmset_frontier (c_pts c1 loc)
              + union_frontiers c1 loc) t'"
          using iiws unchanged_imps by simp
      }
      ultimately have
        "zcount (c_imp c1 loc' + c_work c1 loc') t'
            = zcount (zmset_frontier (c_pts c1 loc')
              + union_frontiers c1 loc') t'"
        using loc by auto
    }
    ultimately have
      "zcount (c_imp c1 loc' + c_work c1 loc') t'
          = zcount (zmset_frontier (c_pts c1 loc')
              + union_frontiers c1 loc') t'"
      by auto
  }
  with assms show ?thesis
    by (auto simp: Let_def inv_imps_work_sum_zcount inv_imps_work_sum_zcount_def)
qed

\<comment> \<open>PR preserves @{term inv_imps_work_sum}\<close>
lemma p_preserves_inv_imps_work_sum:
  assumes "next_propagate' c0 c1 loc t"
    and   "inv_imps_work_sum c0"
  shows   "inv_imps_work_sum c1"
proof -
  \<comment> \<open>Given @{term next_propagate'} for loc, t, we show the result for loc', t'.\<close>
  { fix loc t loc' t'
    assume p': "next_propagate' c0 c1 loc t"
    note p = this[unfolded next_propagate'_def]
    from p have unchanged_ps: "unchanged c_pts c0 c1"
      by simp
    assume "inv_imps_work_sum c0"
    then have iiws': "inv_imps_work_sum_zcount c0"
      by (simp add: inv_imps_work_sum_zcount)
    note iiws = iiws'[unfolded inv_imps_work_sum_zcount_def, THEN spec2]
    { assume loc: "loc=loc'"
      note iiws
      moreover note unchanged_ps
        \<comment> \<open>The t entries in loc's worklist are shifted to the implications.\<close>
      moreover from p have "zcount (c_work c1 loc) t = 0"
        by simp
      moreover from p have
        "zcount (c_imp c1 loc) t
         = zcount (c_imp c0 loc) t + zcount (c_work c0 loc) t"
        by simp
          \<comment> \<open>Since the implications of other locations don't change and loc can't have an edge to
              itself, @{term union_frontiers} at loc doesn't change.\<close>
      moreover from p have "union_frontiers c1 loc = union_frontiers c0 loc"
        using summary_self by (auto intro!: sum.cong arg_cong[where f = Sum])
          \<comment> \<open>For all the other timestamps the worklist and implications don't change.\<close>
      moreover from p have
        "tX \<noteq> t \<Longrightarrow> zcount (c_work c1 loc) tX = zcount (c_work c0 loc) tX" for tX
        by simp
      moreover from p have
        "tX \<noteq> t \<Longrightarrow> zcount (c_imp c1 loc) tX = zcount (c_imp c0 loc) tX" for tX
        by simp
      ultimately have
        "zcount (c_imp c1 loc' + c_work c1 loc') t'
         = zcount (zmset_frontier (c_pts c1 loc') + union_frontiers c1 loc') t'"
        unfolding loc
        by (cases "t=t'") simp_all
    }
    moreover
    { assume loc: "loc\<noteq>loc'"
        \<comment> \<open>The implications are unchanged at all locations other than loc.\<close>
      from p loc have unchanged_imps: "c_imp c1 loc' = c_imp c0 loc'"
        by simp
      { assume sum: "summary loc loc' = {}\<^sub>A"
        note iiws
        moreover note unchanged_ps
        moreover note unchanged_imps
          \<comment> \<open>The worklist only changes if loc, loc' are connected.\<close>
        moreover from p loc sum have "c_work c1 loc' = c_work c0 loc'"
          by simp
            \<comment> \<open>Since the implications only change at loc and loc is not connected to loc',
            @{term union_frontiers} doesn't change.\<close>
        moreover from p loc sum have "union_frontiers c1 loc' = union_frontiers c0 loc'"
          by (auto intro!: sum.cong arg_cong[where f = Sum])
        ultimately have
          "zcount (c_imp c1 loc' + c_work c1 loc') t'
           = zcount (zmset_frontier (c_pts c1 loc') + union_frontiers c1 loc') t'"
          by simp
      }
      moreover
      { assume sum: "summary loc loc' \<noteq> {}\<^sub>A"
          \<comment> \<open>@{term union_frontiers} at loc' changed by whatever amount the frontier changed.\<close>
        note iiws
          unchanged_imps
          unchanged_ps
        moreover from p' sum have
          "union_frontiers c1 loc' =
           union_frontiers c0 loc'
            + after_summary
                (zmset_frontier (c_imp c1 loc) - zmset_frontier (c_imp c0 loc))
                (summary loc loc')"
          by (auto intro!: next_p_union_frontier_change)
            \<comment> \<open>The worklist at loc' changed by the same amount\<close>
        moreover from p' sum have
          "c_work c1 loc' =
           c_work c0 loc'
            + after_summary
                (zmset_frontier (c_imp c1 loc) - zmset_frontier (c_imp c0 loc))
                (summary loc loc')"
          by (auto intro!: next_p_frontier_change)
            \<comment> \<open>The two changes cancel out.\<close>
        ultimately have
          "zcount (c_imp c1 loc' + c_work c1 loc') t'
         = zcount (zmset_frontier (c_pts c1 loc') + union_frontiers c1 loc') t'"
          by simp
      }
      ultimately have
        "zcount (c_imp c1 loc' + c_work c1 loc') t'
         = zcount (zmset_frontier (c_pts c1 loc') + union_frontiers c1 loc') t'"
        by auto
    }
    ultimately have
      "zcount (c_imp c1 loc' + c_work c1 loc') t'
         = zcount (zmset_frontier (c_pts c1 loc') + union_frontiers c1 loc') t'"
      by (cases "loc=loc'") auto
  }
  with assms show ?thesis
    by (auto simp: next_propagate'_def Let_def inv_imps_work_sum_zcount inv_imps_work_sum_zcount_def)
qed

lemma next_preserves_inv_imps_work_sum:
  assumes "next s"
    and   "holds inv_imps_work_sum s"
  shows   "nxt (holds inv_imps_work_sum) s"
  using assms
    cm_preserves_inv_imps_work_sum
    p_preserves_inv_imps_work_sum
  by (simp, cases rule: next'_inv)

lemma spec_imp_iiws: "spec s \<Longrightarrow> alw (holds inv_imps_work_sum) s"
  using init_imp_inv_imps_work_sum next_preserves_inv_imps_work_sum
  by (auto intro: alw_invar simp: alw_mono spec_def)

subsubsection\<open>Invariant: @{term inv_imp_plus_work_nonneg}\<close>

text \<open>There is never an update in the worklist that could cause implications to become negative.\<close>
definition inv_imp_plus_work_nonneg where
  "inv_imp_plus_work_nonneg c \<equiv> \<forall>loc t. 0 \<le> zcount (c_imp c loc) t + zcount (c_work c loc) t"

lemma iiws_imp_iipwn:
  assumes "inv_imps_work_sum c"
  shows "inv_imp_plus_work_nonneg c"
proof -
  {
    fix loc
    fix t
    assume "inv_imps_work_sum c"
    then have iiws': "inv_imps_work_sum_zcount c"
      by (simp add: inv_imps_work_sum_zcount)
    note iiws = iiws'[unfolded inv_imps_work_sum_zcount_def, THEN spec2]
    have "0 \<le> zcount (union_frontiers c loc) t"
      by (simp add: union_frontiers_nonneg)
    with iiws have "0 \<le> zcount (c_imp c loc + c_work c loc) t"
      by simp
  }
  with assms show ?thesis
    by (simp add: inv_imp_plus_work_nonneg_def)
qed

lemma spec_imp_iipwn: "spec s \<Longrightarrow> alw (holds inv_imp_plus_work_nonneg) s"
  using spec_imp_iiws iiws_imp_iipwn
    alw_mono holds_mono
  by blast


subsubsection\<open>Invariant: @{term inv_implications_nonneg}\<close>

lemma init_imp_inv_implications_nonneg:
  assumes "init_config c"
  shows   "inv_implications_nonneg c"
  using assms by (simp add: init_config_def inv_implications_nonneg_def)

lemma cm_preserves_inv_implications_nonneg:
  assumes "next_change_multiplicity' c0 c1 loc t n"
    and     "inv_implications_nonneg c0"
  shows   "inv_implications_nonneg c1"
  using assms by (simp add: next_change_multiplicity'_def inv_implications_nonneg_def)

lemma p_preserves_inv_implications_nonneg:
  assumes "next_propagate' c0 c1 loc t"
    and     "inv_implications_nonneg c0"
    and     "inv_imp_plus_work_nonneg c0"
  shows   "inv_implications_nonneg c1"
  using assms
  by (auto simp: next_propagate'_def Let_def inv_implications_nonneg_def inv_imp_plus_work_nonneg_def)

lemma next_preserves_inv_implications_nonneg:
  assumes "next s"
    and     "holds inv_implications_nonneg s"
    and     "holds inv_imp_plus_work_nonneg s"
  shows   "nxt (holds inv_implications_nonneg) s"
  using assms
    cm_preserves_inv_implications_nonneg
    p_preserves_inv_implications_nonneg
  by (simp, cases rule: next'_inv)

lemma alw_inv_implications_nonneg: "spec s \<Longrightarrow> alw (holds inv_implications_nonneg) s"
  apply (frule spec_imp_iipwn)
  unfolding spec_def
  apply (rule alw_invar)
  using init_imp_inv_implications_nonneg apply auto []
  using next_preserves_inv_implications_nonneg
  apply (metis (no_types, lifting) alw_iff_sdrop)
  done

lemma after_summary_Diff: "after_summary (M - N) S = after_summary M S - after_summary N S"
  by (simp add: sum_subtractf after_summary_def)

lemma mem_zmset_frontier: "x \<in>#\<^sub>z zmset_frontier M \<longleftrightarrow> x \<in>\<^sub>A frontier M"
  by transfer simp

lemma obtain_frontier_elem:
  assumes "0 < zcount M t"
  obtains u where "u \<in>\<^sub>A frontier M" "u \<le> t"
  using assms by (atomize_elim, transfer)
    (auto simp: minimal_antichain_def dest: order_zmset_exists_foundation)

lemma frontier_unionD: "t \<in>\<^sub>A frontier (M+N) \<Longrightarrow> 0 < zcount M t \<or> 0 < zcount N t"
  by transfer' (auto simp: minimal_antichain_def)

lemma ps_frontier_in_imps_wl:
  assumes "inv_imps_work_sum c"
    and   "0 < zcount (zmset_frontier (c_pts c loc)) t"
  shows   "0 < zcount (c_imp c loc + c_work c loc) t"
proof -
  have "0 \<le> zcount (union_frontiers c loc) t"
    by (rule union_frontiers_nonneg)
  with assms(2) show ?thesis
    using assms(1)[unfolded inv_imps_work_sum_def, THEN spec, of loc]
    by fastforce
qed

lemma obtain_elem_frontier:
  assumes "0 < zcount M t"
  obtains s where "s \<le> t \<and> s \<in>\<^sub>A frontier M"
  by (rule order_finite_set_obtain_foundation[of "{s. zcount M s > 0}" t thesis])
    (auto simp: assms antichain_inverse frontier_def member_antichain.rep_eq
      in_minimal_antichain)

lemma obtain_elem_zmset_frontier:
  assumes "0 < zcount M t"
  obtains s where "s \<le> t \<and> 0 < zcount (zmset_frontier M) s"
  using assms by (auto simp: member_antichain.rep_eq intro: obtain_elem_frontier)

lemma ps_in_imps_wl:
  assumes "inv_imps_work_sum c"
    and   "0 < zcount (c_pts c loc) t"
  obtains s where "s \<le> t \<and> 0 < zcount (c_imp c loc + c_work c loc) s"
proof atomize_elim
  note iiws = assms(1)[unfolded inv_imps_work_sum_def, THEN spec, of loc]
  obtain u where u: " u \<le> t \<and> u \<in>\<^sub>A frontier (c_pts c loc)"
    using assms(2) obtain_elem_frontier by blast
  with assms(1) have "0 < zcount (c_imp c loc + c_work c loc) u"
    apply (intro ps_frontier_in_imps_wl[of c loc u])
     apply (auto intro: iffD1[OF member_antichain.rep_eq])
    done
  with u show "\<exists>s\<le>t. 0 < zcount (c_imp c loc + c_work c loc) s"
    by (auto intro: exI[of _ u])
qed

lemma zero_le_after_summary_single[simp]: "0 \<le> zcount (after_summary {#t#}\<^sub>z S) x"
  by (auto intro: zero_le_sum_single simp: after_summary_def)

lemma one_le_zcount_after_summary: "s \<in>\<^sub>A S \<Longrightarrow> 1 \<le> zcount (after_summary {#t#}\<^sub>z S) (results_in t s)"
  unfolding image_zmset_single after_summary_def
  apply (subst zcount_sum)
  apply (subst forw_subst[of 1 "zcount {#results_in t s#}\<^sub>z (results_in t s)"])
    apply simp
   apply (rule sum_nonneg_leq_bound[of "set_antichain S" "\<lambda>u. zcount {#results_in t u#}\<^sub>z (results_in t s)" _ s])
      apply (auto simp: member_antichain.rep_eq)
  done

lemma zero_lt_zcount_after_summary: "s \<in>\<^sub>A S \<Longrightarrow> 0 < zcount (after_summary {#t#}\<^sub>z S) (results_in t s)"
  apply (subst int_one_le_iff_zero_less[symmetric])
  apply (intro one_le_zcount_after_summary)
  apply simp
  done

lemma pos_zcount_after_summary:
  "(\<And>t. 0 \<le> zcount M t) \<Longrightarrow> 0 < zcount M t \<Longrightarrow> s \<in>\<^sub>A S \<Longrightarrow> 0 < zcount (after_summary M S) (results_in t s)"
  by (auto intro!: sum_pos2 pos_zcount_image_zmset simp: member_antichain.rep_eq zcount_sum after_summary_def)

lemma after_summary_nonneg: "(\<And>t. 0 \<le> zcount M t) \<Longrightarrow> 0 \<le> zcount (after_summary M S) t"
  by (auto simp: zcount_sum after_summary_def intro: sum_nonneg)

lemma after_summary_zmset_of_nonneg[simp, intro]: "0 \<le> zcount (after_summary (zmset_of M) S) t"
  by (simp add: mset_neg_image_zmset mset_neg_sum_set mset_neg_zcount_nonneg after_summary_def)

lemma pos_zcount_union_frontiers:
  "zcount (after_summary (zmset_frontier (c_imp c l1)) (summary l1 l2)) (results_in t s)
    \<le> zcount (union_frontiers c l2) (results_in t s)"
  apply (subst zcount_sum)
  apply (rule member_le_sum)
    apply (auto intro!: pos_zcount_image_zmset)
  done

lemma after_summary_Sum_fun: "finite MM \<Longrightarrow> after_summary (\<Sum>M\<in>MM. f M) A = (\<Sum>M\<in>MM. after_summary (f M) A)"
  by (induct MM rule: finite_induct) (auto simp: after_summary_union)

lemma after_summary_obtain_pre:
  assumes "\<And>t. 0 \<le> zcount M t" (* could prove without this assumption *)
    and   "0 < zcount (after_summary M S) t"
  obtains t' s where "0 < zcount M t'" "results_in t' s = t" "s \<in>\<^sub>A S"
  using assms unfolding after_summary_def
  apply atomize_elim
  apply (subst (asm) zcount_sum)
  apply (drule sum_pos_ex_elem_pos)
  apply clarify
  subgoal for s
    apply (subst ex_comm)
    apply (rule exI[of _ s])
    apply (drule pos_image_zmset_obtain_pre[rotated])
     apply simp
    apply (simp add: member_antichain.rep_eq)
    done
  done

lemma empty_antichain[dest]: "x \<in>\<^sub>A antichain {} \<Longrightarrow> False"
  by (metis empty_antichain.abs_eq mem_antichain_nonempty)

definition impWitnessPath where
  "impWitnessPath c loc1 loc2 xs t = (
    path loc1 loc2 xs \<and>
    distinct xs \<and>
    (\<exists>t'. t' \<in>\<^sub>A frontier (c_imp c loc1) \<and> t = results_in t' (sum_path_weights xs) \<and>
    (\<forall>k<length xs. (\<exists>t. t \<in>\<^sub>A frontier (c_imp c (TO (xs ! k))) \<and> t = results_in t' (sum_path_weights (take (k+1) xs))))))"

lemma impWitnessPathEx:
  assumes "t \<in>\<^sub>A frontier (c_imp c loc2)"
  shows "(\<exists>loc1 xs. impWitnessPath c loc1 loc2 xs t)"
proof -
  have 1: "path loc2 loc2 []" by (simp add: path0)
  have 2: "distinct []" by auto
  have "0 = sum_path_weights []" using foldr_Nil list.map(1) by auto
  then have 3: "t = results_in t (sum_path_weights [])" by (simp add: results_in_zero)
  with 1 2 assms show ?thesis
    unfolding impWitnessPath_def
    by (force simp: results_in_zero)
qed

definition longestImpWitnessPath where
  "longestImpWitnessPath  c loc1 loc2 xs t = (
  impWitnessPath c loc1 loc2 xs t \<and>
  (\<forall>loc' xs'. impWitnessPath c loc' loc2 xs' t \<longrightarrow> length (xs') \<le> length (xs)))"

lemma finite_edges: "finite {(loc1,s,loc2). s \<in>\<^sub>A summary loc1 loc2}"
proof -
  let ?sums = "(\<Union> ((\<lambda>(loc1,loc2). set_antichain (summary loc1 loc2)) ` UNIV))"
  have "finite ?sums"
    by auto
  then have "finite ((UNIV::'loc set) \<times> ?sums \<times> (UNIV::'loc set))"
    by auto
  moreover have "{(loc1,s,loc2). s \<in>\<^sub>A summary loc1 loc2} \<subseteq> ((UNIV::'loc set) \<times> ?sums \<times> (UNIV::'loc set))"
    by (force simp: member_antichain.rep_eq)
  ultimately show ?thesis
    by (rule rev_finite_subset)
qed

lemma longestImpWitnessPathEx:
  assumes "t \<in>\<^sub>A frontier (c_imp c loc2)"
  shows "(\<exists>loc1 xs. longestImpWitnessPath c loc1 loc2 xs t)"
proof -
  define paths where "paths = {(loc1, xs). impWitnessPath c loc1 loc2 xs t}"
  with impWitnessPathEx[OF assms] obtain p where "p \<in> paths" by auto
  have "\<forall>p. p \<in> paths \<longrightarrow> (length \<circ> snd) p  < card {(loc1,s,loc2). s \<in>\<^sub>A summary loc1 loc2} + 1"
  proof (intro allI impI)
    fix p
    assume p:  "p \<in> paths"
    then show "(length \<circ> snd) p < card {(loc1,s,loc2). s \<in>\<^sub>A summary loc1 loc2} + 1"
      by (auto simp: paths_def impWitnessPath_def less_Suc_eq_le finite_edges path_edge
          dest!: distinct_card[symmetric] intro!: card_mono)
  qed
  from ex_has_greatest_nat[OF \<open>p \<in> paths\<close> this] show ?thesis
    by (auto simp: paths_def longestImpWitnessPath_def)
qed

lemma path_first_loc: "path l1 l2 xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> xs ! 0 = (l1',s,l2') \<Longrightarrow> l1 = l1'"
proof (induct arbitrary: l1' s l2 rule: path.induct)
  case (path0 l1 l2)
  then show ?case by auto
next
  case (path l1 l2 xs lbl l3)
  then show ?case
    apply (cases "xs=[]")
     apply (auto elim: path0E) []
    apply (rule path(2)[of l1' s])
    by (auto simp: nth_append)
qed

lemma find_witness_from_frontier:
  assumes "t \<in>\<^sub>A frontier (c_imp c loc2)"
    and "inv_imps_work_sum c"
  shows "\<exists>t' loc1 xs. (path loc1 loc2 xs \<and> t =  results_in t' (sum_path_weights xs) \<and>
           (t' \<in>\<^sub>A frontier (c_pts c loc1) \<or> 0 > zcount (c_work c loc1) t'))"
proof -
  obtain loc1 xs where longestP: "longestImpWitnessPath c loc1 loc2 xs t"
    using assms(1) longestImpWitnessPathEx by blast
  then obtain t' where t': "t' \<in>\<^sub>A frontier (c_imp c loc1)" "t = results_in t' (sum_path_weights xs)"
    "(\<forall>k<length xs. (\<exists>t. t \<in>\<^sub>A frontier (c_imp c (TO (xs ! k))) \<and> t = results_in t' (sum_path_weights (take (k+1) xs))))"
    by (auto simp add: longestImpWitnessPath_def impWitnessPath_def)
  from t'(1) have cases: "0 > zcount (c_work c loc1) t' \<or>
             (t' \<in>#\<^sub>z (zmset_frontier (c_pts c loc1) + union_frontiers c loc1))"
    using assms(2)
    apply (clarsimp intro!: verit_forall_inst(6) simp: inv_imps_work_sum_def not_less)
    apply (metis add_pos_nonneg mem_zmset_frontier member_frontier_pos_zmset obtain_frontier_elem zcount_empty zcount_ne_zero_iff zcount_union zmset_frontier_empty)
    done
  then show ?thesis
  proof cases
    assume case1: "0 > zcount (c_work c loc1) t'"
    then show ?thesis  using t' longestP
      using impWitnessPath_def longestImpWitnessPath_def dataflow_topology_axioms by blast
  next
    assume case2: "\<not>0 > zcount (c_work c loc1) t'"
    have "(t' \<in>#\<^sub>z (zmset_frontier (c_pts c loc1) + union_frontiers c loc1))"
      using case2 cases by auto
    then have case_split2: "(t' \<in>#\<^sub>z zmset_frontier (c_pts c loc1)) \<or> (t' \<in>#\<^sub>z union_frontiers c loc1)"
      by (metis (no_types, lifting) add_diff_cancel_left' in_diff_zcount zcount_ne_zero_iff)
    then show ?thesis
    proof cases
      assume case2_1: "t' \<in>#\<^sub>z zmset_frontier (c_pts c loc1)"
      have "t' \<in>\<^sub>A frontier (c_pts c loc1)"
        using case2_1 mem_zmset_frontier by blast
      then show ?thesis
        using t' impWitnessPath_def longestImpWitnessPath_def dataflow_topology_axioms longestP by blast
    next
      assume "\<not>t' \<in>#\<^sub>z zmset_frontier (c_pts c loc1)"
      then have case2_2: "t' \<in>#\<^sub>z  union_frontiers c loc1" using case_split2 by blast
      then obtain loc0 t0 s0 where loc0 : "t0 \<in>\<^sub>A frontier (c_imp c loc0)"
        "s0 \<in>\<^sub>A (summary loc0 loc1)"
        "t' = results_in t0 s0"
        by (fastforce simp: after_summary_def set_zmset_def zcount_sum
            member_antichain.rep_eq[symmetric] zcount_image_zmset card_gt_0_iff
            simp del: zcount_ne_zero_iff
            elim!: sum.not_neutral_contains_not_neutral)
      let ?xs' = "(loc0, s0, loc1) # xs"
      have path_xs: "path loc1 loc2 xs"
        using impWitnessPath_def longestImpWitnessPath_def longestP by blast
      have is_path_xs': "path loc0 loc2 ?xs'" using longestP
        apply (simp add: longestImpWitnessPath_def impWitnessPath_def)
        by (metis append_Cons append_Nil path_singleton path_trans loc0(2))
      have "\<forall>k<length ?xs'.
              results_in t0 (sum_path_weights (take (k+1) ?xs'))
              \<in>\<^sub>A frontier (c_imp c (TO (?xs' ! k)))"
        apply clarify
        subgoal for k
          apply (cases "k=0")
          subgoal
            using loc0(3) t'(1) by (auto simp: results_in_zero)
          subgoal
            using t'(3)[rule_format, unfolded loc0(3) followed_by_summary, of "k-1", simplified]
            by auto
          done
        done
      note r = this[rule_format]
      have distinctxs: "distinct xs"
        using longestP
        by (simp add: longestImpWitnessPath_def impWitnessPath_def)
      then show ?thesis
      proof cases
        assume case_distinct: "distinct ?xs'"
          (* show that we have a longer longestImpWitnessPathEx \<longrightarrow> contradicition *)
        have "t = results_in t0 (sum_path_weights ?xs')" using longestP loc0(3)
          apply (simp add: longestImpWitnessPath_def impWitnessPath_def)
          by (simp add: followed_by_summary t'(2))
        then have impPath: "impWitnessPath c loc0 loc2 ?xs' t"
          using is_path_xs' case_distinct loc0(1)
          apply (simp add: impWitnessPath_def)
          using r by auto
        have "length ?xs' > length xs" by auto
        then have "\<not> longestImpWitnessPath c loc1 loc2 xs t"
          using impPath leD unfolding longestImpWitnessPath_def by blast
        then show ?thesis using longestP by blast
      next
        assume "\<not> distinct ?xs'"
          (* show that we have a non-increasing cycle along path (loc0, s0, loc1) # xs *)
        with distinctxs obtain k where k: "TO (?xs' ! k) = loc0" "k < length ?xs'"
          apply atomize_elim
          apply clarsimp
          apply (subst (asm) in_set_conv_nth)
          apply clarify
          subgoal for i
            apply (cases "i=0")
            subgoal
              using path_first_loc[OF path_xs]
              by force
            subgoal
              apply (rule exI[of _ i])
              using path_xs
              apply (auto dest: path_to_eq_from[of _ _ xs "i-1"])
              done
            done
          done
        have "results_in t0 (sum_path_weights (take (k+1) ?xs')) \<in>\<^sub>A frontier (c_imp c loc0)"
          by (rule r[OF k(2), unfolded k(1)])
        moreover have "t0 < results_in t0 (sum_path_weights (take (k+1) ?xs'))"
          apply simp
          apply (rule no_zero_cycle[of loc0 "take (k+1) ?xs'" "sum_path_weights (take (k+1) ?xs')" t0, simplified])
          using is_path_xs' k  path_take_to by fastforce
        ultimately show ?thesis
          using loc0(1) frontier_comparable_False by blast
      qed
    qed
  qed
qed

lemma implication_implies_pointstamp:
  assumes "t \<in>\<^sub>A frontier (c_imp c loc)"
    and   "inv_imps_work_sum c"
  shows   "\<exists>t' loc' s. s \<in>\<^sub>A path_summary loc' loc \<and> t \<ge> results_in t' s \<and>
               (t' \<in>\<^sub>A frontier (c_pts c loc') \<or> 0 > zcount (c_work c loc') t')"
proof -
  obtain loc' t' xs where witness:
    "path loc' loc xs"
    "t = results_in t' (sum_path_weights xs)"
    "t' \<in>\<^sub>A frontier (c_pts c loc') \<or> 0 > zcount (c_work c loc') t'"
    using assms find_witness_from_frontier by blast
  obtain s where s: "s \<in>\<^sub>A path_summary loc' loc"  "s \<le> (sum_path_weights xs)"
    using witness(1) path_path_weight by blast
  then have "t \<ge> results_in t' s"
    using witness(2) results_in_mono(2) by blast
  then show ?thesis
    using witness(3) s by auto
qed


subsection\<open>Proof of Safety\<close>

lemma results_in_sum_path_weights_append:
  "results_in t (sum_path_weights (xs @ [(loc2, s, loc3)])) = results_in (results_in t (sum_path_weights xs)) s"
  by (metis followed_by_summary sum_path_weights_append_singleton)

context
  fixes c :: "('loc, 't) configuration"
begin

inductive loc_imps_fw where
  "loc_imps_fw loc loc (c_imp c loc) []" |
  "loc_imps_fw loc1 loc2 M xs \<Longrightarrow> s \<in>\<^sub>A summary loc2 loc3 \<Longrightarrow> distinct (xs @ [(loc2,s,loc3)]) \<Longrightarrow>
   loc_imps_fw loc1 loc3 ({# results_in t s. t \<in>#\<^sub>z M #} + c_imp c loc3) (xs @ [(loc2,s,loc3)])"

end

lemma loc_imps_fw_conv_path: "loc_imps_fw c loc1 loc2 M xs \<Longrightarrow> path loc1 loc2 xs"
  by (induct rule: loc_imps_fw.induct) (auto intro: path.intros)

lemma path_conv_loc_imps_fw: "path loc1 loc2 xs \<Longrightarrow> distinct xs \<Longrightarrow> \<exists>M. loc_imps_fw c loc1 loc2 M xs"
proof (induct rule: path.induct)
  case (path0 l1 l2)
  then show ?case by (auto intro: loc_imps_fw.intros)
next
  case (path l1 l2 xs lbl l3)
  then obtain M where "loc_imps_fw c l1 l2 M xs"
    by auto
  with path show ?case
    by (force intro: loc_imps_fw.intros(2))
qed

lemma path_summary_conv_loc_imps_fw:
  "s \<in>\<^sub>A path_summary loc1 loc2 \<Longrightarrow> \<exists>M xs. loc_imps_fw c loc1 loc2 M xs \<and> sum_path_weights xs = s"
proof -
  assume path_sum: "s \<in>\<^sub>A path_summary loc1 loc2"
  then obtain M xs where le: "path loc1 loc2 xs" "loc_imps_fw c loc1 loc2 M xs" "sum_path_weights xs \<le> s" "distinct xs"
    apply atomize_elim
    apply (drule path_weight_conv_path)
    apply clarsimp
    apply (drule path_distinct)
    apply clarsimp
    subgoal for ys xs
      apply (rule exI[of _ xs])
      apply (rule conjI, assumption)
      apply (drule path_conv_loc_imps_fw[of loc1 loc2 xs c])
      using subseq_sum_weights_le apply auto
      done
    done
  show ?thesis
  proof (cases "sum_path_weights xs = s")
    case True
    with le show ?thesis by auto
  next
    case False
    with le have "sum_path_weights xs < s"
      by auto
    with le(1) path_sum have False
      by (auto dest: path_weight_conv_path)
    then show ?thesis
      by blast
  qed
qed

lemma image_zmset_id[simp]: "{#x. x \<in>#\<^sub>z M#} = M"
  by transfer (auto simp: equiv_zmset_def)

lemma sum_pos: "finite M \<Longrightarrow> \<forall>x\<in>M. 0 \<le> f x \<Longrightarrow> y \<in> M \<Longrightarrow> 0 < (f y::_::ordered_comm_monoid_add) \<Longrightarrow> 0 < (\<Sum>x\<in>M. f x)"
proof (induct M rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  then show ?case
    by (cases "0 < f x") (auto intro: sum_nonneg add_pos_nonneg add_nonneg_pos)
qed

lemma loc_imps_fw_M_in_implications:
  assumes "loc_imps_fw c loc1 loc2 M xs"
    and   "inv_imps_work_sum c"
    and   "inv_implications_nonneg c"
    and   "\<And>loc. c_work c loc = {#}\<^sub>z"
    and   "0 < zcount M t"
  shows   "\<exists>s. s \<le> t \<and> s \<in>\<^sub>A frontier (c_imp c loc2)"
  using assms(1,5)
proof (induct arbitrary: t rule: loc_imps_fw.induct)
  note iiws = assms(2)[unfolded inv_imps_work_sum_def assms(4), simplified, rule_format]
  case (1 loc t)
  then show ?case
    by (auto elim: obtain_elem_frontier)
next
  note iiws = assms(2)[unfolded inv_imps_work_sum_def assms(4), simplified, rule_format]
  case (2 loc1 loc2 M xs s loc3 t)
  from 2(5) have disj: "0 < zcount {# results_in t s. t \<in>#\<^sub>z M #} t \<or> 0 < zcount (c_imp c loc3) t"
    by auto
  show ?case
  proof -
    { assume "0 < zcount {# results_in t s. t \<in>#\<^sub>z M #} t"
      then obtain t' where t': "results_in t' s = t" "0 < zcount M t'"
        apply atomize_elim
        apply (rule ccontr)
        apply (subst (asm) zcount_image_zmset)
        apply (clarsimp simp: vimage_def)
        apply (metis (mono_tags, lifting) Int_iff mem_Collect_eq sum_pos_ex_elem_pos)
        done
      obtain u where u: "u \<le> t'" "u \<in>\<^sub>A frontier (c_imp c loc2)"
        by atomize_elim (rule 2(2)[OF t'(2)])
      then have riu_le_rit': "results_in u s \<le> t"
        by (simp add: t'(1)[symmetric] results_in_mono)
      from u have "0 < zcount (union_frontiers c loc3) (results_in u s)"
        apply (subst zcount_sum)
        apply (rule sum_pos[where y=loc2])
           apply simp_all [3]
        apply (clarsimp simp: after_summary_def)
        apply (subst zcount_sum)
        apply (rule sum_pos[where y=s])
        using 2(3) apply simp_all [3]
        apply (subst zcount_image_zmset)
        apply simp
        apply (subst card_eq_sum)
        apply (rule sum_pos[where y=u])
           apply simp_all
        done
      then have "0 < zcount (zmset_frontier (c_pts c loc3)) (results_in u s) + zcount (union_frontiers c loc3) (results_in u s)"
        by (auto intro: add_nonneg_pos)
      with riu_le_rit' have ?thesis
        apply (subst (asm) zcount_union[symmetric])
        apply (subst iiws)
        apply (erule obtain_elem_frontier)
        subgoal for u'
          by (auto intro!: exI[of _ u'])
        done
    }
    moreover
    { \<comment> \<open>Same as induction base case\<close>
      assume "0 < zcount (c_imp c loc3) t"
      then have ?thesis
        by (auto elim: obtain_elem_frontier)
    }
    moreover note disj
    ultimately show ?thesis
      by blast
  qed
qed

lemma loc_imps_fw_M_nonneg[simp]:
  assumes "loc_imps_fw c loc1 loc2 M xs"
    and   "inv_implications_nonneg c"
  shows "0 \<le> zcount M t"
  using assms
  by (induct arbitrary: t rule: loc_imps_fw.induct)
    (auto intro!: add_nonneg_nonneg sum_nonneg simp: zcount_image_zmset assms(2)[unfolded inv_implications_nonneg_def])

lemma loc_imps_fw_implication_in_M:
  assumes "inv_imps_work_sum c"
    and   "inv_implications_nonneg c"
    and   "loc_imps_fw c loc1 loc2 M xs"
    and   "0 < zcount (c_imp c loc1) t"
  shows   "0 < zcount M (results_in t (sum_path_weights xs))"
  using assms(3,4)
proof (induct rule: loc_imps_fw.induct)
  note iiws = assms(1)[unfolded inv_imps_work_sum_def assms(3), simplified, rule_format]
  case (1 loc)
  then show ?case
    by (simp add: results_in_zero)
next
  case (2 loc1 loc2 M xs s loc3)
  have "0 < zcount M (results_in t (sum_path_weights xs))"
    by (rule 2(2)[OF 2(5)])
  then show ?case
    apply (subst results_in_sum_path_weights_append)
    apply (subst zcount_union)
    apply (rule add_pos_nonneg)
     apply (subst zcount_image_zmset)
     apply (rule sum_pos[where y = "results_in t (sum_weights (map (\<lambda>(s, l, t). l) xs))"])
        apply simp
       apply (auto simp: loc_imps_fw_M_nonneg[OF 2(1) assms(2)] zcount_inI) [3]
    apply (auto simp: assms(2)[unfolded inv_implications_nonneg_def])
    done
qed

definition impl_safe :: "('loc, 't) configuration \<Rightarrow> bool" where
  "impl_safe c \<equiv> \<forall>loc1 loc2 t s. zcount (c_imp c loc1) t > 0 \<and> s \<in>\<^sub>A path_summary loc1 loc2
                   \<longrightarrow> (\<exists>t'. t' \<in>\<^sub>A frontier (c_imp c loc2) \<and> t' \<le> results_in t s)"

lemma impl_safe:
  assumes "inv_imps_work_sum c"
    and   "inv_implications_nonneg c"
    and   "\<And>loc. c_work c loc = {#}\<^sub>z"
  shows   "impl_safe c"
  unfolding impl_safe_def
  apply clarify
proof -
  note iiws = assms(1)[unfolded inv_imps_work_sum_def assms(3), simplified, rule_format]
  fix loc1 loc2 t s
  assume "0 < zcount (c_imp c loc1) t"
  then obtain t' where t': "t' \<in>\<^sub>A frontier (c_imp c loc1)" "t' \<le> t"
    by (auto elim: obtain_elem_frontier)
  then have t'_zcount: "0 < zcount (c_imp c loc1) t'"
    by (simp add: member_frontier_pos_zmset)
  assume path_sum: "s \<in>\<^sub>A path_summary loc1 loc2"
  obtain M xs where Mxs: "loc_imps_fw c loc1 loc2 M xs" "sum_path_weights xs = s"
    by atomize_elim (rule path_summary_conv_loc_imps_fw[OF path_sum])
  have inM: "0 < zcount M (results_in t' (sum_path_weights xs))"
    by (rule loc_imps_fw_implication_in_M[OF assms(1,2) Mxs(1) t'_zcount])
  obtain u where u: "u \<le> results_in t' (sum_path_weights xs)" "u \<in>\<^sub>A frontier (c_imp c loc2)"
    by atomize_elim (rule loc_imps_fw_M_in_implications[OF Mxs(1) assms(1,2,3) inM])
  then show "\<exists>t'. t' \<in>\<^sub>A frontier (c_imp c loc2) \<and> t' \<le> results_in t s"
    apply (intro exI[of _ u])
    apply (simp add: Mxs(2))
    using t'(2) apply (meson order.trans results_in_mono(1))
    done
qed

\<comment> \<open>Safety for states where worklist is non-empty\<close>

lemma cm_preserves_impl_safe:
  assumes "impl_safe c0"
    and   "next_change_multiplicity' c0 c1 loc t n"
  shows   "impl_safe c1"
  using assms
  by (auto simp: impl_safe_def next_change_multiplicity'_def)

lemma cm_preserves_safe:
  assumes "safe c0"
    and   "impl_safe c0"
    and   "next_change_multiplicity' c0 c1 loc t n"
  shows   "safe c1"
proof -
  from assms(1) have safe: "0 < zcount (c_pts c0 loc1) t \<Longrightarrow> s \<in>\<^sub>A path_summary loc1 loc2
        \<Longrightarrow> \<exists>t'\<le>results_in t s. t' \<in>\<^sub>A frontier (c_imp c0 loc2)" for loc1 loc2 t s
    by (auto simp: safe_def)
  from assms(2) have impl_safe: "0 < zcount (c_imp c0 loc1) t \<Longrightarrow> s \<in>\<^sub>A path_summary loc1 loc2
        \<Longrightarrow> \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c0 loc2) \<and> t' \<le> results_in t s" for loc1 loc2 t s
    by (auto simp: impl_safe_def)
  from assms(3) have imps: "c_imp c1 = c_imp c0"
    unfolding next_change_multiplicity'_def by auto
  { fix loc1 loc2 u s \<comment> \<open>`safe c1` variables\<close>
    assume u: "0 < zcount (c_pts c1 loc1) u"
    then obtain u' where u': "u' \<in>\<^sub>A frontier (c_pts c1 loc1)" "u' \<le> u"
      using obtain_frontier_elem by blast
    assume path_sum: "s \<in>\<^sub>A path_summary loc1 loc2"
      \<comment> \<open>CM state changes:\<close>
    assume n_neq_zero: "n \<noteq> 0"
    assume impl: "\<exists>t'. t' \<in>\<^sub>A frontier (c_imp c0 loc) \<and> t' \<le> t"
    assume pointstamps:
      "\<forall>loc'. c_pts c1 loc' =
                    (if loc' = loc then update_zmultiset (c_pts c0 loc') t n
                                   else c_pts c0 loc')"
    have "\<exists>t'\<le>results_in u s. t' \<in>\<^sub>A frontier (c_imp c1 loc2)"
    proof (cases "n < 0")
      case True \<comment> \<open>Trivial, because no new pointstamp could have appeared\<close>
      with u have u_c0: "0 < zcount (c_pts c0 loc1) u"
        unfolding pointstamps[rule_format]
        by (cases "loc1=loc"; cases "t=u") (auto simp: zcount_update_zmultiset)
      show ?thesis
        unfolding imps
        by (rule safe[OF u_c0 path_sum])
    next
      case False
      with n_neq_zero have "n > 0"
        by linarith
      then show ?thesis
        unfolding imps
        apply (cases "loc=loc1"; cases "t=u")
        using impl
           apply (elim exE conjE)
        subgoal for t'
          apply simp
          apply (drule member_frontier_pos_zmset)
          apply (drule impl_safe[rotated, OF path_sum])
          apply (elim exE)
          subgoal for t''
            apply (rule exI[of _ t''])
            using results_in_mono(1) order_trans apply blast
            done
          done
        using u path_sum apply (auto simp: zcount_update_zmultiset pointstamps[rule_format] intro: safe)
        done
    qed
  }
  note r = this
  show ?thesis
    unfolding safe_def
    apply clarify
    subgoal for loc1 loc2 t s
      using assms(3)[unfolded next_change_multiplicity'_def]
      by (intro r[of loc1 t s loc2]) auto
    done
qed

subsection\<open>A Better (More Invariant) Safety\<close>

definition worklists_vacant_to :: "('loc, 't) configuration \<Rightarrow> 't \<Rightarrow> bool" where
  "worklists_vacant_to c t =
    (\<forall>loc1 loc2 s t'. s \<in>\<^sub>A path_summary loc1 loc2 \<and> t' \<in>#\<^sub>z c_work c loc1 \<longrightarrow> \<not> results_in t' s \<le> t)"

definition inv_safe :: "('loc, 't) configuration \<Rightarrow> bool" where
  "inv_safe c = (\<forall>loc1 loc2 t s. 0 < zcount (c_pts c loc1) t
                            \<and> s \<in>\<^sub>A path_summary loc1 loc2
                            \<and> worklists_vacant_to c (results_in t s)
                \<longrightarrow> (\<exists>t' \<le> results_in t s. t' \<in>\<^sub>A frontier (c_imp c loc2)))"

text\<open>Intuition: Unlike safe, @{term inv_safe} is an invariant because it only claims the safety property
@{term "t' \<in>\<^sub>A frontier (c_imp c loc2)"} for pointstamps that can't be modified by future propagated
updates anymore (i.e. there are no upstream worklist entries which can result in a less or equal pointstamp).\<close>

lemma in_frontier_diff: "\<forall>y\<in>#\<^sub>zN. \<not> y \<le> x \<Longrightarrow> x \<in>\<^sub>A frontier (M - N) \<longleftrightarrow> x \<in>\<^sub>A frontier M"
  apply transfer'
  unfolding in_minimal_antichain
  apply (metis (mono_tags, lifting) diff_zero le_less mem_Collect_eq set_zmset_def zcount_diff)
  done

lemma worklists_vacant_to_trans:
  "worklists_vacant_to c t \<Longrightarrow> t' \<le> t \<Longrightarrow> worklists_vacant_to c t'"
  unfolding worklists_vacant_to_def
  using order.trans by blast

lemma loc_imps_fw_M_in_implications':
  assumes "loc_imps_fw c loc1 loc2 M xs"
    and   "inv_imps_work_sum c"
    and   "inv_implications_nonneg c"
    and   "worklists_vacant_to c t"
    and   "0 < zcount M t"
  shows   "\<exists>s\<le>t. s \<in>\<^sub>A frontier (c_imp c loc2)"
  using assms(1,4,5)
proof (induct arbitrary: t rule: loc_imps_fw.induct)
  note iiws = assms(2)[unfolded inv_imps_work_sum_def, rule_format]
  case (1 loc t)
  then show ?case
    by (auto elim: obtain_elem_frontier)
next
  note iiws = assms(2)[unfolded inv_imps_work_sum_def eq_diff_eq[symmetric], rule_format]
  case (2 loc1 loc2 M xs s loc3 t)
  from 2(6) consider "0 < zcount {# results_in t s. t \<in>#\<^sub>z M #} t" | "0 < zcount (c_imp c loc3) t"
    by atomize_elim auto
  then show ?case
  proof cases
    case 1
    then obtain t' where t': "results_in t' s = t" "0 < zcount M t'"
      apply atomize_elim
      apply (rule ccontr)
      apply (subst (asm) zcount_image_zmset)
      apply (clarsimp simp: vimage_def)
      apply (metis (mono_tags, lifting) Int_iff mem_Collect_eq sum_pos_ex_elem_pos)
      done
    have vacant_to: "worklists_vacant_to c t'"
      apply (rule worklists_vacant_to_trans)
       apply (rule 2(5))
      using zero_le results_in_mono(2) results_in_zero t'(1) apply fastforce
      done
    obtain u where u: "u \<le> t'" "u \<in>\<^sub>A frontier (c_imp c loc2)"
      using 2(2)[OF vacant_to t'(2)] by fast
    then have riu_le_rit': "results_in u s \<le> t"
      by (simp add: t'(1)[symmetric] results_in_mono)
    from u have "0 < zcount (union_frontiers c loc3) (results_in u s)"
      apply (subst zcount_sum)
      apply (rule sum_pos[where y=loc2])
         apply simp_all [3]
      apply (clarsimp simp: after_summary_def)
      apply (subst zcount_sum)
      apply (rule sum_pos[where y=s])
      using 2(3) apply simp_all [3]
      apply (subst zcount_image_zmset)
      apply simp
      apply (subst card_eq_sum)
      apply (rule sum_pos[where y=u])
         apply simp_all
      done
    then have "0 < zcount (zmset_frontier (c_pts c loc3)) (results_in u s) + zcount (union_frontiers c loc3) (results_in u s)"
      by (auto intro: add_nonneg_pos)
    with riu_le_rit' show ?thesis
      apply (subst (asm) zcount_union[symmetric])
      apply (subst iiws)
      apply (erule obtain_elem_frontier)
      subgoal for u'
        apply (rule exI[of _ u'])
        apply (subst in_frontier_diff)
         apply clarify
        subgoal for t'
          using 2(5)[unfolded worklists_vacant_to_def, rule_format, of 0 loc3 loc3 t']
          apply -
          apply (drule meta_mp)
           apply (intro conjI)
            apply simp
           apply simp
          apply (metis order_trans results_in_zero)
          done
        apply auto
        done
      done
  next
    case 2
    then show ?thesis
      by (auto elim: obtain_elem_frontier)
  qed
qed

lemma inv_safe:
  assumes "inv_imps_work_sum c"
    and   "inv_implications_nonneg c"
  shows   "inv_safe c"
  unfolding inv_safe_def
  apply clarify
proof -
  note iiws = assms(1)[unfolded inv_imps_work_sum_def, rule_format]
  fix loc1 loc2 t s
  assume vacant: "worklists_vacant_to c (results_in t s)"
  assume "0 < zcount (c_pts c loc1) t"
  then obtain t' where t': "t' \<in>\<^sub>A frontier (c_pts c loc1)" "t' \<le> t"
    using obtain_frontier_elem by blast
  have zcount_wl: "zcount (c_work c loc1) t' = 0"
    using vacant[unfolded worklists_vacant_to_def, rule_format, of 0 loc1 loc1 t', simplified]
    by (metis add.left_neutral order.trans le_plus(1) results_in_mono(2) results_in_zero t'(2) zcount_ne_zero_iff)
  obtain t'' where t'': "t'' \<in>\<^sub>A frontier (c_imp c loc1)" "t'' \<le> t'"
  proof atomize_elim
    from t'(1) have "0 < zcount (zmset_frontier (c_pts c loc1)) t' + zcount (union_frontiers c loc1) t'"
      by (auto intro: add_pos_nonneg simp: union_frontiers_nonneg)
    then show "\<exists>t''. t'' \<in>\<^sub>A frontier (c_imp c loc1) \<and> t'' \<le> t'"
      apply (subst (asm) zcount_union[symmetric])
      apply (subst (asm) iiws[symmetric])
      using zcount_wl
      apply (auto elim: obtain_frontier_elem)
      done
  qed
  then have t''_zcount: "0 < zcount (c_imp c loc1) t''"
    by (simp add: member_frontier_pos_zmset)
  assume path_sum: "s \<in>\<^sub>A path_summary loc1 loc2"
  obtain M xs where Mxs: "loc_imps_fw c loc1 loc2 M xs" "sum_path_weights xs = s"
    by atomize_elim (rule path_summary_conv_loc_imps_fw[OF path_sum])
  have inM: "0 < zcount M (results_in t'' (sum_path_weights xs))"
    by (rule loc_imps_fw_implication_in_M[OF assms(1,2) Mxs(1) t''_zcount])
  have vacant2: "worklists_vacant_to c (results_in t'' (sum_weights (map (\<lambda>(s, l, t). l) xs)))"
    apply (subst Mxs(2))
    apply (meson results_in_mono(1) worklists_vacant_to_trans t''(2) t'(2) vacant)
    done
  obtain u where u: "u \<le> results_in t'' (sum_path_weights xs)" "u \<in>\<^sub>A frontier (c_imp c loc2)"
    by atomize_elim (rule loc_imps_fw_M_in_implications'[OF Mxs(1) assms(1,2) vacant2 inM])
  then show "\<exists>t'\<le>results_in t s. t' \<in>\<^sub>A frontier (c_imp c loc2)"
    apply (intro exI[of _ u])
    apply (simp add: Mxs(2))
    using t''(2) t'(2) apply (meson order.trans results_in_mono(1))
    done
qed

lemma alw_conjI: "alw P s \<Longrightarrow> alw Q s \<Longrightarrow> alw (\<lambda>s. P s \<and> Q s) s"
  by (coinduction arbitrary: s) auto

lemma alw_inv_safe: "spec s \<Longrightarrow> alw (holds inv_safe) s"
  apply (frule spec_imp_iiws)
  apply (drule alw_inv_implications_nonneg)
  apply (rule alw_mp[where \<phi> = "\<lambda>s. holds inv_imps_work_sum s \<and> holds inv_implications_nonneg s"])
   apply (rule alw_conjI)
    apply assumption+
  apply (simp add: alw_mono inv_safe)
  done

lemma empty_worklists_vacant_to: "\<forall>loc. c_work c loc = {#}\<^sub>z \<Longrightarrow> worklists_vacant_to c t"
  unfolding worklists_vacant_to_def
  by auto

lemma inv_safe_safe: "(\<And>loc. c_work c loc = {#}\<^sub>z) \<Longrightarrow> inv_safe c \<Longrightarrow> safe c"
  unfolding inv_safe_def safe_def worklists_vacant_to_def by auto

lemma safe:
  assumes "inv_imps_work_sum c"
    and   "inv_implications_nonneg c"
    and   "\<And>loc. c_work c loc = {#}\<^sub>z"
  shows   "safe c"
  by (rule inv_safe_safe[OF assms(3) inv_safe[OF assms(1,2)]])

subsection \<open>Implied Frontier\<close>

abbreviation zmset_pos where "zmset_pos M \<equiv> zmset_of (mset_pos M)"

definition implied_frontier where
  "implied_frontier P loc = frontier (\<Sum>loc'\<in>UNIV. after_summary (zmset_pos (P loc')) (path_summary loc' loc))"

definition implied_frontier_alt where
  "implied_frontier_alt c loc = frontier (\<Sum>loc'\<in>UNIV. after_summary (zmset_frontier (c_pts c loc')) (path_summary loc' loc))"

lemma in_frontier_least: "x \<in>\<^sub>A frontier M \<Longrightarrow> \<forall>y. 0 < zcount M y \<longrightarrow> \<not> y < x"
  by transfer' (auto simp: minimal_antichain_def)

lemma in_frontier_trans: "0 < zcount M y \<Longrightarrow> x \<in>\<^sub>A frontier M \<Longrightarrow> y \<le> x \<Longrightarrow> y \<in>\<^sub>A frontier M"
  by transfer (simp add: le_less minimal_antichain_def)

lemma implied_frontier_alt_least:
  assumes "b \<in>\<^sub>A implied_frontier_alt c loc2"
  shows "\<forall>loc a' s'. a' \<in>\<^sub>A frontier (c_pts c loc) \<longrightarrow> s' \<in>\<^sub>A path_summary loc loc2 \<longrightarrow> \<not> results_in a' s' < b"
proof (intro allI impI notI)
  fix loc a' s'
  assume a': "a' \<in>\<^sub>A frontier (c_pts c loc)"
  assume s': "s' \<in>\<^sub>A path_summary loc loc2"
  assume lt: "results_in a' s' < b"
  have "0 < zcount (after_summary (zmset_frontier (c_pts c loc)) (path_summary loc loc2)) (results_in a' s')"
    using a' s' by (auto intro!: pos_zcount_after_summary)
  then have "0 < zcount (\<Sum>loc'\<in>UNIV. after_summary (zmset_frontier (c_pts c loc')) (path_summary loc' loc2)) (results_in a' s')"
    by (auto intro!: sum_pos[where y = loc] simp: zcount_sum)
  then have "results_in a' s' \<in>\<^sub>A implied_frontier_alt c loc2"
    using assms lt unfolding implied_frontier_alt_def
    by (auto dest!: in_frontier_trans[where y = "results_in a' s'" and x = b])
  with lt assms show "False"
    unfolding implied_frontier_alt_def
    using frontier_comparable_False
    by blast
qed

lemma implied_frontier_alt_in_pointstamps:
  assumes "b \<in>\<^sub>A implied_frontier_alt c loc2"
  obtains a s loc1 where
    "a \<in>\<^sub>A frontier (c_pts c loc1)" "s \<in>\<^sub>A path_summary loc1 loc2" "results_in a s = b"
  using assms apply atomize_elim
  unfolding implied_frontier_alt_def
  apply (drule member_frontier_pos_zmset)
  apply (subst (asm) zcount_sum)
  apply (drule sum_pos_ex_elem_pos)
  apply clarify
  apply (rule after_summary_obtain_pre[rotated])
    apply simp
  subgoal for loc1 a s
    by (auto intro!: exI[of _ loc1] exI[of _ a] exI[of _ s])
  apply simp
  done

lemma in_implied_frontier_alt_in_implication_frontier:
  assumes "inv_imps_work_sum c"
    and   "inv_implications_nonneg c"
    and   "worklists_vacant_to c b"
    and   "b \<in>\<^sub>A implied_frontier_alt c loc2"
  shows   "b \<in>\<^sub>A frontier (c_imp c loc2)"
proof -
  have safe: "0 < zcount (c_pts c loc1) t \<Longrightarrow> s \<in>\<^sub>A path_summary loc1 loc2 \<Longrightarrow> results_in t s \<le> b
        \<Longrightarrow> \<exists>t'\<le>results_in t s. t' \<in>\<^sub>A frontier (c_imp c loc2)" for loc1 loc2 t s
    by (rule inv_safe[OF assms(1,2), unfolded inv_safe_def, rule_format])
      (auto elim: worklists_vacant_to_trans[OF assms(3)])
      \<comment> \<open>Pointstamp @{term b} in the @{term implied_frontier_alt} is caused by a pointstamp @{term a} and summary @{term s}
          and @{term "results_in a s"} is least among such pointstamps\<close>
  from assms(4) obtain loc1 a s where loc1_a_s:
    "a \<in>\<^sub>A frontier (c_pts c loc1)" "s \<in>\<^sub>A path_summary loc1 loc2" "results_in a s = b"
    "\<forall>loc a' s'. a' \<in>\<^sub>A frontier (c_pts c loc) \<longrightarrow> s' \<in>\<^sub>A path_summary loc loc2 \<longrightarrow> \<not> results_in a' s' < b"
    apply atomize_elim
    apply (rule implied_frontier_alt_in_pointstamps)
     apply simp
    apply (drule implied_frontier_alt_least)
    apply fast
    done
  then have zcount_ps: "0 < zcount (c_pts c loc1) a"
    using member_frontier_pos_zmset by blast
      \<comment> \<open>From `safe` we know that pointstamp @{term a} is reflected in the implications by some
      poinstamp @{term "b' \<le> b"}\<close>
  obtain b' where b': "b' \<in>\<^sub>A frontier (c_imp c loc2)" "b' \<le> results_in a s"
    using safe[OF zcount_ps loc1_a_s(2)] loc1_a_s(3) by blast
  have "b' = results_in a s"
  proof -
    have "zcount (c_work c loc) t = 0" if "results_in t s \<le> b'" for t s loc
    proof -
      have "results_in t s \<le> b"
        using b'(2) loc1_a_s(3) that by force
      then show ?thesis
        by (meson assms(3) results_in_mono(2) worklists_vacant_to_def flow.zero_le order_trans
            path_weight_refl zcount_inI)
    qed
      \<comment> \<open>but the pointstamp can't be strictly less, because we know that @{term "results_in a s"} is least\<close>
    then obtain a' loc1' s' where a':
      "s' \<in>\<^sub>A path_summary loc1' loc2" "results_in a' s' \<le> b'" "a' \<in>\<^sub>A frontier (c_pts c loc1')"
      using implication_implies_pointstamp[OF b'(1) assms(1), simplified] by force
    { assume "b' \<noteq> results_in a s"
      with b'(2) have b'_lt: "b' < results_in a s"
        by simp
      note loc1_a_s(4)[rule_format, unfolded loc1_a_s(3)[symmetric], OF a'(3,1)]
      with b'_lt a'(2) have False
        by (simp add: leD less_le order_trans)
    }
    then show ?thesis
      by (rule ccontr)
  qed
    \<comment> \<open>Hence, the @{term implied_frontier_alt} pointstamp @{term b} is reflected in the implications\<close>
  with b' show "b \<in>\<^sub>A frontier (c_imp c loc2)"
    by (auto simp: loc1_a_s(3))
qed

lemma in_implication_frontier_in_implied_frontier_alt:
  assumes "inv_imps_work_sum c"
    and   "inv_implications_nonneg c"
    and   "worklists_vacant_to c b"
    and   "b \<in>\<^sub>A frontier (c_imp c loc2)"
  shows   "b \<in>\<^sub>A implied_frontier_alt c loc2"
proof -
  have safe: "0 < zcount (c_pts c loc1) t \<Longrightarrow> s \<in>\<^sub>A path_summary loc1 loc2 \<Longrightarrow> results_in t s \<le> b
        \<Longrightarrow> \<exists>t'\<le>results_in t s. t' \<in>\<^sub>A frontier (c_imp c loc2)" for loc1 loc2 t s
    by (rule inv_safe[OF assms(1,2), unfolded inv_safe_def, rule_format])
      (auto elim: worklists_vacant_to_trans[OF assms(3)])
  have "zcount (c_work c loc) t = 0" if "results_in t s \<le> b" for t s loc
    using that by (meson assms(3) results_in_mono(2) worklists_vacant_to_def flow.zero_le
        order_trans path_weight_refl zcount_inI)
      \<comment> \<open>Pointstamp @{term b} in the implications is caused by a pointstamp @{term a} and a summary @{term s}\<close>
  then obtain loc1 a s where loc1_a_s:
    "s \<in>\<^sub>A path_summary loc1 loc2" "results_in a s \<le> b" "a \<in>\<^sub>A frontier (c_pts c loc1)"
    using implication_implies_pointstamp[OF assms(4) assms(1), simplified] by force
  then have zcount_a: "0 < zcount (c_pts c loc1) a"
    using member_frontier_pos_zmset by blast
  have b_ria: "results_in a s = b"
  proof (rule ccontr)
    assume "results_in a s \<noteq> b"
    with loc1_a_s(2) have "results_in a s < b"
      by simp
    then show False
      using safe[OF zcount_a loc1_a_s(1)] assms(4) loc1_a_s(2)
      using order.strict_trans1 frontier_comparable_False by blast
  qed
    \<comment> \<open>@{term "results_in a s"} is a candidate for inclusion in the @{term implied_frontier_alt}..\<close>
  have "0 < zcount (\<Sum>loc'\<in>UNIV. after_summary (zmset_frontier (c_pts c loc')) (path_summary loc' loc2)) (results_in a s)"
    unfolding after_summary_def
    apply (subst zcount_sum)
    apply (rule sum_pos[of _ _ loc1])
       apply simp
      apply (clarsimp simp: zcount_sum)
      apply (rule sum_nonneg)
      apply (subst zcount_image_zmset)
      apply auto [2]
    apply (subst zcount_sum)
    apply (rule sum_pos[of _ _ s])
    using loc1_a_s(1) apply simp_all [3]
    apply (subst zcount_image_zmset)
    apply (rule sum_pos[of _ _ a])
    using loc1_a_s(3) apply auto
    done
      \<comment> \<open>..which means a pointstamp @{term "b' \<le> results_in a s"} must exist in the @{term implied_frontier_alt}..\<close>
  then obtain b' where b': "b' \<in>\<^sub>A implied_frontier_alt c loc2" "b' \<le> results_in a s"
    by (auto simp: implied_frontier_alt_def elim: obtain_frontier_elem)
  then have "worklists_vacant_to c b'"
    using loc1_a_s(2) by (auto intro: worklists_vacant_to_trans[OF assms(3)])
  with b' have b'_frontier: "b' \<in>\<^sub>A frontier (c_imp c loc2)"
    using in_implied_frontier_alt_in_implication_frontier assms by blast
      \<comment> \<open>..and this pointstamp must be equal to @{term b'}\<close>
  have b'_ria: "b' = results_in a s"
  proof (rule ccontr)
    assume "b' \<noteq> results_in a s"
    with b'(2) have b'_lt: "b' < results_in a s"
      by simp
    from b'_frontier b'_lt b_ria assms(4) show False
      using frontier_comparable_False by blast
  qed
    \<comment> \<open>Hence, the implication frontier pointstamp @{term b} is reflected in the @{term implied_frontier_alt}\<close>
  from b' b'_ria b_ria show "b \<in>\<^sub>A implied_frontier_alt c loc2"
    by (auto simp: implied_frontier_alt_def)
qed

lemma implication_frontier_iff_implied_frontier_alt_vacant:
  assumes "inv_imps_work_sum c"
    and   "inv_implications_nonneg c"
    and   "worklists_vacant_to c b"
  shows   "b \<in>\<^sub>A frontier (c_imp c loc) \<longleftrightarrow> b \<in>\<^sub>A implied_frontier_alt c loc"
  using
    ac_eq_iff
    in_implication_frontier_in_implied_frontier_alt[OF assms]
    in_implied_frontier_alt_in_implication_frontier[OF assms]
  by blast

lemma next_propagate_implied_frontier_alt_def:
  "next_propagate c c' \<Longrightarrow> implied_frontier_alt c loc = implied_frontier_alt c' loc"
  by (auto simp: next_propagate'_def implied_frontier_alt_def)

lemma implication_frontier_eq_implied_frontier_alt:
  assumes "inv_imps_work_sum c"
    and   "inv_implications_nonneg c"
    and   "\<And>loc. c_work c loc = {#}\<^sub>z"
  shows   "frontier (c_imp c loc) = implied_frontier_alt c loc"
  using ac_eq_iff implication_frontier_iff_implied_frontier_alt_vacant empty_worklists_vacant_to assms
  by blast

lemma alw_implication_frontier_eq_implied_frontier_alt_empty: "spec s \<Longrightarrow>
  alw (holds (\<lambda>c. (\<forall>loc. c_work c loc = {#}\<^sub>z) \<longrightarrow> frontier (c_imp c loc) = implied_frontier_alt c loc)) s"
  apply (frule spec_imp_iiws)
  apply (drule alw_inv_implications_nonneg)
  apply (drule (1) alw_conjI)
  apply (erule thin_rl)
  apply (auto elim!: alw_mono simp: implication_frontier_eq_implied_frontier_alt)
  done

lemma alw_implication_frontier_eq_implied_frontier_alt_vacant: "spec s \<Longrightarrow>
  alw (holds (\<lambda>c. worklists_vacant_to c b \<longrightarrow> b \<in>\<^sub>A frontier (c_imp c loc) \<longleftrightarrow> b \<in>\<^sub>A implied_frontier_alt c loc)) s"
  apply (frule spec_imp_iiws)
  apply (drule alw_inv_implications_nonneg)
  apply (drule (1) alw_conjI)
  apply (erule thin_rl)
  apply (auto elim!: alw_mono simp: implication_frontier_iff_implied_frontier_alt_vacant)
  done

lemma antichain_eqI: "(\<And>b. b \<in>\<^sub>A A \<longleftrightarrow> b \<in>\<^sub>A B) \<Longrightarrow> A = B"
  by transfer auto

lemma zmset_frontier_zmset_pos: "zmset_frontier A \<subseteq>#\<^sub>z zmset_pos A"
  unfolding subseteq_zmset_def
  by transfer' (auto simp: count_mset_set_if minimal_antichain_def)

lemma image_mset_mono_pos: 
  "\<forall>b. 0 \<le> zcount A b \<Longrightarrow> \<forall>b. 0 \<le> zcount B b \<Longrightarrow> A \<subseteq>#\<^sub>z B \<Longrightarrow> image_zmset f A \<subseteq>#\<^sub>z image_zmset f B"
  unfolding subseteq_zmset_def zcount_image_zmset
  apply (intro allI)
  apply (rule order_trans[OF sum_mono sum_mono2])
     apply simp_all
  by (metis Int_subset_iff antisym subsetI zcount_ne_zero_iff)

lemma sum_mono_subseteq:
  "(\<And>i. i\<in>K \<Longrightarrow> f i \<subseteq>#\<^sub>z g i) \<Longrightarrow> (\<Sum>i\<in>K. f i) \<subseteq>#\<^sub>z (\<Sum>i\<in>K. g i)"
  by (simp add: subseteq_zmset_def sum_mono zcount_sum)

lemma after_summary_zmset_frontier: 
  "after_summary (zmset_frontier A) S \<subseteq>#\<^sub>z after_summary (zmset_pos A) S"
  unfolding after_summary_def
  apply (rule sum_mono_subseteq)
  apply (rule image_mset_mono_pos[OF _ _ zmset_frontier_zmset_pos])
   apply auto
  done

lemma frontier_eqI: "\<forall>b. 0 \<le> zcount A b \<Longrightarrow> \<forall>b. 0 \<le> zcount B b \<Longrightarrow>
  A \<subseteq>#\<^sub>z B \<Longrightarrow> (\<And>b. b \<in>#\<^sub>z B \<Longrightarrow> \<exists>a. a \<in>#\<^sub>z A \<and> a \<le> b) \<Longrightarrow> frontier A = frontier B"
  apply (transfer fixing: A B)
  apply (clarsimp simp: minimal_antichain_def subseteq_zmset_def)
  apply safe
     apply (metis less_le_trans)
    apply (metis less_le less_le_trans zcount_ne_zero_iff)
   apply (metis antisym less_le zcount_ne_zero_iff)
  apply (meson less_le_trans)
  done

lemma implied_frontier_implied_frontier_alt: "implied_frontier (c_pts c) loc = implied_frontier_alt c loc"
  unfolding implied_frontier_alt_def implied_frontier_def
  apply (rule frontier_eqI[symmetric])
  subgoal by (auto simp: zcount_sum sum_nonneg)
  subgoal by (auto simp: zcount_sum sum_nonneg)
  subgoal by (rule sum_mono_subseteq[OF after_summary_zmset_frontier])
  apply (simp flip: zcount_ne_zero_iff add: zcount_sum)
  apply (erule sum.not_neutral_contains_not_neutral)
  apply (simp flip: zcount_ne_zero_iff add: after_summary_def zcount_sum)
  apply (erule sum.not_neutral_contains_not_neutral)
  apply (simp flip: zcount_ne_zero_iff add: zcount_image_zmset split: if_splits)
  apply (erule sum.not_neutral_contains_not_neutral)
  apply (simp flip: zcount_ne_zero_iff)
  subgoal for u loc s t
    apply (rule obtain_elem_frontier[of "c_pts c loc" t])
    apply (metis le_less)
    subgoal for a
      apply (rule exI[of _ "results_in a s"])
      apply (rule conjI[rotated])
      using results_in_mono(1) apply blast
      apply (subst sum_nonneg_eq_0_iff; simp add: sum_nonneg)
      apply (rule exI[of _ loc])
      apply (subst sum_nonneg_eq_0_iff; simp)
      apply (rule bexI[of _ s])
      apply auto
      done
    done
  done

lemmas alw_implication_frontier_eq_implied_frontier_vacant =
  alw_implication_frontier_eq_implied_frontier_alt_vacant[folded implied_frontier_implied_frontier_alt]
lemmas implication_frontier_iff_implied_frontier_vacant =
  implication_frontier_iff_implied_frontier_alt_vacant[folded implied_frontier_implied_frontier_alt]

end

(*<*)
end
(*>*)