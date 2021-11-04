section \<open>Combined Progress Tracking Protocol\label{sec:combined}\<close>

(*<*)
theory Combined
  imports
    Exchange
    Propagate
begin
(*>*)

lemma fold_invar:
  assumes "finite M"
    and   "P z"
    and   "\<forall>z. \<forall>x\<in>M. P z \<longrightarrow> P (f x z)"
    and   "comp_fun_commute f"
  shows   "P (Finite_Set.fold f z M)"
  using assms by (induct M arbitrary: z rule: finite_induct) (auto simp: comp_fun_commute.fold_insert)

subsection\<open>Could-result-in Relation\<close>

context dataflow_topology begin

definition cri_less_eq :: "('loc \<times> 't) \<Rightarrow> ('loc \<times> 't) \<Rightarrow> bool" ("_\<le>\<^sub>p_" [51,51] 50) where
  "cri_less_eq =
    (\<lambda>(loc1,t1) (loc2,t2). (\<exists>s. s \<in>\<^sub>A path_summary loc1 loc2 \<and> results_in t1 s \<le> t2))"

definition cri_less :: "('loc \<times> 't) \<Rightarrow> ('loc \<times> 't) \<Rightarrow> bool" ("_<\<^sub>p_" [51,51] 50) where
  "cri_less x y = (x \<le>\<^sub>p y \<and> x \<noteq> y)"

lemma cri_asym1: "x <\<^sub>p y \<longrightarrow> \<not> y <\<^sub>p x"
  for x y apply (cases x; cases y)
proof (rule ccontr)
  fix loc1 t1 loc2 t2
  assume as: "\<not> (x <\<^sub>p y \<longrightarrow> \<not> y <\<^sub>p x)" "x = (loc1, t1)" "y = (loc2, t2)"
  then have as1: "loc1 \<noteq> loc2"
    unfolding cri_less_def cri_less_eq_def
    by clarsimp
      (metis add.right_neutral order.antisym order.trans le_plus(2) results_in_mono(2) results_in_zero)
  from as obtain s1 where s1: "s1 \<in>\<^sub>A path_summary loc1 loc2"
    "results_in t1 s1 \<le> t2"
    using cri_less_def cri_less_eq_def by auto
  then obtain path1 where path1: "flow.path loc1 loc2 path1"
    "s1 = flow.sum_path_weights path1"
    "path1 \<noteq> []"
    using as1 flow.path_weight_conv_path flow.path0E by blast
  from as obtain s2 where s2: "s2 \<in>\<^sub>A path_summary loc2 loc1"
    "results_in t2 s2 \<le> t1"
    using cri_less_def cri_less_eq_def by auto
  then obtain path2 where path2: "flow.path loc2 loc1 path2"
    "s2 = flow.sum_path_weights path2"
    "path2 \<noteq> []"
    using as1 flow.path_weight_conv_path flow.path0E by blast
  with path1 have path_total: "flow.path loc1 loc1 (path1@path2)"
    using flow.path_trans path2(3) by blast
  then obtain s3 where s3: "s3 = flow.sum_path_weights (path1@path2)" by auto
  then have s3_sum: "s3 = followed_by s1 s2"
    using path1 path2 flow.sum_weights_append by auto
  have "\<not> t1 < results_in t1 s3"
    using s3_sum s1(2) s2(2) followed_by_summary
    by (metis le_less_trans less_le_not_le results_in_mono(1))
  then show False using path_total no_zero_cycle s3 path1(3) path2(3) by blast
qed

lemma cri_asym2: "x <\<^sub>p y \<longrightarrow> x \<noteq> y"
  by (simp add: cri_less_def)

sublocale cri: order cri_less_eq cri_less
  apply standard
  subgoal
    using cri_asym1 cri_asym2 cri_less_def by blast
  subgoal for x
    unfolding cri_less_eq_def
    using flow.path_weight_refl results_in_zero by fastforce
  subgoal
    for x y z apply (cases x; cases y; cases z)
  proof -
    fix a b aa ba ab bb
    assume as: "x \<le>\<^sub>p y" "y \<le>\<^sub>p z" "x = (a, b)" "y = (aa, ba)" "z = (ab, bb)"
    then obtain s1 where s1: "s1 \<in>\<^sub>A path_summary a aa" "results_in b s1 \<le> ba"
      using cri_less_eq_def by auto
    from as(2,4,5) obtain s2 where s2: "s2 \<in>\<^sub>A path_summary aa ab" "results_in ba s2 \<le> bb"
      using cri_less_eq_def by auto
    with s1 obtain s3 where s3: "s3 \<in>\<^sub>A path_summary a ab" "s3 \<le> followed_by s1 s2"
      using flow.path_weight_elem_trans by blast
    with s1 s2 have "results_in b s3 \<le> bb"
    proof -
      have "\<forall>s. results_in (results_in b s1) s \<le> results_in ba s"
        by (meson results_in_mono(1) s1(2))
      then show ?thesis
        by (metis (no_types) results_in_mono(2) followed_by_summary order_trans s2(2) s3(2))
    qed
    with as s3 show ?thesis unfolding cri_less_eq_def by blast
  qed
  using cri_asym1 cri_asym2 cri_less_def by blast

lemma wf_cri: "wf {(l, l'). (l, t) <\<^sub>p (l', t)}"
  by (rule finite_acyclic_wf)
    (auto intro: cri.acyclicI_order[THEN acyclic_converse[THEN iffD1]])

end

subsection\<open>Specification\<close>

subsubsection\<open>Configuration\<close>

record ('p::finite, 't::order, 'loc) configuration =
  exchange_config :: "('p, ('loc \<times> 't)) Exchange.configuration"
  prop_config :: "'p \<Rightarrow> ('loc, 't) Propagate.configuration"
  init :: "'p \<Rightarrow> bool" (* True = initialization finished *)

type_synonym ('p, 't, 'loc) computation = "('p, 't, 'loc) configuration stream"

context dataflow_topology begin

definition the_cm where
  "the_cm c loc t n = (THE c'. next_change_multiplicity' c c' loc t n)"

text\<open>@{term the_cm} is not commutative in general, only if the necessary conditions hold. It can be converted
to @{term apply_cm} for which we prove @{term comp_fun_commute}.\<close>
definition apply_cm where
  "apply_cm c loc t n =
    (let new_pointstamps = (\<lambda>loc'.
                (if loc' = loc then update_zmultiset (c_pts c loc') t n
                               else c_pts c loc')) in
        c \<lparr> c_pts := new_pointstamps \<rparr>
          \<lparr> c_work :=
            (\<lambda>loc'. c_work c loc' + frontier_changes (new_pointstamps loc') (c_pts c loc'))\<rparr>)"

definition cm_all' where
  "cm_all' c0 \<Delta> =
      Finite_Set.fold (\<lambda>(loc, t) c. apply_cm c loc t (zcount \<Delta> (loc,t))) c0 (set_zmset \<Delta>)"

definition cm_all where
  "cm_all c0 \<Delta> =
      Finite_Set.fold (\<lambda>(loc, t) c. the_cm c loc t (zcount \<Delta> (loc,t))) c0 (set_zmset \<Delta>)"

definition "propagate_all c0 = while_option (\<lambda>c. \<exists>loc. (c_work c loc) \<noteq> {#}\<^sub>z)
                                            (\<lambda>c. SOME c'. \<exists>loc t. next_propagate' c c' loc t) c0"

subsubsection\<open>Initial state and state transitions\<close>

definition InitConfig :: "('p::finite, 't::order, 'loc) configuration \<Rightarrow> bool" where
  "InitConfig c =
      ((\<forall>p. init c p = False)
    \<and> cri.init_config (exchange_config c)
    \<and> (\<forall>p loc t. zcount (c_pts (prop_config c p) loc) t
       = zcount (c_glob (exchange_config c) p) (loc, t))
    \<and> (\<forall>w. init_config (prop_config c w)))"

definition NextPerformOp' :: "('p::finite, 't::order, 'loc) configuration \<Rightarrow> ('p, 't, 'loc) configuration
                              \<Rightarrow> 'p \<Rightarrow> ('loc \<times> 't) multiset \<Rightarrow> ('p \<times> ('loc \<times> 't)) multiset \<Rightarrow> ('loc \<times> 't) multiset \<Rightarrow> bool" where
  "NextPerformOp' c0 c1 p \<Delta>neg \<Delta>mint_msg \<Delta>mint_self = (
     cri.next_performop' (exchange_config c0) (exchange_config c1) p \<Delta>neg \<Delta>mint_msg \<Delta>mint_self
   \<and> unchanged prop_config c0 c1
   \<and> unchanged init c0 c1)"

abbreviation NextPerformOp where
  "NextPerformOp c0 c1 \<equiv> \<exists>p \<Delta>neg \<Delta>mint_msg \<Delta>mint_self. NextPerformOp' c0 c1 p \<Delta>neg \<Delta>mint_msg \<Delta>mint_self"

definition NextRecvCap'
  :: "('p::finite, 't::order, 'loc) configuration \<Rightarrow> ('p, 't, 'loc) configuration \<Rightarrow> 'p \<Rightarrow> 'loc \<times> 't \<Rightarrow> bool" where
  "NextRecvCap' c0 c1 p t = (
     cri.next_recvcap' (exchange_config c0) (exchange_config c1) p t
   \<and> unchanged prop_config c0 c1
   \<and> unchanged init c0 c1)"

abbreviation NextRecvCap where
  "NextRecvCap c0 c1 \<equiv> \<exists>p t. NextRecvCap' c0 c1 p t"

definition NextSendUpd' :: "('p::finite, 't::order, 'loc) configuration \<Rightarrow> ('p, 't, 'loc) configuration
                              \<Rightarrow> 'p \<Rightarrow> ('loc \<times> 't) set \<Rightarrow> bool" where
  "NextSendUpd' c0 c1 p tt = (
    cri.next_sendupd' (exchange_config c0) (exchange_config c1) p tt
  \<and> unchanged prop_config c0 c1
  \<and> unchanged init c0 c1)"

abbreviation NextSendUpd where
  "NextSendUpd c0 c1 \<equiv> \<exists>p tt. NextSendUpd' c0 c1 p tt"

definition NextRecvUpd' :: "('p::finite, 't::order, 'loc) configuration \<Rightarrow> ('p, 't, 'loc) configuration
                              \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool" where
  "NextRecvUpd' c0 c1 p q = (
     init c0 q \<comment> \<open>Once init is set we are guaranteed that the CM transitions' premises are satisfied\<close>
   \<and> cri.next_recvupd' (exchange_config c0) (exchange_config c1) p q
   \<and> unchanged init c0 c1
   \<and> (\<forall>p'. prop_config c1 p' =
          (if p' = q
           then cm_all (prop_config c0 q) (hd (c_msg (exchange_config c0) p q))
           else prop_config c0 p')))"

abbreviation NextRecvUpd where
  "NextRecvUpd c0 c1 \<equiv> \<exists>p q. NextRecvUpd' c0 c1 p q"

definition NextPropagate' :: "('p::finite, 't::order, 'loc) configuration \<Rightarrow> ('p, 't, 'loc) configuration
                              \<Rightarrow> 'p \<Rightarrow> bool" where
  "NextPropagate' c0 c1 p = (
     unchanged exchange_config c0 c1
   \<and>  init c1 = (init c0)(p := True)
   \<and> (\<forall>p'. Some (prop_config c1 p') =
          (if p' = p
           then propagate_all (prop_config c0 p')
           else Some (prop_config c0 p'))))"

abbreviation NextPropagate where
  "NextPropagate c0 c1 \<equiv> \<exists>p. NextPropagate' c0 c1 p"

definition "Next'" where
  "Next' c0 c1 = (NextPerformOp c0 c1 \<or> NextSendUpd c0 c1 \<or> NextRecvUpd c0 c1 \<or> NextPropagate c0 c1 \<or> NextRecvCap c0 c1 \<or> c1 = c0)"

abbreviation "Next" where
  "Next s \<equiv> Next' (shd s) (shd (stl s))"

definition FullSpec :: "('p :: finite, 't :: order, 'loc) computation \<Rightarrow> bool" where
  "FullSpec s = (holds InitConfig s \<and> alw Next s)"

lemma NextPerformOpD:
  assumes "NextPerformOp' c0 c1 p \<Delta>neg \<Delta>mint_msg \<Delta>mint_self"
  shows
    "cri.next_performop' (exchange_config c0) (exchange_config c1) p \<Delta>neg \<Delta>mint_msg \<Delta>mint_self"
    "unchanged prop_config c0 c1"
    "unchanged init c0 c1"
  using assms unfolding NextPerformOp'_def by simp_all

lemma NextSendUpdD:
  assumes "NextSendUpd' c0 c1 p tt"
  shows
    "cri.next_sendupd' (exchange_config c0) (exchange_config c1) p tt"
    "unchanged prop_config c0 c1"
    "unchanged init c0 c1"
  using assms unfolding NextSendUpd'_def by simp_all

lemma NextRecvUpdD:
  assumes "NextRecvUpd' c0 c1 p q"
  shows
    "init c0 q"
    "cri.next_recvupd' (exchange_config c0) (exchange_config c1) p q"
    "unchanged init c0 c1"
    "(\<forall>p'. prop_config c1 p' =
         (if p' = q
          then cm_all (prop_config c0 q) (hd (c_msg (exchange_config c0) p q))
          else prop_config c0 p'))"
  using assms unfolding NextRecvUpd'_def by simp_all

lemma NextPropagateD:
  assumes "NextPropagate' c0 c1 p"
  shows
    "unchanged exchange_config c0 c1"
    "init c1 = (init c0)(p := True)"
    "(\<forall>p'. Some (prop_config c1 p') =
         (if p' = p
          then propagate_all (prop_config c0 p')
          else Some (prop_config c0 p')))"
  using assms unfolding NextPropagate'_def by simp_all

lemma NextRecvCapD:
  assumes "NextRecvCap' c0 c1 p t"
  shows
    "cri.next_recvcap' (exchange_config c0) (exchange_config c1) p t"
    "unchanged prop_config c0 c1"
    "unchanged init c0 c1"
  using assms unfolding NextRecvCap'_def by simp_all

subsection\<open>Auxiliary Lemmas\<close>

subsubsection\<open>Auxiliary Lemmas for CM Conversion\<close>

lemma apply_cm_is_cm:
  "\<exists>t'. t' \<in>\<^sub>A frontier (c_imp c loc) \<and> t' \<le> t \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> next_change_multiplicity' c (apply_cm c loc t n) loc t n"
  by (auto simp: next_change_multiplicity'_def apply_cm_def
      intro!: Propagate.configuration.equality)

lemma update_zmultiset_commute:
  "update_zmultiset (update_zmultiset M t' n') t n = update_zmultiset (update_zmultiset M t n) t' n'"
  by transfer (auto simp: equiv_zmset_def split: if_splits)

lemma apply_cm_commute: "apply_cm (apply_cm c loc t n) loc' t' n' = apply_cm (apply_cm c loc' t' n') loc t n"
  unfolding apply_cm_def Let_def
  by (auto intro!: Propagate.configuration.equality simp: update_zmultiset_commute)

lemma comp_fun_commute_apply_cm[simp]: "comp_fun_commute (\<lambda>(loc, t) c. apply_cm c loc t (f loc t))"
  by (auto intro!: Propagate.configuration.equality simp: update_zmultiset_commute comp_fun_commute_def o_def apply_cm_commute)

lemma ex_cm_imp_conds:
  assumes "\<exists>c'. next_change_multiplicity' c c' loc t n"
  shows "\<exists>t'. t' \<in>\<^sub>A frontier (c_imp c loc) \<and> t' \<le> t" "n \<noteq> 0"
  using assms by (auto simp: next_change_multiplicity'_def)

lemma the_cm_eq_apply_cm:
  assumes "\<exists>c'. next_change_multiplicity' c c' loc t n"
  shows   "the_cm c loc t n = apply_cm c loc t n"
proof -
  from assms have cond: "\<exists>t'. t' \<in>\<^sub>A frontier (c_imp c loc) \<and> t' \<le> t" "n \<noteq> 0"
    using ex_cm_imp_conds by blast+
  show ?thesis
    unfolding the_cm_def
    apply (rule the1_equality)
     apply (rule next_change_multiplicity'_unique[OF cond(2,1)])
    unfolding apply_cm_def next_change_multiplicity'_def
    using cond apply (auto intro!: Propagate.configuration.equality)
    done
qed

lemma apply_cm_preserves_cond:
  assumes "\<forall>(loc,t)\<in>set_zmset \<Delta>. \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c0 loc) \<and> t' \<le> t"
  shows   "\<forall>(loc,t)\<in>set_zmset \<Delta>. \<exists>t'. t' \<in>\<^sub>A frontier (c_imp (apply_cm c0 loc' t'' n) loc) \<and> t' \<le> t"
  using assms by (auto simp: apply_cm_def)

lemma cm_all_eq_cm_all':
  assumes "\<forall>(loc,t)\<in>set_zmset \<Delta>. \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c0 loc) \<and> t' \<le> t"
  shows   "cm_all c0 \<Delta> = cm_all' c0 \<Delta>"
  unfolding cm_all_def cm_all'_def
  apply (rule fold_closed_eq[where B = "{c. \<forall>(loc,t)\<in>set_zmset \<Delta>. \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c loc) \<and> t' \<le> t}"])
  subgoal for a \<Delta>
    apply (cases a)
    apply simp
    apply (rule the_cm_eq_apply_cm)
    apply (rule ex1_implies_ex)
    apply (rule next_change_multiplicity'_unique)
     apply auto
    done
  subgoal for a \<Delta>
    apply (cases a)
    apply simp
    apply (rule apply_cm_preserves_cond)
    apply auto
    done
  subgoal
    using assms by simp
  done

lemma cm_eq_the_cm:
  assumes "next_change_multiplicity' c c' loc t n"
  shows   "the_cm c loc t n = c'"
proof -
  from assms have cond: "\<exists>u. u \<in>\<^sub>A frontier (c_imp c loc) \<and> u \<le> t" "n \<noteq> 0"
    unfolding next_change_multiplicity'_def by auto
  then show ?thesis
    using next_change_multiplicity'_unique[OF cond(2,1)] assms the_cm_def
    by auto
qed

lemma zcount_ps_apply_cm:
  "zcount (c_pts (apply_cm c loc t n) loc') t' = zcount (c_pts c loc') t' + (if loc = loc' \<and> t = t' then n else 0)"
  by (auto simp: apply_cm_def zcount_update_zmultiset)

lemma zcount_pointstamps_update: "zcount (c_pts (c\<lparr>c_pts:=M\<rparr>) loc) x = zcount (M loc) x"
  by auto

lemma nop: "loc1 \<noteq> loc2 \<or> t1 \<noteq> t2 \<longrightarrow>
    zcount (c_pts (apply_cm c loc2 t2 (zcount \<Delta> (loc2, t2))) loc1) t1 =
    zcount (c_pts c loc1) t1"
  apply (simp add: apply_cm_def)
  using zcount_update_zmultiset
  by (simp add: zcount_update_zmultiset)

lemma fold_nop:
  "zcount (c_pts (Finite_Set.fold (\<lambda>(loc', t') c. apply_cm c loc' t' (zcount \<Delta>' (loc', t'))) c
                          (set_zmset \<Delta> - {(loc, t)})) loc) t
  = zcount (c_pts c loc) t"
proof -
  have "finite (set_zmset \<Delta>- {(loc, t)})" using finite_set_zmset by blast
  then show ?thesis
  proof (induct "set_zmset \<Delta> - {(loc, t)}" arbitrary: \<Delta> rule: finite_induct)
    case empty
    then show ?case using fold_empty by auto
  next
    let ?f = "(\<lambda>(loc', t') c. apply_cm c loc' t' (zcount \<Delta>' (loc',t')))"
    case (insert x F)
    obtain loc' t' where x_pair: "x = (loc', t')" by (meson surj_pair)
    from insert have nonmember: "x \<noteq> (loc, t)" by auto
    then have finite_s: "finite F" using insert by auto
    have commute: "comp_fun_commute ?f"
      by (simp add: comp_fun_commute_def comp_def apply_cm_commute)
    with finite_s have step1:
      "Finite_Set.fold ?f c (insert x F) = ?f x (Finite_Set.fold ?f c F)"
      by (metis (mono_tags, lifting) comp_fun_commute.fold_insert insert.hyps(1) insert.hyps(2))
    from nonmember have step2:
      "zcount (c_pts (?f x (Finite_Set.fold ?f c F)) loc) t
          = zcount (c_pts (Finite_Set.fold ?f c F) loc) t"
      using x_pair
      by (metis (mono_tags, lifting) case_prod_conv nop)
    with step1 and x_pair have final:
      "zcount (c_pts (Finite_Set.fold ?f c (insert x F)) loc) t
          = zcount (c_pts (Finite_Set.fold ?f c F) loc) t"
      by simp
    from insert(2,4) obtain \<Delta>2 where \<Delta>2: "\<Delta>2 = filter_zmset (\<lambda>y. y\<noteq>x) \<Delta>" by blast
    then have "F = set_zmset \<Delta>2 - {(loc, t)}"
    proof -
      from \<Delta>2 have *: "x \<notin>#\<^sub>z \<Delta>2" by (simp add: not_in_iff_zmset)
      from insert(4) and nonmember have **: "x \<in>#\<^sub>z \<Delta>" by blast
      from \<Delta>2 ** have ***: "\<forall>y. y \<in>#\<^sub>z \<Delta> \<longleftrightarrow> (y \<in>#\<^sub>z \<Delta>2 \<or> y = x)"
        by (metis (mono_tags, lifting) count_filter_zmset zcount_ne_zero_iff)
      with *** have "\<forall>y. (y \<in> set_zmset \<Delta> = (y \<in> (set_zmset \<Delta>2 \<union> {x})))" by blast
      then have "set_zmset \<Delta> = set_zmset \<Delta>2 \<union> {x}" by (auto simp add: set_eq_iff)
      with insert(2,3,4) *  show ?thesis
        by (metis (mono_tags, lifting) Diff_insert Diff_insert2 Diff_insert_absorb Un_empty_right Un_insert_right)
    qed
    with final insert show ?case by metis
  qed
qed

lemma zcount_pointstamps_cm_all':
  "zcount (c_pts (cm_all' c \<Delta>) loc) x
 = zcount (c_pts c loc) x + zcount \<Delta> (loc,x)"
proof -
  let ?f = "(\<lambda>(loc', t') c. apply_cm c loc' t' (zcount \<Delta> (loc',t')))"
  have ?thesis
  proof (cases "zcount \<Delta> (loc,x) = 0")
    case case_nonmember: True
    then have set_zmset\<Delta>: "set_zmset \<Delta> - {(loc, x)} = set_zmset \<Delta>" using zcount_eq_zero_iff by fastforce
    have "zcount (c_pts (cm_all' c \<Delta>) loc) x
             = zcount (c_pts c loc) x"
      unfolding cm_all'_def
      apply (subst set_zmset\<Delta>[symmetric])
      apply (simp add: fold_nop)
      done
    with case_nonmember show ?thesis by auto
  next
    case case_member: False
    then have fold_rec: "Finite_Set.fold ?f c (set_zmset \<Delta>)
             = ?f (loc, x) (Finite_Set.fold ?f c (set_zmset \<Delta> - {(loc, x)}))"
    proof -
      have "(loc, x) \<in>#\<^sub>z \<Delta>"
        by (meson case_member zcount_inI)
      then show ?thesis
        using comp_fun_commute_apply_cm
        apply (intro comp_fun_commute.fold_rec)
          apply simp_all
        done
    qed
    have "zcount (c_pts (Finite_Set.fold ?f c (set_zmset \<Delta> - {(loc, x)})) loc) x
          = zcount (c_pts c loc) x" by (simp add: fold_nop)
    then have "zcount (c_pts (Finite_Set.fold ?f c (set_zmset \<Delta>)) loc) x
             = zcount (c_pts (?f (loc, x) c) loc) x"
      using fold_nop fold_rec by (simp add: zcount_ps_apply_cm)
    then show ?thesis
      by (simp add: zcount_ps_apply_cm cm_all'_def)
  qed
  then show ?thesis ..
qed

lemma implications_apply_cm[simp]: "c_imp (apply_cm c loc t n) = c_imp c"
  by (auto simp: apply_cm_def)

lemma implications_cm_all[simp]:
  "c_imp (cm_all' c \<Delta>) = c_imp c"
  unfolding cm_all'_def Let_def
  apply (rule fold_invar[OF finite_set_zmset])
    apply auto
  done

lemma lift_cm_inv_cm_all':
  assumes "(\<And>c0 c1 loc t n. P c0 \<Longrightarrow> next_change_multiplicity' c0 c1 loc t n \<Longrightarrow> P c1)"
    and   "\<forall>(loc,t)\<in>#\<^sub>z\<Delta>. \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c0 loc) \<and> t' \<le> t"
    and   "P c0"
  shows   "P (cm_all' c0 \<Delta>)"
proof -
  let ?cond_invar = "\<lambda>c. \<forall>(loc, t)\<in>#\<^sub>z\<Delta>. \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c loc) \<and> t' \<le> t"
  let ?invar = "\<lambda>c. ?cond_invar c \<and> P c"
  show ?thesis
    unfolding cm_all'_def
    apply (rule conjunct2[OF fold_invar[OF finite_set_zmset, of ?invar]])
    using assms(2,3) apply simp
    subgoal
      apply safe
       apply auto []
      apply (rule assms(1))
       apply simp
      apply (rule apply_cm_is_cm)
       apply auto
      done
    apply simp
    done
qed

lemma lift_cm_inv_cm_all:
  assumes "\<And>c0 c1 loc t n. P c0 \<Longrightarrow> next_change_multiplicity' c0 c1 loc t n \<Longrightarrow> P c1"
    and   "\<forall>(loc,t)\<in>#\<^sub>z\<Delta>. \<exists>t'. t' \<in>\<^sub>A frontier (c_imp c0 loc) \<and> t' \<le> t"
    and   "P c0"
  shows   "P (cm_all c0 \<Delta>)"
  apply (subst cm_all_eq_cm_all')
  using assms(2) apply simp
  using assms apply (rule lift_cm_inv_cm_all')
   apply simp_all
  done

(* Finds a minimal timestamp - location pair in a non-empty zmset (e.g. in c_work) *)
lemma obtain_min_worklist:
  assumes "(a (loc'::(_ :: finite))::(('t :: order) zmultiset)) \<noteq> {#}\<^sub>z"
  obtains loc t
  where "t \<in>#\<^sub>z a loc"
    and "\<forall>t' loc'. t' \<in>#\<^sub>z a loc' \<longrightarrow> \<not> t' < t"
  using assms
proof atomize_elim
  obtain f where f: "f = minimal_antichain (\<Union>loc'. set_zmset (a loc'))"
    by blast
  from assms obtain x' where x': "x' \<in> (\<Union>loc'. set_zmset (a loc'))"
    using pos_zcount_in_zmset by fastforce
  from assms have "finite  (\<Union>loc'. set_zmset (a loc'))"
    using finite_UNIV by blast
  with x' have "f \<noteq> {}" unfolding f
    using minimal_antichain_nonempty by blast
  then obtain t where t: "t \<in> f" "(\<forall>s\<in>f. \<not> s < t)"
    using ex_min_if_finite f minimal_antichain_def by fastforce
  with f have thesis1:  "\<forall>t' loc'. t' \<in>#\<^sub>z a loc' \<longrightarrow> \<not> t' < t" "\<exists>loc. t \<in>#\<^sub>z a loc"
    by (simp add: minimal_antichain_def)+
  then show "\<exists>t loc. t \<in>#\<^sub>z a loc \<and> (\<forall>t' loc'. t' \<in>#\<^sub>z a loc' \<longrightarrow> \<not> t' < t)" by blast
qed

lemma propagate_pointstamps_eq:
  assumes "c_work c loc \<noteq> {#}\<^sub>z"
  shows   "c_pts c = c_pts (SOME c'. \<exists>loc t. next_propagate' c c' loc t)"
proof -
  from assms obtain loc' t where loc't: "t \<in>#\<^sub>z c_work c loc'"
    "\<forall>t' loc'. t' \<in>#\<^sub>z c_work c loc' \<longrightarrow> \<not> t' < t"
    apply (rule obtain_min_worklist[of "c_work c" "loc"]) by blast
  let ?imps = "\<lambda>locX. if locX = loc' then c_imp c locX + {#t' \<in>#\<^sub>z c_work c locX. t' = t#}
                                     else c_imp c locX"
  let ?wl = "\<lambda>locX. if locX = loc' then {#t' \<in>#\<^sub>z c_work c locX. t' \<noteq> t#}
                    else c_work c locX
                           + after_summary
                               (frontier_changes (?imps loc') (c_imp c loc'))
                               (summary loc' locX)"
  let ?c = "c\<lparr>c_imp := ?imps, c_work := ?wl\<rparr>"
  from loc't assms have propagate: "\<exists>c'. \<exists>loc t. next_propagate' c c' loc t"
    by (intro exI[of _ ?c] exI[of _ loc'] exI[of _ t])
      (auto simp add: next_propagate'_def intro!: Propagate.configuration.equality)
  { fix c' loc t
    assume "next_propagate' c c' loc t"
    then have "c_pts c = c_pts c'"
      by (simp add: next_propagate'_def)
  }
  with propagate show ?thesis
    by (simp add: verit_sko_ex')
qed

lemma propagate_all_imp_InvGlobPointstampsEq:
  "Some c1 = propagate_all c0 \<Longrightarrow> c_pts c0 = c_pts c1"
  unfolding propagate_all_def
  using while_option_rule[where P="(\<lambda>c. c_pts c0 = c_pts c)"
      and b="(\<lambda>c. \<exists>loc. c_work c loc \<noteq> {#}\<^sub>z)"
      and c="(\<lambda>c. SOME c'. \<exists>loc t. next_propagate' c c' loc t)"]
    propagate_pointstamps_eq by (metis (no_types, lifting))

lemma exists_next_propagate':
  assumes "c_work c loc \<noteq> {#}\<^sub>z"
  shows   "\<exists>c' loc t. next_propagate' c c' loc t"
proof -
  from assms obtain loc' t where loc't:
    "t \<in>#\<^sub>z c_work c loc'"
    "\<forall>t' loc'. t' \<in>#\<^sub>z c_work c loc' \<longrightarrow> \<not> t' < t"
    by (rule obtain_min_worklist)
  let ?imps = "\<lambda>locX. if locX = loc' then c_imp c locX + {#t' \<in>#\<^sub>z c_work c locX. t' = t#}
                                     else c_imp c locX"
  let ?wl = "\<lambda>locX. if locX = loc' then {#t' \<in>#\<^sub>z c_work c locX. t' \<noteq> t#}
                    else c_work c locX
                           + after_summary
                               (frontier_changes (?imps loc') (c_imp c loc'))
                               (summary loc' locX)"
  let ?c = "c\<lparr>c_imp := ?imps, c_work := ?wl\<rparr>"
  from loc't assms show ?thesis
    by (intro exI[of _ ?c] exI[of _ loc'] exI[of _ t])
      (auto simp: next_propagate'_def intro!: Propagate.configuration.equality)
qed

lemma lift_propagate_inv_propagate_all:
  assumes "(\<And>c0 c1 loc t. P c0 \<Longrightarrow> next_propagate' c0 c1 loc t \<Longrightarrow> P c1)"
    and   "P c0"
    and   "propagate_all c0 = Some c1"
  shows   "P c1"
  apply (rule while_option_rule[of P _, rotated, OF assms(3)[unfolded propagate_all_def], OF assms(2)])
  apply clarify
  subgoal for c loc
    apply (drule exists_next_propagate')
    apply (simp add: assms(1) verit_sko_ex')
    done
  done

subsection\<open>Exchange is a Subsystem of Tracker\<close>

text\<open>Steps in the Tracker are valid steps in the Exchange protocol.\<close>
lemma next_imp_exchange_next:
  "Next' c0 c1 \<Longrightarrow> cri.next' (exchange_config c0) (exchange_config c1)"
  unfolding Next'_def cri.next'_def NextPerformOp'_def NextRecvUpd'_def NextSendUpd'_def NextPropagate'_def NextRecvCap'_def
  by auto

lemma alw_next_imp_exchange_next: "alw Next s \<Longrightarrow> alw cri.next (smap exchange_config s)"
  by (coinduction arbitrary: s rule: alw.coinduct) (auto dest: alwD next_imp_exchange_next)

text\<open>Any Tracker trace is a valid Exchange trace\<close>
lemma spec_imp_exchange_spec: "FullSpec s \<Longrightarrow> cri.spec (smap exchange_config s)"
  unfolding cri.spec_def FullSpec_def
  by (auto simp: InitConfig_def intro: alw_next_imp_exchange_next)

lemma lift_exchange_invariant:
  assumes "\<And>s. cri.spec s \<Longrightarrow> alw (holds P) s"
  shows   "FullSpec s \<Longrightarrow> alw (\<lambda>s. P (exchange_config (shd s))) s"
proof -
  assume "FullSpec s"
  note spec_imp_exchange_spec[OF this]
  note assms[OF this]
  then show ?thesis
    by (auto simp: alw_holds_smap_conv_comp)
qed

text\<open>Lifted Exchange invariants\<close>
lemmas
  exch_alw_InvCapsNonneg                 = lift_exchange_invariant[OF cri.alw_InvCapsNonneg, unfolded atomize_imp, simplified, folded atomize_imp] and
  exch_alw_InvRecordCount                = lift_exchange_invariant[OF cri.alw_InvRecordCount, simplified atomize_imp, simplified, folded atomize_imp] and
  exch_alw_InvRecordsNonneg              = lift_exchange_invariant[OF cri.alw_InvRecordsNonneg, simplified atomize_imp, simplified, folded atomize_imp] and
  exch_alw_InvGlobVacantImpRecordsVacant = lift_exchange_invariant[OF cri.alw_InvGlobVacantImpRecordsVacant, simplified atomize_imp, simplified, folded atomize_imp] and
  exch_alw_InvGlobNonposImpRecordsNonpos = lift_exchange_invariant[OF cri.alw_InvGlobNonposImpRecordsNonpos, simplified atomize_imp, simplified, folded atomize_imp] and
  exch_alw_InvJustifiedGII               = lift_exchange_invariant[OF cri.alw_InvJustifiedGII, simplified atomize_imp, simplified, folded atomize_imp] and
  exch_alw_InvJustifiedII                = lift_exchange_invariant[OF cri.alw_InvJustifiedII, simplified atomize_imp, simplified, folded atomize_imp] and
  exch_alw_InvGlobNonposEqVacant         = lift_exchange_invariant[OF cri.alw_InvGlobNonposEqVacant, simplified atomize_imp, simplified, folded atomize_imp] and
  exch_alw_InvMsgInGlob                  = lift_exchange_invariant[OF cri.alw_InvMsgInGlob, simplified atomize_imp, simplified, folded atomize_imp] and
  exch_alw_InvTempJustified              = lift_exchange_invariant[OF cri.alw_InvTempJustified, simplified atomize_imp, simplified, folded atomize_imp]

subsection\<open>Definitions\<close>

(* First variant of global safe *)
definition safe_combined :: "('p::finite, 't::order, 'loc) configuration \<Rightarrow> bool" where
  "safe_combined c \<equiv> \<forall>loc1 loc2 t s p.
        zcount (cri.records (exchange_config c)) (loc1, t) > 0 \<and> s \<in>\<^sub>A path_summary loc1 loc2 \<and> init c p
         \<longrightarrow> (\<exists>t'. t' \<in>\<^sub>A frontier (c_imp (prop_config c p) loc2) \<and> t' \<le> results_in t s)"

(* Second variant of global safe *)
definition safe_combined2 :: "('p::finite, 't::order, 'loc) configuration \<Rightarrow> bool" where
  "safe_combined2 c \<equiv> \<forall>loc1 loc2 t s p1 p2.
        zcount (c_caps (exchange_config c) p1) (loc1, t) > 0 \<and> s \<in>\<^sub>A path_summary loc1 loc2 \<and> init c p2
         \<longrightarrow> (\<exists>t'. t' \<in>\<^sub>A frontier (c_imp (prop_config c p2) loc2) \<and> t' \<le> results_in t s)"

definition InvGlobPointstampsEq :: "('p :: finite, 't :: order, 'loc) configuration \<Rightarrow> bool" where
  "InvGlobPointstampsEq c = (
     (\<forall>p loc t. zcount (c_pts (prop_config c p) loc) t
                 = zcount (c_glob (exchange_config c) p) (loc, t)))"

lemma safe_combined_implies_safe_combined2:
  assumes "cri.InvCapsNonneg (exchange_config c)"
    and   "safe_combined c"
  shows   "safe_combined2 c"
  unfolding safe_combined2_def
  apply clarify
  subgoal for loc1 loc2 t s p1 p2
    apply (rule assms(2)[unfolded safe_combined_def, rule_format, of loc1 t s loc2 p2])
    apply (simp add: cri.records_def)
    apply (rule add_pos_nonneg)
     apply (subst zcount_sum)
     apply (rule sum_pos[where y = p1])
    using assms(1)
        apply (simp_all add: cri.InvCapsNonneg_def)
    done
  done

subsection\<open>Propagate is a Subsystem of Tracker\<close>

subsubsection\<open>CM Conditions\<close>

definition InvMsgCMConditions where
  "InvMsgCMConditions c = (\<forall>p q.
    init c q \<longrightarrow> c_msg (exchange_config c) p q \<noteq> [] \<longrightarrow>
     (\<forall>(loc,t) \<in>#\<^sub>z (hd (c_msg (exchange_config c) p q)). \<exists>t'. t' \<in>\<^sub>A frontier (c_imp (prop_config c q) loc) \<and> t' \<le> t))"

text\<open>Pointstamps in incoming messages all satisfy the CM premise, which is required during NextRecvUpd' steps.\<close>
lemma msg_is_cm_safe:
  fixes c :: "('p::finite, 't::order, 'loc) configuration"
  assumes "safe (prop_config c q)"
    and   "InvGlobPointstampsEq c"
    and   "cri.InvMsgInGlob (exchange_config c)"
    and   "c_msg (exchange_config c) p q \<noteq> []"
  shows   "\<forall>(loc,t) \<in>#\<^sub>z (hd (c_msg (exchange_config c) p q)). \<exists>t'. t' \<in>\<^sub>A frontier (c_imp (prop_config c q) loc) \<and> t' \<le> t"
  using assms(3)[unfolded cri.InvMsgInGlob_def, rule_format, OF assms(4)] assms(1)[unfolded safe_def, rule_format]
  apply (clarsimp simp: cri_less_eq_def assms(2)[unfolded InvGlobPointstampsEq_def, rule_format, symmetric])
  using order_trans apply blast
  done

subsubsection\<open>Propagate Safety and InvGlobPointstampsEq\<close>

text\<open>To be able to use the @{thm[source] msg_is_cm_safe} lemma at all times and show that Propagate is a
subsystem we need to prove that the specification implies Propagate's safe and the
InvGlobPointstampsEq. Both of these depend on the CM conditions being satisfied during the
NextRecvUpd' step and the safety proof additionally depends on other Propagate invariants, which
means that we need to prove all of these jointly.\<close>

abbreviation prop_invs where
  "prop_invs c \<equiv> inv_implications_nonneg c \<and> inv_imps_work_sum c"

abbreviation prop_safe where
  "prop_safe c \<equiv> impl_safe c \<and> safe c"

definition inv_init_imp_prop_safe where
  "inv_init_imp_prop_safe c = (\<forall>p. init c p \<longrightarrow> prop_safe (prop_config c p))"

lemma NextRecvUpd'_preserves_prop_safe:
  assumes "prop_safe (prop_config c0 q)"
    and   "InvGlobPointstampsEq c0"
    and   "cri.InvMsgInGlob (exchange_config c0)"
    and   "NextRecvUpd' c0 c1 p q"
  shows   "prop_safe (prop_config c1 q)"
proof -
  have safe: "safe (prop_config c0 q)"
    using assms(1) by blast
  note recvupd_change = cri.next_recvupdD(1)[OF NextRecvUpdD(2)[OF assms(4)]]
  note cm_conds = msg_is_cm_safe[OF safe assms(2,3) recvupd_change]
  have safes:
    "prop_safe c0 \<Longrightarrow> next_change_multiplicity' c0 c1 loc t n \<Longrightarrow> prop_safe c1" for c0 c1 loc t n
    using
      cm_preserves_safe
      cm_preserves_impl_safe
    by auto
  show "prop_safe (prop_config c1 q)"
    using
      lift_cm_inv_cm_all[rotated, OF cm_conds, of prop_safe, OF assms(1)]
      safes
      NextRecvUpdD(4)[OF assms(4)]
    by metis
qed

lemma NextRecvUpd'_preserves_InvGlobPointstampsEq:
  assumes "impl_safe (prop_config c0 q) \<and> safe (prop_config c0 q)"
    and   "InvGlobPointstampsEq c0"
    and   "cri.InvMsgInGlob (exchange_config c0)"
    and   "NextRecvUpd' c0 c1 p q"
  shows   "InvGlobPointstampsEq c1"
proof -
  have safe: "safe (prop_config c0 q)"
    using assms(1) by blast
  note recvupd_change = cri.next_recvupdD(1)[OF NextRecvUpdD(2)[OF assms(4)]]
  note cm_conds = msg_is_cm_safe[OF safe assms(2,3) recvupd_change]
  show "InvGlobPointstampsEq c1"
    using
      assms(2,4)
      cm_conds
    unfolding NextRecvUpd'_def cri.next_recvupd'_def Let_def InvGlobPointstampsEq_def
    by (clarsimp simp: zcount_pointstamps_cm_all' cm_all_eq_cm_all')+
qed

\<comment> \<open>Whenever some worker p propagates it ends up in a Propagate-safe state\<close>
lemma NextPropagate'_causes_safe:
  assumes "NextPropagate' c0 c1 p"
    and   "inv_imps_work_sum (prop_config c1 p)"
    and   "inv_implications_nonneg (prop_config c1 p)"
  shows   "safe (prop_config c1 p)" "impl_safe (prop_config c1 p)"
proof -
  from assms(1) have "Some (prop_config c1 p) = propagate_all (prop_config c0 p)"
    by (simp add: NextPropagate'_def)
  then have wl: "c_work (prop_config c1 p) loc = {#}\<^sub>z" for loc
    unfolding propagate_all_def
    by (subst (asm) eq_commute) (auto dest: while_option_stop)
  show "safe (prop_config c1 p)" "impl_safe (prop_config c1 p)"
    by (rule safe[OF assms(2,3) wl]) (rule impl_safe[OF assms(2,3) wl])
qed

\<comment> \<open>NextPropagate' preserves Propagate-safe at all workers\<close>
lemma NextPropagate'_preserves_safe:
  assumes "NextPropagate' c0 c1 q"
    and   "inv_imps_work_sum (prop_config c1 p)"
    and   "inv_implications_nonneg (prop_config c1 p)"
    and   "safe (prop_config c0 p)"
  shows   "safe (prop_config c1 p)"
  apply (cases "p=q")
  subgoal
    using assms(1-3) by (auto intro: NextPropagate'_causes_safe)
  subgoal
    using assms(1,4) by (auto dest: spec[of _ p] simp: NextPropagate'_def)
  done

lemma NextPropagate'_preserves_impl_safe:
  assumes "NextPropagate' c0 c1 q"
    and   "inv_imps_work_sum (prop_config c1 p)"
    and   "inv_implications_nonneg (prop_config c1 p)"
    and   "impl_safe (prop_config c0 p)"
  shows   "impl_safe (prop_config c1 p)"
  apply (cases "p=q")
  subgoal
    using assms(1-3) by (auto intro: NextPropagate'_causes_safe)
  subgoal
    using assms(1,4) by (auto dest: spec[of _ p] simp: NextPropagate'_def)
  done

lemma NextRecvUpd'_preserves_inv_init_imp_prop_safe:
  assumes "cri.InvMsgInGlob (exchange_config c0)"
    and   "inv_init_imp_prop_safe c0"
    and   "InvGlobPointstampsEq c0"
    and   "NextRecvUpd' c0 c1 p q"
  shows   "inv_init_imp_prop_safe c1"
  using assms(2) unfolding inv_init_imp_prop_safe_def
  apply clarify
  subgoal for p
    apply (cases "p=q")
    subgoal
      apply (drule spec[of _p])
      apply (simp add: NextRecvUpdD(1)[OF assms(4)])
      apply (drule NextRecvUpd'_preserves_prop_safe[OF _ assms(3,1,4)])
      apply simp
      done
    subgoal
      using NextRecvUpdD(3,4)[OF assms(4)] by fastforce
    done
  done

lemma NextRecvUpd'_preserves_prop_invs:
  assumes "cri.InvMsgInGlob (exchange_config c0)"
    and   "inv_init_imp_prop_safe c0"
    and   "\<forall>p. prop_invs (prop_config c0 p)"
    and   "InvGlobPointstampsEq c0"
    and   "NextRecvUpd' c0 c1 p q"
  shows   "\<forall>p. prop_invs (prop_config c1 p)"
proof -
  have safe: "safe (prop_config c0 q)"
    using NextRecvUpdD(1) assms(2,5) inv_init_imp_prop_safe_def by blast
  note recvupd_change = cri.next_recvupdD(1)[OF NextRecvUpdD(2)[OF assms(5)]]
  note cm_conds = msg_is_cm_safe[OF safe assms(4,1) recvupd_change]
  have invs:
    "prop_invs c0 \<Longrightarrow> next_change_multiplicity' c0 c1 loc t n \<Longrightarrow> prop_invs c1" for c0 c1 loc t n
    using
      cm_preserves_inv_imps_work_sum
      cm_preserves_inv_implications_nonneg
    by auto
  show "\<forall>q. prop_invs (prop_config c1 q)"
    apply rule
    subgoal for q'
      apply (cases "q'=q")
      subgoal
        using
          lift_cm_inv_cm_all[rotated, OF cm_conds, of prop_invs, OF assms(3)[rule_format]]
          invs
          NextRecvUpdD(4)[OF assms(5)]
        by metis
      subgoal
        using NextRecvUpdD(4) assms(3) assms(5) by fastforce
      done
    done
qed

lemma NextPropagate'_preserves_prop_invs:
  assumes "prop_invs (prop_config c0 q)"
    and   "NextPropagate' c0 c1 p"
  shows   "prop_invs (prop_config c1 q)"
  apply (cases "p=q")
  subgoal
    using
      assms(1)
      lift_propagate_inv_propagate_all[
        of prop_invs,
        rotated 2,
        OF NextPropagateD(3)[OF assms(2), rule_format, of p, simplified, symmetric]]
    by (simp add: iiws_imp_iipwn p_preserves_inv_implications_nonneg p_preserves_inv_imps_work_sum)
  subgoal
    by (metis NextPropagateD(3) assms(1) assms(2) option.simps(1))
  done

lemma NextPropagate'_preserves_inv_init_imp_prop_safe:
  assumes "prop_invs (prop_config c0 p)"
    and   "inv_init_imp_prop_safe c0"
    and   "NextPropagate' c0 c1 p"
  shows   "inv_init_imp_prop_safe c1"
  using assms(2) unfolding inv_init_imp_prop_safe_def
  apply clarsimp
  subgoal for p'
    apply (cases "p'=p")
    subgoal
      using NextPropagate'_preserves_prop_invs[OF assms(1,3)]
      using NextPropagate'_causes_safe(1,2)[OF assms(3)] by blast
    subgoal
      using NextPropagateD(2,3)[OF assms(3)]
      by (auto dest: spec[of _ p'])
    done
  done

lemma Next'_preserves_invs:
  assumes "cri.InvMsgInGlob (exchange_config c0)"
    and   "inv_init_imp_prop_safe c0"
    and   "InvGlobPointstampsEq c0"
    and   "Next' c0 c1"
    and   "\<forall>p. prop_invs (prop_config c0 p)"
  shows
    "inv_init_imp_prop_safe c1"
    "\<forall>p. prop_invs (prop_config c1 p)"
    "InvGlobPointstampsEq c1"
  subgoal
    using assms(4) unfolding Next'_def
    using assms(2)
    apply (elim disjE)
    subgoal
      unfolding inv_init_imp_prop_safe_def
      using NextPerformOpD(2,3) by fastforce
    subgoal
      unfolding inv_init_imp_prop_safe_def
      using NextSendUpdD(2,3) by fastforce
    subgoal
      using NextRecvUpd'_preserves_inv_init_imp_prop_safe[OF assms(1,2,3)]
      by blast
    subgoal
      using NextPropagate'_preserves_inv_init_imp_prop_safe assms(5) by blast
    subgoal
      unfolding inv_init_imp_prop_safe_def
      using NextRecvCapD(2,3) by fastforce
    subgoal by simp
    done
  subgoal
    using assms(4) unfolding Next'_def
    using assms(5)
    apply (elim disjE)
    subgoal
      using NextPerformOpD(2) by fastforce
    subgoal
      using NextSendUpdD(2) by fastforce
    subgoal
      using assms(1,2,3) NextRecvUpd'_preserves_prop_invs by blast
    subgoal
      using NextPropagate'_preserves_prop_invs by blast
    subgoal
      unfolding inv_init_imp_prop_safe_def
      using NextRecvCapD(2,3) by fastforce
    subgoal by simp
    done
  subgoal
    using assms(4) unfolding Next'_def
    using assms(3)
    apply (elim disjE)
    subgoal
      by (metis InvGlobPointstampsEq_def NextPerformOpD(1,2) cri.next_performopD(7))
    subgoal
      by (metis InvGlobPointstampsEq_def NextSendUpdD(1,2) cri.next_sendupdD(5))
    subgoal
      using NextRecvUpdD(1) NextRecvUpd'_preserves_InvGlobPointstampsEq assms(1,2) inv_init_imp_prop_safe_def by blast
    subgoal
      unfolding NextPropagate'_def InvGlobPointstampsEq_def
      using propagate_all_imp_InvGlobPointstampsEq
      by (metis option.inject)
    subgoal
      by (metis InvGlobPointstampsEq_def NextRecvCapD(1) NextRecvCapD(2) cri.next_recvcapD(4))
    subgoal by simp
    done
  done

lemma init_imp_InvGlobPointstampsEq: "InitConfig c \<Longrightarrow> InvGlobPointstampsEq c"
  by (simp add: InitConfig_def cri.init_config_def InvGlobPointstampsEq_def)

lemma init_imp_inv_init_imp_prop_safe: "InitConfig c \<Longrightarrow> inv_init_imp_prop_safe c"
  by (simp add: inv_init_imp_prop_safe_def InitConfig_def)

lemma init_imp_prop_invs: "InitConfig c \<Longrightarrow> \<forall>p. prop_invs (prop_config c p)"
  by (simp add: InitConfig_def init_imp_inv_implications_nonneg init_imp_inv_imps_work_sum)

abbreviation all_invs where
  "all_invs c \<equiv> InvGlobPointstampsEq c \<and> inv_init_imp_prop_safe c \<and> (\<forall>p. prop_invs (prop_config c p))"

lemma alw_Next'_alw_invs:
  assumes "holds all_invs s"
    and   "alw (holds (\<lambda>c. cri.InvMsgInGlob (exchange_config c))) s"
    and   "alw Next s"
  shows   "alw (holds all_invs) s"
  using assms
  apply (coinduction arbitrary: s)
  apply clarsimp
  apply safe
       apply (metis (mono_tags, lifting) alw_holds2 Next'_preserves_invs(3) alwD)
      apply (metis (mono_tags, lifting) alw_holds2 Next'_preserves_invs(1) alwD)
     apply (metis (mono_tags, lifting) alw_holds2 Next'_preserves_invs(2) alwD)
    apply (metis (mono_tags, lifting) alw_holds2 Next'_preserves_invs(2) alwD)
   apply auto
  done

lemma alw_invs: "FullSpec s \<Longrightarrow> alw (holds all_invs) s"
  apply (frule exch_alw_InvMsgInGlob)
  unfolding FullSpec_def
  apply clarsimp
  apply (frule init_imp_InvGlobPointstampsEq)
  apply (frule init_imp_inv_init_imp_prop_safe)
  apply (drule init_imp_prop_invs)
  by (simp add: alw_Next'_alw_invs alw_mono)

lemma alw_InvGlobPointstampsEq: "FullSpec s \<Longrightarrow> alw (holds InvGlobPointstampsEq) s"
  using alw_invs alw_mono holds_mono by blast

lemma alw_inv_init_imp_prop_safe: "FullSpec s \<Longrightarrow> alw (holds inv_init_imp_prop_safe) s"
  using alw_invs alw_mono holds_mono by blast

lemma alw_holds_conv_shd: "alw (holds \<phi>) s = alw (\<lambda>s. \<phi> (shd s)) s"
  by (simp add: alw_iff_sdrop)

lemma alw_prop_invs: "FullSpec s \<Longrightarrow> alw (holds (\<lambda>c. \<forall>p. prop_invs (prop_config c p))) s"
  by (auto
      intro: alw_mono[of "holds all_invs" s "holds (\<lambda>c. \<forall>p. prop_invs (prop_config c p))"]
      dest: alw_invs)

lemma nrec_pts_delayed:
  assumes "cri.InvGlobNonposImpRecordsNonpos (exchange_config c)"
    and "zcount (cri.records (exchange_config c)) x > 0"
  shows "\<exists>x'. x' \<le>\<^sub>p x \<and> zcount (c_glob (exchange_config c) p) x' > 0"
proof -
  from assms have r: "\<forall>p. \<not> cri.nonpos_upto (c_glob (exchange_config c) p) x"
    unfolding cri.InvGlobNonposImpRecordsNonpos_def cri.nonpos_upto_def
    by (metis linorder_not_less cri.order.order_iff_strict)
  show ?thesis
    using r[rule_format, of p]
    by (auto simp: cri.nonpos_upto_def not_le)
qed

lemma help_lemma:
  assumes "0 < zcount (c_pts (prop_config c p) loc0) t0"
    and "(loc0, t0) \<le>\<^sub>p (loc1, t1)"
    and "s2 \<in>\<^sub>A path_summary loc1 loc2"
    and "safe (prop_config c p)"
  shows "\<exists> t2. (t2 \<le> results_in t1 s2
                \<and> t2 \<in>\<^sub>A frontier (c_imp (prop_config c p) loc2))"
proof -
  from assms(2) obtain s1 where s1: "s1 \<in>\<^sub>A path_summary loc0 loc1" "results_in t0 s1 \<le> t1"
    by (auto simp add: cri_less_eq_def)
  from s1(1) assms(3) obtain s_full where s_full: "s_full \<in>\<^sub>A path_summary loc0 loc2" "s_full \<le> followed_by s1 s2"
    using flow.path_weight_elem_trans by blast
  from s_full(1) assms(1,4) obtain t2 where t2:
    "t2 \<in>\<^sub>A frontier (c_imp (prop_config c p) loc2)" "t2 \<le> results_in t0 s_full"
    unfolding safe_def by blast
  from t2(2) and s_full(2) have "t2 \<le> results_in (results_in t0 s1) s2"
    by (metis followed_by_summary order_trans results_in_mono(2))
  with s1(2) have "t2 \<le> results_in t1 s2" by (meson order.trans results_in_mono(1))
  with t2(1) show ?thesis by auto
qed

\<comment> \<open>Lift an invariant's preservation proof over @{term next_propagate'} to NextPropagate' transitions\<close>
lemma lift_prop_inv_NextPropagate':
  assumes "(\<And>c0 c1 loc t. P c0 \<Longrightarrow> next_propagate' c0 c1 loc t \<Longrightarrow> P c1)"
  shows   "P (prop_config c0 p') \<Longrightarrow> NextPropagate' c0 c1 p \<Longrightarrow> P (prop_config c1 p')"
proof -
  assume pc0: "P (prop_config c0 p')"
  assume np: "NextPropagate' c0 c1 p"
  have n_p: "(\<And>c0 c1. P c0 \<Longrightarrow> next_propagate c0 c1 \<Longrightarrow> P c1)"
    using assms by auto
  let ?f = "\<lambda>c. SOME c'. next_propagate c c'"
  let ?b = "\<lambda>c. \<exists>loc. c_work c loc \<noteq> {#}\<^sub>z"
  from np have pc1: "Some (prop_config c1 p) = propagate_all (prop_config c0 p)"
    by (simp add: NextPropagate'_def)
  show ?thesis
    apply (cases "p'=p")
    subgoal
      apply (rule while_option_rule[of P ?b ?f "prop_config c0 p"])
        apply (rule n_p)
         apply assumption
        apply (rule iffD1[OF verit_sko_ex])
        apply (elim exE)
        apply (rule exists_next_propagate')
        apply assumption
      using pc1 apply (simp add: propagate_all_def)
      using pc0 apply simp
      done
    subgoal
      using np pc0 by (auto simp: NextPropagate'_def dest!: spec[of _ p'])
    done
qed

subsubsection\<open>Propagate is a Subsystem\<close>


lemma NextRecvUpd'_next':
  assumes "safe (prop_config c0 q)"
    and   "InvGlobPointstampsEq c0"
    and   "cri.InvMsgInGlob (exchange_config c0)"
    and   "NextRecvUpd' c0 c1 p q"
  shows   "next'\<^sup>+\<^sup>+ (prop_config c0 q') (prop_config c1 q')"
  apply (subst NextRecvUpdD(4)[OF assms(4), rule_format])
  apply simp
  apply safe
  subgoal
    apply (subst cm_all_eq_cm_all')
     apply clarsimp
     apply (drule assms(3)[unfolded cri.InvMsgInGlob_def, rule_format, OF cri.next_recvupdD(1)[OF NextRecvUpdD(2)[OF assms(4)]]])
     apply clarsimp
    subgoal for loc t loc' t'
      apply (subst (asm) assms(2)[unfolded InvGlobPointstampsEq_def, rule_format, symmetric])
      apply (clarsimp simp: cri_less_eq_def)
      subgoal for s
        using assms(1)[unfolded safe_def, rule_format, of loc' t' s loc]
        apply -
        apply (drule meta_mp)
         apply simp
        apply clarsimp
        subgoal for t''
          apply (clarsimp intro!: exI[of _ t''])
          using order_trans apply blast
          done
        done
      done
    apply (rule lift_cm_inv_cm_all')
      apply (rule tranclp.intros(2))
       apply (auto simp: next'_def) [2]
     apply clarsimp
     apply (drule assms(3)[unfolded cri.InvMsgInGlob_def, rule_format, OF cri.next_recvupdD(1)[OF NextRecvUpdD(2)[OF assms(4)]]])
     apply clarsimp
    subgoal for loc t loc' t'
      apply (subst (asm) assms(2)[unfolded InvGlobPointstampsEq_def, rule_format, symmetric])
      apply (clarsimp simp: cri_less_eq_def)
      subgoal for s
        using assms(1)[unfolded safe_def, rule_format, of loc' t' s loc]
        apply -
        apply (drule meta_mp)
         apply simp
        apply clarsimp
        subgoal for t''
          apply (clarsimp intro!: exI[of _ t''])
          using order_trans apply blast
          done
        done
      done
    apply (auto simp: next'_def)
    done
  apply (auto simp: next'_def)
  done

lemma NextPropagate'_next':
  assumes "NextPropagate' c0 c1 p"
  shows   "next'\<^sup>+\<^sup>+ (prop_config c0 q) (prop_config c1 q)"
  apply (cases "p=q")
  subgoal
    apply (rule lift_propagate_inv_propagate_all[of _ "prop_config c0 p"])
      apply (rule tranclp.intros(2))
       apply (auto simp: next'_def NextPropagateD(3)[OF assms, rule_format])
    done
  subgoal
    by (metis NextPropagateD(3) assms next'_def option.simps(1) tranclp.intros(1))
  done

lemma next_imp_propagate_next:
  assumes "inv_init_imp_prop_safe c0"
    and   "InvGlobPointstampsEq c0"
    and   "cri.InvMsgInGlob (exchange_config c0)"
  shows   "Next' c0 c1 \<Longrightarrow> next'\<^sup>+\<^sup>+ (prop_config c0 p) (prop_config c1 p)"
  unfolding Next'_def NextPerformOp'_def NextSendUpd'_def NextRecvCap'_def
  apply safe
  subgoal by (auto simp: next'_def)
  subgoal by (auto simp: next'_def)
  subgoal for p' q
    using assms(1)[unfolded inv_init_imp_prop_safe_def, rule_format, of q]
    apply -
    apply (drule meta_mp)
     apply (rule NextRecvUpdD(1))
     apply simp    
    apply (cases "q=p")
     apply (auto dest!: NextRecvUpd'_next'[rotated, OF assms(2-)]) []
    apply (auto simp add: NextRecvUpd'_def next'_def)
    done
  subgoal by (rule NextPropagate'_next')
  subgoal by (auto simp: next'_def)
  subgoal by (auto simp: next'_def)
  done

lemma alw_next_imp_propagate_next:
  assumes "alw (holds inv_init_imp_prop_safe) s"
    and   "alw (holds InvGlobPointstampsEq) s"
    and   "alw (holds cri.InvMsgInGlob) (smap exchange_config s)"
    and   "alw Next s"
  shows   "alw (relates (next'\<^sup>+\<^sup>+)) (smap (\<lambda>s. prop_config s p) s)"
  using assms by (coinduction arbitrary: s rule: alw.coinduct) (auto intro!: next_imp_propagate_next simp: relates_def alw_holds_smap_conv_comp)

text\<open>Any Tracker trace is a valid Propagate trace (using the transitive closure of next, since
tracker may take multiple propagate steps at once).\<close>
lemma spec_imp_propagate_spec: "FullSpec s \<Longrightarrow> (holds init_config aand alw (relates (next'\<^sup>+\<^sup>+))) (smap (\<lambda>c. prop_config c p) s)"
  apply (frule alw_inv_init_imp_prop_safe)
  apply (frule alw_InvGlobPointstampsEq)
  apply (frule spec_imp_exchange_spec)
  apply (drule cri.alw_InvMsgInGlob)
  apply (auto intro!: alw_next_imp_propagate_next simp: FullSpec_def InitConfig_def)
  done

subsection\<open>Safety Proofs\<close>

lemma safe_satisfied:
  assumes "cri.InvGlobNonposImpRecordsNonpos (exchange_config c)"
    and "inv_init_imp_prop_safe c"
    and "InvGlobPointstampsEq c"
  shows "safe_combined c"
proof -
  {
    fix loc1 loc2 t s p
    assume as: "0 < zcount (cri.records (exchange_config c)) (loc1, t)"
      "s \<in>\<^sub>A path_summary loc1 loc2" "init c p"
    obtain loc0 t0 where delayed:
      "(loc0, t0) \<le>\<^sub>p (loc1, t)" "0 < zcount (c_glob (exchange_config c) p) (loc0, t0)"
      using nrec_pts_delayed[OF assms(1) as(1)]
      by fast
    with as(2,3) assms(2) have
      "\<exists>t2. t2 \<le> results_in t s \<and> t2 \<in>\<^sub>A frontier (c_imp (prop_config c p) loc2)"
      using help_lemma delayed
      by (metis InvGlobPointstampsEq_def assms(3) inv_init_imp_prop_safe_def)
  }
  then show ?thesis
    unfolding safe_combined_def by blast
qed

lemma alw_safe_combined: "FullSpec s \<Longrightarrow> alw (holds safe_combined) s"
  apply (frule alw_inv_init_imp_prop_safe)
  apply (frule exch_alw_InvGlobNonposImpRecordsNonpos)
  apply (drule alw_InvGlobPointstampsEq)
  apply (coinduction arbitrary: s rule: alw.coinduct)
  apply clarsimp
  apply (rule conjI)
   apply (metis alwD alw_holds2 safe_satisfied)
  apply (rule disjI1)
  apply blast
  done

lemma alw_safe_combined2: "FullSpec s \<Longrightarrow> alw (holds safe_combined2) s"
  apply (frule exch_alw_InvCapsNonneg)
  apply (drule alw_safe_combined)
  apply (simp add: alw_iff_sdrop safe_combined_implies_safe_combined2)
  done

lemma alw_implication_frontier_eq_implied_frontier:
  "FullSpec s \<Longrightarrow> 
    alw (holds (\<lambda>c. worklists_vacant_to (prop_config c p) b \<longrightarrow>
      b \<in>\<^sub>A frontier (c_imp (prop_config c p) loc) \<longleftrightarrow> b \<in>\<^sub>A implied_frontier (c_pts (prop_config c p)) loc)) s"
  by (drule alw_prop_invs)
    (auto simp: implication_frontier_iff_implied_frontier_vacant all_imp_alw elim: alw_mp)

end

(*<*)
end
(*>*)