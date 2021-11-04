section \<open>Traces\<close>

text \<open>Traces extend transitions to finitely many intermediate events.\<close>

theory Trace
  imports
    "HOL-Library.Sublist"
    Distributed_System

begin

context distributed_system

begin

text \<open>We can think of a trace as the transitive closure of the next
relation. A trace consists of initial and final configurations $c$ and
$c'$, with an ordered list of events $t$ occurring sequentially on $c$,
yielding $c'$.\<close>

inductive (in distributed_system) trace where
    tr_init: "trace c [] c"
  | tr_step: "\<lbrakk> c \<turnstile> ev \<mapsto> c'; trace c' t c'' \<rbrakk>
              \<Longrightarrow> trace c (ev # t) c''"

subsection \<open>Properties of traces\<close>

lemma trace_trans:
  shows
    "\<lbrakk> trace c t c';
       trace c' t' c''
     \<rbrakk> \<Longrightarrow> trace c (t @ t') c''"
proof (induct c t c' rule:trace.induct)
  case tr_init
  then show ?case by simp
next
  case tr_step
  then show ?case using trace.tr_step by auto
qed

lemma trace_decomp_head:
  assumes
    "trace c (ev # t) c'"
  shows
    "\<exists>c''. c \<turnstile> ev \<mapsto> c'' \<and> trace c'' t c'"
  using assms trace.simps by blast

lemma trace_decomp_tail:
  shows
    "trace c (t @ [ev]) c' \<Longrightarrow> \<exists>c''. trace c t c'' \<and> c'' \<turnstile> ev \<mapsto> c'"
proof (induct t arbitrary: c)
  case Nil
  then show ?case 
    by (metis (mono_tags, lifting) append_Nil distributed_system.trace.simps distributed_system_axioms list.discI list.sel(1) list.sel(3))
next
  case (Cons ev' t)
  then obtain d where step: "c \<turnstile> ev' \<mapsto> d" and "trace d (t @ [ev]) c'" using trace_decomp_head by force
  then obtain d' where tr: "trace d t d'" and "d' \<turnstile> ev \<mapsto> c'" using Cons.hyps by blast
  moreover have "trace c (ev' # t) d'" using step tr trace.tr_step by simp
  ultimately show ?case by auto
qed

lemma trace_snoc: 
  assumes
    "trace c t c'" and
    "c' \<turnstile> ev \<mapsto> c''"
  shows
    "trace c (t @ [ev]) c''"
  using assms(1) assms(2) tr_init tr_step trace_trans by auto

lemma trace_rev_induct [consumes 1, case_names tr_rev_init tr_rev_step]:
  "\<lbrakk> trace c t c';
     (\<And>c. P c [] c);
     (\<And>c t c' ev c''. trace c t c' \<Longrightarrow> P c t c' \<Longrightarrow> c' \<turnstile> ev \<mapsto> c'' \<Longrightarrow> P c (t @ [ev]) c'')
   \<rbrakk> \<Longrightarrow> P c t c'"
proof (induct t arbitrary: c' rule:rev_induct)
  case Nil
  then show ?case 
    using distributed_system.trace.cases distributed_system_axioms by blast
next
  case (snoc ev t)
  then obtain c'' where "trace c t c''" "c'' \<turnstile> ev \<mapsto> c'" using trace_decomp_tail by blast
  then show ?case using snoc by simp
qed

lemma trace_and_start_determines_end:
  shows
    "trace c t c' \<Longrightarrow> trace c t d' \<Longrightarrow> c' = d'"
proof (induct c t c' arbitrary: d' rule:trace_rev_induct)
  case tr_rev_init
  then show ?case using trace.cases by fastforce
next
  case (tr_rev_step c t c' ev c'')
  then obtain d'' where "trace c t d''" "d'' \<turnstile> ev \<mapsto> d'" using trace_decomp_tail by blast
  then show ?case using tr_rev_step state_and_event_determine_next by simp
qed

lemma suffix_split_trace:
  shows
    "\<lbrakk> trace c t c';
       suffix t' t
     \<rbrakk> \<Longrightarrow> \<exists>c''. trace c'' t' c'"
proof (induct t arbitrary: c)
  case Nil
  then have "t' = []" by simp
  then have "trace c' t' c'" using tr_init by simp
  then show ?case by blast
next
  case (Cons ev t'')
  from Cons.prems have q: "suffix t' t'' \<or> t' = ev # t''" by (meson suffix_Cons)
  thus ?case
  proof (cases "suffix t' t''")
    case True
    then show ?thesis using Cons.hyps Cons.prems(1) trace.simps by blast
  next
    case False
    hence "t' = ev # t''" using q by simp
    thus ?thesis using Cons.hyps Cons.prems by blast
  qed
qed

lemma prefix_split_trace:
  fixes
    c :: "('p, 's, 'm) configuration" and
    t :: "('p, 's, 'm) trace"
  shows
    "\<lbrakk> \<exists>c'. trace c t c';
       prefix t' t
     \<rbrakk> \<Longrightarrow> \<exists>c''. trace c t' c''"
proof (induct t rule:rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc ev t'')
  from snoc.prems have q: "prefix t' t'' \<or> t' = t'' @ [ev]" by auto
  thus ?case
  proof (cases "prefix t' t''")
    case True
    thus ?thesis using trace_decomp_tail using snoc.hyps snoc.prems(1) trace.simps by blast
  next
    case False
    thus ?thesis using q snoc.prems by fast
  qed
qed

lemma split_trace:
  shows
    "\<lbrakk> trace c t c';
       t = t' @ t''
     \<rbrakk> \<Longrightarrow> \<exists>c''. trace c t' c'' \<and> trace c'' t'' c'"
proof (induct t'' arbitrary: t')
  case Nil
  then show ?case using tr_init by auto
next
  case (Cons ev t'')
  obtain c'' where p: "trace c (t' @ [ev]) c''"
    using Cons.prems prefix_split_trace rotate1.simps(2) by force
  then have "trace c'' t'' c'"
    using Cons.hyps Cons.prems trace_and_start_determines_end by force
  then show ?case
    by (meson distributed_system.tr_step distributed_system.trace_decomp_tail distributed_system_axioms p)
qed

subsection \<open>Describing intermediate configurations\<close>

definition construct_fun_from_rel :: "('a * 'b) set \<Rightarrow> 'a \<Rightarrow> 'b" where
  "construct_fun_from_rel R x = (THE y. (x,y) \<in> R)"

definition trace_rel where
  "trace_rel \<equiv> {((x, t'), y). trace x t' y}"

lemma fun_must_admit_trace:
  shows
    "single_valued R \<Longrightarrow> x \<in> Domain R
     \<Longrightarrow> (x, construct_fun_from_rel R x) \<in> R"
  unfolding construct_fun_from_rel_def
  by (rule theI') (auto simp add: single_valued_def)

lemma single_valued_trace_rel:
  shows
    "single_valued trace_rel"
proof (rule single_valuedI)
  fix x y y'
  assume asm: "(x, y) \<in> trace_rel" "(x, y') \<in> trace_rel"
  then obtain x' t where "x = (x', t)"
    by (meson surj_pair)
  then have "trace x' t y" "trace x' t y'"
    using asm trace_rel_def by auto
  then show "y = y'"
    using trace_and_start_determines_end by blast
qed

definition run_trace where
  "run_trace \<equiv> construct_fun_from_rel trace_rel"

text \<open>In order to describe intermediate configurations
of a trace we introduce the $s$ function definition, which,
given an initial configuration $c$, a trace $t$ and an index $i \in \mathbb{N}$,
determines the unique state after the first $i$ events of $t$.\<close>

definition s where
  "s c t i = (THE c'. trace c (take i t) c')"

lemma s_is_partial_execution:
  shows
    "s c t i = run_trace (c, take i t)"
  unfolding s_def run_trace_def
            construct_fun_from_rel_def trace_rel_def
  by auto

lemma exists_trace_for_any_i:
  assumes
    "\<exists>c'. trace c t c'"
  shows
    "trace c (take i t) (s c t i)"
proof -
  have "prefix (take i t) t" using take_is_prefix by auto
  then obtain c'' where tr: "trace c (take i t) c''" using assms prefix_split_trace by blast
  then show ?thesis
  proof -
    have "((c, take i t), s c t i) \<in> trace_rel"
      unfolding s_def trace_rel_def construct_fun_from_rel_def 
      by (metis case_prod_conv distributed_system.trace_and_start_determines_end distributed_system_axioms mem_Collect_eq the_equality tr)
    then show ?thesis by (simp add: trace_rel_def)
  qed
qed

lemma exists_trace_for_any_i_j:
  assumes
    "\<exists>c'. trace c t c'" and
    "i \<le> j"
  shows
    "trace (s c t i) (take (j - i) (drop i t)) (s c t j)"
proof -
  have "trace c (take j t) (s c t j)" using exists_trace_for_any_i assms by simp
  from \<open>j \<ge> i\<close> have "take j t = take i t @ (take (j - i) (drop i t))"
    by (metis le_add_diff_inverse take_add)
  then have "trace c (take i t) (s c t i) \<and> trace (s c t i) (take (j - i) (drop i t)) (s c t j)"
    by (metis (no_types, lifting) assms(1) exists_trace_for_any_i split_trace trace_and_start_determines_end)
  then show ?thesis by simp
qed

lemma step_Suc:
  assumes
    "i < length t" and
    valid: "trace c t c'"
  shows "(s c t i) \<turnstile> (t ! i) \<mapsto> (s c t (Suc i))"
proof -
  have ex_trace: "trace (s c t i) (take (Suc i - i) (drop i t)) (s c t (Suc i))"
    using exists_trace_for_any_i_j le_less valid by blast
  moreover have "Suc i - i = 1" by auto
  moreover have "take 1 (drop i t) = [t ! i]"
    by (metis \<open>Suc i - i = 1\<close> assms(1) hd_drop_conv_nth le_add_diff_inverse lessI nat_less_le same_append_eq take_add take_hd_drop)
  ultimately show ?thesis
    by (metis list.discI trace.simps trace_decomp_head)
qed

subsection \<open>Trace-related lemmas\<close>

lemma snapshot_state_unchanged_trace:
  assumes
    "trace c t c'" and
    "ps c p = Some u"
  shows
    "ps c' p = Some u"
  using assms snapshot_state_unchanged by (induct c t c', auto)

lemma no_state_change_if_only_nonregular_events:
  shows
    "\<lbrakk> trace c t c';
       \<nexists>ev. ev \<in> set t \<and> regular_event ev \<and> occurs_on ev = p;
       states c p = st
     \<rbrakk> \<Longrightarrow> states c' p = st"
proof (induct c t c' rule:trace_rev_induct)
  case (tr_rev_init c)
  then show ?case by simp
next
  case (tr_rev_step c t c' ev c'')
  then have "states c' p = st"
  proof -
    have "\<nexists>ev. ev : set t \<and> regular_event ev \<and> occurs_on ev = p" 
      using tr_rev_step by auto
    then show ?thesis using tr_rev_step by blast
  qed
  then show ?case
    using tr_rev_step no_state_change_if_no_event no_state_change_if_nonregular_event
    by auto
qed

lemma message_must_be_delivered_2_trace:
  assumes
    "trace c t c'" and
    "m : set (msgs c i)" and
    "m \<notin> set (msgs c' i)" and
    "channel i = Some (q, p)"
  shows
    "\<exists>ev \<in> set t. (\<exists>p q. ev = RecvMarker i p q \<and> m = Marker) \<or> (\<exists>p q s s' m'. ev = Recv i q p s s' m' \<and> m = Msg m')"
proof (rule ccontr)
  assume "~ (\<exists>ev \<in> set t. (\<exists>p q. ev = RecvMarker i p q \<and> m = Marker) \<or> (\<exists>p q s s' m'. ev = Recv i q p s s' m' \<and> m = Msg m'))" (is ?P)
  have "\<lbrakk> trace c t c'; m : set (msgs c i); ?P \<rbrakk> \<Longrightarrow> m : set (msgs c' i)"
  proof (induct c t c' rule:trace_rev_induct)
    case (tr_rev_init c)
    then show ?case by simp
  next
    case (tr_rev_step c t d ev c')
    then have m_in_set: "m : set (msgs d i)" 
      using tr_rev_step by auto
    then show ?case
    proof (cases ev)
      case (Snapshot r)
      then show ?thesis 
        using distributed_system.message_must_be_delivered_2 distributed_system_axioms m_in_set tr_rev_step.hyps(3) by blast
    next
      case (RecvMarker i' r s)
      then show ?thesis
      proof (cases "m = Marker")
        case True
        then have "i' \<noteq> i" using tr_rev_step RecvMarker by simp
        then show ?thesis 
          using RecvMarker m_in_set message_must_be_delivered_2 tr_rev_step.hyps(3) by blast
      next
        case False
        then show ?thesis 
          using RecvMarker tr_rev_step.hyps(3) m_in_set message_must_be_delivered_2 by blast
      qed
    next
      case (Trans r u u')
      then show ?thesis 
        using tr_rev_step.hyps(3) m_in_set by auto
    next
      case (Send i' r s u u' m')
      then show ?thesis 
        using distributed_system.message_must_be_delivered_2 distributed_system_axioms m_in_set tr_rev_step.hyps(3) by blast
    next
      case (Recv i' r s u u' m')
      then show ?thesis
      proof (cases "Msg m' = m")
        case True
        then have "i' \<noteq> i" using Recv tr_rev_step by auto
        then show ?thesis 
          using Recv m_in_set tr_rev_step(3) by auto
      next
        case False
        then show ?thesis 
          by (metis Recv event.distinct(17) event.inject(3) m_in_set message_must_be_delivered_2 tr_rev_step.hyps(3))
      qed
    qed
  qed
  then have "m : set (msgs c' i)" using assms \<open>?P\<close> by auto
  then show False using assms by simp
qed

lemma marker_must_be_delivered_2_trace:
  assumes
    "trace c t c'" and
    "Marker : set (msgs c i)" and
    "Marker \<notin> set (msgs c' i)" and
    "channel i = Some (p, q)"
  shows
    "\<exists>ev \<in> set t. (\<exists>p q. ev = RecvMarker i p q)"
proof -
  show "\<exists>ev \<in> set t. (\<exists>p q. ev = RecvMarker i p q)"
    using assms message_must_be_delivered_2_trace by fast
qed

lemma snapshot_stable:
  shows
    "\<lbrakk> trace c t c';
       has_snapshotted c p
     \<rbrakk> \<Longrightarrow> has_snapshotted c' p"
proof (induct c t c' rule:trace_rev_induct)
  case (tr_rev_init c)
  then show ?case by blast
next
  case (tr_rev_step c t c' ev c'')
  then show ?case
  proof (cases ev)
    case (Snapshot q)
    then have "p \<noteq> q" using tr_rev_step next_snapshot can_occur_def by auto
    then show ?thesis using Snapshot tr_rev_step by auto
  next
    case (RecvMarker i q r)
    with tr_rev_step show ?thesis
      by (cases "p = q"; auto)
  qed simp_all
qed

lemma snapshot_stable_2:
  shows
    "trace c t c' \<Longrightarrow> ~ has_snapshotted c' p \<Longrightarrow> ~ has_snapshotted c p"
  using snapshot_stable by blast

lemma no_markers_if_all_snapshotted:
  shows
    "\<lbrakk> trace c t c';
      \<forall>p. has_snapshotted c p;
      Marker \<notin> set (msgs c i)
     \<rbrakk> \<Longrightarrow> Marker \<notin> set (msgs c' i)"
proof (induct c t c' rule:trace_rev_induct)
  case (tr_rev_init c)
  then show ?case by simp
next
  case (tr_rev_step c t c' ev c'')
  have all_snapshotted: "\<forall>p. has_snapshotted c' p" using snapshot_stable tr_rev_step by auto
  have no_marker: "Marker \<notin> set (msgs c' i)" using tr_rev_step by blast
  then show ?case
  proof (cases ev)
    case (Snapshot r)
    then show ?thesis using can_occur_def tr_rev_step all_snapshotted by auto
  next
    case (RecvMarker i' r s)
    have "i' \<noteq> i"
    proof (rule ccontr)
      assume "~ i' \<noteq> i"
      then have "Marker : set (msgs c i)"
        using can_occur_def RecvMarker tr_rev_step  RecvMarker_implies_Marker_in_set by blast
      then show False using tr_rev_step by simp
    qed
    then show ?thesis using tr_rev_step all_snapshotted no_marker RecvMarker by auto
  next
    case (Trans p s s')
    then show ?thesis using tr_rev_step no_marker by auto
  next
   case (Send i' r s u u' m)
   then show ?thesis
   proof (cases "i' = i")
     case True
     then have "msgs c'' i = msgs c' i @ [Msg m]" using tr_rev_step Send by auto
     then show ?thesis using no_marker by auto
   next
     case False
     then show ?thesis using Send tr_rev_step no_marker by auto
   qed
  next
    case (Recv i' r s u u' m)
    then show ?thesis
    proof (cases "i = i'")
      case True
      then have "msgs c'' i = tl (msgs c' i)" using tr_rev_step Recv by auto
      then show ?thesis using no_marker by (metis list.sel(2) list.set_sel(2))
    next
      case False
      then show ?thesis using Recv tr_rev_step no_marker by auto
    qed
  qed
qed

lemma event_stays_valid_if_no_occurrence_trace:
  shows
    "\<lbrakk> trace c t c';
       list_all (\<lambda>ev. occurs_on ev \<noteq> occurs_on ev') t;
       can_occur ev' c
     \<rbrakk> \<Longrightarrow> can_occur ev' c'"
proof (induct c t c' rule:trace_rev_induct)
  case tr_rev_init
  then show ?case by blast
next
  case tr_rev_step
  then show ?case using event_stays_valid_if_no_occurrence by auto
qed

lemma event_can_go_back_if_no_sender_trace:
  shows
    "\<lbrakk> trace c t c';
       list_all (\<lambda>ev. occurs_on ev \<noteq> occurs_on ev') t;
       can_occur ev' c';
       ~ isRecvMarker ev';
       list_all (\<lambda>ev. ~ isSend ev) t
     \<rbrakk> \<Longrightarrow> can_occur ev' c"
proof (induct c t c' rule:trace_rev_induct)
  case tr_rev_init
  then show ?case by blast
next
  case tr_rev_step
  then show ?case using event_can_go_back_if_no_sender by auto
qed

lemma done_only_from_recv_marker_trace:
  assumes
    "trace c t c'" and
    "t \<noteq> []" and
    "snd (cs c cid) \<noteq> Done" and
    "snd (cs c' cid) = Done" and
    "channel cid = Some (p, q)"
  shows
    "RecvMarker cid q p \<in> set t"
proof (rule ccontr)
  assume "~ RecvMarker cid q p \<in> set t"
  moreover have "\<lbrakk> trace c t c'; ~ RecvMarker cid q p \<in> set t; snd (cs c cid) \<noteq> Done; channel cid = Some (p, q) \<rbrakk>
                 \<Longrightarrow> snd (cs c' cid) \<noteq> Done"
  proof (induct t arbitrary: c' rule:rev_induct)
    case Nil
    then show ?case 
      by (metis list.discI trace.simps)
  next
    case (snoc ev t)
    then obtain d where ind: "trace c t d" and step: "d \<turnstile> ev \<mapsto> c'" 
      using trace_decomp_tail by blast
    then have "snd (cs d cid) \<noteq> Done"
    proof -
      have "~ RecvMarker cid q p \<in> set t" 
        using snoc.prems(2) by auto
      then show ?thesis using snoc ind by blast
    qed
    then show ?case 
      using done_only_from_recv_marker local.step snoc.prems(2) snoc.prems(4) by auto
  qed
  ultimately have "snd (cs c' cid) \<noteq> Done" using assms by blast
  then show False using assms by simp
qed

lemma cs_not_not_started_stable_trace:
  shows
    "\<lbrakk> trace c t c'; snd (cs c cid) \<noteq> NotStarted; channel cid = Some (p, q) \<rbrakk> \<Longrightarrow> snd (cs c' cid) \<noteq> NotStarted"
proof (induct t arbitrary:c' rule:rev_induct)
  case Nil
  then show ?case 
    by (metis list.discI trace.simps)
next
  case (snoc ev t)
  then obtain d where tr: "trace c t d" and step: "d \<turnstile> ev \<mapsto> c'" 
    using trace_decomp_tail by blast
  then have "snd (cs d cid) \<noteq> NotStarted" using snoc by blast
  then show ?case using cs_not_not_started_stable snoc step by blast
qed

lemma no_messages_introduced_if_no_channel:
  assumes
    trace: "trace init t final" and
    no_msgs_if_no_channel: "\<forall>i. channel i = None \<longrightarrow> msgs init i = []"
  shows
    "channel cid = None \<Longrightarrow> msgs (s init t i) cid = []"
proof (induct i)
  case 0
  then show ?case
    by (metis assms exists_trace_for_any_i no_msgs_if_no_channel take0 tr_init trace_and_start_determines_end)
next
  case (Suc n)
  have f: "trace (s init t n) (take ((Suc n) - n) (drop n t)) (s init t (Suc n))"
    using exists_trace_for_any_i_j order_le_less trace assms by blast
  then show ?case
  proof (cases "drop n t = Nil")
    case True
    then show ?thesis using Suc.hyps Suc.prems
      by (metis f tr_init trace_and_start_determines_end take_Nil) 
  next
    case False
    have suc_n_minus_n: "Suc n - n = 1" by auto
    then have "length (take ((Suc n) - n) (drop n t)) = 1" using False by auto
    then obtain ev where "ev # Nil = take ((Suc n) - n) (drop n t)"
      by (metis False One_nat_def suc_n_minus_n length_greater_0_conv self_append_conv2 take_eq_Nil take_hd_drop)
    then have g: "(s init t n) \<turnstile> ev \<mapsto> (s init t (Suc n))"
      by (metis f tr_init trace_and_start_determines_end trace_decomp_head)
    then show ?thesis
    proof (cases ev)
      case (Snapshot r)
      then show ?thesis 
        using Suc.hyps Suc.prems g by auto
    next
      case (RecvMarker cid' sr r)
      have "cid' \<noteq> cid" using RecvMarker can_occur_def g Suc by auto
      with RecvMarker Suc g show ?thesis by (cases "has_snapshotted (s init t n) sr", auto)
    next
      case (Trans r u u')
      then show ?thesis
        by (metis Suc.hyps Suc.prems g next_trans)
    next
      case (Send cid' r s u u' m)
      have "cid' \<noteq> cid" using Send can_occur_def g Suc by auto
      then show ?thesis using Suc g Send by simp
    next
      case (Recv cid' s r u u' m)
      have "cid' \<noteq> cid" using Recv can_occur_def g Suc by auto
      then show ?thesis using Suc g Recv by simp
    qed
  qed
qed

end (* context distributed_system *)

end (* theory Trace *)
