section \<open>The Chandy--Lamport algorithm\<close>

theory Snapshot
  imports
    "HOL-Library.Sublist"
    "HOL-Library.Permutation"
    Distributed_System
    Trace
    Util
    Swap

begin

subsection \<open>The computation locale\<close>

text \<open>We extend the distributed system locale presented
earlier: Now we are given a trace t of the distributed system between
two configurations, the initial and final configuartions of t. Our objective
is to show that the Chandy--Lamport algorithm terminated successfully and
exhibits the same properties as claimed in~\cite{chandy}. In the initial state
no snapshotting must have taken place yet, however the computation itself may
have progressed arbitrarily far already.

We assume that there exists at least one process, that the
total number of processes in the system is finite, and that there
are only finitely many channels between the processes. The process graph
is strongly connected. Finally there are Chandy and Lamport's core assumptions:
every process snapshots at some time and no marker may remain in a channel forever.\<close>

locale computation = distributed_system +
  fixes
    init final :: "('a, 'b, 'c) configuration"
  assumes
    finite_channels:
      "finite {i. \<exists>p q. channel i = Some (p, q)}" and
    strongly_connected_raw:
      "\<forall>p q. (p \<noteq> q) \<longrightarrow>
         (tranclp (\<lambda>p q. (\<exists>i. channel i = Some (p, q)))) p q" and

    at_least_two_processes:
      "card (UNIV :: 'a set) > 1" and
    finite_processes:
      "finite (UNIV :: 'a set)" and

    no_initial_Marker:
      "\<forall>i. (\<exists>p q. channel i = Some (p, q))
      \<longrightarrow> Marker \<notin> set (msgs init i)" and
    no_msgs_if_no_channel:
      "\<forall>i. channel i = None \<longrightarrow> msgs init i = []" and
    no_initial_process_snapshot:
      "\<forall>p. ~ has_snapshotted init p" and
    no_initial_channel_snapshot:
      "\<forall>i. channel_snapshot init i = ([], NotStarted)" and

    valid: "\<exists>t. trace init t final" and
    l1: "\<forall>t i cid. trace init t final
                 \<and> Marker \<in> set (msgs (s init t i) cid)
      \<longrightarrow> (\<exists>j. j \<ge> i \<and> Marker \<notin> set (msgs (s init t j) cid))" and
    l2: "\<forall>t p. trace init t final
      \<longrightarrow> (\<exists>i. has_snapshotted (s init t i) p \<and> i \<le> length t)"
begin

definition has_channel where
  "has_channel p q \<longleftrightarrow> (\<exists>i. channel i = Some (p, q))"

lemmas strongly_connected = strongly_connected_raw[folded has_channel_def]

lemma exists_some_channel:
  shows "\<exists>i p q. channel i = Some (p, q)"
proof -
  obtain p q where "p : (UNIV :: 'a set) \<and> q : (UNIV :: 'a set) \<and> p \<noteq> q" 
    by (metis (mono_tags) One_nat_def UNIV_eq_I all_not_in_conv at_least_two_processes card_Suc_Diff1 card.empty finite_processes insert_iff iso_tuple_UNIV_I less_numeral_extra(4) n_not_Suc_n)
  then have "(tranclp has_channel) p q" using strongly_connected by simp
  then obtain r s where "has_channel r s" 
    by (meson tranclpD)
  then show ?thesis using has_channel_def by auto
qed

abbreviation S where
  "S \<equiv> s init"

lemma no_messages_if_no_channel:
  assumes "trace init t final"
  shows "channel cid = None \<Longrightarrow> msgs (s init t i) cid = []"
  using no_messages_introduced_if_no_channel[OF assms no_msgs_if_no_channel] by blast

lemma S_induct [consumes 3, case_names S_init S_step]:
  "\<lbrakk> trace init t final; i \<le> j; j \<le> length t;
     \<And>i. P i i;
     \<And>i j. i < j \<Longrightarrow> j \<le> length t \<Longrightarrow> (S t i) \<turnstile> (t ! i) \<mapsto> (S t (Suc i)) \<Longrightarrow> P (Suc i) j \<Longrightarrow> P i j
   \<rbrakk> \<Longrightarrow> P i j"
proof (induct "j - i" arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (Suc i))" using Suc step_Suc by simp
  then show ?case using Suc by simp
qed

lemma exists_index:
  assumes
    "trace init t final" and
    "ev \<in> set (take (j - i) (drop i t))"
  shows
    "\<exists>k. i \<le> k \<and> k < j \<and> ev = t ! k"
proof -
  have "trace (S t i) (take (j - i) (drop i t)) (S t j)" 
    by (metis assms(1) assms(2) diff_is_0_eq' exists_trace_for_any_i_j list.distinct(1) list.set_cases nat_le_linear take_eq_Nil)
  obtain l where "ev = (take (j - i) (drop i t)) ! l" "l < length (take (j - i) (drop i t))"
    by (metis assms(2) in_set_conv_nth)
  let ?k = "l + i"
  have "(take (j - i) (drop i t)) ! l = drop i t ! l" 
    using \<open>l < length (take (j - i) (drop i t))\<close> by auto
  also have "... = t ! ?k" 
    by (metis add.commute assms(2) drop_all empty_iff list.set(1) nat_le_linear nth_drop take_Nil)
  finally have "ev = t ! ?k" 
    using \<open>ev = take (j - i) (drop i t) ! l\<close> by blast
  moreover have "i \<le> ?k \<and> ?k < j" 
    using \<open>l < length (take (j - i) (drop i t))\<close> by auto
  ultimately show ?thesis by blast
qed

lemma no_change_if_ge_length_t:
  assumes
    "trace init t final" and
    "i \<ge> length t" and
    "j \<ge> i"
  shows
    "S t i = S t j"
proof -
  have "trace (S t i) (take (j - i) (drop i t)) (S t j)" 
    using assms(1) assms(3) exists_trace_for_any_i_j by blast
  moreover have "(take (j - i) (drop i t)) = Nil" 
    by (simp add: assms(2))
  ultimately show ?thesis 
    by (metis tr_init trace_and_start_determines_end)
qed

lemma no_marker_if_no_snapshot:
  shows
    "\<lbrakk> trace init t final; channel cid = Some (p, q);
       ~ has_snapshotted (S t i) p \<rbrakk>
     \<Longrightarrow>  Marker \<notin> set (msgs (S t i) cid)"
proof (induct i)
  case 0
  then show ?case 
    by (metis exists_trace_for_any_i no_initial_Marker take_eq_Nil tr_init trace_and_start_determines_end)
next
  case (Suc n)
  then have IH: "Marker \<notin> set (msgs (S t n) cid)" 
    by (meson distributed_system.exists_trace_for_any_i_j distributed_system.snapshot_stable_2 distributed_system_axioms eq_iff le_Suc_eq)
  then obtain tr where decomp: "trace (S t n) tr (S t (Suc n))" "tr = take (Suc n - n) (drop n t)"
    using Suc exists_trace_for_any_i_j le_Suc_eq by blast
  have "Marker \<notin> set (msgs (S t (Suc n)) cid)"
  proof (cases "tr = []")
    case True
    then show ?thesis 
      by (metis IH decomp(1) tr_init trace_and_start_determines_end)
  next
    case False
    then obtain ev where step: "tr = [ev]" "(S t n) \<turnstile> ev \<mapsto> (S t (Suc n))" 
      by (metis One_nat_def Suc_eq_plus1 Suc_leI \<open>tr = take (Suc n - n) (drop n t)\<close> \<open>trace (S t n) tr (S t (Suc n))\<close> add_diff_cancel_left' append.simps(1) butlast_take cancel_comm_monoid_add_class.diff_cancel length_greater_0_conv list.distinct(1) list.sel(3) snoc_eq_iff_butlast take0 take_Nil trace.cases)
    then show ?thesis
    proof (cases ev)
      case (Snapshot p')
      then show ?thesis 
        by (metis IH Suc.prems(2) Suc.prems(3) local.step(2) new_Marker_in_set_implies_nonregular_occurence new_msg_in_set_implies_occurrence nonregular_event_induces_snapshot snapshot_state_unchanged)
    next
      case (RecvMarker cid' p' q')
      have "p' \<noteq> p"
      proof (rule ccontr)
        assume asm: "~ p' \<noteq> p"
        then have "has_snapshotted (S t (Suc n)) p"
        proof -
          have "~ regular_event ev" using RecvMarker by auto
          moreover have "occurs_on ev = p" using asm RecvMarker by auto
          ultimately show ?thesis using step(2) Suc.hyps Suc.prems 
            by (metis nonregular_event_induces_snapshot snapshot_state_unchanged)
        qed
        then show False using Suc.prems by blast
      qed
      moreover have "cid \<noteq> cid'"
      proof (rule ccontr)
        assume "~ cid \<noteq> cid'"
        then have "hd (msgs (S t n) cid) = Marker \<and> length (msgs (S t n) cid) > 0" 
          using step RecvMarker can_occur_def by auto
        then have "Marker : set (msgs (S t n) cid)" 
          using list.set_sel(1) by fastforce
        then show False using IH by simp
      qed
      ultimately have "msgs (S t (Suc n)) cid = msgs (S t n) cid"
      proof -
        have "\<nexists>r. channel cid = Some (p', r)" 
          using Suc.prems(2) \<open>p' \<noteq> p\<close> by auto
        with \<open>cid \<noteq> cid'\<close> RecvMarker step show ?thesis by (cases "has_snapshotted (S t n) p'", auto) 
      qed
      then show ?thesis by (simp add: IH)
    next
      case (Trans p' s s')
      then show ?thesis 
        using IH local.step(2) by force
    next
      case (Send cid' p' q' s s' m)
      with step IH show ?thesis by (cases "cid' = cid", auto)
    next
      case (Recv cid' p' q' s s' m)
      with step IH show ?thesis by (cases "cid' = cid", auto)
    qed
  qed
  then show ?case by blast
qed

subsection \<open>Termination\<close>

text \<open>We prove that the snapshot algorithm terminates, as exhibited
by lemma \texttt{snapshot\_algorithm\_must\_terminate}. In the final configuration all
processes have snapshotted, and no markers remain in the channels.\<close>

lemma must_exist_snapshot:
  assumes
    "trace init t final"
  shows
    "\<exists>p i. Snapshot p = t ! i"
proof (rule ccontr)
  assume "\<nexists>p i. Snapshot p = t ! i"
  have "\<forall>i p. ~ has_snapshotted (S t i) p"
  proof (rule allI)
    fix i
    show "\<forall>p. ~ has_snapshotted (S t i) p"
    proof (induct i)
      case 0
      then show ?case 
       by (metis assms distributed_system.trace_and_start_determines_end distributed_system_axioms exists_trace_for_any_i computation.no_initial_process_snapshot computation_axioms take0 tr_init)
    next
      case (Suc n)
      then have IH: "\<forall>p. ~ has_snapshotted (S t n) p" by auto
      then obtain tr where "trace (S t n) tr (S t (Suc n))" "tr = take (Suc n - n) (drop n t)"
        using assms exists_trace_for_any_i_j le_Suc_eq by blast
      show "\<forall>p. ~ has_snapshotted (S t (Suc n)) p"
      proof (cases "tr = []")
        case True
        then show ?thesis
          by (metis IH \<open>trace (S t n) tr (S t (Suc n))\<close> tr_init trace_and_start_determines_end)
      next
        case False
        then obtain ev where step: "tr = [ev]" "(S t n) \<turnstile> ev \<mapsto> (S t (Suc n))"
          by (metis One_nat_def Suc_eq_plus1 Suc_leI \<open>tr = take (Suc n - n) (drop n t)\<close> \<open>trace (S t n) tr (S t (Suc n))\<close> add_diff_cancel_left' append.simps(1) butlast_take cancel_comm_monoid_add_class.diff_cancel length_greater_0_conv list.distinct(1) list.sel(3) snoc_eq_iff_butlast take0 take_Nil trace.cases)
        then show ?thesis
        using step Suc.hyps proof (cases ev)
          case (Snapshot q)
          then show ?thesis 
            by (metis \<open>\<nexists>p i. Snapshot p = t ! i\<close> \<open>tr = [ev]\<close> \<open>tr = take (Suc n - n) (drop n t)\<close> append_Cons append_take_drop_id nth_append_length)
        next
          case (RecvMarker cid' q r)
          then have m: "Marker \<in> set (msgs (S t n) cid')" 
            using RecvMarker_implies_Marker_in_set step by blast
          have "~ has_snapshotted (S t n) q" using Suc by auto
          then have "Marker \<notin> set (msgs (S t n) cid')"
          proof -
            have "channel cid' = Some (r, q)" using step can_occur_def RecvMarker by auto
            then show ?thesis 
              using IH assms no_marker_if_no_snapshot by blast
          qed
          then show ?thesis using m by auto
        qed auto
      qed
    qed
  qed
  obtain j p where "has_snapshotted (S t j) p" using l2 assms by blast
  then show False 
    using \<open>\<forall>i p. \<not> has_snapshotted (S t i) p\<close> by blast
qed

lemma recv_marker_means_snapshotted:
  assumes
    "trace init t final" and
    "ev = RecvMarker cid p q" and
    "(S t i) \<turnstile> ev \<mapsto> (S t (Suc i))"
  shows
    "has_snapshotted (S t i) q"
proof -
  have "Marker = hd (msgs (S t i) cid) \<and> length (msgs (S t i) cid) > 0" 
  proof -
    have "Marker # msgs (S t (Suc i)) cid = msgs (S t i) cid"
      using assms(2) assms(3) next_recv_marker by blast
    then show ?thesis 
      by (metis length_greater_0_conv list.discI list.sel(1))
  qed
  then have "Marker \<in> set (msgs (S t i) cid)" 
    using hd_in_set by fastforce
  then show "has_snapshotted (S t i) q"
  proof -
    have "channel cid = Some (q, p)" using assms can_occur_def by auto
    then show ?thesis 
      using \<open>Marker \<in> set (msgs (S t i) cid)\<close> assms(1) no_marker_if_no_snapshot by blast
  qed
qed

lemma recv_marker_means_cs_Done:
  assumes
    "trace init t final" and
    "t ! i = RecvMarker cid p q" and
    "i < length t"
  shows
    "snd (cs (S t (i+1)) cid) = Done"
proof -
  have "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (i+1))" 
    using assms(1) assms(3) step_Suc by auto
  then show ?thesis 
    by (simp add: assms(2))
qed

lemma snapshot_produces_marker:
  assumes
    "trace init t final" and
    "~ has_snapshotted (S t i) p" and
    "has_snapshotted (S t (Suc i)) p" and
    "channel cid = Some (p, q)"
  shows
    "Marker : set (msgs (S t (Suc i)) cid) \<or> has_snapshotted (S t i) q"
proof -
  obtain ev where ex_ev: "(S t i) \<turnstile> ev \<mapsto> (S t (Suc i))"
    by (metis append_Nil2 append_take_drop_id assms(1) assms(2) assms(3) distributed_system.step_Suc distributed_system_axioms drop_eq_Nil less_Suc_eq_le nat_le_linear not_less_eq s_def)
  then have "occurs_on ev = p" 
    using assms(2) assms(3) no_state_change_if_no_event by force
  then show ?thesis
  using assms ex_ev proof (cases ev)
    case (Snapshot r)
    then have "Marker \<in> set (msgs (S t (Suc i)) cid)" 
      using ex_ev assms(2) assms(3) assms(4) by fastforce
    then show ?thesis by simp
  next
    case (RecvMarker cid' r s)
    have "r = p" using \<open>occurs_on ev = p\<close> 
      by (simp add: RecvMarker)
    then show ?thesis
    proof (cases "cid = cid'")
      case True
      then have "has_snapshotted (S t i) q" 
        using RecvMarker RecvMarker_implies_Marker_in_set assms(1) assms(2) assms(4) ex_ev no_marker_if_no_snapshot by blast
      then show ?thesis by simp
    next
      case False
      then have "\<exists>s. channel cid = Some (r, s)" using RecvMarker assms can_occur_def \<open>r = p\<close> by simp
      then have "msgs (S t (Suc i)) cid = msgs (S t i) cid @ [Marker]"
        using RecvMarker assms ex_ev \<open>r = p\<close> False by simp
      then show ?thesis by simp
    qed
  qed auto
qed

lemma exists_snapshot_for_all_p:
  assumes
    "trace init t final"
  shows
    "\<exists>i. ~ has_snapshotted (S t i) p \<and> has_snapshotted (S t (Suc i)) p" (is ?Q)
proof -
  obtain i where "has_snapshotted (S t i) p" using l2 assms by blast
  let ?j = "LEAST j. has_snapshotted (S t j) p"
  have "?j \<noteq> 0"
  proof -
    have "~ has_snapshotted (S t 0) p" 
      by (metis exists_trace_for_any_i list.discI no_initial_process_snapshot s_def take_eq_Nil trace.simps)
    then show ?thesis 
      by (metis (mono_tags, lifting) \<open>has_snapshotted (S t i) p\<close> wellorder_Least_lemma(1))
  qed
  have "?j \<le> i" 
    by (meson Least_le \<open>has_snapshotted (S t i) p\<close>)
  have "\<not> has_snapshotted (S t (?j - 1)) p" (is ?P)
  proof (rule ccontr)
    assume "\<not> ?P"
    then have "has_snapshotted (S t (?j - 1)) p" by simp
    then have "\<exists>j. j < ?j \<and> has_snapshotted (S t j) p" 
      by (metis One_nat_def \<open>(LEAST j. ps (S t j) p \<noteq> None) \<noteq> 0\<close> diff_less lessI not_gr_zero)
    then show False 
      using not_less_Least by blast
  qed
  show ?thesis
  proof (rule ccontr)
    assume "\<not> ?Q"
    have "\<forall>i. \<not> has_snapshotted (S t i) p"
    proof (rule allI)
      fix i'
      show "\<not> has_snapshotted (S t i') p"
      proof (induct i')
        case 0
        then show ?case 
          using \<open>(LEAST j. ps (S t j) p \<noteq> None) \<noteq> 0\<close> by force
      next
        case (Suc i'')
        then show ?case 
          using \<open>\<nexists>i. \<not> ps (S t i) p \<noteq> None \<and> ps (S t (Suc i)) p \<noteq> None\<close> by blast
      qed
    qed
    then show False 
      using \<open>ps (S t i) p \<noteq> None\<close> by blast
  qed
qed

lemma all_processes_snapshotted_in_final_state:
  assumes
    "trace init t final"
  shows
    "has_snapshotted final p"
proof -
  obtain i where "has_snapshotted (S t i) p \<and> i \<le> length t"
    using assms l2 by blast
  moreover have "final = (S t (length t))"
    by (metis (no_types, lifting) assms exists_trace_for_any_i le_Suc_eq length_Cons take_Nil take_all trace.simps trace_and_start_determines_end)
  ultimately show ?thesis 
    using assms exists_trace_for_any_i_j snapshot_stable by blast
qed

definition next_marker_free_state where
  "next_marker_free_state t i cid = (LEAST j. j \<ge> i \<and> Marker \<notin> set (msgs (S t j) cid))"

lemma exists_next_marker_free_state:
  assumes
    "channel cid = Some (p, q)"
    "trace init t final"
  shows
    "\<exists>!j. next_marker_free_state t i cid = j \<and> j \<ge> i \<and> Marker \<notin> set (msgs (S t j) cid)"
proof (cases "Marker \<in> set (msgs (S t i) cid)")
  case False
  then have "next_marker_free_state t i cid = i" unfolding next_marker_free_state_def
    by (metis (no_types, lifting) Least_equality order_refl)
  then show ?thesis using False assms by blast
next
  case True
  then obtain j where "j \<ge> i" "Marker \<notin> set (msgs (S t j) cid)" using l1 assms by blast
  then show ?thesis
    by (metis (no_types, lifting) LeastI_ex next_marker_free_state_def)
qed

theorem snapshot_algorithm_must_terminate:
  assumes
    "trace init t final"
  shows
    "\<exists>phi. ((\<forall>p. has_snapshotted (S t phi) p)
          \<and> (\<forall>cid. Marker \<notin> set (msgs (S t phi) cid)))"
proof -
  let ?i = "{i. i \<le> length t \<and> (\<forall>p. has_snapshotted (S t i) p)}"
  have fin_i: "finite ?i" by auto
  moreover have "?i \<noteq> empty"
  proof -
    have "\<forall>p. has_snapshotted (S t (length t)) p" 
      by (meson assms exists_trace_for_any_i_j l2 snapshot_stable_2)
    then show ?thesis by blast
  qed
  then obtain i where asm: "\<forall>p. has_snapshotted (S t i) p" by blast
  have f: "\<forall>j. j \<ge> i \<longrightarrow> (\<forall>p. has_snapshotted (S t j) p)"
    using snapshot_stable asm exists_trace_for_any_i_j valid assms by blast
  let ?s = "(\<lambda>cid. (next_marker_free_state t i cid)) ` { cid. channel cid \<noteq> None }"
  have "?s \<noteq> empty" using exists_some_channel by auto
  have fin_s: "finite ?s" using finite_channels by simp
  let ?phi = "Max ?s"
  have "?phi \<ge> i"
  proof (rule ccontr)
    assume asm: "\<not> ?phi \<ge> i"
    obtain cid p q where g: "channel cid = Some (p, q)" using exists_some_channel by auto
    then have "next_marker_free_state t i cid \<ge> i" using exists_next_marker_free_state assms by blast
    then have "Max ?s \<ge> i" using Max_ge_iff g fin_s by fast
    then show False using asm by simp
  qed
  then have "\<And>cid. Marker \<notin> set (msgs (S t ?phi) cid)"
  proof -
    fix cid
    show "Marker \<notin> set (msgs (S t ?phi) cid)"
    proof (cases "Marker : set (msgs (S t i) cid)")
      case False
      then show ?thesis
        using \<open>i \<le> Max ?s\<close> asm assms exists_trace_for_any_i_j no_markers_if_all_snapshotted by blast
    next
      case True
      then have cpq: "channel cid \<noteq> None" using no_messages_if_no_channel assms by fastforce
      then obtain p q where chan: "channel cid = Some (p, q)" by auto
      then obtain j where i: "j = next_marker_free_state t i cid" "Marker \<notin> set (msgs (S t j) cid)"
        using exists_next_marker_free_state assms by fast
      have "j \<le> ?phi" using cpq fin_s i(1) pair_imageI by simp
      then show "Marker \<notin> set (msgs (S t ?phi) cid)"
      proof -
        have "trace (S t j) (take (?phi - j) (drop j t)) (S t ?phi)" 
          using \<open>j \<le> ?phi\<close> assms exists_trace_for_any_i_j by blast
        moreover have "\<forall>p. has_snapshotted (S t j) p" 
          by (metis assms chan f computation.exists_next_marker_free_state computation_axioms i(1))
        ultimately show ?thesis 
          using i(2) no_markers_if_all_snapshotted by blast
      qed
    qed
  qed
  thus ?thesis using f \<open>?phi \<ge> i\<close> by blast
qed

subsection \<open>Correctness\<close>

text \<open>The greatest part of this work is spent on the correctness
of the Chandy-Lamport algorithm. We prove that the snapshot is
consistent, i.e.\ there exists a permutation $t'$ of the trace $t$ and an intermediate
configuration $c'$ of $t'$ such that the configuration recorded in the snapshot
corresponds to the snapshot taken during execution of $t$, which is given as Theorem 1
in~\cite{chandy}.\<close>

lemma snapshot_stable_ver_2:
  shows "trace init t final \<Longrightarrow> has_snapshotted (S t i) p \<Longrightarrow> j \<ge> i \<Longrightarrow> has_snapshotted (S t j) p"
  using exists_trace_for_any_i_j snapshot_stable by blast

lemma snapshot_stable_ver_3:
  shows "trace init t final \<Longrightarrow> ~ has_snapshotted (S t i) p \<Longrightarrow> i \<ge> j \<Longrightarrow> ~ has_snapshotted (S t j) p"
  using snapshot_stable_ver_2 by blast

lemma marker_must_stay_if_no_snapshot:
  assumes
    "trace init t final" and
    "has_snapshotted (S t i) p" and
    "~ has_snapshotted (S t i) q" and
    "channel cid = Some (p, q)"
  shows
    "Marker : set (msgs (S t i) cid)"
proof -
  obtain j where "~ has_snapshotted (S t j) p \<and> has_snapshotted (S t (Suc j)) p"
    using exists_snapshot_for_all_p assms by blast
  have "j \<le> i"
  proof (rule ccontr)
    assume asm: "~ j \<le> i"
    then have "~ has_snapshotted (S t i) p" 
      using \<open>\<not> has_snapshotted (S t j) p \<and> has_snapshotted (S t (Suc j)) p\<close> assms(1) less_imp_le_nat snapshot_stable_ver_3 
      by (meson nat_le_linear)
    then show False using assms(2) by simp
  qed
  have "i \<le> length t"
  proof (rule ccontr)
    assume "~ i \<le> length t"
    then have "i > length t" 
      using not_less by blast
    obtain i' where a: "\<forall>p. has_snapshotted (S t i') p" using assms snapshot_algorithm_must_terminate by blast
    have "i' \<ge> i" 
      using \<open>\<forall>p. has_snapshotted (S t i') p\<close> assms(1) assms(3) nat_le_linear snapshot_stable_ver_3 by blast
    have "(S t i') \<noteq> (S t i)" using assms a by force
    then have "i \<le> length t" 
      using \<open>i \<le> i'\<close> assms(1) computation.no_change_if_ge_length_t computation_axioms nat_le_linear by fastforce
    then show False using \<open>~ i \<le> length t\<close> by simp
  qed
  have marker_in_set: "Marker : set (msgs (S t (Suc j)) cid)" 
    using \<open>\<not> has_snapshotted (S t j) p \<and> has_snapshotted (S t (Suc j)) p\<close> \<open>j \<le> i\<close> assms(1) assms(3) assms(4) snapshot_produces_marker snapshot_stable_ver_3 by blast
  show ?thesis
  proof (rule ccontr)
    assume asm: "Marker \<notin> set (msgs (S t i) cid)"
    then have range: "(Suc j) < i" 
      by (metis Suc_lessI \<open>\<not> ps (S t j) p \<noteq> None \<and> ps (S t (Suc j)) p \<noteq> None\<close> \<open>j \<le> i\<close> assms(2) marker_in_set order.order_iff_strict)
    let ?k = "LEAST k. k \<ge> (Suc j) \<and> Marker \<notin> set (msgs (S t k) cid)"
    have range_k: "(Suc j) < ?k \<and> ?k \<le> i"
    proof -
      have "j < (LEAST n. Suc j \<le> n \<and> Marker \<notin> set (msgs (S t n) cid))"
        by (metis (full_types) Suc_le_eq assms(1) assms(4) exists_next_marker_free_state next_marker_free_state_def)
      then show ?thesis
      proof -
        assume a1: "j < (LEAST n. Suc j \<le> n \<and> Marker \<notin> set (msgs (S t n) cid))"
        have "j < i"
          using local.range by linarith (* 4 ms *)
        then have "(Suc j \<le> i \<and> Marker \<notin> set (msgs (S t i) cid)) \<and> (LEAST n. Suc j \<le> n \<and> Marker \<notin> set (msgs (S t n) cid)) \<noteq> Suc j"
          by (metis (lifting) Suc_leI asm marker_in_set wellorder_Least_lemma(1)) (* 64 ms *)
        then show ?thesis
          using a1 by (simp add: wellorder_Least_lemma(2)) (* 16 ms *)
      qed
    qed
    have a: "Marker : set (msgs (S t (?k-1)) cid)" 
    proof -
      obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
        "\<forall>x0 x1. (\<exists>v2. x0 = Suc (x1 + v2)) = (x0 = Suc (x1 + nn x0 x1))"
        by moura
      then have f1: "(LEAST n. Suc j \<le> n \<and> Marker \<notin> set (msgs (S t n) cid)) = Suc (Suc j + nn (LEAST n. Suc j \<le> n \<and> Marker \<notin> set (msgs (S t n) cid)) (Suc j))"
        using \<open>Suc j < (LEAST k. Suc j \<le> k \<and> Marker \<notin> set (msgs (S t k) cid)) \<and> (LEAST k. Suc j \<le> k \<and> Marker \<notin> set (msgs (S t k) cid)) \<le> i\<close> less_iff_Suc_add by fastforce
      have f2: "Suc j \<le> Suc j + nn (LEAST n. Suc j \<le> n \<and> Marker \<notin> set (msgs (S t n) cid)) (Suc j)"
        by simp
      have f3: "\<forall>p n. \<not> p (n::nat) \<or> Least p \<le> n"
        by (meson wellorder_Least_lemma(2))
      have "\<not> (LEAST n. Suc j \<le> n \<and> Marker \<notin> set (msgs (S t n) cid)) \<le> Suc j + nn (LEAST n. Suc j \<le> n \<and> Marker \<notin> set (msgs (S t n) cid)) (Suc j)"
        using f1 by linarith
      then have f4: "\<not> (Suc j \<le> Suc j + nn (LEAST n. Suc j \<le> n \<and> Marker \<notin> set (msgs (S t n) cid)) (Suc j) \<and> Marker \<notin> set (msgs (S t (Suc j + nn (LEAST n. Suc j \<le> n \<and> Marker \<notin> set (msgs (S t n) cid)) (Suc j))) cid))"
        using f3 by force
      have "Suc j + nn (LEAST n. Suc j \<le> n \<and> Marker \<notin> set (msgs (S t n) cid)) (Suc j) = (LEAST n. Suc j \<le> n \<and> Marker \<notin> set (msgs (S t n) cid)) - 1"
        using f1 by linarith
      then show ?thesis
        using f4 f2 by presburger
    qed
    have b: "Marker \<notin> set (msgs (S t ?k) cid)" 
      using assms(1) assms(4) exists_next_marker_free_state next_marker_free_state_def by fastforce
    have "?k - 1 < i" using range_k by auto
    then obtain ev where step: "(S t (?k-1)) \<turnstile> ev \<mapsto> (S t (Suc (?k-1)))" 
      by (meson Suc_le_eq \<open>i \<le> length t\<close> assms(1) le_trans step_Suc)
    then show False
      using a assms(1) assms(3) assms(4) b computation.snapshot_stable_ver_3 computation_axioms less_iff_Suc_add range_k recv_marker_means_snapshotted_2 by fastforce
  qed
qed

subsubsection \<open>Pre- and postrecording events\<close>

definition prerecording_event:
  "prerecording_event t i \<equiv>
      i < length t \<and> regular_event (t ! i)
    \<and> ~ has_snapshotted (S t i) (occurs_on (t ! i))"

definition postrecording_event:
  "postrecording_event t i \<equiv>
      i < length t \<and> regular_event (t ! i)
    \<and> has_snapshotted (S t i) (occurs_on (t ! i))"

abbreviation neighboring where
  "neighboring t i j \<equiv> i < j \<and> j < length t \<and> regular_event (t ! i) \<and> regular_event (t ! j)
                     \<and> (\<forall>k. i < k \<and> k < j \<longrightarrow> ~ regular_event (t ! k))"

lemma pre_if_regular_and_not_post:
  assumes
    "regular_event (t ! i)" and
    "~ postrecording_event t i" and
    "i < length t"
  shows
    "prerecording_event t i"
  using assms computation.postrecording_event computation_axioms prerecording_event by metis

lemma post_if_regular_and_not_pre:
  assumes
    "regular_event (t ! i)" and
    "~ prerecording_event t i" and
    "i < length t"
  shows
    "postrecording_event t i"
  using assms computation.postrecording_event computation_axioms prerecording_event by metis

lemma post_before_pre_different_processes:
  assumes
    "i < j" and
    "j < length t" and
    neighboring: "\<forall>k. (i < k \<and> k < j) \<longrightarrow> ~ regular_event (t ! k)" and
    post_ei: "postrecording_event t i" and
    pre_ej: "prerecording_event t j" and
    valid: "trace init t final"
  shows
    "occurs_on (t ! i) \<noteq> occurs_on (t ! j)"
proof -
  let ?p = "occurs_on (t ! i)"
  let ?q = "occurs_on (t ! j)"
  have sp: "has_snapshotted (S t i) ?p"
    using assms postrecording_event prerecording_event by blast
  have nsq: "~ has_snapshotted (S t j) ?q"
    using assms postrecording_event prerecording_event by blast
  show "?p \<noteq> ?q"
  proof -
    have "~ has_snapshotted (S t i) ?q"
    proof (rule ccontr)
      assume sq: "~ ~ has_snapshotted (S t i) ?q"
      from \<open>i < j\<close> have "i \<le> j" using less_imp_le by blast
      then obtain tr where ex_trace: "trace (S t i) tr (S t j)"
        using exists_trace_for_any_i_j valid by blast
      then have "has_snapshotted (S t j) ?q" using ex_trace snapshot_stable sq by blast
      then show False using nsq by simp
    qed
    then show ?thesis using sp by auto
  qed
qed

lemma post_before_pre_neighbors:
  assumes
    "i < j" and
    "j < length t" and
    neighboring: "\<forall>k. (i < k \<and> k < j) \<longrightarrow> ~ regular_event (t ! k)" and
    post_ei: "postrecording_event t i" and
    pre_ej: "prerecording_event t j" and
    valid: "trace init t final"
  shows
    "Ball (set (take (j - (i+1)) (drop (i+1) t))) (%ev. ~ regular_event ev \<and> ~ occurs_on ev = occurs_on (t ! j))"
proof -
  let ?p = "occurs_on (t ! i)"
  let ?q = "occurs_on (t ! j)"
  let ?between = "take (j - (i+1)) (drop (i+1) t)"
  show ?thesis
  proof (unfold Ball_def, rule allI, rule impI)
    fix ev
    assume "ev : set ?between"
    have len_nr: "length ?between = (j - (i+1))" using assms(2) by auto
    then obtain l where "?between ! l = ev" and range_l: "0 \<le> l \<and> l < (j - (i+1))" 
      by (metis \<open>ev \<in> set (take (j - (i + 1)) (drop (i + 1) t))\<close> gr_zeroI in_set_conv_nth le_numeral_extra(3) less_le)
    let ?k = "l + (i+1)"
    have "?between ! l = (t ! ?k)"
    proof -
      have "j < length t"
        by (metis assms(2))
      then show ?thesis
        by (metis (no_types) Suc_eq_plus1 Suc_leI add.commute assms(1) drop_take length_take less_diff_conv less_imp_le_nat min.absorb2 nth_drop nth_take range_l)
    qed
    have "~ regular_event ev" 
      by (metis (no_types, lifting) assms(3) range_l One_nat_def Suc_eq_plus1 \<open>take (j - (i + 1)) (drop (i + 1) t) ! l = ev\<close> \<open>take (j - (i + 1)) (drop (i + 1) t) ! l = t ! (l + (i + 1))\<close> add.left_commute add_lessD1 lessI less_add_same_cancel2 less_diff_conv order_le_less)
    have step_ev: "(S t ?k) \<turnstile> ev \<mapsto> (S t (?k+1))" 
    proof -
      have "j \<le> length t"
        by (metis assms(2) less_or_eq_imp_le)
      then have "l + (i + 1) < length t"
        by (meson less_diff_conv less_le_trans range_l)
      then show ?thesis
        by (metis (no_types) Suc_eq_plus1 \<open>take (j - (i + 1)) (drop (i + 1) t) ! l = ev\<close> \<open>take (j - (i + 1)) (drop (i + 1) t) ! l = t ! (l + (i + 1))\<close> distributed_system.step_Suc distributed_system_axioms valid)
    qed
    obtain cid s r where f: "ev = RecvMarker cid s r \<or> ev = Snapshot r" using \<open>~ regular_event ev\<close>
      by (meson isRecvMarker_def isSnapshot_def nonregular_event)
    from f have "occurs_on ev \<noteq> ?q"
    proof (elim disjE)
      assume snapshot: "ev = Snapshot r"
      show ?thesis
      proof (rule ccontr)
        assume occurs_on_q: "~ occurs_on ev \<noteq> ?q"
        then have "?q = r" using snapshot by auto
        then have q_snapshotted: "has_snapshotted (S t (?k+1)) ?q"
          using snapshot step_ev by auto
        then show False 
        proof -
          have "l + (i + 1) < j"
            by (meson less_diff_conv range_l)
          then show ?thesis
            by (metis (no_types) Suc_eq_plus1 Suc_le_eq computation.snapshot_stable_ver_2 computation_axioms pre_ej prerecording_event q_snapshotted valid)
        qed
      qed
    next
      assume RecvMarker: "ev = RecvMarker cid s r"
      show ?thesis
      proof (rule ccontr)
        assume occurs_on_q: "~ occurs_on ev \<noteq> ?q"
        then have "s = ?q" using RecvMarker by auto
        then have q_snapshotted: "has_snapshotted (S t (?k+1)) ?q"
        proof (cases "has_snapshotted (S t ?k) ?q")
          case True
          then show ?thesis using snapshot_stable_ver_2 step_Suc step_ev valid by auto
        next
          case False
          then show "has_snapshotted (S t (?k+1)) ?q"
            using \<open>s = ?q\<close> next_recv_marker RecvMarker step_ev by auto
        qed
        then show False 
        proof -
          have "l + (i + 1) < j"
            using less_diff_conv range_l by blast
          then show ?thesis
            by (metis (no_types) Suc_eq_plus1 Suc_le_eq computation.snapshot_stable_ver_2 computation_axioms pre_ej prerecording_event q_snapshotted valid)
        qed
      qed
    qed
    then show "\<not> regular_event ev \<and> occurs_on ev \<noteq> ?q"
      using \<open>~ regular_event ev\<close> by simp
  qed
qed

lemma can_swap_neighboring_pre_and_postrecording_events:
  assumes
    "i < j" and
    "j < length t" and
    "occurs_on (t ! i) = p" and
    "occurs_on (t ! j) = q" and
    neighboring: "\<forall>k. (i < k \<and> k < j)
                   \<longrightarrow> ~ regular_event (t ! k)" and
    post_ei: "postrecording_event t i" and
    pre_ej: "prerecording_event t j" and
    valid: "trace init t final"
  shows
    "can_occur (t ! j) (S t i)"
proof -
  have "p \<noteq> q" using post_before_pre_different_processes assms by auto
  have sp: "has_snapshotted (S t i) p" 
    using assms(3) post_ei postrecording_event prerecording_event by blast
  have nsq: "~ has_snapshotted (S t j) q" 
    using assms(4) pre_ej prerecording_event by auto
  let ?nr = "take (j - (Suc i)) (drop (Suc i) t)"
  have valid_subtrace: "trace (S t (Suc i)) ?nr (S t j)"
    using assms(1) exists_trace_for_any_i_j valid by fastforce
  have "Ball (set ?nr) (%ev. ~ occurs_on ev = q \<and> ~ regular_event ev)"
  proof -
    have "?nr = take (j - (i+1)) (drop (i+1) t)" by auto
    then show ?thesis
      by (metis assms(1) assms(2) assms(4) neighboring post_ei pre_ej valid post_before_pre_neighbors)
  qed
  then have la: "list_all (%ev. ~ occurs_on ev = q) ?nr"
      by (meson list_all_length nth_mem)
  have tj_to_tSi: "can_occur (t ! j) (S t (Suc i))"
  proof - 
    have "list_all (%ev. ~ isSend ev) ?nr"
    proof -
      have "list_all (%ev. ~ regular_event ev) ?nr" 
        using \<open>\<forall>ev\<in>set (take (j - (Suc i)) (drop (Suc i) t)). occurs_on ev \<noteq> q \<and> \<not> regular_event ev\<close> \<open>list_all (\<lambda>ev. occurs_on ev \<noteq> q) (take (j - (Suc i)) (drop (Suc i) t))\<close> list.pred_mono_strong by fastforce
      then show ?thesis
        by (simp add: list.pred_mono_strong)
    qed
    moreover have "~ isRecvMarker (t ! j)" using prerecording_event assms by auto
    moreover have "can_occur (t ! j) (S t j)" 
    proof -
      have "(S t j) \<turnstile> (t ! j) \<mapsto> (S t (Suc j))" 
        using assms(2) step_Suc valid by auto
      then show ?thesis 
        using happen_implies_can_occur by blast
    qed
    ultimately show "can_occur (t ! j) (S t (Suc i))" 
      using assms(4) event_can_go_back_if_no_sender_trace valid_subtrace la by blast
  qed
  show "can_occur (t ! j) (S t i)"
  proof (cases "isSend (t ! i)")
    case False
    have "~ isRecvMarker (t ! j)" using assms prerecording_event by auto
    moreover have "~ isSend (t ! i)" using False by simp
    ultimately show ?thesis 
      by (metis \<open>p \<noteq> q\<close> assms(3) assms(4) event_can_go_back_if_no_sender post_ei postrecording_event step_Suc tj_to_tSi valid)
  next
    case True
    obtain cid s u u' m where Send: "t ! i = Send cid p s u u' m" 
      by (metis True isSend_def assms(3) event.sel(2))
    have chan: "channel cid = Some (p, s)"
    proof -
      have "can_occur (t ! i) (S t i)" 
        by (meson computation.postrecording_event computation_axioms happen_implies_can_occur post_ei step_Suc valid)
      then show ?thesis using can_occur_def Send by simp
    qed
    have n: "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (Suc i))" 
      using assms(1) assms(2) step_Suc valid True by auto
    have st: "states (S t i) q = states (S t (Suc i)) q" 
      using Send \<open>p \<noteq> q\<close> n by auto
    have "isTrans (t ! j) \<or> isSend (t ! j) \<or> isRecv (t ! j)"
      using assms(7) computation.prerecording_event computation_axioms regular_event by blast
    then show ?thesis 
    proof (elim disjE)
      assume "isTrans (t ! j)"
      then show ?thesis
        by (metis (no_types, lifting) tj_to_tSi st can_occur_def assms(4) event.case(1) event.collapse(1))
    next
      assume "isSend (t ! j)"
      then obtain cid' s' u'' u''' m' where Send: "t ! j = Send cid' q s' u'' u''' m'" 
        by (metis (no_types, lifting) assms(4) event.sel(2) isSend_def)
      have co_tSi: "can_occur (Send cid' q s' u'' u''' m') (S t (Suc i))" 
        using Send tj_to_tSi by auto
      then have "channel cid' = Some (q, s') \<and> send cid' q s' u'' u''' m'"
        using Send can_occur_def by simp
      then show ?thesis using can_occur_def st Send assms co_tSi by auto
    next
      assume "isRecv (t ! j)"
      then obtain cid' s' u'' u''' m' where Recv: "t ! j = Recv cid' q s' u'' u''' m'"
        by (metis assms(4) event.sel(3) isRecv_def)
      have co_tSi: "can_occur (Recv cid' q s' u'' u''' m') (S t (Suc i))" 
        using Recv tj_to_tSi by auto
      then have a: "channel cid' = Some (s', q) \<and> length (msgs (S t (Suc i)) cid') > 0
                  \<and> hd (msgs (S t (Suc i)) cid') = Msg m'"
        using can_occur_def co_tSi by fastforce
      show "can_occur (t ! j) (S t i)"
      proof (cases "cid = cid'")
        case False
        with Send n have "msgs (S t (Suc i)) cid' = msgs (S t i) cid'" by auto
        then have b: "length (msgs (S t i) cid') > 0 \<and> hd (msgs (S t i) cid') = Msg m'"
          using a by simp
        with can_occur_Recv co_tSi st a Recv show ?thesis
          unfolding can_occur_def by auto
      next
        case True (* This is the interesting case *)
        have stu: "states (S t i) q = u''" 
          using can_occur_Recv co_tSi st by blast
        show ?thesis
        proof (rule ccontr)
          have marker_in_set: "Marker \<in> set (msgs (S t i) cid)"
          proof -
            have "(s', q) = (p, q)" 
              using True a chan by auto
            then show ?thesis
              by (metis (no_types, lifting) True \<open>p \<noteq> q\<close> a assms(3) marker_must_stay_if_no_snapshot n no_state_change_if_no_event nsq snapshot_stable_2 sp valid valid_subtrace)
          qed
          assume asm: "~ can_occur (t ! j) (S t i)"
          then show False
          proof (unfold can_occur_def, (auto simp add: marker_in_set True Recv stu))
            assume "msgs (S t i) cid' = []"
            then show False using marker_in_set 
              by (simp add: True)
          next
            assume "hd (msgs (S t i) cid') \<noteq> Msg m'"
            have "msgs (S t i) cid \<noteq> []" using marker_in_set by auto
            then have "msgs (S t (Suc i)) cid = msgs (S t i) cid @ [Msg m]"
              using Send True n chan by auto
            then have "hd (msgs (S t (Suc i)) cid) \<noteq> Msg m'" 
              using True \<open>hd (msgs (S t i) cid') \<noteq> Msg m'\<close> \<open>msgs (S t i) cid \<noteq> []\<close> by auto
            then have "~ can_occur (t ! j) (S t (Suc i))" 
              using True a by blast
            then show False 
              using tj_to_tSi by blast
          next
            assume "~ recv cid' q s' u'' u''' m'"
            then show False 
              using can_occur_Recv co_tSi by blast
          next
            assume "channel cid' \<noteq> Some (s', q)"
            then show False using can_occur_def tj_to_tSi Recv by simp
          qed
        qed
      qed
    qed
  qed
qed

subsubsection \<open>Event swapping\<close>

lemma swap_events:
  shows "\<lbrakk> i < j; j < length t;
          \<forall>k. (i < k \<and> k < j) \<longrightarrow> ~ regular_event (t ! k);
          postrecording_event t i; prerecording_event t j;
          trace init t final \<rbrakk>
        \<Longrightarrow> trace init (swap_events i j t) final
          \<and> (\<forall>k. k \<ge> j + 1 \<longrightarrow> S (swap_events i j t) k = S t k)
          \<and> (\<forall>k. k \<le> i \<longrightarrow> S (swap_events i j t) k = S t k)
          \<and> prerecording_event (swap_events i j t) i
          \<and> postrecording_event (swap_events i j t) (i+1)
          \<and> (\<forall>k. k > i+1 \<and> k < j+1
               \<longrightarrow> ~ regular_event ((swap_events i j t) ! k))"
proof (induct "j - (i+1)" arbitrary: j t)
  case 0
  let ?p = "occurs_on (t ! i)"
  let ?q = "occurs_on (t ! j)"
  have "j = (i+1)"
    using "0.prems" "0.hyps" by linarith
  let ?subt = "take (j - (i+1)) (drop (i+1) t)"
  have "t = take i t @ [t ! i] @ ?subt @ [t ! j] @ drop (j+1) t" 
  proof -
    have "take (Suc i) t = take i t @ [t ! i]"
      using "0.prems"(2) \<open>j = i + 1\<close> add_lessD1 take_Suc_conv_app_nth by blast
    then show ?thesis
      by (metis (no_types) "0.hyps" "0.prems"(2) Suc_eq_plus1 \<open>j = i + 1\<close> append_assoc append_take_drop_id self_append_conv2 take_Suc_conv_app_nth take_eq_Nil)
  qed
  have sp: "has_snapshotted (S t i) ?p"
    using "0.prems" postrecording_event prerecording_event by blast
  have nsq: "~ has_snapshotted (S t j) ?q"
    using "0.prems" postrecording_event prerecording_event by blast
  have "?p \<noteq> ?q"
    using "0.prems" computation.post_before_pre_different_processes computation_axioms by blast
  have "?subt = Nil"
    by (simp add: \<open>j = i + 1\<close>)
  have reg_step_1: "(S t i) \<turnstile> (t ! i) \<mapsto> (S t j)" 
    by (metis "0.prems"(2) "0.prems"(6) Suc_eq_plus1 \<open>j = i + 1\<close> add_lessD1 step_Suc)
  have reg_step_2: "(S t j) \<turnstile> (t ! j) \<mapsto> (S t (j+1))" 
    using "0.prems"(2) "0.prems"(6) step_Suc by auto
  have "can_occur (t ! j) (S t i)" 
    using "0.prems" can_swap_neighboring_pre_and_postrecording_events by blast
  then obtain d' where new_step1: "(S t i) \<turnstile> (t ! j) \<mapsto> d'"
    using exists_next_if_can_occur by blast

  have st: "states d' ?p = states (S t i) ?p" 
    using \<open>(S t i) \<turnstile> t ! j \<mapsto> d'\<close> \<open>occurs_on (t ! i) \<noteq> occurs_on (t ! j)\<close> no_state_change_if_no_event by auto
  then have "can_occur (t ! i) d'" 
    using \<open>occurs_on (t ! i) \<noteq> occurs_on (t ! j)\<close> event_stays_valid_if_no_occurrence happen_implies_can_occur new_step1 reg_step_1 by auto
  then obtain e where new_step2: "d' \<turnstile> (t ! i) \<mapsto> e" 
    using exists_next_if_can_occur by blast

  have "states e = states (S t (j+1))"
  proof (rule ext)
    fix p
    show "states e p = states (S t (j+1)) p"
    proof (cases "p = ?p \<or> p = ?q")
      case True
      then show ?thesis
      proof (elim disjE)
        assume "p = ?p"
        then have "states d' p = states (S t i) p" 
          by (simp add: st)
        thm same_state_implies_same_result_state
        then have "states e p = states (S t j) p"
          using "0.prems"(2) "0.prems"(6) new_step2 reg_step_1 by (blast intro:same_state_implies_same_result_state[symmetric])
        moreover have "states (S t j) p = states (S t (j+1)) p" 
          using \<open>occurs_on (t ! i) \<noteq> occurs_on (t ! j)\<close> \<open>p = occurs_on (t ! i)\<close> no_state_change_if_no_event reg_step_2 by auto
        ultimately show ?thesis by simp
      next
        assume "p = ?q"
        then have "states (S t j) p = states (S t i) p" 
          using reg_step_1 \<open>occurs_on (t ! i) \<noteq> occurs_on (t ! j)\<close> no_state_change_if_no_event by auto
        then have "states d' p = states (S t (j+1)) p" 
          using "0.prems"(5) prerecording_event computation_axioms new_step1 reg_step_2 same_state_implies_same_result_state by blast
        moreover have "states e p = states (S t (j+1)) p" 
          using \<open>occurs_on (t ! i) \<noteq> occurs_on (t ! j)\<close> \<open>p = occurs_on (t ! j)\<close> calculation new_step2 no_state_change_if_no_event by auto
        ultimately show ?thesis by simp
      qed
    next
      case False
      then have "states (S t i) p = states (S t j) p" 
        using no_state_change_if_no_event reg_step_1 by auto
      moreover have "... = states (S t (j+1)) p" 
        using False no_state_change_if_no_event reg_step_2 by auto
      moreover have "... = states d' p" 
        using False calculation new_step1 no_state_change_if_no_event by auto
      moreover have "... = states e p" 
        using False new_step2 no_state_change_if_no_event by auto
      ultimately show ?thesis by simp 
    qed
  qed

  moreover have "msgs e = msgs (S t (j+1))"
  proof (rule ext)
    fix cid
    have "isTrans (t ! i) \<or> isSend (t ! i) \<or> isRecv (t ! i)"
      using "0.prems"(4) computation.postrecording_event computation_axioms regular_event by blast
    moreover have "isTrans (t ! j) \<or> isSend (t ! j) \<or> isRecv (t ! j)" 
      using "0.prems"(5) computation.prerecording_event computation_axioms regular_event by blast
    ultimately show "msgs e cid = msgs (S t (j+1)) cid"
    proof (elim disjE, goal_cases)
      case 1
      then have "msgs d' cid = msgs (S t j) cid" 
        by (metis Trans_msg new_step1 reg_step_1)
      then show ?thesis 
        using Trans_msg \<open>isTrans (t ! i)\<close> \<open>isTrans (t ! j)\<close> new_step2 reg_step_2 by auto
    next
      case 2
      then show ?thesis 
        using \<open>occurs_on (t ! i) \<noteq> occurs_on (t ! j)\<close> new_step1 new_step2 reg_step_1 reg_step_2 swap_msgs_Trans_Send by auto
    next
      case 3
      then show ?thesis 
        using \<open>occurs_on (t ! i) \<noteq> occurs_on (t ! j)\<close> new_step1 new_step2 reg_step_1 reg_step_2 swap_msgs_Trans_Recv by auto
    next
      case 4
      then show ?thesis
        using \<open>occurs_on (t ! i) \<noteq> occurs_on (t ! j)\<close> new_step1 new_step2 reg_step_1 reg_step_2 swap_msgs_Send_Trans by auto
    next
      case 5
      then show ?thesis 
        using \<open>occurs_on (t ! i) \<noteq> occurs_on (t ! j)\<close> new_step1 new_step2 reg_step_1 reg_step_2 swap_msgs_Recv_Trans by auto
    next
      case 6
      then show ?thesis
        using \<open>occurs_on (t ! i) \<noteq> occurs_on (t ! j)\<close> new_step1 new_step2 reg_step_1 reg_step_2 by (blast intro:swap_msgs_Send_Send[symmetric])
    next
      case 7
      then show ?thesis 
        using \<open>occurs_on (t ! i) \<noteq> occurs_on (t ! j)\<close> new_step1 new_step2 reg_step_1 reg_step_2 swap_msgs_Send_Recv by auto
    next
      case 8
      then show ?thesis 
        using \<open>occurs_on (t ! i) \<noteq> occurs_on (t ! j)\<close> new_step1 new_step2 reg_step_1 reg_step_2 swap_msgs_Send_Recv by simp
    next
      case 9
      then show ?thesis
        using \<open>occurs_on (t ! i) \<noteq> occurs_on (t ! j)\<close> new_step1 new_step2 reg_step_1 reg_step_2 by (blast intro:swap_msgs_Recv_Recv[symmetric])
    qed
  qed

  moreover have "process_snapshot e = process_snapshot (S t (j+1))"
  proof (rule ext)
    fix p
    have "process_snapshot d' p = process_snapshot (S t j) p" 
      by (metis "0.prems"(4) "0.prems"(5) computation.postrecording_event computation.prerecording_event computation_axioms new_step1 reg_step_1 regular_event_preserves_process_snapshots)
    then show "process_snapshot e p = process_snapshot (S t (j+1)) p"
      by (metis "0.prems"(4) "0.prems"(5) computation.postrecording_event computation.prerecording_event computation_axioms new_step2 reg_step_2 regular_event_preserves_process_snapshots)
  qed

  moreover have "channel_snapshot e = channel_snapshot (S t (j+1))"
  proof (rule ext)
    fix cid
    show "cs e cid = cs (S t (j+1)) cid"
    proof (cases "isRecv (t ! i)"; cases "isRecv (t ! j)", goal_cases)
      case 1
      then show ?thesis
        using \<open>?p \<noteq> ?q\<close> new_step1 new_step2 reg_step_1 reg_step_2
        by (blast intro:regular_event_implies_same_channel_snapshot_Recv_Recv[symmetric])
    next
      case 2
      moreover have "regular_event (t ! j)" using prerecording_event 0 by simp
      ultimately show ?thesis 
        using \<open>?p \<noteq> ?q\<close> new_step1 new_step2 reg_step_1 reg_step_2 regular_event_implies_same_channel_snapshot_Recv by auto
    next
      assume 3: "~ isRecv (t ! i)" "isRecv (t ! j)"
      moreover have "regular_event (t ! i)" using postrecording_event 0 by simp
      ultimately show ?thesis 
        using \<open>?p \<noteq> ?q\<close> new_step1 new_step2 reg_step_1 reg_step_2 regular_event_implies_same_channel_snapshot_Recv by auto

    next
      assume 4: "~ isRecv (t ! i)" "~ isRecv (t ! j)"
      moreover have "regular_event (t ! j)" using prerecording_event 0 by simp
      moreover have "regular_event (t ! i)" using postrecording_event 0 by simp
      ultimately show ?thesis 
        using \<open>?p \<noteq> ?q\<close> new_step1 new_step2 reg_step_1 reg_step_2 
        by (metis no_cs_change_if_no_event)
    qed
  qed
  ultimately have "e = S t (j+1)" by simp
  then have "(S t i) \<turnstile> (t ! j) \<mapsto> d' \<and> d' \<turnstile> (t ! i) \<mapsto> (S t (j+1))"
    using new_step1 new_step2 by blast
  then have swap: "trace (S t i) [t ! j, t ! i] (S t (j+1))" 
    by (meson trace.simps)
  have "take (j-1) t @ [t ! j, t ! i] = ((take (j+1) t)[i := t ! j])[j := t ! i]"
  proof -
    have "i = j - 1" 
      by (simp add: \<open>j = i + 1\<close>)
    show ?thesis
    proof (subst (1 2 3) \<open>i = j - 1\<close>)
      have "j < length t" using "0.prems" by auto
      then have "take (j - 1) t @ [t ! j, t ! (j - 1)] @ drop (j + 1) t = t[j - 1 := t ! j, j := t ! (j - 1)]"
        by (metis Suc_eq_plus1 \<open>i = j - 1\<close> \<open>j = i + 1\<close> add_Suc_right arith_special(3) swap_neighbors)
      then show "take (j - 1) t @ [t ! j, t ! (j - 1)] = (take (j+1) t)[j - 1 := t ! j, j := t ! (j - 1)]"
      proof -
        assume a1: "take (j - 1) t @ [t ! j, t ! (j - 1)] @ drop (j + 1) t = t [j - 1 := t ! j, j := t ! (j - 1)]"
        have f2: "t[j - 1 := t ! j, j := t ! (j - 1)] = take j (t[j - 1 := t ! j]) @ t ! (j - 1) # drop (Suc j) (t[j - 1 := t ! j])"
          by (metis (no_types) "0.prems"(2) length_list_update upd_conv_take_nth_drop) (* 32 ms *)
        have f3: "\<forall>n na. \<not> n < na \<or> Suc n \<le> na"
          using Suc_leI by blast (* 0.0 ms *)
        then have "min (length t) (j + 1) = j + 1"
          by (metis (no_types) "0.prems"(2) Suc_eq_plus1 min.absorb2) (* 16 ms *)
        then have f4: "length ((take (j + 1) t)[j - 1 := t ! j]) = j + 1"
          by simp (* 4 ms *)
        have f5: "j + 1 \<le> length (t[j - 1 := t ! j])"
          using f3 by (metis (no_types) "0.prems"(2) Suc_eq_plus1 length_list_update) (* 8 ms *)
        have "Suc j \<le> j + 1"
          by linarith (* 0.0 ms *)
        then have "(take (j + 1) (t[j - 1 := t ! j]))[j := t ! (j - 1)] = take j (t[j - 1 := t ! j]) @ t ! (j - 1) # [] @ []"
          using f5 f4 by (metis (no_types) Suc_eq_plus1 add_diff_cancel_right' butlast_conv_take butlast_take drop_eq_Nil lessI self_append_conv2 take_update_swap upd_conv_take_nth_drop) (* 180 ms *)
        then show ?thesis
          using f2 a1 by (simp add: take_update_swap) (* 120 ms *)
      qed
    qed
  qed
  have s: "trace init (take i t) (S t i)" 
    using "0.prems"(6) exists_trace_for_any_i by blast
  have e: "trace (S t (j+1)) (take (length t - (j+1)) (drop (j+1) t)) final"
  proof -
    have "trace init (take (length t) t) final" 
      by (simp add: "0.prems"(6))
    then show ?thesis 
      by (metis "0.prems"(2) Suc_eq_plus1 Suc_leI exists_trace_for_any_i exists_trace_for_any_i_j nat_le_linear take_all trace_and_start_determines_end)
  qed
  have "trace init (take i t @ [t ! j] @ [t ! i] @ drop (j+1) t) final"
  proof -
    from s swap have "trace init (take i t @ [t ! j,t ! i]) (S t (j+1))" using trace_trans by blast
    then have "trace init (take i t @ [t ! j, t ! i] @ (take (length t - (j+1)) (drop (j+1) t))) final"
      using e trace_trans by fastforce
    moreover have "take (length t - (j+1)) (drop (j+1) t) = drop (j+1) t" by simp
    ultimately show ?thesis by simp
  qed
  moreover have "take i t @ [t ! j] @ [t ! i] @ drop (j+1) t = (t[i := t ! j])[j := t ! i]"
  proof -
    have "length (take i t @ [t ! j] @ [t ! i] @ drop (j+1) t) = length ((t[i := t ! j])[j := t ! i])"
      by (metis (mono_tags, lifting) \<open>t = take i t @ [t ! i] @ take (j - (i + 1)) (drop (i + 1) t) @ [t ! j] @ drop (j + 1) t\<close> \<open>take (j - (i + 1)) (drop (i + 1) t) = []\<close> length_append length_list_update list.size(4) self_append_conv2)
    moreover have "\<And>k. k < length ((t[i := t ! j])[j := t ! i]) \<Longrightarrow> (take i t @ [t ! j] @ [t ! i] @ drop (j+1) t) ! k = ((t[i := t ! j])[j := t ! i]) ! k"
    proof -
      fix k
      assume "k < length ((t[i := t ! j])[j := t ! i])"
      show "(take i t @ [t ! j] @ [t ! i] @ drop (j+1) t) ! k = ((t[i := t ! j])[j := t ! i]) ! k"
      proof (cases "k = i \<or> k = j")
        case True
        then show ?thesis
        proof (elim disjE)
          assume "k = i"
          then show ?thesis 
            by (metis (no_types, lifting) \<open>k < length (t[i := t ! j, j := t ! i])\<close> append_Cons le_eq_less_or_eq length_list_update length_take min.absorb2 nth_append_length nth_list_update_eq nth_list_update_neq)
        next
          assume "k = j"
          then show ?thesis 
            by (metis (no_types, lifting) "0.prems"(4) Suc_eq_plus1 \<open>j = i + 1\<close> \<open>k < length (t[i := t ! j, j := t ! i])\<close> append.assoc append_Cons le_eq_less_or_eq length_append_singleton length_list_update length_take min.absorb2 nth_append_length nth_list_update postrecording_event)
        qed
      next
        case knij: False
        then show ?thesis
        proof (cases "k < i")
          case True
          then show ?thesis 
            by (metis (no_types, lifting) "0.prems"(2) \<open>j = i + 1\<close> add_lessD1 length_take less_imp_le_nat min.absorb2 not_less nth_append nth_list_update_neq nth_take)
        next
          case False
          then have "k > j" 
            using \<open>j = i + 1\<close> knij by linarith
          then have "(take i t @ [t ! j] @ [t ! i] @ drop (j+1) t) ! k = drop (j+1) t ! (k-(j+1))"
          proof -
            assume a1: "j < k"
            have f2: "\<forall>n na. ((n::nat) < na) = (n \<le> na \<and> n \<noteq> na)"
              using nat_less_le by blast (* 0.0 ms *)
            have f3: "i + 0 = min (length t) i + (0 + 0)"
              using "0.prems"(2) \<open>j = i + 1\<close> by linarith (* 8 ms *)
            have f4: "min (length t) i + Suc (0 + 0) = length (take i t) + length [t ! j]"
              by force (* 4 ms *)
            have f5: "take i t @ [t ! j] @ [] = take i t @ [t ! j]"
              by auto (* 0.0 ms *)
            have "j = length (take i t @ [t ! j] @ [])"
              using f3 by (simp add: \<open>j = i + 1\<close>) (* 4 ms *)
            then have "j + 1 = length (take i t @ [t ! j] @ [t ! i])"
              by fastforce (* 4 ms *)
            then show ?thesis
              using f5 f4 f3 f2 a1 by (metis (no_types) One_nat_def \<open>j = i + 1\<close> add_Suc_right append.assoc length_append less_antisym list.size(3) not_less nth_append) (* 284 ms *)
          qed
          moreover have "(t[i := t ! j])[j := t ! i] ! k = drop (j+1) ((t[i := t ! j])[j := t ! i]) ! (k-(j+1))" 
            using "0.prems"(2) \<open>j < k\<close> by auto
          moreover have "drop (j+1) ((t[i := t ! j])[j := t ! i]) = drop (j+1) t" 
            using "0.prems"(1) by auto
          ultimately show ?thesis by simp
        qed
      qed
    qed
    ultimately show ?thesis by (simp add: list_eq_iff_nth_eq)
  qed
  moreover have "\<forall>k. k \<ge> j + 1 \<longrightarrow> S t k = S ((t[i := t ! j])[j := t ! i]) k"
  proof (rule allI, rule impI)
    fix k
    assume "k \<ge> j + 1"
    let ?newt = "((t[i := t ! j])[j := t ! i])"
    have "trace init (take k ?newt) (S ?newt k)" 
      using calculation(1) calculation(2) exists_trace_for_any_i by auto
    have "take k ?newt = take (j+1) ?newt @ take (k - (j+1)) (drop (j+1) ?newt)"
      by (metis \<open>j + 1 \<le> k\<close> le_add_diff_inverse take_add)
    have same_traces: "drop (j+1) t = drop (j+1) ?newt" 
      by (metis "0.prems"(1) Suc_eq_plus1 \<open>j = i + 1\<close> drop_update_cancel less_SucI less_add_same_cancel1)
    have "trace init (take (j+1) ((t[i := t ! j])[j := t ! i])) (S t (j+1))"
      by (metis (no_types, lifting) \<open>j = i + 1\<close> \<open>take (j - 1) t @ [t ! j, t ! i] = (take (j + 1) t)[i := t ! j, j := t ! i]\<close> add_diff_cancel_right' local.swap s take_update_swap trace_trans)
    moreover have "trace init (take (j+1) ?newt) (S ?newt (j+1))"  
      using \<open>take i t @ [t ! j] @ [t ! i] @ drop (j + 1) t = t[i := t ! j, j := t ! i]\<close> \<open>trace init (take i t @ [t ! j] @ [t ! i] @ drop (j + 1) t) final\<close> exists_trace_for_any_i by auto
    ultimately have "S ?newt (j+1) = S t (j+1)" 
      using trace_and_start_determines_end by blast
    have "trace (S t (j+1)) (take (k - (j+1)) (drop (j+1) t)) (S t k)" 
      using "0.prems"(6) \<open>j + 1 \<le> k\<close> exists_trace_for_any_i_j by blast
    moreover have "trace (S ?newt (j+1)) (take (k - (j+1)) (drop (j+1) ?newt)) (S ?newt k)" 
      using \<open>j + 1 \<le> k\<close> \<open>take i t @ [t ! j] @ [t ! i] @ drop (j + 1) t = t[i := t ! j, j := t ! i]\<close> \<open>trace init (take i t @ [t ! j] @ [t ! i] @ drop (j + 1) t) final\<close> exists_trace_for_any_i_j by fastforce
    ultimately show "S t k = S ?newt k" 
      using \<open>S (t[i := t ! j, j := t ! i]) (j + 1) = S t (j + 1)\<close> same_traces trace_and_start_determines_end by auto
  qed
  moreover have "\<forall>k. k \<le> i \<longrightarrow> S t k = S ((t[i := t ! j])[j := t ! i]) k"
  proof (rule allI, rule impI)
    fix k
    assume "k \<le> i"
    let ?newt = "((t[i := t ! j])[j := t ! i])"
    have "trace init (take k t) (S t k)" 
      using "0.prems"(6) exists_trace_for_any_i by blast
    moreover have "trace init (take k ?newt) (S ?newt k)" 
      using \<open>take i t @ [t ! j] @ [t ! i] @ drop (j + 1) t = t[i := t ! j, j := t ! i]\<close> \<open>trace init (take i t @ [t ! j] @ [t ! i] @ drop (j + 1) t) final\<close> exists_trace_for_any_i by auto
    moreover have "take k t = take k ?newt" 
      using "0.prems"(1) \<open>k \<le> i\<close> by auto
    ultimately show "S t k = S ?newt k" 
      by (simp add: trace_and_start_determines_end)
  qed
  moreover have "prerecording_event (swap_events i j t) i"
  proof -
    have "~ has_snapshotted (S ((t[i := t ! j])[j := t ! i]) i) ?q" 
      by (metis "0.prems"(6) \<open>j = i + 1\<close> add.right_neutral calculation(4) le_add1 nsq snapshot_stable_ver_3)
    moreover have "regular_event ((t[i := t ! j])[j := t ! i] ! i)" 
      by (metis "0.prems"(4) "0.prems"(5) \<open>occurs_on (t ! i) \<noteq> occurs_on (t ! j)\<close> nth_list_update_eq nth_list_update_neq postrecording_event prerecording_event)
    moreover have "i < length ((t[i := t ! j])[j := t ! i])" 
      using "0.prems"(1) "0.prems"(2) by auto
    ultimately show ?thesis unfolding prerecording_event 
      by (metis (no_types, hide_lams) "0.prems"(1) \<open>take (j - (i + 1)) (drop (i + 1) t) = []\<close> \<open>take i t @ [t ! j] @ [t ! i] @ drop (j + 1) t = t[i := t ! j, j := t ! i]\<close> append_Cons length_list_update nat_less_le nth_list_update_eq nth_list_update_neq self_append_conv2)
  qed
  moreover have "postrecording_event (swap_events i j t) (i+1)"
  proof -
    have "has_snapshotted (S ((t[i := t ! j])[j := t ! i]) (i+1)) ?p" 
      by (metis "0.prems"(4) add.right_neutral calculation(1) calculation(2) calculation(4) le_add1 postrecording_event snapshot_stable_ver_3)
    moreover have "regular_event ((t[i := t ! j])[j := t ! i] ! j)" 
      using "0.prems"(2) "0.prems"(4) length_list_update postrecording_event by auto
    moreover have "j < length t" using "0.prems" by auto
    ultimately show ?thesis unfolding postrecording_event 
      by (metis \<open>j = i + 1\<close> length_list_update nth_list_update_eq swap_neighbors_2)
  qed
  moreover have "\<forall>k. k > i+1 \<and> k < j+1 \<longrightarrow> ~ regular_event ((swap_events i j t) ! k)" using "0" by force
  ultimately show ?case using \<open>j = i + 1\<close> by force
next
  case (Suc n)
  let ?p = "occurs_on (t ! i)"
  let ?q = "occurs_on (t ! j)"
  let ?t = "take ((j+1) - i) (drop i t)"
  let ?subt = "take (j - (i+1)) (drop (i+1) t)"
  let ?subt' = "take ((j-1) - (i+1)) (drop (i+1) t)"
  have sp: "has_snapshotted (S t i) ?p"
    using Suc.prems postrecording_event prerecording_event by blast
  have nsq: "~ has_snapshotted (S t j) ?q"
    using Suc.prems postrecording_event prerecording_event by blast
  have "?p \<noteq> ?q"
    using Suc.prems computation.post_before_pre_different_processes computation_axioms by blast
  have "?subt \<noteq> Nil" 
    using Suc.hyps(2) Suc.prems(1) Suc.prems(2) by auto
  have "?subt' = butlast ?subt" 
    by (metis Suc.prems(2) Suc_eq_plus1 butlast_drop butlast_take drop_take less_imp_le_nat)
  have "?t = t ! i # ?subt @ [t ! j]" 
  proof -
    have f1: "Suc j - i = Suc (j - i)"
      using Suc.prems(1) Suc_diff_le le_simps(1) by presburger
    have f2: "t ! i # drop (Suc i) t = drop i t"
      by (meson Cons_nth_drop_Suc Suc.prems(1) Suc.prems(2) less_trans)
    have f3: "t ! j # drop (Suc j) t = drop j t"
      using Cons_nth_drop_Suc Suc.prems(2) by blast
    have f4: "j - (i + 1) + (i + 1) = j"
      using Suc.prems(1) by force
    have "j - (i + 1) + Suc 0 = j - i"
      using Suc.prems(1) Suc_diff_Suc by presburger
    then show ?thesis
      using f4 f3 f2 f1 by (metis One_nat_def Suc.hyps(2) Suc_eq_plus1 drop_drop take_Suc_Cons take_add take_eq_Nil)
  qed
  then have "trace (S t i) ?t (S t (j+1))" 
    by (metis Suc.prems(1) Suc.prems(6) Suc_eq_plus1 exists_trace_for_any_i_j less_SucI nat_less_le)
  then have reg_tr_1:  "trace (S t i) (t ! i # ?subt) (S t j)" 
    by (metis (no_types, hide_lams) Suc.hyps(2) Suc.prems(1) Suc.prems(4) Suc.prems(6) Suc_eq_plus1 discrete exists_trace_for_any_i_j postrecording_event step_Suc tr_step)
  have reg_st_2: "(S t j) \<turnstile> (t ! j) \<mapsto> (S t (j+1))" 
    using Suc.prems(2) Suc.prems(6) step_Suc by auto
  have "?subt = ?subt' @ [t ! (j-1)]"
  proof -
    have f1: "\<forall>n es. \<not> n < length es \<or> take n es @ [hd (drop n es)::('a, 'b, 'c) event] = take (Suc n) es"
      by (meson take_hd_drop) (* 0.0 ms *)
    have f2: "j - 1 - (i + 1) = n"
      by (metis (no_types) Suc.hyps(2) Suc_eq_plus1 diff_Suc_1 diff_diff_left plus_1_eq_Suc) (* 28 ms *)
    have f3: "\<forall>n na. \<not> n < na \<or> Suc n \<le> na"
      using Suc_leI by blast (* 0.0 ms *)
    then have f4: "Suc i \<le> j - 1"
      by (metis (no_types) Suc.hyps(2) Suc_eq_plus1 diff_diff_left plus_1_eq_Suc zero_less_Suc zero_less_diff) (* 12 ms *)
    have f5: "i + 1 < j"
      by (metis Suc.hyps(2) zero_less_Suc zero_less_diff) (* 4 ms *)
    then have f6: "t ! (j - 1) = hd (drop n (drop (i + 1) t))"
      using f4 f3 by (metis (no_types) Suc.hyps(2) Suc.prems(2) Suc_eq_plus1 Suc_lessD add_Suc_right diff_Suc_1 drop_drop hd_drop_conv_nth le_add_diff_inverse2 plus_1_eq_Suc) (* 140 ms *)
    have "n < length (drop (i + 1) t)"
      using f5 f3 by (metis (no_types) Suc.hyps(2) Suc.prems(2) Suc_eq_plus1 Suc_lessD drop_drop le_add_diff_inverse2 length_drop zero_less_diff) (* 144 ms *)
    then show ?thesis
      using f6 f2 f1 Suc.hyps(2) by presburger (* 4 ms *)
  qed
  then have reg_tr: "trace (S t i) (t ! i # ?subt') (S t (j-1))" 
  proof -
    have f1: "j - Suc i = Suc n"
      using Suc.hyps(2) by presburger
    have f2: "length (take j t) = j"
      by (metis (no_types) Suc.prems(2) length_take min.absorb2 nat_le_linear not_less)
    have f3: "(t ! i # drop (Suc i) (take j t)) @ [t ! j] = drop i (take (Suc j) t)"
      by (metis (no_types) Suc_eq_plus1 \<open>take (j + 1 - i) (drop i t) = t ! i # take (j - (i + 1)) (drop (i + 1) t) @ [t ! j]\<close> append_Cons drop_take)
    have f4: "Suc (i + n) = j - 1"
      using f1 by (metis (no_types) Suc.prems(1) Suc_diff_Suc add_Suc_right diff_Suc_1 le_add_diff_inverse nat_le_linear not_less)
    have "Suc (j - 1) = j"
      using f1 by simp
    then have f5: "butlast (take (Suc j) t) = take j t"
      using f4 f3 f2 f1 by (metis (no_types) Groups.add_ac(2) One_nat_def append_eq_conv_conj append_take_drop_id butlast_take diff_Suc_1 drop_drop length_append length_drop list.size(3) list.size(4) order_refl plus_1_eq_Suc plus_nat.simps(2) take_add take_all)
    have f6: "butlast (take j t) = take (j - 1) t"
      by (meson Suc.prems(2) butlast_take nat_le_linear not_less)
    have "drop (Suc i) (take j t) \<noteq> []"
      by (metis (no_types) Nil_is_append_conv Suc_eq_plus1 \<open>take (j - (i + 1)) (drop (i + 1) t) = take (j - 1 - (i + 1)) (drop (i + 1) t) @ [t ! (j - 1)]\<close> drop_take list.distinct(1))
    then show ?thesis
      using f6 f5 f4 f3 by (metis (no_types) Suc.prems(6) Suc_eq_plus1 butlast.simps(2) butlast_drop butlast_snoc drop_take exists_trace_for_any_i_j less_add_Suc1 nat_le_linear not_less)
  qed

  have reg_st_1: "(S t (j-1)) \<turnstile> (t ! (j-1)) \<mapsto> (S t j)" 
    by (metis Suc.prems(1) Suc.prems(2) Suc.prems(6) Suc_lessD diff_Suc_1 less_imp_Suc_add step_Suc)
  have "~ regular_event (t ! (j-1))" 
    using Suc.prems(3) \<open>take (j - (i + 1)) (drop (i + 1) t) \<noteq> []\<close> less_diff_conv by auto
  moreover have "regular_event (t ! j)" 
    using Suc.prems(5) computation.prerecording_event computation_axioms by blast
  moreover have "can_occur (t ! j) (S t j)" 
    using happen_implies_can_occur reg_tr_1 reg_st_2 by blast
  moreover have njmiq: "occurs_on (t ! (j-1)) \<noteq> ?q"
  proof (rule ccontr)
    assume "~ occurs_on (t ! (j-1)) \<noteq> ?q"
    then have "occurs_on (t ! (j-1)) = ?q" by simp
    then have "has_snapshotted (S t j) ?q" 
      using Suc.prems(6) calculation(1) diff_le_self nonregular_event_induces_snapshot reg_st_1 snapshot_stable_ver_2 by blast
    then show False using nsq by simp
  qed
  ultimately have "can_occur (t ! j) (S t (j-1))"
    using reg_tr reg_st_1 event_can_go_back_if_no_sender by auto
  then obtain d where new_st_1: "(S t (j-1)) \<turnstile> (t ! j) \<mapsto> d" 
    using exists_next_if_can_occur by blast
  then have "trace (S t i) (t ! i # ?subt' @ [t ! j]) d" using reg_tr trace_snoc by fastforce
  moreover have "can_occur (t ! (j-1)) d" 
    using \<open>(S t (j-1)) \<turnstile> t ! j \<mapsto> d\<close> \<open>occurs_on (t ! (j - 1)) \<noteq> occurs_on (t ! j)\<close> event_stays_valid_if_no_occurrence happen_implies_can_occur reg_st_1 by auto
  moreover obtain e where new_st_2: "d \<turnstile> (t ! (j-1)) \<mapsto> e" 
    using calculation(2) exists_next_if_can_occur by blast

  have pre_swap: "e = (S t (j+1))"
  proof -
    have "states e = states (S t (j+1))"
    proof (rule ext)
      fix p
      have "states (S t (j-1)) p = states (S t j) p"
        using no_state_change_if_nonregular_event\<open>~ regular_event (t ! (j-1))\<close> reg_st_1 by auto
      moreover have "states d p = states e p"
        using no_state_change_if_nonregular_event\<open>~ regular_event (t ! (j-1))\<close> new_st_2 by auto
      moreover have "states d p = states (S t (j+1)) p" 
      proof -
        have "\<forall>a. states (S t (j + 1)) a = states d a"
          by (meson \<open>\<not> regular_event (t ! (j - 1))\<close> new_st_1 no_state_change_if_nonregular_event reg_st_1 reg_st_2 same_state_implies_same_result_state)
        then show ?thesis
          by presburger
      qed
      ultimately show "states e p = states (S t (j+1)) p" by simp
    qed

    moreover have "msgs e = msgs (S t (j+1))"
    proof (rule ext)
      fix cid
      have "isTrans (t ! j) \<or> isSend (t ! j) \<or> isRecv (t ! j)" 
        using \<open>regular_event (t ! j)\<close> by auto
      moreover have "isSnapshot (t ! (j-1)) \<or> isRecvMarker (t ! (j-1))"
        using nonregular_event \<open>~ regular_event (t ! (j-1))\<close> by auto
      ultimately show "msgs e cid = msgs (S t (j+1)) cid"
      proof (elim disjE, goal_cases)
        case 1
        then show ?case 
          using new_st_1 new_st_2 njmiq reg_st_1 reg_st_2 swap_Trans_Snapshot by auto
      next
        case 2
        then show ?case 
          using new_st_1 new_st_2 njmiq reg_st_1 reg_st_2 swap_msgs_Trans_RecvMarker by auto
      next
        case 3
        then show ?case 
          using new_st_1 new_st_2 njmiq reg_st_1 reg_st_2 swap_Send_Snapshot by auto
      next
        case 4
        then show ?case 
          using new_st_1 new_st_2 njmiq reg_st_1 reg_st_2 swap_Recv_Snapshot by auto
      next
        case 5
        then show ?case 
          using new_st_1 new_st_2 njmiq reg_st_1 reg_st_2 swap_msgs_Send_RecvMarker by auto
      next
        case 6
        then show ?case 
          using new_st_1 new_st_2 njmiq reg_st_1 reg_st_2 swap_msgs_Recv_RecvMarker by auto
      qed
    qed

    moreover have "process_snapshot e = process_snapshot (S t (j+1))"
    proof (rule ext)
      fix p
      have "process_snapshot (S t j) p = process_snapshot (S t (j+1)) p" 
        using \<open>regular_event (t ! j)\<close> reg_st_2 regular_event_preserves_process_snapshots by blast
      moreover have "process_snapshot (S t (j-1)) p = process_snapshot d p" 
        using \<open>regular_event (t ! j)\<close> new_st_1 regular_event_preserves_process_snapshots by blast
      moreover have "process_snapshot e p = process_snapshot (S t j) p" 
      proof -
        have "occurs_on (t ! j) = p \<longrightarrow> ps e p = ps (S t j) p"
          using calculation(2) new_st_2 njmiq no_state_change_if_no_event reg_st_1 by force
        then show ?thesis
          by (meson new_st_1 new_st_2 no_state_change_if_no_event reg_st_1 same_snapshot_state_implies_same_result_snapshot_state)
      qed
      ultimately show "process_snapshot e p = process_snapshot (S t (j+1)) p" by simp
    qed

    moreover have "cs e = cs (S t (j+1))"
    proof (rule ext)
      fix cid
      have "isTrans (t ! j) \<or> isSend (t ! j) \<or> isRecv (t ! j)" 
        using \<open>regular_event (t ! j)\<close> by auto
      moreover have "isSnapshot (t ! (j-1)) \<or> isRecvMarker (t ! (j-1))"
        using nonregular_event \<open>~ regular_event (t ! (j-1))\<close> by auto
      ultimately show "cs e cid = cs (S t (j+1)) cid"
      proof (elim disjE, goal_cases)
        case 1
        then show ?case 
          using new_st_1 new_st_2 reg_st_1 reg_st_2 swap_cs_Trans_Snapshot by auto
      next
        case 2
        then show ?case
          using new_st_1 new_st_2 reg_st_1 reg_st_2 swap_cs_Trans_RecvMarker by auto
      next
        case 3
        then show ?case
          using new_st_1 new_st_2 reg_st_1 reg_st_2 swap_cs_Send_Snapshot by auto
      next
        case 4
        then show ?case
          using new_st_1 new_st_2 reg_st_1 reg_st_2 swap_cs_Recv_Snapshot njmiq by auto
      next
        case 5
        then show ?case
          using new_st_1 new_st_2 reg_st_1 reg_st_2 swap_cs_Send_RecvMarker by auto
      next
        case 6
        then show ?case
          using new_st_1 new_st_2 reg_st_1 reg_st_2 swap_cs_Recv_RecvMarker njmiq by auto
      qed
    qed
    ultimately show ?thesis by auto
  qed

  let ?it = "(t[j-1 := t ! j])[j := t ! (j-1)]"
  have same_prefix: "take (j-1) ?it = take (j-1) t" by simp
  have same_suffix: "drop (j+1) ?it = drop (j+1) t" by simp
  have trace_prefix: "trace init (take (j-1) ?it) (S t (j-1))"
    using Suc.prems(6) exists_trace_for_any_i by auto
  have "?it = take (j-1) t @ [t ! j, t ! (j-1)] @ drop (j+1) t" 
  proof -
    have "1 < j"
      by (metis (no_types) Suc.hyps(2) Suc_eq_plus1 add_lessD1 plus_1_eq_Suc zero_less_Suc zero_less_diff) (* 12 ms *)
    then have "j - 1 + 1 = j"
      by (metis (no_types) le_add_diff_inverse2 nat_less_le) (* 4 ms *)
    then show ?thesis
      by (metis (no_types) Suc.prems(2) Suc_eq_plus1 add_Suc_right one_add_one swap_neighbors) (* 76 ms *)
  qed
  have "trace (S t (j-1)) [t ! j, t ! (j-1)] (S t (j+1))" 
    by (metis new_st_1 new_st_2 pre_swap trace.simps)
  have "trace init (take (j+1) t @ drop (j+1) t) final" 
    by (simp add: Suc.prems(6))
  then have "trace init (take (j+1) t) (S t (j+1)) \<and> trace (S t (j+1)) (drop (j+1) t) final" 
    using Suc.prems(6) exists_trace_for_any_i split_trace trace_and_start_determines_end by blast
  then have trace_suffix: "trace (S t (j+1)) (drop (j+1) ?it) final" using same_suffix by simp
  have "trace init ?it final" 
    by (metis (no_types, lifting) \<open>t[j - 1 := t ! j, j := t ! (j - 1)] = take (j - 1) t @ [t ! j, t ! (j - 1)] @ drop (j + 1) t\<close> \<open>trace (S t (j + 1)) (drop (j + 1) (t[j - 1 := t ! j, j := t ! (j - 1)])) final\<close> \<open>trace (S t (j - 1)) [t ! j, t ! (j - 1)] (S t (j + 1))\<close> \<open>trace init (take (j - 1) (t[j - 1 := t ! j, j := t ! (j - 1)])) (S t (j - 1))\<close> same_prefix same_suffix trace_trans)
  have suffix_same_states: "\<forall>k. k > j \<longrightarrow> S t k = S ?it k"
  proof (rule allI, rule impI)
    fix k
    assume "k > j"
    have eq_trace: "drop (j+1) t = drop (j+1) ?it" by simp
    have "trace init (take (j+1) ?it) (S ?it (j+1))" 
      using \<open>trace init (t[j - 1 := t ! j, j := t ! (j - 1)]) final\<close> exists_trace_for_any_i by blast
    moreover have "trace init (take (j+1) ?it) (S t (j+1))" 
    proof -
      have f1: "\<forall>es esa esb esc. (esb::('a, 'b, 'c) event list) @ es \<noteq> esa @ esc @ es \<or> esa @ esc = esb"
        by auto
      have f2: "take (j + 1) (t[j - 1 := t ! j, j := t ! (j - 1)]) @ drop (j + 1) t = t [j - 1 := t ! j, j := t ! (j - 1)]"
        by (metis append_take_drop_id same_suffix)
      have "trace init (take (j - 1) t @ [t ! j, t ! (j - 1)]) (S t (j + 1))"
        using \<open>trace (S t (j - 1)) [t ! j, t ! (j - 1)] (S t (j + 1))\<close> same_prefix trace_prefix trace_trans by presburger
      then show ?thesis
        using f2 f1 by (metis (no_types) \<open>t[j - 1 := t ! j, j := t ! (j - 1)] = take (j - 1) t @ [t ! j, t ! (j - 1)] @ drop (j + 1) t\<close>)
    qed
    ultimately have eq_start: "S ?it (j+1) = S t (j+1)" 
      using trace_and_start_determines_end by blast
    then have "take k ?it = take (j+1) ?it @ take (k - (j+1)) (drop (j+1) ?it)" 
      by (metis Suc_eq_plus1 Suc_leI \<open>j < k\<close> le_add_diff_inverse take_add)
    have "trace (S ?it (j+1)) (take (k - (j+1)) (drop (j+1) ?it)) (S ?it k)" 
      by (metis Suc_eq_plus1 Suc_leI \<open>j < k\<close> \<open>trace init (t[j - 1 := t ! j, j := t ! (j - 1)]) final\<close> exists_trace_for_any_i_j)
    moreover have "trace (S t (j+1)) (take (k - (j+1)) (drop (j+1) t)) (S t k)" 
      using Suc.prems(6) \<open>j < k\<close> exists_trace_for_any_i_j by fastforce
    ultimately show "S t k = S ?it k" 
      using eq_start trace_and_start_determines_end by auto
  qed
  have prefix_same_states: "\<forall>k. k < j \<longrightarrow> S t k = S ?it k"
  proof (rule allI, rule impI)
    fix k
    assume "k < j"
    have "trace init (take k t) (S t k)" 
      using Suc.prems(6) exists_trace_for_any_i by blast
    moreover have "trace init (take k ?it) (S ?it k)" 
      by (meson \<open>trace init (t[j - 1 := t ! j, j := t ! (j - 1)]) final\<close> exists_trace_for_any_i)
    ultimately show "S t k = S ?it k" 
      using \<open>k < j\<close> s_def by auto
  qed
  moreover have "j - 1 < length ?it"
    using Suc.prems(2) by auto
  moreover have "prerecording_event ?it (j-1)" 
  proof -
    have f1: "t[j - 1 := t ! j, j := t ! (j - 1)] ! (j - 1) = t[j - 1 := t ! j] ! (j - 1)"
      by (metis (no_types) njmiq nth_list_update_neq) (* 28 ms *)
    have "j \<noteq> 0"
      by (metis (no_types) Suc.prems(1) not_less_zero) (* 0.0 ms *)
    then have "\<not> j < 1"
      by blast (* 0.0 ms *)
    then have "S t (j - 1) = S (t[j - 1 := t ! j, j := t ! (j - 1)]) (j - 1)"
      by (simp add: prefix_same_states) (* 8 ms *)
    then show ?thesis
      using f1 by (metis \<open>regular_event (t ! j)\<close> calculation(4) computation.prerecording_event computation_axioms length_list_update njmiq no_state_change_if_no_event nsq nth_list_update_eq reg_st_1) (* 456 ms *)
  qed
  moreover have "postrecording_event ?it i"
  proof -
    have "i < length ?it" 
      using Suc.prems(4) postrecording_event by auto
    then show ?thesis 
    proof -
      assume "i < length (t[j - 1 := t ! j, j := t ! (j - 1)])"
      have "i < j - 1"
        by (metis (no_types) Suc.hyps(2) cancel_ab_semigroup_add_class.diff_right_commute diff_diff_left zero_less_Suc zero_less_diff)
      then show ?thesis
        using Suc.prems(1) Suc.prems(4) postrecording_event prefix_same_states by auto
    qed
  qed
  moreover have "i < j - 1"
    using Suc.hyps(2) by auto
  moreover have "\<forall>k. i < k \<and> k < (j-1) \<longrightarrow> ~ regular_event (?it ! k)"
  proof (rule allI, rule impI)
    fix k
    assume "i < k \<and> k < (j-1)"
    show "~ regular_event (?it ! k)" 
      using Suc.prems(3) \<open>i < k \<and> k < j - 1\<close> by force
  qed
  moreover have "(j-1) - (i+1) = n" using Suc.prems Suc.hyps by auto
  ultimately have ind: "trace init (swap_events i (j-1) ?it) final
                        \<and> (\<forall>k. k \<ge> (j-1)+1 \<longrightarrow> S (swap_events i (j-1) ?it) k = S ?it k)
                        \<and> (\<forall>k. k \<le> i \<longrightarrow> S (swap_events i (j-1) ?it) k = S ?it k)
                        \<and> prerecording_event (swap_events i (j-1) ?it) i
                        \<and> postrecording_event (swap_events i (j-1) ?it) (i+1)
                        \<and> (\<forall>k. k > i+1 \<and> k < (j-1)+1 \<longrightarrow> ~ regular_event ((swap_events i (j-1) ?it) ! k))"
    using Suc.hyps \<open>trace init ?it final\<close> by blast
  then have new_trace: "trace init (swap_events i (j-1) ?it) final" by blast
  have equal_suffix_states: "\<forall>k. k \<ge> j \<longrightarrow> S (swap_events i (j-1) ?it) k = S ?it k" 
    using Suc.prems(1) ind by simp
  have equal_prefix_states: "\<forall>k. k \<le> i \<longrightarrow> S (swap_events i (j-1) ?it) k = S ?it k"
    using ind by blast
  have neighboring_events_shifted: "\<forall>k. k > i+1 \<and> k < j \<longrightarrow> ~ regular_event ((swap_events i (j-1) ?it) ! k)"
    using ind by force

  let ?itn = "swap_events i (j-1) ?it"
  have "?itn = swap_events i j t"
  proof -
    have f1: "i \<le> j - 1"
      using \<open>i < j - 1\<close> less_imp_le_nat by blast
    have "t ! j # [t ! (j - 1)] @ drop (j + 1) t = drop (j - 1) (take (j - 1) t @ [t ! j, t ! (j - 1)] @ drop (j + 1) t)"
      using \<open>t[j - 1 := t ! j, j := t ! (j - 1)] = take (j - 1) t @ [t ! j, t ! (j - 1)] @ drop (j + 1) t\<close> same_prefix by force
    then have f2: "t[j - 1 := t ! j, j := t ! (j - 1)] ! (j - 1) = t ! j \<and> drop (j - 1 + 1) (t[j - 1 := t ! j, j := t ! (j - 1)]) = t ! (j - 1) # [] @ drop (j + 1) t"
      by (metis (no_types) Cons_nth_drop_Suc Suc_eq_plus1 \<open>j - 1 < length (t[j - 1 := t ! j, j := t ! (j - 1)])\<close> \<open>t[j - 1 := t ! j, j := t ! (j - 1)] = take (j - 1) t @ [t ! j, t ! (j - 1)] @ drop (j + 1) t\<close> append_Cons list.inject)
    have "t ! i = t[j - 1 := t ! j, j := t ! (j - 1)] ! i"
      by (metis (no_types) Suc.prems(1) \<open>i < j - 1\<close> nat_neq_iff nth_list_update_neq)
    then show ?thesis
      using f2 f1 by (metis (no_types) Suc.prems(1) \<open>take (j - (i + 1)) (drop (i + 1) t) = take (j - 1 - (i + 1)) (drop (i + 1) t) @ [t ! (j - 1)]\<close> append.assoc append_Cons drop_take less_imp_le_nat same_prefix take_update_cancel)
  qed

  moreover have "\<forall>k. k \<le> i \<longrightarrow> S t k = S ?itn k" 
    using Suc.prems(1) equal_prefix_states prefix_same_states by auto
  moreover have "\<forall>k. k \<ge> j + 1 \<longrightarrow> S t k = S ?itn k" 
    by (metis (no_types, lifting) Suc_eq_plus1 add_lessD1 equal_suffix_states lessI nat_less_le suffix_same_states)
  moreover have "\<forall>k. k > i+1 \<and> k < j+1 \<longrightarrow> ~ regular_event (?itn ! k)"
  proof -
    have "~ regular_event (?itn ! j)" 
    proof -
      have f1: "j - 1 < length t"
        using \<open>j - 1 < length (t[j - 1 := t ! j, j := t ! (j - 1)])\<close> by force
      have f2: "\<And>n na es. \<not> n < na \<or> \<not> na < length es \<or> drop (Suc na) (take n es @ [hd (drop na es), es ! n::('a, 'b, 'c) event] @ take (na - Suc n) (drop (Suc n) es) @ drop (Suc na) es) = drop (Suc na) es"
        by (metis Suc_eq_plus1 hd_drop_conv_nth swap_identical_tails)
      have f3: "t ! j = hd (drop j t)"
        by (simp add: Suc.prems(2) hd_drop_conv_nth)
      have "\<not> j < 1"
        using Suc.prems(1) by blast
      then have "\<not> regular_event (hd (drop j (take i (t[j - 1 := hd (drop j t), j := hd (drop (j - 1) t)]) @ [hd (drop (j - 1) (t[j - 1 := hd (drop j t), j := hd (drop (j - 1) t)])), t[j - 1 := hd (drop j t), j := hd (drop (j - 1) t)] ! i] @ take (j - 1 - Suc i) (drop (Suc i) (t[j - 1 := hd (drop j t), j := hd (drop (j - 1) t)])) @ drop (Suc (j - 1)) (t[j - 1 := hd (drop j t), j := hd (drop (j - 1) t)]))))"
        using f2 f1 by (metis (no_types) Suc.prems(2) \<open>\<not> regular_event (t ! (j - 1))\<close> \<open>i < j - 1\<close> add_diff_inverse_nat hd_drop_conv_nth length_list_update nth_list_update_eq plus_1_eq_Suc)
      then show ?thesis
        using f3 f1 by (metis Suc.prems(2) Suc_eq_plus1 \<open>i < j - 1\<close> hd_drop_conv_nth length_list_update swap_identical_length)
    qed
    then show ?thesis 
      by (metis Suc_eq_plus1 less_Suc_eq neighboring_events_shifted)
  qed

  ultimately show ?case using ind by presburger
qed

subsubsection \<open>Relating configurations and the computed snapshot\<close>

definition ps_equal_to_snapshot where
  "ps_equal_to_snapshot c c' \<equiv>
     \<forall>p. Some (states c p) = process_snapshot c' p"

definition cs_equal_to_snapshot where
  "cs_equal_to_snapshot c c' \<equiv>
     \<forall>cid. channel cid \<noteq> None
       \<longrightarrow> filter ((\<noteq>) Marker) (msgs c cid)
           = map Msg (fst (channel_snapshot c' cid))"

definition state_equal_to_snapshot where
  "state_equal_to_snapshot c c' \<equiv>
     ps_equal_to_snapshot c c' \<and> cs_equal_to_snapshot c c'"

lemma init_is_s_t_0:
  assumes
    "trace init t final"
  shows
    "init = (S t 0)"
  by (metis assms exists_trace_for_any_i take_eq_Nil tr_init trace_and_start_determines_end)

lemma final_is_s_t_len_t:
  assumes
    "trace init t final"
  shows
    "final = S t (length t)"
  by (metis assms exists_trace_for_any_i order_refl take_all trace_and_start_determines_end)

lemma snapshot_event:
  assumes
    "trace init t final" and
    "~ has_snapshotted (S t i) p" and
    "has_snapshotted (S t (i+1)) p"
  shows
    "isSnapshot (t ! i) \<or> isRecvMarker (t ! i)"
proof -
  have "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (i+1))" 
    by (metis Suc_eq_plus1 assms(1) assms(2) assms(3) distributed_system.step_Suc computation_axioms computation_def nat_less_le not_less not_less_eq s_def take_all)
  then show ?thesis 
    using assms(2) assms(3) nonregular_event regular_event_cannot_induce_snapshot by blast
qed

lemma snapshot_state:
  assumes
    "trace init t final" and
    "states (S t i) p = u" and
    "~ has_snapshotted (S t i) p" and
    "has_snapshotted (S t (i+1)) p"
  shows
    "ps (S t (i+1)) p = Some u"
proof -
  have step: "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (i+1))" 
    by (metis add.commute assms(1) assms(3) assms(4) le_SucI le_eq_less_or_eq le_refl nat_neq_iff no_change_if_ge_length_t plus_1_eq_Suc step_Suc)
  let ?q = "occurs_on (t ! i)"
  have qp: "?q = p"
  proof (rule ccontr)
    assume "?q \<noteq> p"
    then have "has_snapshotted (S t (i+1)) p = has_snapshotted (S t i) p" 
      using local.step no_state_change_if_no_event by auto
    then show False using assms by simp
  qed
  have "isSnapshot (t ! i) \<or> isRecvMarker (t ! i)" using assms snapshot_event by auto
  then show ?thesis
  proof (elim disjE, goal_cases)
    case 1
    then have "t ! i = Snapshot p"
      by (metis event.collapse(4) qp)
    then show ?thesis 
      using assms(2) local.step by auto
  next
    case 2
    then obtain cid' q where "t ! i = RecvMarker cid' p q"
      by (metis event.collapse(5) qp)
    then show ?thesis using assms step by auto
  qed
qed

lemma snapshot_state_unchanged_trace_2:
  shows
    "\<lbrakk> trace init t final; i \<le> j; j \<le> length t;
       ps (S t i) p = Some u
     \<rbrakk> \<Longrightarrow> ps (S t j) p = Some u"
proof (induct i j rule:S_induct)
  case S_init
  then show ?case by simp
next
  case S_step
  then show ?case using snapshot_state_unchanged by auto
qed

lemma no_recording_cs_if_not_snapshotted:
  shows
    "\<lbrakk> trace init t final; ~ has_snapshotted (S t i) p;
       channel cid = Some (q, p) \<rbrakk> \<Longrightarrow> cs (S t i) cid = cs init cid"
proof (induct i)
  case 0
  then show ?case 
    by (metis exists_trace_for_any_i list.discI take_eq_Nil trace.simps)
next
  case (Suc i)
  have "Suc i < length t"
  proof -
    have "has_snapshotted final p" 
      using all_processes_snapshotted_in_final_state valid by blast
    show ?thesis
    proof (rule ccontr)
      assume "~ Suc i < length t"
      then have "Suc i \<ge> length t" by simp
      then have "has_snapshotted (S t (Suc i)) p" 
        using Suc.prems(1) \<open>ps final p \<noteq> None\<close> final_is_s_t_len_t snapshot_stable_ver_3 by blast
      then show False using Suc by simp
    qed
  qed

  then have t_dec: "trace init (take i t) (S t i) \<and> (S t i) \<turnstile> (t ! i) \<mapsto> (S t (Suc i))"
    using Suc.prems(1) exists_trace_for_any_i step_Suc by auto
  moreover have step: "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (Suc i))" using calculation by simp

  ultimately have IH: "cs (S t i) cid = cs init cid" 
    using Suc.hyps Suc.prems(1) Suc.prems(2) Suc.prems(3) snapshot_state_unchanged by fastforce

  then show ?case
  proof (cases "t ! i")
    case (Snapshot r)
    have "r \<noteq> p"
    proof (rule ccontr)
      assume "~ r \<noteq> p"
      then have "r = p" by simp
      then have "has_snapshotted (S t (Suc i)) p" 
        using Snapshot step by auto
      then show False using Suc by simp
    qed
    then have "cs (S t i) cid = cs (S t (Suc i)) cid" 
      using Snapshot Suc.prems(3) local.step by auto
    then show ?thesis using IH by simp
  next
    case (RecvMarker cid' r s)
    have "r \<noteq> p"
    proof (rule ccontr)
      assume "~ r \<noteq> p"
      then have "r = p" by simp
      then have "has_snapshotted (S t (Suc i)) p"
        using RecvMarker t_dec recv_marker_means_snapshotted_1 by blast
      then show False using Suc by simp
    qed
    have "cid' \<noteq> cid"
    proof (rule ccontr)
      assume "~ cid' \<noteq> cid"
      then have "channel cid' = Some (s, r)" using t_dec can_occur_def RecvMarker by simp
      then show False 
        using Suc.prems(3) \<open>\<not> cid' \<noteq> cid\<close> \<open>r \<noteq> p\<close> by auto
    qed
    then have "cs (S t i) cid = cs (S t (Suc i)) cid"
    proof -
      have "\<nexists>s. channel cid = Some (s, r)" using \<open>r \<noteq> p\<close> Suc by simp
      with RecvMarker t_dec \<open>cid' \<noteq> cid\<close> \<open>r \<noteq> p\<close> Suc.prems(3) show ?thesis
        by (cases "has_snapshotted (S t i) r", auto)
    qed
    then show ?thesis using IH by simp
  next
    case (Trans r u u')
    then show ?thesis 
      using IH t_dec by auto
  next
    case (Send cid' r s u u' m)
    then show ?thesis 
      using IH local.step by auto
  next
    case (Recv cid' r s u u' m)
    then have "snd (cs (S t i) cid) = NotStarted" 
      by (simp add: IH no_initial_channel_snapshot)
    with Recv step Suc show ?thesis by (cases "cid' = cid", auto) 
  qed
qed

lemma cs_done_implies_has_snapshotted:
  assumes
    "trace init t final" and
    "snd (cs (S t i) cid) = Done" and
    "channel cid = Some (p, q)"
  shows
    "has_snapshotted (S t i) q"
proof -
  show ?thesis 
    using assms no_initial_channel_snapshot no_recording_cs_if_not_snapshotted by fastforce
qed

lemma exactly_one_snapshot:
  assumes
    "trace init t final"
  shows
    "\<exists>!i. ~ has_snapshotted (S t i) p \<and> has_snapshotted (S t (i+1)) p" (is ?P)
proof -
  have "~ has_snapshotted init p" 
    using no_initial_process_snapshot by auto
  moreover have "has_snapshotted final p" 
    using all_processes_snapshotted_in_final_state valid by blast
  moreover have "trace (S t 0) t (S t (length t))" 
    using assms final_is_s_t_len_t init_is_s_t_0 by auto
  ultimately have ex_snap: "\<exists>i. ~ has_snapshotted (S t i) p \<and> has_snapshotted (S t (i+1)) p" 
    using assms exists_snapshot_for_all_p by auto
  show ?thesis
  proof (rule ccontr)
    assume "~ ?P"
    then have "\<exists>i j. (i \<noteq> j) \<and> ~ has_snapshotted (S t i) p \<and> has_snapshotted (S t (i+1)) p \<and>
                                ~ has_snapshotted (S t j) p \<and> has_snapshotted (S t (j+1)) p"
      using ex_snap by blast
    then have "\<exists>i j. (i < j) \<and> ~ has_snapshotted (S t i) p \<and> has_snapshotted (S t (i+1)) p \<and>
                                ~ has_snapshotted (S t j) p \<and> has_snapshotted (S t (j+1)) p"
      by (meson linorder_neqE_nat)
    then obtain i j where "i < j" "~ has_snapshotted (S t i) p" "has_snapshotted (S t (i+1)) p"
                                  "~ has_snapshotted (S t j) p" "has_snapshotted (S t (j+1)) p"
      by blast
    have "trace (S t (i+1)) (take (j - (i+1)) (drop (i+1) t)) (S t j)" 
      using \<open>i < j\<close> assms exists_trace_for_any_i_j by fastforce
    then have "has_snapshotted (S t j) p" 
      using \<open>ps (S t (i + 1)) p \<noteq> None\<close> snapshot_stable by blast
    then show False using \<open>~ has_snapshotted (S t j) p\<close> by simp
  qed
qed

lemma initial_cs_changes_implies_nonregular_event:
  assumes
    "trace init t final" and
    "snd (cs (S t i) cid) = NotStarted" and
    "snd (cs (S t (i+1)) cid) \<noteq> NotStarted" and
    "channel cid = Some (p, q)"
  shows
    "~ regular_event (t ! i)"
proof -
  have "i < length t"
  proof (rule ccontr)
    assume "~ i < length t"
    then have "S t i = S t (i+1)" 
      using assms(1) no_change_if_ge_length_t by auto
    then show False using assms by presburger
    qed
  then have step: "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (i+1))" 
    using assms(1) step_Suc by auto
  show ?thesis
  proof (rule ccontr)
    assume "~ ~ regular_event (t ! i)"
    then have "regular_event (t ! i)" by simp
    then have "cs (S t i) cid = cs (S t (i+1)) cid"
    proof (cases "isRecv (t ! i)")
      case False
      then show ?thesis 
        using \<open>regular_event (t ! i)\<close> local.step no_cs_change_if_no_event by blast
    next
      case True
      then obtain cid' r s u u' m where Recv: "t ! i = Recv cid' r s u u' m" by (meson isRecv_def)
      with assms step show ?thesis
      proof (cases "cid = cid'")
        case True
        then show ?thesis using assms step Recv by simp
      next
        case False
        then show ?thesis using assms step Recv by simp
      qed
    qed
    then show False using assms by simp
  qed
qed

lemma cs_in_initial_state_implies_not_snapshotted:
  assumes
    "trace init t final" and
    "snd (cs (S t i) cid) = NotStarted" and
    "channel cid = Some (p, q)"
  shows
    "~ has_snapshotted (S t i) q"
proof (rule ccontr)
  assume "~ ~ has_snapshotted (S t i) q"
  then obtain j where "j < i" "~ has_snapshotted (S t j) q" "has_snapshotted (S t (j+1)) q" 
    by (metis Suc_eq_plus1 assms(1) exists_snapshot_for_all_p computation.snapshot_stable_ver_3 computation_axioms nat_le_linear order_le_less)
  have step_j: "(S t j) \<turnstile> (t ! j) \<mapsto> (S t (j+1))" 
    by (metis \<open>\<not> \<not> ps (S t i) q \<noteq> None\<close> \<open>\<not> ps (S t j) q \<noteq> None\<close> \<open>j < i\<close> add.commute assms(1) linorder_neqE_nat no_change_if_ge_length_t order_le_less order_refl plus_1_eq_Suc step_Suc)
  have tr_j_i: "trace (S t (j+1)) (take (i - (j+1)) (drop (j+1) t)) (S t i)" 
    using \<open>j < i\<close> assms(1) exists_trace_for_any_i_j by fastforce
  have "~ regular_event (t ! j)" 
    using step_j \<open>\<not> ps (S t j) q \<noteq> None\<close> \<open>ps (S t (j + 1)) q \<noteq> None\<close> regular_event_cannot_induce_snapshot by blast
  then have "isSnapshot (t ! j) \<or> isRecvMarker (t ! j)" 
    using nonregular_event by auto
  then have "snd (cs (S t (j+1)) cid) \<noteq> NotStarted"
  proof (elim disjE, goal_cases)
    case 1
    have "occurs_on (t ! j) = q" 
      using \<open>\<not> ps (S t j) q \<noteq> None\<close> \<open>ps (S t (j + 1)) q \<noteq> None\<close> distributed_system.no_state_change_if_no_event distributed_system_axioms step_j by fastforce
    with 1 have "t ! j = Snapshot q" using isSnapshot_def by auto
    then show ?thesis using step_j assms by simp
  next
    case 2
    have "occurs_on (t ! j) = q" 
      using \<open>\<not> ps (S t j) q \<noteq> None\<close> \<open>ps (S t (j + 1)) q \<noteq> None\<close> distributed_system.no_state_change_if_no_event distributed_system_axioms step_j by fastforce
    with 2 obtain cid' s where RecvMarker: "t ! j = RecvMarker cid' q s"
      by (metis event.collapse(5))
    then show ?thesis
    proof (cases "cid' = cid")
      case True
      then show ?thesis using RecvMarker step_j assms by simp
    next
      case False
      have "~ has_snapshotted (S t j) q" 
        using \<open>\<not> ps (S t j) q \<noteq> None\<close> by auto
      moreover have "\<exists>r. channel cid = Some (r, q)" 
        by (simp add: assms(3))
      ultimately show ?thesis using RecvMarker step_j assms False by simp
    qed
  qed
  then have "snd (cs (S t i) cid) \<noteq> NotStarted"
    using tr_j_i cs_not_not_started_stable_trace assms by blast
  then show False using assms by simp
qed

lemma nonregular_event_in_initial_state_implies_cs_changed:
  assumes
    "trace init t final" and
    "snd (cs (S t i) cid) = NotStarted" and
    "~ regular_event (t ! i)" and
    "occurs_on (t ! i) = q" and
    "channel cid = Some (p, q)" and
    "i < length t"
  shows
    "snd (cs (S t (i+1)) cid) \<noteq> NotStarted"
proof -
  have step: "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (i+1))" using step_Suc assms by auto
  have "isSnapshot (t ! i) \<or> isRecvMarker (t ! i)" 
    using assms(3) nonregular_event by blast
  then show ?thesis
  proof (elim disjE, goal_cases)
    case 1
    then show ?thesis 
      using assms cs_in_initial_state_implies_not_snapshotted local.step nonregular_event_induces_snapshot by blast
  next
    case 2
    then show ?thesis 
      by (metis assms(1) assms(2) assms(3) assms(4) assms(5) cs_in_initial_state_implies_not_snapshotted local.step nonregular_event_induces_snapshot)
  qed
qed

lemma cs_recording_implies_snapshot:
  assumes
    "trace init t final" and
    "snd (cs (S t i) cid) = Recording" and
    "channel cid = Some (p, q)"
  shows
    "has_snapshotted (S t i) q"
proof (rule ccontr)
  assume "~ has_snapshotted (S t i) q"
  have "\<lbrakk> trace init t final; ~ has_snapshotted (S t i) p; channel cid = Some (p, q) \<rbrakk>
        \<Longrightarrow> snd (cs (S t i) cid) = NotStarted"
  proof (induct i)
    case 0
    then show ?case 
      using init_is_s_t_0 no_initial_channel_snapshot by auto
  next
    case (Suc n)
    have step: "(S t n) \<turnstile> (t ! n) \<mapsto> (S t (n+1))" 
      by (metis Suc.prems(2) Suc_eq_plus1 all_processes_snapshotted_in_final_state assms(1) distributed_system.step_Suc distributed_system_axioms final_is_s_t_len_t le_add1 not_less snapshot_stable_ver_3)
    have "snd (cs (S t n) cid) = NotStarted" 
      using Suc.hyps Suc.prems(2) assms snapshot_state_unchanged computation_axioms local.step by fastforce
    then show ?case 
      by (metis Suc.prems(1) \<open>\<not> ps (S t i) q \<noteq> None\<close> assms(2) assms(3) cs_not_not_started_stable_trace exists_trace_for_any_i no_recording_cs_if_not_snapshotted recording_state.simps(2))
  qed
  then show False 
    using \<open>\<not> ps (S t i) q \<noteq> None\<close> assms computation.no_initial_channel_snapshot computation_axioms no_recording_cs_if_not_snapshotted by fastforce
qed

lemma cs_done_implies_both_snapshotted:
  assumes
    "trace init t final" and
    "snd (cs (S t i) cid) = Done" and
    "i < length t" and
    "channel cid = Some (p, q)"
  shows
    "has_snapshotted (S t i) p"
    "has_snapshotted (S t i) q"
proof -
  have "trace init (take i t) (S t i)" 
    using assms(1) exists_trace_for_any_i by blast
  then have "RecvMarker cid q p : set (take i t)" 
    by (metis assms(1,2,4) cs_done_implies_has_snapshotted done_only_from_recv_marker_trace computation.no_initial_process_snapshot computation_axioms init_is_s_t_0 list.discI trace.simps)
  then obtain k where "t ! k = RecvMarker cid q p" "0 \<le> k" "k < i" 
    by (metis add.right_neutral add_diff_cancel_right' append_Nil append_take_drop_id assms(1) exists_index take0)
  then have "has_snapshotted (S t (k+1)) q" 
    by (metis (no_types, lifting) Suc_eq_plus1 Suc_leI assms(1,2,4) computation.cs_done_implies_has_snapshotted computation.no_change_if_ge_length_t computation_axioms less_le not_less_eq recv_marker_means_cs_Done)
  then show "has_snapshotted (S t i) q" 
    using assms cs_done_implies_has_snapshotted by blast
  have step_k: "(S t k) \<turnstile> (t ! k) \<mapsto> (S t (k+1))" 
    by (metis Suc_eq_plus1 \<open>k < i\<close> add_lessD1 assms(1) assms(3) distributed_system.step_Suc distributed_system_axioms less_imp_add_positive)
  then have "Marker : set (msgs (S t k) cid)"
  proof -
    have "can_occur (t ! k) (S t k)" using happen_implies_can_occur step_k by blast
    then show ?thesis unfolding can_occur_def \<open>t ! k = RecvMarker cid q p\<close> 
      using hd_in_set by fastforce
  qed
  then have "has_snapshotted (S t k) p" 
    using assms(1,4) no_marker_if_no_snapshot by blast
  then show "has_snapshotted (S t i) p" 
    using \<open>k < i\<close> assms(1) less_imp_le_nat snapshot_stable_ver_3 by blast
qed

lemma cs_done_implies_same_snapshots:
  assumes "trace init t final" "i \<le> j" "j \<le> length t"
  shows "snd (cs (S t i) cid) = Done \<Longrightarrow> channel cid = Some (p, q) \<Longrightarrow> cs (S t i) cid = cs (S t j) cid"
using assms proof (induct i j rule: S_induct)
  case (S_init i)
  then show ?case by auto
next
  case (S_step i j)
  have snap_p: "has_snapshotted (S t i) p" 
    using S_step.hyps(1) S_step.hyps(2) S_step.prems(1,2) assms(1) cs_done_implies_both_snapshotted(1) by auto
  have snap_q: "has_snapshotted (S t i) q" 
    using S_step.prems(1,2) assms(1) cs_done_implies_has_snapshotted by blast
  from S_step have "cs (S t i) cid = cs (S t (Suc i)) cid"
  proof (cases "t ! i")
    case (Snapshot r)
    from Snapshot S_step.hyps(3) snap_p have False if "r = p" using that by (auto simp: can_occur_def)
    moreover
    from Snapshot S_step.hyps(3) snap_q have False if "r = q" using that by (auto simp: can_occur_def)
    ultimately show ?thesis using Snapshot S_step by force
  next
    case (RecvMarker cid' r s)
    then show ?thesis
    proof (cases "has_snapshotted (S t i) r")
      case True
      with RecvMarker S_step show ?thesis
      proof (cases "cid = cid'")
        case True
        then have "cs (S t (Suc i)) cid = (fst (cs (S t i) cid), Done)"
          using RecvMarker S_step by simp
        then show ?thesis 
          by (metis S_step.prems(1) prod.collapse)
      qed auto
    next
      case no_snap: False
      then show ?thesis
      proof (cases "cid = cid'")
        case True
        then have "cs (S t (Suc i)) cid = (fst (cs (S t i) cid), Done)"
          using RecvMarker S_step by simp
        then show ?thesis 
          by (metis S_step.prems(1) prod.collapse)
      next
        case False
        then have "r \<noteq> p" using no_snap snap_p by auto
        moreover have "\<nexists>s. channel cid = Some (s, r)" 
          using S_step(5) assms(1) cs_done_implies_has_snapshotted no_snap by blast
        ultimately show ?thesis using RecvMarker S_step False no_snap by simp
      qed
    qed
  next
    case (Recv cid' r s u u' m)
    with S_step show ?thesis by (cases "cid = cid'", auto)
  qed auto
  with S_step show ?case by auto
qed

lemma snapshotted_and_not_done_implies_marker_in_channel:
  assumes
    "trace init t final" and
    "has_snapshotted (S t i) p" and
    "snd (cs (S t i) cid) \<noteq> Done" and
    "i \<le> length t" and
    "channel cid = Some (p, q)"
  shows
    "Marker : set (msgs (S t i) cid)"
proof -
  obtain j where jj: "j < i" "~ has_snapshotted (S t j) p" "has_snapshotted (S t (j+1)) p" 
    by (metis Suc_eq_plus1 assms(1) assms(2) exists_snapshot_for_all_p computation.snapshot_stable_ver_2 computation_axioms le_eq_less_or_eq nat_neq_iff)
  have step: "(S t j) \<turnstile> (t ! j) \<mapsto> (S t (j+1))" 
    by (metis \<open>\<not> ps (S t j) p \<noteq> None\<close> \<open>j < i\<close> add.commute assms(1) assms(2) linorder_neqE_nat no_change_if_ge_length_t order_le_less order_refl plus_1_eq_Suc step_Suc)
  then have "Marker : set (msgs (S t (j+1)) cid)"
  proof -
    have "~ regular_event (t ! j)" 
      by (meson \<open>\<not> ps (S t j) p \<noteq> None\<close> \<open>ps (S t (j + 1)) p \<noteq> None\<close> distributed_system.regular_event_cannot_induce_snapshot distributed_system_axioms local.step)
    then have "isSnapshot (t ! j) \<or> isRecvMarker (t ! j)" using nonregular_event by blast
    then show ?thesis
    proof (elim disjE, goal_cases)
      case 1
      then obtain r where Snapshot: "t ! j = Snapshot r" by (meson isSnapshot_def)
      then have "r = p" 
        using jj(2) jj(3) local.step by auto
      then show ?thesis using Snapshot assms step by simp
    next
      case 2
      then obtain cid' s where RecvMarker: "t ! j = RecvMarker cid' p s" 
        by (metis jj(2,3) distributed_system.no_state_change_if_no_event distributed_system_axioms event.sel(5) isRecvMarker_def local.step)
      moreover have "cid \<noteq> cid'"
      proof (rule ccontr)
        assume "~ cid \<noteq> cid'"
        then have "snd (cs (S t (j+1)) cid) = Done" using RecvMarker step by simp
        then have "snd (cs (S t i) cid) = Done" 
        proof -
          assume a1: "snd (cs (S t (j + 1)) cid) = Done"
          have f2: "ps (S t j) p = None"
            using jj(2) by blast
          have "j < length t"
            using assms(4) jj(1) by linarith
          then have "t ! j = RecvMarker cid q p"
            using f2 a1 assms(1) assms(5) cs_done_implies_both_snapshotted(1) done_only_from_recv_marker local.step by blast
          then show ?thesis
            using f2 by (metis (no_types) Suc_eq_plus1 assms(1) local.step recv_marker_means_snapshotted)
        qed
        then show False using assms by simp
      qed
      ultimately show ?thesis using jj assms step by auto
    qed
  qed
  show ?thesis
  proof (rule ccontr)
    let ?t = "take (i - (j+1)) (drop (j+1) t)"
    have tr_j: "trace (S t (j+1)) ?t (S t i)" 
      by (metis \<open>j < i\<close> assms(1) discrete exists_trace_for_any_i_j)
    assume "~ Marker : set (msgs (S t i) cid)"
    then obtain ev where "ev \<in> set ?t" "\<exists>p q. ev = RecvMarker cid p q" 
      using \<open>Marker \<in> set (msgs (S t (j + 1)) cid)\<close> marker_must_be_delivered_2_trace tr_j assms by blast
    obtain k where "t ! k = ev" "j < k" "k < i"
      using \<open>ev \<in> set (take (i - (j + 1)) (drop (j + 1) t))\<close> assms(1) exists_index by fastforce
    have step_k: "(S t k) \<turnstile> (t ! k) \<mapsto> (S t (k+1))"
    proof -
      have "k < length t" 
        using \<open>k < i\<close> assms(4) by auto
      then show ?thesis using step_Suc assms by simp
    qed
    have "ev = RecvMarker cid q p" using assms step_k can_occur_def 
      using \<open>\<exists>p q. ev = RecvMarker cid p q\<close> \<open>t ! k = ev\<close> by auto
    then have "snd (cs (S t (k+1)) cid) = Done" 
      using \<open>k < i\<close> \<open>t ! k = ev\<close> assms(1) assms(4) recv_marker_means_cs_Done by auto
    moreover have "trace (S t (k+1)) (take (i - (k+1)) (drop (k+1) t)) (S t i)" 
      by (meson \<open>k < i\<close> assms(1) discrete exists_trace_for_any_i_j)
    ultimately have "snd (cs (S t i) cid) = Done" 
      by (metis \<open>k < i\<close> assms(1) assms(4) assms(5) cs_done_implies_same_snapshots discrete)
    then show False using assms by simp
  qed
qed

lemma no_marker_left_in_final_state:
  assumes
    "trace init t final"
  shows
    "Marker \<notin> set (msgs final cid)" (is ?P)
proof (rule ccontr)
  assume "~ ?P"
  then obtain i where "i > length t" "Marker \<notin> set (msgs (S t i) cid)" using assms l1 
    by (metis final_is_s_t_len_t le_neq_implies_less)
  then have "S t (length t) \<noteq> S t i"
  proof -
    have "msgs (S t i) cid \<noteq> msgs final cid"
      using \<open>Marker \<notin> set (msgs (S t i) cid)\<close> \<open>~ ?P\<close> by auto
    then show ?thesis using final_is_s_t_len_t assms by auto
  qed
  moreover have "S t (length t) = S t i"
    using assms \<open>i > length t\<close> less_imp_le no_change_if_ge_length_t by simp
  ultimately show False by simp
qed

lemma all_channels_done_in_final_state:
  assumes
    "trace init t final" and
    "channel cid = Some (p, q)"
  shows
    "snd (cs final cid) = Done"
proof (rule ccontr)
  assume cs_not_done: "~ snd (cs final cid) = Done"
  obtain i where snap_p: "~ has_snapshotted (S t i) p" "has_snapshotted (S t (i+1)) p"
    by (metis Suc_eq_plus1 assms(1) exists_snapshot_for_all_p)
  have "i < length t"
  proof -
    have "S t i \<noteq> S t (i+1)" using snap_p by auto
    then show ?thesis 
      by (meson assms(1) computation.no_change_if_ge_length_t computation_axioms le_add1 not_less)
  qed
  let ?t = "take (length t - (i+1)) (drop (i+1) t)"
  have tr: "trace (S t (i+1)) ?t (S t (length t))" 
    by (meson \<open>i < length t\<close> assms(1) discrete exists_trace_for_any_i_j)
  have "Marker \<in> set (msgs (S t (i+1)) cid)"
  proof -
    have n_done: "snd (cs (S t (i+1)) cid) \<noteq> Done"
    proof (rule ccontr)
      assume "~ snd (cs (S t (i+1)) cid) \<noteq> Done"
      then have "snd (cs final cid) = Done" 
        by (metis Suc_eq_plus1 Suc_leI \<open>i < length t\<close> assms final_is_s_t_len_t computation.cs_done_implies_same_snapshots computation_axioms order_refl)
      then show False using cs_not_done by simp
    qed
    then show ?thesis using snapshotted_and_not_done_implies_marker_in_channel snap_p assms
    proof -
      have "i+1 \<le> length t" using \<open>i < length t\<close> by auto
      then show ?thesis
        using snapshotted_and_not_done_implies_marker_in_channel snap_p assms n_done by simp
    qed
  qed
  moreover have "Marker \<notin> set (msgs (S t (length t)) cid)" using final_is_s_t_len_t no_marker_left_in_final_state assms by blast
  ultimately have rm_prov: "\<exists>ev \<in> set ?t. (\<exists>q p. ev = RecvMarker cid q p)" using tr message_must_be_delivered_2_trace assms 
    by (simp add: marker_must_be_delivered_2_trace)
  then obtain k where "\<exists>q p. t ! k = RecvMarker cid q p" "i+1 \<le> k" "k < length t" 
    by (metis assms(1) exists_index)
  then have step: "(S t k) \<turnstile> (t ! k) \<mapsto> (S t (k+1))" 
    by (metis Suc_eq_plus1_left add.commute assms(1) step_Suc)
  then have RecvMarker: "t ! k = RecvMarker cid q p" 
    by (metis RecvMarker_given_channel \<open>\<exists>q p. t ! k = RecvMarker cid q p\<close> assms(2) event.disc(25) event.sel(10) happen_implies_can_occur)
  then have "snd (cs (S t (k+1)) cid) = Done" 
    using step \<open>k < length t\<close> assms(1) recv_marker_means_cs_Done by blast
  then have "snd (cs final cid) = Done" 
    using \<open>Marker \<notin> set (msgs (S t (length t)) cid)\<close> all_processes_snapshotted_in_final_state assms(1) assms(2) final_is_s_t_len_t snapshotted_and_not_done_implies_marker_in_channel by fastforce
  then show False using cs_not_done by simp
qed

lemma cs_NotStarted_implies_empty_cs:
  shows
    "\<lbrakk> trace init t final; channel cid = Some (p, q); i < length t; ~ has_snapshotted (S t i) q \<rbrakk>
     \<Longrightarrow> cs (S t i) cid = ([], NotStarted)"
  by (simp add: no_initial_channel_snapshot no_recording_cs_if_not_snapshotted)

lemma fst_changed_by_recv_recording_trace:
  assumes
    "i < j" and
    "j \<le> length t" and
    "trace init t final" and
    "fst (cs (S t i) cid) \<noteq> fst (cs (S t j) cid)" and
    "channel cid = Some (p, q)"
  shows
    "\<exists>k. i \<le> k \<and> k < j \<and> (\<exists>p q u u' m. t ! k = Recv cid q p u u' m) \<and> (snd (cs (S t k) cid) = Recording)" (is ?P)
proof (rule ccontr)
  assume "~ ?P"
  have "\<lbrakk> i < j; j \<le> length t; ~ ?P; trace init t final; channel cid = Some (p, q) \<rbrakk> \<Longrightarrow> fst (cs (S t i) cid) = fst (cs (S t j) cid)"
  proof (induct "j - i" arbitrary: i)
    case 0
    then show ?case by linarith
  next
    case (Suc n)
    then have step: "(S t i) \<turnstile> t ! i \<mapsto> (S t (Suc i))" 
      using step_Suc by auto
    then have "fst (cs (S t (Suc i)) cid) = fst (cs (S t i) cid)" 
      by (metis Suc.prems(1) Suc.prems(3) assms(5) fst_cs_changed_by_recv_recording le_eq_less_or_eq)
    also have "fst (cs (S t (Suc i)) cid) = fst (cs (S t j) cid)"
    proof -
      have "j - Suc i = n" using Suc by simp
      moreover have "~ (\<exists>k. (Suc i) \<le> k \<and> k < j \<and> (\<exists>p q u u' m. t ! k = Recv cid q p u u' m) \<and> (snd (cs (S t k) cid) = Recording))"
        using \<open>~ ?P\<close> Suc.prems(3) Suc_leD by blast
      ultimately show ?thesis using Suc by (metis Suc_lessI)
    qed
    finally show ?case by simp
  qed
  then show False using assms \<open>~ ?P\<close> by blast
qed

lemma cs_not_nil_implies_postrecording_event:
  assumes
    "trace init t final" and
    "fst (cs (S t i) cid) \<noteq> []" and
    "i \<le> length t" and
    "channel cid = Some (p, q)"
  shows
    "\<exists>j. j < i \<and> postrecording_event t j"
proof -
  have "fst (cs init cid) = []" using no_initial_channel_snapshot by auto
  then have diff_cs: "fst (cs (S t 0) cid) \<noteq> fst (cs (S t i) cid)" 
    using assms(1) assms(2) init_is_s_t_0 by auto
  moreover have "0 < i"
  proof (rule ccontr)
    assume "~ 0 < i"
    then have "0 = i" by auto
    then have "fst (cs (S t 0) cid) = fst (cs (S t i) cid)" 
      by blast
    then show False using diff_cs by simp
  qed
  ultimately obtain j where "j < i" and Recv: "\<exists>p q u u' m. t ! j = Recv cid q p u u' m" "snd (cs (S t j) cid) = Recording"
    using assms(1) assms(3) assms(4) fst_changed_by_recv_recording_trace by blast
  then have "has_snapshotted (S t j) q" 
    using assms(1) assms(4) cs_recording_implies_snapshot by blast
  moreover have "regular_event (t ! j)" using Recv by auto
  moreover have "occurs_on (t ! j) = q"
  proof -
    have "can_occur (t ! j) (S t j)" 
      by (meson Suc_le_eq \<open>j < i\<close> assms(1) assms(3) happen_implies_can_occur le_trans step_Suc)
    then show ?thesis using Recv Recv_given_channel assms(4) by force
  qed
  ultimately have "postrecording_event t j" unfolding postrecording_event using \<open>j < i\<close> assms(3) by simp
  then show ?thesis using \<open>j < i\<close> by auto
qed

subsubsection \<open>Relating process states\<close>

lemma snapshot_state_must_have_been_reached:
  assumes
    "trace init t final" and
    "ps final p = Some u" and
    "~ has_snapshotted (S t i) p" and
    "has_snapshotted (S t (i+1)) p" and
    "i < length t"
  shows
    "states (S t i) p = u"
proof (rule ccontr)
  assume "states (S t i) p \<noteq> u"
  then have "ps (S t (i+1)) p \<noteq> Some u" 
    using assms(1) assms(3) snapshot_state by force
  then have "ps final p \<noteq> Some u"
    by (metis One_nat_def Suc_leI add.right_neutral add_Suc_right assms(1) assms(3) assms(4) assms(5) final_is_s_t_len_t order_refl snapshot_state snapshot_state_unchanged_trace_2)
  then show False using assms by simp
qed

lemma ps_after_all_prerecording_events:
  assumes
    "trace init t final" and
    "\<forall>i'. i' \<ge> i \<longrightarrow> ~ prerecording_event t i'" and
    "\<forall>j'. j' < i \<longrightarrow> ~ postrecording_event t j'"
  shows
    "ps_equal_to_snapshot (S t i) final"
proof (unfold ps_equal_to_snapshot_def, rule allI)
  fix p
  show "Some (states (S t i) p) = ps final p"
  proof (rule ccontr)
    obtain s where "ps final p = Some s \<or> ps final p = None" by auto
    moreover assume "Some (states (S t i) p) \<noteq> ps final p"
    ultimately have "ps final p = None \<or> states (S t i) p \<noteq> s" by auto
    then show False
    proof (elim disjE)
      assume "ps final p = None"
      then show False 
        using assms all_processes_snapshotted_in_final_state by blast
    next
      assume st: "states (S t i) p \<noteq> s"
      then obtain j where "~ has_snapshotted (S t j) p \<and> has_snapshotted (S t (j+1)) p" 
        using Suc_eq_plus1 assms(1) exists_snapshot_for_all_p by presburger
      then show False
      proof (cases "has_snapshotted (S t i) p")
        case False
        then have "j \<ge> i"
          by (metis Suc_eq_plus1 \<open>\<not> ps (S t j) p \<noteq> None \<and> ps (S t (j + 1)) p \<noteq> None\<close> assms(1) not_less_eq_eq snapshot_stable_ver_3)

        let ?t = "take (j-i) (drop i t)"
        have "\<exists>ev. ev \<in> set ?t \<and> regular_event ev \<and> occurs_on ev = p"
        proof (rule ccontr)
          assume "~ (\<exists>ev. ev \<in> set ?t \<and> regular_event ev \<and> occurs_on ev = p)"
          moreover have "trace (S t i) ?t (S t j)" 
            using \<open>i \<le> j\<close> assms(1) exists_trace_for_any_i_j by blast
          ultimately have "states (S t j) p = states (S t i) p"
            using no_state_change_if_only_nonregular_events st by blast
          then show False 
            by (metis \<open>\<not> ps (S t j) p \<noteq> None \<and> ps (S t (j + 1)) p \<noteq> None\<close> \<open>ps final p = Some s \<or> ps final p = None\<close> assms(1) final_is_s_t_len_t computation.all_processes_snapshotted_in_final_state computation.snapshot_stable_ver_3 computation_axioms linorder_not_le snapshot_state_must_have_been_reached st)
        qed

        then obtain ev where "ev \<in> set ?t \<and> regular_event ev \<and> occurs_on ev = p"
          by blast
        then obtain k where t_ind: "0 \<le> k \<and> k < length ?t \<and> ev = ?t ! k"
          by (metis in_set_conv_nth not_le not_less_zero)
        moreover have "length ?t \<le> j - i" by simp
        ultimately have "?t ! k = (drop i t) ! k" 
          using less_le_trans nth_take by blast
        also have "... = t ! (k+i)" 
          by (metis \<open>ev \<in> set (take (j - i) (drop i t)) \<and> regular_event ev \<and> occurs_on ev = p\<close> add.commute drop_eq_Nil length_greater_0_conv length_pos_if_in_set nat_le_linear nth_drop take_eq_Nil)
        finally have "?t ! k = t ! (k+i)" by simp
        have "prerecording_event t (k+i)"
        proof -
          have "regular_event (?t ! k)" 
            using \<open>ev \<in> set (take (j - i) (drop i t)) \<and> regular_event ev \<and> occurs_on ev = p\<close> t_ind by blast
          moreover have "occurs_on (?t ! k) = p" 
            using \<open>ev \<in> set (take (j - i) (drop i t)) \<and> regular_event ev \<and> occurs_on ev = p\<close> t_ind by blast
          moreover have "~ has_snapshotted (S t (k+i)) p"
          proof -
            have "k+i \<le> j"
              using \<open>length (take (j - i) (drop i t)) \<le> j - i\<close> t_ind by linarith
            show ?thesis 
              using \<open>\<not> ps (S t j) p \<noteq> None \<and> ps (S t (j + 1)) p \<noteq> None\<close> \<open>k+i \<le> j\<close> assms(1) snapshot_stable_ver_3 by blast
          qed
          ultimately show ?thesis 
            using \<open>take (j - i) (drop i t) ! k = t ! (k + i)\<close> prerecording_event t_ind by auto
        qed

        then show False using assms by auto
      next
        case True

        have "j < i"
        proof (rule ccontr)
          assume "~ j < i"
          then have "j \<ge> i" by simp
          moreover have "~ has_snapshotted (S t j) p" 
            using \<open>\<not> ps (S t j) p \<noteq> None \<and> ps (S t (j + 1)) p \<noteq> None\<close> by blast
          moreover have "trace (S t i) (take (j - i) (drop i t)) (S t j)" 
            using assms(1) calculation(1) exists_trace_for_any_i_j by blast
          ultimately have "~ has_snapshotted (S t i) p" 
            using snapshot_stable by blast
          then show False using True by simp
        qed

        let ?t = "take (i-j) (drop j t)"
        have "\<exists>ev. ev \<in> set ?t \<and> regular_event ev \<and> occurs_on ev = p"
        proof (rule ccontr)
          assume "~ (\<exists>ev. ev \<in> set ?t \<and> regular_event ev \<and> occurs_on ev = p)"
          moreover have "trace (S t j) ?t (S t i)" 
            using \<open>j < i\<close> assms(1) exists_trace_for_any_i_j less_imp_le by blast
          ultimately have "states (S t j) p = states (S t i) p" 
            using no_state_change_if_only_nonregular_events by auto
          moreover have "states (S t j) p = s" 
            by (metis \<open>\<not> ps (S t j) p \<noteq> None \<and> ps (S t (j + 1)) p \<noteq> None\<close> \<open>ps final p = Some s \<or> ps final p = None\<close> assms(1) final_is_s_t_len_t computation.all_processes_snapshotted_in_final_state computation.snapshot_stable_ver_3 computation_axioms linorder_not_le snapshot_state_must_have_been_reached)
          ultimately show False using \<open>states (S t i) p \<noteq> s\<close> by simp
        qed

        then obtain ev where ev: "ev \<in> set ?t \<and> regular_event ev \<and> occurs_on ev = p" by blast
        then obtain k where t_ind: "0 \<le> k \<and> k < length ?t \<and> ev = ?t ! k" 
          by (metis in_set_conv_nth le0)
        have "length ?t \<le> i - j" by simp
        have "?t ! k = (drop j t) ! k" 
          using t_ind by auto
        also have "... = t ! (k + j)" 
          by (metis \<open>ev \<in> set (take (i - j) (drop j t)) \<and> regular_event ev \<and> occurs_on ev = p\<close> add.commute drop_eq_Nil length_greater_0_conv length_pos_if_in_set nat_le_linear nth_drop take_eq_Nil)
        finally have "?t ! k = t ! (k+j)" by simp
        have "postrecording_event t (k+j)"
        proof -
          have "trace (S t j) (take k (drop j t)) (S t (k+j))" 
            by (metis add_diff_cancel_right' assms(1) exists_trace_for_any_i_j le_add_same_cancel2 t_ind)
          then have "has_snapshotted (S t (k+j)) p"
            by (metis Suc_eq_plus1 Suc_leI \<open>\<not> ps (S t j) p \<noteq> None \<and> ps (S t (j + 1)) p \<noteq> None\<close> \<open>take (i - j) (drop j t) ! k = t ! (k + j)\<close> assms(1) drop_eq_Nil ev computation.snapshot_stable_ver_3 computation_axioms le_add_same_cancel2 length_greater_0_conv length_pos_if_in_set linorder_not_le order_le_less regular_event_preserves_process_snapshots step_Suc t_ind take_eq_Nil)
          then show ?thesis 
            using \<open>take (i - j) (drop j t) ! k = t ! (k + j)\<close> ev postrecording_event t_ind by auto
        qed
        moreover have "k + j < i" 
          using \<open>length (take (i - j) (drop j t)) \<le> i - j\<close> t_ind by linarith
        ultimately show False using assms(3) by simp
      qed
    qed
  qed
qed

subsubsection \<open>Relating channel states\<close>

lemma cs_when_recording:
  shows
    "\<lbrakk> i < j; j \<le> length t; trace init t final;
       has_snapshotted (S t i) p;
       snd (cs (S t i) cid) = Recording;
       snd (cs (S t j) cid) = Done;
       channel cid = Some (p, q) \<rbrakk>
     \<Longrightarrow> map Msg (fst (cs (S t j) cid))
         = map Msg (fst (cs (S t i) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t i) cid)"
proof (induct "j - (i+1)" arbitrary: i)
  case 0
  then have "j = i+1" by simp
  then have step: "(S t i) \<turnstile> (t ! i) \<mapsto> (S t j)" using "0.prems" step_Suc by simp
  then have rm: "\<exists>q p. t ! i = RecvMarker cid q p" using done_only_from_recv_marker "0.prems" by force
  then have RecvMarker: "t ! i = RecvMarker cid q p"
    by (metis "0.prems"(7) RecvMarker_given_channel event.collapse(5) event.disc(25) event.inject(5) happen_implies_can_occur local.step)
  then have "takeWhile ((\<noteq>) Marker) (msgs (S t i) cid) = []"
  proof -
    have "can_occur (t ! i) (S t i)" using happen_implies_can_occur step by simp
    then show ?thesis
    proof -
      have "\<And>p ms. takeWhile p ms = [] \<or> p (hd ms::'c message)"
        by (metis (no_types) hd_append2 hd_in_set set_takeWhileD takeWhile_dropWhile_id)
      then show ?thesis
        using \<open>can_occur (t ! i) (S t i)\<close> can_occur_def rm by fastforce
    qed
  qed
  then show ?case 
    using local.step rm by auto
next
  case (Suc n)
  then have step: "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (i+1))" 
    by (metis Suc_eq_plus1 less_SucI nat_induct_at_least step_Suc)
  have ib: "i+1 < j \<and> j \<le> length t \<and> has_snapshotted (S t (i+1)) p \<and> snd (cs (S t j) cid) = Done"
    using Suc.hyps(2) Suc.prems(2) Suc.prems(4) Suc.prems(6) local.step snapshot_state_unchanged by auto
  have snap_q: "has_snapshotted (S t i) q" 
    using Suc(7) Suc.prems(3) Suc cs_recording_implies_snapshot by blast
  then show ?case
  proof (cases "t ! i")
    case (Snapshot r)
    then have "r \<noteq> p" 
      using Suc.prems(4) can_occur_def local.step by auto
    then have "msgs (S t (i+1)) cid = msgs (S t i) cid" 
      using Snapshot local.step Suc.prems(7) by auto
    moreover have "cs (S t (i+1)) cid = cs (S t i) cid"
    proof -
      have "r \<noteq> q" using Snapshot can_occur_def snap_q step by auto
      then show ?thesis using Snapshot local.step Suc.prems(7) by auto
    qed
    ultimately show ?thesis using Suc ib by force
  next
    case (RecvMarker cid' r s)
    then show ?thesis
    proof (cases "cid = cid'")
      case True
      then have "takeWhile ((\<noteq>) Marker) (msgs (S t i) cid) = []"
      proof -
        have "can_occur (t ! i) (S t i)" using happen_implies_can_occur step by simp
        then show ?thesis
        proof -
          have "\<And>p ms. takeWhile p ms = [] \<or> p (hd ms::'c message)"
            by (metis (no_types) hd_append2 hd_in_set set_takeWhileD takeWhile_dropWhile_id)
          then show ?thesis
            using RecvMarker True \<open>can_occur (t ! i) (S t i)\<close> can_occur_def by fastforce
        qed
      qed
      moreover have "snd (cs (S t (i+1)) cid) = Done" 
        using RecvMarker Suc.prems(1) Suc.prems(2) Suc.prems(3) True recv_marker_means_cs_Done by auto
      moreover have "fst (cs (S t i) cid) = fst (cs (S t (i+1)) cid)" 
        using RecvMarker True local.step by auto
      ultimately show ?thesis 
        by (metis Suc.prems(1) Suc.prems(2) Suc.prems(3) Suc.prems(7) Suc_eq_plus1 Suc_leI append_Nil2 cs_done_implies_same_snapshots)
    next
      case False
      then have "msgs (S t i) cid = msgs (S t (i+1)) cid"
      proof (cases "has_snapshotted (S t i) r")
        case True
        then show ?thesis using RecvMarker step Suc False by auto
      next
        case False
        with RecvMarker step Suc \<open>cid \<noteq> cid'\<close> show ?thesis by (cases "s = p", auto)
      qed
      moreover have "cs (S t i) cid = cs (S t (i+1)) cid"
      proof (cases "has_snapshotted (S t i) r")
        case True
        then show ?thesis using RecvMarker step Suc False by auto
      next
        case no_snap: False
        then show ?thesis
        proof (cases "r = q")
          case True
          then show ?thesis using snap_q no_snap \<open>r = q\<close> by simp
        next
          case False
          then show ?thesis using RecvMarker step Suc no_snap False \<open>cid \<noteq> cid'\<close> by simp
        qed
      qed
      ultimately show ?thesis using Suc ib by simp
    qed
  next
    case (Trans r u u')
    then have "msgs (S t i) cid = msgs (S t (i+1)) cid" using step by auto
    moreover have "cs (S t i) cid = cs (S t (i+1)) cid" using step Trans by auto
    ultimately show ?thesis using Suc ib by simp
  next
    case (Send cid' r s u u' m)
    then show ?thesis
    proof (cases "cid = cid'")
      case True
      have marker_in_msgs: "Marker \<in> set (msgs (S t i) cid)"
      proof -
        have "has_snapshotted (S t i) p" using Suc by simp
        moreover have "i < length t" 
          using Suc.prems(1) Suc.prems(2) less_le_trans by blast
        moreover have "snd (cs (S t i) cid) \<noteq> Done" using Suc by simp
        ultimately show ?thesis using snapshotted_and_not_done_implies_marker_in_channel less_imp_le using Suc by blast
      qed
      then have "takeWhile ((\<noteq>) Marker) (msgs (S t i) cid) = takeWhile ((\<noteq>) Marker) (msgs (S t (i+1)) cid)"
      proof -
        have "butlast (msgs (S t (i+1)) cid) = msgs (S t i) cid" using step True Send by auto
        then show ?thesis
        proof -
          have "takeWhile ((\<noteq>) Marker) (msgs (S t i) cid @ [last (msgs (S t (i + 1)) cid)]) = takeWhile ((\<noteq>) Marker) (msgs (S t i) cid)"
            using marker_in_msgs by force
          then show ?thesis
            by (metis (no_types) \<open>butlast (msgs (S t (i + 1)) cid) = msgs (S t i) cid\<close> append_butlast_last_id in_set_butlastD length_greater_0_conv length_pos_if_in_set marker_in_msgs)
        qed
      qed
      moreover have "cs (S t i) cid = cs (S t (i+1)) cid" using step Send by auto
      ultimately show ?thesis using ib Suc by simp
    next
      case False
      then have "msgs (S t i) cid = msgs (S t (i+1)) cid" using step Send by auto
      moreover have "cs (S t i) cid = cs (S t (i+1)) cid" using step Send by auto
      ultimately show ?thesis using Suc ib by simp
    qed
  next
    case (Recv cid' r s u u' m)
    then show ?thesis
    proof (cases "cid = cid'")
      case True
      then have msgs_ip1: "Msg m # msgs (S t (i+1)) cid = msgs (S t i) cid"
        using Suc Recv step by auto
      moreover have cs_ip1: "cs (S t (i+1)) cid = (fst (cs (S t i) cid) @ [m], Recording)"
        using True Suc Recv step by auto
      ultimately show ?thesis
      proof -
        have "map Msg (fst (cs (S t j) cid))
            = map Msg (fst (cs (S t (i+1)) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t (i+1)) cid)"
          using Suc ib cs_ip1 by force
        moreover have "map Msg (fst (cs (S t i) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t i) cid)
                     = map Msg (fst (cs (S t (i+1)) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t (i+1)) cid)"
        proof -
          have "takeWhile ((\<noteq>) Marker) (Msg m # msgs (S t (i+1)) cid) = Msg m # takeWhile ((\<noteq>) Marker) (msgs (S t (i + 1)) cid)"
            by auto
          then have "takeWhile ((\<noteq>) Marker) (msgs (S t i) cid) = Msg m # takeWhile ((\<noteq>) Marker) (msgs (S t (i + 1)) cid)"
            by (metis msgs_ip1)
          then show ?thesis
            using cs_ip1 by auto
        qed
        ultimately show ?thesis by simp
      qed
    next
      case False
      then have "msgs (S t i) cid = msgs (S t (i+1)) cid" using step Recv by auto
      moreover have "cs (S t i) cid = cs (S t (i+1)) cid" using step Recv False by auto
      ultimately show ?thesis using Suc ib by simp
    qed
  qed
qed

lemma cs_when_recording_2:
  shows
    "\<lbrakk> i \<le> j; trace init t final;
       ~ has_snapshotted (S t i) p;
       \<forall>k. i \<le> k \<and> k < j \<longrightarrow> ~ occurs_on (t ! k) = p;
       snd (cs (S t i) cid) = Recording;
       channel cid = Some (p, q) \<rbrakk>
     \<Longrightarrow> map Msg (fst (cs (S t j) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t j) cid)
         = map Msg (fst (cs (S t i) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t i) cid)
         \<and> snd (cs (S t j) cid) = Recording"
proof (induct "j - i" arbitrary: i)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have step: "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (i+1))" 
    by (metis Suc_eq_plus1 all_processes_snapshotted_in_final_state distributed_system.step_Suc distributed_system_axioms computation.final_is_s_t_len_t computation_axioms linorder_not_le snapshot_stable_ver_3)
  have ib: "i+1 \<le> j \<and> ~ has_snapshotted (S t (i+1)) p
         \<and> (\<forall>k. (i+1) \<le> k \<and> k < j \<longrightarrow> ~ occurs_on (t ! k) = p) \<and> j - (i+1) = n" 
    by (metis Suc.hyps(2) Suc.prems(1) Suc.prems(3) Suc.prems(4) diff_Suc_1 diff_diff_left Suc_eq_plus1 Suc_leD Suc_le_eq Suc_neq_Zero cancel_comm_monoid_add_class.diff_cancel le_neq_implies_less le_refl local.step no_state_change_if_no_event)
  have snap_q: "has_snapshotted (S t i) q" 
    using Suc.prems(5,6) Suc.prems(2) cs_recording_implies_snapshot by blast
  then show ?case
  proof (cases "t ! i")
    case (Snapshot r)
    then have "r \<noteq> p" using Suc by auto
    then have "msgs (S t (i+1)) cid = msgs (S t i) cid" 
      using Snapshot local.step Suc.prems(6) by auto
    moreover have "cs (S t (i+1)) cid = cs (S t i) cid"
    proof -
      have "r \<noteq> q" using step can_occur_def Snapshot snap_q by auto
      then show ?thesis using Snapshot step Suc by simp
    qed
    ultimately show ?thesis using Suc ib by auto
  next
    case (RecvMarker cid' r s)
    then show ?thesis
    proof (cases "cid = cid'")
      case True
      then have "Marker \<in> set (msgs (S t i) cid)" 
        using RecvMarker RecvMarker_implies_Marker_in_set local.step by blast
      then have "has_snapshotted (S t i) p" 
        using Suc.prems(2) no_marker_if_no_snapshot Suc by blast
      then show ?thesis using Suc.prems by simp
    next
      case False
      then have "msgs (S t i) cid = msgs (S t (i+1)) cid"
      proof (cases "has_snapshotted (S t i) r")
        case True
        then show ?thesis using RecvMarker step Suc False by auto
      next
        case False
        with RecvMarker step Suc \<open>cid \<noteq> cid'\<close> show ?thesis by (cases "s = p", auto)
      qed
      moreover have "cs (S t i) cid = cs (S t (i+1)) cid"
      proof (cases "has_snapshotted (S t i) r")
        case True
        then show ?thesis using RecvMarker step Suc False by auto
      next
        case no_snap: False
        then show ?thesis
        proof (cases "r = q")
          case True
          then show ?thesis using snap_q no_snap \<open>r = q\<close> by simp
        next
          case False
          then show ?thesis using RecvMarker step Suc no_snap False \<open>cid \<noteq> cid'\<close> by simp
        qed
      qed
      ultimately show ?thesis using Suc ib by auto
    qed
  next
    case (Trans r u u')
    then have "msgs (S t i) cid = msgs (S t (i+1)) cid" using step by auto
    moreover have "cs (S t i) cid = cs (S t (i+1)) cid" using step Trans by auto
    ultimately show ?thesis using Suc ib by auto
  next
    case (Send cid' r s u u' m)
    then have "r \<noteq> p" 
      using Suc.hyps(2) Suc.prems(4) Suc by auto
    have "cid \<noteq> cid'"
    proof (rule ccontr)
      assume "~ cid \<noteq> cid'"
      then have "channel cid = channel cid'" by auto
      then have "(p, q) = (r, s)" using can_occur_def step Send Suc by auto
      then show False using \<open>r \<noteq> p\<close> by simp
    qed
    then have "msgs (S t i) cid = msgs (S t (i+1)) cid" using step Send by simp
    moreover have "cs (S t i) cid = cs (S t (i+1)) cid" using step Send by auto
    ultimately show ?thesis using Suc ib by auto
  next
    case (Recv cid' r s u u' m)
    then show ?thesis
    proof (cases "cid = cid'")
      case True
      then have msgs_ip1: "Msg m # msgs (S t (i+1)) cid = msgs (S t i) cid"
        using Suc Recv step by auto
      moreover have cs_ip1: "cs (S t (i+1)) cid = (fst (cs (S t i) cid) @ [m], Recording)"
        using True Suc Recv step by auto
      ultimately show ?thesis
      proof -
        have "map Msg (fst (cs (S t j) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t j) cid)
            = map Msg (fst (cs (S t (i+1)) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t (i+1)) cid)
            \<and> snd (cs (S t j) cid) = Recording"
          using Suc ib cs_ip1 by auto
        moreover have "map Msg (fst (cs (S t i) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t i) cid)
                     = map Msg (fst (cs (S t (i+1)) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t (i+1)) cid)"
        proof -
          have "takeWhile ((\<noteq>) Marker) (Msg m # msgs (S t (i + 1)) cid) = Msg m # takeWhile ((\<noteq>) Marker) (msgs (S t (i + 1)) cid)"
            by fastforce
          then have "takeWhile ((\<noteq>) Marker) (msgs (S t i) cid) = Msg m # takeWhile ((\<noteq>) Marker) (msgs (S t (i + 1)) cid)"
            by (metis msgs_ip1)
          then show ?thesis
            using cs_ip1 by force
        qed
        ultimately show ?thesis using cs_ip1 by simp
      qed
    next
      case False
      then have "msgs (S t i) cid = msgs (S t (i+1)) cid" using step Recv by auto
      moreover have "cs (S t i) cid = cs (S t (i+1)) cid" using step Recv False by auto
      ultimately show ?thesis using Suc ib by auto
    qed
  qed
qed

lemma cs_when_recording_3:
  shows
    "\<lbrakk> i \<le> j; trace init t final;
       ~ has_snapshotted (S t i) q;
       \<forall>k. i \<le> k \<and> k < j \<longrightarrow> ~ occurs_on (t ! k) = q;
       snd (cs (S t i) cid) = NotStarted;
       has_snapshotted (S t i) p;
       Marker : set (msgs (S t i) cid);
       channel cid = Some (p, q) \<rbrakk>
     \<Longrightarrow> map Msg (fst (cs (S t j) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t j) cid)
         = map Msg (fst (cs (S t i) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t i) cid)
         \<and> snd (cs (S t j) cid) = NotStarted"
proof (induct "j - i" arbitrary: i)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have step: "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (i+1))" 
    by (metis Suc_eq_plus1 all_processes_snapshotted_in_final_state distributed_system.step_Suc distributed_system_axioms computation.final_is_s_t_len_t computation_axioms linorder_not_le snapshot_stable_ver_3)
  have ib: "i+1 \<le> j \<and> ~ has_snapshotted (S t (i+1)) q \<and> has_snapshotted (S t (i+1)) p
         \<and> (\<forall>k. (i+1) \<le> k \<and> k < j \<longrightarrow> ~ occurs_on (t ! k) = q) \<and> j - (i+1) = n
         \<and> Marker : set (msgs (S t (i+1)) cid) \<and> cs (S t i) cid = cs (S t (i+1)) cid" 
  proof -
    have "i+1 \<le> j \<and> ~ has_snapshotted (S t (i+1)) q
         \<and> (\<forall>k. (i+1) \<le> k \<and> k < j \<longrightarrow> ~ occurs_on (t ! k) = q) \<and> j - (i+1) = n" 
      by (metis Suc.hyps(2) Suc.prems(1) Suc.prems(3) Suc.prems(4) diff_Suc_1 diff_diff_left Suc_eq_plus1 Suc_leD Suc_le_eq Suc_neq_Zero cancel_comm_monoid_add_class.diff_cancel le_neq_implies_less le_refl local.step no_state_change_if_no_event)
    moreover have "has_snapshotted (S t (i+1)) p" 
      using Suc.prems(6) local.step snapshot_state_unchanged by auto
    moreover have "Marker : set (msgs (S t (i+1)) cid)" 
      using Suc calculation(1) local.step recv_marker_means_snapshotted_2 by blast
    moreover have "cs (S t i) cid = cs (S t (i+1)) cid" 
      using Suc calculation(1) no_recording_cs_if_not_snapshotted by auto
    ultimately show ?thesis by simp
  qed
  then show ?case
  proof (cases "t ! i")
    case (Snapshot r)
    then have "r \<noteq> q" using Suc by auto
    then have "takeWhile ((\<noteq>) Marker) (msgs (S t (i+1)) cid) = takeWhile ((\<noteq>) Marker) (msgs (S t i) cid)" 
    proof (cases "occurs_on (t ! i) = p")
      case True
      then show ?thesis
        by (metis (mono_tags, lifting) Snapshot Suc.prems(6) distributed_system.can_occur_def event.sel(4) event.simps(29) computation_axioms computation_def happen_implies_can_occur local.step)
    next
      case False
      then have "msgs (S t (i+1)) cid = msgs (S t i) cid" 
        using Snapshot local.step Suc by auto
      then show ?thesis by simp
    qed
    then show ?thesis using Suc ib by metis
  next
    case (RecvMarker cid' r s)
    then show ?thesis
    proof (cases "cid = cid'")
      case True
      then have "snd (cs (S t i) cid) = Done"
        by (metis RecvMarker Suc.prems(2) Suc_eq_plus1 Suc_le_eq exactly_one_snapshot computation.no_change_if_ge_length_t computation.recv_marker_means_cs_Done computation.snapshot_stable_ver_2 computation_axioms ib nat_le_linear)
      then show ?thesis using Suc.prems by simp
    next
      case False
      then have "takeWhile ((\<noteq>) Marker) (msgs (S t i) cid) = takeWhile ((\<noteq>) Marker) (msgs (S t (i+1)) cid)"
      proof (cases "has_snapshotted (S t i) r")
        case True
        with RecvMarker False step show ?thesis by auto
      next
        case no_snap: False
        then have "r \<noteq> p" 
          using Suc.prems(6) by auto
        then show ?thesis using no_snap RecvMarker step Suc.prems False by auto
      qed
      then show ?thesis using Suc ib by metis
    qed
  next
    case (Trans r u u')
    then have "msgs (S t i) cid = msgs (S t (i+1)) cid" using step by auto
    then show ?thesis using Suc ib by auto
  next
    case (Send cid' r s u u' m)
    then have "r \<noteq> q" 
      using Suc.hyps(2) Suc.prems(4) by auto
    have marker: "Marker \<in> set (msgs (S t i) cid)" using Suc by simp
    with step Send marker have "takeWhile ((\<noteq>) Marker) (msgs (S t i) cid) = takeWhile ((\<noteq>) Marker) (msgs (S t (i+1)) cid)"
      by (cases "cid = cid'", auto)
    then show ?thesis using Suc ib by auto
  next
    case (Recv cid' r s u u' m)
    then have "cid' \<noteq> cid" 
      by (metis Suc.hyps(2) Suc.prems(4) Suc.prems(8) distributed_system.can_occur_Recv distributed_system_axioms event.sel(3) happen_implies_can_occur local.step option.inject order_refl prod.inject zero_less_Suc zero_less_diff)
    then have "msgs (S t i) cid = msgs (S t (i+1)) cid" using step Recv Suc by simp
    then show ?thesis using Suc ib by auto
  qed
qed

lemma at_most_one_marker:
  shows
    "\<lbrakk> trace init t final; channel cid = Some (p, q) \<rbrakk>
     \<Longrightarrow> Marker \<notin> set (msgs (S t i) cid)
       \<or> (\<exists>!j. j < length (msgs (S t i) cid) \<and> msgs (S t i) cid ! j = Marker)"
proof (induct i)
  case 0
  then show ?case using no_initial_Marker init_is_s_t_0 by auto
next
  case (Suc i)
  then show ?case
  proof (cases "i < length t")
    case False
    then show ?thesis 
      by (metis Suc.prems(1) final_is_s_t_len_t computation.no_change_if_ge_length_t computation_axioms le_refl less_imp_le_nat no_marker_left_in_final_state not_less_eq)
  next
    case True
    then have step: "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (Suc i))" using step_Suc Suc.prems by blast
    moreover have "Marker \<notin> set (msgs (S t i) cid)
                \<or> (\<exists>!j. j < length (msgs (S t i) cid) \<and> msgs (S t i) cid ! j = Marker)"
      using Suc.hyps Suc.prems(1) Suc.prems(2) by linarith
    moreover have "Marker \<notin> set (msgs (S t (Suc i)) cid)
                \<or> (\<exists>!j. j < length (msgs (S t (Suc i)) cid) \<and> msgs (S t (Suc i)) cid ! j = Marker)"
    proof (cases "Marker \<notin> set (msgs (S t i) cid)")
      case no_marker: True
      then show ?thesis
      proof (cases "t ! i")
        case (Snapshot r)
        then show ?thesis
        proof (cases "r = p")
          case True
          then have new_msgs: "msgs (S t (Suc i)) cid = msgs (S t i) cid @ [Marker]"
            using step Snapshot Suc by auto
          then show ?thesis using util_exactly_one_element no_marker by fastforce
        next
          case False
          then show ?thesis 
            using Snapshot local.step no_marker Suc by auto
        qed
      next
        case (RecvMarker cid' r s)
        then show ?thesis
        proof (cases "cid = cid'")
          case True
          then show ?thesis 
            using RecvMarker RecvMarker_implies_Marker_in_set local.step no_marker by blast
        next
          case False
          then show ?thesis
          proof (cases "has_snapshotted (S t i) r")
            case True
            then show ?thesis using RecvMarker step Suc False by simp
          next
            case no_snap: False
            then show ?thesis
            proof (cases "r = p")
              case True
              then have "msgs (S t (i+1)) cid = msgs (S t i) cid @ [Marker]" using RecvMarker step Suc.prems no_snap \<open>cid \<noteq> cid'\<close> by simp
              then show ?thesis
              proof -
                assume a1: "msgs (S t (i + 1)) cid = msgs (S t i) cid @ [Marker]"
                { fix nn :: "nat \<Rightarrow> nat"
                  have "\<forall>ms m. \<exists>n. \<forall>na. ((m::'c message) \<in> set ms \<or> n < length (ms @ [m])) \<and> (m \<in> set ms \<or> (ms @ [m]) ! n = m) \<and> (\<not> na < length (ms @ [m]) \<or> (ms @ [m]) ! na \<noteq> m \<or> m \<in> set ms \<or> na = n)"
                    by (metis (no_types) util_exactly_one_element)
                  then have "\<exists>n. n < length (msgs (S t (Suc i)) cid) \<and> nn n = n \<and> msgs (S t (Suc i)) cid ! n = Marker \<or> n < length (msgs (S t (Suc i)) cid) \<and> msgs (S t (Suc i)) cid ! n = Marker \<and> \<not> nn n < length (msgs (S t (Suc i)) cid) \<or> n < length (msgs (S t (Suc i)) cid) \<and> msgs (S t (Suc i)) cid ! n = Marker \<and> msgs (S t (Suc i)) cid ! nn n \<noteq> Marker"
                    using a1 by (metis Suc_eq_plus1 no_marker) }
                then show ?thesis
                  by (metis (no_types))
              qed
            next
              case False
              then have "msgs (S t i) cid = msgs (S t (i+1)) cid" using RecvMarker step Suc.prems \<open>cid \<noteq> cid'\<close> no_snap by simp
              then show ?thesis using Suc by simp
            qed
          qed
        qed
      next
        case (Trans r u u')
        then show ?thesis using no_marker step by auto
      next
        case (Send cid' r s u u' m)
        then show ?thesis
        proof (cases "cid = cid'")
          case True
          then have "Marker \<notin> set (msgs (S t (Suc i)) cid)" using step no_marker Send by auto
          then show ?thesis by simp
        next
          case False
          then have "Marker \<notin> set (msgs (S t (Suc i)) cid)" using step no_marker Send by auto
          then show ?thesis by simp
        qed
      next
        case (Recv cid' r s u u' m)
        with step no_marker Recv show ?thesis by (cases "cid = cid'", auto)
      qed
    next
      case False
      then have asm: "\<exists>!j. j < length (msgs (S t i) cid) \<and> msgs (S t i) cid ! j = Marker"
        using Suc by simp
      have len_filter: "length (filter ((=) Marker) (msgs (S t i) cid)) = 1" 
        by (metis False \<open>Marker \<notin> set (msgs (S t i) cid) \<or> (\<exists>!j. j < length (msgs (S t i) cid) \<and> msgs (S t i) cid ! j = Marker)\<close> exists_one_iff_filter_one)
      have snap_p: "has_snapshotted (S t i) p" 
        using False Suc.prems no_marker_if_no_snapshot by blast
      show ?thesis
      proof (cases "t ! i")
        case (Snapshot r)
        have "r \<noteq> p"
        proof (rule ccontr)
          assume "~ r \<noteq> p"
          moreover have "can_occur (t ! i) (S t i)" using happen_implies_can_occur step by blast
          ultimately show False using snap_p can_occur_def Snapshot by auto
        qed
        then have "msgs (S t (Suc i)) cid = msgs (S t i) cid" using step Snapshot Suc by auto
        then show ?thesis using asm by simp
      next
        case (RecvMarker cid' r s)
        then show ?thesis
        proof (cases "cid = cid'")
          case True
          then have "Marker # msgs (S t (Suc i)) cid = msgs (S t i) cid"
            using RecvMarker step by auto
          then have "Marker \<notin> set (msgs (S t (Suc i)) cid)"
          proof -
            have "\<forall>j. j \<noteq> 0 \<and> j < length (msgs (S t i) cid) \<longrightarrow> msgs (S t i) cid ! j \<noteq> Marker" 
              by (metis False \<open>Marker # msgs (S t (Suc i)) cid = msgs (S t i) cid\<close> asm length_pos_if_in_set nth_Cons_0)
            then show ?thesis 
            proof -
              assume a1: "\<forall>j. j \<noteq> 0 \<and> j < length (msgs (S t i) cid) \<longrightarrow> msgs (S t i) cid ! j \<noteq> Marker"
              have "\<And>ms n. ms \<noteq> msgs (S t i) cid \<or> length (msgs (S t (Suc i)) cid) \<noteq> n \<or> length ms = Suc n"
                by (metis \<open>Marker # msgs (S t (Suc i)) cid = msgs (S t i) cid\<close> length_Suc_conv)
              then show ?thesis
                using a1 by (metis (no_types) Suc_mono Zero_not_Suc \<open>Marker # msgs (S t (Suc i)) cid = msgs (S t i) cid\<close> in_set_conv_nth nth_Cons_Suc)
            qed
          qed
          then show ?thesis by simp
        next
          case cid_neq_cid': False
          then show ?thesis
          proof (cases "has_snapshotted (S t i) r")
            case True
            then have "msgs (S t (Suc i)) cid = msgs (S t i) cid" 
              using cid_neq_cid' RecvMarker local.step snap_p by auto
            then show ?thesis using asm by simp
          next
            case False
            then have "r \<noteq> p" 
              using snap_p by blast
            then have "msgs (S t (Suc i)) cid = msgs (S t i) cid" using cid_neq_cid' RecvMarker step False Suc by auto
            then show ?thesis using asm by simp
          qed
        qed
      next
        case (Trans r u u')
        then show ?thesis using step asm by auto
      next
        case (Send cid' r s u u' m)
        then show ?thesis
        proof (cases "cid = cid'")
          case True
          then have new_messages: "msgs (S t (Suc i)) cid = msgs (S t i) cid @ [Msg m]"
            using step Send by auto
          then have "\<exists>!j. j < length (msgs (S t (Suc i)) cid) \<and> msgs (S t (Suc i)) cid ! j = Marker"
          proof -
            have "length (filter ((=) Marker) (msgs (S t (Suc i)) cid))
                = length (filter ((=) Marker) (msgs (S t i) cid))
                + length (filter ((=) Marker) [Msg m])" 
              by (simp add: new_messages)
            then have "length (filter ((=) Marker) (msgs (S t (Suc i)) cid)) = 1"
              using len_filter by simp
            then show ?thesis using exists_one_iff_filter_one by metis
          qed
          then show ?thesis by simp
        next
          case False
          then show ?thesis using step Send asm by auto
        qed
      next
        case (Recv cid' r s u u' m)
       then show ?thesis
        proof (cases "cid = cid'")
          case True
          then have new_msgs: "Msg m # msgs (S t (Suc i)) cid = msgs (S t i) cid" using step Recv by auto
          then show ?thesis
          proof -
            have "length (filter ((=) Marker) (msgs (S t i) cid))
                = length (filter ((=) Marker) [Msg m])
                + length (filter ((=) Marker) (msgs (S t (Suc i)) cid))" 
              by (metis append_Cons append_Nil filter_append len_filter length_append new_msgs)
            then have "length (filter ((=) Marker) (msgs (S t (Suc i)) cid)) = 1"
              using len_filter by simp
            then show ?thesis using exists_one_iff_filter_one by metis
          qed
        next
          case False
          then show ?thesis using step Recv asm by auto
        qed
      qed
    qed
    then show ?thesis by simp
  qed
qed

lemma last_changes_implies_send_when_msgs_nonempty:
  assumes
    "trace init t final" and
    "msgs (S t i) cid \<noteq> []" and
    "msgs (S t (i+1)) cid \<noteq> []" and
    "last (msgs (S t i) cid) = Marker" and
    "last (msgs (S t (i+1)) cid) \<noteq> Marker" and
    "channel cid = Some (p, q)"
  shows
    "(\<exists>u u' m. t ! i = Send cid p q u u' m)"
proof -
  have step: "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (i+1))" 
    by (metis Suc_eq_plus1_left add.commute assms(1) assms(4) assms(5) le_Suc_eq nat_le_linear nat_less_le no_change_if_ge_length_t step_Suc)
  then show ?thesis
  proof (cases "t ! i")
    case (Snapshot r)
    then show ?thesis 
      by (metis assms(4) assms(5) last_snoc local.step next_snapshot)
  next
    case (RecvMarker cid' r s)
    then show ?thesis
    proof (cases "cid = cid'")
      case True
      then have "last (msgs (S t i) cid) = last (msgs (S t (i+1)) cid)" 
      proof -
        have "Marker # msgs (S t (i + 1)) cid = msgs (S t i) cid"
          using RecvMarker local.step True by auto
        then show ?thesis
          by (metis assms(3) last_ConsR)
      qed
      then show ?thesis using assms by simp
    next
      case no_snap: False
      then have "last (msgs (S t i) cid) = last (msgs (S t (i+1)) cid)"
      proof (cases "has_snapshotted (S t i) r")
        case True
        then show ?thesis using RecvMarker step no_snap by simp
      next
        case False
        with RecvMarker step no_snap \<open>cid \<noteq> cid'\<close> assms show ?thesis by (cases "p = r", auto)
      qed
      then show ?thesis using assms by simp
    qed
  next
    case (Trans r u u')
    then show ?thesis 
      using assms(4) assms(5) local.step by auto
  next
    case (Send cid' r s u u' m)
    then have "cid = cid'" 
      by (metis (no_types, hide_lams) assms(4) assms(5) local.step next_send)
    moreover have "(p, q) = (r, s)"
    proof -
      have "channel cid = channel cid'" using \<open>cid = cid'\<close> by simp
      moreover have "channel cid = Some (p, q)" using assms by simp
      moreover have "channel cid' = Some (r, s)" using Send step can_occur_def by auto
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis using Send by auto
  next
    case (Recv cid' r s u u' m)
    then show ?thesis
    proof (cases "cid = cid'")
      case True
      then have "last (msgs (S t i) cid) = last (msgs (S t (i+1)) cid)" 
        by (metis (no_types, lifting) Recv assms(3) assms(4) last_ConsR local.step next_recv)
      then show ?thesis using assms by simp
    next
      case False
      then have "msgs (S t i) cid = msgs (S t (i+1)) cid" using Recv step by auto
      then show ?thesis using assms by simp
    qed
  qed
qed

lemma no_marker_after_RecvMarker:
  assumes
    "trace init t final" and
    "(S t i) \<turnstile> RecvMarker cid p q \<mapsto> (S t (i+1))" and
    "channel cid = Some (q, p)"
  shows
    "Marker \<notin> set (msgs (S t (i+1)) cid)"
proof -
  have new_msgs: "msgs (S t i) cid = Marker # msgs (S t (i+1)) cid" 
    using assms(2) by auto
  have one_marker: "\<exists>!j. j < length (msgs (S t i) cid) \<and> msgs (S t i) cid ! j = Marker" 
    by (metis assms(1,3) at_most_one_marker list.set_intros(1) new_msgs)
  then obtain j where "j < length (msgs (S t i) cid)" "msgs (S t i) cid ! j = Marker" by blast
  then have "j = 0" using one_marker new_msgs by auto
  then have "\<forall>j. j \<noteq> 0 \<and> j < length (msgs (S t i) cid) \<longrightarrow> msgs (S t i) cid ! j \<noteq> Marker"
    using one_marker 
    using \<open>j < length (msgs (S t i) cid)\<close> \<open>msgs (S t i) cid ! j = Marker\<close> by blast
  then have "\<forall>j. j < length (msgs (S t (i+1)) cid) \<longrightarrow> msgs (S t (i+1)) cid ! j \<noteq> Marker"
    by (metis One_nat_def Suc_eq_plus1 Suc_le_eq Suc_mono le_zero_eq list.size(4) new_msgs not_less0 nth_Cons_Suc)
  then show ?thesis 
    by (simp add: in_set_conv_nth)
qed

lemma no_marker_and_snapshotted_implies_no_more_markers_trace:
  shows
    "\<lbrakk> trace init t final; i \<le> j; j \<le> length t;
       has_snapshotted (S t i) p;
       Marker \<notin> set (msgs (S t i) cid);
       channel cid = Some (p, q) \<rbrakk>
     \<Longrightarrow> Marker \<notin> set (msgs (S t j) cid)"
proof (induct "j - i" arbitrary: i)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have step: "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (i+1))" 
    by (metis (no_types, hide_lams) Suc_eq_plus1 cancel_comm_monoid_add_class.diff_cancel distributed_system.step_Suc distributed_system_axioms less_le_trans linorder_not_less old.nat.distinct(2) order_eq_iff)
  then have "Marker \<notin> set (msgs (S t (i+1)) cid)"
    using no_marker_and_snapshotted_implies_no_more_markers Suc step by blast
  moreover have "has_snapshotted (S t (i+1)) p" 
    using Suc.prems(4) local.step snapshot_state_unchanged by auto
  ultimately show ?case 
  proof -
    assume a1: "ps (S t (i + 1)) p \<noteq> None"
    assume a2: "Marker \<notin> set (msgs (S t (i + 1)) cid)"
    have f3: "j \<noteq> i"
      using Suc.hyps(2) by force
    have "j - Suc i = n"
      by (metis (no_types) Suc.hyps(2) Suc.prems(2) add.commute add_Suc_right add_diff_cancel_left' le_add_diff_inverse)
    then show ?thesis
      using f3 a2 a1 by (metis Suc.hyps(1) Suc.prems(1) Suc.prems(2) Suc.prems(3) Suc.prems(6) Suc_eq_plus1_left add.commute less_Suc_eq linorder_not_less)
  qed
qed

lemma marker_not_vanishing_means_always_present:
  shows
    "\<lbrakk> trace init t final; i \<le> j; j \<le> length t;
       Marker : set (msgs (S t i) cid);
       Marker : set (msgs (S t j) cid);
       channel cid = Some (p, q)
     \<rbrakk> \<Longrightarrow> \<forall>k. i \<le> k \<and> k \<le> j \<longrightarrow> Marker : set (msgs (S t k) cid)"
proof (induct "j - i" arbitrary: i)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have step: "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (i+1))" 
    by (metis (no_types, lifting) Suc_eq_plus1 add_lessD1 distributed_system.step_Suc distributed_system_axioms le_add_diff_inverse order_le_less zero_less_Suc zero_less_diff)
  have "Marker : set (msgs (S t (i+1)) cid)"
  proof (rule ccontr)
    assume asm: "~ Marker : set (msgs (S t (i+1)) cid)"
    have snap_p: "has_snapshotted (S t i) p" 
      using Suc.prems(1) Suc.prems(4,6) no_marker_if_no_snapshot by blast
    then have "has_snapshotted (S t (i+1)) p" 
      using local.step snapshot_state_unchanged by auto
    then have "Marker \<notin> set (msgs (S t j) cid)"
      by (metis Suc.hyps(2) Suc.prems(1) Suc.prems(3) Suc.prems(6) asm discrete no_marker_and_snapshotted_implies_no_more_markers_trace zero_less_Suc zero_less_diff)
    then show False using Suc.prems by simp
  qed
  then show ?case
    by (meson Suc.prems(1) Suc.prems(3) Suc.prems(4) Suc.prems(5) Suc.prems(6) computation.snapshot_stable_ver_3 computation_axioms no_marker_and_snapshotted_implies_no_more_markers_trace no_marker_if_no_snapshot)
qed

lemma last_stays_if_no_recv_marker_and_no_send:
  shows "\<lbrakk> trace init t final; i < j; j \<le> length t;
           last (msgs (S t i) cid) = Marker;
           Marker : set (msgs (S t i) cid);
           Marker : set (msgs (S t j) cid);
           \<forall>k. i \<le> k \<and> k < j \<longrightarrow> ~ (\<exists>u u' m. t ! k = Send cid p q u u' m);
           channel cid = Some (p, q) \<rbrakk>
         \<Longrightarrow> last (msgs (S t j) cid) = Marker"
proof (induct "j - (i+1)" arbitrary: i)
  case 0
  then have "j = i+1" by simp
  then have step: "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (i+1))" 
    by (metis "0"(2) "0.prems"(2) "0.prems"(3) Suc_eq_plus1 distributed_system.step_Suc distributed_system_axioms less_le_trans)
  have "Marker = last (msgs (S t (i+1)) cid)"
  proof (rule ccontr)
    assume "~ Marker = last (msgs (S t (i+1)) cid)"
    then have "\<exists>u u' m. t ! i = Send cid p q u u' m"
    proof -
      have "msgs (S t (i+1)) cid \<noteq> []" using "0" \<open>j = i+1\<close> by auto
      moreover have "msgs (S t i) cid \<noteq> []" using "0" by auto
      ultimately show ?thesis 
        using "0.prems"(1) "0.prems"(4) "0.prems"(8) \<open>Marker \<noteq> last (msgs (S t (i + 1)) cid)\<close> last_changes_implies_send_when_msgs_nonempty by auto
    qed
    then show False using 0 by auto
  qed
  then show ?case using \<open>j = i+1\<close> by simp
next
  case (Suc n)
  then have step: "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (i+1))" 
    by (metis (no_types, hide_lams) Suc_eq_plus1 distributed_system.step_Suc distributed_system_axioms less_le_trans)
  have marker_present: "Marker : set (msgs (S t (i+1)) cid)" 
    by (meson Suc.prems(1) Suc.prems(2) Suc.prems(3) Suc.prems(5) Suc.prems(6) Suc.prems(8) discrete le_add1 less_imp_le_nat marker_not_vanishing_means_always_present)
  moreover have "Marker = last (msgs (S t (i+1)) cid)"
  proof (rule ccontr)
    assume asm: "~ Marker = last (msgs (S t (i+1)) cid)"
    then have "\<exists>u u' m. t ! i = Send cid p q u u' m"
    proof -
      have "msgs (S t (i+1)) cid \<noteq> []" using marker_present by auto
      moreover have "msgs (S t i) cid \<noteq> []" using Suc by auto
      ultimately show ?thesis 
        using Suc.prems(1) Suc.prems(4) Suc.prems(8) asm last_changes_implies_send_when_msgs_nonempty by auto
    qed
    then show False using Suc by auto
  qed
  moreover have "\<forall>k. i+1 \<le> k \<and> k < j \<longrightarrow> ~ (\<exists>u u' m. t ! k = Send cid p q u u' m)"
    using Suc.prems by force
  moreover have "i+1 < j" using Suc by auto
  moreover have "j \<le> length t" using Suc by auto
  moreover have "trace init t final" using Suc by auto
  moreover have "Marker : set (msgs (S t j) cid)" using Suc by auto
  ultimately show ?case using Suc 
    by (metis diff_Suc_1 diff_diff_left)
qed

lemma last_changes_implies_send_when_msgs_nonempty_trace:
  assumes
    "trace init t final"
    "i < j"
    "j \<le> length t"
    "Marker : set (msgs (S t i) cid)"
    "Marker : set (msgs (S t j) cid)"
    "last (msgs (S t i) cid) = Marker"
    "last (msgs (S t j) cid) \<noteq> Marker"
    "channel cid = Some (p, q)"
  shows
    "\<exists>k u u' m. i \<le> k \<and> k < j \<and> t ! k = Send cid p q u u' m"
proof (rule ccontr)
  assume "~ (\<exists>k u u' m. i \<le> k \<and> k < j \<and> t ! k = Send cid p q u u' m)"
  then have "\<forall>k. i \<le> k \<and> k < j \<longrightarrow> ~ (\<exists>u u' m. t ! k = Send cid p q u u' m)" by blast
  then have "last (msgs (S t j) cid) = Marker" using assms last_stays_if_no_recv_marker_and_no_send by blast
  then show False using assms by simp
qed

lemma msg_after_marker_and_nonempty_implies_postrecording_event:
  assumes
    "trace init t final" and
    "Marker : set (msgs (S t i) cid)" and
    "Marker \<noteq> last (msgs (S t i) cid)" and
    "i \<le> length t" and
    "channel cid = Some (p, q)"
  shows
    "\<exists>j. j < i \<and> postrecording_event t j" (is ?P)
proof -
  let ?len = "length (msgs (S t i) cid)"
  have "?len \<noteq> 0" using assms(2) by auto
  have snap_p_i: "has_snapshotted (S t i) p" 
    using assms no_marker_if_no_snapshot by blast
  obtain j where snap_p: "~ has_snapshotted (S t j) p" "has_snapshotted (S t (j+1)) p" 
    by (metis Suc_eq_plus1 assms(1) exists_snapshot_for_all_p)
  have "j < i" 
    by (meson assms(1) computation.snapshot_stable_ver_2 computation_axioms not_less snap_p(1) snap_p_i)
  have step_snap: "(S t j) \<turnstile> (t ! j) \<mapsto> (S t (j+1))" 
    by (metis Suc_eq_plus1 assms(1) l2 nat_le_linear nat_less_le snap_p(1) snapshot_stable_ver_2 step_Suc)
  have re: "~ regular_event (t ! j)" 
    by (meson distributed_system.regular_event_cannot_induce_snapshot distributed_system_axioms snap_p(1) snap_p(2) step_snap)
  have op: "occurs_on (t ! j) = p" 
    using no_state_change_if_no_event snap_p(1) snap_p(2) step_snap by force
  have marker_last: "Marker = last (msgs (S t (j+1)) cid) \<and> msgs (S t (j+1)) cid \<noteq> []"
  proof -
    have "isSnapshot (t ! j) \<or> isRecvMarker (t ! j)" using re nonregular_event by auto
    then show ?thesis
    proof (elim disjE, goal_cases)
      case 1
      then have "t ! j = Snapshot p" 
        using op by auto
      then show ?thesis using step_snap assms by auto
    next
      case 2
      then obtain cid' r where RecvMarker: "t ! j = RecvMarker cid' p r" 
        by (metis event.collapse(5) op)
      then have "cid \<noteq> cid'" 
        using RecvMarker_implies_Marker_in_set assms(1) assms(5) no_marker_if_no_snapshot snap_p(1) step_snap by blast
      then show ?thesis 
        using assms snap_p(1) step_snap RecvMarker by auto
    qed
  qed
  then have "\<exists>k u u' m. j+1 \<le> k \<and> k < i \<and> t ! k = Send cid p q u u' m"
  proof -
    have "j+1 < i"
    proof -
      have "(S t (j+1)) \<noteq> (S t i)" 
        using assms(3) marker_last by auto
      then have "j+1 \<noteq> i" by auto
      moreover have "j+1 \<le> i" using \<open>j < i\<close> by simp
      ultimately show ?thesis by simp
    qed
    moreover have "trace init t final" using assms by simp
    moreover have "Marker = last (msgs (S t (j+1)) cid)" using marker_last by simp
    moreover have "Marker : set (msgs (S t (j+1)) cid)" using marker_last by (simp add: marker_last)
    ultimately show ?thesis using assms last_changes_implies_send_when_msgs_nonempty_trace by simp
  qed
  then obtain k where Send: "\<exists>u u' m. j+1 \<le> k \<and> k < i \<and> t ! k = Send cid p q u u' m" by blast
  then have "postrecording_event t k"
  proof -
    have "k < length t" using Send assms by simp
    moreover have "isSend (t ! k)" using Send by auto
    moreover have "has_snapshotted (S t k) p" using Send snap_p 
      using assms(1) snapshot_stable_ver_3 by blast
    moreover have "occurs_on (t ! k) = p" using Send by auto
    ultimately show ?thesis unfolding postrecording_event by simp
  qed
  then show ?thesis using Send by auto
qed

lemma same_messages_if_no_occurrence_trace:
  shows
    "\<lbrakk> trace init t final; i \<le> j; j \<le> length t;
       (\<forall>k. i \<le> k \<and> k < j \<longrightarrow> occurs_on (t ! k) \<noteq> p \<and> occurs_on (t ! k) \<noteq> q);
       channel cid = Some (p, q) \<rbrakk>
     \<Longrightarrow> msgs (S t i) cid = msgs (S t j) cid \<and> cs (S t i) cid = cs (S t j) cid"
proof (induct "j - i" arbitrary: i)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have step: "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (i+1))" 
    by (metis (no_types, hide_lams) Suc_eq_plus1 Suc_n_not_le_n diff_self_eq_0 distributed_system.step_Suc distributed_system_axioms le0 le_eq_less_or_eq less_le_trans)
  then have "msgs (S t i) cid = msgs (S t (i+1)) cid \<and> cs (S t i) cid = cs (S t (i+1)) cid"
  proof -
    have "~ occurs_on (t ! i) = p" using Suc by simp
    moreover have "~ occurs_on (t ! i) = q" using Suc by simp
    ultimately show ?thesis using step Suc same_messages_if_no_occurrence by blast
  qed
  moreover have "msgs (S t (i+1)) cid = msgs (S t j) cid \<and> cs (S t (i+1)) cid = cs (S t j) cid"
  proof -
    have "i+1 \<le> j" using Suc by linarith
    moreover have "\<forall>k. i+1 \<le> k \<and> k < j \<longrightarrow> occurs_on (t ! k) \<noteq> p \<and> occurs_on (t ! k) \<noteq> q" using Suc by force
    ultimately show ?thesis using Suc by auto
  qed
  ultimately show ?case by simp
qed

lemma snapshot_step_cs_preservation_p:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "~ regular_event ev" and
    "occurs_on ev = p" and
    "channel cid = Some (p, q)"
  shows
    "map Msg (fst (cs c cid)) @ takeWhile ((\<noteq>) Marker) (msgs c cid)
   = map Msg (fst (cs c' cid)) @ takeWhile ((\<noteq>) Marker) (msgs c' cid)
   \<and> snd (cs c cid) = snd (cs c' cid)"
proof -
  have "isSnapshot ev \<or> isRecvMarker ev" using assms nonregular_event by blast
  then show ?thesis
  proof (elim disjE, goal_cases)
    case 1
    then have Snap: "ev = Snapshot p" by (metis event.collapse(4) assms(3))
    then have "fst (cs c cid) = fst (cs c' cid)" 
      using assms(1) assms(2) regular_event same_cs_if_not_recv by blast
    moreover have "takeWhile ((\<noteq>) Marker) (msgs c cid)
                 = takeWhile ((\<noteq>) Marker) (msgs c' cid)"
    proof -
      have "msgs c' cid = msgs c cid @ [Marker]" using assms Snap by auto
      then show ?thesis 
        by (simp add: takeWhile_tail)
    qed
    moreover have "snd (cs c cid) = snd (cs c' cid)" 
      using Snap assms no_self_channel by fastforce
    ultimately show ?thesis by simp
  next
    case 2
    then obtain cid' r where RecvMarker: "ev = RecvMarker cid' p r" by (metis event.collapse(5) assms(3))
    have "cid \<noteq> cid'" 
      by (metis "2" RecvMarker assms(1) assms(4) distributed_system.RecvMarker_given_channel distributed_system.happen_implies_can_occur distributed_system_axioms event.sel(5,10) no_self_channel)
    then have "fst (cs c cid) = fst (cs c' cid)"
      using RecvMarker assms(1) assms(2) regular_event same_cs_if_not_recv by blast
    moreover have "takeWhile ((\<noteq>) Marker) (msgs c cid)
                 = takeWhile ((\<noteq>) Marker) (msgs c' cid)"
    proof (cases "has_snapshotted c p")
      case True
      then have "msgs c cid = msgs c' cid" using RecvMarker \<open>cid \<noteq> cid'\<close> assms by auto
      then show ?thesis by simp
    next
      case False
      then have "msgs c' cid = msgs c cid @ [Marker]" using RecvMarker \<open>cid \<noteq> cid'\<close> assms by auto
      then show ?thesis
        by (simp add: takeWhile_tail)
    qed
    moreover have "snd (cs c cid) = snd (cs c' cid)"
    proof (cases "has_snapshotted c p")
      case True
      then have "cs c cid = cs c' cid" using RecvMarker \<open>cid \<noteq> cid'\<close> assms by simp
      then show ?thesis by simp
    next
      case False
      then show ?thesis
        using RecvMarker \<open>cid \<noteq> cid'\<close> assms(1) assms(4) no_self_channel by auto
    qed
    ultimately show ?thesis by simp
  qed
qed

lemma snapshot_step_cs_preservation_q:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "~ regular_event ev" and
    "occurs_on ev = q" and
    "channel cid = Some (p, q)" and
    "Marker \<notin> set (msgs c cid)" and
    "~ has_snapshotted c q"
  shows
    "map Msg (fst (cs c cid)) @ takeWhile ((\<noteq>) Marker) (msgs c cid)
   = map Msg (fst (cs c' cid)) @ takeWhile ((\<noteq>) Marker) (msgs c' cid)
   \<and> snd (cs c' cid) = Recording"
proof -
  have "isSnapshot ev \<or> isRecvMarker ev" using assms nonregular_event by blast
  then show ?thesis
  proof (elim disjE, goal_cases)
    case 1
    then have Snapshot: "ev = Snapshot q" by (metis event.collapse(4) assms(3))
    then have "fst (cs c cid) = fst (cs c' cid)" 
      using assms(1) assms(2) regular_event same_cs_if_not_recv by blast
    moreover have "takeWhile ((\<noteq>) Marker) (msgs c cid)
                 = takeWhile ((\<noteq>) Marker) (msgs c' cid)"
    proof -
      have "msgs c' cid = msgs c cid" using assms Snapshot 
        by (metis distributed_system.next_snapshot distributed_system_axioms eq_fst_iff no_self_channel option.inject)
      then show ?thesis by simp
    qed
    moreover have "snd (cs c' cid) = Recording" using assms Snapshot by auto
    ultimately show ?thesis by simp
  next
    case 2
    then obtain cid' r where RecvMarker: "ev = RecvMarker cid' q r" by (metis event.collapse(5) assms(3))
    have "cid \<noteq> cid'" 
      using RecvMarker RecvMarker_implies_Marker_in_set assms(1) assms(5) by blast
    have "fst (cs c cid) = fst (cs c' cid)"
      using assms(1) assms(2) regular_event same_cs_if_not_recv by blast
    moreover have "takeWhile ((\<noteq>) Marker) (msgs c cid)
                 = takeWhile ((\<noteq>) Marker) (msgs c' cid)"
    proof -
      have "\<nexists>r. channel cid = Some (q, r)" 
        using assms(4) no_self_channel by auto
      with RecvMarker assms \<open>cid \<noteq> cid'\<close> have "msgs c cid = msgs c' cid" by (cases "has_snapshotted c r", auto)
      then show ?thesis by simp
    qed
    moreover have "snd (cs c' cid) = Recording" using assms RecvMarker \<open>cid \<noteq> cid'\<close> by simp
    ultimately show ?thesis by simp
  qed
qed

lemma Marker_in_channel_implies_not_done:
  assumes
    "trace init t final" and
    "Marker : set (msgs (S t i) cid)" and
    "channel cid = Some (p, q)" and
    "i \<le> length t"
  shows
    "snd (cs (S t i) cid) \<noteq> Done"
proof (rule ccontr)
  assume is_done: "~ snd (cs (S t i) cid) \<noteq> Done"
  let ?t = "take i t"
  have tr: "trace init ?t (S t i)" 
    using assms(1) exists_trace_for_any_i by blast
  have "\<exists>q p. RecvMarker cid q p \<in> set ?t" 
    by (metis (mono_tags, lifting) assms(3) distributed_system.trace.simps distributed_system_axioms done_only_from_recv_marker_trace computation.no_initial_channel_snapshot computation_axioms is_done list.discI recording_state.simps(4) snd_conv tr)
  then obtain j where RecvMarker: "\<exists>q p. t ! j = RecvMarker cid q p" "j < i" 
    by (metis (no_types, lifting) assms(4) in_set_conv_nth length_take min.absorb2 nth_take)
  then have step_j: "(S t j) \<turnstile> (t ! j) \<mapsto> (S t (j+1))" 
    by (metis Suc_eq_plus1 assms(1) distributed_system.step_Suc distributed_system_axioms assms(4) less_le_trans)
  then have "t ! j = RecvMarker cid q p"
    by (metis RecvMarker(1) RecvMarker_given_channel assms(3) event.disc(25) event.sel(10) happen_implies_can_occur)
  then have "Marker \<notin> set (msgs (S t (j+1)) cid)" 
    using assms(1) assms(3) no_marker_after_RecvMarker step_j by presburger
  moreover have "has_snapshotted (S t (j+1)) p" 
    using Suc_eq_plus1 \<open>t ! j = RecvMarker cid q p\<close> assms(1) recv_marker_means_snapshotted snapshot_state_unchanged step_j by presburger
  ultimately have "Marker \<notin> set (msgs (S t i) cid)" 
    by (metis RecvMarker(2) Suc_eq_plus1 Suc_leI assms(1,3) assms(4) no_marker_and_snapshotted_implies_no_more_markers_trace)
  then show False using assms by simp
qed

lemma keep_empty_if_no_events:
  shows
    "\<lbrakk> trace init t final; i \<le> j; j \<le> length t;
       msgs (S t i) cid = [];
       has_snapshotted (S t i) p;
       channel cid = Some (p, q);
       \<forall>k. i \<le> k \<and> k < j \<and> regular_event (t ! k) \<longrightarrow> ~ occurs_on (t ! k) = p \<rbrakk>
     \<Longrightarrow> msgs (S t j) cid = []"
proof (induct "j - i" arbitrary: i)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have step: "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (i+1))" 
  proof -
    have "i < length t"
      using Suc.hyps(2) Suc.prems(3) by linarith
    then show ?thesis
      by (metis (full_types) Suc.prems(1) Suc_eq_plus1 step_Suc)
  qed
  have "msgs (S t (i+1)) cid = []"
  proof (cases "t ! i")
    case (Snapshot r)
    have "r \<noteq> p"
    proof (rule ccontr)
      assume "~ r \<noteq> p"
      moreover have "can_occur (t ! i) (S t i)"
        using happen_implies_can_occur local.step by blast
      ultimately show False using can_occur_def Snapshot Suc by simp
    qed
    then have "msgs (S t i) cid = msgs (S t (i+1)) cid" 
      using Snapshot local.step Suc by auto
    then show ?thesis using Suc by simp
  next
    case (RecvMarker cid' r s)
    have "cid \<noteq> cid'"
    proof (rule ccontr)
      assume "~ cid \<noteq> cid'"
      then have "msgs (S t i) cid \<noteq> []" 
        by (metis RecvMarker length_greater_0_conv linorder_not_less list.size(3) local.step nat_less_le recv_marker_other_channels_not_shrinking)
      then show False using Suc by simp
    qed
    then show ?thesis
    proof (cases "has_snapshotted (S t i) r")
      case True
      then have "msgs (S t (i+1)) cid = msgs (S t i) cid" using RecvMarker Suc step \<open>cid \<noteq> cid'\<close> by auto
      then show ?thesis using Suc by simp
    next
      case False
      have "r \<noteq> p" 
        using False Suc.prems(5) by blast
      then show ?thesis using RecvMarker Suc step \<open>cid \<noteq> cid'\<close> False by simp
    qed
  next
    case (Trans r u u')
    then show ?thesis using Suc step by simp
  next
    case (Send cid' r s u u' m)
    have "r \<noteq> p"
    proof (rule ccontr)
      assume "~ r \<noteq> p"
      then have "occurs_on (t ! i) = p \<and> regular_event (t ! i)" using Send by simp
      moreover have "i \<le> i \<and> i < j" using Suc by simp
      ultimately show False using Suc.prems by blast
    qed
    have "cid \<noteq> cid'"
    proof (rule ccontr)
      assume "~ cid \<noteq> cid'"
      then have "channel cid = channel cid'" by auto
      then have "channel cid' = Some (r, s)" using Send step can_occur_def by simp
      then show False using Suc \<open>r \<noteq> p\<close> \<open>~ cid \<noteq> cid'\<close> by auto
    qed
    then have "msgs (S t i) cid = msgs (S t (i+1)) cid"
      using step Send Suc by simp
    then show ?thesis using Suc by simp
  next
    case (Recv cid' r s u u' m)
    have "cid \<noteq> cid'"
    proof (rule ccontr)
      assume "~ cid \<noteq> cid'"
      then have "msgs (S t i) cid \<noteq> []" 
        using Recv local.step by auto
      then show False using Suc by simp
    qed
    then have "msgs (S t i) cid = msgs (S t (i+1)) cid" using Recv step by auto
    then show ?thesis using Suc by simp
  qed
  moreover have "\<forall>k. i+1 \<le> k \<and> k < j \<and> regular_event (t ! k) \<longrightarrow> ~ occurs_on (t ! k) = p"
    using Suc by simp
  moreover have "has_snapshotted (S t (i+1)) p" 
    by (meson Suc.prems(1) Suc.prems(5) discrete less_not_refl nat_le_linear snapshot_stable_ver_3)
  moreover have "i+1 \<le> j" using Suc by simp
  moreover have "j \<le> length t" using Suc by simp
  moreover have "j - (i+1) = n" using Suc by linarith
  ultimately show ?case using Suc by blast
qed

lemma last_unchanged_or_empty_if_no_events:
  shows
    "\<lbrakk> trace init t final; i \<le> j; j \<le> length t;
       msgs (S t i) cid \<noteq> [];
       last (msgs (S t i) cid) = Marker;
       has_snapshotted (S t i) p;
       channel cid = Some (p, q);
       \<forall>k. i \<le> k \<and> k < j \<and> regular_event (t ! k) \<longrightarrow> ~ occurs_on (t ! k) = p \<rbrakk>
     \<Longrightarrow> msgs (S t j) cid = [] \<or> (msgs (S t j) cid \<noteq> [] \<and> last (msgs (S t j) cid) = Marker)"
proof (induct "j - i" arbitrary: i)
  case 0
  then show ?case 
    by auto
next
  case (Suc n)
  then have step: "(S t i) \<turnstile> (t ! i) \<mapsto> (S t (i+1))" 
  proof -
    have "i < length t"
      using Suc.hyps(2) Suc.prems(3) by linarith
    then show ?thesis
      by (metis (full_types) Suc.prems(1) Suc_eq_plus1 step_Suc)
  qed
  have msgs_s_ip1: "msgs (S t (i+1)) cid = [] \<or> (msgs (S t (i+1)) cid \<noteq> [] \<and> last (msgs (S t (i+1)) cid) = Marker)"
  proof (cases "t ! i")
    case (Snapshot r)
    have "r \<noteq> p"
    proof (rule ccontr)
      assume "~ r \<noteq> p"
      moreover have "can_occur (t ! i) (S t i)"
        using happen_implies_can_occur local.step by blast
      ultimately show False using can_occur_def Snapshot Suc by simp
    qed
    then have "msgs (S t i) cid = msgs (S t (i+1)) cid" 
      using Snapshot local.step Suc by auto
    then show ?thesis using Suc by simp
  next
    case (RecvMarker cid' r s)
    then show ?thesis
    proof (cases "cid = cid'")
      case True
      then have "msgs (S t (i+1)) cid = []" 
      proof -
        have "Marker # msgs (S t (i+1)) cid = msgs (S t i) cid"
          using RecvMarker True local.step by auto
        then show ?thesis
        proof -
          assume a1: "Marker # msgs (S t (i + 1)) cid = msgs (S t i) cid"
          have "i < j"
            by (metis (no_types) Suc.hyps(2) Suc.prems(2) Suc_neq_Zero diff_is_0_eq le_neq_implies_less)
          then have "i < length t"
            using Suc.prems(3) less_le_trans by blast
          then show ?thesis
            using a1 by (metis (no_types) Marker_in_channel_implies_not_done RecvMarker Suc.prems(1) Suc.prems(5) Suc.prems(7) Suc_eq_plus1 Suc_le_eq True last_ConsR last_in_set recv_marker_means_cs_Done)
        qed
      qed
      then show ?thesis by simp
    next
      case False
      then show ?thesis
      proof (cases "has_snapshotted (S t i) r")
        case True
        then show ?thesis 
          using False RecvMarker Suc.prems(5) local.step by auto
      next
        case False
        then have "r \<noteq> p" 
          using Suc.prems(6) by blast
        with RecvMarker False Suc.prems step \<open>cid \<noteq> cid'\<close> show ?thesis by auto
      qed
    qed
  next
    case (Trans r u u')
    then show ?thesis using Suc step by simp
  next
    case (Send cid' r s u u' m)
    have "r \<noteq> p"
    proof (rule ccontr)
      assume "~ r \<noteq> p"
      then have "occurs_on (t ! i) = p \<and> regular_event (t ! i)" using Send by simp
      moreover have "i \<le> i \<and> i < j" using Suc by simp
      ultimately show False using Suc.prems by blast
    qed
    have "cid \<noteq> cid'"
    proof (rule ccontr)
      assume "~ cid \<noteq> cid'"
      then have "channel cid = channel cid'" by auto
      then have "channel cid' = Some (r, s)" using Send step can_occur_def by simp
      then show False using Suc \<open>r \<noteq> p\<close> \<open>~ cid \<noteq> cid'\<close> by auto
    qed
    then have "msgs (S t i) cid = msgs (S t (i+1)) cid"
      using step Send by simp
    then show ?thesis using Suc by simp
  next
    case (Recv cid' r s u u' m)
    then show ?thesis
    proof (cases "cid = cid'")
      case True
      then have "msgs (S t i) cid = Msg m # msgs (S t (i+1)) cid" 
        using Recv local.step by auto
      then have "last (msgs (S t (i+1)) cid) = Marker" 
        by (metis Suc.prems(5) last.simps message.simps(3))
      then show ?thesis by blast
    next
      case False
      then have "msgs (S t i) cid = msgs (S t (i+1)) cid" using Recv step by auto
      then show ?thesis using Suc by simp
    qed
  qed
  then show ?case
  proof (elim disjE, goal_cases)
    case 1
    moreover have "trace init t final" using Suc by simp
    moreover have "i+1 \<le> j" using Suc by simp
    moreover have "j \<le> length t" using Suc by simp
    moreover have "has_snapshotted (S t (i+1)) p" 
      using Suc.prems(6) local.step snapshot_state_unchanged by auto
    moreover have "j - (i+1) = n" using Suc by linarith
    moreover have "\<forall>k. i+1 \<le> k \<and> k < j \<and> regular_event (t ! k) \<longrightarrow> ~ occurs_on (t ! k) = p"
      using Suc by auto
    ultimately have "msgs (S t j) cid = []" using keep_empty_if_no_events Suc.prems(7) by blast
    then show ?thesis by simp
  next
    case 2
    moreover have "trace init t final" using Suc by simp
    moreover have "i+1 \<le> j" using Suc by simp
    moreover have "j \<le> length t" using Suc by simp
    moreover have "has_snapshotted (S t (i+1)) p" 
      using Suc.prems(6) local.step snapshot_state_unchanged by auto
    moreover have "j - (i+1) = n" using Suc by linarith
    moreover have "\<forall>k. i+1 \<le> k \<and> k < j \<and> regular_event (t ! k) \<longrightarrow> ~ occurs_on (t ! k) = p"
      using Suc by auto
    ultimately show ?thesis using Suc.prems(7) Suc.hyps by blast
  qed
qed

lemma cs_after_all_prerecording_events:
  assumes
    "trace init t final" and
    "\<forall>i'. i' \<ge> i \<longrightarrow> ~ prerecording_event t i'" and
    "\<forall>j'. j' < i \<longrightarrow> ~ postrecording_event t j'" and
    "i \<le> length t"
  shows
    "cs_equal_to_snapshot (S t i) final"
proof (unfold cs_equal_to_snapshot_def, rule allI, rule impI)
  fix cid
  assume "channel cid \<noteq> None"
  then obtain p q where chan: "channel cid = Some (p, q)" by auto
  have cs_done: "snd (cs (S t (length t)) cid) = Done" 
    using chan all_channels_done_in_final_state assms(1) final_is_s_t_len_t by blast
  have "filter ((\<noteq>) Marker) (msgs (S t i) cid) = takeWhile ((\<noteq>) Marker) (msgs (S t i) cid)" (is ?B)
  proof (rule ccontr)
    let ?m = "msgs (S t i) cid"
    assume "~ ?B"
    then obtain j k where range: "j < k" "k < length ?m" and "?m ! j = Marker" "?m ! k \<noteq> Marker"
      using filter_neq_takeWhile by metis
    then have "Marker \<in> set ?m" 
      by (metis less_trans nth_mem)
    moreover have "last ?m \<noteq> Marker"
    proof -
      have "\<forall>l. l < length ?m \<and> l \<noteq> j \<longrightarrow> ?m ! l \<noteq> Marker" 
        using chan \<open>j < k\<close> \<open>k < length (msgs (S t i) cid)\<close> \<open>msgs (S t i) cid ! j = Marker\<close> assms(1) at_most_one_marker calculation less_trans by blast
      moreover have "last ?m = ?m ! (length ?m - 1)" 
        by (metis \<open>Marker \<in> set (msgs (S t i) cid)\<close> empty_iff last_conv_nth list.set(1))
      moreover have "length ?m - 1 \<noteq> j" using range by auto
      ultimately show ?thesis using range by auto
    qed
    moreover have "i \<le> length t" 
      using chan assms(1) calculation(1) computation.exists_next_marker_free_state computation.no_change_if_ge_length_t computation_axioms nat_le_linear by fastforce
    ultimately have "\<exists>j. j < i \<and> postrecording_event t j"
      using chan assms(1) msg_after_marker_and_nonempty_implies_postrecording_event by auto
    then show False using assms by auto
  qed
  moreover have "takeWhile ((\<noteq>) Marker) (msgs (S t i) cid) = map Msg (fst (cs final cid))"
  proof (cases "snd (cs (S t i) cid)")
    case NotStarted
    text \<open>show that q and p have to snapshot, and then reduce it to the case below depending on
          the order they snapshotted in\<close>
    have nsq: "~ has_snapshotted (S t i) q" 
      using NotStarted chan assms(1) cs_in_initial_state_implies_not_snapshotted by auto
    obtain j where snap_q: "~ has_snapshotted (S t j) q" "has_snapshotted (S t (j+1)) q" 
      by (metis Suc_eq_plus1 assms(1) exists_snapshot_for_all_p)
    have step_q: "(S t j) \<turnstile> (t ! j) \<mapsto> (S t (j+1))" 
      by (metis \<open>\<not> ps (S t j) q \<noteq> None\<close> add.commute assms(1) le_SucI le_eq_less_or_eq le_refl linorder_neqE_nat no_change_if_ge_length_t plus_1_eq_Suc snap_q step_Suc)
    obtain k where snap_p: "~ has_snapshotted (S t k) p" "has_snapshotted (S t (k+1)) p" 
      by (metis Suc_eq_plus1 assms(1) exists_snapshot_for_all_p)
    have bound: "i \<le> j"
    proof (rule ccontr)
      assume "~ i \<le> j"
      then have "i \<ge> j+1" by simp
      then have "has_snapshotted (S t i) q" 
        by (meson assms(1) computation.snapshot_stable_ver_3 computation_axioms snap_q(2))
      then show False using nsq by simp
    qed
    have step_p: "(S t k) \<turnstile> (t ! k) \<mapsto> (S t (k+1))" 
      by (metis \<open>\<not> ps (S t k) p \<noteq> None\<close> add.commute assms(1) le_SucI le_eq_less_or_eq le_refl linorder_neqE_nat no_change_if_ge_length_t plus_1_eq_Suc snap_p step_Suc)
    have oq: "occurs_on (t ! j) = q"
    proof (rule ccontr)
      assume "~ occurs_on (t ! j) = q"
      then have "has_snapshotted (S t j) q = has_snapshotted (S t (j+1)) q" 
        using no_state_change_if_no_event step_q by auto
      then show False using snap_q by blast
    qed
    have op: "occurs_on (t ! k) = p"
    proof (rule ccontr)
      assume "~ occurs_on (t ! k) = p"
      then have "has_snapshotted (S t k) p = has_snapshotted (S t (k+1)) p"
        using no_state_change_if_no_event step_p by auto
      then show False using snap_p by blast
    qed
    have "p \<noteq> q" using chan no_self_channel by blast
    then have "j \<noteq> k" using oq op event_occurs_on_unique by blast
    show ?thesis
    proof (cases "j < k")
      case True
      then have "msgs (S t i) cid = msgs (S t j) cid \<and> cs (S t i) cid = cs (S t j) cid"
      proof -
        have "\<forall>k. i \<le> k \<and> k < j \<longrightarrow> occurs_on (t ! k) \<noteq> p \<and> occurs_on (t ! k) \<noteq> q" (is ?Q)
        proof (rule ccontr)
          assume "~ ?Q"
          then obtain l where range: "i \<le> l" "l < j" and "occurs_on (t ! l) = p \<or> occurs_on (t ! l) = q" by blast
          then show False
          proof (elim disjE, goal_cases)
            case 1
            then show ?thesis
            proof (cases "regular_event (t ! l)")
              case True
              have "l < k" using range \<open>j < k\<close> by simp
              have "~ has_snapshotted (S t l) p" using snap_p(1) range \<open>j < k\<close> snapshot_stable_ver_3 assms(1) by simp
              then have "prerecording_event t l" using True "1" prerecording_event 
                using s_def snap_q(1) snap_q(2) by fastforce
              then show False using assms range by blast
            next
              case False
              then have step_l: "(S t l) \<turnstile> t ! l \<mapsto> (S t (l+1))" 
                by (metis (no_types, lifting) Suc_eq_plus1 Suc_lessD True assms(1) distributed_system.step_Suc distributed_system_axioms less_trans_Suc linorder_not_le local.range(2) s_def snap_p(1) snap_p(2) take_all)
              then have "has_snapshotted (S t (l+1)) p" using False nonregular_event_induces_snapshot 
                by (metis "1"(3) snapshot_state_unchanged)
              then show False 
                by (metis Suc_eq_plus1 Suc_leI True assms(1) less_imp_le_nat local.range(2) snap_p(1) snapshot_stable_ver_3)
            qed
          next
            case 2
            then show ?thesis
            proof (cases "regular_event (t ! l)")
              case True
              have "~ has_snapshotted (S t l) q" using snap_q(1) range \<open>j < k\<close> snapshot_stable_ver_3 assms(1) by simp
              then have "prerecording_event t l" using True "2" prerecording_event 
                using s_def snap_q(2) by fastforce
              then show False using assms range by blast
            next
              case False
              then have step_l: "(S t l) \<turnstile> t ! l \<mapsto> (S t (l+1))" 
                by (metis (no_types, lifting) Suc_eq_plus1 Suc_lessD True assms(1) distributed_system.step_Suc distributed_system_axioms less_trans_Suc linorder_not_le local.range(2) s_def snap_p(1) snap_p(2) take_all)
              then have "has_snapshotted (S t (l+1)) q" using False nonregular_event_induces_snapshot 
                by (metis "2"(3) snapshot_state_unchanged)
              then show False 
                by (metis Suc_eq_plus1 Suc_leI assms(1) range(2) snap_q(1) snapshot_stable_ver_3)
            qed
          qed
        qed
        moreover have "j \<le> length t"
        proof (rule ccontr)
          assume "~ j \<le> length t"
          then have "S t j = S t (j+1)" using no_change_if_ge_length_t assms by simp
          then show False using snap_q by auto
        qed
        ultimately show ?thesis using chan same_messages_if_no_occurrence_trace assms less_imp_le bound by blast
      qed
      moreover have "map Msg (fst (cs (S t j) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t j) cid)
                   = map Msg (fst (cs (S t (j+1)) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t (j+1)) cid)
                   \<and> snd (cs (S t (j+1)) cid) = Recording"
      proof -
        have "~ regular_event (t ! j)" using snap_q 
          using regular_event_cannot_induce_snapshot step_q by blast
        moreover have "Marker \<notin> set (msgs (S t j) cid)" 
          by (meson chan True assms(1) computation.no_marker_if_no_snapshot computation.snapshot_stable_ver_2 computation_axioms less_imp_le_nat snap_p(1))
        ultimately show ?thesis using oq snapshot_step_cs_preservation_q step_q chan snap_q(1) by blast
      qed
      moreover have "map Msg (fst (cs (S t k) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t k) cid)
                 = map Msg (fst (cs (S t (j+1)) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t (j+1)) cid)"
      proof -
        have "snd (cs (S t (j+1)) cid) = Recording" using calculation by simp
        moreover have "\<forall>a. j+1 \<le> a \<and> a < k \<longrightarrow> ~ occurs_on (t ! a) = p" (is ?R)
        proof (rule ccontr)
          assume "~ ?R"
          then obtain a where "j+1 \<le> a" "a < k" and ocp: "occurs_on (t ! a) = p" by blast
          have "a < length t"
          proof -
            have "k < length t"
            proof (rule ccontr)
              assume "~ k < length t"
              then have "S t k = S t (k+1)" 
                using assms(1) no_change_if_ge_length_t by auto
              then show False using snap_p by auto
            qed
            then show ?thesis using \<open>a < k\<close> by simp
          qed
          then show False
          proof (cases "regular_event (t ! a)")
            case True
            have "~ has_snapshotted (S t a) p" 
              by (meson \<open>a < k\<close> assms(1) computation.snapshot_stable_ver_2 computation_axioms less_imp_le_nat snap_p(1))
            then have "prerecording_event t a" using \<open>a < length t\<close> ocp True prerecording_event by simp
            then show False using \<open>j+1 \<le> a\<close> \<open>j \<ge> i\<close> assms by auto
          next
            case False
            then have "(S t a) \<turnstile> (t ! a) \<mapsto> (S t (a+1))" 
              using \<open>a < length t\<close> assms(1) step_Suc by auto
            then have "has_snapshotted (S t (a+1)) p" 
              by (metis False ocp nonregular_event_induces_snapshot snapshot_state_unchanged)
            then show False 
              by (metis Suc_eq_plus1 Suc_leI \<open>a < k\<close> assms(1) snap_p(1) snapshot_stable_ver_3)
          qed
        qed
        moreover have "~ has_snapshotted (S t (j+1)) p" 
          by (metis Suc_eq_plus1 Suc_le_eq True assms(1) computation.snapshot_stable_ver_2 computation_axioms snap_p(1))
        ultimately show ?thesis using chan cs_when_recording_2 True assms(1) by auto
      qed
      moreover have "map Msg (fst (cs (S t k) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t k) cid)
                 = map Msg (fst (cs (S t (k+1)) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t (k+1)) cid)"
      proof -
        have "\<not> regular_event (t ! k)"
          using regular_event_preserves_process_snapshots snap_p(1) snap_p(2) step_p by force
        then show ?thesis
          using chan computation.snapshot_step_cs_preservation_p computation_axioms op step_p by fastforce
      qed
      moreover have "map Msg (fst (cs (S t (k+1)) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t (k+1)) cid)
                 = map Msg (fst (cs final cid))"
      proof -
        have f1: "\<forall>f p pa pb c ca es n a na. \<not> computation f p pa pb (c::('a, 'b, 'c) configuration) ca \<or> \<not> distributed_system.trace f p pa pb c es ca \<or> ps (distributed_system.s f p pa pb c es n) a = None \<or> \<not> n \<le> na \<or> ps (distributed_system.s f p pa pb c es na) a \<noteq> None"
          by (meson computation.snapshot_stable_ver_2)
        have f2: "computation channel trans send recv init (S t (length t))"
          using assms(1) final_is_s_t_len_t computation_axioms by blast
        have f3: "trace init t (S t (length t))"
          using assms(1) final_is_s_t_len_t by blast
        have f4: "ps (S t k) p = None"
          by (meson snap_p(1))
        then have f5: "k < length t"
          using f3 f2 f1 by (metis le_eq_less_or_eq not_le s_def snap_p(2) take_all)
        have "\<not> regular_event (t ! k)"
          using f4 by (meson distributed_system.regular_event_cannot_induce_snapshot distributed_system_axioms snap_p(2) step_p)
        then have f6: "map Msg (fst (cs (S t k) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t k) cid) = map Msg (fst (cs (S t (k + 1)) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t (k + 1)) cid) \<and> snd (cs (S t k) cid) = snd (cs (S t (k + 1)) cid)"
          using chan computation.snapshot_step_cs_preservation_p computation_axioms op step_p by fastforce
        then have f7: "snd (cs (S t (k + 1)) cid) \<noteq> Done"
          using f5 f4 by (metis (no_types) assms(1) chan cs_done_implies_both_snapshotted(1))
        have "j + 1 \<le> k + 1"
          using True by linarith
       then have "snd (cs (S t (k + 1)) cid) = Recording"
          using f7 f3 f2 f1 by (meson chan computation.cs_in_initial_state_implies_not_snapshotted recording_state.exhaust snap_q(2))
       then show ?thesis
         using f6 f5 by (metis (no_types) Suc_eq_plus1 Suc_leI assms(1) chan cs_done cs_done_implies_both_snapshotted(1) cs_when_recording final_is_s_t_len_t le_eq_less_or_eq snap_p(2))
      qed
      ultimately show ?thesis 
        by (metis (no_types, lifting) chan Nil_is_map_conv assms(1) computation.no_initial_channel_snapshot computation_axioms fst_conv no_recording_cs_if_not_snapshotted self_append_conv2 snap_q(1))
    next
      case False
      then have "k < j" using \<open>j \<noteq> k\<close> False by simp
      then have "map Msg (fst (cs (S t i) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t i) cid)
               = map Msg (fst (cs (S t j) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t j) cid)"
      proof (cases "i \<le> k")
        case True
        then have "msgs (S t i) cid = msgs (S t k) cid \<and> cs (S t i) cid = cs (S t k) cid"
        proof -
          have "\<forall>j. i \<le> j \<and> j < k \<longrightarrow> occurs_on (t ! j) \<noteq> p \<and> occurs_on (t ! j) \<noteq> q" (is ?Q)
          proof (rule ccontr)
            assume "~ ?Q"
            then obtain l where range: "i \<le> l" "l < k" and "occurs_on (t ! l) = p \<or> occurs_on (t ! l) = q" by blast
            then show False
            proof (elim disjE, goal_cases)
              case 1
              then show ?thesis
              proof (cases "regular_event (t ! l)")
                case True
                have "l < k" using range \<open>k < j\<close> by simp
                have "~ has_snapshotted (S t l) p" using snap_p(1) range \<open>k < j\<close> snapshot_stable_ver_3 assms(1) by simp
                then have "prerecording_event t l" using True "1" prerecording_event 
                  using s_def snap_p by fastforce
                then show False using assms range by blast
              next
                case False
                then have step_l: "(S t l) \<turnstile> t ! l \<mapsto> (S t (l+1))" 
                  by (metis (no_types, lifting) Suc_eq_plus1 Suc_lessD assms(1) distributed_system.step_Suc distributed_system_axioms less_trans_Suc linorder_not_le local.range(2) s_def snap_p(1) snap_p(2) take_all)
                then have "has_snapshotted (S t (l+1)) p" using False nonregular_event_induces_snapshot 
                  by (metis "1"(3) snapshot_state_unchanged)
                then show False 
                  by (metis Suc_eq_plus1 Suc_leI assms(1) local.range(2) snap_p(1) snapshot_stable_ver_3)
              qed
            next
              case 2
              then show ?thesis
              proof (cases "regular_event (t ! l)")
                case True
                have "~ has_snapshotted (S t l) p" using snap_p(1) range \<open>k < j\<close> snapshot_stable_ver_3 assms(1) by simp
                moreover have "l < length t" 
                  using \<open>k < j\<close> local.range(2) s_def snap_q(1) snap_q(2) by force
                ultimately have "prerecording_event t l" using True "2" prerecording_event 
                proof -
                  have "l \<le> j"
                    by (meson False \<open>l < k\<close> less_trans not_less)
                  then show ?thesis
                    by (metis (no_types) True \<open>l < length t\<close> \<open>occurs_on (t ! l) = q\<close> assms(1) computation.prerecording_event computation.snapshot_stable_ver_2 computation_axioms snap_q(1))
                qed
                then show False using assms range by blast
              next
                case False
                then have step_l: "(S t l) \<turnstile> t ! l \<mapsto> (S t (l+1))" 
                  by (metis (no_types, lifting) Suc_eq_plus1 Suc_lessD assms(1) distributed_system.step_Suc distributed_system_axioms less_trans_Suc linorder_not_le local.range(2) s_def snap_p(1) snap_p(2) take_all)
                then have "has_snapshotted (S t (l+1)) q" using False nonregular_event_induces_snapshot 
                  by (metis "2"(3) snapshot_state_unchanged)
                then show False 
                  by (metis Suc_eq_plus1 Suc_leI \<open>k < j\<close> assms(1) less_imp_le_nat local.range(2) snap_q(1) snapshot_stable_ver_3)
              qed
            qed
          qed
          moreover have "k \<le> length t"
          proof (rule ccontr)
            assume "~ k \<le> length t"
            then have "S t k = S t (k+1)" using no_change_if_ge_length_t assms by simp
            then show False using snap_p by auto
          qed
          ultimately show ?thesis using chan same_messages_if_no_occurrence_trace assms True less_imp_le by auto
        qed
        moreover have "map Msg (fst (cs (S t k) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t k) cid)
                   = map Msg (fst (cs (S t (k+1)) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t (k+1)) cid)
                   \<and> snd (cs (S t (k+1)) cid) = NotStarted"
        proof -
          have "~ regular_event (t ! k)" using snap_p 
            using regular_event_cannot_induce_snapshot step_p by blast
          then show ?thesis
            using calculation op snapshot_step_cs_preservation_p step_p chan NotStarted by auto
        qed
        moreover have "map Msg (fst (cs (S t (k+1)) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t (k+1)) cid)
                   = map Msg (fst (cs (S t j) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t j) cid)"
        proof -
          have "\<forall>a. k+1 \<le> a \<and> a < j \<longrightarrow> ~ occurs_on (t ! a) = q" (is ?R)
          proof (rule ccontr)
            assume "~ ?R"
            then obtain a where "k+1 \<le> a" "a < j" and ocp: "occurs_on (t ! a) = q" by blast
            have "a < length t"
            proof -
              have "j < length t"
              proof (rule ccontr)
                assume "~ j < length t"
                then have "S t j = S t (j+1)" 
                  using assms(1) no_change_if_ge_length_t by auto
                then show False using snap_q by auto
              qed
              then show ?thesis using \<open>a < j\<close> by simp
            qed
            then show False
            proof (cases "regular_event (t ! a)")
              case True
              have "~ has_snapshotted (S t a) q" 
                by (meson \<open>a < j\<close> assms(1) computation.snapshot_stable_ver_2 computation_axioms less_imp_le_nat snap_q(1))
              then have "prerecording_event t a" using \<open>a < length t\<close> ocp True prerecording_event by simp
              then show False using \<open>k+1 \<le> a\<close> \<open>k \<ge> i\<close> assms by auto
            next
              case False
              then have "(S t a) \<turnstile> (t ! a) \<mapsto> (S t (a+1))" 
                using \<open>a < length t\<close> assms(1) step_Suc by auto
              then have "has_snapshotted (S t (a+1)) q" 
                by (metis False ocp nonregular_event_induces_snapshot snapshot_state_unchanged)
              then show False 
                by (metis Suc_eq_plus1 Suc_leI \<open>a < j\<close> assms(1) snap_q(1) snapshot_stable_ver_3)
            qed
          qed
          moreover have "Marker : set (msgs (S t (k+1)) cid)" 
            using chan \<open>map Msg (fst (cs (S t k) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t k) cid) = map Msg (fst (cs (S t (k + 1)) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t (k + 1)) cid) \<and> snd (cs (S t (k + 1)) cid) = NotStarted\<close> assms(1) cs_in_initial_state_implies_not_snapshotted marker_must_stay_if_no_snapshot snap_p(2) by blast
          moreover have "has_snapshotted (S t (k+1)) p" 
            using snap_p(2) by blast
          moreover have "~ has_snapshotted (S t (k+1)) q" 
            using chan \<open>map Msg (fst (cs (S t k) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t k) cid) = map Msg (fst (cs (S t (k + 1)) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t (k + 1)) cid) \<and> snd (cs (S t (k + 1)) cid) = NotStarted\<close> assms(1) cs_in_initial_state_implies_not_snapshotted by blast
          moreover have "k+1 \<le> j" 
            using \<open>k < j\<close> by auto
          moreover have "trace init t final" using assms by simp
          moreover have "snd (cs (S t (k+1)) cid) = NotStarted" 
            using \<open>map Msg (fst (cs (S t k) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t k) cid) = map Msg (fst (cs (S t (k + 1)) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t (k + 1)) cid) \<and> snd (cs (S t (k + 1)) cid) = NotStarted\<close> by blast
          ultimately show ?thesis using cs_when_recording_3 chan by simp
        qed
        ultimately show ?thesis by simp
      next
        case False
        show ?thesis
        proof -
          have "has_snapshotted (S t i) p" 
            by (metis False Suc_eq_plus1 assms(1) not_less_eq_eq snap_p(2) snapshot_stable_ver_3)
          moreover have "~ has_snapshotted (S t i) q" 
            using nsq by auto
          moreover have "Marker : set (msgs (S t i) cid)" 
            using chan assms(1) calculation(1) marker_must_stay_if_no_snapshot nsq by blast
          moreover have "\<forall>k. i \<le> k \<and> k < j \<longrightarrow> ~ occurs_on (t ! k) = q" (is ?R)
          proof (rule ccontr)
            assume "~ ?R"
            then obtain k where "i \<le> k" "k < j" and ocp: "occurs_on (t ! k) = q" by blast
            have "k < length t"
            proof -
              have "j < length t"
              proof (rule ccontr)
                assume "~ j < length t"
                then have "S t j = S t (j+1)" 
                  using assms(1) no_change_if_ge_length_t by auto
                then show False using snap_q by auto
              qed
              then show ?thesis using \<open>k < j\<close> by simp
            qed
            then show False
            proof (cases "regular_event (t ! k)")
              case True
              have "~ has_snapshotted (S t k) q" 
                by (meson \<open>k < j\<close> assms(1) computation.snapshot_stable_ver_2 computation_axioms less_imp_le_nat snap_q(1))
              then have "prerecording_event t k" using \<open>k < length t\<close> ocp True prerecording_event by simp
              then show False using \<open>i \<le> j\<close> \<open>k \<ge> i\<close> assms by auto
            next
              case False
              then have "(S t k) \<turnstile> (t ! k) \<mapsto> (S t (k+1))" 
                using \<open>k < length t\<close> assms(1) step_Suc by auto
              then have "has_snapshotted (S t (k+1)) q" 
                by (metis False ocp nonregular_event_induces_snapshot snapshot_state_unchanged)
              then show False 
                by (metis Suc_eq_plus1 Suc_leI \<open>k < j\<close> assms(1) snap_q(1) snapshot_stable_ver_3)
            qed
          qed
          ultimately show ?thesis using cs_when_recording_3 
            using NotStarted assms(1) bound chan by auto
        qed
      qed
      moreover have "map Msg (fst (cs (S t j) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t j) cid)
                   = map Msg (fst (cs final cid))"
      proof (cases "\<exists>q p. t ! j = RecvMarker cid q p")
        case True
        then have "fst (cs (S t j) cid) = fst (cs (S t (j+1)) cid)" 
          using step_q by auto
        moreover have RecvMarker: "t ! j = RecvMarker cid q p"
        proof -
          have "can_occur (t ! j) (S t j)" using happen_implies_can_occur step_q by simp
          then show ?thesis 
            using RecvMarker_given_channel True chan by force
        qed
        moreover have "takeWhile ((\<noteq>) Marker) (msgs (S t j) cid) = []"
        proof -
          have "can_occur (t ! j) (S t j)" using happen_implies_can_occur step_q by simp
          then have "length (msgs (S t j) cid) > 0 \<and> hd (msgs (S t j) cid) = Marker"
            using RecvMarker can_occur_def by auto
          then show ?thesis 
            by (metis (mono_tags, lifting) hd_conv_nth length_greater_0_conv nth_mem set_takeWhileD takeWhile_nth)
        qed
        moreover have "snd (cs (S t (j+1)) cid) = Done" using step_q True by auto
        moreover have "cs (S t (j+1)) cid = cs final cid" using chan calculation cs_done_implies_same_snapshots assms(1) 
          by (metis final_is_s_t_len_t nat_le_linear no_change_if_ge_length_t)
        ultimately show ?thesis 
          by simp
      next
        case False
        have "~ regular_event (t ! j)" 
          using regular_event_preserves_process_snapshots snap_q(1) snap_q(2) step_q by auto
        then have "isSnapshot (t ! j) \<or> isRecvMarker (t ! j)" using nonregular_event by auto
        then have "map Msg (fst (cs (S t j) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t j) cid)
                 = map Msg (fst (cs (S t (j+1)) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t (j+1)) cid)
                 \<and> snd (cs (S t (j+1)) cid) = Recording"
        proof (elim disjE, goal_cases)
          case 1
          have Snapshot: "t ! j = Snapshot q" 
            using "1" oq by auto
          then have "msgs (S t j) cid = msgs (S t (j+1)) cid"
            using \<open>p \<noteq> q\<close> step_q chan by auto
          moreover have "cs (S t (j+1)) cid = (fst (cs (S t j) cid), Recording)"
            using step_q Snapshot chan by simp
          ultimately show ?thesis by simp
        next
          case 2
          obtain cid' r where RecvMarker: "t ! j = RecvMarker cid' q r" 
            by (metis "2" event.collapse(5) oq)
          have "cid \<noteq> cid'"
          proof (rule ccontr)
            assume "~ cid \<noteq> cid'"
            then have "channel cid = channel cid'" by simp
            then have "channel cid' = Some (r, q)" 
              using False RecvMarker \<open>\<not> cid \<noteq> cid'\<close> by blast
            then show False 
              using False RecvMarker \<open>\<not> cid \<noteq> cid'\<close> by blast
          qed
          then have "msgs (S t j) cid = msgs (S t (j+1)) cid"
            using \<open>cid \<noteq> cid'\<close> step_q snap_q RecvMarker chan \<open>p \<noteq> q\<close> by simp
          moreover have "cs (S t (j+1)) cid = (fst (cs (S t j) cid), Recording)"
            using \<open>p \<noteq> q\<close> \<open>cid \<noteq> cid'\<close>step_q snap_q RecvMarker chan by auto
          ultimately show ?thesis by simp
        qed
        moreover have "map Msg (fst (cs (S t (j+1)) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t (j+1)) cid)
                     = map Msg (fst (cs final cid))"
        proof -
          have "snd (cs (S t (j+1)) cid) = Recording" 
            using calculation by blast
          moreover have "has_snapshotted (S t (j+1)) p" 
            by (metis Suc_eq_plus1 Suc_leI \<open>k < j\<close> assms(1) le_add1 snap_p(2) snapshot_stable_ver_3)
          moreover have "has_snapshotted (S t (j+1)) q" using snap_q by auto
          moreover have "j < length t" 
            by (metis (no_types, lifting) chan Suc_eq_plus1 assms(1) cs_done cs_done_implies_both_snapshotted(2) computation.no_change_if_ge_length_t computation.snapshot_stable_ver_3 computation_axioms leI le_Suc_eq snap_q(1) snap_q(2))
          ultimately show ?thesis using cs_when_recording assms(1) cs_done final_is_s_t_len_t
          proof -
            assume a1: "j < length t"
            assume a2: "trace init t final"
            assume a3: "snd (cs (S t (length t)) cid) = Done"
            assume a4: "snd (cs (S t (j + 1)) cid) = Recording"
            assume a5: "ps (S t (j + 1)) p \<noteq> None"
            assume a6: "\<And>t. trace init t final \<Longrightarrow> final = S t (length t)"
            assume a7: "\<And>i j t p cid q. \<lbrakk>i < j; j \<le> length t; trace init t final; ps (S t i) p \<noteq> None; snd (cs (S t i) cid) = Recording; snd (cs (S t j) cid) = Done; channel cid = Some (p, q)\<rbrakk> \<Longrightarrow> map Msg (fst (cs (S t j) cid)) = map Msg (fst (cs (S t i) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t i) cid)"
            have "Suc j < length t"
              using a3 a2 a1 by (metis (no_types) False Suc_eq_plus1 Suc_lessI chan cs_done_implies_has_snapshotted done_only_from_recv_marker snap_q(1) step_q)
            then show ?thesis
              using a7 a6 a5 a4 a3 a2 by (metis (no_types) Suc_eq_plus1 chan nat_le_linear)
          qed
        qed
        ultimately show ?thesis by simp
      qed
      ultimately show ?thesis 
        by (metis (no_types, lifting) Nil_is_map_conv assms(1) assms(3) chan cs_done cs_done_implies_has_snapshotted cs_not_nil_implies_postrecording_event nat_le_linear nsq self_append_conv2 snapshot_stable_ver_3)
    qed
  next
    case Recording
    then obtain j where snap_p: "~ has_snapshotted (S t j) p" "has_snapshotted (S t (j+1)) p" 
      by (metis Suc_eq_plus1 assms(1) exists_snapshot_for_all_p) 
    have snap_q: "has_snapshotted (S t i) q" 
      using Recording assms(1) chan cs_recording_implies_snapshot by blast
    have fst_cs_empty: "cs (S t i) cid = ([], Recording)" (is ?P)
    proof (rule ccontr)
      assume "~ ?P"
      have "snd (cs (S t i) cid) = Recording" using Recording by simp
      moreover have "fst (cs (S t i) cid) \<noteq> []" using \<open>~ ?P\<close> prod.collapse calculation by metis
      ultimately have "\<exists>j. j < i \<and> postrecording_event t j" 
        using assms(1) assms(4) chan cs_not_nil_implies_postrecording_event by blast
      then show False using assms by auto
    qed
    then show ?thesis
    proof -
      have i_less_len_t: "i < length t"
      proof (rule ccontr)
        assume "~ i < length t"
        then have "snd (cs (S t i) cid) = Done" 
          by (metis assms(1) cs_done le_eq_less_or_eq nat_le_linear no_change_if_ge_length_t)
        then show False using Recording by simp
      qed
      then have "map Msg (fst (cs final cid))
          = map Msg (fst (cs (S t i) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t i) cid)"
      proof (cases "j < i")
        case True
        then have "has_snapshotted (S t i) p" 
          by (metis Suc_eq_plus1 Suc_leI assms(1) snap_p(2) snapshot_stable_ver_3)
        moreover have "length t \<le> length t" by simp
        ultimately show ?thesis 
          using Recording chan assms(1) cs_done cs_when_recording final_is_s_t_len_t i_less_len_t by blast
      next
        case False
        text \<open>need to show that next message that comes into the channel must be marker\<close>
        have "\<forall>k. i \<le> k \<and> k < j \<longrightarrow> ~ occurs_on (t ! k) = p" (is ?P)
        proof (rule ccontr)
          assume "~ ?P"
          then obtain k where "i \<le> k" "k < j" "occurs_on (t ! k) = p" by blast
          then show False
          proof (cases "regular_event (t ! k)")
            case True
            then have "prerecording_event t k" 
              by (metis (no_types, hide_lams) \<open>k < j\<close> \<open>occurs_on (t ! k) = p\<close> all_processes_snapshotted_in_final_state assms(1) final_is_s_t_len_t computation.prerecording_event computation_axioms less_trans nat_le_linear not_less snap_p(1) snapshot_stable_ver_2)
            then show ?thesis using assms \<open>i \<le> k\<close> by auto
          next
            case False
            then have step_k: "(S t k) \<turnstile> (t ! k) \<mapsto> (S t (Suc k))" 
              by (metis (no_types, lifting) Suc_leI \<open>k < j\<close> all_processes_snapshotted_in_final_state assms(1) final_is_s_t_len_t le_Suc_eq less_imp_Suc_add linorder_not_less no_change_if_ge_length_t snap_p(1) step_Suc)
            then have "has_snapshotted (S t (Suc k)) p" 
              by (metis False \<open>occurs_on (t ! k) = p\<close> nonregular_event_induces_snapshot snapshot_state_unchanged)
            then have "k \<ge> j" 
              by (metis Suc_leI \<open>k < j\<close> assms(1) snap_p(1) snapshot_stable_ver_3)
            then show False using \<open>k < j\<close> by simp
          qed
        qed
        moreover have "~ has_snapshotted (S t i) p" 
          using False assms(1) snap_p(1) snapshot_stable_ver_3 by auto
        ultimately have to_snapshot: "map Msg (fst (cs (S t j) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t j) cid)
                       = map Msg (fst (cs (S t i) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t i) cid)"
          using False chan Recording assms(1) cs_when_recording_2 by auto
        have step_j: "(S t j) \<turnstile> (t ! j) \<mapsto> (S t (j+1))" 
          by (metis Suc_eq_plus1 Suc_le_eq assms(1) distributed_system.step_Suc distributed_system_axioms computation.no_change_if_ge_length_t computation_axioms le_add1 not_less_eq_eq snap_p(1) snap_p(2))
        then have "map Msg (fst (cs (S t j) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t j) cid)
                 = map Msg (fst (cs (S t (j+1)) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t (j+1)) cid)"
        proof -
          have o: "~ regular_event (t ! j) \<and> occurs_on (t ! j) = p"
            by (metis (no_types, hide_lams) distributed_system.no_state_change_if_no_event distributed_system.regular_event_cannot_induce_snapshot distributed_system_axioms snap_p(1) snap_p(2) step_j)
          then show ?thesis
            using chan snapshot_step_cs_preservation_p step_j by blast
        qed
        moreover have "map Msg (fst (cs final cid))
           = map Msg (fst (cs (S t (j+1)) cid)) @ takeWhile ((\<noteq>) Marker) (msgs (S t (j+1)) cid)"
        proof -
          have "snd (cs (S t (j+1)) cid) = Recording"
          proof -
            have f1: "ps (S t j) p = None"
              by (meson snap_p(1))
            then have f2: "j < length t"
              by (metis (no_types) all_processes_snapshotted_in_final_state assms(1) final_is_s_t_len_t linorder_not_le snapshot_stable_ver_3)
            have "t ! j \<noteq> RecvMarker cid q p"
              using f1 by (metis (no_types) Suc_eq_plus1 assms(1) recv_marker_means_snapshotted step_j)
            then show ?thesis
              using f2 f1 by (meson False assms(1) chan cs_done_implies_both_snapshotted(1) cs_in_initial_state_implies_not_snapshotted cs_not_not_started_stable done_only_from_recv_marker linorder_not_le recording_state.exhaust snap_q snapshot_stable_ver_3 step_j)
          qed
          moreover have "j+1 < length t"
          proof (rule ccontr)
            assume "~ j+1 < length t"
            then have "snd (cs (S t (j+1)) cid) = Done"
              by (metis assms(1) cs_done le_Suc_eq less_imp_Suc_add linorder_not_le no_change_if_ge_length_t)
            then show False using calculation by auto
          qed
          ultimately show ?thesis
            using chan snap_p(2) assms final_is_s_t_len_t cs_when_recording cs_done by blast
        qed
        ultimately show ?thesis using to_snapshot by simp
      qed
      then show ?thesis using fst_cs_empty by simp
    qed
  next
    case Done
    text \<open>msgs must be empty, and cs must also be empty\<close>
    have fst_cs_empty: "fst (cs (S t i) cid) = []"
    proof (rule ccontr)
      assume "~ fst (cs (S t i) cid) = []" 
      then have "fst (cs (S t 0) cid) \<noteq> fst (cs (S t i) cid)" 
        by (metis chan assms(1) cs_not_nil_implies_postrecording_event gr_implies_not0 le0)
      then have "\<exists>j. j < i \<and> postrecording_event t j" 
        using chan \<open>fst (cs (S t i) cid) \<noteq> []\<close> assms(1) assms(4) cs_not_nil_implies_postrecording_event by blast
      then show False using assms by auto
    qed
    moreover have "msgs (S t i) cid = []"
    proof -
      have no_marker: "Marker \<notin> set (msgs (S t i) cid)" (is ?P)
      proof (rule ccontr)
        assume "~ ?P"
        then have "Marker : set (msgs (S t i) cid)" by simp
        then have "snd (cs (S t i) cid) \<noteq> Done" 
          by (metis Marker_in_channel_implies_not_done chan assms(1) nat_le_linear s_def take_all)
        then show False using Done by simp
      qed
      have snap_both: "has_snapshotted (S t i) p \<and> has_snapshotted (S t i) q" 
        by (metis chan Done assms(1) cs_done_implies_both_snapshotted(1) cs_done_implies_has_snapshotted final_is_s_t_len_t computation.all_processes_snapshotted_in_final_state computation_axioms le_refl not_less s_def take_all)
      obtain j where snap_p: "~ has_snapshotted (S t j) p" "has_snapshotted (S t (j+1)) p" 
        by (metis Suc_eq_plus1 assms(1) exists_snapshot_for_all_p)
      have "j < i" 
        by (meson assms(1) not_le_imp_less snap_both snap_p(1) snapshot_stable_ver_2)
      have step_j: "(S t j) \<turnstile> (t ! j) \<mapsto> (S t (j+1))" 
        by (metis Suc_eq_plus1 assms(1) distributed_system.step_Suc distributed_system_axioms computation.no_change_if_ge_length_t computation_axioms le_add1 linorder_not_less snap_p(1) snap_p(2))
      have nonreg_j: "~ regular_event (t ! j)" 
        by (meson distributed_system.regular_event_cannot_induce_snapshot distributed_system_axioms snap_p(1) snap_p(2) step_j)
      have oc_j: "occurs_on (t ! j) = p" 
        using no_state_change_if_no_event snap_p(1) snap_p(2) step_j by force
      have "msgs (S t i) cid = [] \<or> (msgs (S t i) cid \<noteq> [] \<and> last (msgs (S t i) cid) = Marker)"
      proof -
        have "msgs (S t (j+1)) cid \<noteq> [] \<and> last (msgs (S t (j+1)) cid) = Marker"
        proof -
          have "msgs (S t (j+1)) cid = msgs (S t j) cid @ [Marker]"
          proof -
            have "isSnapshot (t ! j) \<or> isRecvMarker (t ! j)" using nonregular_event nonreg_j by blast
            then show ?thesis
            proof (elim disjE, goal_cases)
              case 1
              then have "t ! j = Snapshot p" using oc_j by auto
              then show ?thesis using step_j chan by auto
            next
              case 2
              then obtain cid' r where RecvMarker: "t ! j = RecvMarker cid' p r" 
                by (metis event.collapse(5) oc_j)
              have "cid \<noteq> cid'"
              proof (rule ccontr)
                assume "~ cid \<noteq> cid'"
                then have "channel cid = channel cid'" by auto
                then have "Some (p, q) = Some (r, p)" 
                  by (metis RecvMarker RecvMarker_implies_Marker_in_set assms(1) chan computation.no_marker_if_no_snapshot computation_axioms snap_p(1) step_j)
                then show False using no_self_channel chan by simp
              qed
              then show ?thesis using oc_j snap_p step_j chan RecvMarker by auto
            qed
          qed
          then show ?thesis by auto
        qed
        moreover have "i \<le> length t" using assms by simp
        moreover have "j+1 \<le> i" using \<open>j < i\<close> by simp
        moreover have "\<forall>k. j+1 \<le> k \<and> k < i \<and> regular_event (t ! k) \<longrightarrow> ~ occurs_on (t ! k) = p" (is ?R)
        proof (rule ccontr)
          assume "~ ?R"
          then obtain k where range: "j+1 \<le> k" "k < i" and "regular_event (t ! k)" "occurs_on (t ! k) = p"
            by blast
          then have "postrecording_event t k" using snap_p 
            by (meson assms(1) calculation(2) le_trans linorder_not_less pre_if_regular_and_not_post prerecording_event snapshot_stable_ver_2)
          then show False using assms range by auto
        qed
        ultimately show ?thesis 
          using assms(1) chan last_unchanged_or_empty_if_no_events snap_p(2) by auto
      qed
      then show ?thesis using no_marker last_in_set by fastforce
    qed
    ultimately show ?thesis 
      using chan Done assms(1) assms(4) final_is_s_t_len_t computation.cs_done_implies_same_snapshots computation_axioms by fastforce
  qed
  ultimately show "filter ((\<noteq>) Marker) (msgs (S t i) cid) = map Msg (fst (cs final cid))" by simp
qed

lemma snapshot_after_all_prerecording_events:
  assumes
    "trace init t final" and
    "\<forall>i'. i' \<ge> i \<longrightarrow> ~ prerecording_event t i'" and
    "\<forall>j'. j' < i \<longrightarrow> ~ postrecording_event t j'" and
    "i \<le> length t"
  shows
    "state_equal_to_snapshot (S t i) final"
proof (unfold state_equal_to_snapshot_def, rule conjI)
  show "ps_equal_to_snapshot (S t i) final"
    using assms ps_after_all_prerecording_events by auto
  show "cs_equal_to_snapshot (S t i) final"
    using assms cs_after_all_prerecording_events by auto
qed

subsection \<open>Obtaining the desired traces\<close>

abbreviation all_prerecording_before_postrecording where
  "all_prerecording_before_postrecording t \<equiv> \<exists>i. (\<forall>j. j < i \<longrightarrow> ~ postrecording_event t j)
                                               \<and> (\<forall>j. j \<ge> i \<longrightarrow> ~ prerecording_event t j)
                                               \<and> i \<le> length t
                                               \<and> trace init t final"

definition count_violations :: "('a, 'b, 'c) trace \<Rightarrow> nat" where
  "count_violations t = sum (\<lambda>i. if postrecording_event t i
                                 then card {j \<in> {i+1..<length t}. prerecording_event t j}
                                 else 0)
                        {0..<length t}"

lemma violations_ge_0:
  shows
    "(if postrecording_event t i
     then card {j \<in> {i+1..<length t}. prerecording_event t j}
     else 0) \<ge> 0"
  by simp

lemma count_violations_ge_0:
  shows
    "count_violations t \<ge> 0"
  by simp

lemma violations_0_implies_all_subterms_0:
  assumes
    "count_violations t = 0"
  shows
    "\<forall>i \<in> {0..<length t}. (if postrecording_event t i
                                 then card {j \<in> {i+1..<length t}. prerecording_event t j}
                                 else 0) = 0"
proof -
  have "sum (\<lambda>i. if postrecording_event t i
                                 then card {j \<in> {i+1..<length t}. prerecording_event t j}
                                 else 0)
        {0..<length t} = 0" using count_violations_def assms by simp
  then show "\<forall>i \<in> {0..<length t}. (if postrecording_event t i
                                 then card {j \<in> {i+1..<length t}. prerecording_event t j}
                                 else 0) = 0"
    by auto
qed

lemma exists_postrecording_violation_if_count_greater_0:
  assumes
    "count_violations t > 0"
  shows
    "\<exists>i. postrecording_event t i \<and> card {j \<in> {i+1..<length t}. prerecording_event t j} > 0" (is ?P)
proof (rule ccontr)
  assume "~ ?P"
  then have "\<forall>i. ~ postrecording_event t i \<or> card {j \<in> {i+1..<length t}. prerecording_event t j} = 0" by simp
  have "count_violations t = 0"
  proof (unfold count_violations_def)
    have "\<forall>i. (if postrecording_event t i
             then card {j \<in> {i+1..<length t}. prerecording_event t j}
             else 0) = 0"
      using \<open>\<forall>i. \<not> postrecording_event t i \<or> card {j \<in> {i + 1..<length t}. prerecording_event t j} = 0\<close> by auto
    then show "sum (\<lambda>i. if postrecording_event t i
                          then card {j \<in> {i+1..<length t}. prerecording_event t j}
                          else 0) {0..<length t} = 0" by simp
  qed
  then show False using assms by simp
qed

lemma exists_prerecording_violation_when_card_greater_0:
  assumes
    "card {j \<in> {i+1..<length t}. prerecording_event t j} > 0"
  shows
    "\<exists>j \<in> {i+1..<length t}. prerecording_event t j" 
  by (metis (no_types, lifting) Collect_empty_eq assms card_0_eq empty_subsetI finite_atLeastLessThan not_gr_zero subset_card_intvl_is_intvl)

lemma card_greater_0_if_post_after_pre:
  assumes
    "i < j" and
    "postrecording_event t i" and
    "prerecording_event t j"
  shows
    "card {j \<in> {i+1..<length t}. prerecording_event t j} > 0"
proof -
  have "j < length t" using prerecording_event assms by auto
  have "{j \<in> {i+1..<length t}. prerecording_event t j} \<noteq> empty" 
    using Suc_eq_plus1 \<open>j < length t\<close> assms(1) assms(3) less_imp_triv by auto
  then show ?thesis by fastforce
qed

lemma exists_neighboring_violation_pair:
  assumes
    "trace init t final" and
    "count_violations t > 0"
  shows
    "\<exists>i j. i < j \<and> postrecording_event t i \<and> prerecording_event t j
         \<and> (\<forall>k. (i < k \<and> k < j) \<longrightarrow> ~ regular_event (t ! k)) \<and> j < length t"
proof -
  let ?I = "{i. postrecording_event t i \<and> card {j \<in> {i+1..<length t}. prerecording_event t j} > 0}"
  have nonempty_I: "?I \<noteq> empty" using assms exists_postrecording_violation_if_count_greater_0 by blast
  have fin_I: "finite ?I"
  proof (rule ccontr)
    assume "~ finite ?I"
    then obtain i where "i > length t" "postrecording_event t i" 
      by (simp add: postrecording_event)
    then show False using postrecording_event by simp
  qed
  let ?i = "Max ?I"
  have no_greater_postrec_violation: "\<forall>i. i > ?i \<longrightarrow> ~ (postrecording_event t i \<and> card {j \<in> {i+1..<length t}. prerecording_event t j} > 0)"
    using Max_gr_iff fin_I by blast
  have post_i: "postrecording_event t ?i" 
    using Max_in fin_I nonempty_I by blast
  have "card {j \<in> {?i+1..<length t}. prerecording_event t j} > 0"
  proof -
    have "?i \<in> ?I" 
      using Max_in fin_I nonempty_I by blast
    then show ?thesis by simp
  qed
  let ?J = "{j \<in> {?i+1..<length t}. prerecording_event t j}"
  have nonempty_J: "?J \<noteq> empty"
    using \<open>card {j \<in> {?i+1..<length t}. prerecording_event t j} > 0\<close> exists_prerecording_violation_when_card_greater_0
    by blast
  have fin_J: "finite ?J" by auto
  let ?j = "Min ?J"
  have pre_j: "prerecording_event t ?j"
    using Min_in fin_J nonempty_J by blast
  have no_smaller_prerec_violation: "\<forall>j \<in> {?i+1..<length t}. j < ?j \<longrightarrow> ~ prerecording_event t j" 
    using Min_less_iff fin_J by blast
  have j_less_len_t: "?j < length t"
    using pre_j prerecording_event by blast
  have "\<forall>k. (?i < k \<and> k < ?j) \<longrightarrow> ~ regular_event (t ! k)"
  proof (rule allI, rule impI)
    fix k
    assume asm: "?i < k \<and> k < ?j"
    then show "~ regular_event (t ! k)"
    proof -
      have "0_le_k": "0 \<le> k" by simp
      have k_less_len_t: "k < length t" using j_less_len_t asm by auto
      show ?thesis
      proof (rule ccontr)
        assume reg_event: "~ ~ regular_event (t ! k)"
        then show False
        proof (cases "has_snapshotted (S t k) (occurs_on (t ! k))")
          case True
          then have post_k: "postrecording_event t k" using reg_event k_less_len_t postrecording_event by simp
          moreover have "card {j \<in> {k+1..<length t}. prerecording_event t j} > 0"
            using post_k pre_j card_greater_0_if_post_after_pre asm pre_j by blast
          ultimately show False using no_greater_postrec_violation asm by blast
        next
          case False
          then have pre_k: "prerecording_event t k" using reg_event k_less_len_t prerecording_event by simp
          moreover have "k \<in> {?i+1..<length t}" using asm k_less_len_t by simp
          ultimately show False using no_smaller_prerec_violation asm by blast
        qed
      qed
    qed
  qed
  moreover have "?i < ?j" using nonempty_J by auto
  ultimately show ?thesis using pre_j post_i j_less_len_t by blast
qed

lemma same_cardinality_post_swap_1:
  assumes
    "prerecording_event t j" and
    "postrecording_event t i" and
    "i < j" and
    "j < length t" and
    "count_violations t = Suc n" and
    "\<forall>k. (i < k \<and> k < j) \<longrightarrow> ~ regular_event (t ! k)" and
    "trace init t final"
  shows
    "{k \<in> {0..<i}. prerecording_event t k}
   = {k \<in> {0..<i}. prerecording_event (swap_events i j t) k}"
proof -
  let ?t = "swap_events i j t"
  have same_begin: "take i t = take i ?t" using swap_identical_heads assms by blast
  have same_length: "length t = length (swap_events i j t)" using swap_identical_length assms by blast
  have a: "\<forall>k. k < i \<longrightarrow> t ! k = ?t ! k" 
    by (metis nth_take same_begin)
  then have "\<forall>k. k < i \<longrightarrow> prerecording_event t k = prerecording_event ?t k"
  proof -
    have "\<forall>k. k < i \<longrightarrow> S t k = S ?t k" using assms swap_events by simp
    then show ?thesis unfolding prerecording_event using a same_length by presburger
  qed
  then show ?thesis by auto
qed

lemma same_cardinality_post_swap_2:
  assumes
    "prerecording_event t j" and
    "postrecording_event t i" and
    "i < j" and
    "j < length t" and
    "count_violations t = Suc n" and
    "\<forall>k. (i < k \<and> k < j) \<longrightarrow> ~ regular_event (t ! k)" and
    "trace init t final"
  shows
    "card {k \<in> {i..<j+1}. prerecording_event t k}
   = card {k \<in> {i..<j+1}. prerecording_event (swap_events i j t) k}"
proof -
  let ?t = "swap_events i j t"
  have "card {k \<in> {i..<j+1}. prerecording_event t k} = 1"
  proof -
    have "\<forall>k. i \<le> k \<and> k < j \<longrightarrow> ~ prerecording_event t k"
    proof (rule allI, rule impI)
      fix k
      assume asm: "i \<le> k \<and> k < j"
      then show "~ prerecording_event t k"
      proof (cases "k = i")
        case True
        then have "postrecording_event t k" using assms by simp
        then show ?thesis 
          by (meson computation.postrecording_event computation.prerecording_event computation_axioms)
      next
        case False
        then have "i < k \<and> k < j" using asm by force
        then have "~ regular_event (t ! k)" using assms by simp
        then show ?thesis unfolding prerecording_event by simp
      qed
    qed
    then have "{k \<in> {i..<j}. prerecording_event t k} = empty" by simp
    moreover have "{k \<in> {j..<j+1}. prerecording_event t k} = {j}"
    proof -
      have "{j..<j+1} = {j}" by auto
      moreover have "prerecording_event t j" using assms by simp
      ultimately show ?thesis by blast
    qed
    ultimately have "{k \<in> {i..<j+1}. prerecording_event t k} = {j}" using assms(3-4) by auto
    then show ?thesis by simp
  qed
  moreover have "card {k \<in> {i..<j+1}. prerecording_event ?t k} = 1"
  proof -
    have swap_ind: "prerecording_event ?t i
          \<and> postrecording_event ?t (i+1)
          \<and> (\<forall>k. k > i+1 \<and> k < j+1 \<longrightarrow> ~ regular_event (?t ! k))"
      using assms swap_events by blast
    have "\<forall>k. i+1 \<le> k \<and> k < j+1 \<longrightarrow> ~ prerecording_event ?t k"
    proof (rule allI, rule impI)
      fix k
      assume asm: "i+1 \<le> k \<and> k < j+1"
      then show "~ prerecording_event ?t k"
      proof (cases "k = i+1")
        case True
        then have "postrecording_event ?t k" using swap_ind by blast
        then show ?thesis 
          by (meson computation.postrecording_event computation.prerecording_event computation_axioms)
      next
        case False
        then have "i+1 < k \<and> k < j+1" using asm by linarith
        then have "~ regular_event (?t ! k)" using asm assms swap_ind by blast
        then show ?thesis unfolding prerecording_event by simp
      qed
    qed
    then have "{k \<in> {i+1..<j+1}. prerecording_event ?t k} = empty" by simp
    moreover have "{k \<in> {i..<i+1}. prerecording_event ?t k} = {i}"
    proof -
      have "{i..<i+1} = {i}" by simp
      moreover have "prerecording_event ?t i" using swap_ind by blast
      ultimately show ?thesis by blast
    qed
    ultimately have "{k \<in> {i..<j+1}. prerecording_event ?t k} = {i}" using assms(3-4) by auto
    then show ?thesis by simp
  qed
  ultimately show ?thesis by simp
qed

lemma same_cardinality_post_swap_3:
  assumes
    "prerecording_event t j" and
    "postrecording_event t i" and
    "i < j" and
    "j < length t" and
    "count_violations t = Suc n" and
    "\<forall>k. (i < k \<and> k < j) \<longrightarrow> ~ regular_event (t ! k)" and
    "trace init t final"
  shows
    "{k \<in> {j+1..<length t}. prerecording_event t k}
   = {k \<in> {j+1..<length (swap_events i j t)}. prerecording_event (swap_events i j t) k}"
proof -
  let ?t = "swap_events i j t"
  have "drop (j+1) t = drop (j+1) ?t" 
    using assms(3) assms(4) swap_identical_tails by blast
  have same_length: "length t = length ?t" using swap_identical_length assms by blast
  have a: "\<forall>k. j+1 \<le> k \<and> k < length t \<longrightarrow> ?t ! k = t ! k"
  proof (rule allI, rule impI)
   fix k
    assume "j+1 \<le> k \<and> k < length t"
    then have "?t ! k = drop (j+1) (swap_events i j t) ! (k-(j+1))" 
      by (metis (no_types, lifting) Suc_eq_plus1 Suc_leI assms(4) le_add_diff_inverse nth_drop same_length)
    moreover have "t ! k = drop (j+1) t ! (k-(j+1))" 
      using \<open>j + 1 \<le> k \<and> k < length t\<close> by auto
    ultimately have "drop (j+1) ?t ! (k-(j+1)) = drop (j+1) t ! (k-(j+1))"
      using assms swap_identical_tails by metis
    then show "?t ! k = t ! k" 
      using \<open>?t ! k = drop (j + 1) ?t ! (k - (j + 1))\<close> \<open>t ! k = drop (j + 1) t ! (k - (j + 1))\<close> by auto
  qed
  then have "\<forall>k. j+1 \<le> k \<and> k < length t \<longrightarrow> prerecording_event t k = prerecording_event ?t k"
  proof -
    have "\<forall>k. k \<ge> (j+1) \<longrightarrow> S t k = S ?t k" using assms swap_events by simp
    then show ?thesis unfolding prerecording_event using a by auto
  qed
  then have "{k \<in> {j+1..<length t}. prerecording_event t k}
           = {k \<in> {j+1..<length t}. prerecording_event ?t k}"
    by auto
  then show ?thesis using same_length by metis
qed

lemma card_ip1_to_j_is_1_in_normal_events:
  assumes
    "prerecording_event t j" and
    "postrecording_event t i" and
    "i < j" and
    "j < length t" and
    "count_violations t = Suc n" and
    "\<forall>k. (i < k \<and> k < j) \<longrightarrow> ~ regular_event (t ! k)" and
    "count_violations t = Suc n" and
    "trace init t final"
  shows
    "card {k \<in> {i+1..<j+1}. prerecording_event t k} = 1"
proof -
  have "\<forall>k. i < k \<and> k < j \<longrightarrow> ~ prerecording_event t k"
  proof (rule allI, rule impI)
    fix k
    assume asm: "i < k \<and> k < j"
    then show "~ prerecording_event t k"
    proof -
      have "~ regular_event (t ! k)" using asm assms by blast
      then show ?thesis unfolding prerecording_event by simp
    qed
  qed
  then have "{k \<in> {i+1..<j}. prerecording_event t k} = empty" by auto
  moreover have "{k \<in> {j..<j+1}. prerecording_event t k} = {j}"
  proof -
    have "{j..<j+1} = {j}" by auto
    moreover have "prerecording_event t j" using assms by simp
    then show ?thesis by auto
  qed
  ultimately have "{k \<in> {i+1..<j+1}. prerecording_event t k} = {j}" using assms by auto
  then show ?thesis by simp
qed

lemma card_ip1_to_j_is_0_in_swapped_events:
  assumes
    "prerecording_event t j" and
    "postrecording_event t i" and
    "i < j" and
    "j < length t" and
    "count_violations t = Suc n" and
    "\<forall>k. (i < k \<and> k < j) \<longrightarrow> ~ regular_event (t ! k)" and
    "count_violations t = Suc n" and
    "trace init t final"
  shows
    "card {k \<in> {i+1..<j+1}. prerecording_event (swap_events i j t) k} = 0"
proof -
  let ?t = "swap_events i j t"
  have postrec_ip1: "postrecording_event ?t (i+1)" using assms swap_events by blast
  have neigh_shift: "\<forall>k. i+1 < k \<and> k < j+1 \<longrightarrow> ~ regular_event (?t ! k)" using assms swap_events by blast
  have "\<forall>k. i+1 \<le> k \<and> k < j+1 \<longrightarrow> ~ prerecording_event ?t k"
  proof (rule allI, rule impI)
    fix k
    assume asm: "i+1 \<le> k \<and> k < j+1"
    then show "~ prerecording_event ?t k"
    proof (cases "k = i+1")
      case True
      then show ?thesis using postrec_ip1 
        by (meson computation.postrecording_event computation.prerecording_event computation_axioms)
    next
      case False
      then have "i+1 < k \<and> k < j+1" using asm by simp
      then have "~ regular_event (?t ! k)" using neigh_shift by blast
      then show ?thesis unfolding prerecording_event by simp
    qed
  qed
  then have "{k \<in> {i+1..<j+1}. prerecording_event ?t k} = empty" by auto
  then show ?thesis by simp
qed

lemma count_violations_swap:
  assumes
    "prerecording_event t j" and
    "postrecording_event t i" and
    "i < j" and
    "j < length t" and
    "count_violations t = Suc n" and
    "\<forall>k. (i < k \<and> k < j) \<longrightarrow> ~ regular_event (t ! k)" and
    "count_violations t = Suc n" and
    "trace init t final"
  shows
    "count_violations (swap_events i j t) = n"
proof -
  let ?t = "swap_events i j t"
  let ?f = "(\<lambda>i. if postrecording_event t i then card {j \<in> {i+1..<length t}. prerecording_event t j} else 0)"
  let ?f' = "(\<lambda>i. if postrecording_event ?t i then card {j \<in> {i+1..<length ?t}. prerecording_event ?t j} else 0)"
  have same_postrec_prefix: "\<forall>k. k < i \<longrightarrow> postrecording_event t k = postrecording_event ?t k"
  proof -
    have "\<forall>k. k < i \<longrightarrow> S t k = S ?t k" using assms swap_events by auto
    then show ?thesis unfolding postrecording_event
    proof -
      assume a1: "\<forall>k<i. S t k = S (swap_events i j t) k"
      { fix nn :: nat
        have "\<And>n na es nb. \<not> n < na \<or> \<not> na < length es \<or> \<not> nb < n \<or> swap_events n na es ! nb = (es ! nb::('a, 'b, 'c) event)"
          by (metis (no_types) nth_take swap_identical_heads)
        then have "\<not> nn < i \<or> \<not> nn < length t \<and> \<not> nn < length (swap_events i j t) \<or> \<not> regular_event (t ! nn) \<and> \<not> regular_event (swap_events i j t ! nn) \<or> ps (S t nn) (occurs_on (t ! nn)) = None \<and> ps (S (swap_events i j t) nn) (occurs_on (swap_events i j t ! nn)) = None \<or> regular_event (t ! nn) \<and> regular_event (swap_events i j t ! nn) \<and> nn < length t \<and> nn < length (swap_events i j t) \<and> ps (S t nn) (occurs_on (t ! nn)) \<noteq> None \<and> ps (S (swap_events i j t) nn) (occurs_on (swap_events i j t ! nn)) \<noteq> None"
          using a1 by (metis (no_types) assms(3) assms(4) swap_identical_length) }
      then show "\<forall>n<i. (n < length t \<and> regular_event (t ! n) \<and> ps (S t n) (occurs_on (t ! n)) \<noteq> None) = (n < length (swap_events i j t) \<and> regular_event (swap_events i j t ! n) \<and> ps (S (swap_events i j t) n) (occurs_on (swap_events i j t ! n)) \<noteq> None)"
        by (metis (no_types))
    qed
  qed
  have same_postrec_suffix: "\<forall>k. k \<ge> j+1 \<longrightarrow> postrecording_event t k = postrecording_event ?t k"
  proof -
    have post_equal_states: "\<forall>k. k \<ge> j+1 \<longrightarrow> S t k = S ?t k" using assms swap_events by presburger
    show ?thesis
    proof (rule allI, rule impI)
      fix k
      assume "j+1 \<le> k"
      then show "postrecording_event t k = postrecording_event ?t k"
      proof (cases "k < length t")
        case False
        then have "~ postrecording_event t k" using postrecording_event by simp
        moreover have "~ postrecording_event ?t k"
          using postrecording_event swap_identical_length False assms by metis
        ultimately show ?thesis by simp
      next
        case True
        then show "postrecording_event t k = postrecording_event ?t k"
          using post_equal_states
        proof -
          assume a1: "\<forall>k\<ge>j + 1. S t k = S (swap_events i j t) k"
          assume a2: "k < length t"
          have f3: "length t = length (swap_events i j t)"
            using assms(3) assms(4) swap_identical_length by blast
          have f4: "k - (j + 1) + (j + 1) = k"
            using \<open>j + 1 \<le> k\<close> le_add_diff_inverse2 by blast
          have "drop (j + 1) t = drop (j + 1) (swap_events i j t)"
            using assms(3) assms(4) swap_identical_tails by blast
          then have "swap_events i j t ! k = t ! k"
            using f4 f3 a2 by (metis (no_types) drop_drop hd_drop_conv_nth)
          then show ?thesis
            using f3 a1 \<open>j + 1 \<le> k\<close> postrecording_event by presburger
        qed
      qed
    qed
  qed

  have sum_decomp_f: "sum ?f {0..<length t} = sum ?f {0..<i} + sum ?f {i..<j+1} + sum ?f {j+1..<length t}"
    by (metis (no_types, lifting) One_nat_def add.right_neutral add_Suc_right assms(3) assms(4) discrete le_add2 less_SucI less_or_eq_imp_le sum.atLeastLessThan_concat)
  have sum_decomp_f': "sum ?f' {0..<length t} = sum ?f' {0..<i} + sum ?f' {i..<j+1} + sum ?f' {j+1..<length t}"
    by (metis (no_types, lifting) One_nat_def add.right_neutral add_Suc_right assms(3) assms(4) discrete le_add2 less_SucI less_or_eq_imp_le sum.atLeastLessThan_concat)

  have prefix_sum: "sum ?f {0..<i} = sum ?f' {0..<i}"
  proof -
    have "\<forall>l. 0 \<le> l \<and> l < i \<longrightarrow> ?f l = ?f' l"
    proof (rule allI, rule impI)
      fix l
      assume "0 \<le> l \<and> l < i"
      then have "l < i" by simp
      show "?f l = ?f' l"
      proof (cases "postrecording_event t l")
      case True
        let ?G = "{k \<in> {l+1..<length t}. prerecording_event t k}"
        let ?G' = "{k \<in> {l+1..<length t}. prerecording_event ?t k}"
        let ?A = "{k \<in> {l+1..<i}. prerecording_event t k}"
        let ?B = "{k \<in> {i..<j+1}. prerecording_event t k}"
        let ?C = "{k \<in> {j+1..<length t}. prerecording_event t k}"
        let ?A' = "{k \<in> {l+1..<i}. prerecording_event ?t k}"
        let ?B' = "{k \<in> {i..<j+1}. prerecording_event ?t k}"
        let ?C' = "{k \<in> {j+1..<length t}. prerecording_event ?t k}"
        have card_G: "card ?G = card ?A + card ?B + card ?C"
        proof -
          have "?G = ?A \<union> (?B \<union> ?C)" using assms \<open>l < i\<close> by auto
          then have "card ?G = card (?A \<union> (?B \<union> ?C))" by simp
          also have "card (?A \<union> (?B \<union> ?C)) = card ?A + card (?B \<union> ?C)"
          proof -
            have "?A \<inter> (?B \<union> ?C) = {}" using \<open>l < i\<close> assms by auto
            then show ?thesis by (simp add: card_Un_disjoint disjoint_iff_not_equal)
          qed
          also have "card ?A + card (?B \<union> ?C) = card ?A + card ?B + card ?C"
          proof -
            have "?B \<inter> ?C = {}" by auto
            then show ?thesis by (simp add: card_Un_disjoint disjoint_iff_not_equal)
          qed
          finally show ?thesis by simp
        qed
        have card_G': "card ?G' = card ?A' + card ?B' + card ?C'"
        proof -
          have "?G' = ?A' \<union> (?B' \<union> ?C')" using assms \<open>l < i\<close> by auto
          then have "card ?G' = card (?A' \<union> (?B' \<union> ?C'))" by simp
          also have "card (?A' \<union> (?B' \<union> ?C')) = card ?A' + card (?B' \<union> ?C')"
          proof -
            have "?A' \<inter> (?B' \<union> ?C') = {}" using \<open>l < i\<close> assms by auto
            then show ?thesis by (simp add: card_Un_disjoint disjoint_iff_not_equal)
          qed
          also have "card ?A' + card (?B' \<union> ?C') = card ?A' + card ?B' + card ?C'"
          proof -
            have "?B' \<inter> ?C' = {}" by auto
            then show ?thesis by (simp add: card_Un_disjoint disjoint_iff_not_equal)
          qed
          finally show ?thesis by simp
        qed
        have "card ?G = card ?G'"
        proof -
          have "card ?A = card ?A'"
          proof -
            have "{k \<in> {0..<i}. prerecording_event t k} = {k \<in> {0..<i}. prerecording_event ?t k}"
              using assms same_cardinality_post_swap_1 by blast
            then have "?A = ?A'" by auto
            then show ?thesis by simp
          qed
          moreover have "card ?B = card ?B'" using assms same_cardinality_post_swap_2 by blast
          moreover have "card ?C = card ?C'"
          proof -
            have "?C = ?C'" using assms same_cardinality_post_swap_3 by auto
            then show ?thesis by simp
          qed
          ultimately show ?thesis using card_G card_G' by linarith
        qed
        moreover have "postrecording_event ?t l" using True same_postrec_prefix \<open>l < i\<close> by blast
        moreover have "length ?t = length t" using assms(3) assms(4) by fastforce
        ultimately show ?thesis using True by presburger
      next
        case False
        then have "~ postrecording_event ?t l" using same_postrec_prefix \<open>l < i\<close> by blast
        then show ?thesis using False by simp
      qed
    qed
    then show ?thesis using sum_eq_if_same_subterms by auto
  qed

  have infix_sum: "sum ?f {i..<j+1} = sum ?f' {i..<j+1} + 1"
  proof -
    have sum_decomp_f: "sum ?f {i..<j+1} = sum ?f {i..<i+2} + sum ?f {i+2..<j+1}" 
      by (metis (no_types, lifting) Suc_eq_plus1 Suc_leI add_2_eq_Suc' assms(3) less_Suc_eq linorder_not_le sum.atLeastLessThan_concat)
    have sum_decomp_f': "sum ?f' {i..<j+1} = sum ?f' {i..<i+2} + sum ?f' {i+2..<j+1}" 
      by (metis (no_types, lifting) Suc_eq_plus1 Suc_mono add.assoc assms(3) discrete le_add1 one_add_one sum.atLeastLessThan_concat)
    have "sum ?f {i+2..<j+1} = sum ?f' {i+2..<j+1}"
    proof -
      have "\<forall>l. i+2 \<le> l \<and> l < j+1 \<longrightarrow> ?f l = ?f' l"
      proof (rule allI, rule impI)
        fix l
        assume asm: "i+2 \<le> l \<and> l < j+1"
        have "?f l = 0"
        proof (cases "l = j")
          case True
          then have "~ postrecording_event t l" 
            using assms(1) postrecording_event prerecording_event by auto
          then show ?thesis by simp
        next
          case False
          then have "i < l \<and> l < j" using assms asm by simp
          then have "~ regular_event (t ! l)" using assms by blast
          then have "~ postrecording_event t l" unfolding postrecording_event by simp
          then show ?thesis by simp
        qed
        moreover have "?f' l = 0"
        proof -
          have "\<forall>k. i+1 < k \<and> k < j+1 \<longrightarrow> ~ regular_event (?t ! k)" using assms swap_events by blast 
          then have "~ regular_event (?t ! l)" using asm by simp
          then have "~ postrecording_event ?t l" unfolding postrecording_event by simp
          then show ?thesis by simp
        qed
        ultimately show "?f l = ?f' l" by simp
      qed
      then show ?thesis using sum_eq_if_same_subterms by simp
    qed

    moreover have "sum ?f {i..<i+2} = 1 + sum ?f' {i..<i+2}"
    proof -
      have int_def: "{i..<i+2} = {i,i+1}" by auto
      then have "sum ?f {i,i+1} = ?f i + ?f (i+1)" by simp
      moreover have "sum ?f' {i,i+1} = ?f' i + ?f' (i+1)" using int_def by simp

      moreover have "?f (i+1) = 0"
      proof (cases "j = i+1")
        case True
        then have "prerecording_event t (i+1)" using assms by simp
        then have "~ postrecording_event t (i+1)"
          unfolding postrecording_event using prerecording_event by simp
        then show ?thesis by simp
      next
        case False
        then have "~ regular_event (t ! (i+1))" using assms by simp
        then have "~ postrecording_event t (i+1)" unfolding postrecording_event by simp
        then show ?thesis by simp
      qed
      moreover have "?f' i = 0"
      proof -
        have "prerecording_event ?t i" using assms swap_events by blast
        then have "~ postrecording_event ?t i"
          unfolding postrecording_event using prerecording_event by simp
        then show ?thesis by simp
      qed
      moreover have "?f i = ?f' (i+1) + 1"
      proof -
        have pi: "postrecording_event t i" using assms by simp
        moreover have pip1: "postrecording_event ?t (i+1)" using assms swap_events by blast
        let ?G = "{k \<in> {i+1..<length t}. prerecording_event t k}"
        let ?G' = "{k \<in> {i+2..<length ?t}. prerecording_event ?t k}"
        let ?A = "{k \<in> {i+1..<j+1}. prerecording_event t k}"
        let ?B = "{k \<in> {j+1..<length t}. prerecording_event t k}"
        let ?A' = "{k \<in> {i+2..<j+1}. prerecording_event ?t k}"
        let ?B' = "{k \<in> {j+1..<length ?t}. prerecording_event ?t k}"
        have card_G: "card ?G = card ?A + card ?B"
        proof -
          have "?G = ?A \<union> ?B" using assms by auto
          moreover have "?A \<inter> ?B = {}" by auto
          ultimately show ?thesis by (simp add: card_Un_disjoint disjoint_iff_not_equal)
        qed
        have card_G': "card ?G' = card ?A' + card ?B'"
        proof -
          have "?G' = ?A' \<union> ?B'" using assms by auto
          moreover have "?A' \<inter> ?B' = {}" by auto
          ultimately show ?thesis by (simp add: card_Un_disjoint disjoint_iff_not_equal)
        qed
        have "card ?G = card ?G' + 1"
        proof -
          have "card ?A = card ?A' + 1"
          proof -
            have "card ?A = 1" using assms card_ip1_to_j_is_1_in_normal_events by blast
            moreover have "card ?A' = 0" using assms card_ip1_to_j_is_0_in_swapped_events by force
            ultimately show ?thesis by algebra
          qed
          moreover have "card ?B = card ?B'" using assms same_cardinality_post_swap_3 by force
          ultimately show ?thesis using card_G card_G' by presburger
        qed
        moreover have "card ?G = ?f i" using pi by simp
        moreover have "card ?G' = ?f' (i+1)" using pip1 by simp
        ultimately show ?thesis by argo
      qed
      ultimately show ?thesis by auto
    qed

    ultimately show ?thesis using sum_decomp_f sum_decomp_f' by linarith
  qed

  have suffix_sum: "sum ?f {j+1..<length t} = sum ?f' {j+1..<length t}"
  proof -
    have "\<forall>l. l > j \<longrightarrow> ?f l = ?f' l"
    proof (rule allI, rule impI)
      fix l
      assume "l > j"
      then show "?f l = ?f' l"
      proof (cases "postrecording_event t l")
        case True
        let ?G = "{k \<in> {l+1..<length t}. prerecording_event t k}"
        let ?G' = "{k \<in> {l+1..<length t}. prerecording_event ?t k}"
        let ?C = "{k \<in> {j+1..<length t}. prerecording_event t k}"
        let ?C' = "{k \<in> {j+1..<length t}. prerecording_event ?t k}"
        have "card ?G = card ?G'"
        proof -
          have "?C = ?C'" using assms same_cardinality_post_swap_3 by auto
          then have "?G = ?G'" using \<open>l > j\<close> by fastforce
          then show ?thesis by simp
        qed
        moreover have "postrecording_event ?t l" using True same_postrec_suffix \<open>l > j\<close> by simp
        moreover have "length ?t = length t" using assms(3) assms(4) by fastforce
        ultimately show ?thesis using True by presburger
      next
        case False
        then have "~ postrecording_event ?t l" using same_postrec_suffix \<open>l > j\<close> by simp
        then show ?thesis using False by simp
      qed
    qed
    then have "\<forall>k. j+1 \<le> k \<and> k < length t \<longrightarrow> ?f k = ?f' k"
      using discrete by blast
    moreover have "length t = length ?t" 
      using assms(3) assms(4) swap_identical_length by blast
    ultimately show ?thesis by (blast intro:sum_eq_if_same_subterms)
  qed
  have "sum ?f {0..<length t} = sum ?f' {0..<length t} + 1"
  proof -
    have "sum ?f {0..<i} = sum ?f' {0..<i}" using prefix_sum by simp
    moreover have "sum ?f {i..<j+1} = sum ?f' {i..<j+1} + 1" using infix_sum by simp
    moreover have "sum ?f {j+1..<length t} = sum ?f' {j+1..<length t}" using suffix_sum by simp
    ultimately show ?thesis using sum_decomp_f sum_decomp_f' by presburger
  qed
  moreover have "length ?t = length t" 
    using assms(3) assms(4) by auto
  moreover have "sum ?f {0..<length t} = n + 1" using assms count_violations_def by simp
  ultimately have "sum ?f' {0..<length ?t} = n" by presburger
  then show ?thesis unfolding count_violations_def by presburger
qed

lemma desired_trace_always_exists:
  assumes
    "trace init t final"
  shows
    "\<exists>t'. perm t' t
        \<and> all_prerecording_before_postrecording t'"
using assms proof (induct "count_violations t" arbitrary: t)
  case 0
  then show ?case
  proof (cases "\<exists>i. prerecording_event t i")
    case False
    then have "\<forall>j. ~ prerecording_event t j" by auto
    then have "\<forall>j. j \<le> 0 \<longrightarrow> ~ postrecording_event t j" 
      using "0.prems" init_is_s_t_0 no_initial_process_snapshot postrecording_event by auto
    moreover have "\<forall>j. j > 0 \<longrightarrow> ~ prerecording_event t j"  using False by auto
    moreover have "length t > 0" 
      by (metis "0.prems" all_processes_snapshotted_in_final_state length_greater_0_conv no_initial_process_snapshot tr_init trace_and_start_determines_end)
    ultimately show ?thesis using "0.prems" False by auto
  next
    case True
    let ?Is = "{i. prerecording_event t i}"
    have "?Is \<noteq> empty"
      by (simp add: True)
    moreover have fin_Is: "finite ?Is"
    proof (rule ccontr)
      assume "~ finite ?Is"
      then obtain i where "i > length t" "prerecording_event t i" 
        by (simp add: prerecording_event)
      then show False using prerecording_event by auto
    qed
    let ?i = "Max ?Is"
    have pi: "prerecording_event t ?i" 
      using Max_in calculation fin_Is by blast
    have "?i < length t"
    proof (rule ccontr)
      assume "~ ?i < length t"
      then show False 
        using calculation fin_Is computation.prerecording_event computation_axioms by force
    qed
    moreover have "\<forall>j. j \<ge> ?i+1 \<longrightarrow> ~ prerecording_event t j"
    proof -
      have "\<forall>j. j > ?i \<longrightarrow> ~ prerecording_event t j"
        using Max_less_iff fin_Is by auto
      then show ?thesis by auto
    qed
    moreover have "\<forall>j. j < ?i+1 \<longrightarrow> ~ postrecording_event t j"
    proof -
      have "\<forall>j. j \<le> ?i \<longrightarrow> ~ postrecording_event t j"
      proof (rule allI, rule impI, rule ccontr)
        fix j
        assume "j \<le> ?i" "~ ~ postrecording_event t j"
        then have "j < ?i" 
          by (metis add_diff_inverse_nat dual_order.antisym le_add1 pi postrecording_event prerecording_event)
        then have "count_violations t > 0"
        proof -
          have "(if postrecording_event t j
                   then card {l \<in> {j+1..<length t}. prerecording_event t l}
                   else 0) = card {l \<in> {j+1..<length t}. prerecording_event t l}"
            using \<open>~ ~ postrecording_event t j\<close> by simp
          moreover have "card {l \<in> {j+1..<length t}. prerecording_event t l} > 0"
          proof -
            have "j + 1 \<le> ?i \<and> ?i < length t" 
              using \<open>Max {i. prerecording_event t i} < length t\<close> \<open>j < Max {i. prerecording_event t i}\<close> discrete by blast
            moreover have "prerecording_event t ?i" using pi by simp
            ultimately have "{l \<in> {j+1..<length t}. prerecording_event t l} \<noteq> empty" by fastforce
            then show ?thesis by fastforce
          qed
          ultimately show ?thesis
            by (metis (no_types, lifting) violations_0_implies_all_subterms_0 \<open>Max {i. prerecording_event t i} < length t\<close> \<open>j < Max {i. prerecording_event t i}\<close> atLeastLessThan_iff less_trans linorder_not_le neq0_conv)
        qed
        then show False using "0" by simp
      qed
      then show ?thesis by auto
    qed
    moreover have "?i+1 \<le> length t" 
      using calculation(2) discrete by blast
    ultimately show ?thesis using "0.prems" by blast
  qed
next
  case (Suc n)
  then obtain i j where ind: "postrecording_event t i" "prerecording_event t j"
                             "\<forall>k. (i < k \<and> k < j) \<longrightarrow> ~ regular_event (t ! k)"
                             "i < j" "j < length t" using exists_neighboring_violation_pair Suc by force
  then have "trace init (swap_events i j t) final
          \<and> (\<forall>k. k \<ge> j + 1 \<longrightarrow> S (swap_events i j t) k = S t k)
          \<and> (\<forall>k. k \<le> i \<longrightarrow> S (swap_events i j t) k = S t k)"
    using Suc swap_events by presburger
  moreover have "perm (swap_events i j t) t" using swap_events_perm ind by blast
  moreover have "count_violations (swap_events i j t) = n"
    using count_violations_swap Suc ind by simp
  ultimately show ?case using Suc.hyps by blast
qed

theorem snapshot_algorithm_is_correct:
  assumes
    "trace init t final"
  shows
    "\<exists>t' i. trace init t' final \<and> perm t' t
          \<and> state_equal_to_snapshot (S t' i) final \<and> i \<le> length t'"
proof -
  obtain t' where "perm t' t" and
                  "all_prerecording_before_postrecording t'"
    using assms desired_trace_always_exists by blast
  then show ?thesis using snapshot_after_all_prerecording_events
    by blast
qed

subsection \<open>Stable property detection\<close>

text \<open>Finally, we show that the computed snapshot is indeed
suitable for stable property detection, as claimed in~\cite{chandy}.\<close>

definition stable where
  "stable p \<equiv> (\<forall>c. p c \<longrightarrow> (\<forall>t c'. trace c t c' \<longrightarrow> p c'))"

lemma has_snapshot_stable:
  assumes
    "trace init t final"
  shows
    "stable (\<lambda>c. has_snapshotted c p)" 
  using snapshot_stable stable_def by auto

definition some_snapshot_state where
  "some_snapshot_state t \<equiv>
     SOME (t', i). trace init t final
                 \<and> trace init t' final \<and> perm t' t
                 \<and> state_equal_to_snapshot (S t' i) final"

lemma split_S:
  assumes
    "trace init t final"
  shows
    "trace (S t i) (drop i t) final"
proof -
  have "t = take i t @ drop i t" by simp
  then show ?thesis
    by (metis split_trace assms exists_trace_for_any_i
              trace_and_start_determines_end)
qed

theorem Stable_Property_Detection:
  assumes
    "stable p" and
    "trace init t final" and
    "(t', i) = some_snapshot_state t" and
    "p (S t' i)"
  shows
    "p final"
proof -
  have "\<exists>t' i. trace init t final
             \<and> trace init t' final \<and> perm t' t
             \<and> state_equal_to_snapshot (S t' i) final"
    using snapshot_algorithm_is_correct assms(2) by blast
  then have "trace init t' final"
    using assms
    unfolding some_snapshot_state_def
    by (metis (lifting) case_prodD case_prodI someI_ex)
  then show ?thesis
    using assms stable_def split_S by metis
qed

end (* locale computation *)

end (* theory Snapshot *)
