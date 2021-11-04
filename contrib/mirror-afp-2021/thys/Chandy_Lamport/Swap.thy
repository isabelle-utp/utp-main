section \<open>Swap lemmas\<close>

text \<open>\<close>

theory Swap
  imports
    Distributed_System

begin

context distributed_system

begin

lemma swap_msgs_Trans_Trans:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isTrans ev" and
    "isTrans ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e i = msgs e' i"
proof -
  let ?p = "occurs_on ev"
  let ?q = "occurs_on ev'"
  obtain u u' where "ev = Trans ?p u u'" 
    by (metis assms(3) event.collapse(1))
  obtain u'' u''' where "ev' = Trans ?q u'' u'''" 
    by (metis assms(4) event.collapse(1))
  then have "msgs d' i = msgs d i" 
    by (metis Trans_msg assms(1) assms(3) assms(4) assms(5))
  then have "msgs e i = msgs e' i" 
    using Trans_msg assms(2) assms(3) assms(4) assms(6) by auto
  then show ?thesis by blast
qed

lemma swap_msgs_Send_Send:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isSend ev" and
    "isSend ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e i = msgs e' i"
proof -
  let ?p = "occurs_on ev"
  let ?q = "occurs_on ev'"
  obtain i' r u u' m where Send_ev: "ev = Send i' ?p r u u' m" 
    by (metis assms(3) event.collapse(2))
  obtain i'' s u'' u''' m' where Send_ev': "ev' = Send i'' ?q s u'' u''' m'" 
    by (metis assms(4) event.collapse(2))
  have "i' \<noteq> i''"
    by (metis (mono_tags, lifting) \<open>ev = Send i' (occurs_on ev) r u u' m\<close> \<open>ev' = Send i'' (occurs_on ev') s u'' u''' m'\<close> assms(1) assms(2) assms(7) can_occur_def event.simps(27) happen_implies_can_occur option.simps(1) prod.simps(1))
  then show ?thesis
  proof (cases "i = i' \<or> i = i''")
    case True
    then show ?thesis
    proof (elim disjE)
      assume "i = i'"
      then have "msgs d i = msgs c i @ [Msg m]" 
        by (metis \<open>ev = Send i' (occurs_on ev) r u u' m\<close> assms(1) next_send)
      moreover have "msgs e i = msgs d i" 
        by (metis \<open>ev' = Send i'' (occurs_on ev') s u'' u''' m'\<close> \<open>i = i'\<close> \<open>i' \<noteq> i''\<close> assms(2) assms(4) event.sel(8) msgs_unchanged_for_other_is regular_event)
      moreover have "msgs d' i = msgs c i" 
        by (metis \<open>ev' = Send i'' (occurs_on ev') s u'' u''' m'\<close> \<open>i = i'\<close> \<open>i' \<noteq> i''\<close> assms(4) assms(5) event.sel(8) msgs_unchanged_for_other_is regular_event)
      moreover have "msgs e' i = msgs d' i @ [Msg m]" 
        by (metis \<open>ev = Send i' (occurs_on ev) r u u' m\<close> \<open>i = i'\<close> assms(6) next_send)
      ultimately show ?thesis by simp
    next
      assume "i = i''"
      then have "msgs d i = msgs c i" 
        by (metis Send_ev \<open>i' \<noteq> i''\<close> assms(1) assms(3) event.sel(8) msgs_unchanged_for_other_is regular_event)
      moreover have "msgs e i = msgs d i @ [Msg m']" 
        by (metis Send_ev' \<open>i = i''\<close> assms(2) next_send)
      moreover have "msgs d' i = msgs c i @ [Msg m']" 
        by (metis Send_ev' \<open>i = i''\<close> assms(5) next_send)
      moreover have "msgs e' i = msgs d' i" 
        by (metis Send_ev \<open>i = i''\<close> \<open>i' \<noteq> i''\<close> assms(3) assms(6) event.sel(8) msgs_unchanged_for_other_is regular_event)
      ultimately show ?thesis by simp
    qed
  next
    case False
    then have "msgs e i = msgs d i" using Send_ev' assms 
      by (metis event.sel(8) msgs_unchanged_for_other_is regular_event)
    also have "... = msgs c i" 
      by (metis False Send_ev assms(1) assms(3) event.sel(8) msgs_unchanged_for_other_is regular_event)
    also have "... = msgs d' i" 
      by (metis (no_types, hide_lams) \<open>msgs d i = msgs c i\<close> assms(2) assms(4) assms(5) calculation regular_event same_messages_imply_same_resulting_messages)
    also have "... = msgs e' i" 
      by (metis (no_types, hide_lams) \<open>msgs c i = msgs d' i\<close> \<open>msgs d i = msgs c i\<close> assms(1) assms(3) assms(6) regular_event same_messages_imply_same_resulting_messages)
    finally show ?thesis by simp
  qed
qed

lemma swap_msgs_Recv_Recv:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isRecv ev" and
    "isRecv ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e i = msgs e' i"
proof -
  let ?p = "occurs_on ev"
  let ?q = "occurs_on ev'"
  obtain i' r u u' m where Recv_ev: "ev = Recv i' ?p r u u' m" 
    by (metis assms(3) event.collapse(3))
  obtain i'' s u'' u''' m' where Recv_ev': "ev' = Recv i'' ?q s u'' u''' m'" 
    by (metis assms(4) event.collapse(3))
  have "i' \<noteq> i''" 
    by (metis Recv_ev Recv_ev' assms(1) assms(2) assms(7) can_occur_Recv happen_implies_can_occur option.simps(1) prod.simps(1))
  show ?thesis
  proof (cases "i = i' \<or> i = i''")
    case True
    then show ?thesis
    proof (elim disjE)
      assume "i = i'"
      then have "Msg m # msgs d i = msgs c i" using Recv_ev assms by (metis next_recv)
      moreover have "msgs e i = msgs d i" 
        by (metis Recv_ev' \<open>i = i'\<close> \<open>i' \<noteq> i''\<close> assms(2) assms(4) event.sel(9) msgs_unchanged_for_other_is regular_event)
      moreover have "msgs d' i = msgs c i" 
        by (metis Recv_ev' \<open>i = i'\<close> \<open>i' \<noteq> i''\<close> assms(4) assms(5) event.sel(9) msgs_unchanged_for_other_is regular_event)
      moreover have "Msg m # msgs e' i = msgs d' i" 
        by (metis Recv_ev \<open>i = i'\<close> assms(6) next_recv)
      ultimately show ?thesis by (metis list.inject)
    next
      assume "i = i''"
      then have "msgs d i = msgs c i" 
        by (metis Recv_ev \<open>i' \<noteq> i''\<close> assms(1) assms(3) event.sel(9) msgs_unchanged_for_other_is regular_event)
      moreover have "Msg m' # msgs e i = msgs d i" 
        by (metis Recv_ev' \<open>i = i''\<close> assms(2) next_recv)
      moreover have "Msg m' # msgs d' i = msgs c i" 
        by (metis Recv_ev' \<open>i = i''\<close> assms(5) next_recv)
      moreover have "msgs e' i = msgs d' i" 
        by (metis Recv_ev \<open>i = i''\<close> \<open>i' \<noteq> i''\<close> assms(3) assms(6) event.sel(9) msgs_unchanged_for_other_is regular_event)
      ultimately show ?thesis by (metis list.inject)
    qed
  next
    case False
    then have "msgs e i = msgs d i" 
      by (metis Recv_ev' assms(2) assms(4) event.sel(9) msgs_unchanged_for_other_is regular_event)
    also have "... = msgs c i" 
      by (metis False Recv_ev assms(1) assms(3) event.sel(9) msgs_unchanged_for_other_is regular_event)
    also have "... = msgs d' i" 
      by (metis (no_types, hide_lams) \<open>msgs d i = msgs c i\<close> assms(2) assms(4) assms(5) calculation regular_event same_messages_imply_same_resulting_messages)
    also have "... = msgs e' i" 
      by (metis (no_types, lifting) \<open>msgs c i = msgs d' i\<close> \<open>msgs d i = msgs c i\<close> assms(1) assms(3) assms(6) regular_event same_messages_imply_same_resulting_messages)
    finally show ?thesis by simp
  qed
qed

lemma swap_msgs_Send_Trans:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isSend ev" and
    "isTrans ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e i = msgs e' i"
proof -
  let ?p = "occurs_on ev"
  let ?q = "occurs_on ev'"
  obtain i' r u u' m where Send: "ev = Send i' ?p r u u' m" 
    by (metis assms(3) event.collapse(2))
  obtain u'' u''' where Trans: "ev' = Trans ?q u'' u'''" 
    by (metis assms(4) event.collapse(1))
  show ?thesis
  proof (cases "i = i'")
    case True
    then have "msgs d i = msgs c i @ [Msg m]" 
      by (metis Send assms(1) next_send)
    moreover have "msgs e i = msgs d i"
      using Trans_msg assms(2) assms(4) by auto
    moreover have "msgs d' i = msgs c i" 
      using Trans_msg assms(4) assms(5) by auto
    moreover have "msgs e' i = msgs d' i @ [Msg m]" 
      by (metis Send True assms(6) next_send)
    ultimately show ?thesis by simp 
  next
    case False
    then have "msgs e i = msgs d i" 
      using Trans_msg assms(2) assms(4) by auto
    also have "... = msgs c i" 
      by (metis False Send assms(1) assms(3) event.sel(8) msgs_unchanged_for_other_is regular_event)
    also have "... = msgs d' i" 
      using Trans_msg assms(4) assms(5) by blast
    also have "... = msgs e' i" 
      by (metis (no_types, lifting) \<open>msgs c i = msgs d' i\<close> \<open>msgs d i = msgs c i\<close> assms(1) assms(3) assms(6) regular_event same_messages_imply_same_resulting_messages)
    finally show ?thesis by simp
  qed
qed

lemma swap_msgs_Trans_Send:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isTrans ev" and
    "isSend ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e i = msgs e' i"
  using assms swap_msgs_Send_Trans by auto

lemma swap_msgs_Recv_Trans:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isRecv ev" and
    "isTrans ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e i = msgs e' i"
proof -
  let ?p = "occurs_on ev"
  let ?q = "occurs_on ev'"
  obtain i' r u u' m where Recv: "ev = Recv i' ?p r u u' m" 
    by (metis assms(3) event.collapse(3))
  obtain u'' u''' where Trans: "ev' = Trans ?q u'' u'''" 
    by (metis assms(4) event.collapse(1))
  show ?thesis
  proof (cases "i = i'")
    case True
    then have "Msg m # msgs d i = msgs c i" 
      by (metis Recv assms(1) next_recv)
    moreover have "msgs e i = msgs d i" 
      using Trans_msg assms(2) assms(4) by auto
    moreover have "msgs d' i = msgs c i" 
      using Trans_msg assms(4) assms(5) by auto
    moreover have "Msg m # msgs e' i = msgs d' i" 
      by (metis Recv True assms(6) next_recv)
    ultimately show ?thesis by (metis list.inject) 
  next
    case False
    then have "msgs e i = msgs d i" 
      using Trans_msg assms(2) assms(4) by auto
    also have "... = msgs c i" 
      by (metis False Recv assms(1) assms(3) event.sel(9) msgs_unchanged_for_other_is regular_event)
    also have "... = msgs d' i" 
      using Trans_msg assms(4) assms(5) by blast
    also have "... = msgs e' i" 
      by (metis False Recv assms(6) next_recv)
    finally show ?thesis by simp
  qed
qed

lemma swap_msgs_Trans_Recv:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isTrans ev" and
    "isRecv ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e i = msgs e' i"
  using assms swap_msgs_Recv_Trans by auto

lemma swap_msgs_Send_Recv:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isSend ev" and
    "isRecv ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e i = msgs e' i"
proof -
  let ?p = "occurs_on ev"
  let ?q = "occurs_on ev'"
  obtain i' r u u' m where Send: "ev = Send i' ?p r u u' m" 
    by (metis assms(3) event.collapse(2))
  obtain i'' s u'' u''' m' where Recv: "ev' = Recv i'' ?q s u'' u''' m'" 
    by (metis assms(4) event.collapse(3))
  show ?thesis
  proof (cases "i = i'"; cases "i = i''", goal_cases)
    case 1
    then have "msgs e' i = msgs d' i @ [Msg m]" 
      by (metis Send assms(6) next_send)
    moreover have "Msg m' # msgs d' i = msgs c i" 
      by (metis "1"(2) Recv assms(5) next_recv)
    moreover have "msgs d i = msgs c i @ [Msg m]" 
      by (metis "1"(1) Send assms(1) next_send)
    moreover have "Msg m' # msgs e i = msgs d i" 
      by (metis "1"(2) Recv assms(2) next_recv)
    ultimately show ?thesis 
      by (metis list.sel(2) list.sel(3) not_Cons_self2 tl_append2)
  next
    case 2
    then have "msgs d i = msgs c i @ [Msg m]" 
      by (metis Send assms(1) next_send)
    moreover have "msgs e i = msgs d i" 
      by (metis "2"(2) Recv assms(2) assms(4) event.sel(9) msgs_unchanged_for_other_is regular_event)
    moreover have "msgs d' i = msgs c i" 
      by (metis "2"(2) Recv assms(4) assms(5) event.sel(9) msgs_unchanged_for_other_is regular_event)
    moreover have "msgs e' i = msgs d' i @ [Msg m]" 
      by (metis Send 2(1) assms(6) next_send)
    ultimately show ?thesis by simp 
  next
    assume 3: "i \<noteq> i'" "i = i''"
    then have "msgs d i = msgs c i" 
      by (metis Send assms(1) assms(3) event.sel(8) msgs_unchanged_for_other_is regular_event)
    moreover have "Msg m' # msgs e i = msgs d i" using 3 Recv assms by (metis next_recv)
    moreover have "Msg m' # msgs d' i = msgs c i" 
      by (metis "3"(2) Recv assms(5) next_recv)
    moreover have "msgs e' i = msgs d' i" 
      by (metis "3"(1) Send assms(6) next_send)
    ultimately show ?thesis by (metis list.inject)
  next
    assume 4: "i \<noteq> i'" "i \<noteq> i''"
    then have "msgs e i = msgs d i" 
      by (metis Recv assms(2) assms(4) event.sel(9) msgs_unchanged_for_other_is regular_event)
    also have "... = msgs c i" 
      by (metis "4"(1) Send assms(1) assms(3) event.sel(8) msgs_unchanged_for_other_is regular_event)
    also have "... = msgs d' i" 
      by (metis "4"(2) Recv assms(5) next_recv)
    also have "... = msgs e' i" 
      by (metis "4"(1) Send assms(6) next_send)
    finally show ?thesis by simp
  qed
qed

lemma swap_msgs_Recv_Send:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isRecv ev" and
    "isSend ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e i = msgs e' i"
  using assms swap_msgs_Send_Recv by auto

lemma same_cs_implies_same_resulting_cs:
  assumes
    "cs c i = cs d i"
    "c \<turnstile> ev \<mapsto> c'" and
    "d \<turnstile> ev \<mapsto> d'" and
    "regular_event ev"
  shows
    "cs c' i = cs d' i"
proof -
  have "isTrans ev \<or> isSend ev \<or> isRecv ev" using assms by simp
  then show ?thesis
  proof (elim disjE)
    assume "isTrans ev"
    then show ?thesis 
      by (metis (no_types, lifting) assms(1) assms(2) assms(3) assms(4) event.distinct_disc(4) no_cs_change_if_no_event)
  next
    assume "isSend ev"
    then show ?thesis 
      by (metis (no_types, lifting) assms(1) assms(2) assms(3) assms(4) event.distinct_disc(10) no_cs_change_if_no_event)
  next
    assume "isRecv ev"
    then obtain i' r s u u' m where Recv: "ev = Recv i' r s u u' m" 
      by (meson isRecv_def)
    then show ?thesis
    proof (cases "i' = i")
      case True
      with assms Recv show ?thesis by (cases "snd (cs c i) = Recording", auto)
    next
      case False
      then show ?thesis using assms Recv by simp
    qed
  qed
qed

lemma regular_event_implies_same_channel_snapshot_Recv_Recv:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isRecv ev" and
    "isRecv ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "cs e i = cs e' i"
proof -
  let ?p = "occurs_on ev"
  let ?q = "occurs_on ev'"
  obtain i' r u u' m where Recv_ev: "ev = Recv i' ?p r u u' m" 
    by (metis assms(3) event.collapse(3))
  obtain i'' s u'' u''' m' where Recv_ev': "ev' = Recv i'' ?q s u'' u''' m'" 
    by (metis assms(4) event.collapse(3))
  have "i' \<noteq> i''" 
    by (metis Recv_ev Recv_ev' assms(1) assms(5) assms(7) can_occur_Recv happen_implies_can_occur option.simps(1) prod.simps(1))
  show ?thesis
  proof (cases "i = i' \<or> i = i''")
    case True
    then show ?thesis
    proof (elim disjE)
      assume "i = i'"
      then have "cs d' i = cs c i" 
        using assms(4) assms(5) assms(7) no_cs_change_if_no_event
        by (metis Recv_ev' \<open>i' \<noteq> i''\<close> event.sel(9) regular_event)
      then have "cs e' i = cs d i" 
        using assms(1) assms(3) assms(6) distributed_system.same_cs_implies_same_resulting_cs distributed_system_axioms regular_event by blast
      then have "cs d i = cs e i" 
        by (metis Recv_ev' \<open>i = i'\<close> \<open>i' \<noteq> i''\<close> assms(2) assms(4) event.sel(9) no_cs_change_if_no_event regular_event)
      then show ?thesis
        by (simp add: \<open>cs e' i = cs d i\<close>)
    next
      assume "i = i''"
      then have "cs d i = cs c i" 
        by (metis Recv_ev \<open>i' \<noteq> i''\<close> assms(1) assms(3) event.sel(9) no_cs_change_if_no_event regular_event)
      then have "cs e i = cs d' i"
        using assms(2) assms(4) assms(5) regular_event same_cs_implies_same_resulting_cs by blast
      then have "cs d' i = cs e' i" 
        by (metis Recv_ev \<open>i = i''\<close> \<open>i' \<noteq> i''\<close> assms(3) assms(6) event.sel(9) no_cs_change_if_no_event regular_event)
      then show ?thesis 
        by (simp add: \<open>cs e i = cs d' i\<close>)
    qed
  next
    case False
    then show ?thesis 
      by (metis Recv_ev Recv_ev' assms(1) assms(2) assms(5) assms(6) next_recv)
  qed
qed

lemma regular_event_implies_same_channel_snapshot_Recv:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "~ isRecv ev" and
    "regular_event ev" and
    "isRecv ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "cs e i = cs e' i"
proof -
  let ?p = "occurs_on ev"
  let ?q = "occurs_on ev'"
  obtain i' s u'' u''' m' where Recv: "ev' = Recv i' ?q s u'' u''' m'" 
    by (metis assms(5) event.collapse(3))
  show ?thesis
  proof (cases "i = i'")
    case True
    then have "cs d i = cs c i" 
      using assms(1) assms(3) assms(7) no_cs_change_if_no_event \<open>regular_event ev\<close> \<open>~ isRecv ev\<close> by auto
    then have "cs e i = cs d' i"
      using assms(2) assms(5) assms(6) regular_event same_cs_implies_same_resulting_cs by blast
    then have "cs d' i = cs e' i" 
      using True assms(3) assms(6) assms(7) no_cs_change_if_no_event \<open>regular_event ev\<close> \<open>~ isRecv ev\<close> by auto
    then show ?thesis 
      by (simp add: \<open>cs e i = cs d' i\<close>)
  next
    case False
    then have "cs d i = cs c i" 
      using assms(1) assms(3) assms(4) no_cs_change_if_no_event by auto
    then have "cs d' i = cs e i" 
      by (metis (no_types, lifting) assms(2) assms(5) assms(6) regular_event same_cs_implies_same_resulting_cs)
    then show "cs e i = cs e' i" 
      using assms(3) assms(4) assms(7) no_cs_change_if_no_event by auto 
  qed
qed

lemma same_messages_2:
  assumes
    "\<forall>p. has_snapshotted c p = has_snapshotted d p" and
    "msgs c i = msgs d i" and
    "c \<turnstile> ev \<mapsto> c'" and
    "d \<turnstile> ev \<mapsto> d'" and
    "~ regular_event ev"
  shows
    "msgs c' i = msgs d' i"
proof (cases "channel i = None")
  case True
  then show ?thesis 
    using assms(2) assms(3) assms(4) no_msgs_change_if_no_channel by auto
next
  case False
  then obtain p q where chan: "channel i = Some (p, q)" by auto
  have "isSnapshot ev \<or> isRecvMarker ev"
    using assms(5) event.exhaust_disc by auto
  then show ?thesis
  proof (elim disjE)
    assume "isSnapshot ev"
    then obtain r where Snapshot: "ev = Snapshot r" by (meson isSnapshot_def)
    then show ?thesis
    proof (cases "r = p")
      case True
      then have "msgs c' i = msgs c i @ [Marker]" using chan Snapshot assms by simp
      moreover have "msgs d' i = msgs d i @ [Marker]" using chan Snapshot assms True by simp
      ultimately show ?thesis using assms by simp
    next
      case False
      then have "msgs c' i = msgs c i" using chan Snapshot assms by simp
      moreover have "msgs d' i = msgs d i" using chan Snapshot assms False by simp
      ultimately show ?thesis using assms by simp
    qed
  next
    assume "isRecvMarker ev"
    then obtain i' r s where RecvMarker: "ev = RecvMarker i' r s"
      by (meson isRecvMarker_def)
    then show ?thesis
    proof (cases "has_snapshotted c r")
      case snap: True
      then show ?thesis
      proof (cases "i = i'")
        case True
        then have "Marker # msgs c' i = msgs c i" using chan RecvMarker assms snap by simp
        moreover have "Marker # msgs d' i = msgs d i" using chan RecvMarker assms snap True by simp
        ultimately show ?thesis using assms by (metis list.inject)
      next
        case False
        then have "msgs d' i = msgs d i" 
          using RecvMarker assms(1) assms(4) snap by auto
        also have "... = msgs c i" using assms by simp
        also have "... = msgs c' i" 
          using False RecvMarker snap assms by auto
        finally show ?thesis using snap by simp
      qed
    next
      case no_snap: False
      then show ?thesis
      proof (cases "i = i'")
        case True
        then have "Marker # msgs c' i = msgs c i" using chan RecvMarker assms by simp
        moreover have "Marker # msgs d' i = msgs d i" using chan RecvMarker assms True by simp
        ultimately show ?thesis using assms by (metis list.inject)
      next
        case not_i: False
        then show ?thesis
        proof (cases "r = p")
          case True
          then have "msgs c' i = msgs c i @ [Marker]"
            using no_snap RecvMarker assms True chan not_i by auto
          moreover have "msgs d' i = msgs d i @ [Marker]"
          proof -
            have "~ has_snapshotted d r" using assms no_snap True by simp
            then show ?thesis
              using no_snap RecvMarker assms True chan not_i by auto
          qed
          ultimately show ?thesis using assms by simp
        next
          case False
          then have "msgs c i = msgs c' i" using False RecvMarker no_snap chan assms not_i by simp
          moreover have "msgs d' i = msgs d i"
          proof -
            have "~ has_snapshotted d r" using assms no_snap False by simp
            then show ?thesis
              using False RecvMarker no_snap chan assms not_i by simp
          qed
          ultimately show ?thesis using assms by simp
        qed
      qed
    qed
  qed
qed

lemma same_cs_2:
  assumes
    "\<forall>p. has_snapshotted c p = has_snapshotted d p" and
    "cs c i = cs d i" and
    "c \<turnstile> ev \<mapsto> c'" and
    "d \<turnstile> ev \<mapsto> d'"
  shows
    "cs c' i = cs d' i"
proof (cases "channel i = None")
  case True
  then show ?thesis 
    using assms(2) assms(3) assms(4) no_cs_change_if_no_channel by auto
next
  case False
  then obtain p q where chan: "channel i = Some (p, q)" by auto
  then show ?thesis
  proof (cases ev)
    case (Snapshot r)
    with assms chan show ?thesis by (cases "r = q", auto)
  next
    case (RecvMarker i' r s)
    then show ?thesis
    proof (cases "has_snapshotted c r")
      case snap: True
      then have sdr: "has_snapshotted d r" using assms by auto
      then show ?thesis
      proof (cases "i = i'")
        case True
        then have "cs c' i = (fst (cs c i), Done)" 
          using RecvMarker assms(3) next_recv_marker by blast
        also have "... = cs d' i" 
          using RecvMarker True assms(2) assms(4) by auto
        finally show ?thesis using True by simp
      next
        case False
        then have "cs c' i = cs c i" using RecvMarker assms snap by auto
        also have "... = cs d' i" using RecvMarker assms snap sdr False by auto
        finally show ?thesis by simp
      qed
    next
      case no_snap: False
      then have nsdr: "~ has_snapshotted d r" using assms by blast
      show ?thesis
      proof (cases "i = i'")
        case True
        then have "cs c' i = (fst (cs c i), Done)" 
          using RecvMarker assms(3) next_recv_marker by blast
        also have "... = cs d' i" 
          using RecvMarker True assms(2) assms(4) by auto
        finally show ?thesis using True by simp
      next
        case not_i: False
        with assms RecvMarker chan no_snap show ?thesis by (cases "r = q", auto)
      qed
    qed
  next
    case (Trans r u u')
    then show ?thesis 
      by (metis assms(2) assms(3) assms(4) event.disc(1) regular_event same_cs_implies_same_resulting_cs)
  next
    case (Send i' r s u u' m)
    then show ?thesis 
      by (metis assms(2) assms(3) assms(4) event.disc(7) regular_event same_cs_implies_same_resulting_cs)
  next
    case (Recv i' r s u u' m)
    then show ?thesis  
      by (metis assms(2) assms(3) assms(4) event.disc(13) regular_event same_cs_implies_same_resulting_cs)
  qed
qed

lemma swap_Snapshot_Trans:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isSnapshot ev" and
    "isTrans ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e i = msgs e' i"
proof -
  let ?p = "occurs_on ev"
  let ?q = "occurs_on ev'"
  have "ev = Snapshot ?p"
    by (metis assms(3) event.collapse(4))
  obtain u'' u''' where "ev' = Trans ?q u'' u'''" 
    by (metis assms(4) event.collapse(1))
  have "msgs c i = msgs d' i" 
    using Trans_msg assms(4) assms(5) by blast
  then have "msgs e' i = msgs d i"
  proof -
    have "\<forall>p. has_snapshotted c p = has_snapshotted d' p" 
      using assms(4) assms(5) regular_event_preserves_process_snapshots by auto
    moreover have "msgs c i = msgs d' i" using \<open>msgs c i = msgs d' i\<close> by auto
    moreover have "c \<turnstile> ev \<mapsto> d" using assms by auto
    moreover have "d' \<turnstile> ev \<mapsto> e'" using assms by auto
    moreover have "~ regular_event ev" using assms by auto
    ultimately show ?thesis by (blast intro: same_messages_2[symmetric])
  qed
  then have "msgs d i = msgs e i" 
    using Trans_msg assms(2) assms(4) by blast
  then show ?thesis 
    by (simp add: \<open>msgs e' i = msgs d i\<close>)
qed

lemma swap_msgs_Trans_RecvMarker:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isRecvMarker ev" and
    "isTrans ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e' i = msgs e i"
proof -
  have nr: "~ regular_event ev" 
    using assms(3) nonregular_event by blast
  let ?p = "occurs_on ev"
  let ?q = "occurs_on ev'"
  obtain i' r where RecvMarker: "ev = RecvMarker i' ?p r"
    by (metis assms(3) event.collapse(5))
  obtain u'' u''' where Trans: "ev' = Trans ?q u'' u'''" 
    by (metis assms(4) event.collapse(1))
  have "msgs c i = msgs d' i" 
    using Trans_msg assms(4) assms(5) by blast
  then have "msgs e' i = msgs d i"
  proof -
    have "\<forall>p. has_snapshotted d' p = has_snapshotted c p" 
      using assms(4) assms(5) regular_event_preserves_process_snapshots by auto
    moreover have "~ regular_event ev" using assms by auto
    moreover have "\<forall>n. msgs d' n = msgs c n" (* why does he need this assumption? *)
      by (metis Trans assms(5) local.next.simps(3))
    ultimately show ?thesis
      using assms(1) assms(6) same_messages_2 by blast
  qed
  thm same_messages_2
  then have "msgs d i = msgs e i" 
    using Trans_msg assms(2) assms(4) by blast
  then show ?thesis 
    by (simp add: \<open>msgs e' i = msgs d i\<close>)
qed

lemma swap_Trans_Snapshot:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isTrans ev" and
    "isSnapshot ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e i = msgs e' i"
  using assms swap_Snapshot_Trans by auto

lemma swap_Send_Snapshot:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isSend ev" and
    "isSnapshot ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e i = msgs e' i"
proof (cases "channel i = None")
  case True
  then show ?thesis 
    by (metis assms(1) assms(2) assms(5) assms(6) no_msgs_change_if_no_channel)
next
  case False
  then obtain p q where chan: "channel i = Some (p, q)" by auto
  let ?p = "occurs_on ev"
  let ?q = "occurs_on ev'"
  obtain i' r u u' m where Send: "ev = Send i' ?p r u u' m" 
    by (metis assms(3) event.collapse(2))
  have Snapshot: "ev' = Snapshot ?q" 
    by (metis assms(4) event.collapse(4))
  show ?thesis
  proof (cases "i = i'"; cases "p = ?q")
    assume asm: "i = i'" "p = ?q"
    then have "?p = p"
    proof -
      have "channel i' = Some (p, q)" using chan asm by simp
      then show ?thesis using assms can_occur_def Send chan 
        by (metis (mono_tags, lifting) event.simps(27) happen_implies_can_occur option.inject prod.inject)
    qed
    then show ?thesis using assms asm by simp
  next
    assume "i = i'" "p \<noteq> ?q"
    then have "msgs d i = msgs c i @ [Msg m]" 
      by (metis Send assms(1) next_send)
    moreover have "msgs e i = msgs d i" 
      by (metis Pair_inject Snapshot \<open>p \<noteq> occurs_on ev'\<close> assms(2) chan next_snapshot option.inject)
    moreover have "msgs d' i = msgs c i"
      by (metis Pair_inject Snapshot \<open>p \<noteq> occurs_on ev'\<close> assms(5) chan next_snapshot option.inject)
    moreover have "msgs e' i = msgs d' i @ [Msg m]" 
      by (metis Send \<open>i = i'\<close> assms(6) next_send)
    ultimately show ?thesis by simp
  next
    assume asm: "i \<noteq> i'" "p = ?q"
    then have "msgs d i = msgs c i" 
      by (metis Send assms(1) assms(3) event.sel(8) msgs_unchanged_for_other_is regular_event)
    moreover have "msgs e i = msgs c i @ [Marker]" 
      by (metis (full_types) Snapshot asm(2) assms(2) calculation chan next_snapshot)
    moreover have "msgs d' i = msgs c i @ [Marker]" 
      by (metis (full_types) Snapshot asm(2) assms(5) chan next_snapshot)
    moreover have "msgs e' i = msgs d' i" 
      by (metis Send asm(1) assms(6) next_send)
    ultimately show ?thesis by simp
  next
    assume "i \<noteq> i'" "p \<noteq> ?q"
    then have "msgs c i = msgs d i" 
      by (metis Send assms(1) assms(3) event.sel(8) msgs_unchanged_for_other_is regular_event)
    then have "msgs e i = msgs d' i"
      by (metis Pair_inject Snapshot \<open>p \<noteq> occurs_on ev'\<close> assms(2,5) chan next_snapshot option.inject)
    then show ?thesis 
      by (metis Send \<open>i \<noteq> i'\<close> assms(6) next_send)
  qed
qed

lemma swap_Snapshot_Send:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isSnapshot ev" and
    "isSend ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e i = msgs e' i"
  using assms swap_Send_Snapshot by auto

lemma swap_Recv_Snapshot:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isRecv ev" and
    "isSnapshot ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e i = msgs e' i"
proof (cases "channel i = None")
  case True
  then show ?thesis 
    by (metis assms(1) assms(2) assms(5) assms(6) no_msgs_change_if_no_channel)
next
  case False
  then obtain p q where chan: "channel i = Some (p, q)" by auto
  let ?p = "occurs_on ev"
  let ?q = "occurs_on ev'"
  obtain i' r u u' m where Recv: "ev = Recv i' ?p r u u' m" 
    by (metis assms(3) event.collapse(3))
  have Snapshot: "ev' = Snapshot ?q" 
    by (metis assms(4) event.collapse(4))
  show ?thesis
  proof (cases "i = i'"; cases "p = ?q")
    assume "i = i'" "p = ?q"
    then have "Msg m # msgs d i = msgs c i" 
      by (metis Recv assms(1) next_recv)
    moreover have "msgs e i = msgs d i @ [Marker]" 
      by (metis (full_types) Snapshot \<open>p = occurs_on ev'\<close> assms(2) chan next_snapshot)
    moreover have "msgs d' i = msgs c i @ [Marker]" 
      by (metis (full_types) Snapshot \<open>p = occurs_on ev'\<close> assms(5) chan next_snapshot)
    moreover have "Msg m # msgs e' i = msgs d' i" 
      by (metis Recv \<open>i = i'\<close> assms(6) next_recv)
    ultimately show ?thesis 
      by (metis list.sel(3) neq_Nil_conv tl_append2)
  next
    assume "i = i'" "p \<noteq> ?q"
    then have "Msg m # msgs d i = msgs c i" 
      by (metis Recv assms(1) next_recv)
    moreover have "msgs e i = msgs d i"
      by (metis Pair_inject Snapshot \<open>p \<noteq> occurs_on ev'\<close> assms(2) chan next_snapshot option.inject)
    moreover have "msgs d' i = msgs c i"
      by (metis Pair_inject Snapshot \<open>p \<noteq> occurs_on ev'\<close> assms(5) chan next_snapshot option.inject)
    moreover have "Msg m # msgs e' i = msgs d' i" 
      by (metis Recv \<open>i = i'\<close> assms(6) next_recv)
    ultimately show ?thesis by (metis list.inject)
  next
    assume "i \<noteq> i'" "p = ?q"
    then have "msgs d i = msgs c i" 
      by (metis Recv assms(1) next_recv)
    moreover have "msgs e i = msgs d i @ [Marker]" 
      by (metis (full_types) Snapshot \<open>p = occurs_on ev'\<close> assms(2) chan next_snapshot)
    moreover have "msgs d' i = msgs c i @ [Marker]" 
      by (metis (full_types) Snapshot \<open>p = occurs_on ev'\<close> assms(5) chan next_snapshot)
    moreover have "msgs e' i = msgs d' i" 
      by (metis Recv \<open>i ~= i'\<close> assms(6) next_recv)
    ultimately show ?thesis by simp
  next
    assume "i \<noteq> i'" "p \<noteq> ?q"
    then have "msgs d i = msgs c i" 
      by (metis Recv assms(1) next_recv)
    moreover have "msgs e i = msgs d i"
      by (metis Pair_inject Snapshot \<open>p \<noteq> occurs_on ev'\<close> assms(2) chan next_snapshot option.inject)
    moreover have "msgs d' i = msgs c i"
      by (metis Pair_inject Snapshot \<open>p \<noteq> occurs_on ev'\<close> assms(5) chan next_snapshot option.inject)
    moreover have "msgs e' i = msgs d' i" 
      by (metis Recv \<open>i ~= i'\<close> assms(6) next_recv)
    ultimately show ?thesis by auto
  qed
qed

lemma swap_Snapshot_Recv:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isSnapshot ev" and
    "isRecv ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e i = msgs e' i"
  using assms swap_Recv_Snapshot by auto

lemma swap_msgs_Recv_RecvMarker:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isRecv ev" and
    "isRecvMarker ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e i = msgs e' i"
proof (cases "channel i = None")
  case True
  then show ?thesis 
    by (metis assms(1) assms(2) assms(5) assms(6) no_msgs_change_if_no_channel)
next
  case False
  then obtain p q where chan: "channel i = Some (p, q)" by auto
  obtain i' p' r u u' m where Recv: "ev = Recv i' p' r u u' m" 
    by (metis assms(3) event.collapse(3))
  obtain i'' q' s where RecvMarker: "ev' = RecvMarker i'' q' s" 
    by (metis assms(4) event.collapse(5))
  have "i' \<noteq> i''"
  proof (rule ccontr)
    assume "~ i' \<noteq> i''"
    then have "channel i' = channel i''" by auto
    then have "Some (r, p') = Some (s, q')" using assms can_occur_def Recv RecvMarker by simp
    then show False using assms 
      by (metis Recv RecvMarker event.sel(3,5) option.inject prod.inject)
  qed
  then show ?thesis
  proof (cases "i = i' \<or> i = i''")
    case True
    then show ?thesis
    proof (elim disjE)
      assume "i = i'"
      then have pqrp: "(p, q) = (r, p')" 
        by (metis Recv assms(1) chan distributed_system.can_occur_Recv distributed_system_axioms next_recv option.inject)
      then show ?thesis
      proof (cases "has_snapshotted c q'")
        case snap: True
        then have "Msg m # msgs d i = msgs c i" 
          by (metis Recv \<open>i = i'\<close> assms(1) next_recv)
        moreover have "msgs c i = msgs d' i" 
          using RecvMarker \<open>i = i'\<close> \<open>i' \<noteq> i''\<close> assms(5) msgs_unchanged_if_snapshotted_RecvMarker_for_other_is snap by blast
        moreover have "msgs d i = msgs e i" 
          using RecvMarker \<open>i = i'\<close> \<open>i' \<noteq> i''\<close> assms(1) assms(2) snap snapshot_state_unchanged by auto
        moreover have "Msg m # msgs e' i = msgs d' i" 
          by (metis Recv \<open>i = i'\<close> assms(6) next_recv)
        ultimately show ?thesis by (metis list.inject)
      next
        case no_snap: False
        then have msgs_d: "Msg m # msgs d i = msgs c i" 
          by (metis Recv \<open>i = i'\<close> assms(1) next_recv)
        then show ?thesis
        proof (cases "q' = r")
          case True
          then have "msgs d' i = msgs c i @ [Marker]"
          proof -
            have "channel i = Some (q', q)" 
              using True chan pqrp by blast
            then show ?thesis using RecvMarker assms no_snap 
              by (simp add: no_snap \<open>i = i'\<close> \<open>i' \<noteq> i''\<close>)
          qed
          moreover have "Msg m # msgs e' i = msgs d' i" 
            by (metis Recv \<open>i = i'\<close> assms(6) next_recv)
          moreover have "msgs e i = msgs d i @ [Marker]"
          proof -
            have "ps d q' = ps c q'" 
              using assms(1) assms(7) no_state_change_if_no_event RecvMarker by auto
            then show ?thesis
              using RecvMarker \<open>i = i'\<close> \<open>i' \<noteq> i''\<close> assms True chan no_snap pqrp by simp
          qed
          ultimately show ?thesis using msgs_d 
            by (metis append_self_conv2 list.inject list.sel(3) message.distinct(1) tl_append2)
        next
          case False
          then have "msgs e i = msgs d i"
          proof -
            have "~ has_snapshotted d q'" 
              using assms(1) assms(7) no_snap no_state_change_if_no_event RecvMarker by auto
            moreover have "\<nexists>r. channel i = Some (q', r)" using chan False pqrp by auto
            moreover have "i \<noteq> i''" using \<open>i = i'\<close> \<open>i' \<noteq> i''\<close> by simp
            ultimately show ?thesis using RecvMarker assms by simp
          qed
          moreover have "msgs d' i = msgs c i"
          proof -
            have "\<nexists>r. channel i = Some (q', r)" 
              using False chan pqrp by auto
            moreover have "i \<noteq> i''" using \<open>i = i'\<close> \<open>i' \<noteq> i''\<close> by simp
            ultimately show ?thesis using RecvMarker assms(5) no_snap by auto
          qed
          moreover have "Msg m # msgs e' i = msgs d' i" 
            by (metis Recv \<open>i = i'\<close> assms(6) next_recv)
          ultimately show ?thesis using msgs_d 
            by (metis list.inject)
        qed
      qed
    next
      assume "i = i''"
      then have "msgs d i = msgs c i" using assms
        by (metis Recv \<open>i' \<noteq> i''\<close> next_recv) 
      moreover have "msgs e i = msgs d' i"
      proof -
        have "\<forall>p. has_snapshotted c p = has_snapshotted d p" 
          by (metis Recv assms(1) next_recv)
        then show ?thesis 
          by (meson assms(2) assms(5) calculation same_messages_2 same_messages_imply_same_resulting_messages)
      qed
      moreover have "msgs e' i = msgs d' i"
        using assms by (metis Recv \<open>i' \<noteq> i''\<close> \<open>i = i''\<close> next_recv)
      ultimately show ?thesis by simp
    qed
  next
    assume asm: "~ (i = i' \<or> i = i'')"
    then have "msgs c i = msgs d i" 
      by (metis Recv assms(1) assms(3) event.distinct_disc(16,18) event.sel(9) msgs_unchanged_for_other_is nonregular_event)
    then have "msgs d' i = msgs e i"
    proof -
      have "\<forall>p. has_snapshotted c p = has_snapshotted d p" 
        using assms(1) assms(3) regular_event_preserves_process_snapshots by auto
      then show ?thesis 
        by (meson \<open>msgs c i = msgs d i\<close> assms(2) assms(5) same_messages_2 same_messages_imply_same_resulting_messages)
    qed
    then show ?thesis 
      by (metis Recv asm assms(3) assms(6) event.distinct_disc(16,18) event.sel(9) msgs_unchanged_for_other_is nonregular_event)
  qed
qed

lemma swap_RecvMarker_Recv:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isRecvMarker ev" and
    "isRecv ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e i = msgs e' i"
  using assms swap_msgs_Recv_RecvMarker by auto

lemma swap_msgs_Send_RecvMarker:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isSend ev" and
    "isRecvMarker ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e i = msgs e' i"
proof (cases "channel i = None")
  case True
  then show ?thesis 
    by (metis assms(1) assms(2) assms(5) assms(6) no_msgs_change_if_no_channel)
next
  case False
  then obtain p q where chan: "channel i = Some (p, q)" by auto
  let ?p = "occurs_on ev"
  let ?q = "occurs_on ev'"
  obtain i' p' r u u' m where Send: "ev = Send i' p' r u u' m" 
    by (metis assms(3) event.collapse(2))
  obtain i'' q' s where RecvMarker: "ev' = RecvMarker i'' q' s" 
    by (metis assms(4) event.collapse(5))
  have "p' \<noteq> q'" using Send RecvMarker assms by simp
  show ?thesis
  proof (cases "i = i'"; cases "i = i''", goal_cases)
    case 1
    then have "msgs e' i = msgs d' i @ [Msg m]" 
      by (metis Send assms(6) next_send)
    moreover have "Marker # msgs d' i = msgs c i" using \<open>i = i''\<close> RecvMarker assms by simp
    moreover have "msgs d i = msgs c i @ [Msg m]" 
      by (metis "1"(1) Send assms(1) next_send)
    moreover have "Marker # msgs e i = msgs d i" using \<open>i = i''\<close> RecvMarker assms by simp
    ultimately show ?thesis 
      by (metis append_self_conv2 list.inject list.sel(3) message.distinct(1) tl_append2)
  next
    case 2
    then have pqpr: "(p, q) = (p', r)" using chan Send can_occur_def assms by simp
    then have "msgs d i = msgs c i @ [Msg m]" 
      by (metis 2(1) Send assms(1) next_send)
    moreover have "msgs e' i = msgs d' i @ [Msg m]" 
      by (metis "2"(1) Send assms(6) next_send)
    moreover have "msgs d' i = msgs c i"
    proof -
      have "\<nexists>r. channel i = Some (q', r)" using \<open>p' \<noteq> q'\<close> chan pqpr by simp
      with RecvMarker \<open>i \<noteq> i''\<close> \<open>i = i'\<close> assms show ?thesis by (cases "has_snapshotted c q'", auto)
    qed
    moreover have "msgs e i = msgs d i"
    proof -
      have "\<nexists>r. channel i = Some (q', r)" using \<open>p' \<noteq> q'\<close> chan pqpr by simp
      with RecvMarker \<open>i \<noteq> i''\<close> \<open>i = i'\<close> assms show ?thesis by (cases "has_snapshotted d q'", auto)
    qed
    ultimately show ?thesis by simp
  next
    assume 3: "i \<noteq> i'" "i = i''"
    then have mcd: "msgs c i = msgs d i" 
      by (metis Send assms(1) next_send)
    moreover have "msgs e i = msgs d' i"
    proof -
      have "\<forall>p. has_snapshotted c p = has_snapshotted d p" 
        using assms(1) assms(3) regular_event_preserves_process_snapshots by auto
      moreover have "~ regular_event ev'" using assms by auto
      ultimately show ?thesis using mcd assms(2,5) by (blast intro: same_messages_2[symmetric])
    qed
    moreover have "msgs e' i = msgs d' i" 
      by (metis "3"(1) Send assms(6) next_send)
    ultimately show ?thesis by simp
  next
    assume 4: "i \<noteq> i'" "i \<noteq> i''"
    have mcd: "msgs c i = msgs d i" 
      by (metis "4"(1) Send assms(1) assms(3) event.distinct_disc(12,14) event.sel(8) msgs_unchanged_for_other_is nonregular_event)
    have "msgs d' i = msgs e i"
    proof -
      have "\<forall>p. has_snapshotted c p = has_snapshotted d p" 
        using assms(1) assms(3) regular_event_preserves_process_snapshots by auto
      moreover have "~ regular_event ev'" using assms by auto
      ultimately show ?thesis using mcd assms(2,5) same_messages_2 by blast
    qed
    moreover have "msgs e' i = msgs d' i"
      by (metis "4"(1) Send assms(6) next_send)
    ultimately show ?thesis by simp
  qed
qed

lemma swap_RecvMarker_Send:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isRecvMarker ev" and
    "isSend ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "msgs e i = msgs e' i"
  using assms swap_msgs_Send_RecvMarker by auto

lemma swap_cs_Trans_Snapshot:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isTrans ev" and
    "isSnapshot ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'"
  shows
    "cs e i = cs e' i"
proof (cases "channel i = None")
  case True
  then show ?thesis 
    by (metis assms(1) assms(2) assms(5) assms(6) no_cs_change_if_no_channel)
next
  case False
  then obtain p q where "channel i = Some (p, q)" by auto
  have nr: "~ regular_event ev'" 
    using assms(4) nonregular_event by blast
  let ?p = "occurs_on ev"
  let ?q = "occurs_on ev'"
  obtain u'' u''' where "ev = Trans ?p u'' u'''" 
    by (metis assms(3) event.collapse(1))
  have "ev' = Snapshot ?q"
    by (metis assms(4) event.collapse(4))
  have "cs d i = cs c i" 
    by (metis assms(1) assms(3) event.distinct_disc(4) no_cs_change_if_no_event regular_event)
  then have "cs e i = cs d' i"
  proof -
    have "\<forall>p. has_snapshotted d p = has_snapshotted c p" 
      using assms(1) assms(3) regular_event_preserves_process_snapshots by auto
    then show ?thesis 
      using \<open>cs d i = cs c i\<close> assms(2) assms(5) same_cs_2 by blast
  qed
  also have "... = cs e' i" 
    using assms(3) assms(6) no_cs_change_if_no_event regular_event by blast
  finally show ?thesis by simp
qed

lemma swap_cs_Snapshot_Trans:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isSnapshot ev" and
    "isTrans ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'"
  shows
    "cs e i = cs e' i"
  using swap_cs_Trans_Snapshot assms by auto

lemma swap_cs_Send_Snapshot:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isSend ev" and
    "isSnapshot ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'"
  shows
    "cs e i = cs e' i"
proof (cases "channel i = None")
  case True
  then show ?thesis 
    by (metis assms(1) assms(2) assms(5) assms(6) no_cs_change_if_no_channel)
next
  case False
  then obtain p q where "channel i = Some (p, q)" by auto
  have nr: "~ regular_event ev'" 
    using assms(4) nonregular_event by blast
  let ?p = "occurs_on ev"
  let ?q = "occurs_on ev'"
  obtain i' r u u' m where Send: "ev = Send i' ?p r u u' m" 
    by (metis assms(3) event.collapse(2))
  have Snapshot: "ev' = Snapshot ?q"
    by (metis assms(4) event.collapse(4))
  have "cs d i = cs c i" 
    by (metis Send assms(1) next_send)
  then have "cs e i = cs d' i"
  proof -
    have "\<forall>p. has_snapshotted d p = has_snapshotted c p" 
      using assms(1) assms(3) regular_event_preserves_process_snapshots by auto
    then show ?thesis 
      using \<open>cs d i = cs c i\<close> assms(2) assms(5) same_cs_2 by blast
  qed
  also have "... = cs e' i" 
    using assms(3) assms(6) no_cs_change_if_no_event regular_event by blast
  finally show ?thesis by simp
qed

lemma swap_cs_Snapshot_Send:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isSnapshot ev" and
    "isSend ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'"
  shows
    "cs e i = cs e' i"
  using swap_cs_Send_Snapshot assms by auto

lemma swap_cs_Recv_Snapshot:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isRecv ev" and
    "isSnapshot ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "cs e i = cs e' i"
proof (cases "channel i = None")
  case True
  then show ?thesis 
    by (metis assms(1) assms(2) assms(5) assms(6) no_cs_change_if_no_channel)
next
  case False
  then obtain p q where chan: "channel i = Some (p, q)" by auto
  have nr: "~ regular_event ev'" 
    using assms(4) nonregular_event by blast
  let ?p = "occurs_on ev"
  let ?q = "occurs_on ev'"
  obtain i' r u u' m where Recv: "ev = Recv i' ?p r u u' m" 
    by (metis assms(3) event.collapse(3))
  have Snapshot: "ev' = Snapshot ?q"
    by (metis assms(4) event.collapse(4))
  show ?thesis
  proof (cases "i = i'")
    case True
    then show ?thesis
    proof (cases "snd (cs c i) = Recording")
      case True
      then have "cs d i = (fst (cs c i) @ [m], Recording)" using Recv assms True \<open>i = i'\<close> chan 
        by (metis next_recv)
      moreover have "cs e i = cs d i"
        by (metis Snapshot assms(2) calculation fst_conv next_snapshot)
      moreover have "cs c i = cs d' i"
        by (metis Snapshot True assms(5) next_snapshot prod.collapse)
      moreover have "cs e' i = (fst (cs d' i) @ [m], Recording)" 
        by (metis (mono_tags, lifting) Recv assms(1) assms(6) calculation(1) calculation(3) next_recv)
      ultimately show ?thesis by simp
    next
      case False
      have "cs d i = cs c i" 
        by (metis False Recv assms(1) next_recv)
      have "cs e i = cs d' i"
      proof -
        have "\<forall>p. has_snapshotted d p = has_snapshotted c p" 
          using assms(1) assms(3) regular_event_preserves_process_snapshots by auto
        then show ?thesis 
          using \<open>cs d i = cs c i\<close> assms(2) assms(5) same_cs_2 by blast
      qed
      moreover have "cs d' i = cs e' i"
      proof -
        have "cs d' i = cs c i" 
          by (metis Pair_inject Recv Snapshot True assms(1) assms(5) assms(7) can_occur_Recv distributed_system.happen_implies_can_occur distributed_system.next_snapshot distributed_system_axioms option.inject)
        then show ?thesis using chan \<open>i = i'\<close> False Recv assms 
          by (metis next_recv)
      qed
      ultimately show ?thesis by simp
    qed
  next
    case False
    have "cs d i = cs c i" 
      by (metis False Recv assms(1) next_recv)
    then have "cs e i = cs d' i"
    proof -
      have "\<forall>p. has_snapshotted d p = has_snapshotted c p" 
        using assms(1) assms(3) regular_event_preserves_process_snapshots by auto
      then show ?thesis 
        using \<open>cs d i = cs c i\<close> assms(2) assms(5) same_cs_2 by blast
    qed
    also have "... = cs e' i" 
      by (metis False Recv assms(6) next_recv)
    finally show ?thesis by simp
  qed
qed

lemma swap_cs_Snapshot_Recv:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isSnapshot ev" and
    "isRecv ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "cs e i = cs e' i"
  using swap_cs_Recv_Snapshot assms by auto

lemma swap_cs_Trans_RecvMarker:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isTrans ev" and
    "isRecvMarker ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'"
  shows
    "cs e i = cs e' i"
proof (cases "channel i = None")
  case True
  then show ?thesis 
    by (metis assms(1) assms(2) assms(5) assms(6) no_cs_change_if_no_channel)
next
  case False
  then obtain p q where chan: "channel i = Some (p, q)" by auto
  have nr: "~ regular_event ev'" 
    using assms(4) nonregular_event by blast
  let ?p = "occurs_on ev"
  let ?q = "occurs_on ev'"
  obtain u'' u''' where "ev = Trans ?p u'' u'''" 
    by (metis assms(3) event.collapse(1))
  obtain i' s where "ev' = RecvMarker i' ?q s"
    by (metis assms(4) event.collapse(5))
  have "cs d i = cs c i" 
    by (metis assms(1) assms(3) event.distinct_disc(4) no_cs_change_if_no_event regular_event)
  then have "cs e i = cs d' i"
  proof -
    have "\<forall>p. has_snapshotted d p = has_snapshotted c p" 
      using assms(1) assms(3) regular_event_preserves_process_snapshots by auto
    then show ?thesis 
      using \<open>cs d i = cs c i\<close> assms(2) assms(5) same_cs_2 by blast
  qed
  also have "... = cs e' i" 
    using assms(3) assms(6) no_cs_change_if_no_event regular_event by blast
  finally show ?thesis by simp
qed

lemma swap_cs_RecvMarker_Trans:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isRecvMarker ev" and
    "isTrans ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'"
  shows
    "cs e i = cs e' i"
  using swap_cs_Trans_RecvMarker assms by auto

lemma swap_cs_Send_RecvMarker:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isSend ev" and
    "isRecvMarker ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'"
  shows
    "cs e i = cs e' i"
proof (cases "channel i = None")
  case True
  then show ?thesis 
    by (metis assms(1) assms(2) assms(5) assms(6) no_cs_change_if_no_channel)
next
  case False
  then obtain p q where chan: "channel i = Some (p, q)" by auto
  have nr: "~ regular_event ev'" 
    using assms(4) nonregular_event by blast
  let ?p = "occurs_on ev"
  let ?q = "occurs_on ev'"
  obtain i' r u u' m where Send: "ev = Send i' ?p r u u' m" 
    by (metis assms(3) event.collapse(2))
  obtain i'' s where RecvMarker: "ev' = RecvMarker i'' ?q s"
    by (metis assms(4) event.collapse(5))
  have "cs d i = cs c i" 
    by (metis assms(1) assms(3) event.distinct_disc(10,12,14) no_cs_change_if_no_event nonregular_event)
  then have "cs e i = cs d' i"
  proof -
    have "\<forall>p. has_snapshotted d p = has_snapshotted c p" 
      using assms(1) assms(3) regular_event_preserves_process_snapshots by auto
    then show ?thesis 
      using \<open>cs d i = cs c i\<close> assms(2) assms(5) same_cs_2 by blast
  qed
  also have "... = cs e' i" 
    using assms(3) assms(6) no_cs_change_if_no_event regular_event by blast
  finally show ?thesis by simp
qed

lemma swap_cs_RecvMarker_Send:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isRecvMarker ev" and
    "isSend ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'"
  shows
    "cs e i = cs e' i"
  using swap_cs_Send_RecvMarker assms by auto

lemma swap_cs_Recv_RecvMarker:
  assumes
    "c \<turnstile> ev \<mapsto> d" and
    "d \<turnstile> ev' \<mapsto> e" and
    "isRecv ev" and
    "isRecvMarker ev'" and
    "c \<turnstile> ev' \<mapsto> d'" and
    "d' \<turnstile> ev \<mapsto> e'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "cs e i = cs e' i"
proof (cases "channel i = None")
  case True
  then show ?thesis 
    by (metis assms(1) assms(2) assms(5) assms(6) no_cs_change_if_no_channel)
next
  case False
  then obtain p q where chan: "channel i = Some (p, q)" by auto
  have nr: "~ regular_event ev'" 
    using assms(4) nonregular_event by blast
  obtain i' p' r u u' m where Recv: "ev = Recv i' p' r u u' m" 
    by (metis assms(3) event.collapse(3))
  obtain i'' q' s where RecvMarker: "ev' = RecvMarker i'' q' s"
    by (metis assms(4) event.collapse(5))
  have "i' \<noteq> i''"
  proof (rule ccontr)
    assume "~ i' \<noteq> i''"
    then have "channel i' = channel i''" by simp
    then have "(r, p') = (s, q')" using Recv RecvMarker assms can_occur_def by simp
    then show False using Recv RecvMarker assms can_occur_def by simp
  qed
  show ?thesis
  proof (cases "i = i'")
    case True
    then have pqrp: "(p, q) = (r, p')" using Recv assms can_occur_def chan by simp
    then show ?thesis
    proof (cases "snd (cs c i)")
      case NotStarted
      then have "cs d i = cs c i" using assms Recv \<open>i = i'\<close> by simp
      moreover have "cs d' i = cs e i"
      proof -
        have "\<forall>p. has_snapshotted c p = has_snapshotted d p" 
          using assms(1) assms(3) regular_event_preserves_process_snapshots by auto
        with assms(2,5) calculation show ?thesis  by (blast intro: same_cs_2[symmetric])
      qed
      thm same_cs_2
      moreover have "cs d' i = cs e' i"
      proof -
        have "cs d' i = cs c i"
        proof -
          have "\<nexists>r. channel i = Some (r, q')" 
            using Recv RecvMarker assms(7) chan pqrp by auto
          with RecvMarker assms chan \<open>i = i'\<close> \<open>i' \<noteq> i''\<close> show ?thesis
            by (cases "has_snapshotted c q'", auto)
        qed
        then show ?thesis using assms Recv \<open>i = i'\<close> NotStarted by simp
      qed
      ultimately show ?thesis by simp
    next
      case Done
      then have "cs d i = cs c i" using assms Recv \<open>i = i'\<close> by simp
      moreover have "cs d' i = cs e i"
      proof -
        have "\<forall>p. has_snapshotted c p = has_snapshotted d p" 
          using assms(1) assms(3) regular_event_preserves_process_snapshots by auto
        then show ?thesis using assms(2,5) calculation by (blast intro: same_cs_2[symmetric])
      qed
      moreover have "cs d' i = cs e' i"
      proof -
        have "cs d' i = cs c i"
        proof -
          have "\<nexists>r. channel i = Some (r, q')" 
            using Recv RecvMarker assms(7) chan pqrp by auto
          with RecvMarker assms chan \<open>i = i'\<close> \<open>i' \<noteq> i''\<close> show ?thesis
            by (cases "has_snapshotted c q'", auto)
        qed
        then show ?thesis using assms Recv \<open>i = i'\<close> Done by simp
      qed
      ultimately show ?thesis by simp
    next
      case Recording
      have "cs d i = (fst (cs c i) @ [m], Recording)" 
        using Recording Recv True assms(1) by auto
      moreover have "cs e i = cs d i"
      proof -
        have "\<nexists>r. channel i = Some (r, q')" 
          using Recv RecvMarker assms(7) chan pqrp by auto
        with RecvMarker assms chan \<open>i = i'\<close> \<open>i' \<noteq> i''\<close> show ?thesis
          by (cases "has_snapshotted d q'", auto)
      qed
      moreover have "cs c i = cs d' i " 
      proof -
        have "\<nexists>r. channel i = Some (r, q')" 
          using Recv RecvMarker assms(7) chan pqrp by auto
        with RecvMarker assms chan \<open>i = i'\<close> \<open>i' \<noteq> i''\<close> show ?thesis
          by (cases "has_snapshotted c q'", auto)
      qed
      moreover have "cs e' i = (fst (cs d' i) @ [m], Recording)" 
        using Recording Recv True assms(6) calculation(3) by auto
      ultimately show ?thesis by simp
    qed
  next
    case False
    have "cs d i = cs c i" 
      using False Recv assms(1) by auto
    then have "cs e i = cs d' i"
    proof -
      have "\<forall>p. has_snapshotted d p = has_snapshotted c p" 
        using assms(1) assms(3) regular_event_preserves_process_snapshots by auto
      then show ?thesis 
        using \<open>cs d i = cs c i\<close> assms(2) assms(5) same_cs_2 by blast
    qed
    also have "... = cs e' i" 
      using False Recv assms(6) by auto
    finally show ?thesis by simp
  qed
qed

end (* context distributed_system *)

end (* theory Swap *)
