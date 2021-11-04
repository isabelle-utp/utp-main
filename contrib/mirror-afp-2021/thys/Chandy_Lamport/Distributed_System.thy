section \<open>Modelling distributed systems\<close>

text \<open>We assume familiarity with Chandy and Lamport's
paper \emph{Distributed Snapshots: Determining Global States of
Distributed Systems}~\cite{chandy}.\<close>

theory Distributed_System

imports Main

begin

type_synonym 'a fifo = "'a list"
type_synonym channel_id = nat

datatype 'm message =
    Marker
  | Msg 'm

datatype recording_state =
    NotStarted
  | Recording
  | Done

text \<open>We characterize distributed systems by three underlying type variables:
Type variable 'p captures the processes of the underlying system.
Type variable 's describes the possible states of the processes.
Finally, type variable 'm describes all possible messages in said system.

Each process is in exactly one state at any point in time of the system.
Processes are interconnected by directed channels, which hold messages in-flight
between connected processes. There can be an arbitrary number of channels between
different processes. The entire state of the system including the (potentially unfinished)
snapshot state is called \emph{configuration}.\<close>

record ('p, 's, 'm) configuration =
  states :: "'p \<Rightarrow> 's"
  msgs :: "channel_id \<Rightarrow> 'm message fifo"

  process_snapshot :: "'p \<Rightarrow> 's option"
  channel_snapshot :: "channel_id \<Rightarrow> 'm fifo * recording_state"

text \<open>An event in Chandy and Lamport's formalization describes a
process' state transition, optionally producing or consuming
(but not both) a message on a channel. Additionally, a process may either initiate
a snapshot spontaneously, or is forced to do so by receiving a snapshot \emph{marker}
on one of it's incoming channels.\<close>

datatype ('p, 's, 'm) event =
    isTrans: Trans (occurs_on: 'p) 's 's
  | isSend:  Send  (getId: channel_id)
                   (occurs_on: 'p)
                   (partner: 'p)
                   's 's (getMsg: 'm)
  | isRecv:  Recv  (getId: channel_id)
                   (occurs_on: 'p)
                   (partner: 'p)
                   's 's (getMsg: 'm)

  | isSnapshot:   Snapshot   (occurs_on: 'p)
  | isRecvMarker: RecvMarker (getId: channel_id)
                             (occurs_on: 'p)
                             (partner: 'p)

text \<open>We introduce abbreviations and type synoyms for commonly used terms.\<close>

type_synonym ('p, 's, 'm) trace = "('p, 's, 'm) event list"

abbreviation ps where "ps \<equiv> process_snapshot"
abbreviation cs where "cs \<equiv> channel_snapshot"

abbreviation no_snapshot_change where
  "no_snapshot_change c c' \<equiv> ((\<forall>p'. ps c p' = ps c' p') \<and> (\<forall>i'. cs c i' = cs c' i'))"

abbreviation has_snapshotted where
  "has_snapshotted c p \<equiv> process_snapshot c p \<noteq> None"

text \<open>A regular event is an event as described in Chandy and Lamport's
original paper: A state transition accompanied by the emission
or receiving of a message. Nonregular events are related to
snapshotting and receiving markers along communication channels.\<close>

definition regular_event[simp]:
  "regular_event ev \<equiv> (isTrans ev \<or> isSend ev \<or> isRecv ev)"

lemma nonregular_event:
  "~ regular_event ev = (isSnapshot ev \<or> isRecvMarker ev)" 
  by (meson event.distinct_disc event.exhaust_disc regular_event)

lemma event_occurs_on_unique:
  assumes
    "p \<noteq> q"
    "occurs_on ev = p"
  shows
    "occurs_on ev \<noteq> q"
  using assms by (cases ev, auto)

subsection \<open>The distributed system locale\<close>

text \<open>In order to capture Chandy and Lamport's computation system
we introduce two locales. The distributed system locale describes
global truths, such as the mapping from channel IDs to sender and
receiver processes, the transition relations for the underlying
computation system and the core assumption that no process has
a channel to itself. While not explicitly mentioned in Chandy's
and Lamport's work, it makes sense to assume that a channel need
not communicate to itself via messages, since it shares memory with
itself.\<close>

locale distributed_system =
  fixes
    channel :: "channel_id \<Rightarrow> ('p * 'p) option" and
    trans :: "'p \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" and
    send :: "channel_id \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'm \<Rightarrow> bool" and
    recv :: "channel_id \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'm \<Rightarrow> bool"
  assumes
    no_self_channel:
      "\<forall>i. \<nexists>p. channel i = Some (p, p)"
begin

subsubsection \<open>State transitions\<close>

definition can_occur :: "('p, 's, 'm) event \<Rightarrow> ('p, 's, 'm) configuration \<Rightarrow> bool" where
"can_occur ev c \<equiv> (case ev of
    Trans p s s'        \<Rightarrow> states c p = s
                        \<and> trans p s s'
  | Send i p q s s' msg \<Rightarrow> states c p = s
                        \<and> channel i = Some (p, q)
                        \<and> send i p q s s' msg
  | Recv i p q s s' msg \<Rightarrow> states c p = s
                        \<and> channel i = Some (q, p)
                        \<and> length (msgs c i) > 0
                        \<and> hd (msgs c i) = Msg msg
                        \<and> recv i p q s s' msg
  | Snapshot p          \<Rightarrow> \<not> has_snapshotted c p
  | RecvMarker i p q    \<Rightarrow> channel i = Some (q, p)
                        \<and> length (msgs c i) > 0
                        \<and> hd (msgs c i) = Marker)"

definition src where
  "src i p \<equiv> (\<exists>q. channel i = Some (p, q))"

definition dest where
  "dest i q \<equiv> (\<exists>p. channel i = Some (p, q))"

lemma can_occur_Recv:
  assumes
    "can_occur (Recv i p q s s' m) c"
  shows
    "states c p = s \<and> channel i = Some (q, p) \<and> (\<exists>xs. msgs c i = Msg m # xs) \<and> recv i p q s s' m"
proof -
  have "\<exists>xs. msgs c i = Msg m # xs" 
    using assms can_occur_def 
    by (metis (mono_tags, lifting) event.case(3) hd_Cons_tl length_greater_0_conv)
  then show ?thesis using assms can_occur_def by auto
qed

abbreviation check_snapshot_occur where
  "check_snapshot_occur c c' p \<equiv>
    (can_occur (Snapshot p) c \<and>
    (ps c' p = Some (states c p))
  \<and> (\<forall>p'. states c p' = states c' p')
  \<and> (\<forall>p'. (p' \<noteq> p) \<longrightarrow> ps c' p' = ps c p')
  \<and> (\<forall>i. (\<exists>q. channel i = Some (p, q)) \<longrightarrow> msgs c' i = msgs c i @ [Marker])
  \<and> (\<forall>i. (\<exists>q. channel i = Some (q, p)) \<longrightarrow> channel_snapshot c' i = (fst (channel_snapshot c i), Recording))
  \<and> (\<forall>i. (\<nexists>q. channel i = Some (p, q)) \<longrightarrow> msgs c' i = msgs c i)
  \<and> (\<forall>i. (\<nexists>q. channel i = Some (q, p)) \<longrightarrow> channel_snapshot c' i = channel_snapshot c i))"

abbreviation check_recv_marker_occur where
  "check_recv_marker_occur c c' i p q \<equiv>
    (can_occur (RecvMarker i p q) c
  \<and> (\<forall>r. states c r = states c' r)
  \<and> (\<forall>r. (r \<noteq> p) \<longrightarrow> process_snapshot c r = process_snapshot c' r)
  \<and> (Marker # msgs c' i = msgs c i)
  \<and> (channel_snapshot c' i = (fst (channel_snapshot c i), Done))
  \<and> (if has_snapshotted c p
        then (process_snapshot c p = process_snapshot c' p)
           \<and> (\<forall>i'. (i' \<noteq> i) \<longrightarrow> msgs c' i' = msgs c i')
           \<and> (\<forall>i'. (i' \<noteq> i) \<longrightarrow> channel_snapshot c i' = channel_snapshot c' i')
        else (process_snapshot c' p = Some (states c p))
           \<and> (\<forall>i'. i' \<noteq> i \<and> (\<exists>r. channel i' = Some (p, r))
             \<longrightarrow> msgs c' i' = msgs c i' @ [Marker])
           \<and> (\<forall>i'. i' \<noteq> i \<and> (\<exists>r. channel i' = Some (r, p))
             \<longrightarrow> channel_snapshot c' i' = (fst (channel_snapshot c i'), Recording))
           \<and> (\<forall>i'. i' \<noteq> i \<and> (\<nexists>r. channel i' = Some (p, r))
             \<longrightarrow> msgs c' i' = msgs c i')
           \<and> (\<forall>i'. i' \<noteq> i \<and> (\<nexists>r. channel i' = Some (r, p))
             \<longrightarrow> channel_snapshot c' i' = channel_snapshot c i')))"

abbreviation check_trans_occur where
  "check_trans_occur c c' p s s'\<equiv>
    (can_occur (Trans p s s') c
  \<and> (states c' p = s')
  \<and> (\<forall>r. (r \<noteq> p) \<longrightarrow> states c' r = states c r)
  \<and> (\<forall>i. msgs c' i = msgs c i)
  \<and> (no_snapshot_change c c'))"

abbreviation check_send_occur where 
  "check_send_occur c c' i p q s s' msg \<equiv>
    (can_occur (Send i p q s s' msg) c
  \<and> (states c' p = s')
  \<and> (\<forall>r. (r \<noteq> p) \<longrightarrow> states c' r = states c r)
  \<and> (msgs c' i = msgs c i @ [Msg msg])
  \<and> (\<forall>i'. i \<noteq> i' \<longrightarrow> msgs c' i' = msgs c i')
  \<and> (no_snapshot_change c c'))"

abbreviation check_recv_occur where
  "check_recv_occur c c' i p q s s' msg \<equiv>
    (can_occur (Recv i p q s s' msg) c
  \<and> (states c p = s \<and> states c' p = s')
  \<and> (\<forall>r. (r \<noteq> p) \<longrightarrow> states c' r = states c r)
  \<and> (msgs c i = Msg msg # msgs c' i)
  \<and> (\<forall>i'. i \<noteq> i' \<longrightarrow> msgs c' i' = msgs c i')
  \<and> (\<forall>r. process_snapshot c r = process_snapshot c' r)
  \<and> (\<forall>i'. i' \<noteq> i \<longrightarrow> channel_snapshot c i' = channel_snapshot c' i')
  \<and> (if snd (channel_snapshot c i) = Recording
     then channel_snapshot c' i = (fst (channel_snapshot c i) @ [msg], Recording)
     else channel_snapshot c i = channel_snapshot c' i))"

text \<open>The \emph{next} predicate lets us express configuration transitions
using events. The predicate $next(s_1, e, s_2)$ denotes the transition
of the configuration $s_1$ to $s_2$ via the event $e$. It ensures that
$e$ can occur in state $s_1$ and the state $s_2$ is correctly constructed
from $s_1$.\<close>

primrec "next" ::
  "('p, 's, 'm) configuration
  \<Rightarrow> ('p, 's, 'm) event
  \<Rightarrow> ('p, 's, 'm) configuration
  \<Rightarrow> bool"
  ("_ \<turnstile> _ \<mapsto> _" [70, 70, 70]) where
    next_snapshot: "c \<turnstile> Snapshot p \<mapsto> c' =
      check_snapshot_occur c c' p"
  | next_recv_marker: "c \<turnstile> RecvMarker i p q \<mapsto> c' =
      check_recv_marker_occur c c' i p q"
  | next_trans: "c \<turnstile> Trans p s s' \<mapsto> c' =
      check_trans_occur c c' p s s'"
  | next_send: "c \<turnstile> Send i p q s s' msg \<mapsto> c' =
      check_send_occur c c' i p q s s' msg"
  | next_recv: "c \<turnstile> Recv i p q s s' msg \<mapsto> c' =
      check_recv_occur c c' i p q s s' msg"

text \<open>Useful lemmas about state transitions\<close>

lemma state_and_event_determine_next:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "c \<turnstile> ev \<mapsto> c''"
  shows
    "c' = c''"
proof (cases ev)
  case (Snapshot p)
  then have "states c' = states c''" using assms by auto
  moreover have "msgs c' = msgs c''"
  proof (rule ext)
    fix i
    show "msgs c' i = msgs c'' i"
    proof (cases "channel i = None")
      case True
      then show ?thesis using Snapshot assms by auto
    next
      case False
      then obtain r s where "channel i = Some (r, s)" by auto
      with assms Snapshot show ?thesis by (cases "r = p", simp_all)
    qed
  qed
  moreover have "process_snapshot c' = process_snapshot c''" by (metis Snapshot assms next_snapshot ext)
  moreover have "channel_snapshot c' = channel_snapshot c''"
  proof (rule ext)
    fix i
    show "channel_snapshot c' i = channel_snapshot c'' i"
    proof (cases "channel i = None")
      case True
      then show ?thesis using assms Snapshot by simp
    next
      case False
      then obtain r s where "channel i = Some (r, s)" by auto
      with assms Snapshot show ?thesis by (cases "s = p", simp_all)
    qed
  qed
  ultimately show "c' = c''" by simp
next
  case (RecvMarker i p)
  then have "states c' = states c''" using assms by auto
  moreover have "msgs c' = msgs c''"
  proof (rule ext)
    fix i'
    show "msgs c' i' = msgs c'' i'"
    proof (cases "i' = i")
      case True
      then have "Marker # msgs c' i' = msgs c i'" using assms RecvMarker by simp
      also have "... = Marker # msgs c'' i'" using assms RecvMarker \<open>i' = i\<close> by simp
      finally show ?thesis by simp
    next
      case False
      then show ?thesis
      proof (cases "has_snapshotted c p")
        case True
        then show ?thesis using assms RecvMarker \<open>i' \<noteq> i\<close> by simp
      next
        case no_snap: False
        then show ?thesis
        proof (cases "channel i' = None")
          case True
          then show ?thesis using assms RecvMarker \<open>i' \<noteq> i\<close> no_snap by simp
        next
          case False
          then obtain r s where "channel i' = Some (r, s)" by auto
          with assms RecvMarker no_snap \<open>i' \<noteq> i\<close> show ?thesis by (cases "r = p"; simp_all)
        qed
      qed
    qed
  qed
  moreover have "process_snapshot c' = process_snapshot c''"
  proof (rule ext)
    fix r
    show "ps c' r = ps c'' r"
    proof (cases "r \<noteq> p")
      case True
      then show ?thesis using assms RecvMarker by simp
    next
      case False
      with assms RecvMarker \<open>~ r \<noteq> p\<close> show ?thesis by (cases "has_snapshotted c r", auto)
    qed
  qed
  moreover have "channel_snapshot c' = channel_snapshot c''"
  proof (rule ext)
    fix i'
    show "cs c' i' = cs c'' i'"
    proof (cases "i' = i")
      case True
      then show ?thesis using assms RecvMarker by simp
    next
      case False
      then show ?thesis
      proof (cases "has_snapshotted c p")
        case True
        then show ?thesis using assms RecvMarker \<open>i' \<noteq> i\<close> by simp
      next
        case no_snap: False
        then show ?thesis
        proof (cases "channel i' = None")
          case True
          then show ?thesis using assms RecvMarker \<open>i' \<noteq> i\<close> no_snap by simp
        next
          case False
          then obtain r s where "channel i' = Some (r, s)" by auto
          with assms RecvMarker no_snap \<open>i' \<noteq> i\<close> show ?thesis by (cases "s = p"; simp_all)
        qed
      qed
    qed
  qed
  ultimately show "c' = c''" by simp
next
  case (Trans p s s')
  then have "states c' = states c''" by (metis (no_types, lifting) assms next_trans ext)
  moreover have "msgs c' = msgs c''" using assms Trans by auto
  moreover have "process_snapshot c' = process_snapshot c''" using assms Trans by auto
  moreover have "channel_snapshot c' = channel_snapshot c''" using assms Trans by auto
  ultimately show "c' = c''" by simp
next
  case (Send i p s s' m)
  then have "states c' = states c''" by (metis (no_types, lifting) assms next_send ext)
  moreover have "msgs c' = msgs c''"
  proof (rule ext)
    fix i'
    from assms Send show "msgs c' i' = msgs c'' i'" by (cases "i' = i", simp_all)
  qed
  moreover have "process_snapshot c' = process_snapshot c''" using assms Send by auto
  moreover have "channel_snapshot c' = channel_snapshot c''" using assms Send by auto
  ultimately show "c' = c''" by simp
next
  case (Recv i p s s' m)
  then have "states c' = states c''" by (metis (no_types, lifting) assms next_recv ext)
  moreover have "msgs c' = msgs c''"
  proof (rule ext)
    fix i'
    from assms Recv show "msgs c' i' = msgs c'' i'" by (cases "i' = i", simp_all)
  qed
  moreover have "process_snapshot c' = process_snapshot c''" using assms Recv by auto
  moreover have "channel_snapshot c' = channel_snapshot c''"
  proof (rule ext)
    fix i'
    show "cs c' i' = cs c'' i'"
    proof (cases "i' \<noteq> i")
      case True
      then show ?thesis using assms Recv by simp
    next
      case False
      with assms Recv show ?thesis by (cases "snd (cs c i') = Recording", auto)
    qed
  qed
  ultimately show "c' = c''" by simp
qed

lemma exists_next_if_can_occur:
  assumes
    "can_occur ev c"
  shows
    "\<exists>c'. c \<turnstile> ev \<mapsto> c'"
proof (cases ev)
  case (Snapshot p)
  let ?c = "\<lparr> states = states c,
              msgs = %i. if (\<exists>q. channel i = Some (p, q)) then msgs c i @ [Marker] else msgs c i,
              process_snapshot = %r. if r = p then Some (states c p) else ps c r,
              channel_snapshot = %i. if (\<exists>q. channel i = Some (q, p)) then (fst (cs c i), Recording) else cs c i \<rparr>"
  have "c \<turnstile> ev \<mapsto> ?c" using Snapshot assms by auto
  then show ?thesis by blast
next
  case (RecvMarker i p q)
  show ?thesis
  proof (cases "has_snapshotted c p")
    case True
    let ?c = "\<lparr> states = states c,
                msgs = %i'. if i = i' then tl (msgs c i') else msgs c i',
                process_snapshot = ps c,
                channel_snapshot = %i'. if i = i' then (fst (cs c i'), Done) else cs c i' \<rparr>"
    have "msgs c i = Marker # msgs ?c i"
      using assms can_occur_def RecvMarker hd_Cons_tl by fastforce
    then have "c \<turnstile> ev \<mapsto> ?c" using True RecvMarker assms by auto
    then show ?thesis by blast
  next
    case False
    let ?c = "\<lparr> states = states c,
                msgs = %i'. if i' = i
                                  then tl (msgs c i')
                                  else if (\<exists>r. channel i' = Some (p, r))
                                         then msgs c i' @ [Marker]
                                         else msgs c i',
                process_snapshot = %r. if r = p then Some (states c r) else ps c r,
                channel_snapshot = %i'. if i = i' then (fst (cs c i'), Done)
                                              else if (\<exists>r. channel i' = Some (r, p))
                                                     then (fst (cs c i'), Recording)
                                                     else cs c i' \<rparr>"
    have "msgs c i = Marker # msgs ?c i"
      using assms can_occur_def RecvMarker hd_Cons_tl by fastforce
    moreover have "ps ?c p = Some (states c p)" by simp
    ultimately have "c \<turnstile> ev \<mapsto> ?c" using RecvMarker assms False by auto
    then show ?thesis by blast
  qed
next
  case (Trans p s s')
  let ?c = "\<lparr> states = %r. if r = p then s' else states c r,
              msgs = msgs c,
              process_snapshot = ps c,
              channel_snapshot = cs c \<rparr>"
  have "c \<turnstile> ev \<mapsto> ?c" 
    using Trans assms by auto
  then show ?thesis by blast
next
  case (Send i p q s s' msg)
    let ?c = "\<lparr> states = %r. if r = p then s' else states c r,
              msgs = %i'. if i = i' then msgs c i' @ [Msg msg] else msgs c i',
              process_snapshot = ps c,
              channel_snapshot = cs c \<rparr>"
  have "c \<turnstile> ev \<mapsto> ?c" 
    using Send assms by auto
  then show ?thesis by blast
next
  case (Recv i p q s s' msg)
  then show ?thesis
  proof (cases "snd (cs c i)")
    case Recording
    let ?c = "\<lparr> states = %r. if r = p then s' else states c r,
                msgs = %i'. if i = i' then tl (msgs c i') else msgs c i',
                process_snapshot = ps c,
                channel_snapshot = %i'. if i = i'
                                              then (fst (cs c i') @ [msg], Recording)
                                              else cs c i'\<rparr>"
    have "c \<turnstile> ev \<mapsto> ?c" 
      using Recv Recording assms can_occur_Recv by fastforce
    then show ?thesis by blast
  next
    case Done
    let ?c = "\<lparr> states = %r. if r = p then s' else states c r,
                msgs = %i'. if i = i' then tl (msgs c i') else msgs c i',
                process_snapshot = ps c,
                channel_snapshot = cs c \<rparr>"
    have "c \<turnstile> ev \<mapsto> ?c"
      using Done Recv assms can_occur_Recv by fastforce
    then show ?thesis by blast
  next
    case NotStarted
    let ?c = "\<lparr> states = %r. if r = p then s' else states c r,
                msgs = %i'. if i = i' then tl (msgs c i') else msgs c i',
                process_snapshot = ps c,
                channel_snapshot = cs c \<rparr>"
    have "c \<turnstile> ev \<mapsto> ?c"
      using NotStarted Recv assms can_occur_Recv by fastforce
    then show ?thesis by blast
  qed
qed

lemma exists_exactly_one_following_state:
  "can_occur ev c \<Longrightarrow> \<exists>!c'. c \<turnstile> ev \<mapsto> c'"
  using exists_next_if_can_occur state_and_event_determine_next by blast

lemma no_state_change_if_no_event:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "occurs_on ev \<noteq> p"
  shows
    "states c p = states c' p \<and> process_snapshot c p = process_snapshot c' p"
  using assms by (cases ev, auto)

lemma no_msgs_change_if_no_channel:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "channel i = None"
  shows
    "msgs c i = msgs c' i"
using assms proof (cases ev)
  case (RecvMarker cid p)
  then have "cid \<noteq> i" using assms RecvMarker can_occur_def by fastforce
  with assms RecvMarker show ?thesis by (cases "has_snapshotted c p", auto)
next
  case (Send cid p s s' m)
  then have "cid \<noteq> i" using assms Send can_occur_def by fastforce
  then show ?thesis using assms Send by auto
next
  case (Recv cid p s s' m)
  then have "cid \<noteq> i" using assms Recv can_occur_def by fastforce
  then show ?thesis using assms Recv by simp
qed simp_all

lemma no_cs_change_if_no_channel:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "channel i = None"
  shows
    "cs c i = cs c' i"
using assms proof (cases ev)
  case (RecvMarker cid p)
  then have "cid \<noteq> i" using assms RecvMarker can_occur_def by fastforce
  with assms RecvMarker show ?thesis by (cases "has_snapshotted c p", auto)
next
  case (Send cid p s s' m)
  then have "cid \<noteq> i" using assms Send can_occur_def by fastforce
  then show ?thesis using assms Send by auto
next
  case (Recv cid p s s' m)
  then have "cid \<noteq> i" using assms Recv can_occur_def by fastforce
  then show ?thesis using assms Recv by simp
qed simp_all

lemma no_msg_change_if_no_event:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "isSend ev \<longrightarrow> getId ev \<noteq> i" and
    "isRecv ev \<longrightarrow> getId ev \<noteq> i" and
    "regular_event ev"
  shows
    "msgs c i = msgs c' i"
proof (cases "channel i = None")
  case True
  then show ?thesis using assms no_msgs_change_if_no_channel by simp
next
  have "isTrans ev \<or> isSend ev \<or> isRecv ev" using assms by simp
  then show ?thesis
  proof (elim disjE)
    assume "isTrans ev"
    then show ?thesis 
      by (metis assms(1) event.collapse(1) next_trans)
  next
    assume "isSend ev"
    then obtain i' r s u u' m where Send: "ev = Send i' r s u u' m" by (meson isSend_def)
    then show ?thesis using Send assms by auto
  next
    assume "isRecv ev"
    then obtain i' r s u u' m where "ev = Recv i' r s u u' m" by (meson isRecv_def)
    then show ?thesis using assms by auto
  qed
qed

lemma no_cs_change_if_no_event:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "isRecv ev \<longrightarrow> getId ev \<noteq> i" and
    "regular_event ev"
  shows
    "cs c i = cs c' i"
proof -
  have "isTrans ev \<or> isSend ev \<or> isRecv ev" using assms by simp
  then show ?thesis
  proof (elim disjE)
    assume "isTrans ev"
    then show ?thesis 
      by (metis assms(1) event.collapse(1) next_trans)
  next
    assume "isSend ev"
    then obtain i' r s u u' m where "ev = Send i' r s u u' m" by (meson isSend_def)
    then show ?thesis using assms by auto
  next
    assume "isRecv ev"
    then obtain i r s u u' m where "ev = Recv i r s u u' m" by (meson isRecv_def)
    then show ?thesis using assms by auto
  qed
qed

lemma happen_implies_can_occur:
  assumes
    "c \<turnstile> ev \<mapsto> c'"
  shows
    "can_occur ev c"
proof -
  show ?thesis using assms by (cases ev, auto)
qed

lemma snapshot_increases_message_length:
  assumes
    "ev = Snapshot p" and
    "c \<turnstile> ev \<mapsto> c'" and
    "channel i = Some (q, r)"
  shows
    "length (msgs c i) \<le> length (msgs c' i)"
  using assms by (cases "p = q", auto)

lemma recv_marker_changes_head_only_at_i:
  assumes
    "ev = RecvMarker i p q" and
    "c \<turnstile> ev \<mapsto> c'" and
    "i' \<noteq> i"
  shows
    "msgs c i' = [] \<or> hd (msgs c i') = hd (msgs c' i')"
proof (cases "channel i' = None")
  case True
  then show ?thesis using assms no_msgs_change_if_no_channel by presburger
next
  case False
  then show ?thesis
  proof (cases "msgs c i'")
    case Nil
    then show ?thesis by simp
  next
    case (Cons m xs)
    then obtain r s where "channel i' = Some (r, s)" using False by auto
    then show ?thesis
    proof (cases "has_snapshotted c p")
      case True
      then show ?thesis using assms by auto
    next
      case False
      with assms show ?thesis by (cases "r = p", auto)
    qed
  qed
qed

lemma recv_marker_other_channels_not_shrinking:
  assumes
    "ev = RecvMarker i p q" and
    "c \<turnstile> ev \<mapsto> c'"
  shows
    "length (msgs c i') \<le> length (msgs c' i') \<longleftrightarrow> i \<noteq> i'"
proof (rule iffI)
  show "length (msgs c i') \<le> length (msgs c' i') \<Longrightarrow> i \<noteq> i'"
  proof (rule ccontr)
    assume asm: "~ i \<noteq> i'" "length (msgs c i') \<le> length (msgs c' i')"
    then have "msgs c i = Marker # msgs c' i" using assms by auto
    then have "length (msgs c i) > length (msgs c' i)" by simp
    then have "length (msgs c i') > length (msgs c' i')" using asm by simp
    then show False using asm by simp
  qed
next
  show "i \<noteq> i' \<Longrightarrow> length (msgs c i') \<le> length (msgs c' i')"
  proof -
    assume "i \<noteq> i'"
    then show ?thesis
    proof (cases "channel i' = None")
      case True
      then show ?thesis using assms no_msgs_change_if_no_channel by presburger
    next
      case False
      then obtain r s where chan: "channel i' = Some (r, s)" by auto
      then show ?thesis
      proof (cases "has_snapshotted c p")
        case True
        with assms \<open>i \<noteq> i'\<close> show ?thesis by auto
      next
        case no_snap: False
        then show ?thesis
        proof (cases "p = r")
          case True
          then have "msgs c' i' = msgs c i' @ [Marker]" using \<open>i \<noteq> i'\<close> assms no_snap chan by auto
          then show ?thesis by auto
        next
          case False
          then show ?thesis using assms \<open>i \<noteq> i'\<close> chan no_snap by auto
        qed
      qed
    qed
  qed
qed

lemma regular_event_cannot_induce_snapshot:
  assumes
    "~ has_snapshotted c p" and
    "c \<turnstile> ev \<mapsto> c'"
  shows
    "regular_event ev \<longrightarrow> ~ has_snapshotted c' p"
proof (cases ev)
  case (Trans q s s')
  then show ?thesis using assms(1) assms(2) by auto
next
  case (Send q r s s' m)
  then show ?thesis using assms by auto
next
  case (Recv q r s s' m) 
  then show ?thesis using assms by auto
qed simp_all

lemma regular_event_preserves_process_snapshots:
  assumes
    "c \<turnstile> ev \<mapsto> c'"
  shows
    "regular_event ev \<Longrightarrow> ps c r = ps c' r"
proof (cases ev)
  case (Trans p s s')
  then show ?thesis 
    using assms by auto
next
  case (Send p q s s' m)
  then show ?thesis 
    using assms by auto
next
  case (Recv p q s s' m)
  then show ?thesis 
    using assms by auto
qed simp_all

lemma no_state_change_if_nonregular_event:
  assumes
    "~ regular_event ev" and
    "c \<turnstile> ev \<mapsto> c'"
  shows
    "states c p = states c' p"
proof -
  have "isSnapshot ev \<or> isRecvMarker ev" using nonregular_event assms by auto
  then show ?thesis
  proof (elim disjE, goal_cases)
    case 1
    then obtain q where "ev = Snapshot q" 
      by (meson isSnapshot_def)
    then show ?thesis 
      using assms(2) by auto
  next
    case 2
    then obtain i q r where "ev = RecvMarker i q r"
      by (meson isRecvMarker_def)
    then show ?thesis using assms(2) by auto
  qed
qed

lemma nonregular_event_induces_snapshot:
  assumes
    "~ has_snapshotted c p" and
    "c \<turnstile> ev \<mapsto> c'" and
    "occurs_on ev = p" and
    "~ regular_event ev"
  shows
    "~ regular_event ev \<longrightarrow> has_snapshotted c' p"
proof (cases ev)
  case (Snapshot q)
  then have "q = p" using assms by auto
  then show ?thesis using Snapshot assms(2) by auto
next
  case (RecvMarker i q r)
  then have "q = p" using assms by auto
  then show ?thesis using RecvMarker assms by auto
qed (simp_all add: assms)

lemma snapshot_state_unchanged:
  assumes
    step: "c \<turnstile> ev \<mapsto> c'" and
    "has_snapshotted c p"
  shows
    "ps c p = ps c' p"
proof (cases "occurs_on ev = p")
  case False
  then show ?thesis 
    using local.step no_state_change_if_no_event by auto
next
  case True
  then show ?thesis
  proof (cases "regular_event ev")
    case True
    then show ?thesis 
      using local.step regular_event_preserves_process_snapshots by auto
  next
    case False
    have "isRecvMarker ev"
    proof (rule ccontr)
      have "isSnapshot ev \<or> isRecvMarker ev" 
        using False nonregular_event by blast
      moreover assume "~ isRecvMarker ev"
      ultimately have "isSnapshot ev" by simp
      then have "ev = Snapshot p" by (metis True event.collapse(4))
      then have "can_occur ev c" 
        using happen_implies_can_occur local.step by blast
      then have "~ has_snapshotted c p" unfolding can_occur_def 
        by (simp add: \<open>ev = Snapshot p\<close>)
      then show False using assms by auto
    qed
    then show ?thesis (* z3 sledgehammer fails for Isabelle2019 *)
    proof -
      have "\<exists>n pa. c \<turnstile> RecvMarker n p pa \<mapsto> c'"
        by (metis True \<open>isRecvMarker ev\<close> event.collapse(5) local.step)
      then show ?thesis
        using assms(2) by force
    qed
  qed
qed

lemma message_must_be_delivered:
  assumes
    valid: "c \<turnstile> ev \<mapsto> c'" and
    delivered: "(msgs c i \<noteq> [] \<and> hd (msgs c i) = m) \<and> (msgs c' i = [] \<or> hd (msgs c' i) \<noteq> m)"
  shows
    "(\<exists>p q.         ev = RecvMarker i p q   \<and> m = Marker)
   \<or> (\<exists>p q s s' m'. ev = Recv i p q s s' m' \<and> m = Msg m')"
proof (cases ev)
  case (Snapshot p)
  then show ?thesis
  proof (cases "msgs c i")
    case Nil
    then show ?thesis using delivered by simp
  next
    case (Cons m xs)
    with assms Snapshot show ?thesis
    proof (cases "channel i = None")
      case True
      then show ?thesis using assms Snapshot by auto
    next
      case False
      then obtain r s where chan: "channel i = Some (r, s)" by auto
      then show ?thesis
      proof (cases "r = p")
        case True
        then have "msgs c' i = msgs c i @ [Marker]" using assms(1) Snapshot chan by auto
        then show ?thesis using delivered by auto
      next
        case False
        then have "msgs c' i = msgs c i" using assms Snapshot chan by simp
        then show ?thesis using delivered Cons by simp
      qed
    qed
  qed
next
  case (RecvMarker i' p q)
  then have "i' = i" 
    by (metis assms(1) delivered le_0_eq length_greater_0_conv list.size(3) recv_marker_changes_head_only_at_i recv_marker_other_channels_not_shrinking)
  moreover have "Marker = m"
    using \<open>i' = i\<close> RecvMarker assms(1) can_occur_def delivered by auto
  moreover have "channel i = Some (q, p)" 
    using RecvMarker assms(1) calculation(1) can_occur_def by auto
  ultimately show ?thesis using RecvMarker by simp
next
  case (Trans p' s s')
  then show ?thesis
    using valid delivered by auto
next
  case (Send p' q' s s' m')
  then show ?thesis
    by (metis (no_types, lifting) delivered distributed_system.next.simps(4) distributed_system_axioms hd_append2 snoc_eq_iff_butlast valid)
next
  case (Recv i' p q s s' m')
  then have "i = i'" 
    using assms(1) delivered by auto
  also have "m = Msg m'" 
    by (metis (no_types, lifting) Recv delivered list.sel(1) next_recv valid)
  ultimately show ?thesis using Recv by auto
qed

lemma message_must_be_delivered_2:
  assumes
    "c \<turnstile> ev \<mapsto> c'"
    "m : set (msgs c i)"
    "m \<notin> set (msgs c' i)"
  shows
    "(\<exists>p q. ev = RecvMarker i p q \<and> m = Marker) \<or> (\<exists>p q s s' m'. ev = Recv i p q s s' m' \<and> m = Msg m')"
proof -
  have uneq_sets: "set (msgs c i) \<noteq> set (msgs c' i)" 
    using assms(2) assms(3) by blast
  then obtain p q where chan: "channel i = Some (p, q)"
    using assms no_msgs_change_if_no_channel by fastforce
  then show ?thesis
  proof (cases ev)
    case (Snapshot p')
    with Snapshot assms chan have "set (msgs c' i) = set (msgs c i)" by (cases "p' = p", auto)
    then show ?thesis using uneq_sets by simp
  next
    case (Trans p' s s')
    then show ?thesis using uneq_sets assms by simp
  next
    case (Send i' p' q' s s' m)
    then show ?thesis
      by (metis (no_types, lifting) UnCI assms(1) assms(2) assms(3) local.next.simps(4) set_append)
  next
    case (RecvMarker i' p' q')
    have "i' = i"
    proof (rule ccontr)
      assume "~ i' = i"
      show False using assms chan RecvMarker
      proof (cases "has_snapshotted c p'")
        case True
        then show False using assms chan RecvMarker \<open>~ i' = i\<close> by simp
      next
        case False
        then show False using assms chan RecvMarker \<open>~ i' = i\<close> by (cases "p' = p", simp_all)
      qed
    qed
    moreover have "m = Marker"
    proof -
      have "msgs c i' = Marker # msgs c' i'" using assms chan RecvMarker by auto
      then show ?thesis using assms \<open>i' = i\<close> by simp
    qed
    ultimately show ?thesis using RecvMarker by simp
  next
    case (Recv i' p' q' s s' m')
    have "i' = i"
    proof (rule ccontr)
      assume "~ i' = i"
      then show False 
        using Recv assms(1) uneq_sets by auto
    qed
    then have "i' = i \<and> m = Msg m'" 
      using Recv assms by auto
    then show ?thesis using Recv by simp
  qed
qed

lemma recv_marker_means_snapshotted_1:
  assumes
    "ev = RecvMarker i p q" and
    "c \<turnstile> ev \<mapsto> c'"
  shows
    "has_snapshotted c' p"
  using assms snapshot_state_unchanged by (cases "has_snapshotted c p", auto)

lemma recv_marker_means_snapshotted_2:
  fixes
    c c' :: "('p, 's, 'm) configuration" and
    ev :: "('p, 's, 'm) event" and
    i :: channel_id
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "Marker : set (msgs c i)" and
    "Marker \<notin> set (msgs c' i)" and
    "channel i = Some (q, p)"
  shows
    "has_snapshotted c' p"
proof -
  have "\<exists>p q. ev = RecvMarker i p q"
    using assms message_must_be_delivered_2 by blast
  then obtain r s where RecvMarker: "ev = RecvMarker i r s"
    by blast
  then have "r = p"
    using assms(1) assms(4) can_occur_def by auto
  then show ?thesis
    using recv_marker_means_snapshotted_1 assms RecvMarker by blast
qed

lemma event_stays_valid_if_no_occurrence:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "occurs_on ev \<noteq> occurs_on ev'" and
    "can_occur ev' c"
  shows
    "can_occur ev' c'"
proof (cases ev')
  case (Trans p s s')
  have "states c p = states c' p"
    using Trans assms(1) assms(2) no_state_change_if_no_event by auto
  moreover have "states c p = s" using can_occur_def assms Trans by simp
  ultimately have "states c' p = s" by simp
  moreover have "trans p s s'" 
    using Trans assms(3) can_occur_def by auto
  ultimately show ?thesis 
    by (simp add: Trans can_occur_def)
next
  case (Recv i p q s s' m)
  then have "hd (msgs c i) = Msg m"
  proof -
    from Recv have "length (msgs c i) > 0" using assms(3) can_occur_def by auto
    then obtain m' xs where mcqp: "msgs c i = m' # xs"
      by (metis list.size(3) nat_less_le neq_Nil_conv)
    then have "Msg m = m'"
    proof (cases m', auto)
      case Marker
      then have "msgs c i = Marker # xs" by (simp add:mcqp)
      then have "~ can_occur ev' c" using Recv can_occur_def by simp
      then show False using assms(3) by simp
    next
      case (Msg msg)
      then have "msgs c i = Msg msg # xs" by (simp add: mcqp)
      then show "m = msg" using Recv can_occur_def assms(3) by simp
    qed
    then show ?thesis by (simp add: mcqp)
  qed
  show ?thesis
  proof (rule ccontr)
    assume asm: "~ can_occur ev' c'"
    then have "msgs c' i = [] \<or> hd (msgs c' i) \<noteq> Msg m"
      using Recv assms can_occur_def no_state_change_if_no_event distributed_system_axioms list.case_eq_if by fastforce
    then obtain i' p' q' s'' s''' m' where RMoR: "ev = RecvMarker i' p' q' \<or> ev = Recv i p' q' s'' s''' m'"
      by (metis Recv \<open>hd (msgs c i) = Msg m\<close> assms(1) assms(3) can_occur_Recv list.discI message_must_be_delivered)
    then have "occurs_on ev = p" 
    proof -
      have f1: "states c p = s \<and> channel i = Some (q, p) \<and> recv i p q s s' m \<and> 0 < length (msgs c i) \<and> hd (msgs c i) = Msg m"
        using Recv assms(3) can_occur_def by force
      have f2: "RecvMarker i' p' q' = ev \<or> states c p' = s'' \<and> channel i = Some (q', p') \<and> recv i p' q' s'' s''' m' \<and> 0 < length (msgs c i) \<and> hd (msgs c i) = Msg m'"
        using RMoR assms(1) can_occur_def by force
      have "\<forall>e n c. \<exists>p pa s sa m. \<forall>ca cb. (\<not> c \<turnstile> e \<mapsto> ca \<or> msgs ca n \<noteq> [] \<or> hd (msgs c n) = Marker \<or> msgs c n = [] \<or> Recv n p pa s sa m = e) \<and> (\<not> c \<turnstile> e \<mapsto> cb \<or> hd (msgs c n) = Marker \<or> hd (msgs cb n) = hd (msgs c n) \<or> msgs c n = [] \<or> Recv n p pa s sa m = e)"
        by (metis (no_types) message_must_be_delivered)
      then show ?thesis
        using f2 f1 by (metis RMoR \<open>msgs c' i = [] \<or> hd (msgs c' i) \<noteq> Msg m\<close> assms(1) event.disc(13,15) event.sel(3,5) length_greater_0_conv message.distinct(1) option.inject prod.inject)
    qed
    then show False using assms Recv by simp
  qed
next
  case (Send i p q s s' m)
  then have "states c p = states c' p" using assms no_state_change_if_no_event by auto
  then show "can_occur ev' c'" using assms assms(3) can_occur_def Send by auto
next
  case (RecvMarker i p q)
  then have msgs_ci: "hd (msgs c i) = Marker \<and> length (msgs c i) > 0"
  proof -
    from RecvMarker have "length (msgs c i) > 0" using assms(3) can_occur_def by auto
    then obtain m' xs where mci: "msgs c i = m' # xs"
      by (metis list.size(3) nat_less_le neq_Nil_conv)
    then have m_mark: "Marker = m'"
    proof (cases m', auto)
      case (Msg msg)
      then have "msgs c i = Msg msg # xs" by (simp add:mci)
      then have "~ can_occur ev' c" using RecvMarker can_occur_def by simp
      then show False using assms(3) by simp
    qed
    then show ?thesis by (simp add: mci)
  qed
  show ?thesis
  proof (rule ccontr)
    assume asm: "~ can_occur ev' c'"
    then have "msgs c' i = [] \<or> hd (msgs c' i) \<noteq> Marker"
      using RecvMarker assms(3) can_occur_def list.case_eq_if by fastforce
    then have "\<exists>p q. ev = RecvMarker i p q \<and> Marker = Marker" using message_must_be_delivered msgs_ci assms by blast
    then obtain r s where RecvMarker_ev: "ev = RecvMarker i r s" by blast
    then have "p = r \<and> q = s" 
      using RecvMarker assms(1) assms(3) can_occur_def by auto
    then have "occurs_on ev = p" using assms RecvMarker_ev by auto
    then show False using assms using RecvMarker by auto
  qed
next
  case (Snapshot p)
  then have "~ has_snapshotted c p" using assms assms(3) can_occur_def by simp
  show ?thesis
  proof (rule ccontr)
    assume asm: "~ can_occur ev' c'"
    then have "has_snapshotted c' p" using can_occur_def Snapshot by simp
    then have "occurs_on ev = p"
      using \<open>\<not> has_snapshotted c p\<close> assms(1) no_state_change_if_no_event by fastforce
    then show False using assms(2) Snapshot by auto
  qed
qed

lemma msgs_unchanged_for_other_is:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "regular_event ev" and
    "getId ev = i" and
    "i' \<noteq> i"
  shows
    "msgs c i' = msgs c' i'"
proof -
  have "isTrans ev \<or> isSend ev \<or> isRecv ev" using assms by simp
  then show ?thesis
  proof (elim disjE, goal_cases)
    case 1
    then obtain p s s' where "ev = Trans p s s'" by (meson isTrans_def)
    then show ?thesis using assms by simp
  next
    case 2
    then obtain i' p q s s' m where "ev = Send i' p q s s' m" by (meson isSend_def)
    then show ?thesis using assms by simp
  next
    case 3
    then obtain i' p q s s' m where "ev = Recv i' p q s s' m" by (meson isRecv_def)
    with assms show ?thesis by auto
  qed
qed

lemma msgs_unchanged_if_snapshotted_RecvMarker_for_other_is:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "ev = RecvMarker i p q" and
    "has_snapshotted c p" and
    "i' \<noteq> i"
  shows
    "msgs c i' = msgs c' i'"
  using assms by auto

lemma event_can_go_back_if_no_sender:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "occurs_on ev \<noteq> occurs_on ev'" and
    "can_occur ev' c'" and
    "~ isRecvMarker ev'" and
    "~ isSend ev"
  shows
    "can_occur ev' c"
proof (cases ev')
  case (Snapshot p)
  then have "~ has_snapshotted c' p" using assms(3) can_occur_def by simp
  then have "~ has_snapshotted c p" using assms(1) snapshot_state_unchanged by force
  then show ?thesis using can_occur_def Snapshot by simp
next
  case (RecvMarker i p q)
  then show ?thesis using assms(4) by auto
next
  case (Trans p s s')
  then show ?thesis
    using assms(1) assms(2) can_occur_def no_state_change_if_no_event assms(3) by auto
next
  case (Send p q s s' m)
  then show ?thesis
    using assms(1) assms(2) can_occur_def no_state_change_if_no_event assms(3) by auto
next
  case (Recv i p q s s' m)
  have "msgs c' i \<noteq> Nil" using Recv can_occur_def assms by auto
  moreover have "hd (msgs c' i) = Msg m \<and> length (msgs c' i) > 0"
  proof -
    from Recv have "length (msgs c' i) > 0" using assms(3) can_occur_def by auto
    then obtain m' xs where mcqp: "msgs c' i = m' # xs"
      by (metis list.size(3) nat_less_le neq_Nil_conv)
    then have "Msg m = m'"
    proof (cases m', auto)
      case Marker
      then have "msgs c' i = Marker # xs" by (simp add:mcqp)
      then have "~ can_occur ev' c'" using Recv can_occur_def by simp
      then show False using assms(3) by simp
    next
      case (Msg msg)
      then have "msgs c' i = Msg msg # xs" by (simp add: mcqp)
      then show "m = msg" using Recv can_occur_def assms(3) by simp
    qed
    then show ?thesis by (simp add: mcqp)
  qed
  moreover have "msgs c i \<noteq> Nil \<and> hd (msgs c' i) = hd (msgs c i)"
  proof (cases ev)
    case (Snapshot p')
    then have "p' \<noteq> p" using assms Recv by simp
    have chan: "channel i = Some (q, p)" 
      by (metis Recv assms(3) distributed_system.can_occur_Recv distributed_system_axioms)
    with Snapshot assms have "length (msgs c i) > 0 \<and> hd (msgs c i) = hd (msgs c' i)"
    proof (cases "q = p'")
      case True
      then have "msgs c' i = msgs c i @ [Marker]" using Snapshot chan assms by simp
      then show ?thesis 
        by (metis append_self_conv2 calculation(2) hd_append2 length_greater_0_conv list.sel(1) message.simps(3))
    next
      case False
      then have "msgs c' i = msgs c i" using Snapshot chan assms by simp
      then show ?thesis using calculation by simp
    qed
    then show ?thesis by simp
  next
    case (RecvMarker i' p' q')
    then have "i' \<noteq> i" 
      using Recv assms(1) assms(2) assms(3) can_occur_def by force
    then show ?thesis
    proof (cases "has_snapshotted c p'")
      case True
      then have "msgs c i = msgs c' i" using \<open>i' \<noteq> i\<close> RecvMarker assms by simp
      then show ?thesis using calculation by simp
    next
      case no_snap: False
      then have chan: "channel i = Some (q, p)" 
        by (metis Recv assms(3) distributed_system.can_occur_Recv distributed_system_axioms)
      then show ?thesis
      proof (cases "q = p'")
        case True
        then have "msgs c' i = msgs c i @ [Marker]" 
          using no_snap RecvMarker \<open>i' \<noteq> i\<close> assms(1) chan by auto
        then show ?thesis 
          by (metis append_self_conv2 calculation(2) hd_append2 list.sel(1) message.simps(3))
      next
        case False
        then have "msgs c' i = msgs c i" using RecvMarker no_snap False chan assms \<open>i' \<noteq> i\<close> by simp
        then show ?thesis using calculation by simp
      qed
    qed
  next
    case (Trans p' s'' s''')
    then show ?thesis using assms(1) \<open>msgs c' i \<noteq> Nil\<close> by auto
  next
    case (Send i' p' q' s'' s''' m'')
    have "p' \<noteq> p"
      using Recv Send assms(2) by auto
    then show ?thesis 
      using Recv Send assms(1) assms(5) calculation(1) by auto
  next
    case (Recv i' p' q' s'' s''' m'')
    then have "i' \<noteq> i" using assms \<open>ev' = Recv i p q s s' m\<close> 
      by (metis distributed_system.can_occur_Recv distributed_system_axioms event.sel(3) next_recv option.inject prod.inject)
    have "msgs c i = msgs c' i" using msgs_unchanged_for_other_is Recv \<open>i' \<noteq> i\<close> assms(1) by auto
    then show ?thesis using \<open>msgs c' i \<noteq> Nil\<close> by simp
  qed
  moreover have "states c p = states c' p" using no_state_change_if_no_event assms Recv by simp
  ultimately show ?thesis
    using Recv assms(3) can_occur_def list.case_eq_if by fastforce
qed

lemma nonregular_event_can_go_back_if_in_distinct_processes:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "regular_event ev" and
    "~ regular_event ev'" and
    "can_occur ev' c'" and
    "occurs_on ev \<noteq> occurs_on ev'"
  shows
    "can_occur ev' c"
proof -
  let ?p = "occurs_on ev"
  let ?q = "occurs_on ev'"
  have "isTrans ev \<or> isSend ev \<or> isRecv ev" using assms by simp
  moreover have "isSnapshot ev' \<or> isRecvMarker ev'" using assms nonregular_event by auto
  ultimately show ?thesis
  proof (elim disjE, goal_cases)
    case 1
    then show ?case 
      using assms(1) assms(4) assms(5) event_can_go_back_if_no_sender by blast
  next
    case 2
    then obtain s s' where Trans: "ev = Trans ?p s s'"
      by (metis event.collapse(1))
    obtain i r where RecvMarker: "ev' = RecvMarker i ?q r"
      using 2 by (metis event.collapse(5))
    have "msgs c i = msgs c' i" 
      using "2"(1) assms(1) assms(2) no_msg_change_if_no_event by blast
    moreover have "can_occur ev' c'" using assms by simp
    ultimately show ?thesis using can_occur_def RecvMarker 
      by (metis (mono_tags, lifting) "2"(2) event.case_eq_if event.distinct_disc(13) event.distinct_disc(17) event.distinct_disc(19) event.distinct_disc(7) event.sel(10))
  next
    case 3
    then have "ev' = Snapshot ?q"
      by (metis event.collapse(4))
    have "~ has_snapshotted c' ?q" 
      by (metis (mono_tags, lifting) "3"(1) assms(4) can_occur_def event.case_eq_if event.distinct_disc(11) event.distinct_disc(16) event.distinct_disc(6))
    then have "~ has_snapshotted c ?q" 
      using assms(1) assms(2) regular_event_preserves_process_snapshots by auto
    then show ?case unfolding can_occur_def using \<open>ev' = Snapshot ?q\<close> 
      by (metis (mono_tags, lifting) event.simps(29))
  next
    case 4
    then have "ev' = Snapshot ?q"
      by (metis event.collapse(4))
    have "~ has_snapshotted c' ?q"
      by (metis (mono_tags, lifting) \<open>ev' = Snapshot (occurs_on ev')\<close> assms(4) can_occur_def event.simps(29))
    then have "~ has_snapshotted c ?q"
      using assms(1) assms(2) regular_event_preserves_process_snapshots by auto
    then show ?case unfolding can_occur_def 
      by (metis (mono_tags, lifting) \<open>ev' = Snapshot (occurs_on ev')\<close> event.simps(29))
  next
    case 5
    then obtain i s u u' m where "ev = Send i ?p s u u' m"
      by (metis event.collapse(2))
    from 5 obtain i' r where "ev' = RecvMarker i' ?q r"
      by (metis event.collapse(5))
    then have pre: "hd (msgs c' i') = Marker \<and> length (msgs c' i') > 0" 
      by (metis (mono_tags, lifting) assms(4) can_occur_def event.simps(30))
    have "hd (msgs c i') = Marker \<and> length (msgs c i') > 0"
    proof (cases "i' = i")
      case False
      then have "msgs c i' = msgs c' i'" 
        by (metis \<open>ev = Send i (occurs_on ev) s u u' m\<close> assms(1) assms(2) event.sel(8) msgs_unchanged_for_other_is)
      then show ?thesis using pre by auto
    next
      case True
      then have "msgs c' i' = msgs c i' @ [Msg m]" 
        by (metis \<open>ev = Send i (occurs_on ev) s u u' m\<close> assms(1) next_send)
      then have "length (msgs c' i') > 1" 
        using pre by fastforce
      then have "length (msgs c i') > 0" 
        by (simp add: \<open>msgs c' i' = msgs c i' @ [Msg m]\<close>)
      then show ?thesis 
        using \<open>msgs c' i' = msgs c i' @ [Msg m]\<close> pre by auto
    qed
    then show ?case unfolding can_occur_def using \<open>ev' = RecvMarker i' ?q r\<close> 
      by (metis (mono_tags, lifting) assms(4) can_occur_def event.simps(30))
  next
    case 6
    then obtain i s u u' m where "ev = Recv i ?p s u u' m"
      by (metis event.collapse(3))
    from 6 obtain i' r where "ev' = RecvMarker i' ?q r"
      by (metis event.collapse(5))
    then have "i' \<noteq> i"
    proof -
      have "?p \<noteq> ?q" using assms by simp
      moreover have "channel i = Some (s, ?p)" 
        by (metis \<open>ev = Recv i (occurs_on ev) s u u' m\<close> assms(1) distributed_system.can_occur_Recv distributed_system_axioms happen_implies_can_occur)
      moreover have "channel i' = Some (r, ?q)"
        by (metis (mono_tags, lifting) \<open>ev' = RecvMarker i' (occurs_on ev') r\<close> assms(4) can_occur_def event.case_eq_if event.disc(5,10,15,20) event.sel(5,10,13))
      ultimately show ?thesis by auto
    qed
    then show ?case
      by (metis (mono_tags, lifting) "6"(1) \<open>ev = Recv i (occurs_on ev) s u u' m\<close> \<open>ev' = RecvMarker i' (occurs_on ev') r\<close> assms(1) assms(4) can_occur_def event.case_eq_if event.distinct_disc(13) event.distinct_disc(17) event.distinct_disc(7) event.sel(10) next_recv)
  qed
qed

lemma same_state_implies_same_result_state:
  assumes
    "states c p = states d p"
    "c \<turnstile> ev \<mapsto> c'" and
    "d \<turnstile> ev \<mapsto> d'"
  shows
    "states d' p = states c' p"
proof (cases "occurs_on ev = p")
  case False
  then show ?thesis 
    by (metis assms(1-3) distributed_system.no_state_change_if_no_event distributed_system_axioms)
next
  case True
  then show ?thesis
    using assms by (cases ev, auto)
qed

lemma same_snapshot_state_implies_same_result_snapshot_state:
  assumes
    "ps c p = ps d p" and
    "states c p = states d p" and
    "c \<turnstile> ev \<mapsto> c'" and
    "d \<turnstile> ev \<mapsto> d'"
  shows
    "ps d' p = ps c' p"
proof (cases "occurs_on ev = p")
  case False
  then show ?thesis
    using assms no_state_change_if_no_event by auto
next
  case True
  then show ?thesis
  proof (cases ev)
    case (Snapshot q)
    then have "p = q" using True by auto
    then show ?thesis 
      using Snapshot assms(2) assms(3) assms(4) by auto
  next
    case (RecvMarker i q r)
    then have "p = q" using True by auto
    then show ?thesis 
    proof -
      have f1: "\<And>c ca. \<not> c \<turnstile> ev \<mapsto> ca \<or> ps c p = None \<or> ps c p = ps ca p"
        using RecvMarker \<open>p = q\<close> by force
      have "\<And>c ca. ps c p \<noteq> None \<or> \<not> c \<turnstile> ev \<mapsto> ca \<or> ps ca p = Some (states c p)"
        using RecvMarker \<open>p = q\<close> by force
      then show ?thesis
        using f1 by (metis (no_types) assms(1) assms(2) assms(3) assms(4))
    qed
  next
    case (Trans q s s')
    then have "p = q" 
      using True by auto
    then show ?thesis 
      using Trans assms(1) assms(3) assms(4) by auto
  next
    case (Send i q r u u' m)
    then have "p = q" using True by auto
    then show ?thesis 
      using Send assms(1) assms(3) assms(4) by auto
  next
    case (Recv i q r u u' m)
    then have "p = q" using True by auto
    then show ?thesis 
      using Recv assms(1) assms(3) assms(4) by auto
  qed
qed

lemma same_messages_imply_same_resulting_messages:
  assumes
    "msgs c i = msgs d i"
    "c \<turnstile> ev \<mapsto> c'" and
    "d \<turnstile> ev \<mapsto> d'" and
    "regular_event ev"
  shows
    "msgs c' i = msgs d' i"
proof -
  have "isTrans ev \<or> isSend ev \<or> isRecv ev" using assms 
    by simp
  then show ?thesis
  proof (elim disjE)
    assume "isTrans ev"
    then show ?thesis 
      by (metis assms(1) assms(2) assms(3) isTrans_def next_trans)
  next
    assume "isSend ev"
    then obtain i' r s u u' m where "ev = Send i' r s u u' m"
      by (metis event.collapse(2))
    with assms show ?thesis by (cases "i = i'", auto)
  next
    assume "isRecv ev"
    then obtain i' r s u u' m where Recv: "ev = Recv i' r s u u' m"
      by (metis event.collapse(3))
    with assms show ?thesis by (cases "i = i'", auto)
  qed
qed

lemma Trans_msg:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "isTrans ev"
  shows
    "msgs c i = msgs c' i"
  using assms(1) assms(2) no_msg_change_if_no_event regular_event by blast

lemma new_msg_in_set_implies_occurrence:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "m \<notin> set (msgs c i)" and
    "m \<in> set (msgs c' i)" and
    "channel i = Some (p, q)"
  shows
    "occurs_on ev = p" (is ?P)
proof (rule ccontr)
  assume "~ ?P"
  have "set (msgs c' i) \<subseteq> set (msgs c i)" 
  proof (cases ev)
    case (Snapshot r)
    then have "msgs c' i = msgs c i" using \<open>~ ?P\<close> assms by simp
    then show ?thesis by auto
  next
    case (RecvMarker i' r s)
    then show ?thesis
    proof (cases "has_snapshotted c r")
      case True
      then show ?thesis
      proof (cases "i' = i")
        case True
        then have "Marker # msgs c' i = msgs c i" using RecvMarker True assms by simp
        then show ?thesis 
          by (metis set_subset_Cons)
      next
        case False
        then show ?thesis using RecvMarker True assms by simp
      qed
    next
      case no_snap: False
      have chan: "channel i' = Some (s, r)" 
        using RecvMarker assms(1) can_occur_def by auto
      then show ?thesis
      proof (cases "i' = i")
        case True
        then have "Marker # msgs c' i = msgs c i" using RecvMarker assms by simp
        then show ?thesis by (metis set_subset_Cons)
      next
        case False
        then have "msgs c' i = msgs c i" using \<open>~ ?P\<close> RecvMarker assms no_snap by simp
        then show ?thesis by simp
      qed
    qed
  next
    case (Trans r u u')
    then show ?thesis using assms \<open>~ ?P\<close> by simp
  next
    case (Send i' r s u u' m')
    then have "i' \<noteq> i" using \<open>~ ?P\<close> can_occur_def assms by auto
    then have "msgs c i = msgs c' i" using \<open>~ ?P\<close> assms Send by simp
    then show ?thesis by simp
  next
    case (Recv i' r s u u' m')
    then show ?thesis 
      by (metis (no_types, lifting) assms(1) eq_iff local.next.simps(5) set_subset_Cons)
  qed
  moreover have "~ set (msgs c' i) \<subseteq> set (msgs c i)" using assms by blast
  ultimately show False by simp
qed

lemma new_Marker_in_set_implies_nonregular_occurence:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "Marker \<notin> set (msgs c i)" and
    "Marker \<in> set (msgs c' i)" and
    "channel i = Some (p, q)"
  shows
    "~ regular_event ev" (is ?P)
proof (rule ccontr)
  have "occurs_on ev = p" 
    using assms new_msg_in_set_implies_occurrence by blast
  assume "~ ?P"
  then have "isTrans ev \<or> isSend ev \<or> isRecv ev" by simp
  then have "Marker \<notin> set (msgs c' i)"
  proof (elim disjE, goal_cases)
    case 1
    then obtain r u u' where "ev = Trans r u u'"
      by (metis event.collapse(1))
    then show ?thesis 
      using assms(1) assms(2) by auto
  next
    case 2
    then obtain i' r q u u' m where "ev = Send i' r q u u' m"
      by (metis event.collapse(2))
    then show ?thesis 
      by (metis (no_types, lifting) Un_iff assms(1) assms(2) empty_iff empty_set insert_iff list.set(2) message.distinct(1) next_send set_append)
  next
    case 3
    then obtain i' r q u u' m where "ev = Recv i' r q u u' m"
      by (metis event.collapse(3))
    then show ?thesis 
      by (metis assms(1) assms(2) list.set_intros(2) next_recv)
  qed
  then show False using assms by simp
qed

lemma RecvMarker_implies_Marker_in_set:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "ev = RecvMarker cid p q"
  shows
    "Marker \<in> set (msgs c cid)"
  by (metis (mono_tags, lifting) assms(1) assms(2) can_occur_def distributed_system.happen_implies_can_occur distributed_system_axioms event.simps(30) list.set_sel(1) list.size(3) nat_less_le)

lemma RecvMarker_given_channel:
  assumes
    "isRecvMarker ev" and
    "getId ev = cid" and
    "channel cid = Some (p, q)" and
    "can_occur ev c"
  shows
    "ev = RecvMarker cid q p"
  by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) assms(4) can_occur_def event.case_eq_if event.collapse(5) event.distinct_disc(8,14,18,20) option.inject prod.inject)

lemma Recv_given_channel:
  assumes
    "isRecv ev" and
    "getId ev = cid" and
    "channel cid = Some (p, q)" and
    "can_occur ev c"
  shows
    "\<exists>s s' m. ev = Recv cid q p s s' m"
  by (metis assms(1) assms(2) assms(3) assms(4) distributed_system.can_occur_Recv distributed_system_axioms event.collapse(3) option.inject prod.inject)

lemma same_cs_if_not_recv:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "~ isRecv ev"
  shows
     "fst (cs c cid) = fst (cs c' cid)"
proof (cases "channel cid = None")
  case True
  then show ?thesis 
    using assms(1) no_cs_change_if_no_channel by auto
next
  case False
  then obtain p q where chan: "channel cid = Some (p, q)" by auto
  then show ?thesis
  proof (cases ev)
    case (Snapshot r)
    with Snapshot assms chan show ?thesis by (cases "r = q", auto)
  next
    case (RecvMarker cid' r s)
    then show ?thesis
    proof (cases "has_snapshotted c r")
      case True
      with assms RecvMarker chan show ?thesis by (cases "cid' = cid", auto)
    next
      case no_snap: False
      then show ?thesis
      proof (cases "cid' = cid")
        case True
        then show ?thesis using RecvMarker assms chan by auto
      next
        case False
        with assms RecvMarker chan no_snap show ?thesis by (cases "r = q", auto)
      qed
    qed
  next
    case (Trans r u u')
    then show ?thesis using assms by auto
  next
    case (Send r s u u')
    then show ?thesis using assms by auto
  qed (metis assms(2) isRecv_def)
qed

lemma done_only_from_recv_marker:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "channel cid = Some (p, q)" and
    "snd (cs c cid) \<noteq> Done" and
    "snd (cs c' cid) = Done"
  shows
    "ev = RecvMarker cid q p"
proof (rule ccontr)
  assume "~ ev = RecvMarker cid q p"
  then show False
  proof (cases "isRecvMarker ev")
    case True
    then obtain cid' s r where RecvMarker: "ev = RecvMarker cid' s r" by (meson isRecvMarker_def)
    have "cid \<noteq> cid'"
    proof (rule ccontr)
      assume "~ cid \<noteq> cid'"
      then show False
        using \<open>ev = RecvMarker cid' s r\<close> \<open>ev \<noteq> RecvMarker cid q p\<close> assms(1) assms(2) can_occur_def by auto
    qed
    then have "snd (cs c' cid) \<noteq> Done"
    proof (cases "has_snapshotted c s")
      case True
      then show ?thesis using RecvMarker assms \<open>cid \<noteq> cid'\<close> by simp
    next
      case False
      with RecvMarker assms \<open>cid \<noteq> cid'\<close> show ?thesis by (cases "s = q", auto)
    qed
    then show False using assms by auto
  next
    case False
    then have "isSnapshot ev \<or> isTrans ev \<or> isSend ev \<or> isRecv ev"
    using event.exhaust_disc by blast
    then have "snd (cs c' cid) \<noteq> Done"
    proof (elim disjE, goal_cases)
      case 1
      then obtain r where Snapshot: "ev = Snapshot r"
        by (meson isSnapshot_def)
      with assms show ?thesis by (cases "q = r", auto)
    next
      case 2
      then obtain r u u' where "ev = Trans r u u'"
        by (meson isTrans_def)
      then show ?case using assms by auto
    next
      case 3
      then obtain cid' r s u u' m where "ev = Send cid' r s u u' m"
        by (meson isSend_def)
      then show ?thesis using assms by auto
    next
      case 4
      then obtain cid' r s u u' m where Recv: "ev = Recv cid' r s u u' m"
        by (meson isRecv_def)
      show ?thesis
      using Recv assms proof (cases "cid = cid'")
        case True
        then have "snd (cs c cid) = NotStarted \<or> snd (cs c cid) = Recording"
          using assms(3) recording_state.exhaust by blast
        then show ?thesis
        proof (elim disjE, goal_cases)
          case 1
          then have "snd (cs c' cid') = NotStarted" 
            using True Recv assms(1) by auto
          then show ?case using True by auto
        next
          case 2
          then have "snd (cs c' cid') = Recording"
            using True Recv assms(1) by auto
          then show ?case using True by auto
        qed
      qed auto
    qed
    then show False using assms by auto
  qed
qed

lemma cs_not_not_started_stable:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "snd (cs c cid) \<noteq> NotStarted" and
    "channel cid = Some (p, q)"
  shows
    "snd (cs c' cid) \<noteq> NotStarted"
using assms proof (cases ev)
  case (Snapshot r)
  then show ?thesis 
    by (metis assms(1) assms(2) next_snapshot recording_state.simps(2) sndI)
next
  case (RecvMarker cid' r s)
  then show ?thesis
  proof (cases "has_snapshotted c r")
    case True
    with RecvMarker assms show ?thesis by (cases "cid = cid'", auto)
  next
    case no_snap: False
    then show ?thesis
    proof (cases "cid = cid'")
      case True
      then show ?thesis using RecvMarker assms by auto
    next
      case False
      with RecvMarker assms no_snap show ?thesis by (cases "s = p", auto)
    qed
  qed
next
  case (Recv cid' r s u u' m)
  then have "snd (cs c cid) = Recording \<or> snd (cs c cid) = Done" 
    using assms(2) recording_state.exhaust by blast
  then show ?thesis
  proof (elim disjE, goal_cases)
    case 1
    then show ?thesis 
      by (metis (no_types, lifting) Recv assms(1) eq_snd_iff next_recv recording_state.distinct(1))
  next
    case 2
    with Recv assms show ?thesis by (cases "cid = cid'", auto)
  qed
qed auto

lemma fst_cs_changed_by_recv_recording:
  assumes
    step: "c \<turnstile> ev \<mapsto> c'" and
    "fst (cs c cid) \<noteq> fst (cs c' cid)" and
    "channel cid = Some (p, q)"
  shows
    "snd (cs c cid) = Recording \<and> (\<exists>p q u u' m. ev = Recv cid q p u u' m)"
proof -
  have oc_on: "occurs_on ev = q" 
  proof -
    obtain nn :: "('p, 's, 'm) event \<Rightarrow> nat" and aa :: "('p, 's, 'm) event \<Rightarrow> 'p" and aaa :: "('p, 's, 'm) event \<Rightarrow> 'p" and bb :: "('p, 's, 'm) event \<Rightarrow> 's" and bba :: "('p, 's, 'm) event \<Rightarrow> 's" and cc :: "('p, 's, 'm) event \<Rightarrow> 'm" where
      f1: "\<forall>e. (\<not> isRecv e \<or> e = Recv (nn e) (aa e) (aaa e) (bb e) (bba e) (cc e)) \<and> (isRecv e \<or> (\<forall>n a aa b ba c. e \<noteq> Recv n a aa b ba c))"
      using isRecv_def by moura
    then have f2: "c \<turnstile> Recv (nn ev) (aa ev) (aaa ev) (bb ev) (bba ev) (cc ev) \<mapsto> c'"
      by (metis (no_types) assms(2) local.step same_cs_if_not_recv)
    have f3: "\<forall>x0 x1 x7 x8. (x0 \<noteq> x7 \<longrightarrow> cs (x8::('p, 's, 'm) configuration) x0 = cs (x1::('p, 's, _) configuration) x0) = (x0 = x7 \<or> cs x8 x0 = cs x1 x0)"
      by auto
    have f4: "\<forall>x0 x1 x7 x8. (x7 \<noteq> x0 \<longrightarrow> msgs (x1::('p, 's, 'm) configuration) x0 = msgs (x8::('p, 's, _) configuration) x0) = (x7 = x0 \<or> msgs x1 x0 = msgs x8 x0)"
      by auto
    have "\<forall>x0 x1 x6 x8. (x0 \<noteq> x6 \<longrightarrow> states (x1::('p, 's, 'm) configuration) x0 = states (x8::(_, _, 'm) configuration) x0) = (x0 = x6 \<or> states x1 x0 = states x8 x0)"
      by fastforce
    then have "can_occur (Recv (nn ev) (aa ev) (aaa ev) (bb ev) (bba ev) (cc ev)) c \<and> states c (aa ev) = bb ev \<and> states c' (aa ev) = bba ev \<and> (\<forall>a. a = aa ev \<or> states c' a = states c a) \<and> msgs c (nn ev) = Msg (cc ev) # msgs c' (nn ev) \<and> (\<forall>n. nn ev = n \<or> msgs c' n = msgs c n) \<and> (\<forall>a. ps c a = ps c' a) \<and> (\<forall>n. n = nn ev \<or> cs c n = cs c' n) \<and> (if snd (cs c (nn ev)) = Recording then cs c' (nn ev) = (fst (cs c (nn ev)) @ [cc ev], Recording) else cs c (nn ev) = cs c' (nn ev))"
    using f4 f3 f2 by force
  then show ?thesis
    using f1 by (metis (no_types) Pair_inject assms(2) assms(3) can_occur_Recv event.sel(3) local.step option.sel same_cs_if_not_recv)
qed
  have "isRecv ev" (is ?P)
  proof (rule ccontr)
    assume "~ ?P"
    then have "fst (cs c cid) = fst (cs c' cid)" by (metis local.step same_cs_if_not_recv)
    then show False using assms by simp
  qed
  then obtain cid' r s u u' m where Recv: "ev = Recv cid' r s u u' m" by (meson isRecv_def)
  have "cid = cid'"
  proof (rule ccontr)
    assume "~ cid = cid'"
    then have "fst (cs c cid) = fst (cs c' cid)" using Recv step by auto
    then show False using assms by simp
  qed
  moreover have "snd (cs c cid) = Recording"
  proof (rule ccontr)
    assume "~ snd (cs c cid) = Recording"
    then have "fst (cs c cid) = fst (cs c' cid)" using Recv step \<open>cid = cid'\<close> by auto
    then show False using assms by simp
  qed
  ultimately show ?thesis using Recv by simp
qed

lemma no_marker_and_snapshotted_implies_no_more_markers:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "has_snapshotted c p" and
    "Marker \<notin> set (msgs c cid)" and
    "channel cid = Some (p, q)"
  shows
    "Marker \<notin> set (msgs c' cid)"
proof (cases ev)
  case (Snapshot r)
  then have "r \<noteq> p" 
    using assms(1) assms(2) can_occur_def by auto
  then have "msgs c cid = msgs c' cid" using assms Snapshot by simp
  then show ?thesis using assms by simp
next
  case (RecvMarker cid' r s)
  have "cid \<noteq> cid'"
  proof (rule ccontr)
    assume "~ cid \<noteq> cid'"
    moreover have "can_occur ev c" using happen_implies_can_occur assms by blast
    ultimately have "Marker : set (msgs c cid)" using can_occur_def RecvMarker 
      by (metis (mono_tags, lifting) assms(1) event.simps(30) hd_in_set list.size(3) recv_marker_other_channels_not_shrinking zero_order(1))
    then show False using assms by simp
  qed
  then have "msgs c cid = msgs c' cid"
  proof (cases "r = p")
    case True
    then show ?thesis 
      using RecvMarker \<open>cid \<noteq> cid'\<close> assms(1) assms(2) msgs_unchanged_if_snapshotted_RecvMarker_for_other_is by blast
  next
    case False
    with RecvMarker \<open>cid \<noteq> cid'\<close> step assms show ?thesis by (cases "has_snapshotted c r", auto)
  qed
  then show ?thesis using assms by simp
next
  case (Trans r u u')
  then show ?thesis using assms by auto
next
  case (Send cid' r s u u' m)
  with assms Send show ?thesis by (cases "cid = cid'", auto)
next
  case (Recv cid' r s u u' m)
  with assms Recv show ?thesis by (cases "cid = cid'", auto)
qed

lemma same_messages_if_no_occurrence:
  assumes
    "c \<turnstile> ev \<mapsto> c'" and
    "~ occurs_on ev = p" and
    "~ occurs_on ev = q" and
    "channel cid = Some (p, q)"
  shows
    "msgs c cid = msgs c' cid \<and> cs c cid = cs c' cid"
proof (cases ev)
  case (Snapshot r)
  then show ?thesis using assms by auto
next
  case (RecvMarker cid' r s)
  have "cid \<noteq> cid'"
    by (metis RecvMarker_given_channel assms(1) assms(3) assms(4) RecvMarker event.sel(5,10) happen_implies_can_occur isRecvMarker_def)
  have "\<nexists>a. channel cid = Some (r, q)" 
    using assms(2) assms(4) RecvMarker by auto
  with RecvMarker assms \<open>cid \<noteq> cid'\<close> show ?thesis by (cases "has_snapshotted c r", auto)
next
  case (Trans r u u')
  then show ?thesis using assms by auto
next
  case (Send cid' r s u u' m)
  then have "cid \<noteq> cid'" 
    by (metis (mono_tags, lifting) Pair_inject assms(1) assms(2) assms(4) can_occur_def event.sel(2) event.simps(27) happen_implies_can_occur option.inject)
  then show ?thesis using assms Send by simp
next
  case (Recv cid' r s u u' m)
  then have "cid \<noteq> cid'" 
    by (metis assms(1) assms(3) assms(4) distributed_system.can_occur_Recv distributed_system.happen_implies_can_occur distributed_system_axioms event.sel(3) option.inject prod.inject)
  then show ?thesis using assms Recv by simp
qed

end (* locale distributed_system *)

end (* theory Distributed_System *)
