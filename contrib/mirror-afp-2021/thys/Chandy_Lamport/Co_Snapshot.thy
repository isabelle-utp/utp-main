theory Co_Snapshot
  imports
    Snapshot
    Ordered_Resolution_Prover.Lazy_List_Chain
begin

section \<open>Extension to infinite traces\<close>

text \<open>The computation locale assumes that there already exists a known
final configuration $c'$ to the given initial $c$ and trace $t$. However,
we can show that the snapshot algorithm must terminate correctly even if
the underlying computation itself does not terminate. We relax
the trace relation to allow for a potentially infinite number of ``intermediate'' events, and
show that the algorithm's correctness still holds when imposing the same constraints
as in the computation locale.

We use a preexisting theory of lazy list chains by Schlichtkrull, Blanchette,
Traytel and Waldmann~\cite{Ordered_Resolution_Prover-AFP} to construct infinite traces.\<close>

primrec ltake where
  "ltake 0 t = []"
| "ltake (Suc i) t = (case t of LNil \<Rightarrow> [] | LCons x t' \<Rightarrow> x # ltake i t')"

primrec ldrop where
  "ldrop 0 t = t"
| "ldrop (Suc i) t = (case t of LNil \<Rightarrow> LNil | LCons x t' \<Rightarrow> ldrop i t')"

lemma ltake_LNil[simp]: "ltake i LNil = []"
  by (induct i) auto

lemma ltake_LCons: "0 < i \<Longrightarrow> ltake i (LCons x t) = x # ltake (i - 1) t"
  by (induct i) auto

lemma take_ltake: "i \<le> j \<Longrightarrow> take i (ltake j xs) = ltake i xs"
  by (induct j arbitrary: i xs) (auto simp: le_Suc_eq take_Cons' ltake_LCons split: llist.splits if_splits)

lemma nth_ltake [simp]: "i < min n (llength xs) \<Longrightarrow> (ltake n xs) ! i = lnth xs i"
  by (induct n arbitrary: i xs)
    (auto simp: nth_Cons' gr0_conv_Suc eSuc_enat[symmetric] split: llist.splits)

lemma length_ltake[simp]: "length (ltake i xs) = (case llength xs of \<infinity> \<Rightarrow> i | enat m \<Rightarrow> min i m)"
  by (induct i arbitrary: xs)
    (auto simp: zero_enat_def[symmetric] eSuc_enat split: llist.splits enat.splits)

lemma ltake_prepend:
  "ltake i (prepend xs t) = (if i \<le> length xs then take i xs else xs @ ltake (i - length xs) t)"
proof (induct i arbitrary: xs t)
  case 0
  then show ?case 
    by (cases xs) auto
next
  case (Suc i)
  then show ?case
    by (cases xs) auto
qed

lemma prepend_ltake_ldrop_id: "prepend (ltake i t) (ldrop i t) = t"
  by (induct i arbitrary: t) (auto split: llist.splits)

context distributed_system
begin

coinductive cotrace where
    cotr_init: "cotrace c LNil"
  | cotr_step: "\<lbrakk> c \<turnstile> ev \<mapsto> c'; cotrace c' t \<rbrakk> \<Longrightarrow> cotrace c (LCons ev t)"

lemma cotrace_trace: "cotrace c t \<Longrightarrow> \<exists>!c'. trace c (ltake i t) c'"
proof (induct i arbitrary: c t)
  case (Suc i)
  then show ?case
  proof (cases t)
    case (LCons ev t')
    with Suc(2) obtain c' where "c \<turnstile> ev \<mapsto> c'" "cotrace c' t'"
      by (auto elim: cotrace.cases)
    with Suc(1)[OF \<open>cotrace c' t'\<close>] show ?thesis
      by (auto simp: LCons elim: trace.intros(2) elim: trace.cases trace_and_start_determines_end)
  qed (auto intro: trace.intros elim: trace.cases)
qed (auto simp: zero_enat_def[symmetric] intro: trace.intros elim: trace.cases)

lemma cotrace_trace': "cotrace c t \<Longrightarrow> \<exists>c'. trace c (ltake i t) c'"
  by (metis cotrace_trace)

definition cos where "cos c t i = s c (ltake i t) i"

lemma cotrace_trace_cos: "cotrace c t \<Longrightarrow> trace c (ltake i t) (cos c t i)"
  unfolding cos_def s_def
  by (subst take_ltake, auto dest!: cotrace_trace[of _ _ i] elim!: theI')

lemma s_0[simp]: "s c t 0 = c"
  unfolding s_def
  by (auto intro!: the_equality[where P = "trace c []"] trace.intros elim: trace.cases)

lemma s_chop: "i \<le> length t \<Longrightarrow> s c t i = s c (take i t) i"
  unfolding s_def
  by auto

lemma cotrace_prepend: "trace c t c' \<Longrightarrow> cotrace c' u \<Longrightarrow> cotrace c (prepend t u)"
  by (induct c t c' rule: trace.induct) (auto intro: cotrace.intros)

lemma s_Cons: "\<exists>c''. trace c' xs c'' \<Longrightarrow> c \<turnstile> ev \<mapsto> c' \<Longrightarrow> s c (ev # xs) (Suc i) = s c' xs i"
  by (smt exists_trace_for_any_i take_Suc_Cons tr_step trace_and_start_determines_end)

lemma cotrace_ldrop: "cotrace c t \<Longrightarrow> i \<le> llength t \<Longrightarrow> cotrace (cos c t i) (ldrop i t)"
proof (induct i arbitrary: c t)
  case (Suc i)
  then show ?case
  proof (cases t)
    case (LCons ev t')
    with Suc(2) obtain c' where "c \<turnstile> ev \<mapsto> c'" "cotrace c' t'"
      by (auto elim: cotrace.cases)
    with Suc(1)[OF \<open>cotrace c' t'\<close>] Suc(3) show ?thesis
      by (auto simp: LCons cos_def eSuc_enat[symmetric] s_chop[symmetric] s_Cons[OF cotrace_trace'])
  qed (auto intro: cotrace.intros)
qed (auto simp: zero_enat_def[symmetric] cos_def intro: cotrace.intros)

end

locale cocomputation = distributed_system +
  fixes
    init :: "('a, 'b, 'c) configuration"
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
      "\<forall>p. \<not> has_snapshotted init p" and
    no_initial_channel_snapshot:
      "\<forall>i. channel_snapshot init i = ([], NotStarted)" and

    valid: "\<exists>t. cotrace init t" and
    l1: "\<forall>t i cid. cotrace init t
                 \<and> Marker \<in> set (msgs (cos init t i) cid)
      \<longrightarrow> (\<exists>j \<le> llength t. j \<ge> i \<and> Marker \<notin> set (msgs (cos init t j) cid))" and
    l2: "\<forall>t p. cotrace init t
      \<longrightarrow> (\<exists>i \<le> llength t. has_snapshotted (cos init t i) p)"
begin

abbreviation coS where "coS \<equiv> cos init"

definition "some_snapshot t p = (SOME i. has_snapshotted (coS t i) p \<and> i \<le> llength t)"

lemma has_snapshotted: 
  "cotrace init t \<Longrightarrow> has_snapshotted (coS t (some_snapshot t p)) p \<and> some_snapshot t p \<le> llength t"
  unfolding some_snapshot_def by (rule someI_ex) (auto dest!: l2[rule_format])

lemma cotrace_cos: "cotrace init t \<Longrightarrow> j < llength t \<Longrightarrow> 
  (coS t j) \<turnstile> lnth t j \<mapsto> (coS t (Suc j))"
  apply (drule cotrace_trace_cos[of _ _ "Suc j"])
  apply (drule step_Suc[rotated, of _ _ _ "j"])
   apply (auto split: enat.splits llist.splits) []
  apply (auto simp: s_chop[of j "_ # ltake j _"] cos_def nth_Cons' ltake_LCons lnth_LCons'
    take_Cons' take_ltake
    split: llist.splits enat.splits if_splits elim: order.strict_trans2[rotated])
  apply (subst (asm) nth_ltake)
   apply (auto elim!: order.strict_trans2[rotated]) []
  apply (subst (asm) s_chop[of j "_ # ltake j _"])
   apply (auto simp: take_Cons' take_ltake split: enat.splits)
  done

lemma snapshot_stable:
  "cotrace init t \<Longrightarrow> i \<le> j \<Longrightarrow> has_snapshotted (coS t i) p \<Longrightarrow> has_snapshotted (coS t j) p"
  apply (drule cotrace_trace_cos[of _ _ j])
  unfolding cos_def
  by (metis exists_trace_for_any_i_j order_refl s_def snapshot_stable take_ltake)

lemma no_markers_if_all_snapshotted:
  "cotrace init t \<Longrightarrow> i \<le> j \<Longrightarrow> \<forall>p. has_snapshotted (coS t i) p \<Longrightarrow>
      Marker \<notin> set (msgs (coS t i) c) \<Longrightarrow> Marker \<notin> set (msgs (coS t j) c)"  
  apply (drule cotrace_trace_cos[of _ _ j])
  unfolding cos_def
  by (metis exists_trace_for_any_i_j no_markers_if_all_snapshotted order_refl s_def take_ltake)

lemma cotrace_all_have_snapshotted:
  assumes "cotrace init t"
  shows "\<exists>i \<le> llength t. \<forall>p. has_snapshotted (coS t i) p"
proof -
  let ?i = "Max (range (some_snapshot t))"
  show ?thesis
    using has_snapshotted[OF assms] snapshot_stable[OF assms, of "some_snapshot t _" ?i _]
    apply (intro exI[of _ ?i])
    apply (auto simp: finite_processes)
     apply (cases "llength t"; auto simp: )
     apply (subst Max_le_iff)
       apply (auto simp: finite_processes)
    apply blast
    done
qed

lemma no_messages_if_no_channel:
  assumes "cotrace init t"
  shows "channel cid = None \<Longrightarrow> msgs (coS t i) cid = []"
  using no_messages_introduced_if_no_channel[OF assms[THEN cotrace_trace_cos, of i] no_msgs_if_no_channel, of cid i]
  by (auto simp: cos_def)

lemma cotrace_all_have_snapshotted_and_no_markers:
  assumes "cotrace init t"
  shows "\<exists>i \<le> llength t. (\<forall>p. has_snapshotted (coS t i) p) \<and> 
                         (\<forall>c. Marker \<notin> set (msgs (coS t i) c))"
proof -
  from cotrace_all_have_snapshotted[OF assms] obtain j :: nat where
    j: "j \<le> llength t" "\<forall>p. has_snapshotted (coS t j) p" by blast
  from j(2) have *: "has_snapshotted (coS t k) p" if "k \<ge> j" for k p
      using snapshot_stable[OF assms, of j k p] that by auto
  define C where "C = {c. Marker \<in> set (msgs (coS t j) c)}"
  have "finite C"
    using no_messages_if_no_channel[OF assms, of _ j] unfolding C_def
    by (intro finite_subset[OF _ finite_channels]) fastforce
  define pick where "pick = (\<lambda>c. SOME k. k \<le> llength t \<and> k \<ge> j \<and> Marker \<notin> set (msgs (coS t k) c))"
  { fix c
    assume "c \<in> C"
    then have "\<exists>k \<le> llength t. k \<ge> j \<and> Marker \<notin> set (msgs (coS t k) c)"
      using l1[rule_format, of t j c] assms unfolding C_def by blast
    then have "pick c \<le> llength t \<and> pick c \<ge> j \<and> Marker \<notin> set (msgs (coS t (pick c)) c)"
      unfolding pick_def
      by (rule someI_ex)
  } note pick = conjunct1[OF this] conjunct1[OF conjunct2[OF this]] conjunct2[OF conjunct2[OF this]]
  show ?thesis
  proof (cases "C = {}")
    case True
    with j show ?thesis
      by (auto intro!: exI[of _ j] simp: C_def)
  next
    define m where "m = Max (pick ` C)"
    case False
    with \<open>finite C\<close> have m: "m \<in> pick ` C" "\<forall>x \<in> pick ` C. m \<ge> x"
      unfolding m_def by auto
    then have "j \<le> m" using pick(2) by auto
    from *[OF \<open>j \<le> m\<close>] have "Marker \<notin> set (msgs (coS t m) c)" for c
    proof (cases "c \<in> C")
      case True
      then show ?thesis
        using no_markers_if_all_snapshotted[OF assms, of "pick c" m c] pick[of c] m *
        by auto
    next
      case False
      then show ?thesis
        using no_markers_if_all_snapshotted[OF assms \<open>j \<le> m\<close> j(2), of c]
        by (auto simp: C_def)
    qed
    with *[OF \<open>j \<le> m\<close>] m pick show ?thesis by auto
  qed
qed

context
  fixes t
  assumes cotrace: "cotrace init t"
begin

definition "final_i \<equiv>
  (SOME i. i \<le> llength t \<and> (\<forall>p. has_snapshotted (coS t i) p) \<and> (\<forall>c. Marker \<notin> set (msgs (coS t i) c)))"

definition final where
  "final = coS t final_i"

lemma final_i: "final_i \<le> llength t" "(\<forall>p. has_snapshotted (coS t final_i) p)" "(\<forall>c. Marker \<notin> set (msgs (coS t final_i) c))"
  unfolding final_i_def
  by (rule someI2_ex[OF cotrace_all_have_snapshotted_and_no_markers[OF cotrace]]; auto intro: cotrace_trace_cos[OF cotrace])+

lemma final: "\<exists>t. trace init t final" "(\<forall>p. has_snapshotted final p)" "(\<forall>c. Marker \<notin> set (msgs final c))"
  unfolding final_def
  by (rule cotrace_trace_cos[OF cotrace] final_i exI)+

interpretation computation channel trans send recv init final
  apply standard
            apply (rule finite_channels)
           apply (rule strongly_connected_raw)
          apply (rule at_least_two_processes)
         apply (rule finite_processes)
        apply (rule no_initial_Marker)
       apply (rule no_msgs_if_no_channel)
      apply (rule no_initial_process_snapshot)
     apply (rule no_initial_channel_snapshot)
    apply (rule final(1))
   apply (intro allI impI)
  subgoal for t i cid
    apply (rule exI[of _ "length t"])
    apply (metis exists_trace_for_any_i final(3) le_cases take_all trace_and_start_determines_end)
    done
  apply (intro allI impI)
  subgoal for t p
    apply (rule exI[of _ "length t"])
    apply (metis exists_trace_for_any_i final(2) order_refl take_all trace_and_start_determines_end)
    done
  done

definition coperm where
  "coperm l r = (\<exists>xs ys z. perm xs ys \<and> l = prepend xs z \<and> r = prepend ys z)"

lemma copermIL: "perm ys xs \<Longrightarrow> t = prepend xs z \<Longrightarrow> coperm (prepend ys z) t"
  unfolding coperm_def by auto

lemma snapshot_algorithm_is_cocorrect:
  "\<exists>t' i. cotrace init t' \<and> coperm t' t \<and> state_equal_to_snapshot (coS t' i) final \<and> i \<le> final_i"
proof -
  define prefix where "prefix = ltake final_i t"
  define suffix where "suffix = ldrop final_i t"
  have [simp]: "prepend prefix suffix = t"
    unfolding prefix_def suffix_def prepend_ltake_ldrop_id ..
  have [simp]: "cotrace final suffix"
    unfolding suffix_def final_def
    by (auto simp: cotrace final_i(1) intro!: cotrace_ldrop)
  from cotrace_trace_cos[OF cotrace] have "trace init prefix final"
    unfolding final_def prefix_def by blast
  with snapshot_algorithm_is_correct obtain prefix' i where
    "trace init prefix' final" "perm prefix' prefix" "state_equal_to_snapshot (S prefix' i) final"
    "i \<le> length prefix'"
    by blast
  moreover from \<open>perm prefix' prefix\<close> \<open>i \<le> length prefix'\<close> have "i \<le> final_i"
    by (auto dest!: perm_length simp: prefix_def split: enat.splits)
  ultimately show ?thesis
    by (intro exI[of _ "prepend prefix' suffix"] exI[of _ i])
      (auto simp: cos_def ltake_prepend s_chop[symmetric] intro!: cotrace_prepend elim!: copermIL)
qed

end

print_statement snapshot_algorithm_is_cocorrect

end

end
