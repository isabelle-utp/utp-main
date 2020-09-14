section \<open> tock-Circus \<close>

theory tockcircus
imports tcircus_calc
begin recall_syntax

subsection \<open> Healthiness Conditions \<close>

text \<open> This is the same as Circus $Skip$, except that it includes an unstable intermediate state. \<close>

definition Skip :: "('s,'e) taction" where
[rdes_def]: "Skip = \<^bold>R(true\<^sub>r \<turnstile> \<U>(true, []) \<diamondop> \<F>(true, [], id\<^sub>s))"

definition TC1 :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" where
[rdes_def]: "TC1(P) = Skip ;; P"

lemma Skip_self_unit: "Skip ;; Skip = Skip"
  by rdes_eq

lemma TC1_idem: "TC1(TC1(P)) = TC1(P)"
  by (simp add: RA1 Skip_self_unit TC1_def)

definition TC2 :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" where
[rdes_def]: "TC2(P) = P ;; Skip"

lemma TC2_idem: "TC2(TC2(P)) = TC2(P)"
  by (simp add: seqr_assoc Skip_self_unit TC2_def)

abbreviation "TC \<equiv> NRD \<circ> TC2 \<circ> TC1"

lemma TC_implies_NRD [closure]: "P is TC \<Longrightarrow> P is NRD"
  by (metis (no_types, hide_lams) Healthy_def NRD_idem comp_apply)

lemma NRD_rdes [rdes_def]:
  assumes "P is RC" "Q is RR" "R is RR"
  shows "NRD(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = (\<^bold>R(P \<turnstile> Q \<diamondop> R))"
  by (simp add: Healthy_if NRD_rdes_intro assms)

lemma TC1_rdes:
  assumes "P is RC" "Q is RR" "R is RR"
  shows "TC1(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = \<^bold>R(II\<^sub>t wp\<^sub>r P \<turnstile> (\<U>(true, []) \<or> TRR(Q)) \<diamondop> TRR(R))"
  using assms
  by (rdes_simp, simp add: TRR_def TRR1_def Healthy_if)

lemma TC1_TRR_rdes [rdes_def]:
  assumes "P is TRC" "Q is TRR" "R is TRR"
  shows "TC1(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = \<^bold>R(P \<turnstile> (\<U>(true, []) \<or> Q) \<diamondop> R)"
  by (subst TC1_rdes, simp_all add: closure assms wp Healthy_if)

lemma TC2_rdes [rdes_def]:
  assumes "P is TRC" "Q is TRR" "R is TRR"
  shows "TC2(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = \<^bold>R(P \<turnstile>(Q \<or> R ;; \<U>(true, [])) \<diamondop> R ;; II\<^sub>t)"
  using assms by (rdes_simp)

lemma TC_implies_TC1 [closure]: 
  assumes "P is TC"
  shows "P is TC1"
proof -
  have a:"P is NRD"
    by (simp add: closure assms)
  have "TC1(TC(P)) = TC(P)"
    by (rdes_eq cls: a)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma TC_implies_TC2 [closure]: 
  assumes "P is TC"
  shows "P is TC2"
proof -
  have a:"P is NRD"
    by (simp add: closure assms)
  have "TC2(TC(P)) = TC(P)"
    by (rdes_eq cls: a)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma TC_closed_seqr [closure]: "\<lbrakk> P is TC; Q is TC \<rbrakk> \<Longrightarrow> P ;; Q is TC"
  apply (auto intro!: Healthy_comp)
  apply (simp add: closure)
  apply (metis (no_types, hide_lams) Healthy_def RA1 TC2_def TC_implies_TC2)
  apply (metis (no_types, hide_lams) Healthy_def RA1 TC1_def TC_implies_TC1)
  done

lemma TC_inner_TRR [closure]:
  assumes "P is TC"
  shows "pre\<^sub>R(P) is TRC" "peri\<^sub>R(P) is TRR" "post\<^sub>R(P) is TRR"
proof -
  have a: "P is NRD"
    using TC_implies_NRD assms by blast
  have 1: "P = \<^bold>R(II\<^sub>t wp\<^sub>r pre\<^sub>R P \<turnstile> (\<U>(true, []) \<or> TRR (peri\<^sub>R P)) \<diamondop> TRR (post\<^sub>R P))"
    by (metis Healthy_if NRD_is_RD NRD_neg_pre_RC RD_healths(2) RD_reactive_tri_design TC1_rdes TC_implies_TC1 a assms periR_RR postR_RR)
  hence 2: "II\<^sub>t wp\<^sub>r pre\<^sub>R P = pre\<^sub>R P"
    by (metis TRR_implies_RR TRR_tc_skip a preR_NRD_RR preR_rdes wp_rea_RR_closed)
  thus [closure]: "pre\<^sub>R(P) is TRC"
    by (simp add: NRD_neg_pre_RC TRC_wp_intro a)
  have "peri\<^sub>R(P) = (pre\<^sub>R(P) \<Rightarrow>\<^sub>r (\<U>(true, []) \<or> TRR (peri\<^sub>R P)))"
    by (subst 1, simp add: rdes closure assms 2)
  also have "... is TRR"
    by (simp add: closure assms)
  finally show "peri\<^sub>R(P) is TRR" .
  have "post\<^sub>R(P) = (pre\<^sub>R(P) \<Rightarrow>\<^sub>r TRR (post\<^sub>R P))"
    by (metis 1 2 Healthy_Idempotent TRR_implies_RR a postR_rdes preR_NRD_RR trel_theory.HCond_Idempotent)
  also have "... is TRR"
    by (simp add: closure assms)
  finally show "post\<^sub>R(P) is TRR" .
qed

subsection \<open> Basic Constructs \<close>

text \<open> The divergent action cannot terminate and exhibits only instability in the pericondition. \<close>

definition Div :: "('s,'e) taction" where
[rdes_def]: "Div = \<^bold>R(true\<^sub>r \<turnstile> \<U>(true, []) \<diamondop> false)"

lemma Div_TC [closure]: "Div is TC"
  by (rule Healthy_intro, rdes_eq)

definition AssignsT :: "'s usubst \<Rightarrow> ('s,'e) taction" ("\<langle>_\<rangle>\<^sub>T") where
[rdes_def]: "AssignsT \<sigma> = \<^bold>R(true\<^sub>r \<turnstile> \<U>(true, []) \<diamondop> \<F>(true, [], \<sigma>))" 

lemma AssignsT_TC [closure]: "\<langle>\<sigma>\<rangle>\<^sub>T is TC"
  by (rule Healthy_intro, rdes_eq)

text \<open> A timed deadlock does not terminate, but permits any period of time to pass, always remaining
  in a quiescent state where another $tock$ can occur. \<close>

definition Stop :: "('s,'e) taction" where
[rdes_def]: "Stop = \<^bold>R(true\<^sub>r \<turnstile> \<T>({}, {0..}) ;; \<E>(true, [], {}, true) \<diamondop> false)"

lemma Stop_TC [closure]: "Stop is TC"
  by (rule Healthy_intro, rdes_eq)

text \<open> An untimed deadlock is stable, but does not accept any events. \<close>

definition Stop\<^sub>U :: "('s,'e) taction" where
[rdes_def]: "Stop\<^sub>U = \<^bold>R(true\<^sub>r \<turnstile> \<E>(true, [], {}, false) \<diamondop> false)"

lemma Stop\<^sub>U_TC [closure]: "Stop\<^sub>U is TC"
  by (rule Healthy_intro, rdes_eq)

text \<open> SDF: Check the following definition against the tick-tock paper. It only allows prefixing
  of non-tock events for now. \<close>

definition DoT :: "('e, 's) uexpr \<Rightarrow> ('s, 'e) taction" ("do\<^sub>T'(_')") where
[rdes_def]: "DoT a =
  \<^bold>R(true\<^sub>r 
  \<turnstile> \<T>({a}, {0..}) ;; (\<E>(true, [], {a}, true) \<or> \<U>(true, [Evt a]))
  \<diamondop> \<T>({a}, {0..}) ;; \<F>(true, [Evt a], id\<^sub>s))"

lemma DoT_TC: "do\<^sub>T(e) is TC"
  by (rule Healthy_intro, rdes_eq)

definition Wait :: "(nat, 's) uexpr \<Rightarrow> ('s,'e) taction" where
[rdes_def]: "Wait n = 
  \<^bold>R(true\<^sub>r 
    \<turnstile> ((\<T>({}, {0..<n}) ;; \<E>(true, [], {}, true)) 
       \<or> (\<T>({}, {n}) ;; \<U>(true, [])))
    \<diamondop> \<T>({}, {n}))"

utp_lift_notation Wait

lemma Wait_TC: "Wait n is TC"
  by (rule Healthy_intro, rdes_eq)

subsection \<open> Algebraic Laws \<close>

lemma "Skip ;; Stop = Stop"
  by (rdes_eq)

lemma "Stop \<sqsubseteq> Div"
  by (rdes_refine)

utp_const lift_state_pre

lemma Wait_0: "Wait 0 = Skip"
  by (rdes_eq)

lemma Wait_Wait: "Wait m ;; Wait n = Wait(m + n)"
  apply (rdes_eq_split)
    apply (rel_auto)
   apply (simp_all add: rpred closure seqr_assoc[THEN sym])
  apply (rel_auto)
  done

text \<open> This is a pleasing result although @{const Wait} raises instability, this is swallowed up 
  by the sequential composition. \<close>

lemma Wait_Stop: "Wait m ;; Stop = Stop"
  by (rdes_eq_split, simp_all add: rpred closure seqr_assoc[THEN sym], rel_auto)

lemma "\<langle>[x \<mapsto>\<^sub>s &x + 1]\<rangle>\<^sub>T ;; do\<^sub>T(a) ;; \<langle>[x \<mapsto>\<^sub>s &x + 1]\<rangle>\<^sub>T = 
        \<^bold>R (\<^U>(R1 true) \<turnstile>
         (\<U>(true, []) \<or>
          \<F>(true, [], \<^U>([x \<mapsto>\<^sub>s &x + 1])) ;; \<T>({a}, {0..}) ;; \<E>(true, [], {a}, true) \<or>
          \<F>(true, [], \<^U>([x \<mapsto>\<^sub>s &x + 1])) ;; \<T>({a}, {0..}) ;; \<U>(true, [Evt a])) \<diamondop>
         \<F>(true, [], \<^U>([x \<mapsto>\<^sub>s &x + 1])) ;; \<T>({a}, {0..}) ;; \<F>(true, [Evt a], \<^U>([x \<mapsto>\<^sub>s &x + 1])))"
  by (rdes_simp, simp add: rpred seqr_assoc usubst)

lemma "Wait(m) ;; do\<^sub>T(a) ;; \<langle>[x \<mapsto>\<^sub>s &x + 1]\<rangle>\<^sub>T = 
      \<^bold>R (true\<^sub>r \<turnstile>
        (\<T>({}, {0..<m}) ;; \<E>(true, [], {}, true) \<or>
         \<T>({}, {m}) ;; \<U>(true, []) \<or> 
         \<T>({}, {m}) ;; \<T>({a}, {0..}) ;; \<E>(true, [], {a}, true) \<or> 
         \<T>({}, {m}) ;; \<T>({a}, {0..}) ;; \<U>(true, [Evt a])) \<diamondop>
         \<T>({}, {m}) ;; \<T>({a}, {0..}) ;; \<F>(true, [Evt a], [x \<mapsto>\<^sub>s &x + 1]))"
  apply (rdes_simp)
  apply (simp add: rpred seqr_assoc usubst)
  oops

definition ExtChoice :: "'i set \<Rightarrow> ('i \<Rightarrow> ('s, 'e) taction) \<Rightarrow> ('s, 'e) taction" where
[upred_defs]:
"ExtChoice I P =
  \<^bold>R(R1(\<And> i\<in>I \<bullet> pre\<^sub>R(P i)) \<comment> \<open> Require all preconditions \<close>

   \<turnstile> (idle(\<And> i\<in>I \<bullet> idle(peri\<^sub>R(P i))) \<comment> \<open> Allow all idle behaviours \<close>
      \<or> (\<Or> i\<in>I \<bullet> active(peri\<^sub>R(P i)) \<comment> \<open> Allow one active action to resolve the choice ...\<close>
         \<and> (\<And> j\<in>I-{i} \<bullet> time(peri\<^sub>R(P j))))) \<comment> \<open> ... whilst the others remain idle \<close>

   \<diamondop> ((\<Or> i\<in>I \<bullet> post\<^sub>R(P i) \<comment> \<open> The postcondition can terminate the external choice without an event ... \<close>
      \<and> (\<And> j\<in>I-{i} \<bullet> time(peri\<^sub>R(P j))))))" \<comment> \<open> ... whilst the others remain quiescent and idle \<close>

(*
definition extChoice :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction \<Rightarrow> ('s, 'e) taction" (infixl "\<box>" 69) where
[upred_defs]: "P \<box> Q = ExtChoice {P, Q} id"
*)

definition extChoice :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction \<Rightarrow> ('s, 'e) taction" (infixl "\<box>" 69) where
[upred_defs]:
"P \<box> Q =
  \<^bold>R((pre\<^sub>R(P) \<and> pre\<^sub>R(Q))
  \<turnstile> (idle(peri\<^sub>R(P)) \<and> idle(peri\<^sub>R(Q)) 
    \<or> time(peri\<^sub>R(P)) \<and> active(peri\<^sub>R(Q))
    \<or> time(peri\<^sub>R(Q)) \<and> active(peri\<^sub>R(P)))
  \<diamondop> (time(peri\<^sub>R(P)) \<and> post\<^sub>R(Q) \<or> time(peri\<^sub>R(Q)) \<and> post\<^sub>R(P)))"

lemma ExtChoice_empty:
  "ExtChoice {} P = Stop"
  by (simp add: ExtChoice_def Stop_def rpred)

lemma ExtChoice_single: 
  assumes "P i is NRD" "peri\<^sub>R(P i) is TRR"
  shows "ExtChoice {i} P = P i"
  by (simp add: ExtChoice_def Healthy_if rpred closure assms RD_reactive_tri_design)

lemma ExtChoice_rdes_def [rdes_def]:
  assumes "\<And> i. P\<^sub>1(i) is TRC" "\<And> i. P\<^sub>2(i) is TRR" "\<And> i. P\<^sub>3(i) is TRR"
  shows "ExtChoice I (\<lambda> i. \<^bold>R(P\<^sub>1(i) \<turnstile> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))) = 
 \<^bold>R ((\<And> i\<in>I \<bullet> P\<^sub>1(i)) 
    \<turnstile> (idle(\<And> i\<in>I \<bullet> idle(P\<^sub>2 i)) \<or> (\<Or> i\<in>I \<bullet> active(P\<^sub>2 i) \<and> (\<And> j\<in>I - {i} \<bullet> time(P\<^sub>2 j)))) \<diamondop>
        (\<Or> i\<in>I \<bullet> (P\<^sub>3 i) \<and> (\<And> j\<in>I - {i} \<bullet> time(P\<^sub>2 j))))"
proof (cases "I = {}")
  case True
  then show ?thesis by (simp add: ExtChoice_empty rpred Stop_def, rel_auto)
next
  case False
  note ne [closure] = this
  then show ?thesis
  proof (cases "\<exists> i. I = {i}")
    case True
    then show ?thesis 
      by (clarsimp simp add: ExtChoice_single rdes closure assms rpred)
  next
    case False
    have [closure]:"\<And>i. i \<in> I \<Longrightarrow> \<not> I \<subseteq> {i}"
      using False by blast
    have "((\<And> i\<in>I \<bullet> RC2(P\<^sub>1(i))) \<Rightarrow>\<^sub>r (idle(\<And> i\<in>I \<bullet> idle(RC2(P\<^sub>1 i) \<Rightarrow>\<^sub>r P\<^sub>2 i)) \<or> (\<Or> i\<in>I \<bullet> active(RC2(P\<^sub>1 i) \<Rightarrow>\<^sub>r P\<^sub>2 i) \<and> (\<And> j\<in>I - {i} \<bullet> time(RC2(P\<^sub>1 j) \<Rightarrow>\<^sub>r P\<^sub>2 j)))))
        = ((\<And> i\<in>I \<bullet> RC2(P\<^sub>1(i))) \<Rightarrow>\<^sub>r (idle(\<And> i\<in>I \<bullet> idle(P\<^sub>2 i)) \<or> (\<Or> i\<in>I \<bullet> active(P\<^sub>2 i) \<and> (\<And> j\<in>I - {i} \<bullet> time(P\<^sub>2 j)))))"
      apply (trr_simp cls: assms, safe)
      apply meson
      apply meson
      apply blast
      apply blast
      apply (metis idleprefix_concat_Evt list_append_prefixD tocks_idleprefix_fp)
      apply (metis idleprefix_concat_Evt list_append_prefixD tocks_idleprefix_fp)
      apply (metis idleprefix_concat_Evt list_append_prefixD tocks_idleprefix_fp)
      apply blast+
      done
    hence 1: "((\<And> i\<in>I \<bullet> P\<^sub>1(i)) \<Rightarrow>\<^sub>r (idle(\<And> i\<in>I \<bullet> idle(P\<^sub>1 i \<Rightarrow>\<^sub>r P\<^sub>2 i)) \<or> (\<Or> i\<in>I \<bullet> active(P\<^sub>1 i \<Rightarrow>\<^sub>r P\<^sub>2 i) \<and> (\<And> j\<in>I - {i} \<bullet> time(P\<^sub>1 j \<Rightarrow>\<^sub>r P\<^sub>2 j)))))
            = ((\<And> i\<in>I \<bullet> P\<^sub>1(i)) \<Rightarrow>\<^sub>r (idle(\<And> i\<in>I \<bullet> idle(P\<^sub>2 i)) \<or> (\<Or> i\<in>I \<bullet> active(P\<^sub>2 i) \<and> (\<And> j\<in>I - {i} \<bullet> time(P\<^sub>2 j)))))"
      by (simp add: Healthy_if assms closure)
    have "((\<And> i\<in>I \<bullet> RC2(P\<^sub>1(i))) \<Rightarrow>\<^sub>r (\<Or> i\<in>I \<bullet> (RC2(P\<^sub>1 i) \<Rightarrow>\<^sub>r P\<^sub>3 i) \<and> (\<And> j\<in>I - {i} \<bullet> time(RC2(P\<^sub>1 j) \<Rightarrow>\<^sub>r P\<^sub>2 j))))
          = ((\<And> i\<in>I \<bullet> RC2(P\<^sub>1(i))) \<Rightarrow>\<^sub>r (\<Or> i\<in>I \<bullet> (P\<^sub>3 i) \<and> (\<And> j\<in>I - {i} \<bullet> time(P\<^sub>2 j))))"
      apply (trr_simp cls: assms, safe)
      apply auto[1]
      apply (meson idleprefix_prefix order.trans)
      apply blast
      done
    hence 2: "((\<And> i\<in>I \<bullet> P\<^sub>1(i)) \<Rightarrow>\<^sub>r (\<Or> i\<in>I \<bullet> (P\<^sub>1 i \<Rightarrow>\<^sub>r P\<^sub>3 i) \<and> (\<And> j\<in>I - {i} \<bullet> time(P\<^sub>1 j \<Rightarrow>\<^sub>r P\<^sub>2 j))))
          =  ((\<And> i\<in>I \<bullet> P\<^sub>1(i)) \<Rightarrow>\<^sub>r (\<Or> i\<in>I \<bullet> (P\<^sub>3 i) \<and> (\<And> j\<in>I - {i} \<bullet> time(P\<^sub>2 j))))"
      by (simp add: Healthy_if assms closure)
    show ?thesis
      by (simp add: ExtChoice_def rdes assms closure Healthy_if)
         (metis (no_types, lifting) "1" "2" rdes_tri_eq_intro rea_impl_mp)
  qed
qed

lemma ExtChoice_dual:
  assumes "P is TC" "Q is TC" "P \<noteq> Q"
  shows
    "ExtChoice {P, Q} id = P \<box> Q"
  apply (subgoal_tac "{P, Q} - {Q} = {P}")
  apply (simp add: ExtChoice_def closure assms extChoice_def rpred usup_and uinf_or conj_disj_distr)
  apply (rule rdes_tri_eq_intro)
    apply (simp_all add: assms Healthy_if closure)
  apply (simp add: disj_comm utp_pred_laws.inf.commute utp_pred_laws.sup.left_commute rpred closure assms)
  apply (simp add: utp_pred_laws.inf_commute utp_pred_laws.sup_commute)
  apply (simp add: assms insert_Diff_if)
  done

text \<open> Proving idempotence of binary external choice is complicated by the need to show that
  @{term "(time(peri\<^sub>R(P)) \<and> post\<^sub>R(P)) = post\<^sub>R(P)"} \<close>

lemma extChoice_rdes_def [rdes_def]:
  assumes "P\<^sub>2 is TRR" "P\<^sub>3 is TRR" "Q\<^sub>2 is TRR" "Q\<^sub>3 is TRR"
  shows
  "\<^bold>R(true\<^sub>r \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<box> \<^bold>R(true\<^sub>r \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) =
       \<^bold>R(true\<^sub>r 
        \<turnstile> (idle(P\<^sub>2) \<and> idle(Q\<^sub>2) \<or> time(P\<^sub>2) \<and> active(Q\<^sub>2) \<or> time(Q\<^sub>2) \<and> active(P\<^sub>2))
        \<diamondop> (time(P\<^sub>2) \<and> Q\<^sub>3 \<or> time(Q\<^sub>2) \<and> P\<^sub>3))"
  by (simp add: extChoice_def ExtChoice_def rdes closure assms rpred)

lemma ExtChoice_unary:
  assumes "P i is TC"
  shows "ExtChoice {i} P = P i"
  by (simp add: ExtChoice_single TC_implies_NRD TC_inner_TRR(2) assms)

lemma [rpred]: "active(\<T>(X, A) ;; \<E>(s, [], E, p)) = false"
  by (rel_auto)

lemma "Skip \<box> Stop = Skip"
  by (rdes_eq)
  
lemma "Wait m \<box> Wait m = Wait m"
  by (rdes_eq)

lemma "Wait m \<box> Wait n = Wait U(min m n)"
  apply (rdes_eq_split, simp_all add: rpred closure)
  oops

lemma "Skip \<box> Stop\<^sub>U = Skip"
  by (rdes_eq)

lemma "Skip \<box> Div = Skip"
  by (rdes_eq)

lemma "Wait(n + 1) \<box> Div = Div"
  by (rdes_eq)

lemma "Wait(n + 1) \<box> Stop\<^sub>U = Stop\<^sub>U"
  by (rdes_eq)

lemma "Stop \<box> do\<^sub>T(a) = do\<^sub>T(a)"
  apply (rdes_eq_split)
    apply (simp_all add: rpred closure)
  apply (trr_auto)
  using tocks_idleprefix_fp tocks_iff_idleprefix_fp apply blast
  done

lemma "Wait m \<box> Skip = Skip"
  by (rdes_eq)

lemma "Stop \<box> \<langle>\<sigma>\<rangle>\<^sub>T = \<langle>\<sigma>\<rangle>\<^sub>T"
  by (rdes_eq)

lemma extChoice_idem:
  assumes "P is NRD" "pre\<^sub>R(P) = true\<^sub>r" "peri\<^sub>R(P) is TRR" "peri\<^sub>R(P) is TIP" "post\<^sub>R(P) is TRF"
    "peri\<^sub>R P \<sqsubseteq> post\<^sub>R P ;; \<U>(true, [])"
  shows "P \<box> P = P"
  apply (rdes_eq_split cls: assms)  
  apply (simp add: assms rpred closure)
   apply (simp add: TIP_time_active TRR_idle_or_active assms(3) assms(4) utp_pred_laws.inf_commute)
  using time_peri_in_post[OF assms(3) assms(4) assms(5) assms(6)]
  apply (simp add: utp_pred_laws.inf.absorb2)
  done

text \<open> Need some additional assumptions \<close>

lemma
  assumes "P is NRD" "pre\<^sub>R(P) = true\<^sub>r" "peri\<^sub>R(P) is TRR" "post\<^sub>R(P) is TRR"
  shows "Stop \<box> P = P"
  by (rdes_eq_split cls: assms)

text \<open> Pedro Comment: Renaming should be a relation rather than a function. \<close>

end