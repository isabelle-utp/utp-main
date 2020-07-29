section \<open> tock-Circus \<close>

theory utp_tockcircus
imports "UTP-Reactive-Designs.utp_rea_designs" "rcircus/Refusal_Tests"
begin recall_syntax

subsection \<open> Foundations \<close>

text \<open> We try and characterise a tock-CSP like model using the standard Circus pattern and adapting
  the CML model and bits of the refusal testing model. First we represent traces. \<close>

datatype ('t, 'e) teva = Tock "'t" | Evt 'e

type_synonym 'e tev = "('e set, 'e) teva"

text \<open> We don't need a tick event, because this is handled by the $wait$ flag. Nor do we need to
  separate refusals and tocks. A refusal in tock-CSP (as I understand) can occur either (1) just
  before a tock occurs, or (2) at the end of a trace. We gain the former by embedding refusals
  in a tock (as in CML). We gain the latter by including the $ref'$ variable as in Circus. We encode
  the healthiness condition that a tock can't occur in a refusal before a tock event using
  the type system. \<close>

alphabet ('s, 'e) tc_vars = "('e tev list, 's) rsp_vars" +
  ref :: "(unit, 'e) teva refusal"

text \<open> The $ref$ variable is not simply a set, but a set augmented with the @{term "\<^bold>\<bullet>"} that denotes
  stability. We need this because tick-tock traces can end without a refusal. Note that unlike
  in the trace this is a refusal over @{typ "'e tev"} so that we can refuse tocks at the end. \<close>

text \<open> The interpretation of $wait$ changes to there being both stable (quiescent) and unstable.
  Extra information is needed for refusals. What is the meaning pericondition? \<close>

(* FIXME: Nasty hack below *)

declare des_vars.splits [alpha_splits del]
declare rp_vars.splits [alpha_splits del]
declare des_vars.splits [alpha_splits del]
declare rsp_vars.splits [alpha_splits del]
declare rsp_vars.splits [alpha_splits]
declare rp_vars.splits [alpha_splits]
declare des_vars.splits [alpha_splits]

type_synonym ('s,'e) taction  = "('s, 'e) tc_vars hrel"

definition tocks :: "'e set \<Rightarrow> 'e tev list set" where
"tocks X = {t. \<forall> e \<in> set(t). \<exists> Y. e = Tock Y \<and> Y \<subseteq> X}"

lemma tocks_Nil [simp]: "[] \<in> tocks X"
  by (simp add: tocks_def)

lemma tocks_Cons: "\<lbrakk> Y \<subseteq> X; t \<in> tocks X \<rbrakk> \<Longrightarrow> Tock Y # t \<in> tocks X"
  by (simp add: tocks_def)

lemma tocks_append [simp]: "\<lbrakk> s \<in> tocks X; t \<in> tocks X \<rbrakk> \<Longrightarrow> s @ t \<in> tocks X"
  by (auto simp add: tocks_def)

lemma tocks_take [simp]: "s \<in> tocks X \<Longrightarrow> take n s \<in> tocks X"
  by (auto simp add: tocks_def, meson in_set_takeD)

lemma tocks_drop [simp]: "s \<in> tocks X \<Longrightarrow> drop n s \<in> tocks X"
  by (auto simp add: tocks_def, meson in_set_dropD)

definition "mk_tocks n = replicate n (Tock {})"

lemma mk_tocks: "mk_tocks n \<in> tocks X"
  by (simp add: mk_tocks_def tocks_def)

lemma length_mk_tocks [simp]: "length (mk_tocks n) = n"
  by (simp add: mk_tocks_def)

fun events :: "'e tev list \<Rightarrow> 'e tev list" where
"events [] = []" |
"events (Tock A # t) = events t" |
"events (Evt x # t) = (Evt x # events t)"

lemma events_append [simp]: "events (xs @ ys) = events(xs) @ events(ys)"
  apply (induct xs, simp_all)
  apply (rename_tac x xs)
  apply (case_tac x)
  apply (simp_all)
done

text \<open> This function is taken from CML and I think might be useful here too. \<close>

fun idleprefix :: "'e tev list \<Rightarrow> 'e tev list" where
"idleprefix [] = []" |
"idleprefix (Tock A # t) = (Tock A # idleprefix t)" |
"idleprefix (Evt x # t) = []"

subsection \<open> Reactive Relation Constructs \<close>

definition TRR :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRR(P) = (\<exists> $ref \<bullet> RR(P))"

lemma TRR_idem: "TRR(TRR(P)) = TRR(P)"
  by (rel_auto)

lemma Idempotent_TRR [closure]: "Idempotent TRR"
  by (simp add: TRR_idem Idempotent_def)

lemma Continuous_CRR [closure]: "Continuous TRR"
  by (rel_blast)

lemma TRR_intro:
  assumes "$ref \<sharp> P" "P is RR"
  shows "P is TRR"
  by (simp add: TRR_def Healthy_def, simp add: Healthy_if assms ex_unrest)

lemma TRR_unrest_ref [unrest]: "P is TRR \<Longrightarrow> $ref \<sharp> P"
  by (metis (no_types, hide_lams) Healthy_def' TRR_def exists_twice in_var_uvar ref_vwb_lens unrest_as_exists vwb_lens_mwb)

lemma TRR_implies_RR [closure]: 
  assumes "P is TRR"
  shows "P is RR"
proof -
  have "RR(TRR(P)) = TRR(P)"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def assms)
qed

no_utp_lift lift_state_rel

definition tc_skip :: "('s, 'e) taction" ("II\<^sub>t") where
[upred_defs]: "tc_skip = ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st)"

text \<open> We introduce a small algebra for peri- and postconditions to capture timed behaviours. The
  first operator captures stable intermediate (i.e. quiescent) behaviours. Here, @{term s} is a 
  predicate on the state (a condition), @{term t} is a trace over non-tock events, and @{term E} 
  is the set of events being accepted at this point. FIXME: Should stable observations
  also update the state? \<close>

definition tc_stable :: "'s upred \<Rightarrow> ('e list, 's) uexpr \<Rightarrow> ((unit, 'e) teva set, 's) uexpr \<Rightarrow> ('s, 'e) taction" ("\<E>'(_, _, _')") where
[upred_defs]: "\<E>(s,t,E) = U(\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> = $tr @ \<lceil>map Evt t\<rceil>\<^sub>S\<^sub>< \<and> (\<forall> e\<in>\<lceil>E\<rceil>\<^sub>S\<^sub><. \<guillemotleft>e\<guillemotright> \<notin>\<^sub>\<R> $ref\<acute>))"

text \<open> We also need unstable intermediate observations, which the following relation provides. It
  has no set associated, since no refusal set is observed. \<close>

definition tc_unstable :: "'s upred \<Rightarrow> ('e list, 's) uexpr \<Rightarrow> ('s, 'e) taction" ("\<U>'(_, _')") where
[upred_defs]: "\<U>(s,t) = U(\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> = $tr @ \<lceil>map Evt t\<rceil>\<^sub>S\<^sub>< \<and> $ref\<acute> = \<^bold>\<bullet>)"

text \<open> A final observation is similar to a stable observation, except it can update the state 
  variables and does not characterise a refusal set. \<close>

definition tc_final :: "'s upred \<Rightarrow> ('e list, 's) uexpr \<Rightarrow> 's usubst \<Rightarrow> ('s, 'e) taction" ("\<F>'(_, _, _')") where
[upred_defs]: "\<F>(s,t,\<sigma>) = U(\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> = $tr @ \<lceil>map Evt t\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S)" 

text \<open> A timed observation represents a period of delay. The set @{term X} characterises the set of
  events that are accepted during this period. The set @{term A} characterises the possible delay
  periods, for example @{term "{0..n}"} means a delay of between $0$ and $n$ units. \<close>

definition tc_time :: "('e set, 's) uexpr \<Rightarrow> (nat set, 's) uexpr \<Rightarrow> ('s, 'e) taction" ("\<T>'(_, _')") where 
[upred_defs]: "\<T>(X, A) = U(\<exists> t \<in> tocks \<lceil>UNIV - X\<rceil>\<^sub>S\<^sub><. $tr\<acute> = $tr @ \<guillemotleft>t\<guillemotright> \<and> length(\<guillemotleft>t\<guillemotright>) \<in> \<lceil>A\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> = $st)"

utp_lift_notation tc_stable
utp_lift_notation tc_unstable
utp_lift_notation tc_final (2)
utp_lift_notation tc_time

lemma [closure]: "II\<^sub>t is TRR"
  by (rel_auto)

lemma [closure]: "\<E>(s, t, E) is TRR"
  by (rel_auto)

lemma [closure]: "\<U>(s, t) is TRR"
  by (rel_auto)

lemma [closure]: "\<F>(s, t, \<sigma>) is TRR"
  by (rel_auto)

lemma [closure]: "\<T>(X, A) is TRR"
  by (rel_auto)

lemma [unrest]: "$st\<acute> \<sharp> \<E>(s, t, E)"
  by (rel_auto)

lemma [unrest]: "$st\<acute> \<sharp> \<U>(s, t)"
  by (rel_auto)

text \<open> Unstable observations are subsumed by stable ones \<close>

lemma instability_subsumed: "\<E>(s, t, E) \<sqsubseteq> \<U>(s, t)"
  by (rel_auto)

lemma [rpred]: "\<F>(s\<^sub>1, t\<^sub>1, \<sigma>\<^sub>1) ;; \<F>(s\<^sub>2, t\<^sub>2, \<sigma>\<^sub>2) = \<F>(s\<^sub>1 \<and> \<sigma>\<^sub>1 \<dagger> s\<^sub>2, t\<^sub>1 @ \<sigma>\<^sub>1 \<dagger> t\<^sub>2, \<sigma>\<^sub>2 \<circ>\<^sub>s \<sigma>\<^sub>1)"
  by (rel_auto)

lemma [rpred]: "\<F>(s\<^sub>1, t\<^sub>1, \<sigma>) ;; \<E>(s\<^sub>2, t\<^sub>2, E) = \<E>(s\<^sub>1 \<and> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1 @ \<sigma> \<dagger> t\<^sub>2, \<sigma> \<dagger> E)"
  by (rel_auto)

lemma [rpred]: "\<F>(s\<^sub>1, t\<^sub>1, \<sigma>) ;; \<U>(s\<^sub>2, t\<^sub>2) = \<U>(s\<^sub>1 \<and> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1 @ \<sigma> \<dagger> t\<^sub>2)"
  by (rel_auto)

lemma TRR_closed_seq [closure]: "\<lbrakk> P is TRR; Q is TRR \<rbrakk> \<Longrightarrow> P ;; Q is TRR"
  by (rule TRR_intro, simp_all add: closure unrest)

lemma trr_left_unit: 
  assumes "P is TRR"
  shows "II\<^sub>t ;; P = P"
proof -
  have "II\<^sub>t ;; TRR(P) = TRR(P)"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed 

lemma [rpred]: "\<T>(X, {0}) = II\<^sub>t"
  by (rel_auto)

lemma [rpred]: "\<F>(true, [], id\<^sub>s) = II\<^sub>t"
  by (rel_auto)

lemma time_single_single [rpred]: "\<T>(X, {m}) ;; \<T>(X, {n}) = \<T>(X, {m+n})"
  apply rel_auto
  apply (rename_tac tr st x)
  apply (rule_tac x="tr @ take (\<lbrakk>m\<rbrakk>\<^sub>e st) x" in exI)
  apply (auto)
  apply (rule_tac x="drop (\<lbrakk>m\<rbrakk>\<^sub>e st) x" in bexI)
   apply (auto)
  done

lemma time_single_lessthan [rpred]: "\<T>(X, {m}) ;; \<T>(X, {0..<n}) = \<T>(X, {m..<m+n})"
  apply rel_auto
  apply (rename_tac tr st x)
  apply (rule_tac x="tr @ take (\<lbrakk>m\<rbrakk>\<^sub>e st) x" in exI)
  apply (auto)
  apply (rule_tac x="drop (\<lbrakk>m\<rbrakk>\<^sub>e st) x" in bexI)
   apply (auto)
  done

lemma time_single_atMost [rpred]: "\<T>(X, {m}) ;; \<T>(X, {0..n}) = \<T>(X, {m..m+n})"
  apply rel_auto
  apply (rename_tac tr st x)
  apply (rule_tac x="tr @ take (\<lbrakk>m\<rbrakk>\<^sub>e st) x" in exI)
  apply (auto)
  apply (rule_tac x="drop (\<lbrakk>m\<rbrakk>\<^sub>e st) x" in bexI)
   apply (auto)
  done

lemma time_single_atLeast [rpred]: "\<T>(X, {m}) ;; \<T>(X, {n..}) = \<T>(X, {m+n..})"
  apply rel_auto
  apply (rename_tac tr st x)
  apply (rule_tac x="tr @ take (\<lbrakk>m\<rbrakk>\<^sub>e st) x" in exI)
  apply (auto)
  apply (rule_tac x="drop (\<lbrakk>m\<rbrakk>\<^sub>e st) x" in bexI)
   apply (auto)
  done

lemma split_time_dom:
  fixes l :: nat
  assumes "m\<^sub>1 + m\<^sub>2 \<le> l" "l \<le> m\<^sub>1 + m\<^sub>2 + (n\<^sub>1 + n\<^sub>2)"
  shows "(\<exists> n. n \<le> l \<and> m\<^sub>1 \<le> n \<and> m\<^sub>2 + n \<le> l \<and> n \<le> m\<^sub>1+n\<^sub>1 \<and> l \<le> m\<^sub>2+n\<^sub>2+n)"
  using assms
  by presburger

lemma [rpred]: "\<T>(X, {m\<^sub>1..m\<^sub>1+n\<^sub>1}) ;; \<T>(X, {m\<^sub>2..m\<^sub>2+n\<^sub>2}) = \<T>(X, {m\<^sub>1 + m\<^sub>2..m\<^sub>1 + m\<^sub>2+(n\<^sub>1 + n\<^sub>2)})"
proof (rel_auto)
  fix tr st t

  assume a: "t \<in> tocks (UNIV - \<lbrakk>X\<rbrakk>\<^sub>e st)" "\<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e st + \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e st \<le> length t" "length t \<le> \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e st + \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e st + (\<lbrakk>n\<^sub>1\<rbrakk>\<^sub>e st + \<lbrakk>n\<^sub>2\<rbrakk>\<^sub>e st)"
  then obtain n where n: "n \<le> length t" "\<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e st \<le> n" "\<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e st + n \<le> length t" "n \<le> \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e st+\<lbrakk>n\<^sub>1\<rbrakk>\<^sub>e st" "length t \<le> \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e st+\<lbrakk>n\<^sub>2\<rbrakk>\<^sub>e st+n"
    using split_time_dom by blast

  with a show "\<exists>tr' st'.
          (\<exists>x\<in>tocks (UNIV - \<lbrakk>X\<rbrakk>\<^sub>e st). tr' = tr @ x \<and> \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e st \<le> length x \<and> length x \<le> \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e st + \<lbrakk>n\<^sub>1\<rbrakk>\<^sub>e st \<and> st' = st) \<and>
          (\<exists>xa\<in>tocks (UNIV - \<lbrakk>X\<rbrakk>\<^sub>e st'). tr @ t = tr' @ xa \<and> \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e st' \<le> length xa \<and> length xa \<le> \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e st' + \<lbrakk>n\<^sub>2\<rbrakk>\<^sub>e st' \<and> st = st')"
    apply (rule_tac x="tr @ take n t" in exI)
    apply (rule_tac x="st" in exI)
    apply (auto)
    apply (rule_tac x="drop n t" in bexI)
     apply (auto)
    done
qed

subsection \<open> Healthiness Conditions \<close>

text \<open> This is the same as Circus $Skip$, except that it includes an unstable intermediate state. \<close>

definition Skip :: "('s,'e) taction" where
[rdes_def]: "Skip = \<^bold>R(true\<^sub>r \<turnstile> \<U>(true, []) \<diamondop> \<F>(true, [], id\<^sub>s))"

definition TC1 :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" where
[rdes_def]: "TC1(P) = Skip ;; P"

definition TC2 :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" where
[rdes_def]: "TC2(P) = P ;; Skip"

lemma TC1_rdes:
  assumes "Q is TRR" "R is TRR"
  shows "TC1(\<^bold>R(true\<^sub>r \<turnstile> Q \<diamondop> R)) = \<^bold>R(true\<^sub>r \<turnstile> (\<U>(true, []) \<or> Q) \<diamondop> R)"
  using assms
  by (rdes_simp simps: trr_left_unit)

subsection \<open> Basic Constructs \<close>

text \<open> The divergent action cannot terminate and exhibits only instability in the pericondition. \<close>

definition Div :: "('s,'e) taction" where
[rdes_def]: "Div = \<^bold>R(true\<^sub>r \<turnstile> \<U>(true, []) \<diamondop> false)"

definition AssignsT :: "'s usubst \<Rightarrow> ('s,'e) taction" ("\<langle>_\<rangle>\<^sub>T") where
[upred_defs]: "AssignsT \<sigma> = \<^bold>R(true \<turnstile> \<U>(true, []) \<diamondop> \<F>(true, [], \<sigma>))" 

text \<open> A timed deadlock does not terminate, but permits any period of time to pass, always remaining
  in a quiescent state where another $tock$ can occur. \<close>

definition Stop :: "('s,'e) taction" where
[rdes_def]: "Stop = \<^bold>R(true\<^sub>r \<turnstile> \<T>({}, {0..}) ;; \<E>(true, [], {Tock ()}) \<diamondop> false)"

text \<open> An untimed deadlock is stable, but does not accept any events. \<close>

definition Stop\<^sub>U :: "('s,'e) taction" where
[rdes_def]: "Stop\<^sub>U = \<^bold>R(true\<^sub>r \<turnstile> \<E>(true, [], {}) \<diamondop> false)"

text \<open> SDF: Check the following definition against the tick-tock paper. It only allows prefixing
  of non-tock events for now. \<close>

definition DoT :: "'e \<Rightarrow> ('s, 'e) taction" ("do\<^sub>T'(_')") where
[rdes_def]: "DoT a =
  \<^bold>R(true\<^sub>r 
  \<turnstile> \<T>({\<guillemotleft>a\<guillemotright>}, {0..}) ;; \<E>(true, [], {Tock (), Evt \<guillemotleft>a\<guillemotright>})
  \<diamondop> \<T>({\<guillemotleft>a\<guillemotright>}, {0..}) ;; \<F>(true, [\<guillemotleft>a\<guillemotright>], id\<^sub>s))"

definition Wait :: "(nat, 's) uexpr \<Rightarrow> ('s,'e) taction" where
[rdes_def]: "Wait n = 
  \<^bold>R(true\<^sub>r 
    \<turnstile> ((\<T>({}, {0..<n}) ;; \<E>(true, [], {Tock ()})) 
       \<or> (\<T>({}, {n}) ;; \<U>(true, [])))
    \<diamondop> \<T>({}, {n}))"

subsection \<open> Algebraic Laws \<close>

lemma "Skip ;; Skip = Skip"
  by (rdes_eq)

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

definition extChoice :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction \<Rightarrow> ('s, 'e) taction" where
"extChoice P Q =
  \<^bold>R(true\<^sub>r 
  \<turnstile> [$tr \<mapsto>\<^sub>s [], $tr\<acute> \<mapsto>\<^sub>s idleprefix(&tt)] \<dagger> (peri\<^sub>R(P) \<and> peri\<^sub>R(Q)) \<diamondop> false)"


text \<open> Pedro Comment: Renaming should be a relation rather than a function. \<close>

end