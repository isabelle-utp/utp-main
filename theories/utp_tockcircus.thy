section \<open> tock-Circus \<close>

theory utp_tockcircus
imports "UTP-Reactive-Designs.utp_rea_designs" "rcircus/Refusal_Tests"
begin recall_syntax

subsection \<open> Preliminaries \<close>

instantiation list :: (type) monoid_mult
begin
definition [simp]: "one_list = []"
definition [simp]: "times_list = (@)"
instance by (intro_classes; simp)
end

lemma power_replicate: "[x]^n = replicate n x"
  by (induct n; simp)

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

subsubsection \<open> Tocks \<close>

definition tocks :: "'e set \<Rightarrow> 'e tev list set" where
"tocks X = {t. \<forall> e \<in> set(t). \<exists> Y. e = Tock Y \<and> Y \<subseteq> X}"

lemma tocks_Nil [simp]: "[] \<in> tocks X"
  by (simp add: tocks_def)

lemma tocks_Tock: "t \<in> tocks X \<Longrightarrow> set t \<subseteq> range Tock"
  by (auto simp add: tocks_def)

lemma tocks_Cons: "\<lbrakk> Y \<subseteq> X; t \<in> tocks X \<rbrakk> \<Longrightarrow> Tock Y # t \<in> tocks X"
  by (simp add: tocks_def)

lemma tocks_Evt [simp]: "Evt e # t \<in> tocks X = False"
  by (simp add: tocks_def)

lemma tocks_subset: "\<lbrakk> A \<subseteq> B; t \<in> tocks A\<rbrakk> \<Longrightarrow> t \<in> tocks B"
  by (auto simp add: tocks_def)

lemma tocks_append [simp]: "s @ t \<in> tocks X \<longleftrightarrow> (s \<in> tocks X \<and> t \<in> tocks X)"
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

subsubsection \<open> Tocks Order \<close>

text \<open> This order states that two traces have the same length, and agree on the order of events 
  and tocks, but each tock can refuse fewer events. \<close>

definition tock_ord :: "'e tev list \<Rightarrow> 'e tev list \<Rightarrow> bool" (infix "\<subseteq>\<^sub>t" 50) where
"(t\<^sub>1 \<subseteq>\<^sub>t t\<^sub>2) = (length t\<^sub>1 = length t\<^sub>2 \<and> (\<forall> i<length t\<^sub>1. t\<^sub>1!i = t\<^sub>2!i \<or> (\<exists> X Y. X \<subseteq> Y \<and> t\<^sub>1!i = Tock X \<and> t\<^sub>2!i = Tock Y)))"

lemma tock_ord_refl: "x \<subseteq>\<^sub>t x"
  by (simp add: tock_ord_def)

lemma tock_ord_trans: "\<lbrakk> x \<subseteq>\<^sub>t y; y \<subseteq>\<^sub>t z \<rbrakk> \<Longrightarrow> x \<subseteq>\<^sub>t z"
  by (auto simp add: tock_ord_def, smt dual_order.trans teva.inject(1))

lemma tock_ord_antisym: "\<lbrakk> x \<subseteq>\<^sub>t y; y \<subseteq>\<^sub>t x \<rbrakk> \<Longrightarrow> x = y"
  by (auto simp add: tock_ord_def, metis nth_equalityI subset_antisym teva.inject(1))

lemma tock_ord_least [simp]: "t \<subseteq>\<^sub>t [] \<longleftrightarrow> t = []"
  by (auto simp add: tock_ord_def)

lemma tock_ord_Nil [simp]: "[] \<subseteq>\<^sub>t t \<longleftrightarrow> t = []"
  by (auto simp add: tock_ord_def)

lemma tock_ord_append: "\<lbrakk> x\<^sub>1 \<subseteq>\<^sub>t y\<^sub>1; x\<^sub>2 \<subseteq>\<^sub>t y\<^sub>2 \<rbrakk> \<Longrightarrow> x\<^sub>1 @ x\<^sub>2 \<subseteq>\<^sub>t y\<^sub>1 @ y\<^sub>2"
  apply (auto simp add: tock_ord_def)
  by (smt diff_add_cancel_left' nat_add_left_cancel_less not_less nth_append)

lemma tock_ord_decompose:
  assumes  "x \<subseteq>\<^sub>t y @ z" 
  shows "take (length y) x \<subseteq>\<^sub>t y" "drop (length y) x \<subseteq>\<^sub>t z"
  using assms
  by (auto simp add: tock_ord_def)
     (metis add_leE not_less nth_append, metis nat_add_left_cancel_less nth_append_length_plus)

lemma tocks_order_power:
  assumes "t \<in> tocks A"
  shows "t \<subseteq>\<^sub>t [Tock A]^length t"
proof -
  from assms have "\<forall>i<length t. t ! i = Tock A \<or> (\<exists>X. X \<subseteq> A \<and> t ! i = Tock X)"
    by (simp add: tocks_def, meson in_set_conv_nth)
  thus ?thesis
    by (auto simp add: tock_ord_def power_replicate)
qed

lemma tock_power_in_tocks: "[Tock A]^n \<in> tocks A"
  by (simp add: tocks_def power_replicate)

lemma tocks_ord_closed:
  "\<lbrakk> t\<^sub>1 \<in> tocks A; t\<^sub>2 \<subseteq>\<^sub>t t\<^sub>1 \<rbrakk> \<Longrightarrow> t\<^sub>2 \<in> tocks A"
  by (auto simp add: tocks_def tock_ord_def in_set_conv_nth)
     (metis (no_types, hide_lams) nth_mem subset_trans teva.inject(1))

subsubsection \<open> Other Functions \<close>

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

lemma idleprefix_tocks [simp]: "idleprefix t \<in> tocks UNIV"
  by (induct t, simp_all, metis idleprefix.elims list.sel(3) subset_UNIV tocks_Cons tocks_Nil)

fun activesuffix :: "'e tev list \<Rightarrow> 'e tev list" where
"activesuffix [] = []" |
"activesuffix (Tock A # t) = activesuffix t" |
"activesuffix (Evt x # t) = (Evt x # t)"

text \<open> If an active suffix has elements, then the first element must be an event. \<close>

lemma hd_activesuffix:
  "activesuffix t \<noteq> [] \<Longrightarrow> hd(activesuffix t) \<in> range(Evt)"
  apply (induct t, simp_all)
  apply (rename_tac a t)
  apply (case_tac a)
   apply (simp_all)
  done

text \<open> A trace can always be decomposed into an idle prefix and an active suffix. \<close>

lemma idle_active_decomp:
  "idleprefix t @ activesuffix t = t"
  apply (induct t, simp_all)
  apply (rename_tac a t)
  apply (case_tac a)
   apply (simp_all)
  done

lemma idleprefix_prefix: "idleprefix(t) \<le> t"
  by (metis Prefix_Order.prefixI idle_active_decomp)

lemma tocks_idleprefix_fp [simp]:
  "t \<in> tocks A \<Longrightarrow> idleprefix(t) = t"
  by (metis hd_Cons_tl hd_activesuffix idle_active_decomp rangeE self_append_conv tocks_Evt tocks_append)

lemma idleprefix_idem [simp]: "idleprefix (idleprefix t) = idleprefix t"
  using idleprefix_tocks tocks_idleprefix_fp by blast

subsection \<open> Reactive Relation Constructs \<close>

definition TRR1 :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRR1(P) = (\<exists> $ref \<bullet> P)"

definition TRR2 :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRR2(P) = (U($tr\<acute> = $tr \<and> $ref\<acute> = \<^bold>\<bullet>) \<or> P)"

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

text \<open> The following healthiness condition is a weakened form of prefix closure -- a relation must
  admit every idle prefix with the state unchanged and the unstable refusal. \<close>

definition TIP :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TIP(P) = (P \<or> U((\<exists> $st\<acute> \<bullet> \<exists> $ref\<acute> \<bullet> \<exists> t. P\<lbrakk>[],\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> $tr\<acute> = $tr @ idleprefix(\<guillemotleft>t\<guillemotright>)) \<and> $st\<acute> = $st \<and> $ref\<acute> = \<^bold>\<bullet>))"

utp_const RR TIP

lemma TIP_idem [simp]: "TIP (TIP P) = TIP P"
  by (rel_auto, blast)

lemma TIP_prop:
  assumes "P is RR" "P is TIP"
  shows "U(P\<lbrakk>$st,\<^bold>\<bullet>,[],idleprefix($tr\<acute>-$tr)/$st\<acute>,$ref\<acute>,$tr,$tr\<acute>\<rbrakk>) \<sqsubseteq> P" 
proof -
  have "U(TIP(RR(P))\<lbrakk>$st,\<^bold>\<bullet>,[],idleprefix($tr\<acute>-$tr)/$st\<acute>,$ref\<acute>,$tr,$tr\<acute>\<rbrakk>) \<sqsubseteq> RR(P)"
    by (rel_simp, blast)
  thus ?thesis
    by (simp add: Healthy_if assms(1) assms(2))
qed

no_utp_lift lift_state_rel

definition tc_skip :: "('s, 'e) taction" ("II\<^sub>t") where
[upred_defs]: "tc_skip = ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st)"

(*
datatype ('s,'e) tsym = Time "('e set, 's) uexpr" "(nat set, 's) uexpr" | Evts "('e list, 's) uexpr"

fun tsyme :: "('s,'e) tsym \<Rightarrow> ('s,'e) taction" where
"tsyme (Time X A) = U(\<exists> t \<in> tocks \<lceil>- X\<rceil>\<^sub>S\<^sub><. $tr\<acute> = $tr @ \<guillemotleft>t\<guillemotright> \<and> length(\<guillemotleft>t\<guillemotright>) \<in> \<lceil>A\<rceil>\<^sub>S\<^sub><)" |
"tsyme (Evts t) = U($tr\<acute> = $tr @ \<lceil>map Evt t\<rceil>\<^sub>S\<^sub><)"
*)

(*
abbreviation tsyme :: "('e tev list, 's) uexpr list \<Rightarrow> ('s, 'e) taction" where
"tsyme ts \<equiv> (bop (\<subseteq>\<^sub>t) $tr\<acute> ($tr ^\<^sub>u \<lceil>foldr (bop (@)) ts \<guillemotleft>[]\<guillemotright>\<rceil>\<^sub>S\<^sub><))"
*)

abbreviation tsyme :: "('e tev list, 's) uexpr \<Rightarrow> ('s, 'e) taction" where
"tsyme t \<equiv> U(\<exists> t\<^sub>0. $tr\<acute> = $tr @ \<guillemotleft>t\<^sub>0\<guillemotright> \<and> t\<^sub>0 \<subseteq>\<^sub>t \<lceil>t\<rceil>\<^sub>S\<^sub><)"

utp_const tsyme

lemma foldr_concat_eval [uexpr_transfer_extra]: "\<lbrakk>foldr (bop (@)) xs t\<rbrakk>\<^sub>e s = concat (map (\<lambda> e. \<lbrakk>e\<rbrakk>\<^sub>e s) xs) @ \<lbrakk>t\<rbrakk>\<^sub>e s"
  by (induct xs, rel_auto+)

definition [upred_defs]: "tc_time' X t = U(replicate t (Tock (-X)))"

utp_const tc_time'

text \<open> We introduce a small algebra for peri- and postconditions to capture timed behaviours. The
  first operator captures stable intermediate (i.e. quiescent) behaviours. Here, @{term s} is a 
  predicate on the state (a condition), @{term t} is a trace over non-tock events, and @{term E} 
  is the set of events being accepted at this point. FIXME: Should stable observations
  also update the state? \<close>

definition tc_stable :: "'s upred \<Rightarrow> ('e tev list, 's) uexpr \<Rightarrow> ((unit, 'e) teva set, 's) uexpr \<Rightarrow> ('s, 'e) taction" ("\<E>'(_, _, _')") where
[upred_defs]: "\<E>(s,t,E) = U(\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> tsyme t \<and> (\<forall> e\<in>\<lceil>E\<rceil>\<^sub>S\<^sub><. \<guillemotleft>e\<guillemotright> \<notin>\<^sub>\<R> $ref\<acute>))"

text \<open> We also need unstable intermediate observations, which the following relation provides. It
  has no set associated, since no refusal set is observed. \<close>

definition tc_unstable :: "'s upred \<Rightarrow> ('e tev list, 's) uexpr \<Rightarrow> ('s, 'e) taction" ("\<U>'(_, _')") where
[upred_defs]: "\<U>(s,t) = U(\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> tsyme t \<and> $ref\<acute> = \<^bold>\<bullet>)"

text \<open> A final observation is similar to a stable observation, except it can update the state 
  variables and does not characterise a refusal set. \<close>

definition tc_final :: "'s upred \<Rightarrow>('e tev list, 's) uexpr \<Rightarrow> 's usubst \<Rightarrow> ('s, 'e) taction" ("\<F>'(_, _, _')") where
[upred_defs]: "\<F>(s,t,\<sigma>) = U(\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> tsyme t \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S)" 
  
text \<open> A timed observation represents a period of delay. The set @{term X} characterises the set of
  events that are accepted during this period. The set @{term A} characterises the possible delay
  periods, for example @{term "{0..n}"} means a delay of between $0$ and $n$ units. \<close>

definition tc_time :: "('e set, 's) uexpr \<Rightarrow> (nat set, 's) uexpr \<Rightarrow> _" ("\<T>'(_, _')") where 
[upred_defs]: "\<T>(X, A) = U(\<exists> t \<in> tocks \<lceil>- X\<rceil>\<^sub>S\<^sub><. $tr\<acute> = $tr @ \<guillemotleft>t\<guillemotright> \<and> length(\<guillemotleft>t\<guillemotright>) \<in> \<lceil>A\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> = $st)"

utp_lift_notation tc_stable
utp_lift_notation tc_unstable
utp_lift_notation tc_final (2)
utp_lift_notation tc_time

utp_const tc_stable

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

lemma [closure]: "\<T>(X, A) is TIP"
  by (rel_auto)

lemma [unrest]: "$st\<acute> \<sharp> \<E>(s, t, E)"
  by (rel_auto)

lemma [unrest]: "$st\<acute> \<sharp> \<U>(s, t)"
  by (rel_auto)

text \<open> Unstable observations are subsumed by stable ones \<close>

lemma instability_subsumed: "\<E>(s, t, E) \<sqsubseteq> \<U>(s, t)"
  by (rel_auto)

lemma stability_modulo_ref: "(\<exists> $ref\<acute> \<bullet> \<E>(s, t, E)) = (\<exists> $ref\<acute> \<bullet> \<U>(s, t))"
  by (rel_auto, meson rmember.simps(1))

lemma tc_final_compose [rpred]: "\<F>(s\<^sub>1, t\<^sub>1, \<sigma>\<^sub>1) ;; \<F>(s\<^sub>2, t\<^sub>2, \<sigma>\<^sub>2) = \<F>(s\<^sub>1 \<and> \<sigma>\<^sub>1 \<dagger> s\<^sub>2, t\<^sub>1 @ \<sigma>\<^sub>1 \<dagger> t\<^sub>2, \<sigma>\<^sub>2 \<circ>\<^sub>s \<sigma>\<^sub>1)"
  apply (rel_auto)
  using tock_ord_append tock_ord_refl tock_ord_trans apply fastforce
  apply (metis append.assoc append_take_drop_id tock_ord_decompose)
  done

lemma time_stable_compose:
  "\<T>(X, A) ;; \<E>(s, t, E) = U(\<Sqinter> n. \<E>(n \<in> A \<and> s, bop (^) [Tock (-X)] n @ t, E))"
  apply (rel_auto)
   apply (rename_tac st ref x y)
   apply (rule_tac x="length x" in exI)
  apply (simp)
   apply (simp add: Compl_eq_Diff_UNIV tock_ord_append tock_ord_refl tock_ord_trans tocks_order_power)
  apply (rename_tac tr st ref n x)
  apply (rule exI)
  apply (rule_tac x="st" in exI)
  apply (rule)
   apply (simp)
   apply (rule_tac x="take n x" in bexI)
  apply (auto)
  apply (metis length_replicate length_take power_replicate tock_ord_decompose(1) tock_ord_def)
  apply (metis length_replicate power_replicate tock_ord_decompose(1) tock_power_in_tocks tocks_ord_closed)
  apply (metis append_take_drop_id length_replicate power_replicate tock_ord_decompose(2))
  done

lemma time_unstable_compose:
  "\<T>(X, A) ;; \<U>(s, t) = (\<Sqinter> n \<bullet> \<U>(\<guillemotleft>n\<guillemotright> \<in> A \<and> s, bop (^) [Tock (-X)] \<guillemotleft>n\<guillemotright> @ t))"
  apply (rel_auto)
  apply (metis tock_ord_append tocks_order_power)
  apply (rename_tac tr st n x)
  apply (rule exI)
  apply (rule_tac x="st" in exI)
  apply (rule)
   apply (simp)
   apply (rule_tac x="take n x" in bexI)
  apply (auto)
  apply (metis length_replicate length_take power_replicate tock_ord_decompose(1) tock_ord_def)
  apply (metis length_replicate power_replicate tock_ord_decompose(1) tock_power_in_tocks tocks_ord_closed)
  apply (metis append_take_drop_id length_replicate power_replicate tock_ord_decompose(2))
  done

lemma time_final_compose:
  "\<T>(X, A) ;; \<F>(s, t, \<sigma>) = (\<Sqinter> n \<bullet> \<F>(\<guillemotleft>n\<guillemotright> \<in> A \<and> s, bop (^) [Tock (-X)] \<guillemotleft>n\<guillemotright> @ t, \<sigma>))"
  apply (rel_auto)
  apply (metis tock_ord_append tocks_order_power)
  apply (rename_tac tr st n x)
  apply (rule exI)
  apply (rule_tac x="st" in exI)
  apply (rule)
   apply (simp)
   apply (rule_tac x="take n x" in bexI)
  apply (auto)
  apply (metis length_replicate length_take power_replicate tock_ord_decompose(1) tock_ord_def)
  apply (metis length_replicate power_replicate tock_ord_decompose(1) tock_power_in_tocks tocks_ord_closed)
  apply (metis append_take_drop_id length_replicate power_replicate tock_ord_decompose(2))
  done

lemma [rpred]: "\<F>(s\<^sub>1, t\<^sub>1, \<sigma>) ;; \<E>(s\<^sub>2, t\<^sub>2, E) = \<E>(s\<^sub>1 \<and> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1 @ \<sigma> \<dagger> t\<^sub>2, \<sigma> \<dagger> E)"
  apply (rel_auto)
  apply (metis tock_ord_append)
  apply (metis append.assoc append_take_drop_id tock_ord_decompose(1) tock_ord_decompose(2))
  done

lemma [rpred]: "\<F>(s\<^sub>1, t\<^sub>1, \<sigma>) ;; \<U>(s\<^sub>2, t\<^sub>2) = \<U>(s\<^sub>1 \<and> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1 @ \<sigma> \<dagger> t\<^sub>2)"
  apply (rel_auto)
  apply (metis tock_ord_append)
  apply (metis append.assoc append_take_drop_id tock_ord_decompose(1) tock_ord_decompose(2))
  done

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

lemma [rpred]: "\<T>(X, {}) = false"
  by (rel_auto)

lemma [rpred]: "\<T>(X, {0}) = II\<^sub>t"
  by (rel_auto)

lemma [rpred]: "\<F>(true, [], id\<^sub>s) = II\<^sub>t"
  by (rel_simp)

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

  assume a: "t \<in> tocks (- \<lbrakk>X\<rbrakk>\<^sub>e st)" "\<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e st + \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e st \<le> length t" "length t \<le> \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e st + \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e st + (\<lbrakk>n\<^sub>1\<rbrakk>\<^sub>e st + \<lbrakk>n\<^sub>2\<rbrakk>\<^sub>e st)"
  then obtain n where n: "n \<le> length t" "\<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e st \<le> n" "\<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e st + n \<le> length t" "n \<le> \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e st+\<lbrakk>n\<^sub>1\<rbrakk>\<^sub>e st" "length t \<le> \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e st+\<lbrakk>n\<^sub>2\<rbrakk>\<^sub>e st+n"
    using split_time_dom by blast

  with a show "\<exists>tr' st'.
          (\<exists>x\<in>tocks (- \<lbrakk>X\<rbrakk>\<^sub>e st). tr' = tr @ x \<and> \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e st \<le> length x \<and> length x \<le> \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e st + \<lbrakk>n\<^sub>1\<rbrakk>\<^sub>e st \<and> st' = st) \<and>
          (\<exists>xa\<in>tocks (- \<lbrakk>X\<rbrakk>\<^sub>e st'). tr @ t = tr' @ xa \<and> \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e st' \<le> length xa \<and> length xa \<le> \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e st' + \<lbrakk>n\<^sub>2\<rbrakk>\<^sub>e st' \<and> st = st')"
    apply (rule_tac x="tr @ take n t" in exI)
    apply (rule_tac x="st" in exI)
    apply (auto)
    apply (rule_tac x="drop n t" in bexI)
     apply (auto)
    done
qed

definition filter_time :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" ("time'(_')") where
[upred_defs]: "filter_time P = U(P \<and> &tt \<in> tocks UNIV)"

text \<open> The two merge types are subtly different. The first forces an event to allow resolution. The
  second also allows the empty trace to resolve it (needed for postconditions). \<close>

definition merge_time :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction \<Rightarrow> ('s, 'e) taction" (infixr "\<triangleright>\<^sub>t" 65) where
[upred_defs]: "P \<triangleright>\<^sub>t Q = U(R1(\<exists> t e es. \<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> (\<exists> $ref\<acute> \<bullet> P)\<lbrakk>\<guillemotleft>t\<guillemotright>/&tt\<rbrakk> \<and> Q \<and> &tt = \<guillemotleft>t @ (Evt e # es)\<guillemotright>))"

definition merge_time' :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction \<Rightarrow> ('s, 'e) taction" (infixr "\<triangleright>\<^sub>t''" 65) where
[upred_defs]: "P \<triangleright>\<^sub>t' Q = U(R1(\<exists> t es. \<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> (length \<guillemotleft>es\<guillemotright> > 0 \<Rightarrow> hd(\<guillemotleft>es\<guillemotright>) \<in> range(Evt)) \<and> (\<exists> $ref\<acute> \<bullet> P)\<lbrakk>\<guillemotleft>t\<guillemotright>/&tt\<rbrakk> \<and> Q \<and> &tt = \<guillemotleft>t @ es\<guillemotright>))"

utp_const filter_time merge_time

lemma time_TRR [closure]: assumes "P is TRR" shows "time(P) is TRR"
proof -
  have "TRR(time(TRR(P))) = time(TRR(P))" by rel_blast
  thus "time(P) is TRR" by (metis Healthy_def assms)
qed

lemma merge_time_TRR [closure]: assumes "P is TRR" "Q is TRR" shows "P \<triangleright>\<^sub>t Q is TRR"
proof -
  have "TRR(P) \<triangleright>\<^sub>t TRR(Q) is TRR"
    by rel_blast
  thus ?thesis
    by (simp add: Healthy_if assms)
qed


lemma merge_time'_TRR [closure]: assumes "P is TRR" "Q is TRR" shows "P \<triangleright>\<^sub>t' Q is TRR"
proof -
  have "TRR(P) \<triangleright>\<^sub>t' TRR(Q) is TRR"
    by (rel_simp, fastforce)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma tock_prefix_eq:
  assumes "x @ (Evt a # as) = y @ (Evt b # bs)" "x \<in> tocks X" "y \<in> tocks Y"
  shows "x = y \<and> a = b \<and> as = bs"
proof (safe)
  show 1:"x = y"
  proof (rule ccontr)
    assume neq: "x \<noteq> y"
    from assms(1) have "\<forall> i. (x @ (Evt a # as))!i = (y @ (Evt b # bs))!i"
      by simp
    show False
    proof (cases "length x" "length y" rule: linorder_cases)
      case less thus ?thesis
        by (metis assms(1) assms(3) less nth_append nth_append_length nth_mem rangeE subsetD teva.distinct(1) tocks_Tock)
    next
      case equal
      then show ?thesis
        by (metis append_eq_append_conv assms(1) neq)
    next
      case greater thus ?thesis
        by (metis assms(1) assms(2) nth_append nth_append_length nth_mem rangeE subsetD teva.distinct(1) tocks_Tock)
    qed
  qed
  show "a = b" 
    by (metis "1" assms(1) nth_append_length teva.inject(2))
  show "as = bs"
    by (metis "1" assms(1) list.inject same_append_eq)
qed

lemma tocks_inter: "\<lbrakk> t \<in> tocks X; t \<in> tocks Y \<rbrakk> \<Longrightarrow> t \<in> tocks (X \<inter> Y)"
  by (auto simp add: tocks_def, metis teva.inject(1))

lemma [rpred]: "(P ;; \<E>(s, t, E)) \<triangleright>\<^sub>t Q = (P ;; \<U>(s, t)) \<triangleright>\<^sub>t Q"
  by (simp add: merge_time_def seqr_exists_right[THEN sym] stability_modulo_ref)

lemma [rpred]: "(P ;; \<E>(s, t, E)) \<triangleright>\<^sub>t' Q = (P ;; \<U>(s, t)) \<triangleright>\<^sub>t' Q"
  by (simp add: merge_time'_def seqr_exists_right[THEN sym] stability_modulo_ref)

lemma [rpred]: "P \<triangleright>\<^sub>t false = false"
  by (rel_auto)

lemma [rpred]: "P \<triangleright>\<^sub>t (Q \<or> R) = (P \<triangleright>\<^sub>t Q \<or> P \<triangleright>\<^sub>t R)"
  by (rel_auto)

lemma [rpred]: "(P \<or> Q) \<triangleright>\<^sub>t R = (P \<triangleright>\<^sub>t R \<or> Q \<triangleright>\<^sub>t R)"
  by (rel_auto)

lemma [rpred]: "P \<triangleright>\<^sub>t' (Q \<or> R) = (P \<triangleright>\<^sub>t' Q \<or> P \<triangleright>\<^sub>t' R)"
  by (rel_blast)

lemma [rpred]: "(P \<or> Q) \<triangleright>\<^sub>t' R = (P \<triangleright>\<^sub>t' R \<or> Q \<triangleright>\<^sub>t' R)"
  by (rel_blast)


lemma [rpred]: "P \<triangleright>\<^sub>t (\<T>(E\<^sub>2, T\<^sub>2) ;; \<E>(s\<^sub>2, [], B)) = false"
  by (rel_auto)

lemma [rpred]: "P \<triangleright>\<^sub>t \<T>(A, B) = false"
  by (rel_auto)

lemma [rpred]: "P \<triangleright>\<^sub>t (\<T>(E\<^sub>2, T\<^sub>2) ;; \<U>(s\<^sub>2, [])) = false"
  by (rel_simp)

lemma tock_ord_Evt: "x \<subseteq>\<^sub>t Evt e # y \<Longrightarrow> (\<exists> t. x = Evt e # t \<and> t \<subseteq>\<^sub>t y)"
  apply (simp add: tock_ord_def)
  apply (rule_tac x="tl x" in exI)
  apply (auto)
  apply (metis hd_Cons_tl length_0_conv nat.simps(3) nth_Cons_0 teva.distinct(1) zero_less_Suc)
  apply (metis Nitpick.size_list_simp(2) Suc_less_eq nat.simps(3) nth_Cons_Suc nth_tl)
  done

lemma tock_ord_EvtE [elim!]: "\<lbrakk> x \<subseteq>\<^sub>t Evt e # y; \<And> t. \<lbrakk> x = Evt e # t; t \<subseteq>\<^sub>t y \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis tock_ord_Evt)

lemma tock_ord_Evt_hd_eq [simp]: "Evt e # x \<subseteq>\<^sub>t Evt f # y \<longleftrightarrow> (e = f \<and> x \<subseteq>\<^sub>t y)"
  by (auto simp add: tock_ord_def)
     (smt One_nat_def add.commute diff_add_cancel_left' length_Cons less_Suc0 list.size(4) nat_add_left_cancel_less not_less nth_Cons')

lemma [rpred]: "(\<T>(E\<^sub>1, T\<^sub>1) ;; \<U>(s\<^sub>1, [])) \<triangleright>\<^sub>t (\<T>(E\<^sub>2, T\<^sub>2) ;; \<E>(s\<^sub>2, Evt e # es, B)) = \<T>(E\<^sub>1 \<union> E\<^sub>2, T\<^sub>1 \<inter> T\<^sub>2) ;; \<E>(s\<^sub>1 \<and> s\<^sub>2, Evt e # es, B)"
  apply (rel_auto)
   apply (drule tock_prefix_eq)
  apply (auto)[1]
    apply (auto)[1]
   apply (auto)[1]
   apply (rename_tac tr st ref x y)
   apply (rule exI)
   apply (rule_tac x="st" in exI)
   apply (simp)
   apply (rule)
  apply (rule_tac x="x" in bexI)
  apply (simp)
    apply (metis tocks_inter) 
    apply (rule_tac x="Evt (\<lbrakk>e\<rbrakk>\<^sub>e st) # y" in exI)
  apply (simp)
   apply (rename_tac tr st ref x y)
  apply (rule_tac x="x" in exI)
  apply (simp)
     apply (rule)
      apply (auto)[1]
   apply (metis subset_UNIV tocks_subset)
      apply (auto)[1]
  apply (metis Diff_Compl Diff_subset tocks_subset)
  apply (metis append_eq_appendI semilattice_inf_class.inf_le2 tock_ord_Evt_hd_eq tocks_subset)
  done

lemma [rpred]: "(\<T>(E\<^sub>1, T\<^sub>1) ;; \<U>(s\<^sub>1, [])) \<triangleright>\<^sub>t (\<T>(E\<^sub>2, T\<^sub>2) ;; \<U>(s\<^sub>2, Evt e # es)) = \<T>(E\<^sub>1 \<union> E\<^sub>2, T\<^sub>1 \<inter> T\<^sub>2) ;; \<U>(s\<^sub>1 \<and> s\<^sub>2, Evt e # es)"
  apply (rel_auto)
   apply (drule tock_prefix_eq)
  apply (auto)[1]
    apply (auto)[1]
   apply (auto)[1]
   apply (rename_tac tr st x y)
   apply (rule exI)
   apply (rule_tac x="st" in exI)
   apply (simp)
   apply (rule)
  apply (rule_tac x="x" in bexI)
  apply (simp)
    apply (metis tocks_inter) 
    apply (rule_tac x="Evt (\<lbrakk>e\<rbrakk>\<^sub>e st) # y" in exI)
  apply (simp)
   apply (rename_tac tr st x y)
  apply (rule_tac x="x" in exI)
  apply (simp)
     apply (rule)
      apply (auto)[1]
   apply (metis subset_UNIV tocks_subset)
      apply (auto)[1]
  apply (metis Diff_Compl Diff_subset tocks_subset)
  apply (metis append_eq_appendI semilattice_inf_class.inf_le2 tock_ord_Evt_hd_eq tocks_subset)
  done

lemma tock_prefix_eq':
  assumes "x @ (Evt a # as) = y @ z" "x \<in> tocks X" "y \<in> tocks Y" "hd(z) \<in> range(Evt)"
  shows "x = y \<and> z = Evt a # as"
proof -
  obtain b bs where "z = Evt b # bs"
    by (metis append.right_neutral assms(1) assms(3) assms(4) hd_Cons_tl image_iff tocks_Evt tocks_append)
  thus ?thesis
    by (metis assms(1) assms(2) assms(3) tock_prefix_eq)
qed

lemma [rpred]: "(\<T>(E\<^sub>1, T\<^sub>1) ;; \<U>(s\<^sub>1, [])) \<triangleright>\<^sub>t' (\<T>(E\<^sub>2, T\<^sub>2) ;; \<F>(s\<^sub>2, Evt e # es, \<sigma>)) = \<T>(E\<^sub>1 \<union> E\<^sub>2, T\<^sub>1 \<inter> T\<^sub>2) ;; \<F>(s\<^sub>1 \<and> s\<^sub>2, Evt e # es, \<sigma>)"
  apply (rel_auto)
   apply (rename_tac tr st a b x E t)
   apply (drule tock_prefix_eq')
      apply (simp)
     apply (simp)
    apply (simp)
   apply (rule exI)
   apply (rule_tac x="st" in exI)
   apply (simp)
   apply (rule)
  apply (rule_tac x="a" in bexI)
  apply (auto)[1]
    apply (metis tocks_inter)
  apply simp 
   apply (rename_tac tr st x y)
  apply (rule_tac x="x" in exI)
  apply (simp)
     apply (rule)
   apply (metis subset_UNIV tocks_subset)
      apply (auto)[1]
  apply (metis Diff_Compl Diff_subset tocks_subset)
  apply (metis append.assoc semilattice_inf_class.inf_le2 tock_ord_Evt_hd_eq tocks_subset)
  done


lemma [rpred]: "(\<T>({}, T\<^sub>1) ;; \<U>(true, [])) \<triangleright>\<^sub>t' \<T>({}, T\<^sub>2) = \<T>({}, T\<^sub>1 \<inter> T\<^sub>2)"
  by (rel_auto, metis add.right_neutral hd_Cons_tl list.size(3) tocks_Evt)
  
lemma [rpred]: "time(II\<^sub>t) = II\<^sub>t"
  by (rel_auto)

lemma [rpred]: "time(false) = false"
  by (rel_auto)

lemma [rpred]: "time(\<T>(X, A)) = \<T>(X, A)" 
  by (rel_auto, simp add: tocks_subset)

lemma time_tocks_stable [rpred]: "time(\<T>(X, A) ;; \<E>(s, [], E)) = \<T>(X, A) ;; \<E>(s, [], E)"
  by (rel_auto, simp add: tocks_subset)

lemma [rpred]: "time(P \<or> Q) = (time(P) \<or> time(Q))"
  by (rel_auto)

lemma [rpred]: "time(\<T>(X, A) ;; \<U>(s, [])) = \<T>(X, A) ;; \<U>(s, [])"
  by (rel_auto, simp add: tocks_subset)

lemma [rpred]: "time(\<E>(s, [], E)) = \<E>(s, [], E)"
  by (rel_auto)

lemma [rpred]: "time(\<E>(s, Evt t # ts, E)) = false"
  by (rel_simp)

lemma [rpred]: "time(\<U>(s, Evt t # ts)) = false"
  by (rel_simp)

lemma [rpred]: "(\<T>(X\<^sub>1, A\<^sub>1) \<and> \<T>(X\<^sub>2, A\<^sub>2)) = \<T>(X\<^sub>1 \<union> X\<^sub>2, A\<^sub>1 \<inter> A\<^sub>2)"
  apply (rel_auto)
  apply (auto simp add: tocks_def)
  apply fastforce
  done

lemma [rpred]: "(\<T>(A, T\<^sub>1) ;; \<E>(s\<^sub>1, [], {Tock ()}) \<and> \<T>(B, T\<^sub>2) ;; \<E>(s\<^sub>2, [], {Tock ()})) 
       = \<T>(A \<union> B, T\<^sub>1 \<inter> T\<^sub>2) ;; \<E>(s\<^sub>1 \<and> s\<^sub>2, [], {Tock ()})"
  apply (rel_auto)
  apply (simp add: Diff_Un tocks_inter)
  apply (metis Diff_Compl Diff_subset tocks_subset)
  apply (metis semilattice_inf_class.inf_le2 tocks_subset)
  done

lemma [rpred]: "(\<T>(X, A) ;; \<E>(true, [], E\<^sub>1) \<and> \<T>(Y, B) ;; \<E>(true, [], E\<^sub>2)) = \<T>(X \<union> Y, A \<inter> B) ;; \<E>(true, [], E\<^sub>1 \<union> E\<^sub>2)"
  apply (rel_auto)
  apply (metis tocks_inter)
  apply (metis Diff_Compl Diff_subset tocks_subset)
  apply (metis semilattice_inf_class.inf_le2 tocks_subset)
  done

lemma nat_set_simps [simp]:
  fixes m::"(nat, _) uexpr"
  shows "U({0..<m} \<inter> {m}) = U({})" "U(A \<inter> A) = U(A)"
  by (rel_simp+)

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

lemma TC1_rdes [rdes_def]:
  assumes "Q is TRR" "R is TRR"
  shows "TC1(\<^bold>R(true\<^sub>r \<turnstile> Q \<diamondop> R)) = \<^bold>R(true\<^sub>r \<turnstile> (\<U>(true, []) \<or> Q) \<diamondop> R)"
  using assms
  by (rdes_simp simps: trr_left_unit)

lemma trr_right_unit: 
  assumes "P is TRR" "$ref\<acute> \<sharp> P"
  shows "P ;; II\<^sub>t = P"
proof -
  have "TRR(\<exists> $ref\<acute> \<bullet> P) ;; II\<^sub>t = TRR(\<exists> $ref\<acute> \<bullet> P)"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms(1) assms(2) ex_unrest)
qed

lemma TC2_rdes [rdes_def]:
  assumes "Q is TRR" "$ref\<acute> \<sharp> R" "R is TRR"
  shows "TC2(\<^bold>R(true\<^sub>r \<turnstile> Q \<diamondop> R)) = \<^bold>R(true\<^sub>r \<turnstile> (Q \<or> R ;; \<U>(true, [])) \<diamondop> R)"
  using assms by (rdes_simp simps: trr_right_unit)

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
[rdes_def]: "Stop = \<^bold>R(true\<^sub>r \<turnstile> \<T>({}, {0..}) ;; \<E>(true, [], {Tock ()}) \<diamondop> false)"

lemma Stop_TC [closure]: "Stop is TC"
  by (rule Healthy_intro, rdes_eq)

text \<open> An untimed deadlock is stable, but does not accept any events. \<close>

definition Stop\<^sub>U :: "('s,'e) taction" where
[rdes_def]: "Stop\<^sub>U = \<^bold>R(true\<^sub>r \<turnstile> \<E>(true, [], {}) \<diamondop> false)"

lemma Stop\<^sub>U_TC [closure]: "Stop\<^sub>U is TC"
  by (rule Healthy_intro, rdes_eq)

text \<open> SDF: Check the following definition against the tick-tock paper. It only allows prefixing
  of non-tock events for now. \<close>

definition DoT :: "('e, 's) uexpr \<Rightarrow> ('s, 'e) taction" ("do\<^sub>T'(_')") where
[rdes_def]: "DoT a =
  \<^bold>R(true\<^sub>r 
  \<turnstile> \<T>({a}, {0..}) ;; (\<E>(true, [], {Tock (), Evt a}) \<or> \<U>(true, [Evt a]))
  \<diamondop> \<T>({a}, {0..}) ;; \<F>(true, [Evt a], id\<^sub>s))"

lemma DoT_TC: "do\<^sub>T(e) is TC"
  by (rule Healthy_intro, rdes_eq)

definition Wait :: "(nat, 's) uexpr \<Rightarrow> ('s,'e) taction" where
[rdes_def]: "Wait n = 
  \<^bold>R(true\<^sub>r 
    \<turnstile> ((\<T>({}, {0..<n}) ;; \<E>(true, [], {Tock ()})) 
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
          \<F>(true, [], \<^U>([x \<mapsto>\<^sub>s &x + 1])) ;; \<T>({a}, {0..}) ;; \<E>(true, [], {Tock (), Evt a}) \<or>
          \<F>(true, [], \<^U>([x \<mapsto>\<^sub>s &x + 1])) ;; \<T>({a}, {0..}) ;; \<U>(true, [Evt a])) \<diamondop>
         \<F>(true, [], \<^U>([x \<mapsto>\<^sub>s &x + 1])) ;; \<T>({a}, {0..}) ;; \<F>(true, [Evt a], \<^U>([x \<mapsto>\<^sub>s &x + 1])))"
  by (rdes_simp, simp add: rpred seqr_assoc usubst)

lemma "Wait(m) ;; do\<^sub>T(a) ;; \<langle>[x \<mapsto>\<^sub>s &x + 1]\<rangle>\<^sub>T = 
      \<^bold>R (true\<^sub>r \<turnstile>
        (\<T>({}, {0..<m}) ;; \<E>(true, [], {Tock ()}) \<or>
         \<T>({}, {m}) ;; \<U>(true, []) \<or> 
         \<T>({}, {m}) ;; \<T>({a}, {0..}) ;; \<E>(true, [], {Tock (), Evt a}) \<or> 
         \<T>({}, {m}) ;; \<T>({a}, {0..}) ;; \<U>(true, [Evt a])) \<diamondop>
         \<T>({}, {m}) ;; \<T>({a}, {0..}) ;; \<F>(true, [Evt a], [x \<mapsto>\<^sub>s &x + 1]))"
  apply (rdes_simp)
  apply (simp add: rpred seqr_assoc usubst)
  oops

definition extChoice :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction \<Rightarrow> ('s, 'e) taction" (infixl "\<box>" 69) where
"P \<box> Q =
  \<^bold>R((pre\<^sub>R(P) \<and> pre\<^sub>R(Q))
  \<turnstile> (time(peri\<^sub>R(P)) \<and> time(peri\<^sub>R(Q)) 
    \<or> peri\<^sub>R(P) \<triangleright>\<^sub>t peri\<^sub>R(Q)
    \<or> peri\<^sub>R(Q) \<triangleright>\<^sub>t peri\<^sub>R(P))
  \<diamondop> (peri\<^sub>R(P) \<triangleright>\<^sub>t' post\<^sub>R(Q) \<or> peri\<^sub>R(Q) \<triangleright>\<^sub>t' post\<^sub>R(P)))"

lemma extChoice_rdes_def [rdes_def]:
  assumes "P\<^sub>2 is RR" "P\<^sub>3 is RR" "Q\<^sub>2 is RR" "Q\<^sub>3 is RR"
  shows
  "\<^bold>R(true\<^sub>r \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<box> \<^bold>R(true\<^sub>r \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) =
       \<^bold>R(true\<^sub>r 
        \<turnstile> (time(P\<^sub>2) \<and> time(Q\<^sub>2) \<or> P\<^sub>2 \<triangleright>\<^sub>t Q\<^sub>2 \<or> Q\<^sub>2 \<triangleright>\<^sub>t P\<^sub>2)
        \<diamondop> (P\<^sub>2 \<triangleright>\<^sub>t' Q\<^sub>3 \<or> Q\<^sub>2 \<triangleright>\<^sub>t' P\<^sub>3))"
  by (simp add: extChoice_def rdes assms closure rpred)

lemma [dest]: "x \<in>\<^sub>\<R> \<^bold>\<bullet> \<Longrightarrow> P"
  by (metis rmember.simps(1))

lemma "Skip \<box> Stop = Skip"
  by (rdes_eq)
  
lemma "Wait m \<box> Wait m = Wait m"
  by (rdes_simp)

lemma "Wait m \<box> Wait n = Wait U(min m n)"
  by (rdes_eq)

lemma append_in_dist_conat: "\<lbrakk> x \<in> xs; y \<in> ys \<rbrakk> \<Longrightarrow> x @ y \<in> xs \<^sup>\<frown> ys"
  by (auto simp add: dist_concat_def)

lemma [rpred]: "time(\<T>(X, T) ;; \<U>(true, [Evt a])) = false"
  by (rel_simp)

lemma [simp]: "U(insert x (insert x A)) = U(insert x A)"
  by (rel_auto)

lemma [rpred]: "P \<triangleright>\<^sub>t' false = false"
  by (rel_auto)

lemma [rpred]: "P \<triangleright>\<^sub>t' (\<Sqinter> i \<bullet> Q(i)) = (\<Sqinter> i \<bullet> P \<triangleright>\<^sub>t' Q(i))"
  by (rel_auto)

lemma "Stop \<box> do\<^sub>T(a) = do\<^sub>T(a)"
  by (rdes_eq_split)

lemma "Wait m \<box> Skip = Skip"
  by (rdes_eq, metis list.exhaust_sel tocks_Evt)

lemma "Stop \<box> \<langle>\<sigma>\<rangle>\<^sub>T = \<langle>\<sigma>\<rangle>\<^sub>T"
  by (rdes_eq)

lemma [rpred]: "time(\<U>(b, [])) = \<U>(b, [])"
  by (rel_auto)

lemma [rpred]: "P \<triangleright>\<^sub>t \<U>(s, []) = false"
  by (rel_auto)

lemma RR_idleprefix_merge' [rpred]:
  assumes "P is RR"
  shows "(\<T>({}, {0..}) ;; \<U>(true, [])) \<triangleright>\<^sub>t' P = P"
proof -
  have "(\<T>({}, {0..}) ;; \<U>(true, [])) \<triangleright>\<^sub>t' (RR P) = (RR P)"
    apply (rel_auto)
    apply (rename_tac tr st ref tr' st' ref' a aa ab b)
    apply (rule_tac x="idleprefix (tr' - tr)" in exI)
    apply (simp)
    apply (rule_tac x="activesuffix (tr' - tr)" in exI)
    apply auto
    using hd_activesuffix apply blast
    apply (simp add: idle_active_decomp)
    done
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma [rpred]:
  assumes "P is RR" 
  shows "(time(P) \<or> (P \<triangleright>\<^sub>t P)) = (P \<triangleright>\<^sub>t' P)"
proof -
  have "(time(RR(P)) \<or> (RR P \<triangleright>\<^sub>t RR P)) = (RR P \<triangleright>\<^sub>t' RR P)"
    apply (rel_auto)
      apply blast
     apply fastforce
    apply (metis hd_Cons_tl tocks_Nil)
    done
  thus ?thesis by (simp add: Healthy_if assms)
qed



lemma 
  assumes "P is RR" "P is TIP"
  shows "P \<triangleright>\<^sub>t' P \<sqsubseteq> P"
proof -
  have "RR P \<triangleright>\<^sub>t' RR P \<sqsubseteq> (U(RR(P) \<and> P\<lbrakk>$st,\<^bold>\<bullet>,[],idleprefix($tr\<acute>-$tr)/$st\<acute>,$ref\<acute>,$tr,$tr\<acute>\<rbrakk>))"
  apply (rel_simp)
  apply (rename_tac ok wait tr st ref ok' wait' tr' st' ref' a aa ab b)
(*  apply (subst (asm) Healthy_if[THEN sym, OF assms]) *)
   apply (rule_tac x="idleprefix(tr' - tr)" in exI)
  apply (simp)
   apply (rule_tac x="activesuffix(tr' - tr)" in exI)
    apply (auto)
    using hd_activesuffix apply blast
    apply (rule_tac x="\<^bold>\<bullet>" in exI)
     apply (rule_tac x="ok" in exI)
     apply (rule_tac x="ok'" in exI)
     apply (rule_tac x="wait" in exI)
     apply (rule_tac x="wait'" in exI)
    oops



lemma 
  assumes "P is NRD" "pre\<^sub>R(P) = true\<^sub>r"
  shows "P \<box> P = P"
  apply (rdes_eq_split cls: assms)
  oops

lemma
  assumes "P is NRD" "pre\<^sub>R(P) = true\<^sub>r"
  shows "Stop \<box> P = P"
  apply (rdes_eq_split cls: assms)
  apply (simp_all add: rpred closure assms)
  apply (rel_auto)
  oops

text \<open> Pedro Comment: Renaming should be a relation rather than a function. \<close>

end