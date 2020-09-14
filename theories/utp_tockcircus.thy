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
  ref :: "'e refusal"
  pat :: "bool" 

text \<open> We record patience/urgency via the @{const pat} variable instead of in the refusal set. This
  is so that conjunction works -- time is deterministic, and so a process is patient (accepts
  Tock) only when all subprocesses do. \<close>

text \<open> The $ref$ variable is not simply a set, but a set augmented with the @{term "\<^bold>\<bullet>"} that denotes
  stability. We need this because tick-tock traces can end without a refusal. Note that unlike
  in the trace this is a refusal over @{typ "'e tev"} so that we can refuse tocks at the end. \<close>

text \<open> The interpretation of $wait$ changes to there being both stable (quiescent) and unstable.
  Extra information is needed for refusals. What is the meaning pericondition? \<close>

(* FIXME: Nasty hack below *)

lemma tc_splits:
  "(\<forall>r. P r) = (\<forall>ok wait tr st ref pat more. P \<lparr>ok\<^sub>v = ok, wait\<^sub>v = wait, tr\<^sub>v = tr, st\<^sub>v = st, ref\<^sub>v = ref, pat\<^sub>v = pat, \<dots> = more\<rparr>)"
  "(\<exists>r. P r) = (\<exists> ok wait tr st ref pat more. P \<lparr>ok\<^sub>v = ok, wait\<^sub>v = wait, tr\<^sub>v = tr, st\<^sub>v = st, ref\<^sub>v = ref, pat\<^sub>v = pat, \<dots> = more\<rparr>)"
  by (metis rp_vars.select_convs(3) rsp_vars.surjective tc_vars.surjective)+

declare tc_vars.splits [alpha_splits del]
declare des_vars.splits [alpha_splits del]
declare rp_vars.splits [alpha_splits del]
declare rsp_vars.splits [alpha_splits del]
declare tc_splits [alpha_splits]
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

lemma tocks_Cons [intro]: "\<lbrakk> Y \<subseteq> X; t \<in> tocks X \<rbrakk> \<Longrightarrow> Tock Y # t \<in> tocks X"
  by (simp add: tocks_def)

lemma tocks_inter [intro!]: "\<lbrakk> t \<in> tocks X; t \<in> tocks Y \<rbrakk> \<Longrightarrow> t \<in> tocks (X \<inter> Y)"
  by (auto simp add: tocks_def, metis teva.inject(1))

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

lemma tocks_inter1 [dest]: "t \<in> tocks (X \<inter> Y) \<Longrightarrow> t \<in> tocks(X)"
  by (auto simp add: tocks_def)

lemma tocks_inter2 [dest]: "t \<in> tocks (X \<inter> Y) \<Longrightarrow> t \<in> tocks(Y)"
  by (auto simp add: tocks_def)

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

lemma idleprefix_concat_Evt [simp]: "idleprefix (t @ Evt e # t') = idleprefix t"
  by ((induct t; simp), metis idleprefix.simps(2) idleprefix.simps(3) teva.exhaust)

lemma idleprefix_prefix: "idleprefix(t) \<le> t"
  by (metis Prefix_Order.prefixI idle_active_decomp)

lemma tocks_idleprefix_fp [simp]:
  "t \<in> tocks A \<Longrightarrow> idleprefix(t) = t"
  by (metis hd_Cons_tl hd_activesuffix idle_active_decomp rangeE self_append_conv tocks_Evt tocks_append)

lemma tocks_iff_idleprefix_fp: "t \<in> tocks UNIV \<longleftrightarrow> idleprefix t = t"
  by (metis idleprefix_tocks tocks_idleprefix_fp)

lemma idleprefix_idem [simp]: "idleprefix (idleprefix t) = idleprefix t"
  using idleprefix_tocks tocks_idleprefix_fp by blast

subsection \<open> Reactive Relation Constructs \<close>

definition tc_skip :: "('s, 'e) taction" ("II\<^sub>t") where
[upred_defs]: "tc_skip = ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st)"

definition TRR1 :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRR1(P) = (II\<^sub>t ;; P)"

definition TRR2 :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRR2(P) = (U($tr\<acute> = $tr \<and> $ref\<acute> = \<^bold>\<bullet>) \<or> P)"

definition TRR3 :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRR3(P) = (P ;; II\<^sub>t)"

definition TRR :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRR(P) = TRR1(RR(P))"

definition TRC :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRC(P) = TRR1(RC(P))"

definition TRF :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRF(P) = TRR3(TRR(P))"

lemma TRR_idem: "TRR(TRR(P)) = TRR(P)"
  by (rel_auto)

lemma TRR_Idempotent [closure]: "Idempotent TRR"
  by (simp add: TRR_idem Idempotent_def)

lemma TRR_Continuous [closure]: "Continuous TRR"
  by (rel_blast)

lemma TRR_alt_def: "TRR(P :: ('s,'e) taction) = (\<exists> $pat \<bullet> \<exists> $ref \<bullet> RR(P))"
  by rel_blast

lemma TRR_intro:
  assumes "$ref \<sharp> P" "$pat \<sharp> P" "P is RR"
  shows "P is TRR"
  by (simp add: TRR_alt_def Healthy_def, simp add: Healthy_if assms ex_unrest)

lemma TRR_unrest_ref [unrest]: "P is TRR \<Longrightarrow> $ref \<sharp> P"
  by (metis (no_types, lifting) Healthy_if TRR_alt_def exists_twice in_var_indep in_var_uvar ref_vwb_lens tc_vars.indeps(2) unrest_as_exists unrest_ex_diff vwb_lens_mwb)

lemma TRR_unrest_pat [unrest]: "P is TRR \<Longrightarrow> $pat \<sharp> P"
  by (metis (no_types, hide_lams) Healthy_if TRR_alt_def exists_twice in_var_uvar pat_vwb_lens unrest_as_exists vwb_lens_mwb)

lemma TRR_implies_RR [closure]: 
  assumes "P is TRR"
  shows "P is RR"
proof -
  have "RR(TRR(P)) = TRR(P)"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma TRC_implies_TRR [closure]:
  assumes "P is TRC"
  shows "P is TRR"
proof -
  have "TRC(P) is TRR"
    apply (rel_auto)
    apply (meson eq_iff minus_cancel_le)
    apply (metis (no_types, hide_lams) Prefix_Order.prefixE Prefix_Order.prefixI Prefix_Order.same_prefix_prefix plus_list_def trace_class.add_diff_cancel_left)
    done
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma TRC_implies_RC2 [closure]:
  assumes "P is TRC"
  shows "P is RC2"
proof -
  have "TRC(P) is RC2"
    by (rel_auto, blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma TRC_implies_RC [closure]: "P is TRC \<Longrightarrow> P is RC"
  by (simp add: RC_intro_prefix_closed TRC_implies_RC2 TRC_implies_TRR TRR_implies_RR)

lemma TRR_closed_TRC [closure]: "TRC(P) is TRR"
  by (metis (no_types, hide_lams) Healthy_Idempotent Healthy_if RC1_RR_closed RC_def TRC_def TRR_Idempotent TRR_def comp_apply rrel_theory.HCond_Idempotent)

utp_const RR TRR 

lemma TRR_transfer_refine:
  fixes P Q :: "('s, 'e) taction"
  assumes "P is TRR" "Q is TRR" 
    "(\<And> t s s' r p. U([$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s true, $wait\<acute> \<mapsto>\<^sub>s true, $tr \<mapsto>\<^sub>s [], $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>, $st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $ref \<mapsto>\<^sub>s \<^bold>\<bullet>, $ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>r\<guillemotright>, $pat \<mapsto>\<^sub>s false, $pat\<acute> \<mapsto>\<^sub>s \<guillemotleft>p\<guillemotright>] \<dagger> P) 
                   \<sqsubseteq> U([$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s true, $wait\<acute> \<mapsto>\<^sub>s true, $tr \<mapsto>\<^sub>s [], $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>, $st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $ref \<mapsto>\<^sub>s \<^bold>\<bullet>, $ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>r\<guillemotright>, $pat \<mapsto>\<^sub>s false, $pat\<acute> \<mapsto>\<^sub>s \<guillemotleft>p\<guillemotright>] \<dagger> Q))"
  shows "P \<sqsubseteq> Q"
proof -
  have "(\<And> t s s' r p. U([$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s true, $wait\<acute> \<mapsto>\<^sub>s true, $tr \<mapsto>\<^sub>s [], $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>, $st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $ref \<mapsto>\<^sub>s \<^bold>\<bullet>, $ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>r\<guillemotright>, $pat \<mapsto>\<^sub>s false, $pat\<acute> \<mapsto>\<^sub>s \<guillemotleft>p\<guillemotright>] \<dagger> TRR P) 
                     \<sqsubseteq> U([$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s true, $wait\<acute> \<mapsto>\<^sub>s true, $tr \<mapsto>\<^sub>s [], $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>, $st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $ref \<mapsto>\<^sub>s \<^bold>\<bullet>, $ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>r\<guillemotright>, $pat \<mapsto>\<^sub>s false, $pat\<acute> \<mapsto>\<^sub>s \<guillemotleft>p\<guillemotright>] \<dagger> TRR Q))"
    by (metis Healthy_if assms(1) assms(2) assms(3))
  hence "TRR P \<sqsubseteq> TRR Q"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_if assms(1) assms(2))
qed


lemma TRR_transfer_eq:
  fixes P Q :: "('s, 'e) taction"
  assumes "P is TRR" "Q is TRR" 
    "(\<And> t s s' r p. U([$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s true, $wait\<acute> \<mapsto>\<^sub>s true, $tr \<mapsto>\<^sub>s [], $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>, $st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $ref \<mapsto>\<^sub>s \<^bold>\<bullet>, $ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>r\<guillemotright>, $pat \<mapsto>\<^sub>s false, $pat\<acute> \<mapsto>\<^sub>s \<guillemotleft>p\<guillemotright>] \<dagger> P) 
                   = U([$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s true, $wait\<acute> \<mapsto>\<^sub>s true, $tr \<mapsto>\<^sub>s [], $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>, $st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $ref \<mapsto>\<^sub>s \<^bold>\<bullet>, $ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>r\<guillemotright>, $pat \<mapsto>\<^sub>s false, $pat\<acute> \<mapsto>\<^sub>s \<guillemotleft>p\<guillemotright>] \<dagger> Q))"
  shows "P = Q"
proof -
  have "(\<And> t s s' r p. U([$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s true, $wait\<acute> \<mapsto>\<^sub>s true, $tr \<mapsto>\<^sub>s [], $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>, $st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $ref \<mapsto>\<^sub>s \<^bold>\<bullet>, $ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>r\<guillemotright>, $pat \<mapsto>\<^sub>s false, $pat\<acute> \<mapsto>\<^sub>s \<guillemotleft>p\<guillemotright>] \<dagger> TRR P) 
                     = U([$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s true, $wait\<acute> \<mapsto>\<^sub>s true, $tr \<mapsto>\<^sub>s [], $tr\<acute> \<mapsto>\<^sub>s \<guillemotleft>t\<guillemotright>, $st \<mapsto>\<^sub>s \<guillemotleft>s\<guillemotright>, $st\<acute> \<mapsto>\<^sub>s \<guillemotleft>s'\<guillemotright>, $ref \<mapsto>\<^sub>s \<^bold>\<bullet>, $ref\<acute> \<mapsto>\<^sub>s \<guillemotleft>r\<guillemotright>, $pat \<mapsto>\<^sub>s false, $pat\<acute> \<mapsto>\<^sub>s \<guillemotleft>p\<guillemotright>] \<dagger> TRR Q))"
    by (metis Healthy_if assms(1) assms(2) assms(3))
  hence "TRR P = TRR Q"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_if assms(1) assms(2))
qed

lemmas TRR_transfer = TRR_transfer_refine TRR_transfer_eq

text \<open> Tailored proof strategy -- eliminates irrelevant variables like ok, wait, tr and ref. \<close>

method trr_simp uses cls = (rule TRR_transfer, simp add: closure cls, simp add: closure cls, rel_simp)

method trr_auto uses cls = (rule TRR_transfer, simp add: closure cls, simp add: closure cls, rel_auto)

lemma TRR_tc_skip [closure]: "II\<^sub>t is TRR"
  by (rel_auto)

lemma TRR_closed_disj [closure]:
  assumes "P is TRR" "Q is TRR"
  shows "(P \<or> Q) is TRR"
  by (rule TRR_intro, simp_all add: unrest closure assms)

lemma TRR_closed_neg [closure]: "P is TRR \<Longrightarrow> \<not>\<^sub>r P is TRR"
  by (rule TRR_intro, simp_all add: unrest closure)

lemma TRR_closed_impl [closure]:
  assumes "P is TRR" "Q is TRR"
  shows "(P \<Rightarrow>\<^sub>r Q) is TRR"
  by (simp add: TRR_closed_disj TRR_closed_neg assms(1) assms(2) rea_impl_def)

lemma TRR_closed_seq [closure]: "\<lbrakk> P is TRR; Q is TRR \<rbrakk> \<Longrightarrow> P ;; Q is TRR"
  by (rule TRR_intro, simp_all add: closure unrest)

lemma TRR_closed_wp [closure]: "\<lbrakk> P is TRR; Q is TRR \<rbrakk> \<Longrightarrow> P wp\<^sub>r Q is TRR"
  by (simp add: wp_rea_def closure)

lemma tc_skip_self_unit [simp]: "II\<^sub>t ;; II\<^sub>t = II\<^sub>t"
  by (trr_auto)

lemma trr_left_unit: 
  assumes "P is TRR"
  shows "II\<^sub>t ;; P = P"
  by (metis Healthy_if TRR1_def TRR_def TRR_implies_RR assms)

method rrel_simp uses cls = (rule RR_eq_transfer, simp add: closure cls, simp add: closure cls)

lemma TRR_ident_intro:
  assumes "P is RR" "II\<^sub>t ;; P = P"
  shows "P is TRR"
  by (metis Healthy_def TRR1_def TRR_def assms(1) assms(2))

lemma TRR_wp_unit [wp]:
  assumes "P is TRC"
  shows "II\<^sub>t wp\<^sub>r P = P"
proof -
  have "II\<^sub>t wp\<^sub>r (TRC P) = TRC P"
    by (trr_auto cls: assms)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma TRC_wp_intro:
  assumes "P is RC" "II\<^sub>t wp\<^sub>r P = P"
  shows "P is TRC"
proof -
  have "II\<^sub>t wp\<^sub>r (RC2 (RR P)) is TRC"
    apply (rel_auto)
    apply (metis (no_types, hide_lams) Prefix_Order.prefixE Prefix_Order.prefixI Prefix_Order.same_prefix_prefix order_refl plus_list_def trace_class.add_diff_cancel_left)
    apply (meson minus_cancel_le order.trans)
    done
  thus ?thesis
    by (simp add: Healthy_if RC_implies_RR RC_prefix_closed assms)
qed

interpretation trel_theory: utp_theory_continuous TRR
  rewrites "P \<in> carrier trel_theory.thy_order \<longleftrightarrow> P is TRR"
  and "le trel_theory.thy_order = (\<sqsubseteq>)"
  and "eq trel_theory.thy_order = (=)"  
  and trel_top: "trel_theory.utp_top = false"
  and trel_bottom: "trel_theory.utp_bottom = true\<^sub>r"
proof -
  interpret utp_theory_continuous TRR
    by (unfold_locales, simp_all add: add: TRR_idem TRR_Continuous)
  show top:"utp_top = false"
    by (simp add: healthy_top, rel_auto)
  show bot:"utp_bottom = true\<^sub>r"
    by (simp add: healthy_bottom, rel_auto)
  show "utp_theory_continuous TRR"
    by (unfold_locales, simp_all add: closure rpred top)
qed (simp_all)

text \<open> The following healthiness condition is a weakened form of prefix closure -- a relation must
  admit every idle prefix with the state unchanged and the unstable refusal. \<close>

definition TIP :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TIP(P) = (P \<or> U((\<exists> $st\<acute> \<bullet> \<exists> $ref\<acute> \<bullet> \<exists> $pat\<acute> \<bullet> \<exists> t. P\<lbrakk>[],\<guillemotleft>t\<guillemotright>/$tr,$tr\<acute>\<rbrakk> \<and> $tr\<acute> = $tr @ idleprefix(\<guillemotleft>t\<guillemotright>)) \<and> $st\<acute> = $st \<and> $ref\<acute> = \<^bold>\<bullet> \<and> $pat\<acute> = false))"

utp_const RR TIP

lemma TIP_idem [simp]: "TIP (TIP P) = TIP P"
  by (rel_auto, blast)

lemma TIP_prop:
  assumes "P is TRR" "P is TIP"
  shows "U(P\<lbrakk>$st,\<^bold>\<bullet>,false,[],idleprefix($tr\<acute>-$tr)/$st\<acute>,$ref\<acute>,$pat\<acute>,$tr,$tr\<acute>\<rbrakk>) \<sqsubseteq> P" 
proof -
  have "U(TIP(TRR(P))\<lbrakk>$st,\<^bold>\<bullet>,false,[],idleprefix($tr\<acute>-$tr)/$st\<acute>,$ref\<acute>,$pat\<acute>,$tr,$tr\<acute>\<rbrakk>) \<sqsubseteq> TRR(P)"
    by (rel_simp, blast)
  thus ?thesis
    by (simp add: Healthy_if assms(1) assms(2))
qed

no_utp_lift lift_state_rel


definition TDC :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" where
[upred_defs]: "TDC(P) = U(\<exists> ref\<^sub>0. P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<le> \<guillemotleft>ref\<^sub>0\<guillemotright>)"

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

definition tc_stable :: "'s upred \<Rightarrow> ('e tev list, 's) uexpr \<Rightarrow> ('e set, 's) uexpr \<Rightarrow> 's upred \<Rightarrow> ('s, 'e) taction" ("\<E>'(_, _, _, _')") where
[upred_defs]: "\<E>(s,t,E,p) = U(\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> tsyme t \<and> (\<forall> e\<in>\<lceil>E\<rceil>\<^sub>S\<^sub><. \<guillemotleft>e\<guillemotright> \<notin>\<^sub>\<R> $ref\<acute>) \<and> ($pat\<acute> \<Rightarrow> \<lceil>p\<rceil>\<^sub>S\<^sub><))"

text \<open> We also need unstable intermediate observations, which the following relation provides. It
  has no set associated, since no refusal set is observed. \<close>

definition tc_unstable :: "'s upred \<Rightarrow> ('e tev list, 's) uexpr \<Rightarrow> ('s, 'e) taction" ("\<U>'(_, _')") where
[upred_defs]: "\<U>(s,t) = U(\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> tsyme t \<and> $ref\<acute> = \<^bold>\<bullet> \<and> $pat\<acute> = false)"

text \<open> A final observation is similar to a stable observation, except it can update the state 
  variables and does not characterise a refusal set. \<close>

definition tc_final :: "'s upred \<Rightarrow>('e tev list, 's) uexpr \<Rightarrow> 's usubst \<Rightarrow> ('s, 'e) taction" ("\<F>'(_, _, _')") where
[upred_defs]: "\<F>(s,t,\<sigma>) = U(\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> tsyme t \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S)" 
  
text \<open> A timed observation represents a period of delay. The set @{term X} characterises the set of
  events that are accepted during this period. The set @{term A} characterises the possible delay
  periods, for example @{term "{0..n}"} means a delay of between $0$ and $n$ units. \<close>

definition tc_time :: "('e set, 's) uexpr \<Rightarrow> (nat set, 's) uexpr \<Rightarrow> ('s, 'e) taction" ("\<T>'(_, _')") where 
[upred_defs]: "\<T>(X, A) = U(\<exists> t \<in> tocks \<lceil>- X\<rceil>\<^sub>S\<^sub><. $tr\<acute> = $tr @ \<guillemotleft>t\<guillemotright> \<and> length(\<guillemotleft>t\<guillemotright>) \<in> \<lceil>A\<rceil>\<^sub>S\<^sub>< \<and> $st\<acute> = $st)"

utp_lift_notation tc_stable
utp_lift_notation tc_unstable
utp_lift_notation tc_final (2)
utp_lift_notation tc_time

lemma [closure]: "\<E>(s, t, E, p) is TRR"
  by (rel_auto)

lemma [closure]: "\<E>(s, t, E, p) is TDC"
  by (rel_auto, (meson refusal_mp)+)

lemma [closure]: "\<U>(s, t) is TRR"
  by (rel_auto)

lemma [closure]: "\<F>(s, t, \<sigma>) is TRR"
  by (rel_auto)

lemma [closure]: "\<T>(X, A) is TRR"
  by (rel_auto)

lemma [closure]: "\<T>(X, A) is TIP"
  by (rel_auto)

lemma [unrest]: "$st\<acute> \<sharp> \<E>(s, t, E, p)"
  by (rel_auto)

lemma [unrest]: "$st\<acute> \<sharp> \<U>(s, t)"
  by (rel_auto)

text \<open> Unstable observations are subsumed by stable ones \<close>

lemma instability_subsumed: "\<E>(s, t, E, p) \<sqsubseteq> \<U>(s, t)"
  by (rel_auto)

lemma "(\<E>(s\<^sub>1, t, E\<^sub>1, p\<^sub>1) \<and> \<E>(s\<^sub>2, t, E\<^sub>2, p\<^sub>2)) = \<E>(s\<^sub>1 \<and> s\<^sub>2, t, E\<^sub>1 \<union> E\<^sub>2, p\<^sub>1 \<and> p\<^sub>2)"
  by (rel_auto)

lemma stability_modulo_ref: "(\<exists> $pat\<acute> \<bullet> \<exists> $ref\<acute> \<bullet> \<E>(s, t, E, p)) = (\<exists> $pat\<acute> \<bullet> \<exists> $ref\<acute> \<bullet> \<U>(s, t))"
  by (rel_auto, meson rmember.simps(1))

lemma tc_final_compose [rpred]: "\<F>(s\<^sub>1, t\<^sub>1, \<sigma>\<^sub>1) ;; \<F>(s\<^sub>2, t\<^sub>2, \<sigma>\<^sub>2) = \<F>(s\<^sub>1 \<and> \<sigma>\<^sub>1 \<dagger> s\<^sub>2, t\<^sub>1 @ \<sigma>\<^sub>1 \<dagger> t\<^sub>2, \<sigma>\<^sub>2 \<circ>\<^sub>s \<sigma>\<^sub>1)"
  apply (trr_auto)
  using tock_ord_append apply blast
  apply (metis append_take_drop_id tock_ord_decompose)
  done

utp_const UINFIMUM (1) USUPREMUM (1)

lemma time_stable_compose:
  "\<T>(X, A) ;; \<E>(s, t, E, p) = (\<Sqinter> n \<bullet> \<E>(n \<in> A \<and> s, bop (^) [Tock (-X)] n @ t, E, p))"
  apply (trr_auto)
  apply (metis lit.rep_eq tock_ord_append tocks_order_power)
  apply (metis lit.rep_eq tock_ord_append tocks_order_power)
  apply (metis (mono_tags, hide_lams) append_take_drop_id length_replicate power_replicate tock_ord_decompose(1) tock_ord_decompose(2) tock_ord_def tock_power_in_tocks tocks_ord_closed)
  apply (metis (mono_tags, hide_lams) append_take_drop_id length_replicate power_replicate tock_ord_decompose(1) tock_ord_decompose(2) tock_ord_def tock_power_in_tocks tocks_ord_closed)
  done

lemma time_unstable_compose:
  "\<T>(X, A) ;; \<U>(s, t) = (\<Sqinter> n \<bullet> \<U>(\<guillemotleft>n\<guillemotright> \<in> A \<and> s, bop (^) [Tock (-X)] \<guillemotleft>n\<guillemotright> @ t))"
  apply (trr_auto)
  apply (metis tock_ord_append tocks_order_power)
  apply (metis (mono_tags, hide_lams) append_take_drop_id length_replicate power_replicate tock_ord_decompose(1) tock_ord_decompose(2) tock_ord_def tock_power_in_tocks tocks_ord_closed)
  done

lemma time_final_compose:
  "\<T>(X, A) ;; \<F>(s, t, \<sigma>) = (\<Sqinter> n \<bullet> \<F>(\<guillemotleft>n\<guillemotright> \<in> A \<and> s, bop (^) [Tock (-X)] \<guillemotleft>n\<guillemotright> @ t, \<sigma>))"
  apply (trr_auto)
  apply (metis tock_ord_append tocks_order_power)
  apply (metis (mono_tags, hide_lams) append_take_drop_id length_replicate power_replicate tock_ord_decompose(1) tock_ord_decompose(2) tock_ord_def tock_power_in_tocks tocks_ord_closed)
  done

lemma [rpred]: "\<F>(s\<^sub>1, t\<^sub>1, \<sigma>) ;; \<E>(s\<^sub>2, t\<^sub>2, E, p) = \<E>(s\<^sub>1 \<and> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1 @ \<sigma> \<dagger> t\<^sub>2, \<sigma> \<dagger> E, \<sigma> \<dagger> p)"
  apply (trr_auto)
  apply (metis tock_ord_append)
  using tock_ord_append apply blast
  apply (metis append_take_drop_id tock_ord_decompose(1) tock_ord_decompose(2))
  apply (metis append_take_drop_id tock_ord_decompose(1) tock_ord_decompose(2))
  done

lemma [rpred]: "\<F>(s\<^sub>1, t\<^sub>1, \<sigma>) ;; \<U>(s\<^sub>2, t\<^sub>2) = \<U>(s\<^sub>1 \<and> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1 @ \<sigma> \<dagger> t\<^sub>2)"
  apply (trr_auto)
  apply (metis tock_ord_append)
  apply (metis append_take_drop_id tock_ord_decompose(1) tock_ord_decompose(2))
  done

lemma [rpred]: "\<T>(X, {}) = false"
  by (rel_auto)

lemma [rpred]: "\<T>(X, {0}) = II\<^sub>t"
  by (rel_auto)

lemma [rpred]: "\<F>(true, [], id\<^sub>s) = II\<^sub>t"
  by (rel_simp)

lemma time_single_single [rpred]: "\<T>(X, {m}) ;; \<T>(X, {n}) = \<T>(X, {m+n})"
  by (trr_auto)
     (metis (mono_tags, hide_lams) add_right_cancel append_take_drop_id length_append length_drop plus_list_def tocks_append trace_class.add_diff_cancel_left)

lemma time_single_lessthan [rpred]: "\<T>(X, {m}) ;; \<T>(X, {0..<n}) = \<T>(X, {m..<m+n})"
  by trr_auto
     (metis (no_types, lifting) add_left_strict_mono add_right_cancel append_take_drop_id diff_add_cancel_left' length_append length_drop tocks_append)

lemma time_single_atMost [rpred]: "\<T>(X, {m}) ;; \<T>(X, {0..n}) = \<T>(X, {m..m+n})"
  by trr_auto
     (metis (no_types, hide_lams) add_le_cancel_left add_right_cancel append_take_drop_id diff_add_cancel_left' length_append length_drop tocks_append)

lemma time_single_atLeast [rpred]: "\<T>(X, {m}) ;; \<T>(X, {n..}) = \<T>(X, {m+n..})"
  apply trr_auto
  apply (rename_tac t s)
  apply (rule_tac x="take (\<lbrakk>m\<rbrakk>\<^sub>e s) t" in exI)
  apply (auto)
  apply (rule_tac x="drop (\<lbrakk>m\<rbrakk>\<^sub>e s) t" in bexI)
   apply (auto)
  done

lemma split_time_dom:
  fixes l :: nat
  assumes "m\<^sub>1 + m\<^sub>2 \<le> l" "l \<le> m\<^sub>1 + m\<^sub>2 + (n\<^sub>1 + n\<^sub>2)"
  shows "(\<exists> n. n \<le> l \<and> m\<^sub>1 \<le> n \<and> m\<^sub>2 + n \<le> l \<and> n \<le> m\<^sub>1+n\<^sub>1 \<and> l \<le> m\<^sub>2+n\<^sub>2+n)"
  using assms
  by presburger

lemma [rpred]: "\<T>(X, {m\<^sub>1..m\<^sub>1+n\<^sub>1}) ;; \<T>(X, {m\<^sub>2..m\<^sub>2+n\<^sub>2}) = \<T>(X, {m\<^sub>1 + m\<^sub>2..m\<^sub>1 + m\<^sub>2+(n\<^sub>1 + n\<^sub>2)})"
proof (trr_auto)
  fix t s

  assume a: "t \<in> tocks (- \<lbrakk>X\<rbrakk>\<^sub>e s)" "\<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e s + \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e s \<le> length t" "length t \<le> \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e s + \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e s + (\<lbrakk>n\<^sub>1\<rbrakk>\<^sub>e s + \<lbrakk>n\<^sub>2\<rbrakk>\<^sub>e s)"
  then obtain n where n: "n \<le> length t" "\<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e s \<le> n" "\<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e s + n \<le> length t" "n \<le> \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e s+\<lbrakk>n\<^sub>1\<rbrakk>\<^sub>e s" "length t \<le> \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e s+\<lbrakk>n\<^sub>2\<rbrakk>\<^sub>e s+n"
    using split_time_dom by blast

  with a show "\<exists>tr. tr \<in> tocks (- \<lbrakk>X\<rbrakk>\<^sub>e s) \<and>
                \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e s \<le> length tr \<and>
                length tr \<le> \<lbrakk>m\<^sub>1\<rbrakk>\<^sub>e s + \<lbrakk>n\<^sub>1\<rbrakk>\<^sub>e s \<and> (\<exists>x\<in>tocks (- \<lbrakk>X\<rbrakk>\<^sub>e s). t = tr @ x \<and> \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e s \<le> length x \<and> length x \<le> \<lbrakk>m\<^sub>2\<rbrakk>\<^sub>e s + \<lbrakk>n\<^sub>2\<rbrakk>\<^sub>e s)"
    apply (rule_tac x="take n t" in exI)
    apply (auto)
    apply (rule_tac x="drop n t" in bexI)
     apply (auto)
    done
qed

definition filter_idle :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" ("idle'(_')") where
[upred_defs]: "filter_idle P = U(R1(P \<and> &tt \<in> tocks UNIV))"

definition filter_time :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" ("time'(_')") where
[upred_defs]: "filter_time P = U(R1(\<exists> $st\<acute> \<bullet> \<exists> $pat\<acute> \<bullet> \<exists> $ref\<acute> \<bullet> P\<lbrakk>idleprefix(&tt)/&tt\<rbrakk>))"

definition filter_active :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" ("active'(_')") where 
[upred_defs]: "filter_active(P) = U(R1(\<exists> t e t'. P \<and> \<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<and> &tt = \<guillemotleft>t @ (Evt e # t')\<guillemotright>))"

text \<open> We make the decision that state changes are not observable during idle periods, as this
  would complicate the semantics. They are only revealed at termination and quiescence. \<close>

definition merge_time :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction \<Rightarrow> ('s, 'e) taction" (infixr "\<triangleright>\<^sub>t" 65) where
[upred_defs]: 
  "P \<triangleright>\<^sub>t Q = 
    U(R1
      (\<exists> t es. &tt = \<guillemotleft>t @ es\<guillemotright> \<comment> \<open> The trace can be decomposed into two pieces \<close>
            \<and> \<guillemotleft>t\<guillemotright> \<in> tocks UNIV \<comment> \<open> The first piece is a sequence of tocks \<close>
            \<and> (\<guillemotleft>es\<guillemotright> = [] \<comment> \<open> The second piece is either empty ... \<close>
               \<or> hd(\<guillemotleft>es\<guillemotright>) \<in> range(Evt)) \<comment> \<open> ... or begins with an event \<close>
            \<and> (\<exists> $st\<acute> \<bullet> \<exists> $pat\<acute> \<bullet> \<exists> $ref\<acute> \<bullet> P)\<lbrakk>\<guillemotleft>t\<guillemotright>/&tt\<rbrakk> \<comment> \<open> The first piece is a trace of @{term P} \<close>
            \<and> Q \<comment> \<open> @{term Q} admits the whole trace \<close>
            ))"

text \<open> There is a trace whose idle prefix is shared by all elements of the set, and at least
  one element which admits the trace plus at least one event. \<close>

definition tmerge :: "'i set \<Rightarrow> ('i \<Rightarrow> ('s, 'e) taction) \<Rightarrow> ('s, 'e) taction" where
[upred_defs]: 
  "tmerge I P = 
      U(R1
        (\<exists> t es. &tt = \<guillemotleft>t @ es\<guillemotright>
               \<and> \<guillemotleft>t\<guillemotright> \<in> tocks UNIV 
               \<and> (\<guillemotleft>es\<guillemotright> = [] 
                  \<or> hd(\<guillemotleft>es\<guillemotright>) \<in> range(Evt))
               \<and> (\<Squnion> i\<in>I \<bullet> (\<exists> $st\<acute> \<bullet> \<exists> $pat\<acute> \<bullet> \<exists> $ref\<acute> \<bullet> (@P i)\<lbrakk>\<guillemotleft>t\<guillemotright>/&tt\<rbrakk>)) 
               \<and> (\<Sqinter> i \<in> I \<bullet> @P i) 
               ))"

syntax
  "_tmerge" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<And>\<^sub>t _\<in>_ \<bullet> _" [0, 0, 10] 10)

translations
  "\<And>\<^sub>t i\<in>I \<bullet> P" == "CONST tmerge I (\<lambda> i. P)"

text \<open> The time merge operator merges the delay traces of one relation with active traces of another. \<close>

utp_const filter_idle filter_active merge_time tmerge

lemma idle_TRR [closure]: assumes "P is TRR" shows "idle(P) is TRR"
proof -
  have "TRR(idle(TRR(P))) = idle(TRR(P))" by rel_blast
  thus "idle(P) is TRR" by (metis Healthy_def assms)
qed

lemma active_TRR [closure]: assumes "P is TRR" shows "active(P) is TRR"
proof -
  have "TRR(active(TRR(P))) = active(TRR(P))" by rel_blast
  thus "active(P) is TRR" by (metis Healthy_def assms)
qed

lemma time_TRR [closure]: assumes "P is TRR" shows "time(P) is TRR"
proof -
  have "TRR(time(TRR(P))) = time(TRR(P))" by rel_blast
  thus "time(P) is TRR" by (metis Healthy_def assms)
qed

lemma TRR_merge_time [closure]: 
  assumes "P is TRR" "Q is TRR" 
  shows "P \<triangleright>\<^sub>t Q is TRR"
proof -
  have "TRR(P) \<triangleright>\<^sub>t TRR(Q) is TRR"
    by (rel_simp, metis)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma 
  assumes "P is TRR"
  shows "(P \<and> time(P)) is TIP"
  apply (rel_auto) oops

lemma active_disj [rpred]: "active(P \<or> Q) = (active(P) \<or> active(Q))"
  by rel_auto

lemma idle_conj [rpred]: "idle(P \<and> Q) = (idle(P) \<and> idle(Q))"
  by (rel_auto)

lemma idle_idem [rpred]: "idle(idle(P)) = idle(P)"
  by rel_auto

lemma idle_true [rpred]: "idle(true) = \<T>({}, {0..}) ;; \<E>(true, [], {}, true)"
  by rel_auto

lemma idle_true': "idle(true) = U(R1(&tt \<in> tocks UNIV))"
  by rel_auto

lemma active_idem [rpred]: "active(active(P)) = active(P)"
  by rel_auto

lemma TRR_idle_or_active [rpred]:
  assumes "P is TRR"
  shows "(idle(P) \<or> active(P)) = P"
  by (trr_auto cls: assms)
     (metis hd_Cons_tl hd_activesuffix idle_active_decomp idleprefix_tocks rangeE tocks_Nil tocks_append)

 
lemma refine_eval_dest: "P \<sqsubseteq> Q \<Longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e s \<Longrightarrow> \<lbrakk>P\<rbrakk>\<^sub>e s"
  by (rel_auto)

lemma Healthy_after: "\<lbrakk> \<And> i. P i is H \<rbrakk> \<Longrightarrow> H \<circ> P = P"
  by (metis (mono_tags, lifting) Healthy_if fun.map_cong fun.map_id0 id_apply image_iff)

lemma tmerge_cong:  
  assumes "\<And> i. i \<in> I \<Longrightarrow> P i = Q i"
  shows "(\<And>\<^sub>t i\<in>I \<bullet> P i) = (\<And>\<^sub>t i\<in>I \<bullet> Q i)"
  using assms apply (rel_auto)
  apply (metis idle_active_decomp minus_cancel plus_list_def tocks_idleprefix_fp trace_class.add_diff_cancel_left)
  apply (metis rangeI)
  apply (metis (full_types) append_Nil2)
  apply (metis rangeI)
  done

lemma RR_tmerge [closure]:
  assumes "\<And> i. i \<in> I \<Longrightarrow> P i is RR"
  shows "(\<And>\<^sub>t i\<in>I \<bullet> P i) is RR"
proof -
  have "(\<And>\<^sub>t i\<in>I \<bullet> RR (P i)) is RR"
    by (rel_auto, blast+)
  thus ?thesis
    by (metis Healthy_if assms tmerge_cong)
qed

lemma [closure]: "P is RR \<Longrightarrow> TRR P is RR"
  using Healthy_def TRR_implies_RR trel_theory.HCond_Idem by auto

lemma TRR_tmerge [closure]:
  assumes "\<And> i. i \<in> I \<Longrightarrow> P i is TRR"
  shows "(\<And>\<^sub>t i\<in>I \<bullet> P i) is TRR"
proof -
  have "(\<And>\<^sub>t i\<in>I \<bullet> TRR (P i)) is TRR"
    unfolding Healthy_def by (rrel_auto cls: assms)
  thus ?thesis
    by (metis Healthy_if assms tmerge_cong)
qed

lemma TRR_tmerge_single [closure]: "P i is TRR \<Longrightarrow> tmerge {i} P is TRR"
  by (auto intro: closure)

lemma TRR_tmerge_dual [closure]: "\<lbrakk> P i is TRR; P j is TRR \<rbrakk> \<Longrightarrow> tmerge {i, j} P is TRR"
  by (auto intro: closure)

lemma tmerge_single:
  assumes "P i is TRR" "P i is TIP"
  shows "tmerge {i} P = P i"
  apply (trr_auto cls: assms)
  apply (drule refine_eval_dest[OF TIP_prop[OF assms(1) assms(2)]])
  apply (rel_simp')
  apply (metis hd_activesuffix idle_active_decomp idleprefix_tocks)
  done

lemma time_merge_self [rpred]:
  assumes "P is TRR" "P is TIP"
  shows "P \<triangleright>\<^sub>t P = P"
  apply (trr_auto cls: assms)
  apply (drule refine_eval_dest[OF TIP_prop[OF assms(1) assms(2)]])
  apply (rel_simp')
  apply (metis hd_activesuffix idle_active_decomp idleprefix_tocks)
  done

lemma time_conj:
  "idle(P \<and> Q) = (idle(P) \<and> idle(Q))"
  by (rel_auto)

lemma time_merge_time_left:
  "idle(P) \<triangleright>\<^sub>t Q = P \<triangleright>\<^sub>t Q"
  by (rel_auto, blast+)

lemma TRR_conj [closure]:
  assumes "P is TRR" "Q is TRR"
  shows "P \<and> Q is TRR"
proof -
  have "TRR(P) \<and> TRR(Q) is TRR"
    unfolding Healthy_def by (rrel_auto cls: assms)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma TRR_ex_ref' [closure]:
  assumes "P is TRR"
  shows "(\<exists> $ref\<acute> \<bullet> P) is TRR"
proof -
  have "(\<exists> $ref\<acute> \<bullet> TRR(P)) is TRR"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed
  
lemma shEx_or: "(\<^bold>\<exists> x \<bullet> P \<or> Q) = ((\<^bold>\<exists> x \<bullet> P) \<or> (\<^bold>\<exists> x \<bullet> Q))"
  by (rel_auto)

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


lemma tmerge_dual_1:
  assumes "P i is TRR" "P j is TRR"
  shows "tmerge {i, j} P = 
          ((P i \<triangleright>\<^sub>t P i \<and> P j \<triangleright>\<^sub>t P i) \<or> (P i \<triangleright>\<^sub>t P j \<and> P j \<triangleright>\<^sub>t P j))"
  apply (trr_auto cls: assms)
  apply blast

                      apply blast
  apply (metis (no_types) append_Nil2)
  apply blast
  apply blast
  apply blast
  apply auto
  apply blast
            apply blast
           apply blast
          apply blast
         apply blast
  apply (metis append_Nil2 list.collapse tocks_Evt)
  apply (metis (no_types) append_self_conv tocks_append)
  apply (smt append_self_conv hd_Cons_tl idleprefix_concat_Evt rangeI tocks_idleprefix_fp)
  apply blast
  apply (metis append_Nil2 hd_Cons_tl tocks_Evt)
  apply (metis append_Nil2 hd_Cons_tl tocks_Evt)
  apply (smt append_Nil2 hd_Cons_tl rangeI tock_prefix_eq tocks_Evt tocks_append)
  done

lemma [simp]: "(Q \<and> (P \<triangleright>\<^sub>t Q)) = (P \<triangleright>\<^sub>t Q)" "((P \<triangleright>\<^sub>t Q) \<and> Q) = (P \<triangleright>\<^sub>t Q)"
  by (rel_auto; blast)+

lemma tmerge_dual:
  assumes "P i is TRR" "P j is TRR" "P i is TIP" "P j is TIP"
  shows "tmerge {i, j} P = (P j \<triangleright>\<^sub>t P i \<or> P i \<triangleright>\<^sub>t P j)"
  by (simp add: tmerge_dual_1 assms time_merge_self)

lemma [rpred]: "(P ;; \<E>(s, t, E, p)) \<triangleright>\<^sub>t Q = (P ;; \<U>(s, t)) \<triangleright>\<^sub>t Q"
  by (simp add: merge_time_def seqr_exists_right[THEN sym] stability_modulo_ref)

lemma [rpred]: "P \<triangleright>\<^sub>t false = false"
  by (rel_auto)

lemma [rpred]: "P \<triangleright>\<^sub>t (Q \<or> R) = (P \<triangleright>\<^sub>t Q \<or> P \<triangleright>\<^sub>t R)"
  by (rel_blast)

lemma [rpred]: "(P \<or> Q) \<triangleright>\<^sub>t R = (P \<triangleright>\<^sub>t R \<or> Q \<triangleright>\<^sub>t R)"
  by (rel_simp, metis)

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

lemma [rpred]: "(\<T>(E\<^sub>1, T\<^sub>1) ;; \<U>(s\<^sub>1, [])) \<triangleright>\<^sub>t (\<T>(E\<^sub>2, T\<^sub>2) ;; \<E>(s\<^sub>2, [], B, p)) = \<T>(E\<^sub>1 \<union> E\<^sub>2, T\<^sub>1 \<inter> T\<^sub>2) ;; \<E>(s\<^sub>1 \<and> s\<^sub>2, [], B, p)"
  apply (trr_auto)
  apply (metis list.collapse tocks_Evt tocks_Nil)
  apply (metis add.right_neutral list.collapse list.size(3) tocks_Evt)
  apply (metis list.collapse tocks_Evt tocks_Nil)
    apply (metis add.right_neutral list.collapse list.size(3) tocks_Evt)
  apply (metis append_Nil2 tocks_idleprefix_fp tocks_iff_idleprefix_fp tocks_inter1 tocks_inter2)
  apply (metis append_Nil2 tocks_idleprefix_fp tocks_iff_idleprefix_fp tocks_inter1 tocks_inter2)
  done

lemma [rpred]: "(\<T>(E\<^sub>1, T\<^sub>1) ;; \<U>(s\<^sub>1, [])) \<triangleright>\<^sub>t (\<T>(E\<^sub>2, T\<^sub>2) ;; \<U>(s\<^sub>2, [])) = \<T>(E\<^sub>1 \<union> E\<^sub>2, T\<^sub>1 \<inter> T\<^sub>2) ;; \<U>(s\<^sub>1 \<and> s\<^sub>2, [])"
  apply (trr_auto)
  apply (metis list.collapse tocks_Evt tocks_Nil)
  apply (metis add.right_neutral list.collapse list.size(3) tocks_Evt)
  using tocks_idleprefix_fp tocks_iff_idleprefix_fp apply blast
  done

lemma [rpred]: "(\<T>(E\<^sub>1, T\<^sub>1) ;; \<U>(s\<^sub>1, [])) \<triangleright>\<^sub>t (\<T>(E\<^sub>2, T\<^sub>2) ;; \<E>(s\<^sub>2, Evt e # es, B, p)) = \<T>(E\<^sub>1 \<union> E\<^sub>2, T\<^sub>1 \<inter> T\<^sub>2) ;; \<E>(s\<^sub>1 \<and> s\<^sub>2, Evt e # es, B, p)"
  oops

lemma [rpred]: "(\<T>(E\<^sub>1, T\<^sub>1) ;; \<U>(s\<^sub>1, [])) \<triangleright>\<^sub>t (\<T>(E\<^sub>2, T\<^sub>2) ;; \<U>(s\<^sub>2, Evt e # es)) = \<T>(E\<^sub>1 \<union> E\<^sub>2, T\<^sub>1 \<inter> T\<^sub>2) ;; \<U>(s\<^sub>1 \<and> s\<^sub>2, Evt e # es)"
  oops


lemma tock_prefix_eq':
  assumes "x @ (Evt a # as) = y @ z" "x \<in> tocks X" "y \<in> tocks Y" "hd(z) \<in> range(Evt)"
  shows "x = y \<and> z = Evt a # as"
proof -
  obtain b bs where "z = Evt b # bs"
    by (metis append.right_neutral assms(1) assms(3) assms(4) hd_Cons_tl image_iff tocks_Evt tocks_append)
  thus ?thesis
    by (metis assms(1) assms(2) assms(3) tock_prefix_eq)
qed

lemma [rpred]: "(\<T>(E\<^sub>1, T\<^sub>1) ;; \<U>(s\<^sub>1, [])) \<triangleright>\<^sub>t (\<T>(E\<^sub>2, T\<^sub>2) ;; \<F>(s\<^sub>2, Evt e # es, \<sigma>)) = \<T>(E\<^sub>1 \<union> E\<^sub>2, T\<^sub>1 \<inter> T\<^sub>2) ;; \<F>(s\<^sub>1 \<and> s\<^sub>2, Evt e # es, \<sigma>)"
  apply (trr_auto)
  apply (metis append_Nil2 hd_Cons_tl idleprefix_concat_Evt tock_ord_Evt_hd_eq tocks_idleprefix_fp tocks_inter)
  apply (metis (mono_tags, lifting) idleprefix_tocks list.sel(1) range_eqI semilattice_inf_class.inf_le1 semilattice_inf_class.inf_le2 tock_ord_Evt_hd_eq tocks_idleprefix_fp tocks_subset)
  done

lemma [rpred]: "(\<T>({}, T\<^sub>1) ;; \<U>(true, [])) \<triangleright>\<^sub>t \<T>({}, T\<^sub>2) = \<T>({}, T\<^sub>1 \<inter> T\<^sub>2)"
  by (rel_auto, metis add.right_neutral hd_Cons_tl list.size(3) tocks_Evt, blast)
  
lemma [rpred]: "idle(II\<^sub>t) = II\<^sub>t"
  by (rel_auto)

lemma [rpred]: "idle(false) = false"
  by (rel_auto)

lemma [rpred]: "idle(\<T>(X, A)) = \<T>(X, A)" 
  by (rel_auto, simp add: tocks_subset)

lemma time_tocks_stable [rpred]: "idle(\<T>(X, A) ;; \<E>(s, [], E, p)) = \<T>(X, A) ;; \<E>(s, [], E, p)"
  by (rel_auto; simp add: tocks_subset)

lemma [rpred]: "idle(P \<or> Q) = (idle(P) \<or> idle(Q))"
  by (rel_auto)

lemma [rpred]: "idle(\<T>(X, A) ;; \<U>(s, [])) = \<T>(X, A) ;; \<U>(s, [])"
  by (rel_auto, simp add: tocks_subset)

lemma [rpred]: "idle(\<E>(s, [], E, p)) = \<E>(s, [], E, p)"
  by (rel_auto)

lemma [rpred]: "idle(\<E>(s, Evt t # ts, E, p)) = false"
  by (rel_simp)

lemma [rpred]: "idle(\<U>(s, Evt t # ts)) = false"
  by (rel_simp)

lemma [rpred]: "(\<T>(X\<^sub>1, A\<^sub>1) \<and> \<T>(X\<^sub>2, A\<^sub>2)) = \<T>(X\<^sub>1 \<union> X\<^sub>2, A\<^sub>1 \<inter> A\<^sub>2)"
  by (rel_auto)

lemma [rpred]: "(\<T>(A, T\<^sub>1) ;; \<E>(s\<^sub>1, [], {}, true) \<and> \<T>(B, T\<^sub>2) ;; \<E>(s\<^sub>2, [], {}, true)) 
       = \<T>(A \<union> B, T\<^sub>1 \<inter> T\<^sub>2) ;; \<E>(s\<^sub>1 \<and> s\<^sub>2, [], {}, true)"
  by (rel_auto)

lemma [rpred]: "(\<T>(X, A) ;; \<E>(true, [], E\<^sub>1, p\<^sub>1) \<and> \<T>(Y, B) ;; \<E>(true, [], E\<^sub>2, p\<^sub>2)) = \<T>(X \<union> Y, A \<inter> B) ;; \<E>(true, [], E\<^sub>1 \<union> E\<^sub>2, p\<^sub>1 \<and> p\<^sub>2)"
  by (rel_auto)

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

lemma TC1_rdes:
  assumes "P is RC" "Q is RR" "R is RR"
  shows "TC1(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = \<^bold>R(II\<^sub>t wp\<^sub>r P \<turnstile> (\<U>(true, []) \<or> TRR(Q)) \<diamondop> TRR(R))"
  using assms
  by (rdes_simp simps: trr_left_unit, simp add: TRR_def TRR1_def Healthy_if)

lemma TC1_TRR_rdes [rdes_def]:
  assumes "P is TRC" "Q is TRR" "R is TRR"
  shows "TC1(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = \<^bold>R(P \<turnstile> (\<U>(true, []) \<or> Q) \<diamondop> R)"
  by (subst TC1_rdes, simp_all add: closure assms wp Healthy_if)

lemma trr_right_unit: 
  assumes "P is TRR" "$ref\<acute> \<sharp> P" "$pat\<acute> \<sharp> P"
  shows "P ;; II\<^sub>t = P"
proof -
  have "TRR(\<exists> $pat\<acute> \<bullet> \<exists> $ref\<acute> \<bullet> P) ;; II\<^sub>t = TRR(\<exists> $pat\<acute> \<bullet> \<exists> $ref\<acute> \<bullet> P)"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms ex_unrest)
qed

lemma TRF_intro:
  assumes "P is TRR" "$ref\<acute> \<sharp> P" "$pat\<acute> \<sharp> P"
  shows "P is TRF"
  by (metis Healthy_def TRF_def TRR3_def assms trr_right_unit)

lemma TRF_unrests [unrest]:
  assumes "P is TRF"
  shows "$ref\<acute> \<sharp> P" "$pat\<acute> \<sharp> P"
proof -
  have "$ref\<acute> \<sharp> TRF(P)" "$pat\<acute> \<sharp> TRF(P)" 
    by (rel_auto)+
  thus "$ref\<acute> \<sharp> P" "$pat\<acute> \<sharp> P"
    by (simp_all add: Healthy_if assms)
qed

lemma TC2_rdes [rdes_def]:
  assumes "P is TRC" "Q is TRR" "$ref\<acute> \<sharp> R" "$pat\<acute> \<sharp> R" "R is TRR"
  shows "TC2(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = \<^bold>R(P \<turnstile>(Q \<or> R ;; \<U>(true, [])) \<diamondop> R)"
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

lemma TRR_USUP_closed [closure]:
  assumes "\<And> i. P(i) is TRR" "I \<noteq> {}"
  shows "(\<And> i\<in>I \<bullet> P(i)) is TRR"
proof -
  have "(\<And> i\<in>I \<bullet> P(i)) = (\<not>\<^sub>r (\<Or> i\<in>I \<bullet> \<not>\<^sub>r P(i)))"
    by (simp add: rpred closure assms)
  also have "... is TRR"
    by (meson TRR_closed_neg UINF_mem_Continuous_closed assms(1) assms(2) trel_theory.HCond_Cont)
  finally show ?thesis .
qed

lemma ExtChoice_empty:
  "ExtChoice {} P = Stop"
  by (simp add: ExtChoice_def Stop_def rpred)

lemma ExtChoice_single: 
  assumes "P i is NRD" "peri\<^sub>R(P i) is TRR"
  shows "ExtChoice {i} P = P i"
  by (simp add: ExtChoice_def Healthy_if rpred closure assms RD_reactive_tri_design)

lemma TRR_RC2_closed [closure]:
   assumes "P is TRR" shows "RC2(P) is TRR"
proof -
  have "RC2(TRR(P)) is TRR"
    by (rel_auto)
       (metis (no_types, hide_lams) Prefix_Order.prefixE Prefix_Order.prefixI append.assoc plus_list_def trace_class.add_diff_cancel_left)+
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

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
  apply (simp add: ExtChoice_def tmerge_dual closure assms extChoice_def rpred usup_and uinf_or conj_disj_distr)
  apply (rule rdes_tri_eq_intro)
    apply (simp_all add: assms Healthy_if closure)
  apply (simp add: disj_comm utp_pred_laws.inf.commute utp_pred_laws.sup.left_commute rpred closure assms)
  apply (simp add: utp_pred_laws.inf_commute utp_pred_laws.sup_commute)
  apply (simp add: assms insert_Diff_if)
  done

text \<open> Proving idempotence of binary external choice is complicated by the need to show that
  @{term "(time(peri\<^sub>R(P)) \<and> post\<^sub>R(P)) = post\<^sub>R(P)"} \<close>

lemma TRC_rea_true: "true\<^sub>r is TRC" by rel_auto

lemma extChoice_rdes_def [rdes_def]:
  assumes "P\<^sub>2 is TRR" "P\<^sub>3 is TRR" "Q\<^sub>2 is TRR" "Q\<^sub>3 is TRR"
  shows
  "\<^bold>R(true\<^sub>r \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<box> \<^bold>R(true\<^sub>r \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) =
       \<^bold>R(true\<^sub>r 
        \<turnstile> (idle(P\<^sub>2) \<and> idle(Q\<^sub>2) \<or> time(P\<^sub>2) \<and> active(Q\<^sub>2) \<or> time(Q\<^sub>2) \<and> active(P\<^sub>2))
        \<diamondop> (time(P\<^sub>2) \<and> Q\<^sub>3 \<or> time(Q\<^sub>2) \<and> P\<^sub>3))"
  by (simp add: extChoice_def ExtChoice_def rdes closure assms rpred)

lemma TIP_has_time [rpred]:
  assumes "P is TRR" "P is TIP"
  shows "(P \<and> time(P)) = P"
  apply (trr_auto cls: assms)
  apply (drule refine_eval_dest[OF TIP_prop[OF assms(1) assms(2)]])
  apply (rel_blast)
  done

lemma TIP_time_active [rpred]:
  assumes "P is TRR" "P is TIP"
  shows "(active(P) \<and> time(P)) = active(P)"
  apply (trr_auto cls: assms)
  apply (drule refine_eval_dest[OF TIP_prop[OF assms(1) assms(2)]])
  apply (rel_blast)
  done

lemma [rpred]: "active(\<U>(s, [])) = false"
  by (rel_auto)

lemma [rpred]: "idle(\<U>(s, [])) = \<U>(s, [])"
  by (rel_auto)

lemma [rpred]: "time(P \<or> Q) = (time(P) \<or> time(Q))"
  by (rel_auto)

lemma [rpred]:
  assumes "P is TRR"
  shows "time(P ;; \<U>(true, [])) = time(P)"
proof -
  have "time(TRR(P) ;; \<U>(true, [])) = time(TRR P)"
    by (rel_blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma ExtChoice_unary:
  assumes "P i is TC"
  shows "ExtChoice {i} P = P i"
  by (simp add: ExtChoice_single TC_implies_NRD TC_inner_TRR(2) assms)

lemma [dest]: "x \<in>\<^sub>\<R> \<^bold>\<bullet> \<Longrightarrow> P"
  by (metis rmember.simps(1))

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

lemma append_in_dist_conat: "\<lbrakk> x \<in> xs; y \<in> ys \<rbrakk> \<Longrightarrow> x @ y \<in> xs \<^sup>\<frown> ys"
  by (auto simp add: dist_concat_def)

lemma [rpred]: "idle(\<T>(X, T) ;; \<U>(true, [Evt a])) = false"
  by (rel_simp)

lemma [simp]: "U(insert x (insert x A)) = U(insert x A)"
  by (rel_auto)

lemma [rpred]: "active(\<T>(X, {0..})) = false"
  by (rel_auto)

lemma [rpred]: "active(\<T>(X, T) ;; \<U>(s, [])) = false"
  by (trr_auto)

lemma [rpred]: "P \<triangleright>\<^sub>t (\<Sqinter> i \<bullet> Q(i)) = (\<Sqinter> i \<bullet> P \<triangleright>\<^sub>t Q(i))"
  by (rel_auto, blast+)

lemma "Stop \<box> do\<^sub>T(a) = do\<^sub>T(a)"
  apply (rdes_eq_split)
    apply (simp_all add: rpred closure)
  apply (trr_auto)
  using tocks_idleprefix_fp tocks_iff_idleprefix_fp apply blast
  apply (trr_simp)
  done

lemma "Wait m \<box> Skip = Skip"
  by (rdes_eq)

lemma "Stop \<box> \<langle>\<sigma>\<rangle>\<^sub>T = \<langle>\<sigma>\<rangle>\<^sub>T"
  by (rdes_eq)

lemma [rpred]: "idle(\<U>(b, [])) = \<U>(b, [])"
  by (rel_auto)

lemma RR_idleprefix_merge' [rpred]:
  assumes "P is TRR"
  shows "(\<T>({}, {0..}) ;; \<U>(true, [])) \<triangleright>\<^sub>t P = P"
  by (trr_auto cls: assms, metis (full_types) hd_activesuffix idle_active_decomp idleprefix_tocks)

lemma [rpred]:
  assumes "P is TRR" 
  shows "(idle(P) \<or> active(P \<triangleright>\<^sub>t P)) = (P \<triangleright>\<^sub>t P)"
  apply (trr_auto cls: assms)
  apply blast
  apply blast
  apply (metis hd_Cons_tl tocks_Nil)
  done

lemma TRR_TIP_closed [closure]:
  assumes "P is TRR"
  shows "TIP(P) is TRR"
proof -
  have "TIP(TRR(P)) is TRR"
    by (rel_auto; fastforce)
  thus ?thesis by (simp add: Healthy_if assms)
qed

utp_const TRF

lemma unstable_TRF:
  assumes "P is TRF"
  shows "P ;; \<U>(true, []) = U((\<exists> $st\<acute> \<bullet> P) \<and> $ref\<acute> = \<^bold>\<bullet> \<and> $pat\<acute> = false)"
proof -
  have "TRF P ;; \<U>(true, []) = U((\<exists> $st\<acute> \<bullet> TRF P) \<and> $ref\<acute> = \<^bold>\<bullet> \<and> $pat\<acute> = false)"
    by (rel_blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma [closure]: "P is TRR \<Longrightarrow> TRF(P) is TRR"
  by (simp add: Healthy_if TRF_def TRR3_def TRR_closed_seq TRR_tc_skip)

lemma [closure]: "P is TRR \<Longrightarrow> TRR3(P) is TRR"
  by (simp add: Healthy_if TRR3_def TRR_closed_seq TRR_tc_skip)

thm RD_elim

lemma RR_elim: "\<lbrakk> P is RR; Q ([$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s true, $wait\<acute> \<mapsto>\<^sub>s true] \<dagger> P) \<rbrakk> \<Longrightarrow> Q P"
  by (simp add: usubst unrest)

lemma TRR_elim: "\<lbrakk> P is TRR; Q ([$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s true, $wait\<acute> \<mapsto>\<^sub>s true] \<dagger> P) \<rbrakk> \<Longrightarrow> Q P"
  by (simp add: usubst unrest closure)

lemma [closure]: "P is TRR \<Longrightarrow> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s true, $wait\<acute> \<mapsto>\<^sub>s true] \<dagger> P is TRR"
  by (simp add: usubst unrest closure)

lemma TRF_implies_TRR3 [closure]: "P is TRF \<Longrightarrow> P is TRR3"
  by (metis (no_types, hide_lams) Healthy_def RA1 TRF_def TRR3_def tc_skip_self_unit)

lemma TRF_implies_TRR [closure]: "P is TRF \<Longrightarrow> P is TRR"
  by (metis Healthy_def TRF_def TRR3_def TRR_closed_seq TRR_tc_skip trel_theory.HCond_Idem)

lemma TRF_time [closure]:
  "P is TRR \<Longrightarrow> time(P) is TRF"
  by (rule TRF_intro, simp add: closure unrest, simp_all add: filter_time_def unrest)

lemma TRF_right_unit:
  "P is TRF \<Longrightarrow> P ;; II\<^sub>t = P"
  by (metis Healthy_if TRF_def TRF_implies_TRR TRR3_def)

text \<open> If a pericondition @{term P} contains an unstable version of each postcondition observation
  in @{term Q}, then every time trace of the @{term P} has an extension in @{term Q}. \<close>

lemma time_peri_in_post:
  assumes "P is TRR" "P is TIP" "Q is TRF" "P \<sqsubseteq> Q ;; \<U>(true, [])"
  shows "time(P) \<sqsubseteq> Q"
proof -
  have "Q ;; \<U>(true, []) ;; II\<^sub>t \<sqsubseteq> Q"
    by (trr_auto cls: assms, blast)
  also have "P ;; II\<^sub>t \<sqsubseteq> ..."
    by (simp add: RA1 assms(4) urel_dioid.mult_isor)
  also have "time(P) ;; II\<^sub>t \<sqsubseteq> ..."
    by (simp add: TIP_has_time assms(1) assms(2) urel_dioid.mult_isor utp_pred_laws.inf.orderI)
  also have "... = time(P)"
    by (simp add: TRF_right_unit TRF_time assms(1))
  finally show ?thesis .
qed

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

lemma [rpred]: "(\<T>({}, {0..}) ;; \<E>(true, [], {}, true) \<and> idle(P)) = idle(P)"
  by (rel_auto)

lemma TRR_conj_time [rpred]:
  assumes "P is TRR"
  shows "(time(\<T>({}, {0..}) ;; \<E>(true, [], {}, true)) \<and> P) = P"
proof -
  have "(time(\<T>({}, {0..}) ;; \<E>(true, [], {}, true)) \<and> TRR(P)) = TRR(P)"
    by (rel_blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma
  assumes "P is NRD" "pre\<^sub>R(P) = true\<^sub>r" "peri\<^sub>R(P) is TRR" "post\<^sub>R(P) is TRR"
  shows "Stop \<box> P = P"
  by (rdes_eq_split cls: assms)

text \<open> Pedro Comment: Renaming should be a relation rather than a function. \<close>

end