theory tcircus_rel
  imports tcircus_traces
begin

subsection \<open> Foundations \<close>

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

subsection \<open> Reactive Relation Constructs \<close>

definition tc_skip :: "('s, 'e) taction" ("II\<^sub>t") where
[upred_defs]: "tc_skip = ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st)"

definition TRR1 :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRR1(P) = (II\<^sub>t ;; P)"

definition TRR2 :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRR2(P) = (U($tr\<acute> = $tr \<and> $ref\<acute> = \<^bold>\<bullet>) \<or> P)"

definition TRR3 :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRR3(P) = (P ;; II\<^sub>t)"

definition uns :: "('s,'e) taction" where
[upred_defs]: "uns = U($tr\<acute> = $tr \<and> $ref\<acute> = \<^bold>\<bullet> \<and> $pat\<acute> = false)"

definition TRR4 :: "('s,'e) taction \<Rightarrow> ('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRR4 P Q = (Q \<or> P ;; uns)"

definition TRR :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRR(P) = TRR1(RR(P))"

definition TRC :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRC(P) = TRR1(RC(P))"

definition TRF :: "('s,'e) taction \<Rightarrow> ('s,'e) taction" where
[upred_defs]: "TRF(P) = TRR3(TRR(P))"

lemma TRR_idem: "TRR(TRR(P)) = TRR(P)"
  by (rel_auto)

lemma TRF_idem: "TRF(TRF(P)) = TRF(P)"
  by (rel_auto)

lemma TRR_Idempotent [closure]: "Idempotent TRR"
  by (simp add: TRR_idem Idempotent_def)

lemma TRF_Idempotent [closure]: "Idempotent TRF"
  by (simp add: TRF_idem Idempotent_def)

lemma TRR_Continuous [closure]: "Continuous TRR"
  by (rel_blast)

lemma TRF_Continuous [closure]: "Continuous TRF"
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

lemma RR_TRR [closure]: "P is RR \<Longrightarrow> TRR P is RR"
  using Healthy_def TRR_idem TRR_implies_RR by auto

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

lemma tc_skip_self_unit [simp]: "II\<^sub>t ;; II\<^sub>t = II\<^sub>t"
  by (rel_auto)

lemma TRR_tc_skip [closure]: "II\<^sub>t is TRR"
  by (rel_auto)

lemma TRF_implies_TRR3 [closure]: "P is TRF \<Longrightarrow> P is TRR3"
  by (metis (no_types, hide_lams) Healthy_def RA1 TRF_def TRR3_def tc_skip_self_unit)

lemma TRR_closed_seq [closure]: "\<lbrakk> P is TRR; Q is TRR \<rbrakk> \<Longrightarrow> P ;; Q is TRR"
  by (rule TRR_intro, simp_all add: closure unrest)

lemma TRF_implies_TRR [closure]: "P is TRF \<Longrightarrow> P is TRR"
  by (metis Healthy_def TRF_def TRR3_def TRR_closed_seq TRR_idem TRR_tc_skip)

lemma TRR_right_unit: 
  assumes "P is TRR" "$ref\<acute> \<sharp> P" "$pat\<acute> \<sharp> P"
  shows "P ;; II\<^sub>t = P"
proof -
  have "TRR(\<exists> $pat\<acute> \<bullet> \<exists> $ref\<acute> \<bullet> P) ;; II\<^sub>t = TRR(\<exists> $pat\<acute> \<bullet> \<exists> $ref\<acute> \<bullet> P)"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms ex_unrest)
qed

lemma TRF_right_unit [rpred]:
  "P is TRF \<Longrightarrow> P ;; II\<^sub>t = P"
  by (metis Healthy_if TRF_def TRF_implies_TRR TRR3_def)

lemma TRF_intro:
  assumes "P is TRR" "$ref\<acute> \<sharp> P" "$pat\<acute> \<sharp> P"
  shows "P is TRF"
  by (metis Healthy_def TRF_def TRR3_def assms TRR_right_unit)

lemma TRF_unrests [unrest]:
  assumes "P is TRF"
  shows "$ref\<acute> \<sharp> P" "$pat\<acute> \<sharp> P"
proof -
  have "$ref\<acute> \<sharp> TRF(P)" "$pat\<acute> \<sharp> TRF(P)" 
    by (rel_auto)+
  thus "$ref\<acute> \<sharp> P" "$pat\<acute> \<sharp> P"
    by (simp_all add: Healthy_if assms)
qed

lemma TRR_TRF [closure]: "P is TRR \<Longrightarrow> TRF(P) is TRR"
  by (simp add: Healthy_if TRF_def TRR3_def TRR_closed_seq TRR_tc_skip)

lemma TRR_TRR3 [closure]: "P is TRR \<Longrightarrow> TRR3(P) is TRR"
  by (simp add: Healthy_if TRR3_def TRR_closed_seq TRR_tc_skip)

lemma TRF_tc_skip [closure]: "II\<^sub>t is TRF"
  by rel_auto

no_utp_lift RR TRR TRF

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

method trr_simp uses cls = (rule_tac TRR_transfer, simp add: closure cls, simp add: closure cls, rel_simp)

method trr_auto uses cls = (rule_tac TRR_transfer, simp add: closure cls, simp add: closure cls, rel_auto)

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

lemma TRR_USUP_closed [closure]:
  assumes "\<And> i. P(i) is TRR" "I \<noteq> {}"
  shows "(\<And> i\<in>I \<bullet> P(i)) is TRR"
proof -
  have "(\<And> i\<in>I \<bullet> P(i)) = (\<not>\<^sub>r (\<Or> i\<in>I \<bullet> \<not>\<^sub>r P(i)))"
    by (simp add: rpred closure assms)
  also have "... is TRR"
    by (meson TRR_Continuous TRR_closed_neg UINF_mem_Continuous_closed assms(1) assms(2))
  finally show ?thesis .
qed

lemma TRR_closed_wp [closure]: "\<lbrakk> P is TRR; Q is TRR \<rbrakk> \<Longrightarrow> P wp\<^sub>r Q is TRR"
  by (simp add: wp_rea_def closure)

lemma TRR_RC2_closed [closure]:
   assumes "P is TRR" shows "RC2(P) is TRR"
proof -
  have "RC2(TRR(P)) is TRR"
    by (rel_auto)
       (metis (no_types, hide_lams) Prefix_Order.prefixE Prefix_Order.prefixI append.assoc plus_list_def trace_class.add_diff_cancel_left)+
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma TRR_left_unit [rpred]: 
  assumes "P is TRR"
  shows "II\<^sub>t ;; P = P"
  by (metis Healthy_if TRR1_def TRR_def TRR_implies_RR assms)

method rrel_simp uses cls = (rule RR_eq_transfer, simp add: closure cls, simp add: closure cls)

lemma TRR_ident_intro:
  assumes "P is RR" "II\<^sub>t ;; P = P"
  shows "P is TRR"
  by (metis Healthy_def TRR1_def TRR_def assms(1) assms(2))

lemma TRR_wp_closure [closure]:
  assumes "P is TRR" "Q is TRC"
  shows "P wp\<^sub>r Q is TRC"
  by (metis Healthy_def TRC_def TRC_implies_RC TRC_implies_TRR TRR1_def TRR_closed_wp TRR_implies_RR TRR_left_unit assms(1) assms(2) wp_rea_RC)

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

lemma TRC_rea_true [closure]: "true\<^sub>r is TRC" by rel_auto

interpretation trel_theory: utp_theory_continuous TRR
  rewrites "P \<in> carrier trel_theory.thy_order \<longleftrightarrow> P is TRR"
  and "le trel_theory.thy_order = (\<sqsubseteq>)"
  and "eq trel_theory.thy_order = (=)"  
  and trel_top: "trel_theory.utp_top = false"
  and trel_bottom: "trel_theory.utp_bottom = true\<^sub>r"
proof -
  interpret utp_theory_continuous TRR
    by (unfold_locales, simp_all add: TRR_idem TRR_Continuous)
  show top:"utp_top = false"          
    by (simp add: healthy_top, rel_auto)
  show bot:"utp_bottom = true\<^sub>r"
    by (simp add: healthy_bottom, rel_auto)
  show "utp_theory_continuous TRR"
    by (unfold_locales, simp_all add: closure rpred top)
qed (simp_all)

interpretation tfin_theory: utp_theory_continuous TRF
  rewrites "P \<in> carrier tfin_theory.thy_order \<longleftrightarrow> P is TRF"
  and "le tfin_theory.thy_order = (\<sqsubseteq>)"
  and "eq tfin_theory.thy_order = (=)"  
  and tfin_top: "tfin_theory.utp_top = false"
  and tfin_bottom: "tfin_theory.utp_bottom = true\<^sub>r"
proof -
  interpret utp_theory_continuous TRF
    by (unfold_locales, simp_all add: TRF_idem TRF_Continuous)
  show top:"utp_top = false"
    by (simp add: healthy_top, rel_auto)
  show bot:"utp_bottom = true\<^sub>r"
    by (simp add: healthy_bottom, rel_auto)
  show "utp_theory_continuous TRF"
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

lemma TRR_TIP_closed [closure]:
  assumes "P is TRR"
  shows "TIP(P) is TRR"
proof -
  have "TIP(TRR(P)) is TRR"
    by (rel_auto; fastforce)
  thus ?thesis by (simp add: Healthy_if assms)
qed

no_utp_lift lift_state_rel

definition TDC :: "('s, 'e) taction \<Rightarrow> ('s, 'e) taction" where
[upred_defs]: "TDC(P) = U(\<exists> ref\<^sub>0. P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<le> \<guillemotleft>ref\<^sub>0\<guillemotright>)"


end