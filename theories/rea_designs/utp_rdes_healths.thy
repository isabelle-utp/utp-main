section \<open> Reactive Designs Healthiness Conditions \<close>

theory utp_rdes_healths
  imports "UTP-Reactive.utp_reactive"
begin

subsection \<open> Preliminaries \<close>

named_theorems rdes and rdes_def and RD_elim

type_synonym ('s,'t) rdes = "('s,'t,unit) hrel_rsp"
  
translations
  (type) "('s,'t) rdes" <= (type) "('s, 't, unit) hrel_rsp"

lemma R2_st_ex: "R2 (\<exists> $st \<bullet> P) = (\<exists> $st \<bullet> R2(P))"
  by (rel_auto)

lemma R2s_st'_eq_st:
  "R2s($st\<acute> =\<^sub>u $st) = ($st\<acute> =\<^sub>u $st)"
  by (rel_auto)

lemma R2c_st'_eq_st:
  "R2c($st\<acute> =\<^sub>u $st) = ($st\<acute> =\<^sub>u $st)"
  by (rel_auto)

lemma R1_des_lift_skip: "R1(\<lceil>II\<rceil>\<^sub>D) = \<lceil>II\<rceil>\<^sub>D"
  by (rel_auto)

lemma R2_des_lift_skip:
  "R2(\<lceil>II\<rceil>\<^sub>D) = \<lceil>II\<rceil>\<^sub>D"
  apply (rel_auto) using minus_zero_eq by blast

lemma R1_R2c_ex_st: "R1 (R2c (\<exists> $st\<acute> \<bullet> Q\<^sub>1)) = (\<exists> $st\<acute> \<bullet> R1 (R2c Q\<^sub>1))"
  by (rel_auto)

subsection \<open> Identities \<close>

text \<open> We define two identities fro reactive designs, which correspond to the regular and 
  state-sensitive versions of reactive designs, respectively. The former is the one used in
  the UTP book and related publications for CSP. \<close>

definition skip_rea :: "('t::trace, '\<alpha>) hrel_rp" ("II\<^sub>c") where
skip_rea_def [urel_defs]: "II\<^sub>c = (II \<or> (\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>))"

definition skip_srea :: "('s, 't::trace, '\<alpha>) hrel_rsp" ("II\<^sub>R") where
skip_srea_def [urel_defs]: "II\<^sub>R = ((\<exists> $st \<bullet> II\<^sub>c) \<triangleleft> $wait \<triangleright> II\<^sub>c)"

lemma skip_rea_R1_lemma: "II\<^sub>c = R1($ok \<Rightarrow> II)"
  by (rel_auto)

lemma skip_rea_form: "II\<^sub>c = (II \<triangleleft> $ok \<triangleright> R1(true))"
  by (rel_auto)

lemma skip_srea_form: "II\<^sub>R = ((\<exists> $st \<bullet> II) \<triangleleft> $wait \<triangleright> II) \<triangleleft> $ok \<triangleright> R1(true)"
  by (rel_auto)

lemma R1_skip_rea: "R1(II\<^sub>c) = II\<^sub>c"
  by (rel_auto)

lemma R2c_skip_rea: "R2c II\<^sub>c = II\<^sub>c"
  by (simp add: skip_rea_def R2c_and R2c_disj R2c_skip_r R2c_not R2c_ok R2c_tr'_ge_tr)

lemma R2_skip_rea: "R2(II\<^sub>c) = II\<^sub>c"
  by (metis R1_R2c_is_R2 R1_skip_rea R2c_skip_rea)

lemma R2c_skip_srea: "R2c(II\<^sub>R) = II\<^sub>R"
  apply (rel_auto) using minus_zero_eq by blast+

lemma skip_srea_R1 [closure]: "II\<^sub>R is R1"
  by (rel_auto)

lemma skip_srea_R2c [closure]: "II\<^sub>R is R2c"
  by (simp add: Healthy_def R2c_skip_srea)

lemma skip_srea_R2 [closure]: "II\<^sub>R is R2"
  by (metis Healthy_def' R1_R2c_is_R2 R2c_skip_srea skip_srea_R1)

subsection \<open> RD1: Divergence yields arbitrary traces \<close>

definition RD1 :: "('t::trace,'\<alpha>,'\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" where
[upred_defs]: "RD1(P) = (P \<or> (\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>))"

text \<open> $RD1$ is essentially $H1$ from the theory of designs, but viewed through the prism of
  reactive processes. \<close>

lemma RD1_idem: "RD1(RD1(P)) = RD1(P)"
  by (rel_auto)

lemma RD1_Idempotent: "Idempotent RD1"
  by (simp add: Idempotent_def RD1_idem)

lemma RD1_mono: "P \<sqsubseteq> Q \<Longrightarrow> RD1(P) \<sqsubseteq> RD1(Q)"
  by (rel_auto)

lemma RD1_Monotonic: "Monotonic RD1"
  using mono_def RD1_mono by blast

lemma RD1_Continuous: "Continuous RD1"
  by (rel_auto)

lemma R1_true_RD1_closed [closure]: "R1(true) is RD1"
  by (rel_auto)

lemma RD1_wait_false [closure]: "P is RD1 \<Longrightarrow> P\<lbrakk>false/$wait\<rbrakk> is RD1"
  by (rel_auto)

lemma RD1_wait'_false [closure]: "P is RD1 \<Longrightarrow> P\<lbrakk>false/$wait\<acute>\<rbrakk> is RD1"
  by (rel_auto)
    
lemma RD1_seq: "RD1(RD1(P) ;; RD1(Q)) = RD1(P) ;; RD1(Q)"
  by (rel_auto)

lemma RD1_seq_closure [closure]: "\<lbrakk> P is RD1; Q is RD1 \<rbrakk> \<Longrightarrow> P ;; Q is RD1"
  by (metis Healthy_def' RD1_seq)

lemma RD1_R1_commute: "RD1(R1(P)) = R1(RD1(P))"
  by (rel_auto)

lemma RD1_R2c_commute: "RD1(R2c(P)) = R2c(RD1(P))"
  by (rel_auto)

lemma RD1_via_R1: "R1(H1(P)) = RD1(R1(P))"
  by (rel_auto)

lemma RD1_R1_cases: "RD1(R1(P)) = (R1(P) \<triangleleft> $ok \<triangleright> R1(true))"
  by (rel_auto)

lemma skip_rea_RD1_skip: "II\<^sub>c = RD1(II)"
  by (rel_auto)

lemma skip_srea_RD1 [closure]: "II\<^sub>R is RD1"
  by (rel_auto)

lemma RD1_algebraic_intro:
  assumes
    "P is R1" "(R1(true\<^sub>h) ;; P) = R1(true\<^sub>h)" "(II\<^sub>c ;; P) = P"
  shows "P is RD1"
proof -
  have "P = (II\<^sub>c ;; P)"
    by (simp add: assms(3))
  also have "... = (R1($ok \<Rightarrow> II) ;; P)"
    by (simp add: skip_rea_R1_lemma)
  also have "... = (((\<not> $ok \<and> R1(true)) ;; P) \<or> P)"
    by (metis (no_types, lifting) R1_def seqr_left_unit seqr_or_distl skip_rea_R1_lemma skip_rea_def utp_pred_laws.inf_top_left utp_pred_laws.sup_commute)
  also have "... = ((R1(\<not> $ok) ;; (R1(true\<^sub>h) ;; P)) \<or> P)"
    using dual_order.trans by (rel_blast)
  also have "... = ((R1(\<not> $ok) ;; R1(true\<^sub>h)) \<or> P)"
    by (simp add: assms(2))
  also have "... = (R1(\<not> $ok) \<or> P)"
    by (rel_auto)
  also have "... = RD1(P)"
    by (rel_auto)
  finally show ?thesis
    by (simp add: Healthy_def)
qed

theorem RD1_left_zero:
  assumes "P is R1" "P is RD1"
  shows "(R1(true) ;; P) = R1(true)"
proof -
  have "(R1(true) ;; R1(RD1(P))) = R1(true)"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms(1) assms(2))
qed

theorem RD1_left_unit:
  assumes "P is R1" "P is RD1"
  shows "(II\<^sub>c ;; P) = P"
proof -
  have "(II\<^sub>c ;; R1(RD1(P))) = R1(RD1(P))"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms(1) assms(2))
qed

lemma RD1_alt_def:
  assumes "P is R1"
  shows "RD1(P) = (P \<triangleleft> $ok \<triangleright> R1(true))"
proof -
  have "RD1(R1(P)) = (R1(P) \<triangleleft> $ok \<triangleright> R1(true))"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

theorem RD1_algebraic:
  assumes "P is R1"
  shows "P is RD1 \<longleftrightarrow> (R1(true\<^sub>h) ;; P) = R1(true\<^sub>h) \<and> (II\<^sub>c ;; P) = P"
  using RD1_algebraic_intro RD1_left_unit RD1_left_zero assms by blast

subsection \<open> R3c and R3h: Reactive design versions of R3 \<close>

definition R3c :: "('t::trace, '\<alpha>) hrel_rp \<Rightarrow> ('t, '\<alpha>) hrel_rp" where
[upred_defs]: "R3c(P) = (II\<^sub>c \<triangleleft> $wait \<triangleright> P)"

definition R3h :: "('s, 't::trace, '\<alpha>) hrel_rsp \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp" where
 R3h_def [upred_defs]: "R3h(P) = ((\<exists> $st \<bullet> II\<^sub>c) \<triangleleft> $wait \<triangleright> P)"

lemma R3c_idem: "R3c(R3c(P)) = R3c(P)"
  by (rel_auto)

lemma R3c_Idempotent: "Idempotent R3c"
  by (simp add: Idempotent_def R3c_idem)

lemma R3c_mono: "P \<sqsubseteq> Q \<Longrightarrow> R3c(P) \<sqsubseteq> R3c(Q)"
  by (rel_auto)

lemma R3c_Monotonic: "Monotonic R3c"
  by (simp add: mono_def R3c_mono)

lemma R3c_Continuous: "Continuous R3c"
  by (rel_auto)

lemma R3h_idem: "R3h(R3h(P)) = R3h(P)"
  by (rel_auto)

lemma R3h_Idempotent: "Idempotent R3h"
  by (simp add: Idempotent_def R3h_idem)

lemma R3h_mono: "P \<sqsubseteq> Q \<Longrightarrow> R3h(P) \<sqsubseteq> R3h(Q)"
  by (rel_auto)

lemma R3h_Monotonic: "Monotonic R3h"
  by (simp add: mono_def R3h_mono)

lemma R3h_Continuous: "Continuous R3h"
  by (rel_auto)

lemma R3h_inf: "R3h(P \<sqinter> Q) = R3h(P) \<sqinter> R3h(Q)"
  by (rel_auto)

lemma R3h_UINF:
  "A \<noteq> {} \<Longrightarrow> R3h(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> R3h(P(i)))"
  by (rel_auto)

lemma R3h_cond: "R3h(P \<triangleleft> b \<triangleright> Q) = (R3h(P) \<triangleleft> b \<triangleright> R3h(Q))"
  by (rel_auto)

lemma R3c_via_RD1_R3: "RD1(R3(P)) = R3c(RD1(P))"
  by (rel_auto)

lemma R3c_RD1_def: "P is RD1 \<Longrightarrow> R3c(P) = RD1(R3(P))"
  by (simp add: Healthy_if R3c_via_RD1_R3)

lemma RD1_R3c_commute: "RD1(R3c(P)) = R3c(RD1(P))"
  by (rel_auto)

lemma R1_R3c_commute: "R1(R3c(P)) = R3c(R1(P))"
  by (rel_auto)

lemma R2c_R3c_commute: "R2c(R3c(P)) = R3c(R2c(P))"
  apply (rel_auto) using minus_zero_eq by blast+

lemma R1_R3h_commute: "R1(R3h(P)) = R3h(R1(P))"
  by (rel_auto)

lemma R2c_R3h_commute: "R2c(R3h(P)) = R3h(R2c(P))"
  apply (rel_auto) using minus_zero_eq by blast+

lemma RD1_R3h_commute: "RD1(R3h(P)) = R3h(RD1(P))"
  by (rel_auto)

lemma R3c_cancels_R3: "R3c(R3(P)) = R3c(P)"
  by (rel_auto)

lemma R3_cancels_R3c: "R3(R3c(P)) = R3(P)"
  by (rel_auto)

lemma R3h_cancels_R3c: "R3h(R3c(P)) = R3h(P)"
  by (rel_auto)

lemma R3c_semir_form:
  "(R3c(P) ;; R3c(R1(Q))) = R3c(P ;; R3c(R1(Q)))"
  by (rel_simp, safe, auto intro: order_trans)

lemma R3h_semir_form:
  "(R3h(P) ;; R3h(R1(Q))) = R3h(P ;; R3h(R1(Q)))"
  by (rel_simp, safe, auto intro: order_trans, blast+)

lemma R3c_seq_closure:
  assumes "P is R3c" "Q is R3c" "Q is R1"
  shows "(P ;; Q) is R3c"
  by (metis Healthy_def' R3c_semir_form assms)

lemma R3h_seq_closure [closure]:
  assumes "P is R3h" "Q is R3h" "Q is R1"
  shows "(P ;; Q) is R3h"
  by (metis Healthy_def' R3h_semir_form assms)

lemma R3c_R3_left_seq_closure:
  assumes "P is R3" "Q is R3c"
  shows "(P ;; Q) is R3c"
proof -
  have "(P ;; Q) = ((P ;; Q)\<lbrakk>true/$wait\<rbrakk> \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (metis cond_var_split cond_var_subst_right in_var_uvar wait_vwb_lens)
  also have "... = (((II \<triangleleft> $wait \<triangleright> P) ;; Q)\<lbrakk>true/$wait\<rbrakk> \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (metis Healthy_def' R3_def assms(1))
  also have "... = ((II\<lbrakk>true/$wait\<rbrakk> ;; Q) \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (subst_tac)
  also have "... = (((II \<and> $wait\<acute>) ;; Q) \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (metis (no_types, lifting) cond_def conj_pos_var_subst seqr_pre_var_out skip_var utp_pred_laws.inf_left_idem wait_vwb_lens)
  also have "... = ((II\<lbrakk>true/$wait\<acute>\<rbrakk> ;; Q\<lbrakk>true/$wait\<rbrakk>) \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (metis seqr_pre_transfer seqr_right_one_point true_alt_def uovar_convr upred_eq_true utp_rel.unrest_ouvar vwb_lens_mwb wait_vwb_lens)
  also have "... = ((II\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (II\<^sub>c \<triangleleft> $wait \<triangleright> Q)\<lbrakk>true/$wait\<rbrakk>) \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (metis Healthy_def' R3c_def assms(2))
  also have "... = ((II\<lbrakk>true/$wait\<acute>\<rbrakk> ;; II\<^sub>c\<lbrakk>true/$wait\<rbrakk>) \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (subst_tac)
  also have "... = (((II \<and> $wait\<acute>) ;; II\<^sub>c) \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (metis seqr_pre_transfer seqr_right_one_point true_alt_def uovar_convr upred_eq_true utp_rel.unrest_ouvar vwb_lens_mwb wait_vwb_lens)
  also have "... = ((II ;; II\<^sub>c) \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (simp add: cond_def seqr_pre_transfer utp_rel.unrest_ouvar)
  also have "... = (II\<^sub>c \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by simp
  also have "... = R3c(P ;; Q)"
    by (simp add: R3c_def)
  finally show ?thesis
    by (simp add: Healthy_def')
qed

lemma R3c_cases: "R3c(P) = ((II \<triangleleft> $ok \<triangleright> R1(true)) \<triangleleft> $wait \<triangleright> P)"
  by (rel_auto)

lemma R3h_cases: "R3h(P) = (((\<exists> $st \<bullet> II) \<triangleleft> $ok \<triangleright> R1(true)) \<triangleleft> $wait \<triangleright> P)"
  by (rel_auto)

lemma R3h_form: "R3h(P) = II\<^sub>R \<triangleleft> $wait \<triangleright> P"
  by (rel_auto)

lemma R3c_subst_wait: "R3c(P) = R3c(P \<^sub>f)"
  by (simp add: R3c_def cond_var_subst_right)

lemma R3h_subst_wait: "R3h(P) = R3h(P \<^sub>f)"
  by (simp add: R3h_cases cond_var_subst_right)

lemma skip_srea_R3h [closure]: "II\<^sub>R is R3h"
  by (rel_auto)

lemma R3h_wait_true:
  assumes "P is R3h"
  shows "P \<^sub>t = II\<^sub>R \<^sub>t"
proof -
  have "P \<^sub>t = (II\<^sub>R \<triangleleft> $wait \<triangleright> P) \<^sub>t"
    by (metis Healthy_if R3h_form assms)
  also have "... = II\<^sub>R \<^sub>t"
    by (simp add: usubst)
  finally show ?thesis .
qed

subsection \<open> RD2: A reactive specification cannot require non-termination \<close>

definition RD2 where
[upred_defs]: "RD2(P) = H2(P)"
  
text \<open> $RD2$ is just $H2$ since the type system will automatically have J identifying 
  the reactive variables as required. \<close>

lemma RD2_idem: "RD2(RD2(P)) = RD2(P)"
  by (simp add: H2_idem RD2_def)

lemma RD2_Idempotent: "Idempotent RD2"
  by (simp add: Idempotent_def RD2_idem)

lemma RD2_mono: "P \<sqsubseteq> Q \<Longrightarrow> RD2(P) \<sqsubseteq> RD2(Q)"
  by (simp add: H2_def RD2_def seqr_mono)

lemma RD2_Monotonic: "Monotonic RD2"
  using mono_def RD2_mono by blast

lemma RD2_Continuous: "Continuous RD2"
  by (rel_auto)

lemma RD1_RD2_commute: "RD1(RD2(P)) = RD2(RD1(P))"
  by (rel_auto)

lemma RD2_R3c_commute: "RD2(R3c(P)) = R3c(RD2(P))"
  by (rel_auto)

lemma RD2_R3h_commute: "RD2(R3h(P)) = R3h(RD2(P))"
  by (rel_auto)

subsection \<open> Major healthiness conditions \<close>

definition RH :: "('t::trace,'\<alpha>) hrel_rp \<Rightarrow> ('t,'\<alpha>) hrel_rp" ("\<^bold>R")
where [upred_defs]: "RH(P) = R1(R2c(R3c(P)))"

definition RHS :: "('s,'t::trace,'\<alpha>) hrel_rsp \<Rightarrow> ('s,'t,'\<alpha>) hrel_rsp" ("\<^bold>R\<^sub>s")
where [upred_defs]: "RHS(P) = R1(R2c(R3h(P)))"

definition RD :: "('t::trace,'\<alpha>) hrel_rp \<Rightarrow> ('t,'\<alpha>) hrel_rp"
where [upred_defs]: "RD(P) = RD1(RD2(RP(P)))"

definition SRD :: "('s,'t::trace,'\<alpha>) hrel_rsp \<Rightarrow> ('s,'t,'\<alpha>) hrel_rsp"
where [upred_defs]: "SRD(P) = RD1(RD2(RHS(P)))"

lemma RH_comp: "RH = R1 \<circ> R2c \<circ> R3c"
  by (auto simp add: RH_def)

lemma RHS_comp: "RHS = R1 \<circ> R2c \<circ> R3h"
  by (auto simp add: RHS_def)

lemma RD_comp: "RD = RD1 \<circ> RD2 \<circ> RP"
  by (auto simp add: RD_def)

lemma SRD_comp: "SRD = RD1 \<circ> RD2 \<circ> RHS"
  by (auto simp add: SRD_def)

lemma RH_idem: "\<^bold>R(\<^bold>R(P)) = \<^bold>R(P)"
  by (simp add: R1_R2c_commute R1_R3c_commute R1_idem R2c_R3c_commute R2c_idem R3c_idem RH_def)

lemma RH_Idempotent: "Idempotent \<^bold>R"
  by (simp add: Idempotent_def RH_idem)

lemma RH_Monotonic: "Monotonic \<^bold>R"
  by (metis (no_types, lifting) R1_Monotonic R2c_Monotonic R3c_mono RH_def mono_def)

lemma RH_Continuous: "Continuous \<^bold>R"
  by (simp add: Continuous_comp R1_Continuous R2c_Continuous R3c_Continuous RH_comp)

lemma RHS_idem: "\<^bold>R\<^sub>s(\<^bold>R\<^sub>s(P)) = \<^bold>R\<^sub>s(P)"
  by (simp add: R1_R2c_is_R2 R1_R3h_commute R2_idem R2c_R3h_commute R3h_idem RHS_def)

lemma RHS_Idempotent [closure]: "Idempotent \<^bold>R\<^sub>s"
  by (simp add: Idempotent_def RHS_idem)

lemma RHS_Monotonic: "Monotonic \<^bold>R\<^sub>s"
  by (simp add: mono_def R1_R2c_is_R2 R2_mono R3h_mono RHS_def)

lemma RHS_mono: "P \<sqsubseteq> Q \<Longrightarrow> \<^bold>R\<^sub>s(P) \<sqsubseteq> \<^bold>R\<^sub>s(Q)"
  using mono_def RHS_Monotonic by blast

lemma RHS_Continuous [closure]: "Continuous \<^bold>R\<^sub>s"
  by (simp add: Continuous_comp R1_Continuous R2c_Continuous R3h_Continuous RHS_comp)

lemma RHS_inf: "\<^bold>R\<^sub>s(P \<sqinter> Q) = \<^bold>R\<^sub>s(P) \<sqinter> \<^bold>R\<^sub>s(Q)"
  using Continuous_Disjunctous Disjunctuous_def RHS_Continuous by auto

lemma RHS_INF:
  "A \<noteq> {} \<Longrightarrow> \<^bold>R\<^sub>s(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> \<^bold>R\<^sub>s(P(i)))"
  by (simp add: RHS_def R3h_UINF R2c_USUP R1_USUP)

lemma RHS_sup: "\<^bold>R\<^sub>s(P \<squnion> Q) = \<^bold>R\<^sub>s(P) \<squnion> \<^bold>R\<^sub>s(Q)"
  by (rel_auto)

lemma RHS_SUP: 
  "A \<noteq> {} \<Longrightarrow> \<^bold>R\<^sub>s(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> \<^bold>R\<^sub>s(P(i)))"
  by (rel_auto)
    
lemma RHS_cond: "\<^bold>R\<^sub>s(P \<triangleleft> b \<triangleright> Q) = (\<^bold>R\<^sub>s(P) \<triangleleft> R2c b \<triangleright> \<^bold>R\<^sub>s(Q))"
  by (simp add: RHS_def R3h_cond R2c_condr R1_cond)

lemma RD_alt_def: "RD(P) = RD1(RD2(\<^bold>R(P)))"
  by (simp add: R3c_via_RD1_R3 RD1_R1_commute RD1_R2c_commute RD1_R3c_commute RD1_RD2_commute RH_def RD_def RP_def)

lemma RD1_RH_commute: "RD1(\<^bold>R(P)) = \<^bold>R(RD1(P))"
  by (simp add: RD1_R1_commute RD1_R2c_commute RD1_R3c_commute RH_def)

lemma RD2_RH_commute: "RD2(\<^bold>R(P)) = \<^bold>R(RD2(P))"
  by (metis R1_H2_commute R2c_H2_commute RD2_R3c_commute RD2_def RH_def)

lemma RD_idem: "RD(RD(P)) = RD(P)"
  by (simp add: RD_alt_def RD1_RH_commute RD2_RH_commute RD1_RD2_commute RD2_idem RD1_idem RH_idem)

lemma RD_Monotonic: "Monotonic RD"
  by (simp add: Monotonic_comp RD1_Monotonic RD2_Monotonic RD_comp RP_Monotonic)

lemma RD_Continuous: "Continuous RD"
  by (simp add: Continuous_comp RD1_Continuous RD2_Continuous RD_comp RP_Continuous)

lemma R3_RD_RP: "R3(RD(P)) = RP(RD1(RD2(P)))"
  by (metis (no_types, lifting) R1_R2c_is_R2 R2_R3_commute R3_cancels_R3c RD1_RH_commute RD2_RH_commute RD_alt_def RH_def RP_def)

lemma RD1_RHS_commute: "RD1(\<^bold>R\<^sub>s(P)) = \<^bold>R\<^sub>s(RD1(P))"
  by (simp add: RD1_R1_commute RD1_R2c_commute RD1_R3h_commute RHS_def)

lemma RD2_RHS_commute: "RD2(\<^bold>R\<^sub>s(P)) = \<^bold>R\<^sub>s(RD2(P))"
  by (metis R1_H2_commute R2c_H2_commute RD2_R3h_commute RD2_def RHS_def)

lemma SRD_idem: "SRD(SRD(P)) = SRD(P)"
  by (simp add: RD1_RD2_commute RD1_RHS_commute RD1_idem RD2_RHS_commute RD2_idem RHS_idem SRD_def)

lemma SRD_Idempotent [closure]: "Idempotent SRD"
  by (simp add: Idempotent_def SRD_idem)

lemma SRD_Monotonic: "Monotonic SRD"
  by (simp add: Monotonic_comp RD1_Monotonic RD2_Monotonic RHS_Monotonic SRD_comp)

lemma SRD_Continuous [closure]: "Continuous SRD"
  by (simp add: Continuous_comp RD1_Continuous RD2_Continuous RHS_Continuous SRD_comp)

lemma SRD_RHS_H1_H2: "SRD(P) = \<^bold>R\<^sub>s(\<^bold>H(P))"
  by (rel_auto)

lemma SRD_healths:
  assumes "P is SRD"
  shows "P is R1" "P is R2" "P is R3h" "P is RD1" "P is RD2"
  apply (metis Healthy_def R1_idem RD1_RHS_commute RD2_RHS_commute RHS_def SRD_def assms)
  apply (metis Healthy_def R1_R2c_is_R2 R2_idem RD1_RHS_commute RD2_RHS_commute RHS_def SRD_def assms)
  apply (metis Healthy_def R1_R3h_commute R2c_R3h_commute R3h_idem RD1_R3h_commute RD2_R3h_commute RHS_def SRD_def assms)
  apply (metis Healthy_def' RD1_idem SRD_def assms)
  apply (metis Healthy_def' RD1_RD2_commute RD2_idem SRD_def assms)
done

lemma SRD_intro:
  assumes "P is R1" "P is R2" "P is R3h" "P is RD1" "P is RD2"
  shows "P is SRD"
  by (metis Healthy_def R1_R2c_is_R2 RHS_def SRD_def assms(2) assms(3) assms(4) assms(5))

lemma SRD_ok_false [usubst]: "P is SRD \<Longrightarrow> P\<lbrakk>false/$ok\<rbrakk> = R1(true)"
  by (metis (no_types, hide_lams) H1_H2_eq_design Healthy_def R1_ok_false RD1_R1_commute RD1_via_R1 RD2_def SRD_def SRD_healths(1) design_ok_false)

lemma SRD_ok_true_wait_true [usubst]:
  assumes "P is SRD"
  shows "P\<lbrakk>true,true/$ok,$wait\<rbrakk> = (\<exists> $st \<bullet> II)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
proof -
  have "P = (\<exists> $st \<bullet> II) \<triangleleft> $ok \<triangleright> R1 true \<triangleleft> $wait \<triangleright> P"
    by (metis Healthy_def R3h_cases SRD_healths(3) assms)
  moreover have "((\<exists> $st \<bullet> II) \<triangleleft> $ok \<triangleright> R1 true \<triangleleft> $wait \<triangleright> P)\<lbrakk>true,true/$ok,$wait\<rbrakk> = (\<exists> $st \<bullet> II)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
    by (simp add: usubst)
  ultimately show ?thesis
    by (simp)
qed

lemma SRD_left_zero_1: "P is SRD \<Longrightarrow> R1(true) ;; P = R1(true)"
  by (simp add: RD1_left_zero SRD_healths(1) SRD_healths(4))

lemma SRD_left_zero_2:
  assumes "P is SRD"
  shows "(\<exists> $st \<bullet> II)\<lbrakk>true,true/$ok,$wait\<rbrakk> ;; P = (\<exists> $st \<bullet> II)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
proof -
  have "(\<exists> $st \<bullet> II)\<lbrakk>true,true/$ok,$wait\<rbrakk> ;; R3h(P) = (\<exists> $st \<bullet> II)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if SRD_healths(3) assms)
qed

subsection \<open> UTP theories \<close>

text \<open> We create two theory objects: one for reactive designs and one for stateful reactive
        designs. \<close>

typedecl RDES
typedecl SRDES

abbreviation "RDES \<equiv> UTHY(RDES, ('t::trace,'\<alpha>) rp)"
abbreviation "SRDES \<equiv> UTHY(SRDES, ('s,'t::trace,'\<alpha>) rsp)"

overloading
  rdes_hcond   == "utp_hcond :: (RDES, ('t::trace,'\<alpha>) rp) uthy \<Rightarrow> (('t,'\<alpha>) rp \<times> ('t,'\<alpha>) rp) health"
  srdes_hcond   == "utp_hcond :: (SRDES, ('s,'t::trace,'\<alpha>) rsp) uthy \<Rightarrow> (('s,'t,'\<alpha>) rsp \<times> ('s,'t,'\<alpha>) rsp) health"
begin
  definition rdes_hcond :: "(RDES, ('t::trace,'\<alpha>) rp) uthy \<Rightarrow> (('t,'\<alpha>) rp \<times> ('t,'\<alpha>) rp) health" where
  [upred_defs]: "rdes_hcond T = RD"
  definition srdes_hcond :: "(SRDES, ('s,'t::trace,'\<alpha>) rsp) uthy \<Rightarrow> (('s,'t,'\<alpha>) rsp \<times> ('s,'t,'\<alpha>) rsp) health" where
  [upred_defs]: "srdes_hcond T = SRD"
end

interpretation rdes_theory: utp_theory "UTHY(RDES, ('t::trace,'\<alpha>) rp)"
  by (unfold_locales, simp_all add: rdes_hcond_def RD_idem)

interpretation rdes_theory_continuous: utp_theory_continuous "UTHY(RDES, ('t::trace,'\<alpha>) rp)"
  rewrites "\<And> P. P \<in> carrier (uthy_order RDES) \<longleftrightarrow> P is RD"
  and "carrier (uthy_order RDES) \<rightarrow> carrier (uthy_order RDES) \<equiv> \<lbrakk>RD\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>RD\<rbrakk>\<^sub>H"
  and "le (uthy_order RDES) = op \<sqsubseteq>"
  and "eq (uthy_order RDES) = op ="
  by (unfold_locales, simp_all add: rdes_hcond_def RD_Continuous)

interpretation rdes_rea_galois:
  galois_connection "(RDES \<leftarrow>\<langle>RD1 \<circ> RD2,R3\<rangle>\<rightarrow> REA)"
proof (simp add: mk_conn_def, rule galois_connectionI', simp_all add: utp_partial_order rdes_hcond_def rea_hcond_def)
  show "R3 \<in> \<lbrakk>RD\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>RP\<rbrakk>\<^sub>H"
    by (metis (no_types, lifting) Healthy_def' Pi_I R3_RD_RP RP_idem mem_Collect_eq)
  show "RD1 \<circ> RD2 \<in> \<lbrakk>RP\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>RD\<rbrakk>\<^sub>H"
    by (simp add: Pi_iff Healthy_def, metis RD_def RD_idem)
  show "isotone (utp_order RD) (utp_order RP) R3"
    by (simp add: R3_Monotonic isotone_utp_orderI)
  show "isotone (utp_order RP) (utp_order RD) (RD1 \<circ> RD2)"
    by (simp add: Monotonic_comp RD1_Monotonic RD2_Monotonic isotone_utp_orderI)
  fix P :: "('a, 'b) hrel_rp"
  assume "P is RD"
  thus "P \<sqsubseteq> RD1 (RD2 (R3 P))"
    by (metis Healthy_if R3_RD_RP RD_def RP_idem eq_iff)
next
  fix P :: "('a, 'b) hrel_rp"
  assume a: "P is RP"
  thus "R3 (RD1 (RD2 P)) \<sqsubseteq> P"
  proof -
    have "R3 (RD1 (RD2 P)) = RP (RD1 (RD2(P)))"
      by (metis Healthy_if R3_RD_RP RD_def a)
    moreover have "RD1(RD2(P)) \<sqsubseteq> P"
      by (rel_auto)
    ultimately show ?thesis
      by (metis Healthy_if RP_mono a)
  qed
qed

interpretation rdes_rea_retract:
  retract "(RDES \<leftarrow>\<langle>RD1 \<circ> RD2,R3\<rangle>\<rightarrow> REA)"
  by (unfold_locales, simp_all add: mk_conn_def utp_partial_order rdes_hcond_def rea_hcond_def)
     (metis Healthy_if R3_RD_RP RD_def RP_idem eq_refl)

interpretation srdes_theory: utp_theory "UTHY(SRDES, ('s,'t::trace,'\<alpha>) rsp)"
  by (unfold_locales, simp_all add: srdes_hcond_def SRD_idem)

interpretation srdes_theory_continuous: utp_theory_continuous "UTHY(SRDES, ('s,'t::trace,'\<alpha>) rsp)"
  rewrites "\<And> P. P \<in> carrier (uthy_order SRDES) \<longleftrightarrow> P is SRD"
  and "P is \<H>\<^bsub>SRDES\<^esub> \<longleftrightarrow> P is SRD"
  and "carrier (uthy_order SRDES) \<rightarrow> carrier (uthy_order SRDES) \<equiv> \<lbrakk>SRD\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  and "\<lbrakk>\<H>\<^bsub>SRDES\<^esub>\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<H>\<^bsub>SRDES\<^esub>\<rbrakk>\<^sub>H \<equiv> \<lbrakk>SRD\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  and "le (uthy_order SRDES) = op \<sqsubseteq>"
  and "eq (uthy_order SRDES) = op ="
  by (unfold_locales, simp_all add: srdes_hcond_def SRD_Continuous)

declare srdes_theory_continuous.top_healthy [simp del]
declare srdes_theory_continuous.bottom_healthy [simp del]

abbreviation Chaos :: "('s,'t::trace,'\<alpha>) hrel_rsp" where
"Chaos \<equiv> \<^bold>\<bottom>\<^bsub>SRDES\<^esub>"

abbreviation Miracle :: "('s,'t::trace,'\<alpha>) hrel_rsp" where
"Miracle \<equiv> \<^bold>\<top>\<^bsub>SRDES\<^esub>"

thm srdes_theory_continuous.weak.bottom_lower
thm srdes_theory_continuous.weak.top_higher
thm srdes_theory_continuous.meet_bottom
thm srdes_theory_continuous.meet_top

abbreviation srd_lfp ("\<mu>\<^sub>R") where "\<mu>\<^sub>R F \<equiv> \<^bold>\<mu>\<^bsub>SRDES\<^esub> F"

abbreviation srd_gfp ("\<nu>\<^sub>R") where "\<nu>\<^sub>R F \<equiv> \<^bold>\<nu>\<^bsub>SRDES\<^esub> F"

syntax
  "_srd_mu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<mu>\<^sub>R _ \<bullet> _" [0, 10] 10)
  "_srd_nu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<nu>\<^sub>R _ \<bullet> _" [0, 10] 10)

translations
  "\<mu>\<^sub>R X \<bullet> P" == "\<^bold>\<mu>\<^bsub>CONST SRDES\<^esub> (\<lambda> X. P)"
  "\<nu>\<^sub>R X \<bullet> P" == "\<^bold>\<nu>\<^bsub>CONST SRDES\<^esub> (\<lambda> X. P)"

text \<open> The reactive design weakest fixed-point can be defined in terms of relational calculus one. \<close>

lemma srd_mu_equiv:
  assumes "Monotonic F" "F \<in> \<lbrakk>SRD\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  shows "(\<mu>\<^sub>R X \<bullet> F(X)) = (\<mu> X \<bullet> F(SRD(X)))"
  by (metis assms srdes_hcond_def srdes_theory_continuous.utp_lfp_def)

end