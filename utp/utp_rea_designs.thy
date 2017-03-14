section {* Reactive designs *}

theory utp_rea_designs
  imports utp_reactive
begin

subsection {* Preliminaries *}

text {* R3 as presented in the UTP book and related publications is not sensitive to state, although
  reactive designs often need this property. Thus is is necessary to use a modification of R3
  from Butterfield et al. (2009) that explicitly states that intermediate
  waiting states do not propogate final state variables. In order to do this we need an additional
  observational variable that capture the program state that we call $st$. *}

alphabet 's rsp_vars = "'t rp_vars" +
  st :: 's

type_synonym ('s,'t,'\<alpha>) rsp = "('t, ('s, '\<alpha>) rsp_vars_scheme) rp"
type_synonym ('s,'t,'\<alpha>,'\<beta>) rel_rsp  = "(('s,'t,'\<alpha>) rsp, ('s,'t,'\<beta>) rsp) rel"
type_synonym ('s,'t,'\<alpha>) hrel_rsp  = "('s,'t,'\<alpha>) rsp hrel"

translations
  (type) "('s,'t,'\<alpha>) rsp" <= (type) "(_,('s,'t,'\<alpha>) rsp_vars_ext) rp"
  (type) "('s,'t,'\<alpha>) rsp" <= (type) "('t, ('s, '\<alpha>) rsp_vars_scheme) rp_vars_ext des"
  (type) "('s,'t,'\<alpha>,'\<beta>) rel_rp" <= (type) "(('s,'t,'\<alpha>) rsp, (_,_,'\<beta>) rsp) rel"

notation rsp_vars_child_lens\<^sub>a ("\<Sigma>\<^sub>s")
notation rsp_vars_child_lens ("\<Sigma>\<^sub>S")

abbreviation lift_state_rel ("\<lceil>_\<rceil>\<^sub>S")
where "\<lceil>P\<rceil>\<^sub>S \<equiv> P \<oplus>\<^sub>p (st \<times>\<^sub>L st)"

abbreviation lift_state_pre ("\<lceil>_\<rceil>\<^sub>S\<^sub><")
where "\<lceil>p\<rceil>\<^sub>S\<^sub>< \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub><\<rceil>\<^sub>S"

interpretation alphabet_state:
  lens_interp "\<lambda>(ok, wait, tr, r). (ok, wait, tr, st\<^sub>v r, more r)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation alphabet_state_rel: lens_interp "\<lambda>(ok, ok', wait, wait', tr, tr', r, r').
  (ok, ok', wait, wait', tr, tr', st\<^sub>v r, st\<^sub>v r', more r, more r')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

lemma st'_unrest_st_lift_pred [unrest]:
  "$st\<acute> \<sharp> \<lceil>a\<rceil>\<^sub>S\<^sub><"
  by (pred_auto)

subsection {* Healthiness conditions *}

text {* The fundamental healthiness conditions of reactive designs are $RD1$ and $RD2$ which
  are essentially modifications of H1 and H2 from the theory of designs, viewed through
  the prism of reactive processes. *}

definition [upred_defs]: "RD1(P) = (P \<or> (\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>))"
definition [upred_defs]: "RD2(P) = H2(P)"

text {* RD2 is just H2 since the type system will automatically have J identifying the reactive
        variables as required. *}

lemma RD1_idem: "RD1(RD1(P)) = RD1(P)"
  by (rel_auto)

lemma RD1_Idempotent: "Idempotent RD1"
  by (simp add: Idempotent_def RD1_idem)

lemma RD1_mono: "P \<sqsubseteq> Q \<Longrightarrow> RD1(P) \<sqsubseteq> RD1(Q)"
  by (rel_auto)

lemma RD1_Monotonic: "Monotonic RD1"
  using Monotonic_def RD1_mono by blast

lemma RD1_Continuous: "Continuous RD1"
  by (rel_auto)

lemma RD2_idem: "RD2(RD2(P)) = RD2(P)"
  by (simp add: H2_idem RD2_def)

lemma RD2_Idempotent: "Idempotent RD2"
  by (simp add: Idempotent_def RD2_idem)

lemma RD2_mono: "P \<sqsubseteq> Q \<Longrightarrow> RD2(P) \<sqsubseteq> RD2(Q)"
  by (simp add: H2_def RD2_def seqr_mono)

lemma RD2_Monotonic: "Monotonic RD2"
  using Monotonic_def RD2_mono by blast

lemma RD2_Continuous: "Continuous RD2"
  by (rel_auto)

lemma RD1_RD2_commute: "RD1(RD2(P)) = RD2(RD1(P))"
  by (rel_auto)

lemma RD1_R1_commute: "RD1(R1(P)) = R1(RD1(P))"
  by (rel_auto)

lemma RD1_R2c_commute: "RD1(R2c(P)) = R2c(RD1(P))"
  by (rel_auto)

lemma RD1_via_R1: "R1(H1(P)) = RD1(R1(P))"
  by (rel_auto)

definition skip_rea_def [urel_defs]: "II\<^sub>r = (II \<or> (\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>))"

definition skip_srea_def [urel_defs]: "II\<^sub>s = ((\<exists> $st \<bullet> II\<^sub>r) \<triangleleft> $wait \<triangleright> II\<^sub>r)"

definition R3c_def [upred_defs]: "R3c(P) = (II\<^sub>r \<triangleleft> $wait \<triangleright> P)"

definition R3h_def [upred_defs]: "R3h(P) = ((\<exists> $st \<bullet> II\<^sub>r) \<triangleleft> $wait \<triangleright> P)"

lemma R3c_idem: "R3c(R3c(P)) = R3c(P)"
  by (rel_auto)

lemma R3c_Idempotent: "Idempotent R3c"
  by (simp add: Idempotent_def R3c_idem)

lemma R3c_mono: "P \<sqsubseteq> Q \<Longrightarrow> R3c(P) \<sqsubseteq> R3c(Q)"
  by (rel_auto)

lemma R3c_Monotonic: "Monotonic R3c"
  by (simp add: Monotonic_def R3c_mono)

lemma R3c_Continuous: "Continuous R3c"
  by (rel_auto)

lemma R3h_idem: "R3h(R3h(P)) = R3h(P)"
  by (rel_auto)

lemma R3h_Idempotent: "Idempotent R3h"
  by (simp add: Idempotent_def R3h_idem)

lemma R3h_mono: "P \<sqsubseteq> Q \<Longrightarrow> R3h(P) \<sqsubseteq> R3h(Q)"
  by (rel_auto)

lemma R3h_Monotonic: "Monotonic R3h"
  by (simp add: Monotonic_def R3h_mono)

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

lemma RD2_R3c_commute: "RD2(R3c(P)) = R3c(RD2(P))"
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

lemma RD2_R3h_commute: "RD2(R3h(P)) = R3h(RD2(P))"
  by (rel_auto)

lemma R3c_cancels_R3: "R3c(R3(P)) = R3c(P)"
  by (rel_auto)

lemma R3_cancels_R3c: "R3(R3c(P)) = R3(P)"
  by (rel_auto)

lemma R3h_cancels_R3c: "R3h(R3c(P)) = R3h(P)"
  by (rel_auto)

lemma skip_rea_RD1_skip: "II\<^sub>r = RD1(II)"
  by (rel_auto)

lemma R1_skip_rea: "R1(II\<^sub>r) = II\<^sub>r"
  by (rel_auto)

lemma skip_rea_form: "II\<^sub>r = (II \<triangleleft> $ok \<triangleright> R1(true))"
  by (rel_auto)

lemma R2c_skip_rea: "R2c II\<^sub>r = II\<^sub>r"
  by (simp add: skip_rea_def R2c_and R2c_disj R2c_skip_r R2c_not R2c_ok R2c_tr'_ge_tr)

definition RH :: "('t::ordered_cancel_monoid_diff,'\<alpha>) hrel_rp \<Rightarrow> ('t,'\<alpha>) hrel_rp" ("\<^bold>R")
where [upred_defs]: "RH(P) = R1(R2c(R3c(P)))"

definition RHS :: "('s,'t::ordered_cancel_monoid_diff,'\<alpha>) hrel_rsp \<Rightarrow> ('s,'t,'\<alpha>) hrel_rsp" ("\<^bold>R\<^sub>s")
where [upred_defs]: "RHS(P) = R1(R2c(R3h(P)))"

definition RD :: "('t::ordered_cancel_monoid_diff,'\<alpha>) hrel_rp \<Rightarrow> ('t,'\<alpha>) hrel_rp"
where [upred_defs]: "RD(P) = RD1(RD2(RP(P)))"

definition SRD :: "('s,'t::ordered_cancel_monoid_diff,'\<alpha>) hrel_rsp \<Rightarrow> ('s,'t,'\<alpha>) hrel_rsp"
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
  by (metis Monotonic_def R1_Monotonic R2c_Monotonic R3c_mono RH_def)

lemma RH_Continuous: "Continuous \<^bold>R"
  by (simp add: Continuous_comp R1_Continuous R2c_Continuous R3c_Continuous RH_comp)

lemma RHS_idem: "\<^bold>R\<^sub>s(\<^bold>R\<^sub>s(P)) = \<^bold>R\<^sub>s(P)"
  by (simp add: R1_R2c_is_R2 R1_R3h_commute R2_idem R2c_R3h_commute R3h_idem RHS_def)

lemma RHS_Idempotent: "Idempotent \<^bold>R\<^sub>s"
  by (simp add: Idempotent_def RHS_idem)

lemma RHS_Monotonic: "Monotonic \<^bold>R\<^sub>s"
  by (simp add: Monotonic_def R1_R2c_is_R2 R2_mono R3h_mono RHS_def)

lemma RHS_mono: "P \<sqsubseteq> Q \<Longrightarrow> \<^bold>R\<^sub>s(P) \<sqsubseteq> \<^bold>R\<^sub>s(Q)"
  using Monotonic_def RHS_Monotonic by blast

lemma RHS_Continuous: "Continuous \<^bold>R\<^sub>s"
  by (simp add: Continuous_comp R1_Continuous R2c_Continuous R3h_Continuous RHS_comp)

lemma RHS_inf: "\<^bold>R\<^sub>s(P \<sqinter> Q) = \<^bold>R\<^sub>s(P) \<sqinter> \<^bold>R\<^sub>s(Q)"
  using Continuous_Disjunctous Disjunctuous_def RHS_Continuous by auto

lemma RHS_INF:
  "A \<noteq> {} \<Longrightarrow> \<^bold>R\<^sub>s(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> \<^bold>R\<^sub>s(P(i)))"
  by (simp add: RHS_def R3h_UINF R2c_USUP R1_USUP)

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
  by (metis Monotonic_def RD1_mono RD2_Monotonic RD_alt_def RH_Monotonic)

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

lemma SRD_Monotonic: "Monotonic SRD"
  by (metis Monotonic_def RD1_mono RD2_Monotonic RHS_Monotonic SRD_def)

lemma SRD_Continuous: "Continuous SRD"
  by (simp add: Continuous_comp RD1_Continuous RD2_Continuous RHS_Continuous SRD_comp)

typedecl RDES
typedecl SRDES

abbreviation "RDES \<equiv> UTHY(RDES, ('t::ordered_cancel_monoid_diff,'\<alpha>) rp)"
abbreviation "SRDES \<equiv> UTHY(SRDES, ('s,'t::ordered_cancel_monoid_diff,'\<alpha>) rsp)"

overloading
  rdes_hcond   == "utp_hcond :: (RDES, ('t::ordered_cancel_monoid_diff,'\<alpha>) rp) uthy \<Rightarrow> (('t,'\<alpha>) rp \<times> ('t,'\<alpha>) rp) health"
  srdes_hcond   == "utp_hcond :: (SRDES, ('s,'t::ordered_cancel_monoid_diff,'\<alpha>) rsp) uthy \<Rightarrow> (('s,'t,'\<alpha>) rsp \<times> ('s,'t,'\<alpha>) rsp) health"
begin
  definition rdes_hcond :: "(RDES, ('t::ordered_cancel_monoid_diff,'\<alpha>) rp) uthy \<Rightarrow> (('t,'\<alpha>) rp \<times> ('t,'\<alpha>) rp) health" where
  [upred_defs]: "rdes_hcond T = RD"
  definition srdes_hcond :: "(SRDES, ('s,'t::ordered_cancel_monoid_diff,'\<alpha>) rsp) uthy \<Rightarrow> (('s,'t,'\<alpha>) rsp \<times> ('s,'t,'\<alpha>) rsp) health" where
  [upred_defs]: "srdes_hcond T = SRD"

end

interpretation rdes_theory: utp_theory "UTHY(RDES, ('t::ordered_cancel_monoid_diff,'\<alpha>) rp)"
  by (unfold_locales, simp_all add: rdes_hcond_def RD_idem)

interpretation rdes_theory_continuous: utp_theory_continuous "UTHY(RDES, ('t::ordered_cancel_monoid_diff,'\<alpha>) rp)"
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

interpretation srdes_theory: utp_theory "UTHY(SRDES, ('s,'t::ordered_cancel_monoid_diff,'\<alpha>) rsp)"
  by (unfold_locales, simp_all add: srdes_hcond_def SRD_idem)

interpretation srdes_theory_continuous: utp_theory_continuous "UTHY(SRDES, ('s,'t::ordered_cancel_monoid_diff,'\<alpha>) rsp)"
  rewrites "\<And> P. P \<in> carrier (uthy_order SRDES) \<longleftrightarrow> P is SRD"
  and "P is \<H>\<^bsub>SRDES\<^esub> \<longleftrightarrow> P is SRD"
  and "carrier (uthy_order SRDES) \<rightarrow> carrier (uthy_order SRDES) \<equiv> \<lbrakk>SRD\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  and "le (uthy_order SRDES) = op \<sqsubseteq>"
  and "eq (uthy_order SRDES) = op ="
  by (unfold_locales, simp_all add: srdes_hcond_def SRD_Continuous)

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

lemma R2_skip_rea: "R2(II\<^sub>r) = II\<^sub>r"
  by (metis R1_R2c_is_R2 R1_skip_rea R2c_skip_rea)

lemma R2c_skip_rea3: "R2c(II\<^sub>s) = II\<^sub>s"
  apply (rel_auto) using minus_zero_eq by blast+

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

lemma R3h_seq_closure:
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
    by (metis (no_types, lifting) cond_def conj_pos_var_subst seqr_pre_var_out skip_var utp_pred.inf_left_idem wait_vwb_lens)
  also have "... = ((II\<lbrakk>true/$wait\<acute>\<rbrakk> ;; Q\<lbrakk>true/$wait\<rbrakk>) \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (metis seqr_pre_transfer seqr_right_one_point true_alt_def uovar_convr upred_eq_true utp_rel.unrest_ouvar vwb_lens_mwb wait_vwb_lens)
  also have "... = ((II\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (II\<^sub>r \<triangleleft> $wait \<triangleright> Q)\<lbrakk>true/$wait\<rbrakk>) \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (metis Healthy_def' R3c_def assms(2))
  also have "... = ((II\<lbrakk>true/$wait\<acute>\<rbrakk> ;; II\<^sub>r\<lbrakk>true/$wait\<rbrakk>) \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (subst_tac)
  also have "... = (((II \<and> $wait\<acute>) ;; II\<^sub>r) \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (metis seqr_pre_transfer seqr_right_one_point true_alt_def uovar_convr upred_eq_true utp_rel.unrest_ouvar vwb_lens_mwb wait_vwb_lens)
  also have "... = ((II ;; II\<^sub>r) \<triangleleft> $wait \<triangleright> (P ;; Q))"
    by (simp add: cond_def seqr_pre_transfer utp_rel.unrest_ouvar)
  also have "... = (II\<^sub>r \<triangleleft> $wait \<triangleright> (P ;; Q))"
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

lemma R3c_subst_wait: "R3c(P) = R3c(P \<^sub>f)"
  by (simp add: R3c_def cond_var_subst_right)

lemma R3h_subst_wait: "R3h(P) = R3h(P \<^sub>f)"
  by (simp add: R3h_cases cond_var_subst_right)

lemma skip_rea_R1_lemma: "II\<^sub>r = R1($ok \<Rightarrow> II)"
  by (rel_auto)

subsection {* Reactive design form *}

lemma RD1_algebraic_intro:
  assumes
    "P is R1" "(R1(true\<^sub>h) ;; P) = R1(true\<^sub>h)" "(II\<^sub>r ;; P) = P"
  shows "P is RD1"
proof -
  have "P = (II\<^sub>r ;; P)"
    by (simp add: assms(3))
  also have "... = (R1($ok \<Rightarrow> II) ;; P)"
    by (simp add: skip_rea_R1_lemma)
  also have "... = (((\<not> $ok \<and> R1(true)) ;; P) \<or> P)"
    by (metis (no_types, lifting) R1_def seqr_left_unit seqr_or_distl skip_rea_R1_lemma skip_rea_def utp_pred.inf_top_left utp_pred.sup_commute)
  also have "... = (((R1(\<not> $ok) ;; R1(true\<^sub>h)) ;; P) \<or> P)"
    by (rel_auto, metis order.trans)
  also have "... = ((R1(\<not> $ok) ;; (R1(true\<^sub>h) ;; P)) \<or> P)"
    by (simp add: seqr_assoc)
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
  shows "(II\<^sub>r ;; P) = P"
proof -
  have "(II\<^sub>r ;; R1(RD1(P))) = R1(RD1(P))"
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
  shows "P is RD1 \<longleftrightarrow> (R1(true\<^sub>h) ;; P) = R1(true\<^sub>h) \<and> (II\<^sub>r ;; P) = P"
  using RD1_algebraic_intro RD1_left_unit RD1_left_zero assms by blast

lemma RD1_reactive_design: "RD1(\<^bold>R(P \<turnstile> Q)) = \<^bold>R(P \<turnstile> Q)"
  by (rel_auto)

lemma RD2_reactive_design:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q"
  shows "RD2(\<^bold>R(P \<turnstile> Q)) = \<^bold>R(P \<turnstile> Q)"
  using assms
  by (metis H2_design RD2_RH_commute RD2_def)

lemma RD1_st_reactive_design: "RD1(\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (rel_auto)

lemma RD2_st_reactive_design:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q"
  shows "RD2(\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  using assms
  by (metis H2_design RD2_RHS_commute RD2_def)

lemma wait_false_design:
  "(P \<turnstile> Q) \<^sub>f = ((P \<^sub>f) \<turnstile> (Q \<^sub>f))"
  by (rel_auto)

lemma RD_RH_design_form:
  "RD(P) = \<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
proof -
  have "RD(P) = RD1(RD2(R1(R2c(R3c(P)))))"
    by (simp add: RD_alt_def RH_def)
  also have "... = RD1(H2(R1(R2s(R3c(P)))))"
    by (simp add: R1_R2s_R2c RD2_def)
  also have "... = RD1(R1(H2(R2s(R3c(P)))))"
    by (simp add: R1_H2_commute)
  also have "... = R1(H1(R1(H2(R2s(R3c(P))))))"
    by (simp add: R1_idem RD1_via_R1)
  also have "... = R1(H1(H2(R2s(R3c(R1(P))))))"
    by (simp add: R1_H2_commute R1_R2c_commute R1_R2s_R2c R1_R3c_commute RD1_via_R1)
  also have "... = R1(R2s(H1(H2(R3c(R1(P))))))"
    by (simp add: R2s_H1_commute R2s_H2_commute)
  also have "... = R1(R2s(H1(R3c(H2(R1(P))))))"
    by (metis RD2_R3c_commute RD2_def)
  also have "... = R2(R1(H1(R3c(H2(R1(P))))))"
    by (metis R1_R2_commute R1_idem R2_def)
  also have "... = R2(R3c(R1(\<^bold>H(R1(P)))))"
    by (simp add: R1_R3c_commute RD1_R3c_commute RD1_via_R1)
  also have "... = RH(\<^bold>H(R1(P)))"
    by (metis R1_R2s_R2c R1_R3c_commute R2_R1_form RH_def)
  also have "... = RH(\<^bold>H(P))"
    by (simp add: R1_H2_commute R1_R2c_commute R1_R3c_commute R1_idem RD1_via_R1 RH_def)
  also have "... = RH((\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
    by (simp add: H1_H2_eq_design)
  also have "... = \<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (metis (no_types, lifting) R3c_subst_wait RH_def subst_not wait_false_design)
  finally show ?thesis .
qed

lemma RD_reactive_design:
  assumes "P is RD"
  shows "\<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = P"
  by (metis RD_RH_design_form Healthy_def' assms)

lemma RD_RH_design:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q"
  shows "RD(\<^bold>R(P \<turnstile> Q)) = \<^bold>R(P \<turnstile> Q)"
  by (simp add: RD1_reactive_design RD2_reactive_design RD_alt_def RH_idem assms(1) assms(2))

lemma RH_design_is_RD:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q"
  shows "\<^bold>R(P \<turnstile> Q) is RD"
  by (simp add: RD_RH_design Healthy_def' assms(1) assms(2))

lemma SRD_RH_design_form:
  "SRD(P) = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
proof -
  have "SRD(P) = R1(R2c(R3h(RD1(RD2(R1(P))))))"
    by (metis (no_types, lifting) R1_H2_commute R1_R2c_commute R1_R3h_commute R1_idem R2c_H2_commute RD1_R1_commute RD1_R2c_commute RD1_R3h_commute RD2_R3h_commute RD2_def RHS_def SRD_def)
  also have "... = R1(R2s(R3h(\<^bold>H(P))))"
    by (metis (no_types, lifting) R1_H2_commute R1_R2c_is_R2 R1_R3h_commute R2_R1_form RD1_via_R1 RD2_def)
  also have "... = \<^bold>R\<^sub>s(\<^bold>H(P))"
    by (simp add: R1_R2s_R2c RHS_def)
  also have "... = \<^bold>R\<^sub>s((\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
    by (simp add: H1_H2_eq_design)
  also have "... = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (metis (no_types, lifting) R3h_subst_wait RHS_def subst_not wait_false_design)
  finally show ?thesis .
qed

lemma SRD_reactive_design:
  assumes "P is SRD"
  shows "\<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = P"
  by (metis SRD_RH_design_form Healthy_def' assms)

lemma SRD_RH_design:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q"
  shows "SRD(\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (simp add: RD1_st_reactive_design RD2_st_reactive_design RHS_idem SRD_def assms(1) assms(2))

lemma RHS_design_is_SRD:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q) is SRD"
  by (simp add: Healthy_def' SRD_RH_design assms(1) assms(2))

lemma SRD_RHS_H1_H2: "SRD(P) = \<^bold>R\<^sub>s(\<^bold>H(P))"
  by (metis (no_types, lifting) H1_H2_eq_design R3h_subst_wait RHS_def SRD_RH_design_form subst_not wait_false_design)

subsection {* Reactive design composition laws *}

theorem R1_design_composition:
  fixes P Q :: "('t::ordered_cancel_monoid_diff,'\<alpha>,'\<beta>) rel_rp"
  and R S :: "('t,'\<beta>,'\<gamma>) rel_rp"
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows
  "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) =
   R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; R1(\<not> R))) \<turnstile> (R1(Q) ;; R1(S)))"
proof -
  have "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) = (\<^bold>\<exists> ok\<^sub>0 \<bullet> (R1(P \<turnstile> Q))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<acute>\<rbrakk> ;; (R1(R \<turnstile> S))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<rbrakk>)"
    using seqr_middle ok_vwb_lens by blast
  also from assms have "... = (\<^bold>\<exists> ok\<^sub>0 \<bullet> R1(($ok \<and> P) \<Rightarrow> (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> Q)) ;; R1((\<guillemotleft>ok\<^sub>0\<guillemotright>  \<and> R) \<Rightarrow> ($ok\<acute> \<and> S)))"
    by (simp add: design_def R1_def usubst unrest)
  also from assms have "... = ((R1(($ok \<and> P) \<Rightarrow> (true \<and> Q)) ;; R1((true \<and> R) \<Rightarrow> ($ok\<acute> \<and> S)))
                             \<or> (R1(($ok \<and> P) \<Rightarrow> (false \<and> Q)) ;; R1((false \<and> R) \<Rightarrow> ($ok\<acute> \<and> S))))"
    by (simp add: false_alt_def true_alt_def)
  also from assms have "... = ((R1(($ok \<and> P) \<Rightarrow> Q) ;; R1(R \<Rightarrow> ($ok\<acute> \<and> S)))
                             \<or> (R1(\<not> ($ok \<and> P)) ;; R1(true)))"
    by simp
  also from assms have "... = ((R1(\<not> $ok \<or> \<not> P \<or> Q) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S)))
                             \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by (simp add: impl_alt_def utp_pred.sup.assoc)
  also from assms have "... = (((R1(\<not> $ok \<or> \<not> P) \<or> R1(Q)) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S)))
                               \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by (simp add: R1_disj utp_pred.disj_assoc)
  also from assms have "... = ((R1(\<not> $ok \<or> \<not> P) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S)))
                               \<or> (R1(Q) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S)))
                               \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by (simp add: seqr_or_distl utp_pred.sup.assoc)
  also from assms have "... = ((R1(Q) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S)))
                               \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by (rel_blast)
  also from assms have "... = ((R1(Q) ;; (R1(\<not> R) \<or> R1(S) \<and> $ok\<acute>))
                               \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by (simp add: R1_disj R1_extend_conj utp_pred.inf_commute)
  also have "... = ((R1(Q) ;; (R1(\<not> R) \<or> R1(S) \<and> $ok\<acute>))
                  \<or> ((R1(\<not> $ok) :: ('t,'\<alpha>,'\<beta>) rel_rp) ;; R1(true))
                  \<or> (R1(\<not> P) ;; R1(true)))"
    by (simp add: R1_disj seqr_or_distl)
  also have "... = ((R1(Q) ;; (R1(\<not> R) \<or> R1(S) \<and> $ok\<acute>))
                  \<or> (R1(\<not> $ok))
                  \<or> (R1(\<not> P) ;; R1(true)))"
  proof -
    have "((R1(\<not> $ok) :: ('t,'\<alpha>,'\<beta>) rel_rp) ;; R1(true)) =
           (R1(\<not> $ok) :: ('t,'\<alpha>,'\<gamma>) rel_rp)"
      by (rel_auto)
    thus ?thesis
      by simp
  qed
  also have "... = ((R1(Q) ;; (R1(\<not> R) \<or> (R1(S \<and> $ok\<acute>))))
                  \<or> R1(\<not> $ok)
                  \<or> (R1(\<not> P) ;; R1(true)))"
    by (simp add: R1_extend_conj)
  also have "... = ( (R1(Q) ;; (R1 (\<not> R)))
                   \<or> (R1(Q) ;; (R1(S \<and> $ok\<acute>)))
                   \<or> R1(\<not> $ok)
                   \<or> (R1(\<not> P) ;; R1(true)))"
    by (simp add: seqr_or_distr utp_pred.sup.assoc)
  also have "... = R1( (R1(Q) ;; (R1 (\<not> R)))
                     \<or> (R1(Q) ;; (R1(S \<and> $ok\<acute>)))
                     \<or> (\<not> $ok)
                     \<or> (R1(\<not> P) ;; R1(true)))"
    by (simp add: R1_disj R1_seqr)
  also have "... = R1( (R1(Q) ;; (R1 (\<not> R)))
                     \<or> ((R1(Q) ;; R1(S)) \<and> $ok\<acute>)
                     \<or> (\<not> $ok)
                     \<or> (R1(\<not> P) ;; R1(true)))"
    by (rel_blast)
  also have "... = R1(\<not>($ok \<and> \<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; (R1 (\<not> R))))
                     \<or>  ((R1(Q) ;; R1(S)) \<and> $ok\<acute>))"
    by (rel_blast)
  also have "... = R1(($ok \<and> \<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; (R1 (\<not> R))))
                      \<Rightarrow> ($ok\<acute> \<and> (R1(Q) ;; R1(S))))"
    by (simp add: impl_alt_def utp_pred.inf_commute)
  also have "... = R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; R1(\<not> R))) \<turnstile> (R1(Q) ;; R1(S)))"
    by (simp add: design_def)
  finally show ?thesis .
qed

definition [upred_defs]: "R3c_pre(P) = (true \<triangleleft> $wait \<triangleright> P)"

definition [upred_defs]: "R3c_post(P) = (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> P)"

definition [upred_defs]: "R3h_post(P) = ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> P)"

lemma R3c_pre_conj: "R3c_pre(P \<and> Q) = (R3c_pre(P) \<and> R3c_pre(Q))"
  by (rel_auto)

lemma R3c_pre_seq:
  "(true ;; Q) = true \<Longrightarrow> R3c_pre(P ;; Q) = (R3c_pre(P) ;; Q)"
  by (rel_auto)

lemma R2s_st'_eq_st:
  "R2s($st\<acute> =\<^sub>u $st) = ($st\<acute> =\<^sub>u $st)"
  by (rel_auto)

lemma R2s_design: "R2s(P \<turnstile> Q) = (R2s(P) \<turnstile> R2s(Q))"
  by (simp add: R2s_def design_def usubst)

lemma R2c_design: "R2c(P \<turnstile> Q) = (R2c(P) \<turnstile> R2c(Q))"
  by (simp add: design_def impl_alt_def R2c_disj R2c_not R2c_ok R2c_and R2c_ok')

lemma R1_R3c_design:
  "R1(R3c(P \<turnstile> Q)) = R1(R3c_pre(P) \<turnstile> R3c_post(Q))"
  by (rel_auto)

lemma R1_R3h_design:
  "R1(R3h(P \<turnstile> Q)) = R1(R3c_pre(P) \<turnstile> R3h_post(Q))"
  by (rel_auto)

lemma unrest_ok_R2s [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R2s(P)"
  by (simp add: R2s_def unrest)

lemma unrest_ok'_R2s [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R2s(P)"
  by (simp add: R2s_def unrest)

lemma unrest_ok_R2c [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma unrest_ok'_R2c [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma unrest_ok_R3c_pre [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R3c_pre(P)"
  by (simp add: R3c_pre_def cond_def unrest)

lemma unrest_ok'_R3c_pre [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R3c_pre(P)"
  by (simp add: R3c_pre_def cond_def unrest)

lemma unrest_ok_R3c_post [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R3c_post(P)"
  by (simp add: R3c_post_def cond_def unrest)

lemma unrest_ok_R3c_post' [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R3c_post(P)"
  by (simp add: R3c_post_def cond_def unrest)

lemma unrest_ok_R3h_post [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R3h_post(P)"
  by (simp add: R3h_post_def cond_def unrest)

lemma unrest_ok_R3h_post' [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R3h_post(P)"
  by (simp add: R3h_post_def cond_def unrest)

lemma R3c_R1_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(R3c(R1(P \<turnstile> Q)) ;; R3c(R1(R \<turnstile> S))) =
       R3c(R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> ((R1(Q) \<and> \<not> $wait\<acute>) ;; R1(\<not> R)))
       \<turnstile> (R1(Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1(S)))))"
proof -
  have 1:"(\<not> (R1 (\<not> R3c_pre P) ;; R1 true)) = (R3c_pre (\<not> (R1 (\<not> P) ;; R1 true)))"
    by (rel_auto)
  have 2:"(\<not> (R1 (R3c_post Q) ;; R1 (\<not> R3c_pre R))) = R3c_pre(\<not> ((R1 Q \<and> \<not> $wait\<acute>) ;; R1 (\<not> R)))"
    by (rel_auto)
  have 3:"(R1 (R3c_post Q) ;; R1 (R3c_post S)) = R3c_post (R1 Q ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 S))"
    by (rel_auto)
  show ?thesis
    apply (simp add: R3c_semir_form R1_R3c_commute[THEN sym] R1_R3c_design unrest )
    apply (subst R1_design_composition)
    apply (simp_all add: unrest assms R3c_pre_conj 1 2 3)
  done
qed

lemma R3h_R1_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(R3h(R1(P \<turnstile> Q)) ;; R3h(R1(R \<turnstile> S))) =
       R3h(R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> ((R1(Q) \<and> \<not> $wait\<acute>) ;; R1(\<not> R)))
       \<turnstile> (R1(Q) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1(S)))))"
proof -
  have 1:"(\<not> (R1 (\<not> R3c_pre P) ;; R1 true)) = (R3c_pre (\<not> (R1 (\<not> P) ;; R1 true)))"
   by (rel_auto, blast+)
  have 2:"(\<not> (R1 (R3h_post Q) ;; R1 (\<not> R3c_pre R))) = R3c_pre(\<not> ((R1 Q \<and> \<not> $wait\<acute>) ;; R1 (\<not> R)))"
    by (rel_auto, blast+)
  have 3:"(R1 (R3h_post Q) ;; R1 (R3h_post S)) = R3h_post (R1 Q ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 S))"
    by (rel_auto, blast+)
  show ?thesis
    apply (simp add: R3h_semir_form R1_R3h_commute[THEN sym] R1_R3h_design unrest )
    apply (subst R1_design_composition)
    apply (simp_all add: unrest assms R3c_pre_conj 1 2 3)
  done
qed

lemma R1_des_lift_skip: "R1(\<lceil>II\<rceil>\<^sub>D) = \<lceil>II\<rceil>\<^sub>D"
  by (rel_auto)

lemma R2s_subst_wait_true [usubst]:
  "(R2s(P))\<lbrakk>true/$wait\<rbrakk> = R2s(P\<lbrakk>true/$wait\<rbrakk>)"
  by (simp add: R2s_def usubst unrest)

lemma R2s_subst_wait'_true [usubst]:
  "(R2s(P))\<lbrakk>true/$wait\<acute>\<rbrakk> = R2s(P\<lbrakk>true/$wait\<acute>\<rbrakk>)"
  by (simp add: R2s_def usubst unrest)

lemma R2_subst_wait_true [usubst]:
  "(R2(P))\<lbrakk>true/$wait\<rbrakk> = R2(P\<lbrakk>true/$wait\<rbrakk>)"
  by (simp add: R2_def R1_def R2s_def usubst unrest)

lemma R2_subst_wait'_true [usubst]:
  "(R2(P))\<lbrakk>true/$wait\<acute>\<rbrakk> = R2(P\<lbrakk>true/$wait\<acute>\<rbrakk>)"
  by (simp add: R2_def R1_def R2s_def usubst unrest)

lemma R2_subst_wait_false [usubst]:
  "(R2(P))\<lbrakk>false/$wait\<rbrakk> = R2(P\<lbrakk>false/$wait\<rbrakk>)"
  by (simp add: R2_def R1_def R2s_def usubst unrest)

lemma R2_subst_wait'_false [usubst]:
  "(R2(P))\<lbrakk>false/$wait\<acute>\<rbrakk> = R2(P\<lbrakk>false/$wait\<acute>\<rbrakk>)"
  by (simp add: R2_def R1_def R2s_def usubst unrest)

lemma R2_des_lift_skip:
  "R2(\<lceil>II\<rceil>\<^sub>D) = \<lceil>II\<rceil>\<^sub>D"
  apply (rel_auto) using minus_zero_eq by blast

lemma R2c_R2s_absorb: "R2c(R2s(P)) = R2s(P)"
  by (rel_auto)

lemma R2_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(R2(P \<turnstile> Q) ;; R2(R \<turnstile> S)) =
       R2((\<not> (R1 (\<not> R2c P) ;; R1 true) \<and> \<not> (R1 (R2c Q) ;; R1 (\<not> R2c R))) \<turnstile> (R1 (R2c Q) ;; R1 (R2c S)))"
  apply (simp add: R2_R2c_def R2c_design R1_design_composition assms unrest R2c_not R2c_and R2c_disj R1_R2c_commute[THEN sym] R2c_idem R2c_R1_seq)
  apply (metis (no_types, lifting) R2c_R1_seq R2c_not R2c_true)
done

lemma RH_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(RH(P \<turnstile> Q) ;; RH(R \<turnstile> S)) =
       RH((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> (\<not> $wait\<acute>)) ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))))"
proof -
  have 1: "R2c (R1 (\<not> R2s P) ;; R1 true) = (R1 (\<not> R2s P) ;; R1 true)"
  proof -
    have 1:"(R1 (\<not> R2s P) ;; R1 true) = (R1(R2 (\<not> P) ;; R2 true))"
      by (rel_auto)
    have "R2c(R1(R2 (\<not> P) ;; R2 true)) = R2c(R1(R2 (\<not> P) ;; R2 true))"
      using R2c_not by blast
    also have "... = R2(R2 (\<not> P) ;; R2 true)"
      by (metis R1_R2c_commute R1_R2c_is_R2)
    also have "... = (R2 (\<not> P) ;; R2 true)"
      by (simp add: R2_seqr_distribute)
    also have "... = (R1 (\<not> R2s P) ;; R1 true)"
      by (simp add: R2_def R2s_not R2s_true)
    finally show ?thesis
      by (simp add: 1)
  qed

  have 2:"R2c ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R)) = ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))"
  proof -
    have "((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R)) = R1 (R2 (Q \<and> \<not> $wait\<acute>) ;; R2 (\<not> R))"
      by (rel_auto)
    hence "R2c ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R)) = (R2 (Q \<and> \<not> $wait\<acute>) ;; R2 (\<not> R))"
      by (metis R1_R2c_commute R1_R2c_is_R2 R2_seqr_distribute)
    also have "... = ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))"
      by (rel_auto)
    finally show ?thesis .
  qed

  have 3:"R2c((R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S)))) = (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S)))"
  proof -
    have "R2c(((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>))
          = ((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)"
    proof -
      have "R2c(((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)) =
            R2c(R1 (R2s (Q\<lbrakk>true/$wait\<acute>\<rbrakk>)) ;; \<lceil>II\<rceil>\<^sub>D\<lbrakk>true/$wait\<rbrakk>)"
        by (simp add: usubst cond_unit_T R1_def R2s_def)
      also have "... = R2c(R2(Q\<lbrakk>true/$wait\<acute>\<rbrakk>) ;; R2(\<lceil>II\<rceil>\<^sub>D\<lbrakk>true/$wait\<rbrakk>))"
        by (metis R2_def R2_des_lift_skip R2_subst_wait_true)
      also have "... = (R2(Q\<lbrakk>true/$wait\<acute>\<rbrakk>) ;; R2(\<lceil>II\<rceil>\<^sub>D\<lbrakk>true/$wait\<rbrakk>))"
        using R2c_seq by blast
      also have "... = ((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)"
        apply (simp add: usubst R2_des_lift_skip)
        apply (metis R2_def R2_des_lift_skip R2_subst_wait'_true R2_subst_wait_true)
      done
      finally show ?thesis .
    qed
    moreover have "R2c(((R1 (R2s Q))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>false/$wait\<rbrakk>))
          = ((R1 (R2s Q))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>false/$wait\<rbrakk>)"
      by (simp add: usubst cond_unit_F)
         (metis (no_types, hide_lams) R1_wait'_false R1_wait_false R2_def R2_subst_wait'_false R2_subst_wait_false R2c_seq)
    ultimately show ?thesis
    proof -
      have "\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S) = R2 (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> S)"
        by (simp add: R1_R2c_is_R2 R1_R2s_R2c R2_condr' R2_des_lift_skip R2s_wait)
      then show ?thesis
        by (simp add: R1_R2c_is_R2 R1_R2s_R2c R2c_seq)
    qed
  qed

  have "(R1(R2s(R3c(P \<turnstile> Q))) ;; R1(R2s(R3c(R \<turnstile> S)))) =
        ((R3c(R1(R2s(P) \<turnstile> R2s(Q)))) ;; R3c(R1(R2s(R) \<turnstile> R2s(S))))"
    by (metis (no_types, hide_lams) R1_R2s_R2c R1_R3c_commute R2c_R3c_commute R2s_design)
  also have "... = R3c (R1 ((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S)))))"
    by (simp add: R3c_R1_design_composition assms unrest)
  also have "... = R3c(R1(R2c((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))) \<turnstile>
                              (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))))))"
    by (simp add: R2c_design R2c_and R2c_not 1 2 3)
  finally show ?thesis
    by (simp add: R1_R2s_R2c R1_R3c_commute R2c_R3c_commute RH_def)
qed

lemma R2_st_ex: "R2 (\<exists> $st \<bullet> P) = (\<exists> $st \<bullet> R2(P))"
  by (rel_auto)

lemma RHS_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q) ;; \<^bold>R\<^sub>s(R \<turnstile> S)) =
       \<^bold>R\<^sub>s((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> (\<not> $wait\<acute>)) ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))))"
proof -
  have 1: "R2c (R1 (\<not> R2s P) ;; R1 true) = (R1 (\<not> R2s P) ;; R1 true)"
  proof -
    have 1:"(R1 (\<not> R2s P) ;; R1 true) = (R1(R2 (\<not> P) ;; R2 true))"
      by (rel_auto, blast)
    have "R2c(R1(R2 (\<not> P) ;; R2 true)) = R2c(R1(R2 (\<not> P) ;; R2 true))"
      using R2c_not by blast
    also have "... = R2(R2 (\<not> P) ;; R2 true)"
      by (metis R1_R2c_commute R1_R2c_is_R2)
    also have "... = (R2 (\<not> P) ;; R2 true)"
      by (simp add: R2_seqr_distribute)
    also have "... = (R1 (\<not> R2s P) ;; R1 true)"
      by (simp add: R2_def R2s_not R2s_true)
    finally show ?thesis
      by (simp add: 1)
  qed

  have 2:"R2c ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R)) = ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))"
  proof -
    have "((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R)) = R1 (R2 (Q \<and> \<not> $wait\<acute>) ;; R2 (\<not> R))"
      by (rel_auto, blast+)
    hence "R2c ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R)) = (R2 (Q \<and> \<not> $wait\<acute>) ;; R2 (\<not> R))"
      by (metis (no_types, lifting) R1_R2c_commute R1_R2c_is_R2 R2_seqr_distribute)
    also have "... = ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))"
      by (rel_auto, blast+)
    finally show ?thesis .
  qed

  have 3:"R2c((R1 (R2s Q) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S)))) =
          (R1 (R2s Q) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S)))"
  proof -
    have "R2c(((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>))
          = ((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)"
    proof -
      have "R2c(((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)) =
            R2c(R1 (R2s (Q\<lbrakk>true/$wait\<acute>\<rbrakk>)) ;; (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D)\<lbrakk>true/$wait\<rbrakk>)"
        by (simp add: usubst cond_unit_T R1_def R2s_def)
      also have "... = R2c(R2(Q\<lbrakk>true/$wait\<acute>\<rbrakk>) ;; R2((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D)\<lbrakk>true/$wait\<rbrakk>))"
        by (metis (no_types, lifting) R2_def R2_des_lift_skip R2_subst_wait_true R2_st_ex)
      also have "... = (R2(Q\<lbrakk>true/$wait\<acute>\<rbrakk>) ;; R2((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D)\<lbrakk>true/$wait\<rbrakk>))"
        using R2c_seq by blast
      also have "... = ((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)"
        apply (simp add: usubst R2_des_lift_skip)
        apply (metis (no_types) R2_def R2_des_lift_skip R2_st_ex R2_subst_wait'_true R2_subst_wait_true)
      done
      finally show ?thesis .
    qed
    moreover have "R2c(((R1 (R2s Q))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>false/$wait\<rbrakk>))
          = ((R1 (R2s Q))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>false/$wait\<rbrakk>)"
      by (simp add: usubst)
         (metis (no_types, lifting) R1_wait'_false R1_wait_false R2_R1_form R2_subst_wait'_false R2_subst_wait_false R2c_seq)
    ultimately show ?thesis
      by (smt R2_R1_form R2_condr' R2_des_lift_skip R2_st_ex R2c_seq R2s_wait)
  qed

  have "(R1(R2s(R3h(P \<turnstile> Q))) ;; R1(R2s(R3h(R \<turnstile> S)))) =
        ((R3h(R1(R2s(P) \<turnstile> R2s(Q)))) ;; R3h(R1(R2s(R) \<turnstile> R2s(S))))"
    by (metis (no_types, hide_lams) R1_R2s_R2c R1_R3h_commute R2c_R3h_commute R2s_design)
  also have "... = R3h (R1 ((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S)))))"
    by (simp add: R3h_R1_design_composition assms unrest)
  also have "... = R3h(R1(R2c((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))) \<turnstile>
                              (R1 (R2s Q) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))))))"
    by (simp add: R2c_design R2c_and R2c_not 1 2 3)
  finally show ?thesis
    by (simp add: R1_R2s_R2c R1_R3h_commute R2c_R3h_commute RHS_def)
qed

lemma RHS_R2s_design_composition:
  assumes
    "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
    "P is R2s" "Q is R2s" "R is R2s" "S is R2s"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q) ;; \<^bold>R\<^sub>s(R \<turnstile> S)) =
       \<^bold>R\<^sub>s((\<not> (R1 (\<not> P) ;; R1 true) \<and> \<not> ((R1 Q \<and> \<not> $wait\<acute>) ;; R1 (\<not> R))) \<turnstile>
                       (R1 Q ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 S)))"
proof -
  have f1: "R2s P = P"
    by (meson Healthy_def assms(5))
  have f2: "R2s Q = Q"
    by (meson Healthy_def assms(6))
  have f3: "R2s R = R"
    by (meson Healthy_def assms(7))
  have "R2s S = S"
    by (meson Healthy_def assms(8))
  then show ?thesis
    using f3 f2 f1 by (simp add: RHS_design_composition assms(1) assms(2) assms(3) assms(4))
qed

lemma RH_design_export_R1: "\<^bold>R(P \<turnstile> Q) = \<^bold>R(P \<turnstile> R1(Q))"
  by (rel_auto)

lemma RH_design_export_R2s: "\<^bold>R(P \<turnstile> Q) = \<^bold>R(P \<turnstile> R2s(Q))"
  by (rel_auto)

lemma RH_design_export_R2c: "\<^bold>R(P \<turnstile> Q) = \<^bold>R(P \<turnstile> R2c(Q))"
  by (rel_auto)

lemma RHS_design_export_R1: "\<^bold>R\<^sub>s(P \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> R1(Q))"
  by (rel_auto)

lemma RHS_design_export_R2s: "\<^bold>R\<^sub>s(P \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> R2s(Q))"
  by (rel_auto)

lemma RHS_design_export_R2c: "\<^bold>R\<^sub>s(P \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> R2c(Q))"
  by (rel_auto)

subsection {* Reactive design triples *}

definition wait'_cond :: 
  "('t::ordered_cancel_monoid_diff,'\<alpha>,'\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" (infixr "\<diamondop>" 65) where
[upred_defs]: "P \<diamondop> Q = (P \<triangleleft> $wait\<acute> \<triangleright> Q)"

lemma wait'_cond_unrest [unrest]:
  "\<lbrakk> out_var wait \<bowtie> x; x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> (P \<diamondop> Q)"
  by (simp add: wait'_cond_def unrest)

lemma wait'_cond_subst [usubst]:
  "$wait\<acute> \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<dagger> (P \<diamondop> Q) = (\<sigma> \<dagger> P) \<diamondop> (\<sigma> \<dagger> Q)"
  by (simp add: wait'_cond_def usubst unrest)

lemma wait'_cond_left_false: "false \<diamondop> P = (\<not> $wait\<acute> \<and> P)"
  by (rel_auto)

lemma wait'_cond_seq: "((P \<diamondop> Q) ;; R) = ((P ;; ($wait \<and> R)) \<or> (Q ;; (\<not>$wait \<and> R)))"
  by (simp add: wait'_cond_def cond_def seqr_or_distl, rel_blast)

lemma wait'_cond_true: "(P \<diamondop> Q \<and> $wait\<acute>) = (P \<and> $wait\<acute>)"
  by (rel_auto)

lemma wait'_cond_false: "(P \<diamondop> Q \<and> (\<not>$wait\<acute>)) = (Q \<and> (\<not>$wait\<acute>))"
  by (rel_auto)

lemma wait'_cond_idem: "P \<diamondop> P = P"
  by (rel_auto)

lemma wait'_cond_conj_exchange:
  "((P \<diamondop> Q) \<and> (R \<diamondop> S)) = (P \<and> R) \<diamondop> (Q \<and> S)"
  by (rel_auto)

lemma subst_wait'_cond_true [usubst]: "(P \<diamondop> Q)\<lbrakk>true/$wait\<acute>\<rbrakk> = P\<lbrakk>true/$wait\<acute>\<rbrakk>"
  by (rel_auto)

lemma subst_wait'_cond_false [usubst]: "(P \<diamondop> Q)\<lbrakk>false/$wait\<acute>\<rbrakk> = Q\<lbrakk>false/$wait\<acute>\<rbrakk>"
  by (rel_auto)

lemma subst_wait'_left_subst: "(P\<lbrakk>true/$wait\<acute>\<rbrakk> \<diamondop> Q) = (P \<diamondop> Q)"
  by (rel_auto)

lemma subst_wait'_right_subst: "(P \<diamondop> Q\<lbrakk>false/$wait\<acute>\<rbrakk>) = (P \<diamondop> Q)"
  by (rel_auto)

lemma wait'_cond_split: "P\<lbrakk>true/$wait\<acute>\<rbrakk> \<diamondop> P\<lbrakk>false/$wait\<acute>\<rbrakk> = P"
  by (simp add: wait'_cond_def cond_var_split)

lemma wait_cond'_assoc: "P \<diamondop> Q \<diamondop> R = P \<diamondop> R"
  by (rel_auto)

lemma wait_cond'_shadow: "(P \<diamondop> Q) \<diamondop> R = P \<diamondop> Q \<diamondop> R"
  by (rel_auto)

lemma wait_cond'_conj: "P \<diamondop> (Q \<and> (R \<diamondop> S)) = P \<diamondop> (Q \<and> S)"
  by (rel_auto)

lemma R1_wait'_cond: "R1(P \<diamondop> Q) = R1(P) \<diamondop> R1(Q)"
  by (rel_auto)

lemma R2s_wait'_cond: "R2s(P \<diamondop> Q) = R2s(P) \<diamondop> R2s(Q)"
  by (simp add: wait'_cond_def R2s_def R2s_def usubst)

lemma R2_wait'_cond: "R2(P \<diamondop> Q) = R2(P) \<diamondop> R2(Q)"
  by (simp add: R2_def R2s_wait'_cond R1_wait'_cond)

lemma RH_design_peri_R1: "\<^bold>R(P \<turnstile> R1(Q) \<diamondop> R) = \<^bold>R(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R1_idem R1_wait'_cond RH_design_export_R1)

lemma RH_design_post_R1: "\<^bold>R(P \<turnstile> Q \<diamondop> R1(R)) = \<^bold>R(P \<turnstile> Q \<diamondop> R)"
  by (metis R1_wait'_cond RH_design_export_R1 RH_design_peri_R1)

lemma RH_design_peri_R2s: "\<^bold>R(P \<turnstile> R2s(Q) \<diamondop> R) = \<^bold>R(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R2s_idem R2s_wait'_cond RH_design_export_R2s)

lemma RH_design_post_R2s: "\<^bold>R(P \<turnstile> Q \<diamondop> R2s(R)) = \<^bold>R(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R2s_idem R2s_wait'_cond RH_design_export_R2s)

lemma RH_design_peri_R2c: "\<^bold>R(P \<turnstile> R2c(Q) \<diamondop> R) = \<^bold>R(P \<turnstile> Q \<diamondop> R)"
  by (metis R1_R2s_R2c RH_design_peri_R1 RH_design_peri_R2s)

lemma RHS_design_peri_R1: "\<^bold>R\<^sub>s(P \<turnstile> R1(Q) \<diamondop> R) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R1_idem R1_wait'_cond RHS_design_export_R1)

lemma RHS_design_post_R1: "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R1(R)) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)"
  by (metis R1_wait'_cond RHS_design_export_R1 RHS_design_peri_R1)

lemma RHS_design_peri_R2s: "\<^bold>R\<^sub>s(P \<turnstile> R2s(Q) \<diamondop> R) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R2s_idem R2s_wait'_cond RHS_design_export_R2s)

lemma RHS_design_post_R2s: "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R2s(R)) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)"
  by (metis R2s_wait'_cond RHS_design_export_R2s RHS_design_peri_R2s)

lemma RHS_design_peri_R2c: "\<^bold>R\<^sub>s(P \<turnstile> R2c(Q) \<diamondop> R) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)"
  by (metis R1_R2s_R2c RHS_design_peri_R1 RHS_design_peri_R2s)

lemma RH_design_lemma1:
  "RH(P \<turnstile> (R1(R2c(Q)) \<or> R) \<diamondop> S) = RH(P \<turnstile> (Q \<or> R) \<diamondop> S)"
  by (metis (no_types, lifting) R1_R2c_is_R2 R1_R2s_R2c R2_R1_form R2_disj R2c_idem RH_design_peri_R1 RH_design_peri_R2s)

lemma RHS_design_lemma1:
  "RHS(P \<turnstile> (R1(R2c(Q)) \<or> R) \<diamondop> S) = RHS(P \<turnstile> (Q \<or> R) \<diamondop> S)"
  by (metis (no_types, lifting) R1_R2c_is_R2 R1_R2s_R2c R2_R1_form R2_disj R2c_idem RHS_design_peri_R1 RHS_design_peri_R2s)

theorem RH_tri_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$ok \<sharp> R" "$ok \<sharp> S\<^sub>1" "$ok \<sharp> S\<^sub>2"
           "$wait\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> S\<^sub>1" "$wait \<sharp> S\<^sub>2"
  shows "(RH(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; RH(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)) =
       RH((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q\<^sub>2) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))) \<turnstile>
                       ((Q\<^sub>1 \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> ((R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))))"
proof -
  have 1:"(\<not> ((R1 (R2s (Q\<^sub>1 \<diamondop> Q\<^sub>2)) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))) =
        (\<not> ((R1 (R2s Q\<^sub>2) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R)))"
    by (metis (no_types, hide_lams) R1_extend_conj R2s_conj R2s_not R2s_wait' wait'_cond_false)
  have 2: "(R1 (R2s (Q\<^sub>1 \<diamondop> Q\<^sub>2)) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s (S\<^sub>1 \<diamondop> S\<^sub>2)))) =
                 ((R1 (R2s Q\<^sub>1) \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))"
  proof -
    have "(R1 (R2s Q\<^sub>1) ;; ($wait \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
                       = (R1 (R2s Q\<^sub>1) \<and> $wait\<acute>)"
    proof -
      have "(R1 (R2s Q\<^sub>1) ;; ($wait \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
           = (R1 (R2s Q\<^sub>1) ;; ($wait \<and> \<lceil>II\<rceil>\<^sub>D))"
        by (rel_auto)
      also have "... = ((R1 (R2s Q\<^sub>1) ;; \<lceil>II\<rceil>\<^sub>D) \<and> $wait\<acute>)"
        by (rel_auto)
      also from assms(2) have "... = ((R1 (R2s Q\<^sub>1)) \<and> $wait\<acute>)"
        by (simp add: lift_des_skip_dr_unit_unrest unrest)
      finally show ?thesis .
    qed

    moreover have "(R1 (R2s Q\<^sub>2) ;; (\<not> $wait \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
                  = ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2)))"
    proof -
      have "(R1 (R2s Q\<^sub>2) ;; (\<not> $wait \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
            = (R1 (R2s Q\<^sub>2) ;; (\<not> $wait \<and> (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))"
        by (metis (no_types, lifting) cond_def conj_disj_not_abs utp_pred.double_compl utp_pred.inf.left_idem utp_pred.sup_assoc utp_pred.sup_inf_absorb)

      also have "... = ((R1 (R2s Q\<^sub>2))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))\<lbrakk>false/$wait\<rbrakk>)"
        by (metis false_alt_def seqr_right_one_point upred_eq_false wait_vwb_lens)

      also have "... = ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2)))"
        by (simp add: wait'_cond_def usubst unrest assms)

      finally show ?thesis .
    qed

    moreover
    have "((R1 (R2s Q\<^sub>1) \<and> $wait\<acute>) \<or> ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
          = (R1 (R2s Q\<^sub>1) \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> ((R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))"
      by (simp add: wait'_cond_def cond_seq_right_distr cond_and_T_integrate unrest)

    ultimately show ?thesis
      by (simp add: R2s_wait'_cond R1_wait'_cond wait'_cond_seq)
  qed

  show ?thesis
    apply (subst RH_design_composition)
    apply (simp_all add: assms)
    apply (simp add: assms wait'_cond_def unrest)
    apply (simp add: assms wait'_cond_def unrest)
    apply (simp add: 1 2)
    apply (simp add: R1_R2s_R2c RH_design_lemma1)
  done
qed

lemma ex_conj_contr_left: "x \<sharp> P \<Longrightarrow> (\<exists> x \<bullet> P \<and> Q) = (P \<and> (\<exists> x \<bullet> Q))"
  by (pred_auto)

lemma ex_conj_contr_right: "x \<sharp> Q \<Longrightarrow> (\<exists> x \<bullet> P \<and> Q) = ((\<exists> x \<bullet> P) \<and> Q)"
  by (pred_auto)

lemma R1_R2c_ex_st: "R1 (R2c (\<exists> $st\<acute> \<bullet> Q\<^sub>1)) = (\<exists> $st\<acute> \<bullet> R1 (R2c Q\<^sub>1))"
  by (rel_auto)

theorem RHS_tri_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$ok \<sharp> R" "$ok \<sharp> S\<^sub>1" "$ok \<sharp> S\<^sub>2"
           "$wait\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> S\<^sub>1" "$wait \<sharp> S\<^sub>2"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)) =
       \<^bold>R\<^sub>s((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> ((R1 (R2s Q\<^sub>2) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))) \<turnstile>
                       (((\<exists> $st\<acute> \<bullet> Q\<^sub>1) \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> ((R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))))"
proof -
  have 1:"(\<not> ((R1 (R2s (Q\<^sub>1 \<diamondop> Q\<^sub>2)) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))) =
        (\<not> ((R1 (R2s Q\<^sub>2) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R)))"
    by (metis (no_types, hide_lams) R1_extend_conj R2s_conj R2s_not R2s_wait' wait'_cond_false)
  have 2: "(R1 (R2s (Q\<^sub>1 \<diamondop> Q\<^sub>2)) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s (S\<^sub>1 \<diamondop> S\<^sub>2)))) =
                 (((\<exists> $st\<acute> \<bullet> R1 (R2s Q\<^sub>1)) \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))"
  proof -
    have "(R1 (R2s Q\<^sub>1) ;; ($wait \<and> ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
                       = (\<exists> $st\<acute> \<bullet> ((R1 (R2s Q\<^sub>1)) \<and> $wait\<acute>))"
    proof -
      have "(R1 (R2s Q\<^sub>1) ;; ($wait \<and> ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
           = (R1 (R2s Q\<^sub>1) ;; ($wait \<and> (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D)))"
        by (rel_auto, blast)
      also have "... = ((R1 (R2s Q\<^sub>1) ;; (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D)) \<and> $wait\<acute>)"
        by (rel_auto)
      also from assms(2) have "... = (\<exists> $st\<acute> \<bullet> ((R1 (R2s Q\<^sub>1)) \<and> $wait\<acute>))"
        by (rel_auto, blast)
      finally show ?thesis .
    qed

    moreover have "(R1 (R2s Q\<^sub>2) ;; (\<not> $wait \<and> ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
                  = ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2)))"
    proof -
      have "(R1 (R2s Q\<^sub>2) ;; (\<not> $wait \<and> ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
            = (R1 (R2s Q\<^sub>2) ;; (\<not> $wait \<and> (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))"
        by (metis (no_types, lifting) cond_def conj_disj_not_abs utp_pred.double_compl utp_pred.inf.left_idem utp_pred.sup_assoc utp_pred.sup_inf_absorb)

      also have "... = ((R1 (R2s Q\<^sub>2))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))\<lbrakk>false/$wait\<rbrakk>)"
        by (metis false_alt_def seqr_right_one_point upred_eq_false wait_vwb_lens)

      also have "... = ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2)))"
        by (simp add: wait'_cond_def usubst unrest assms)

      finally show ?thesis .
    qed

    moreover
    have "((R1 (R2s Q\<^sub>1) \<and> $wait\<acute>) \<or> ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
          = (R1 (R2s Q\<^sub>1) \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> ((R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))"
      by (simp add: wait'_cond_def cond_seq_right_distr cond_and_T_integrate unrest)

    ultimately show ?thesis
      by (simp add: R2s_wait'_cond R1_wait'_cond wait'_cond_seq ex_conj_contr_right unrest)
         (simp add: cond_and_T_integrate cond_seq_right_distr unrest_var wait'_cond_def)
  qed

  show ?thesis
    apply (subst RHS_design_composition)
    apply (simp_all add: assms)
    apply (simp add: assms wait'_cond_def unrest)
    apply (simp add: assms wait'_cond_def unrest)
    apply (simp add: 1 2)
    apply (simp add: R1_R2s_R2c RHS_design_lemma1)
    apply (metis R1_R2c_ex_st RHS_design_lemma1)
  done
qed

text {* Syntax for pre-, post-, and periconditions *}

abbreviation "pre\<^sub>s  \<equiv> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s false, $wait \<mapsto>\<^sub>s false]"
abbreviation "cmt\<^sub>s  \<equiv> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false]"
abbreviation "peri\<^sub>s \<equiv> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false, $wait\<acute> \<mapsto>\<^sub>s true]"
abbreviation "post\<^sub>s \<equiv> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false, $wait\<acute> \<mapsto>\<^sub>s false]"

abbreviation "npre\<^sub>R(P) \<equiv> pre\<^sub>s \<dagger> P"

definition [upred_defs]: "pre\<^sub>R(P)  = (\<not> (npre\<^sub>R(P)))"
definition [upred_defs]: "cmt\<^sub>R(P)  = (cmt\<^sub>s \<dagger> P)"
definition [upred_defs]: "peri\<^sub>R(P) = (peri\<^sub>s \<dagger> P)"
definition [upred_defs]: "post\<^sub>R(P) = (post\<^sub>s \<dagger> P)"

lemma ok_pre_unrest [unrest]: "$ok \<sharp> pre\<^sub>R P"
  by (simp add: pre\<^sub>R_def unrest usubst)

lemma ok_peri_unrest [unrest]: "$ok \<sharp> peri\<^sub>R P"
  by (simp add: peri\<^sub>R_def unrest usubst)

lemma ok_post_unrest [unrest]: "$ok \<sharp> post\<^sub>R P"
  by (simp add: post\<^sub>R_def unrest usubst)

lemma ok_cmt_unrest [unrest]: "$ok \<sharp> cmt\<^sub>R P"
  by (simp add: cmt\<^sub>R_def unrest usubst)

lemma ok'_pre_unrest [unrest]: "$ok\<acute> \<sharp> pre\<^sub>R P"
  by (simp add: pre\<^sub>R_def unrest usubst)

lemma ok'_peri_unrest [unrest]: "$ok\<acute> \<sharp> peri\<^sub>R P"
  by (simp add: peri\<^sub>R_def unrest usubst)

lemma ok'_post_unrest [unrest]: "$ok\<acute> \<sharp> post\<^sub>R P"
  by (simp add: post\<^sub>R_def unrest usubst)

lemma ok'_cmt_unrest [unrest]: "$ok\<acute> \<sharp> cmt\<^sub>R P"
  by (simp add: cmt\<^sub>R_def unrest usubst)

lemma wait_pre_unrest [unrest]: "$wait \<sharp> pre\<^sub>R P"
  by (simp add: pre\<^sub>R_def unrest usubst)

lemma wait_peri_unrest [unrest]: "$wait \<sharp> peri\<^sub>R P"
  by (simp add: peri\<^sub>R_def unrest usubst)

lemma wait_post_unrest [unrest]: "$wait \<sharp> post\<^sub>R P"
  by (simp add: post\<^sub>R_def unrest usubst)

lemma wait_cmt_unrest [unrest]: "$wait \<sharp> cmt\<^sub>R P"
  by (simp add: cmt\<^sub>R_def unrest usubst)

lemma wait'_peri_unrest [unrest]: "$wait\<acute> \<sharp> peri\<^sub>R P"
  by (simp add: peri\<^sub>R_def unrest usubst)

lemma wait'_post_unrest [unrest]: "$wait\<acute> \<sharp> post\<^sub>R P"
  by (simp add: post\<^sub>R_def unrest usubst)

lemma pre\<^sub>s_design: "pre\<^sub>s \<dagger> (P \<turnstile> Q) = (\<not> pre\<^sub>s \<dagger> P)"
  by (simp add: design_def pre\<^sub>R_def usubst)

lemma peri\<^sub>s_design: "peri\<^sub>s \<dagger> (P \<turnstile> Q \<diamondop> R) = peri\<^sub>s \<dagger> (P \<Rightarrow> Q)"
  by (simp add: design_def usubst wait'_cond_def)

lemma post\<^sub>s_design: "post\<^sub>s \<dagger> (P \<turnstile> Q \<diamondop> R) = post\<^sub>s \<dagger> (P \<Rightarrow> R)"
  by (simp add: design_def usubst wait'_cond_def)

lemma cmt\<^sub>s_design: "cmt\<^sub>s \<dagger> (P \<turnstile> Q) = cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)"
  by (simp add: design_def usubst wait'_cond_def)

lemma pre\<^sub>s_R1 [usubst]: "pre\<^sub>s \<dagger> R1(P) = R1(pre\<^sub>s \<dagger> P)"
  by (simp add: R1_def usubst)

lemma pre\<^sub>s_R2c [usubst]: "pre\<^sub>s \<dagger> R2c(P) = R2c(pre\<^sub>s \<dagger> P)"
  by (simp add: R2c_def R2s_def usubst)

lemma peri\<^sub>s_R1 [usubst]: "peri\<^sub>s \<dagger> R1(P) = R1(peri\<^sub>s \<dagger> P)"
  by (simp add: R1_def usubst)

lemma peri\<^sub>s_R2c [usubst]: "peri\<^sub>s \<dagger> R2c(P) = R2c(peri\<^sub>s \<dagger> P)"
  by (simp add: R2c_def R2s_def usubst)

lemma post\<^sub>s_R1 [usubst]: "post\<^sub>s \<dagger> R1(P) = R1(post\<^sub>s \<dagger> P)"
  by (simp add: R1_def usubst)

lemma post\<^sub>s_R2c [usubst]: "post\<^sub>s \<dagger> R2c(P) = R2c(post\<^sub>s \<dagger> P)"
  by (simp add: R2c_def R2s_def usubst)

lemma cmt\<^sub>s_R1 [usubst]: "cmt\<^sub>s \<dagger> R1(P) = R1(cmt\<^sub>s \<dagger> P)"
  by (simp add: R1_def usubst)

lemma cmt\<^sub>s_R2c [usubst]: "cmt\<^sub>s \<dagger> R2c(P) = R2c(cmt\<^sub>s \<dagger> P)"
  by (simp add: R2c_def R2s_def usubst)

lemma pre_wait_false:
  "pre\<^sub>R(P\<lbrakk>false/$wait\<rbrakk>) = pre\<^sub>R(P)"
  by (rel_auto)

lemma cmt_wait_false:
  "cmt\<^sub>R(P\<lbrakk>false/$wait\<rbrakk>) = cmt\<^sub>R(P)"
  by (rel_auto)

lemma subst_tr_pre [usubst]:
  "\<lbrakk> $ok \<sharp> v; $ok\<acute> \<sharp> v; $wait \<sharp> v \<rbrakk> \<Longrightarrow> (pre\<^sub>R P)\<lbrakk>v/$tr\<rbrakk> = pre\<^sub>R (P\<lbrakk>v/$tr\<rbrakk>)"
  by (rel_auto)

lemma subst_tr_peri [usubst]:
  "\<lbrakk> $ok \<sharp> v; $ok\<acute> \<sharp> v; $wait \<sharp> v; $wait\<acute> \<sharp> v \<rbrakk> \<Longrightarrow> (peri\<^sub>R P)\<lbrakk>v/$tr\<rbrakk> = peri\<^sub>R (P\<lbrakk>v/$tr\<rbrakk>)"
  by (rel_auto)

lemma subst_tr_post [usubst]:
  "\<lbrakk> $ok \<sharp> v; $ok\<acute> \<sharp> v; $wait \<sharp> v; $wait\<acute> \<sharp> v \<rbrakk> \<Longrightarrow> (post\<^sub>R P)\<lbrakk>v/$tr\<rbrakk> = post\<^sub>R (P\<lbrakk>v/$tr\<rbrakk>)"
  by (rel_auto)

lemma rea_pre_RHS_design: "pre\<^sub>R(\<^bold>R\<^sub>s(P \<turnstile> Q)) = (\<not> R1(R2c(pre\<^sub>s \<dagger> (\<not> P))))"
  by (simp add: RHS_def usubst R3h_def pre\<^sub>R_def pre\<^sub>s_design)

lemma rea_cmt_RHS_design: "cmt\<^sub>R(\<^bold>R\<^sub>s(P \<turnstile> Q)) = R1(R2c(cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)))"
  by (simp add: RHS_def usubst R3h_def cmt\<^sub>R_def cmt\<^sub>s_design)

lemma rea_peri_RHS_design: "peri\<^sub>R(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = R1(R2c(peri\<^sub>s \<dagger> (P \<Rightarrow> Q)))"
  by (simp add:RHS_def usubst peri\<^sub>R_def R3h_def peri\<^sub>s_design)

lemma rea_post_RHS_design: "post\<^sub>R(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = R1(R2c(post\<^sub>s \<dagger> (P \<Rightarrow> R)))"
  by (simp add:RHS_def usubst post\<^sub>R_def R3h_def post\<^sub>s_design)

lemma rdes_export_cmt: "\<^bold>R\<^sub>s(P \<turnstile> cmt\<^sub>s \<dagger> Q) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (rel_auto)

lemma rdes_export_pre: "\<^bold>R\<^sub>s((P\<lbrakk>true,false/$ok,$wait\<rbrakk>) \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (rel_auto)

lemma RHS_design_pre_post_form:
  "\<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
proof -
  have "\<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f)\<lbrakk>true/$ok\<rbrakk> \<turnstile> P\<^sup>t\<^sub>f\<lbrakk>true/$ok\<rbrakk>)"
    by (simp add: design_subst_ok)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
    by (simp add: pre\<^sub>R_def cmt\<^sub>R_def usubst)
  finally show ?thesis .
qed

lemma SRD_as_reactive_design:
  "SRD(P) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
  by (simp add: RHS_design_pre_post_form SRD_RH_design_form)

lemma SRD_reactive_design_alt:
  assumes "P is SRD"
  shows "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) = P"
proof -
  have "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (simp add: RHS_design_pre_post_form)
  thus ?thesis
    by (simp add: SRD_reactive_design assms)
qed

lemma SRD_reactive_tri_design_lemma:
  "SRD(P) = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f\<lbrakk>true/$wait\<acute>\<rbrakk> \<diamondop> P\<^sup>t\<^sub>f\<lbrakk>false/$wait\<acute>\<rbrakk>)"
  by (simp add: SRD_RH_design_form wait'_cond_split)

lemma SRD_as_reactive_tri_design:
  "SRD(P) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
proof -
  have "SRD(P) = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f\<lbrakk>true/$wait\<acute>\<rbrakk> \<diamondop> P\<^sup>t\<^sub>f\<lbrakk>false/$wait\<acute>\<rbrakk>)"
    by (simp add: SRD_RH_design_form wait'_cond_split)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
    apply (simp add: usubst)
    apply (subst design_subst_ok_ok'[THEN sym])
    apply (simp add: pre\<^sub>R_def peri\<^sub>R_def post\<^sub>R_def usubst unrest)
  done
  finally show ?thesis .
qed

lemma SRD_reactive_tri_design:
  assumes "P is SRD"
  shows "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) = P"
  by (metis Healthy_if SRD_as_reactive_tri_design assms)

lemma RHS_tri_design_is_SRD:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok\<acute> \<sharp> R"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) is SRD"
  by (rule RHS_design_is_SRD, simp_all add: unrest assms)

lemma R1_neg_R2s_pre_RHS:
  assumes "P is SRD"
  shows "R1 (\<not> R2s(pre\<^sub>R(P))) = (\<not> (pre\<^sub>R(P)))"
proof -
  have "(\<not> pre\<^sub>R(P)) = (\<not> pre\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))))"
    by (simp add: SRD_reactive_tri_design assms)
  also have "... = R1(R2s(\<not> pre\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))))"
    by (rel_auto)
  also have "... = R1 (\<not> R2s(pre\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))))"
    by (simp add: R2s_not)
  also have "... = R1 (\<not> R2s(pre\<^sub>R(P)))"
    by (simp add: SRD_reactive_tri_design assms)
  finally show ?thesis ..
qed

lemma R1_R2s_cmt_SRD:
  assumes "P is SRD"
  shows "R1(R2s(cmt\<^sub>R(P))) = cmt\<^sub>R(P)"
  by (metis (no_types, hide_lams) Healthy_def R1_R2s_R2c R2_def R2_idem SRD_as_reactive_design assms rea_cmt_RHS_design)

lemma R1_R2s_peri_SRD:
  assumes "P is SRD"
  shows "R1(R2s(peri\<^sub>R(P))) = peri\<^sub>R(P)"
  by (metis (no_types, hide_lams) Healthy_def R1_R2s_R2c R2_def R2_idem RHS_def SRD_RH_design_form assms peri\<^sub>R_def peri\<^sub>s_R1 peri\<^sub>s_R2c)

lemma R1_R2s_post_SRD:
  assumes "P is SRD"
  shows "R1(R2s(post\<^sub>R(P))) = post\<^sub>R(P)"
  by (metis (no_types, hide_lams) Healthy_def R1_R2s_R2c R2_def R2_idem RHS_def SRD_RH_design_form assms post\<^sub>R_def post\<^sub>s_R1 post\<^sub>s_R2c)

lemma RHS_pre_lemma: "(\<^bold>R\<^sub>s P)\<^sup>f\<^sub>f = R1(R2c(P\<^sup>f\<^sub>f))"
  by (rel_auto)

lemma RHS_design_neg_R1_pre:
  "\<^bold>R\<^sub>s ((\<not> R1 P) \<turnstile> R) = \<^bold>R\<^sub>s ((\<not> P) \<turnstile> R)"
  by (rel_auto)

lemma RHS_design_conj_neg_R1_pre:
  "\<^bold>R\<^sub>s (((\<not> R1 P) \<and> Q) \<turnstile> R) = \<^bold>R\<^sub>s (((\<not> P) \<and> Q) \<turnstile> R)"
  by (rel_auto)

lemma RHS_design_R2c_pre:
  "\<^bold>R\<^sub>s(R2c(P) \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (rel_auto)

lemma UINF_R1_neg_R2s_pre_RHS:
  assumes "A \<subseteq> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  shows "(\<Sqinter> P \<in> A \<bullet> R1 (\<not> R2s (pre\<^sub>R P))) = (\<Sqinter> P \<in> A \<bullet> \<not> (pre\<^sub>R P))"
  by (rule UINF_cong[of A], metis (no_types, lifting) Ball_Collect R1_neg_R2s_pre_RHS assms)

lemma USUP_R1_R2s_cmt_SRD:
  assumes "A \<subseteq> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  shows "(\<Squnion> P \<in> A \<bullet> R1 (R2s (cmt\<^sub>R P))) = (\<Squnion> P \<in> A \<bullet> cmt\<^sub>R P)"
  by (rule USUP_cong[of A], metis (mono_tags, lifting) Ball_Collect R1_R2s_cmt_SRD assms)

lemma UINF_R1_R2s_cmt_SRD:
  assumes "A \<subseteq> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  shows "(\<Sqinter> P \<in> A \<bullet> R1 (R2s (cmt\<^sub>R P))) = (\<Sqinter> P \<in> A \<bullet> cmt\<^sub>R P)"
  by (rule UINF_cong[of A], metis (mono_tags, lifting) Ball_Collect R1_R2s_cmt_SRD assms)

lemma SRD_composition:
  assumes "P is SRD" "Q is SRD"
  shows "(P ;; Q) = \<^bold>R\<^sub>s ((\<not> ((\<not> pre\<^sub>R P) ;; R1 true) \<and> \<not> ((post\<^sub>R P \<and> \<not> $wait\<acute>) ;; (\<not> pre\<^sub>R Q))) \<turnstile>
                       ((\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; post\<^sub>R Q))"
proof -
  have "(P ;; Q) = (\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) ;; \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q)))"
    by (simp add: SRD_reactive_tri_design assms(1) assms(2))
  also from assms have "... = \<^bold>R\<^sub>s ((\<not> ((\<not> pre\<^sub>R P) ;; R1 true) \<and> \<not> ((post\<^sub>R P \<and> \<not> $wait\<acute>) ;; (\<not> pre\<^sub>R Q))) \<turnstile>
        ((\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; post\<^sub>R Q))"
    by (simp add: RHS_tri_design_composition unrest R1_R2s_peri_SRD R1_R2s_post_SRD R1_neg_R2s_pre_RHS)
  finally show ?thesis .
qed

lemma SRD_seqr_closure:
  assumes "P is SRD" "Q is SRD"
  shows "(P ;; Q) is SRD"
proof -
  have "(P ;; Q) = \<^bold>R\<^sub>s ((\<not> ((\<not> pre\<^sub>R P) ;; R1 true) \<and> \<not> ((post\<^sub>R P \<and> \<not> $wait\<acute>) ;; (\<not> pre\<^sub>R Q))) \<turnstile>
                       ((\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; post\<^sub>R Q))"
    by (simp add: SRD_composition assms(1) assms(2))
  also have "... is SRD"
    by (simp add: RHS_design_is_SRD add: unrest)
  finally show ?thesis .
qed

subsection {* Reactive design signature *}

definition srdes_skip :: "('s,'t::ordered_cancel_monoid_diff,'\<alpha>) hrel_rsp" ("II\<^sub>R") where
[upred_defs]: "II\<^sub>R = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> \<lceil>II\<rceil>\<^sub>R))"

abbreviation Chaos :: "('s,'t::ordered_cancel_monoid_diff,'\<alpha>) hrel_rsp" where
"Chaos \<equiv> \<^bold>\<bottom>\<^bsub>SRDES\<^esub>"

abbreviation Miracle :: "('s,'t::ordered_cancel_monoid_diff,'\<alpha>) hrel_rsp" where
"Miracle \<equiv> \<^bold>\<top>\<^bsub>SRDES\<^esub>"

lemma Chaos_def: "Chaos = \<^bold>R\<^sub>s(false \<turnstile> true)"
proof -
  have "Chaos = SRD(true)"
    by (metis srdes_hcond_def srdes_theory_continuous.healthy_bottom)
  also have "... = \<^bold>R\<^sub>s(\<^bold>H(true))"
    by (simp add: SRD_RHS_H1_H2)
  also have "... = \<^bold>R\<^sub>s(false \<turnstile> true)"
    by (metis H1_design H2_true design_false_pre)
  finally show ?thesis .
qed

lemma Miracle_def: "Miracle = \<^bold>R\<^sub>s(true \<turnstile> false)"
proof -
  have "Miracle = SRD(false)"
    by (metis srdes_hcond_def srdes_theory_continuous.healthy_top)
  also have "... = \<^bold>R\<^sub>s(\<^bold>H(false))"
    by (simp add: SRD_RHS_H1_H2)
  also have "... = \<^bold>R\<^sub>s(true \<turnstile> false)"
    by (metis (no_types, lifting) H1_H2_eq_design p_imp_p subst_impl subst_not utp_pred.compl_bot_eq utp_pred.compl_top_eq)
  finally show ?thesis .
qed

thm srdes_theory_continuous.weak.bottom_lower
thm srdes_theory_continuous.weak.top_higher
thm srdes_theory_continuous.meet_bottom
thm srdes_theory_continuous.meet_top

lemma Miracle_left_zero:
  assumes "P is SRD"
  shows "Miracle ;; P = Miracle"
proof -
  have "Miracle ;; P = \<^bold>R\<^sub>s(true \<turnstile> false) ;; \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
    by (simp add: Miracle_def SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s(true \<turnstile> false)"
    by (simp add: RHS_design_composition unrest R1_false R2s_false R2s_true)
  also have "... = Miracle"
    by (simp add: Miracle_def)
  finally show ?thesis .
qed

lemma Chaos_left_zero:
  assumes "P is SRD"
  shows "(Chaos ;; P) = Chaos"
proof -
  have "Chaos ;; P = \<^bold>R\<^sub>s(false \<turnstile> true) ;; \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
    by (simp add: Chaos_def SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s ((\<not> R1 true \<and> \<not> (R1 true \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s (pre\<^sub>R P))) \<turnstile>
                       (R1 true ;; (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s (cmt\<^sub>R P))))"
    by (simp add: RHS_design_composition unrest R2s_false R2s_true R1_false R1_true_comp)
  also have "... = \<^bold>R\<^sub>s ((false \<and> \<not> (R1 true \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s (pre\<^sub>R P))) \<turnstile>
                       (R1 true ;; (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s (cmt\<^sub>R P))))"
    by (simp add: RHS_design_conj_neg_R1_pre)
  also have "... = \<^bold>R\<^sub>s(true)"
    by (simp add: design_false_pre)
  also have "... = \<^bold>R\<^sub>s(false \<turnstile> true)"
    by (simp add: design_def)
  also have "... = Chaos"
    by (simp add: Chaos_def)
  finally show ?thesis .
qed

lemma RHS_design_choice: "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1) \<sqinter> \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2) = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<or> Q\<^sub>2))"
  by (metis RHS_inf design_choice)

lemma RHS_tri_design_choice: "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<sqinter> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) = \<^bold>R\<^sub>s((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> (P\<^sub>2 \<or> Q\<^sub>2) \<diamondop> (P\<^sub>3 \<or> Q\<^sub>3))"
  apply (simp add: RHS_design_choice)
  apply (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"])
  apply (simp)
  apply (rel_auto)
done

lemma RHS_design_USUP:
  assumes "A \<noteq> {}"
  shows "(\<Sqinter> i \<in> A \<bullet> \<^bold>R\<^sub>s(P(i) \<turnstile> Q(i))) = \<^bold>R\<^sub>s((\<Squnion> i \<in> A \<bullet> P(i)) \<turnstile> (\<Sqinter> i \<in> A \<bullet> Q(i)))"
  by (subst RHS_INF[OF assms, THEN sym], simp add: design_USUP assms)

lemma RHS_design_left_unit:
  assumes "P is SRD"
  shows "II\<^sub>R ;; P = P"
proof -
  have "II\<^sub>R ;; P = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> \<lceil>II\<rceil>\<^sub>R)) ;; \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
    by (simp add: SRD_reactive_design_alt assms srdes_skip_def)
  also have "... =  \<^bold>R\<^sub>s ((\<not> (($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> \<lceil>II\<rceil>\<^sub>R) \<and> \<not> $wait\<acute>) ;; (\<not> pre\<^sub>R P)) \<turnstile>
                        (($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> \<lceil>II\<rceil>\<^sub>R) ;; (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> cmt\<^sub>R P))"
    by (simp add: RHS_design_composition unrest R2s_true R1_false R1_R2s_cmt_SRD R2s_wait' R2s_not
                  R1_neg_R2s_pre_RHS assms R2s_conj R1_extend_conj R1_R2s_tr'_eq_tr R2s_lift_rea)
  also have "... =  \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile>
                        (($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> \<lceil>II\<rceil>\<^sub>R) ;; (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> cmt\<^sub>R P))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... =  \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> (($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R) ;; cmt\<^sub>R P))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... =  \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> cmt\<^sub>R P)"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis
    by (simp add: SRD_reactive_design_alt assms)
qed

lemma RHS_design_right_unit_lemma:
  assumes "P is SRD"
  shows "P ;; II\<^sub>R = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> cmt\<^sub>R P))"
proof -
  have "P ;; II\<^sub>R = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) ;; \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> \<lceil>II\<rceil>\<^sub>R))"
    by (simp add: SRD_reactive_design_alt assms srdes_skip_def)
  also have "... = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile>
                       (cmt\<^sub>R P ;; (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> \<lceil>II\<rceil>\<^sub>R)))"
    by (simp add: RHS_design_composition unrest R2s_true R1_false R1_R2s_cmt_SRD R2s_wait' R2s_not
                  R1_neg_R2s_pre_RHS assms R2s_conj R1_extend_conj R1_R2s_tr'_eq_tr R2s_lift_rea)
  also have "... = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> cmt\<^sub>R P))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

lemma RHS_design_right_Chaos_lemma:
  assumes "P is SRD"
  shows "P ;; Chaos = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true \<and> \<not> (cmt\<^sub>R P \<and> \<not> $wait\<acute>) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<and> $wait\<acute>))"
proof -
  have "P ;; Chaos = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) ;; \<^bold>R\<^sub>s(false \<turnstile> false)"
    by (simp add: Chaos_def SRD_reactive_design_alt assms design_false_pre)
  also have "... = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true \<and> \<not> (cmt\<^sub>R P \<and> \<not> $wait\<acute>) ;; R1 true) \<turnstile> (cmt\<^sub>R P ;; ($wait \<and> (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D))))"
    by (simp add: RHS_design_composition unrest R2s_true R1_false R1_R2s_cmt_SRD R2s_wait' R2s_false R2s_not
                  R1_neg_R2s_pre_RHS assms R2s_conj R1_extend_conj R1_R2s_tr'_eq_tr R2s_lift_rea)
       (simp add: cond_def)
  also have "... = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true \<and> \<not> (cmt\<^sub>R P \<and> \<not> $wait\<acute>) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<and> $wait\<acute>))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

lemma RHS_design_right_Miracle_lemma:
  assumes "P is SRD"
  shows "P ;; Miracle = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<and> $wait\<acute>))"
proof -
  have "P ;; Miracle = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) ;; \<^bold>R\<^sub>s(true \<turnstile> false)"
    by (simp add: Miracle_def SRD_reactive_design_alt assms design_false_pre)
  also have "... = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile> (cmt\<^sub>R P ;; ($wait \<and> (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D))))"
    by (simp add: RHS_design_composition unrest R2s_true R1_false R1_R2s_cmt_SRD R2s_wait' R2s_false R2s_not
                  R1_neg_R2s_pre_RHS assms R2s_conj R1_extend_conj R1_R2s_tr'_eq_tr R2s_lift_rea)
       (simp add: cond_def)
  also have "... = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<and> $wait\<acute>))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

subsection {* Reactive design parallel-by-merge *}

definition [upred_defs]: "nil\<^sub>r\<^sub>m = (nil\<^sub>m \<triangleleft> $0-ok \<and> $1-ok \<triangleright> ($tr\<^sub>< \<le>\<^sub>u $tr\<acute>))"

text {* @{term "nil\<^sub>r\<^sub>m"} is the parallel system which does nothing if the parallel predicates have both
  terminated ($0.ok \wedge 1.ok$), and otherwise guarantees only the merged trace gets longer. *}

definition [upred_defs]: "div\<^sub>m = ($tr \<le>\<^sub>u $0-tr\<acute> \<and> $tr \<le>\<^sub>u $1-tr\<acute> \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>)"

text {* @{term "div\<^sub>m"} is the parallel system where both sides traces get longer than the initial
  trace and identifies the before values of the variables. *}

definition [upred_defs]: "wait\<^sub>m = (((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>0) \<and> (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>1) \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>)\<lbrakk>true,true/$ok,$wait\<rbrakk>)"

text {* @{term "wait\<^sub>m"} is the parallel system where ok and wait are both true and all other variables
  are identified, except for the state which is hidden in both the left and right.*}

text {* R3h implicitly depends on RD1, and therefore it requires that both sides be RD1. We also
  require that both sides are R3c, and that @{term "wait\<^sub>m"} is a quasi-unit, and @{term "div\<^sub>m"} yields
  divergence. *}

lemma st_U0_alpha: "\<lceil>\<exists> $st \<bullet> II\<rceil>\<^sub>0 = (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>0)"
  by (rel_auto)

lemma st_U1_alpha: "\<lceil>\<exists> $st \<bullet> II\<rceil>\<^sub>1 = (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>1)"
  by (rel_auto)

lemma U0_skip: "\<lceil>II\<rceil>\<^sub>0 = ($0-\<Sigma>\<acute> =\<^sub>u $\<Sigma>)"
  by (rel_auto)

lemma U1_skip: "\<lceil>II\<rceil>\<^sub>1 = ($1-\<Sigma>\<acute> =\<^sub>u $\<Sigma>)"
  by (rel_auto)

lemma R3h_par_by_merge:
  assumes
    "P is R1" "Q is R1" "P is RD1" "Q is RD1" "P is R3h" "Q is R3h"
    "(wait\<^sub>m ;; M) = ((\<exists> $st \<bullet> II)\<lbrakk>true,true/$ok,$wait\<rbrakk>)" "(div\<^sub>m ;; M) = R1(true)"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is R3h"
proof -
  have "(P \<parallel>\<^bsub>M\<^esub> Q) = (((P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true/$ok\<rbrakk> \<triangleleft> $ok \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk>)\<lbrakk>true/$wait\<rbrakk> \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (simp add: cond_idem cond_var_subst_left cond_var_subst_right)
  also have "... = (((P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true,true/$ok,$wait\<rbrakk> \<triangleleft> $ok \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk>)\<lbrakk>true/$wait\<rbrakk> \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (rel_auto)
  also have "... = (((P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true,true/$ok,$wait\<rbrakk> \<triangleleft> $ok \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk>) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (simp add: cond_var_subst_left)
  also have "... = (((\<exists> $st \<bullet> II)\<lbrakk>true,true/$ok,$wait\<rbrakk> \<triangleleft> $ok \<triangleright> R1(true)) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
  proof -
    have "(P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk> = R1(true)"
    proof -
      have "(P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk> = ((P \<triangleleft> $ok \<triangleright> R1(true)) \<parallel>\<^bsub>M\<^esub> (Q \<triangleleft> $ok \<triangleright> R1(true)))\<lbrakk>false/$ok\<rbrakk>"
        by (metis RD1_alt_def Healthy_if assms)
      also have "... = (R1(true) \<parallel>\<^bsub>M\<lbrakk>false/$ok\<^sub><\<rbrakk>\<^esub> R1(true))"
        by (rel_auto, metis, metis)
      also have "... = (div\<^sub>m ;; M)\<lbrakk>false/$ok\<rbrakk>"
        by (rel_auto, metis, metis)
      also have "... = (R1(true))\<lbrakk>false/$ok\<rbrakk>"
        by (simp add: assms(8))
      also have "... = (R1(true))"
        by (rel_auto)
      finally show ?thesis
        by simp
    qed
    moreover have "(P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true,true/$ok,$wait\<rbrakk> = (\<exists> $st \<bullet> II)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
    proof -
      have "(P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true,true/$ok,$wait\<rbrakk> = (P\<lbrakk>true,true/$ok,$wait\<rbrakk> \<parallel>\<^bsub>M\<^esub> Q\<lbrakk>true,true/$ok,$wait\<rbrakk>)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
        by (rel_auto)
      also have "... = ((((\<exists> $st \<bullet> II) \<triangleleft> $ok \<triangleright> R1(true)) \<triangleleft> $wait \<triangleright> P)\<lbrakk>true,true/$ok,$wait\<rbrakk> \<parallel>\<^bsub>M\<^esub> (((\<exists> $st \<bullet> II) \<triangleleft> $ok \<triangleright> R1(true)) \<triangleleft> $wait \<triangleright> Q)\<lbrakk>true,true/$ok,$wait\<rbrakk>)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
        by (metis Healthy_def' R3h_cases assms(5) assms(6))
      also have "... = ((\<exists> $st \<bullet> II)\<lbrakk>true,true/$ok,$wait\<rbrakk> \<parallel>\<^bsub>M\<^esub> (\<exists> $st \<bullet> II)\<lbrakk>true,true/$ok,$wait\<rbrakk>)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
        by (subst_tac)
      also have "... = ((\<exists> $st \<bullet> II) \<parallel>\<^bsub>M\<^esub> (\<exists> $st \<bullet> II))\<lbrakk>true,true/$ok,$wait\<rbrakk>"
        by (simp add: par_by_merge_def usubst)
      also have "... = (((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>0) \<and> (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>1) \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) ;; M)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
        by (simp add: par_by_merge_def U0_as_alpha U1_as_alpha alpha st_U0_alpha st_U1_alpha skip\<^sub>m_def)
      also have "... = (wait\<^sub>m ;; M)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
        by (rel_auto)
      also have "... = (\<exists> $st \<bullet> II)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
        by (simp add: assms usubst)
      finally show ?thesis .
    qed
    ultimately show ?thesis by simp
  qed
  also have "... = (((\<exists> $st \<bullet> II) \<triangleleft> $ok \<triangleright> R1(true)) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (rel_auto)
  also have "... = R3h(P \<parallel>\<^bsub>M\<^esub> Q)"
    by (simp add: R3h_cases)
  finally show ?thesis
    by (simp add: Healthy_def')
qed

lemma RD1_par_by_merge:
  assumes "P is R1" "Q is R1" "P is RD1" "Q is RD1" "M is R1m" "(div\<^sub>m ;; M) = R1(true)"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RD1"
proof -
  have "(P \<parallel>\<^bsub>M\<^esub> Q) = ((P \<parallel>\<^bsub>M\<^esub> Q) \<triangleleft> $ok \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk>)"
    by (simp add: cond_idem cond_var_subst_right)
  also have "... = ((P \<parallel>\<^bsub>M\<^esub> Q) \<triangleleft> $ok \<triangleright> R1(true))"
  proof -
    have "(P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk> = ((P \<triangleleft> $ok \<triangleright> R1(true)) \<parallel>\<^bsub>M\<^esub> (Q \<triangleleft> $ok \<triangleright> R1(true)))\<lbrakk>false/$ok\<rbrakk>"
      by (metis RD1_alt_def Healthy_if assms)
    also have "... = (R1(true) \<parallel>\<^bsub>M\<lbrakk>false/$ok\<^sub><\<rbrakk>\<^esub> R1(true))"
      by (rel_auto, metis, metis)
    also have "... = (div\<^sub>m ;; M)\<lbrakk>false/$ok\<rbrakk>"
      by (rel_auto, metis, metis)
    also have "... = (R1(true))\<lbrakk>false/$ok\<rbrakk>"
      by (simp add: assms(6))
    also have "... = (R1(true))"
      by (rel_auto)
    finally show ?thesis
      by simp
  qed
  finally show ?thesis
    by (metis RD1_alt_def Healthy_def R1_par_by_merge assms(5))
qed

lemma RD2_par_by_merge:
  assumes "M is RD2"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RD2"
proof -
  have "(P \<parallel>\<^bsub>M\<^esub> Q) = ((P \<parallel>\<^sub>s Q) ;; M)"
    by (simp add: par_by_merge_def)
  also from assms have "... = ((P \<parallel>\<^sub>s Q) ;; (M ;; J))"
    by (simp add: Healthy_def' RD2_def H2_def)
  also from assms have "... = (((P \<parallel>\<^sub>s Q) ;; M) ;; J)"
    by (meson seqr_assoc)
  also from assms have "... = RD2(P \<parallel>\<^bsub>M\<^esub> Q)"
    by (simp add: RD2_def H2_def par_by_merge_def)
  finally show ?thesis
    by (simp add: Healthy_def')
qed

subsection {* Simple parallel composition *}

definition rea_design_par ::
  "('s, 't::ordered_cancel_monoid_diff, '\<alpha>) hrel_rsp \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp" (infixr "\<parallel>\<^sub>R" 85)
where [upred_defs]: "P \<parallel>\<^sub>R Q = \<^bold>R\<^sub>s((pre\<^sub>R(P)  \<and> pre\<^sub>R(Q)) \<turnstile> (cmt\<^sub>R(P) \<and> cmt\<^sub>R(Q)))"

lemma RHS_design_par:
  assumes
    "$ok\<acute> \<sharp> P\<^sub>1" "$wait \<sharp> P\<^sub>1" "$ok\<acute> \<sharp> P\<^sub>2" "$wait \<sharp> P\<^sub>2"
    "$wait \<sharp> Q\<^sub>1" "$wait \<sharp> Q\<^sub>2"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1) \<parallel>\<^sub>R \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2) = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<and> Q\<^sub>2))"
proof -
  have "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1) \<parallel>\<^sub>R \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2) =
        \<^bold>R\<^sub>s((\<not> R1 (R2c (\<not> P\<^sub>1)) \<and> \<not> R1 (R2c (\<not> P\<^sub>2))) \<turnstile>
           (R1 (R2s (P\<^sub>1 \<Rightarrow> Q\<^sub>1)) \<and> R1 (R2s (P\<^sub>2 \<Rightarrow> Q\<^sub>2))))"
    by (simp add: rea_design_par_def rea_pre_RHS_design rea_cmt_RHS_design usubst assms
       ,rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... =
        \<^bold>R\<^sub>s((\<not> R2c (\<not> P\<^sub>1) \<and> \<not> R2c (\<not> P\<^sub>2)) \<turnstile>
           (R1 (R2s (P\<^sub>1 \<Rightarrow> Q\<^sub>1)) \<and> R1 (R2s (P\<^sub>2 \<Rightarrow> Q\<^sub>2))))"
    by (metis (no_types, lifting) R1_disj RHS_design_neg_R1_pre utp_pred.compl_sup)
  also have "... =
        \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (R1 (R2s (P\<^sub>1 \<Rightarrow> Q\<^sub>1)) \<and> R1 (R2s (P\<^sub>2 \<Rightarrow> Q\<^sub>2))))"
    by (simp add: R2c_R3h_commute R2c_and R2c_design R2c_idem R2c_not RHS_def)
  also have "... = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> ((P\<^sub>1 \<Rightarrow> Q\<^sub>1) \<and> (P\<^sub>2 \<Rightarrow> Q\<^sub>2)))"
    by (metis (no_types, lifting) R1_conj R2s_conj RHS_design_export_R1 RHS_design_export_R2s)
  also have "... = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<and> Q\<^sub>2))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

lemma RHS_tri_design_par:
  assumes
    "$ok\<acute> \<sharp> P\<^sub>1" "$wait \<sharp> P\<^sub>1" "$ok\<acute> \<sharp> P\<^sub>2" "$wait \<sharp> P\<^sub>2"
    "$wait \<sharp> Q\<^sub>1" "$wait \<sharp> Q\<^sub>2"
    "$wait \<sharp> R\<^sub>1" "$wait \<sharp> R\<^sub>2"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1 \<diamondop> R\<^sub>1) \<parallel>\<^sub>R \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2 \<diamondop> R\<^sub>2) = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<and> Q\<^sub>2) \<diamondop> (R\<^sub>1 \<and> R\<^sub>2))"
  by (simp add: RHS_design_par assms unrest wait'_cond_conj_exchange)

end

(*
lemma R1_R3c_commute: "R1(R3c(P)) = R3c(R1(P))"
  by (rel_auto)

lemma R1_R3h_commute: "R1(R3h(P)) = R3h(R1(P))"
  by (rel_auto)

lemma R2_R3c_commute: "R2(R3c(P)) = R3c(R2(P))"
  apply (rel_auto)
  using minus_zero_eq apply blast+
done

lemma R2_R3h_commute: "R2(R3h(P)) = R3h(R2(P))"
  apply (rel_auto)
  using minus_zero_eq apply blast+
done

lemma R2c_R3c_commute: "R2c(R3c(P)) = R3c(R2c(P))"
  by (simp add: R3c_def R2c_condr R2c_wait R2c_skip_rea)

lemma R2c_ex_st': "R2c(\<exists> $st \<bullet> P) = (\<exists> $st \<bullet> R2c(P))"
  by (rel_auto)

lemma R2c_R3h_commute: "R2c(R3h(P)) = R3h(R2c(P))"
  by (simp add: R3h_def R2c_condr R2c_wait R2c_ex_st' R2c_skip_rea)

lemma R1_H1_R3c_commute:
  "R1(H1(R3c(P))) = R3c(R1(H1(P)))"
  by (rel_auto)

lemma R1_H1_R3h_commute:
  "R1(H1(R3h(P))) = R3h(R1(H1(P)))"
  by (rel_auto)

lemma R3c_H2_commute: "R3c(H2(P)) = H2(R3c(P))"
  by (simp add: H2_split R3c_def usubst, rel_auto)

lemma R3h_H2_commute: "R3h(H2(P)) = H2(R3h(P))"
  by (simp add: H2_split R3h_def usubst, rel_auto)

lemma R3c_idem: "R3c(R3c(P)) = R3c(P)"
  by (rel_auto)

lemma R3c_Idempotent: "Idempotent R3c"
  using Idempotent_def R3c_idem by blast

lemma R3c_mono: "P \<sqsubseteq> Q \<Longrightarrow> R3c(P) \<sqsubseteq> R3c(Q)"
  by (rel_auto)

lemma R3c_Monotonic: "Monotonic R3c"
  by (simp add: Monotonic_def R3c_mono)

lemma R3h_idem: "R3h(R3h(P)) = R3h(P)"
  by (rel_auto)

lemma R3h_Idempotent: "Idempotent R3h"
  using Idempotent_def R3h_idem by blast

lemma R3h_mono: "P \<sqsubseteq> Q \<Longrightarrow> R3h(P) \<sqsubseteq> R3h(Q)"
  by (rel_auto)

lemma R3h_Monotonic: "Monotonic R3h"
  by (simp add: Monotonic_def R3h_mono)

lemma R3c_conj: "R3c(P \<and> Q) = (R3c(P) \<and> R3c(Q))"
  by (rel_auto)

lemma R3c_disj: "R3c(P \<or> Q) = (R3c(P) \<or> R3c(Q))"
  by (rel_auto)

lemma R3c_USUP:
  assumes "A \<noteq> {}"
  shows "R3c(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> R3c(P(i)))"
  using assms by (rel_auto)

lemma R3c_UINF:
  assumes "A \<noteq> {}"
  shows "R3c(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> R3c(P(i)))"
  using assms by (rel_auto)

lemma R3h_conj: "R3h(P \<and> Q) = (R3h(P) \<and> R3h(Q))"
  by (rel_auto)

lemma R3h_disj: "R3h(P \<or> Q) = (R3h(P) \<or> R3h(Q))"
  by (rel_auto)

lemma R3h_USUP:
  assumes "A \<noteq> {}"
  shows "R3h(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> R3h(P(i)))"
  using assms by (rel_auto)

lemma R3h_UINF:
  assumes "A \<noteq> {}"
  shows "R3h(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> R3h(P(i)))"
  using assms by (rel_auto)

lemma R3c_refines_R3h: "R3h(P) \<sqsubseteq> R3c(P)"
  by (rel_auto)



lemma R3c_absorbs_R3h: "R3c(R3h(P)) = R3c(P)"
  by (rel_auto)

lemma R3h_absorbs_R3c: "R3h(R3c(P)) = R3h(P)"
  by (rel_auto)

lemma R1_skip_rea3: "R1(II\<^sub>R) = II\<^sub>R"
  by (rel_auto)

definition RH_def [upred_defs]: "RH(P) = R1(R2c(R3(P)))"
definition RHS_def [upred_defs]: "RHS(P) = R1(R2s(R3h(P)))"

notation RH ("\<^bold>R")
notation RHS ("\<^bold>R\<^sub>s")

definition reactive_sup :: "_ set \<Rightarrow> _" ("\<Sqinter>\<^sub>r") where
"\<Sqinter>\<^sub>r A = (if (A = {}) then \<^bold>R(false) else \<Sqinter> A)"

definition reactive_inf :: "_ set \<Rightarrow> _" ("\<Squnion>\<^sub>r") where
"\<Squnion>\<^sub>r A = (if (A = {}) then \<^bold>R(true) else \<Squnion> A)"

lemma RH_alt_def:
  "\<^bold>R(P) = R1(R2(R3c(P)))"
  by (simp add: R1_idem R2_def RH_def)

lemma RH_alt_def':
  "\<^bold>R(P) = R2(R3c(P))"
  by (simp add: R2_def RH_def)

lemma RH_alt_def'':
  "\<^bold>R(P) = R1(R2c(R3c(P)))"
  by (simp add: R1_R2s_R2c RH_def)

lemma RHS_alt_def:
  "\<^bold>R\<^sub>s(P) = R1(R2c(R3h(P)))"
  by (simp add: RHS_def R1_R2s_R2c)

lemma RH_idem:
  "\<^bold>R(\<^bold>R(P)) = \<^bold>R(P)"
  by (metis R2_R3c_commute R2_def R2_idem R3c_idem RH_def)

lemma RH_Idempotent: "Idempotent \<^bold>R"
  by (simp add: Idempotent_def RH_idem)

lemma RH_monotone:
  "P \<sqsubseteq> Q \<Longrightarrow> \<^bold>R(P) \<sqsubseteq> \<^bold>R(Q)"
  by (rel_auto)

lemma RHS_idem:
  "\<^bold>R\<^sub>s(\<^bold>R\<^sub>s(P)) = \<^bold>R\<^sub>s(P)"
  by (metis (no_types, hide_lams) R2_R3h_commute R2_def R2_idem R3h_idem RHS_def)

lemma RHS_Idempotent: "Idempotent \<^bold>R\<^sub>s"
  by (simp add: Idempotent_def RHS_idem)

lemma RHS_monotone:
  "P \<sqsubseteq> Q \<Longrightarrow> \<^bold>R\<^sub>s(P) \<sqsubseteq> \<^bold>R\<^sub>s(Q)"
  by (rel_auto)

lemma RH_disj: "\<^bold>R(P \<or> Q) = (\<^bold>R(P) \<or> \<^bold>R(Q))"
  by (simp add: RH_def R3c_disj R2s_disj R1_disj)

lemma RH_USUP:
  assumes "A \<noteq> {}"
  shows "\<^bold>R(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> \<^bold>R(P(i)))"
  using assms by (rel_auto)

lemma RH_UINF:
  assumes "A \<noteq> {}"
  shows "\<^bold>R(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> \<^bold>R(P(i)))"
  using assms by (rel_auto)

lemma RH_intro:
  "\<lbrakk> P is R1; P is R2; P is R3c \<rbrakk> \<Longrightarrow> P is \<^bold>R"
  by (simp add: Healthy_def' R2_def RH_def)

lemma R1_true_left_zero_R: "(R1(true) ;; \<^bold>R(P)) = R1(true)"
  by (rel_auto)

lemma RH_seq_closure:
  assumes "P is \<^bold>R" "Q is \<^bold>R"
  shows "(P ;; Q) is \<^bold>R"
proof (rule RH_intro)
  show "(P ;; Q) is R1"
    by (metis Healthy_def' R1_seqr_closure R2_def RH_alt_def RH_def assms(1) assms(2))
  show "(P ;; Q) is R2"
    by (metis Healthy_def' R2_def R2_idem R2_seqr_closure RH_def assms(1) assms(2))
  show "(P ;; Q) is R3c"
    by (metis Healthy_def' R2_R3c_commute R2_def R3c_idem R3c_seq_closure RH_alt_def RH_def assms(1) assms(2))
qed

lemma RH_R2c_def: "\<^bold>R(P) = R1(R2c(R3c(P)))"
  by (rel_auto)

lemma RHS_R2c_def: "\<^bold>R\<^sub>s(P) = R1(R2c(R3h(P)))"
  by (rel_auto)

lemma RH_absorbs_R2c: "\<^bold>R(R2c(P)) = \<^bold>R(P)"
  by (metis R1_R2_commute R1_R2c_is_R2 R1_R3c_commute R2_R3c_commute R2_idem RH_alt_def RH_alt_def')

lemma RH_subst_wait: "\<^bold>R(P \<^sub>f) = \<^bold>R(P)"
  by (metis R3c_subst_wait RH_alt_def')

lemma RH_false: "\<^bold>R(false) = ($wait \<and> II\<^sub>r)"
  by (rel_auto, metis minus_zero_eq)

lemma RH_true: "\<^bold>R(true) = (II\<^sub>r \<triangleleft> $wait \<triangleright> $tr \<le>\<^sub>u $tr\<acute>)"
  by (rel_auto, metis minus_zero_eq)

lemma RH_false_top:
  "\<^bold>R(P) \<sqsubseteq> \<^bold>R(false)"
  by (simp add: RH_monotone)

lemma RH_false_bottom:
  "\<^bold>R(true) \<sqsubseteq> \<^bold>R(P)"
  by (simp add: RH_monotone)

lemma
  assumes "P is R3"
  shows "R1 (H1 (P)) is R3c"
proof -
  have "R1(H1(R3(P))) = R3c(R1(H1(P)))"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def' assms)
qed

subsection {* Commutativity properties *}

lemma H2_R1_comm: "H2(R1(P)) = R1(H2(P))"
  by (rel_auto)

lemma H2_R2s_comm: "H2(R2s(P)) = R2s(H2(P))"
  by (rel_auto)

lemma H2_R2_comm: "H2(R2(P)) = R2(H2(P))"
  by (simp add: H2_R1_comm H2_R2s_comm R2_def)

lemma H2_R3_comm: "H2(R3c(P)) = R3c(H2(P))"
  by (simp add: R3c_H2_commute)

lemma H2_R3h_comm: "H2(R3h(P)) = R3h(H2(P))"
  by (rel_auto)

lemma R3c_via_H1: "R1(R3c(H1(P))) = R1(H1(R3(P)))"
  by (rel_auto)

lemma skip_rea_via_H1: "II\<^sub>r = R1(H1(R3(II)))"
  by (rel_auto)

lemma R1_true_left_zero_R: "(R1(true) ;; \<^bold>R(P)) = R1(true)"
  by (rel_auto)

lemma skip_rea_R1_lemma: "II\<^sub>r = R1($ok \<Rightarrow> II)"
  by (rel_auto)

lemma skip_rea_R1_dskip: "II\<^sub>r = R1(II\<^sub>D)"
  by (rel_auto)

subsection {* Reactive design composition *}

text {* Pedro's proof for R1 design composition *}

lemma R1_design_composition:
  fixes P Q :: "('t::ordered_cancel_monoid_diff,'\<alpha>,'\<beta>) relation_rp"
  and R S :: "('t,'\<beta>,'\<gamma>) relation_rp"
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows
  "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) =
   R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; R1(\<not> R))) \<turnstile> (R1(Q) ;; R1(S)))"
proof -
  have "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) = (\<^bold>\<exists> ok\<^sub>0 \<bullet> (R1(P \<turnstile> Q))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<acute>\<rbrakk> ;; (R1(R \<turnstile> S))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<rbrakk>)"
    using seqr_middle vwb_lens_ok by blast
  also from assms have "... = (\<^bold>\<exists> ok\<^sub>0 \<bullet> R1(($ok \<and> P) \<Rightarrow> (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> Q)) ;; R1((\<guillemotleft>ok\<^sub>0\<guillemotright>  \<and> R) \<Rightarrow> ($ok\<acute> \<and> S)))"
    by (simp add: design_def R1_def usubst unrest)
  also from assms have "... = ((R1(($ok \<and> P) \<Rightarrow> (true \<and> Q)) ;; R1((true \<and> R) \<Rightarrow> ($ok\<acute> \<and> S)))
                             \<or> (R1(($ok \<and> P) \<Rightarrow> (false \<and> Q)) ;; R1((false \<and> R) \<Rightarrow> ($ok\<acute> \<and> S))))"
    by (simp add: false_alt_def true_alt_def)
  also from assms have "... = ((R1(($ok \<and> P) \<Rightarrow> Q) ;; R1(R \<Rightarrow> ($ok\<acute> \<and> S)))
                             \<or> (R1(\<not> ($ok \<and> P)) ;; R1(true)))"
    by simp
  also from assms have "... = ((R1(\<not> $ok \<or> \<not> P \<or> Q) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S)))
                             \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by (simp add: impl_alt_def utp_pred.sup.assoc)
  also from assms have "... = (((R1(\<not> $ok \<or> \<not> P) \<or> R1(Q)) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S)))
                               \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by (simp add: R1_disj utp_pred.disj_assoc)
  also from assms have "... = ((R1(\<not> $ok \<or> \<not> P) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S)))
                               \<or> (R1(Q) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S)))
                               \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by (simp add: seqr_or_distl utp_pred.sup.assoc)
  also from assms have "... = ((R1(Q) ;; R1(\<not> R \<or> ($ok\<acute> \<and> S)))
                               \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by (rel_blast)
  also from assms have "... = ((R1(Q) ;; (R1(\<not> R) \<or> R1(S) \<and> $ok\<acute>))
                               \<or> (R1(\<not> $ok \<or> \<not> P) ;; R1(true)))"
    by (simp add: R1_disj R1_extend_conj utp_pred.inf_commute)
  also have "... = ((R1(Q) ;; (R1(\<not> R) \<or> R1(S) \<and> $ok\<acute>))
                  \<or> ((R1(\<not> $ok) :: ('t,'\<alpha>,'\<beta>) relation_rp) ;; R1(true))
                  \<or> (R1(\<not> P) ;; R1(true)))"
    by (simp add: R1_disj seqr_or_distl)
  also have "... = ((R1(Q) ;; (R1(\<not> R) \<or> R1(S) \<and> $ok\<acute>))
                  \<or> (R1(\<not> $ok))
                  \<or> (R1(\<not> P) ;; R1(true)))"
  proof -
    have "((R1(\<not> $ok) :: ('t,'\<alpha>,'\<beta>) relation_rp) ;; R1(true)) =
           (R1(\<not> $ok) :: ('t,'\<alpha>,'\<gamma>) relation_rp)"
      by (rel_auto)
    thus ?thesis
      by simp
  qed
  also have "... = ((R1(Q) ;; (R1(\<not> R) \<or> (R1(S \<and> $ok\<acute>))))
                  \<or> R1(\<not> $ok)
                  \<or> (R1(\<not> P) ;; R1(true)))"
    by (simp add: R1_extend_conj)
  also have "... = ( (R1(Q) ;; (R1 (\<not> R)))
                   \<or> (R1(Q) ;; (R1(S \<and> $ok\<acute>)))
                   \<or> R1(\<not> $ok)
                   \<or> (R1(\<not> P) ;; R1(true)))"
    by (simp add: seqr_or_distr utp_pred.sup.assoc)
  also have "... = R1( (R1(Q) ;; (R1 (\<not> R)))
                     \<or> (R1(Q) ;; (R1(S \<and> $ok\<acute>)))
                     \<or> (\<not> $ok)
                     \<or> (R1(\<not> P) ;; R1(true)))"
    by (simp add: R1_disj R1_seqr)
  also have "... = R1( (R1(Q) ;; (R1 (\<not> R)))
                     \<or> ((R1(Q) ;; R1(S)) \<and> $ok\<acute>)
                     \<or> (\<not> $ok)
                     \<or> (R1(\<not> P) ;; R1(true)))"
    by (rel_blast)
  also have "... = R1(\<not>($ok \<and> \<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; (R1 (\<not> R))))
                     \<or>  ((R1(Q) ;; R1(S)) \<and> $ok\<acute>))"
    by (rel_blast)
  also have "... = R1(($ok \<and> \<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; (R1 (\<not> R))))
                      \<Rightarrow> ($ok\<acute> \<and> (R1(Q) ;; R1(S))))"
    by (simp add: impl_alt_def utp_pred.inf_commute)
  also have "... = R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> (R1(Q) ;; R1(\<not> R))) \<turnstile> (R1(Q) ;; R1(S)))"
    by (simp add: design_def)
  finally show ?thesis .
qed

definition [upred_defs]: "R3c_pre(P) = (true \<triangleleft> $wait \<triangleright> P)"

definition [upred_defs]: "R3c_post(P) = (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> P)"

definition [upred_defs]: "R3h_post(P) = ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> P)"

lemma R3c_pre_conj: "R3c_pre(P \<and> Q) = (R3c_pre(P) \<and> R3c_pre(Q))"
  by (rel_auto)

lemma R3c_pre_seq:
  "(true ;; Q) = true \<Longrightarrow> R3c_pre(P ;; Q) = (R3c_pre(P) ;; Q)"
  by (rel_auto)

lemma R2s_design: "R2s(P \<turnstile> Q) = (R2s(P) \<turnstile> R2s(Q))"
  by (simp add: R2s_def design_def usubst)

lemma R2c_design: "R2c(P \<turnstile> Q) = (R2c(P) \<turnstile> R2c(Q))"
  by (simp add: design_def impl_alt_def R2c_disj R2c_not R2c_ok R2c_and R2c_ok')

lemma R1_R3c_design:
  "R1(R3c(P \<turnstile> Q)) = R1(R3c_pre(P) \<turnstile> R3c_post(Q))"
  by (rel_auto)

lemma R1_R3h_design:
  "R1(R3h(P \<turnstile> Q)) = R1(R3c_pre(P) \<turnstile> R3h_post(Q))"
  by (rel_auto)

lemma unrest_ok_R2s [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R2s(P)"
  by (simp add: R2s_def unrest)

lemma unrest_ok'_R2s [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R2s(P)"
  by (simp add: R2s_def unrest)

lemma unrest_ok_R2c [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma unrest_ok'_R2c [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma unrest_ok_R3c_pre [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R3c_pre(P)"
  by (simp add: R3c_pre_def cond_def unrest)

lemma unrest_ok'_R3c_pre [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R3c_pre(P)"
  by (simp add: R3c_pre_def cond_def unrest)

lemma unrest_ok_R3c_post [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R3c_post(P)"
  by (simp add: R3c_post_def cond_def unrest)

lemma unrest_ok_R3c_post' [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R3c_post(P)"
  by (simp add: R3c_post_def cond_def unrest)

lemma unrest_ok_R3h_post [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> R3h_post(P)"
  by (simp add: R3h_post_def cond_def unrest)

lemma unrest_ok_R3h_post' [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> R3h_post(P)"
  by (simp add: R3h_post_def cond_def unrest)

lemma R3c_R1_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(R3c(R1(P \<turnstile> Q)) ;; R3c(R1(R \<turnstile> S))) =
       R3c(R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> ((R1(Q) \<and> \<not> $wait\<acute>) ;; R1(\<not> R)))
       \<turnstile> (R1(Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1(S)))))"
proof -
  have 1:"(\<not> (R1 (\<not> R3c_pre P) ;; R1 true)) = (R3c_pre (\<not> (R1 (\<not> P) ;; R1 true)))"
    by (rel_auto)
  have 2:"(\<not> (R1 (R3c_post Q) ;; R1 (\<not> R3c_pre R))) = R3c_pre(\<not> (R1 Q \<and> \<not> $wait\<acute> ;; R1 (\<not> R)))"
    by (rel_auto)
  have 3:"(R1 (R3c_post Q) ;; R1 (R3c_post S)) = R3c_post (R1 Q ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 S))"
    by (rel_auto)
  show ?thesis
    apply (simp add: R3c_semir_form R1_R3c_commute[THEN sym] R1_R3c_design unrest )
    apply (subst R1_design_composition)
    apply (simp_all add: unrest assms R3c_pre_conj 1 2 3)
  done
qed

lemma R3h_R1_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(R3h(R1(P \<turnstile> Q)) ;; R3h(R1(R \<turnstile> S))) =
       R3h(R1((\<not> (R1(\<not> P) ;; R1(true)) \<and> \<not> ((R1(Q) \<and> \<not> $wait\<acute>) ;; R1(\<not> R)))
       \<turnstile> (R1(Q) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1(S)))))"
proof -
  have 1:"(\<not> (R1 (\<not> R3c_pre P) ;; R1 true)) = (R3c_pre (\<not> (R1 (\<not> P) ;; R1 true)))"
   by (rel_auto, blast+)
  have 2:"(\<not> (R1 (R3h_post Q) ;; R1 (\<not> R3c_pre R))) = R3c_pre(\<not> (R1 Q \<and> \<not> $wait\<acute> ;; R1 (\<not> R)))"
    by (rel_auto, blast+)
  have 3:"(R1 (R3h_post Q) ;; R1 (R3h_post S)) = R3h_post (R1 Q ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 S))"
    by (rel_auto, blast+)
  show ?thesis
    apply (simp add: R3h_semir_form R1_R3h_commute[THEN sym] R1_R3h_design unrest )
    apply (subst R1_design_composition)
    apply (simp_all add: unrest assms R3c_pre_conj 1 2 3)
  done
qed

lemma R1_des_lift_skip: "R1(\<lceil>II\<rceil>\<^sub>D) = \<lceil>II\<rceil>\<^sub>D"
  by (rel_auto)

lemma R2s_subst_wait_true [usubst]:
  "(R2s(P))\<lbrakk>true/$wait\<rbrakk> = R2s(P\<lbrakk>true/$wait\<rbrakk>)"
  by (simp add: R2s_def usubst unrest)

lemma R2s_subst_wait'_true [usubst]:
  "(R2s(P))\<lbrakk>true/$wait\<acute>\<rbrakk> = R2s(P\<lbrakk>true/$wait\<acute>\<rbrakk>)"
  by (simp add: R2s_def usubst unrest)

lemma R2_subst_wait_true [usubst]:
  "(R2(P))\<lbrakk>true/$wait\<rbrakk> = R2(P\<lbrakk>true/$wait\<rbrakk>)"
  by (simp add: R2_def R1_def R2s_def usubst unrest)

lemma R2_subst_wait'_true [usubst]:
  "(R2(P))\<lbrakk>true/$wait\<acute>\<rbrakk> = R2(P\<lbrakk>true/$wait\<acute>\<rbrakk>)"
  by (simp add: R2_def R1_def R2s_def usubst unrest)

lemma R2_subst_wait_false [usubst]:
  "(R2(P))\<lbrakk>false/$wait\<rbrakk> = R2(P\<lbrakk>false/$wait\<rbrakk>)"
  by (simp add: R2_def R1_def R2s_def usubst unrest)

lemma R2_subst_wait'_false [usubst]:
  "(R2(P))\<lbrakk>false/$wait\<acute>\<rbrakk> = R2(P\<lbrakk>false/$wait\<acute>\<rbrakk>)"
  by (simp add: R2_def R1_def R2s_def usubst unrest)

lemma R2_des_lift_skip:
  "R2(\<lceil>II\<rceil>\<^sub>D) = \<lceil>II\<rceil>\<^sub>D"
  by (rel_auto, metis alpha_rp'.cases_scheme alpha_rp'.select_convs(2) alpha_rp'.update_convs(2)  minus_zero_eq)

lemma R2c_R2s_absorb: "R2c(R2s(P)) = R2s(P)"
  by (rel_auto)

lemma R2_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(R2(P \<turnstile> Q) ;; R2(R \<turnstile> S)) =
       R2((\<not> (R1 (\<not> R2c P) ;; R1 true) \<and> \<not> (R1 (R2c Q) ;; R1 (\<not> R2c R))) \<turnstile> (R1 (R2c Q) ;; R1 (R2c S)))"
  apply (simp add: R2_R2c_def R2c_design R1_design_composition assms unrest R2c_not R2c_and R2c_disj R1_R2c_commute[THEN sym] R2c_idem R2c_R1_seq)
  apply (metis (no_types, lifting) R2c_R1_seq R2c_not R2c_true)
done

lemma RH_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(RH(P \<turnstile> Q) ;; RH(R \<turnstile> S)) =
       RH((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> (R1 (R2s Q) \<and> (\<not> $wait\<acute>) ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))))"
proof -
  have 1: "R2c (R1 (\<not> R2s P) ;; R1 true) = (R1 (\<not> R2s P) ;; R1 true)"
  proof -
    have 1:"(R1 (\<not> R2s P) ;; R1 true) = (R1(R2 (\<not> P) ;; R2 true))"
      by (rel_auto)
    have "R2c(R1(R2 (\<not> P) ;; R2 true)) = R2c(R1(R2 (\<not> P) ;; R2 true))"
      using R2c_not by blast
    also have "... = R2(R2 (\<not> P) ;; R2 true)"
      by (metis R1_R2c_commute R1_R2c_is_R2)
    also have "... = (R2 (\<not> P) ;; R2 true)"
      by (simp add: R2_seqr_distribute)
    also have "... = (R1 (\<not> R2s P) ;; R1 true)"
      by (simp add: R2_def R2s_not R2s_true)
    finally show ?thesis
      by (simp add: 1)
  qed

  have 2:"R2c (R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R)) = (R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R))"
  proof -
    have "(R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R)) = R1 (R2 (Q \<and> \<not> $wait\<acute>) ;; R2 (\<not> R))"
      by (rel_auto)
    hence "R2c (R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R)) = (R2 (Q \<and> \<not> $wait\<acute>) ;; R2 (\<not> R))"
      by (metis R1_R2c_commute R1_R2c_is_R2 R2_seqr_distribute)
    also have "... = (R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R))"
      by (rel_auto)
    finally show ?thesis .
  qed

  have 3:"R2c((R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S)))) = (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S)))"
  proof -
    have "R2c(((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>))
          = ((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)"
    proof -
      have "R2c(((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)) =
            R2c(R1 (R2s (Q\<lbrakk>true/$wait\<acute>\<rbrakk>)) ;; \<lceil>II\<rceil>\<^sub>D\<lbrakk>true/$wait\<rbrakk>)"
        by (simp add: usubst cond_unit_T R1_def R2s_def)
      also have "... = R2c(R2(Q\<lbrakk>true/$wait\<acute>\<rbrakk>) ;; R2(\<lceil>II\<rceil>\<^sub>D\<lbrakk>true/$wait\<rbrakk>))"
        by (metis R2_def R2_des_lift_skip R2_subst_wait_true)
      also have "... = (R2(Q\<lbrakk>true/$wait\<acute>\<rbrakk>) ;; R2(\<lceil>II\<rceil>\<^sub>D\<lbrakk>true/$wait\<rbrakk>))"
        using R2c_seq by blast
      also have "... = ((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)"
        apply (simp add: usubst R2_des_lift_skip)
        apply (metis R2_def R2_des_lift_skip R2_subst_wait'_true R2_subst_wait_true)
      done
      finally show ?thesis .
    qed
    moreover have "R2c(((R1 (R2s Q))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>false/$wait\<rbrakk>))
          = ((R1 (R2s Q))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>false/$wait\<rbrakk>)"
      by (simp add: usubst cond_unit_F, metis R2_R1_form R2_subst_wait'_false R2_subst_wait_false R2c_seq)
    ultimately show ?thesis
      by (smt R2_R1_form R2_condr' R2_des_lift_skip R2c_seq R2s_wait)
  qed

  have "(R1(R2s(R3c(P \<turnstile> Q))) ;; R1(R2s(R3c(R \<turnstile> S)))) =
        ((R3c(R1(R2s(P) \<turnstile> R2s(Q)))) ;; R3c(R1(R2s(R) \<turnstile> R2s(S))))"
    by (metis (no_types, hide_lams) R1_R2s_R2c R1_R3c_commute R2c_R3c_commute R2s_design)
  also have "... = R3c (R1 ((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> (R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S)))))"
    by (simp add: R3c_R1_design_composition assms unrest)
  also have "... = R3c(R1(R2c((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> (R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R))) \<turnstile>
                              (R1 (R2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S))))))"
    by (simp add: R2c_design R2c_and R2c_not 1 2 3)
  finally show ?thesis
    by (simp add: R1_R2s_R2c R1_R3c_commute R2c_R3c_commute RH_R2c_def)
qed

lemma R2_st_ex: "R2 (\<exists> $st \<bullet> P) = (\<exists> $st \<bullet> R2(P))"
  by (rel_auto)

lemma RHS_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q) ;; \<^bold>R\<^sub>s(R \<turnstile> S)) =
       \<^bold>R\<^sub>s((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> (R1 (R2s Q) \<and> (\<not> $wait\<acute>) ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))))"
proof -
  have 1: "R2c (R1 (\<not> R2s P) ;; R1 true) = (R1 (\<not> R2s P) ;; R1 true)"
  proof -
    have 1:"(R1 (\<not> R2s P) ;; R1 true) = (R1(R2 (\<not> P) ;; R2 true))"
      by (rel_auto, blast)
    have "R2c(R1(R2 (\<not> P) ;; R2 true)) = R2c(R1(R2 (\<not> P) ;; R2 true))"
      using R2c_not by blast
    also have "... = R2(R2 (\<not> P) ;; R2 true)"
      by (metis R1_R2c_commute R1_R2c_is_R2)
    also have "... = (R2 (\<not> P) ;; R2 true)"
      by (simp add: R2_seqr_distribute)
    also have "... = (R1 (\<not> R2s P) ;; R1 true)"
      by (simp add: R2_def R2s_not R2s_true)
    finally show ?thesis
      by (simp add: 1)
  qed

  have 2:"R2c (R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R)) = (R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R))"
  proof -
    have "(R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R)) = R1 (R2 (Q \<and> \<not> $wait\<acute>) ;; R2 (\<not> R))"
      by (rel_auto, blast+)
    hence "R2c (R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R)) = (R2 (Q \<and> \<not> $wait\<acute>) ;; R2 (\<not> R))"
      by (metis (no_types, lifting) R1_R2c_commute R1_R2c_is_R2 R2_seqr_distribute)
    also have "... = (R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R))"
      by (rel_auto, blast+)
    finally show ?thesis .
  qed

  have 3:"R2c((R1 (R2s Q) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S)))) =
          (R1 (R2s Q) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S)))"
  proof -
    have "R2c(((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>))
          = ((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)"
    proof -
      have "R2c(((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)) =
            R2c(R1 (R2s (Q\<lbrakk>true/$wait\<acute>\<rbrakk>)) ;; (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D)\<lbrakk>true/$wait\<rbrakk>)"
        by (simp add: usubst cond_unit_T R1_def R2s_def)
      also have "... = R2c(R2(Q\<lbrakk>true/$wait\<acute>\<rbrakk>) ;; R2((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D)\<lbrakk>true/$wait\<rbrakk>))"
        by (metis (no_types, lifting) R2_def R2_des_lift_skip R2_subst_wait_true R2_st_ex)
      also have "... = (R2(Q\<lbrakk>true/$wait\<acute>\<rbrakk>) ;; R2((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D)\<lbrakk>true/$wait\<rbrakk>))"
        using R2c_seq by blast
      also have "... = ((R1 (R2s Q))\<lbrakk>true/$wait\<acute>\<rbrakk> ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>true/$wait\<rbrakk>)"
        apply (simp add: usubst R2_des_lift_skip)
        apply (metis (no_types) R2_def R2_des_lift_skip R2_st_ex R2_subst_wait'_true R2_subst_wait_true)
      done
      finally show ?thesis .
    qed
    moreover have "R2c(((R1 (R2s Q))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>false/$wait\<rbrakk>))
          = ((R1 (R2s Q))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))\<lbrakk>false/$wait\<rbrakk>)"
      by (simp add: usubst, metis (no_types, lifting) R2_R1_form R2_subst_wait'_false R2_subst_wait_false R2c_seq)
    ultimately show ?thesis
      by (smt R2_R1_form R2_condr' R2_des_lift_skip R2_st_ex R2c_seq R2s_wait)
  qed

  have "(R1(R2s(R3h(P \<turnstile> Q))) ;; R1(R2s(R3h(R \<turnstile> S)))) =
        ((R3h(R1(R2s(P) \<turnstile> R2s(Q)))) ;; R3h(R1(R2s(R) \<turnstile> R2s(S))))"
    by (metis (no_types, hide_lams) R1_R2s_R2c R1_R3h_commute R2c_R3h_commute R2s_design)
  also have "... = R3h (R1 ((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> (R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R))) \<turnstile>
                       (R1 (R2s Q) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S)))))"
    by (simp add: R3h_R1_design_composition assms unrest)
  also have "... = R3h(R1(R2c((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> (R1 (R2s Q) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R))) \<turnstile>
                              (R1 (R2s Q) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S))))))"
    by (simp add: R2c_design R2c_and R2c_not 1 2 3)
  finally show ?thesis
    by (simp add: R1_R2s_R2c R1_R3h_commute R2c_R3h_commute RHS_R2c_def)
qed

lemma RH_design_export_R1: "RH(P \<turnstile> Q) = RH(P \<turnstile> R1(Q))"
  by (rel_auto)

lemma RH_design_export_R2s: "RH(P \<turnstile> Q) = RH(P \<turnstile> R2s(Q))"
  by (rel_auto)

lemma RH_design_export_R2: "RH(P \<turnstile> Q) = RH(P \<turnstile> R2(Q))"
  by (metis R2_def RH_design_export_R1 RH_design_export_R2s)

lemma RH_design_pre_neg_R1: "RH((\<not> R1 P) \<turnstile> Q) = RH((\<not> P) \<turnstile> Q)"
  by (metis (no_types, lifting) R1_R2c_commute R1_R3c_commute R1_def R1_disj RH_R2c_def design_def impl_alt_def not_conj_deMorgans utp_pred.double_compl utp_pred.inf.orderE utp_pred.inf_le2)

lemma RH_design_pre_R2s: "RH((R2s P) \<turnstile> Q) = RH(P \<turnstile> Q)"
  by (metis (no_types, lifting) R1_R2c_is_R2 R1_R2s_R2c R2_R3c_commute R2s_design R2s_idem RH_alt_def')

lemma RH_design_pre_R2c: "RH((R2c P) \<turnstile> Q) = RH(P \<turnstile> Q)"
  by (metis (no_types, lifting) R2c_design R2c_idem RH_absorbs_R2c)

lemma RH_design_pre_neg_R1_R2c: "RH((\<not> R1 (R2c P)) \<turnstile> Q) = RH((\<not> P) \<turnstile> Q)"
  by (simp add: RH_design_pre_neg_R1, metis R2c_not RH_design_pre_R2c)

lemma RH_design_refine_intro:
  assumes "`P\<^sub>1 \<Rightarrow> P\<^sub>2`" "`P\<^sub>1 \<and> Q\<^sub>2 \<Rightarrow> Q\<^sub>1`"
  shows "RH(P\<^sub>1 \<turnstile> Q\<^sub>1) \<sqsubseteq> RH(P\<^sub>2 \<turnstile> Q\<^sub>2)"
  by (simp add: RH_monotone assms(1) assms(2) design_refine_intro)

text {* Marcel's proof for reactive design composition *}

method rel_auto' = ((simp add: upred_defs urel_defs)?, (transfer, (rule_tac ext)?, auto simp add: uvar_defs lens_defs urel_defs relcomp_unfold fun_eq_iff prod.case_eq_if)?)

lemma reactive_design_composition:
  assumes "out\<alpha> \<sharp> p\<^sub>1" "p\<^sub>1 is R2s" "P\<^sub>2 is R2s" "Q\<^sub>1 is R2s" "Q\<^sub>2 is R2s"
  shows
  "(RH(p\<^sub>1 \<turnstile> Q\<^sub>1) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2)) =
    RH((p\<^sub>1 \<and> \<not> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1 (\<not> P\<^sub>2)))
       \<turnstile> ((($wait\<acute> \<and> Q\<^sub>1) \<or> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1(Q\<^sub>2)))))" (is "?lhs = ?rhs")
proof -
  have "?lhs = RH(?lhs)"
    by (metis Healthy_def' RH_idem RH_seq_closure)
  also have "... = RH ((R2 \<circ> R1) (p\<^sub>1 \<turnstile> Q\<^sub>1) ;; RH (P\<^sub>2 \<turnstile> Q\<^sub>2))"
    by (metis (no_types, hide_lams) R1_R2_commute R1_idem R2_R3c_commute R2_def R2_seqr_distribute R3c_semir_form RH_alt_def' calculation comp_apply)
  also have "... = RH (R1 ((\<not> $ok \<or> R2s (\<not> p\<^sub>1)) \<or> $ok\<acute> \<and> R2s Q\<^sub>1) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2))"
    by (simp add: design_def R2_R1_form impl_alt_def R2s_not R2s_ok R2s_disj R2s_conj R2s_ok')
  also have "... = RH(((\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2))
                      \<or> ((\<not> R2s(p\<^sub>1) \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2))
                      \<or> (($ok\<acute> \<and> R2s(Q\<^sub>1) \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2)))"
    by (smt R1_conj R1_def R1_disj R1_negate_R1 R2_def R2s_not seqr_or_distl utp_pred.conj_assoc utp_pred.inf.commute utp_pred.sup.assoc)
  also have "... = RH(((\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2))
                      \<or> ((\<not> p\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2))
                      \<or> (($ok\<acute> \<and> Q\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2)))"
    by (metis Healthy_def' assms(2) assms(4))

  also have "... = RH((\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>)
                      \<or> (\<not> p\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>)
                      \<or> (($ok\<acute> \<and> Q\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2)))"
  proof -
    have "((\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2)) = (\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>)"
      by (rel_auto)
    moreover have "(((\<not> p\<^sub>1 ;; true) \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; RH(P\<^sub>2 \<turnstile> Q\<^sub>2)) = ((\<not> p\<^sub>1 ;; true) \<and> $tr \<le>\<^sub>u $tr\<acute>)"
      by (rel_auto)
    ultimately show ?thesis
      by (smt assms(1) precond_right_unit unrest_not)
  qed

  also have "... = RH((\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>)
                      \<or> (\<not> p\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>)
                      \<or> (($ok\<acute> \<and> Q\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; ($wait \<and> $ok\<acute> \<and> II))
                      \<or> (($ok\<acute> \<and> Q\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; (\<not> $wait \<and> R1(\<not> P\<^sub>2) \<and> $tr \<le>\<^sub>u $tr\<acute>))
                      \<or> (($ok\<acute> \<and> Q\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; (\<not> $wait \<and> $ok\<acute> \<and> R2(Q\<^sub>2) \<and> $tr \<le>\<^sub>u $tr\<acute>)))"
  proof -
    have 1:"RH(P\<^sub>2 \<turnstile> Q\<^sub>2) = (($wait \<and> \<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>)
                        \<or> ($wait \<and> $ok\<acute> \<and> II)
                        \<or> (\<not> $wait \<and> \<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>)
                        \<or> (\<not> $wait \<and> R2(\<not> P\<^sub>2) \<and> $tr \<le>\<^sub>u $tr\<acute>)
                        \<or> (\<not> $wait \<and> $ok\<acute> \<and> R2(Q\<^sub>2) \<and> $tr \<le>\<^sub>u $tr\<acute>))"
      by (simp add: RH_alt_def' R2_condr' R2s_wait R2_skip_rea R3c_def usubst, rel_auto)
    have 2:"(($ok\<acute> \<and> Q\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; ($wait \<and> \<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>)) = false"
      by (rel_auto)
    have 3:"(($ok\<acute> \<and> Q\<^sub>1 \<and> $tr \<le>\<^sub>u $tr\<acute>) ;; (\<not> $wait \<and> \<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>)) = false"
      by (rel_auto)
    have 4:"R2(\<not> P\<^sub>2) = R1(\<not> P\<^sub>2)"
      by (metis Healthy_def' R1_negate_R1 R2_def R2s_not assms(3))
    show ?thesis
      by (simp add: "1" "2" "3" "4" seqr_or_distr)
  qed

  also have "... = RH((\<not> $ok) \<or> (\<not> p\<^sub>1)
                      \<or> (($ok\<acute> \<and> Q\<^sub>1) ;; ($wait \<and> $ok\<acute> \<and> II))
                      \<or> (($ok\<acute> \<and> Q\<^sub>1) ;; (\<not> $wait \<and> R1(\<not> P\<^sub>2)))
                      \<or> (($ok\<acute> \<and> Q\<^sub>1) ;; (\<not> $wait \<and> $ok\<acute> \<and> R2(Q\<^sub>2))))"
    by (rel_blast)

  also have "... = RH((\<not> $ok) \<or> (\<not> p\<^sub>1)
                      \<or> ($ok\<acute> \<and> $wait\<acute> \<and> Q\<^sub>1)
                      \<or> (($ok\<acute> \<and> Q\<^sub>1) ;; (\<not> $wait \<and> R1(\<not> P\<^sub>2)))
                      \<or> (($ok\<acute> \<and> Q\<^sub>1) ;; (\<not> $wait \<and> $ok\<acute> \<and> R1(Q\<^sub>2))))"
  proof -
    have "(($ok\<acute> \<and> Q\<^sub>1) ;; ($wait \<and> $ok\<acute> \<and> II)) = ($ok\<acute> \<and> $wait\<acute> \<and> Q\<^sub>1)"
      by (rel_auto)
    moreover have "R2(Q\<^sub>2) = R1(Q\<^sub>2)"
      by (metis Healthy_def' R2_def assms(5))
    ultimately show ?thesis by simp
  qed

  also have "... = RH((\<not> $ok) \<or> (\<not> p\<^sub>1)
                      \<or> ($ok\<acute> \<and> $wait\<acute> \<and> Q\<^sub>1)
                      \<or> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; (R1(\<not> P\<^sub>2)))
                      \<or> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; ($ok\<acute> \<and> R1(Q\<^sub>2))))"
    by (rel_auto)'

  also have "... = RH((\<not> $ok) \<or> (\<not> p\<^sub>1) \<or> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1(\<not> P\<^sub>2))
                      \<or> ($ok\<acute> \<and> (($wait\<acute> \<and> Q\<^sub>1) \<or> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1(Q\<^sub>2)))))"
    by (rel_auto)'

  also have "... = RH(\<not> ($ok \<and> p\<^sub>1 \<and> \<not> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1(\<not> P\<^sub>2)))
                      \<or> ($ok\<acute> \<and> (($wait\<acute> \<and> Q\<^sub>1) \<or> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1(Q\<^sub>2)))))"
    by (rel_auto)'

  also have "... = ?rhs"
  proof -
    have "(\<not> ($ok \<and> p\<^sub>1 \<and> \<not> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1(\<not> P\<^sub>2)))
                      \<or> ($ok\<acute> \<and> (($wait\<acute> \<and> Q\<^sub>1) \<or> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1(Q\<^sub>2)))))
          = (($ok \<and> (p\<^sub>1 \<and> \<not> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1(\<not> P\<^sub>2)))) \<Rightarrow>
            ($ok\<acute> \<and> (($wait\<acute> \<and> Q\<^sub>1) \<or> (($ok\<acute> \<and> \<not> $wait\<acute> \<and> Q\<^sub>1) ;; R1(Q\<^sub>2)))))"
      by pred_auto
    thus ?thesis
      by (simp add: design_def)
  qed

  finally show ?thesis .
qed

subsection {* Healthiness conditions *}


abbreviation "CSP(P) \<equiv> RD1(RD2(RH(P)))"

lemma RD1_idem:
  "RD1(RD1(P)) = RD1(P)"
  by pred_auto

lemma RD2_idem:
  "RD2(RD2(P)) = RD2(P)"
  by (simp add: RD2_def H2_idem)

lemma RD1_RD2_commute:
  "RD1(RD2(P)) = RD2(RD1(P))"
  by (simp add: RD1_def RD2_def H2_split usubst, rel_auto)

lemma RD1_R1_commute:
  "RD1(R1(P)) = R1(RD1(P))"
  by (rel_auto)

lemma RD1_R2c_commute:
  "RD1(R2c(P)) = R2c(RD1(P))"
  by (rel_auto)

lemma RD1_R3c_commute:
  "RD1(R3c(P)) = R3c(RD1(P))"
  by (rel_auto)

lemma RD1_R3h_commute:
  "RD1(R3h(P)) = R3h(RD1(P))"
  by (rel_auto)

lemma CSP_idem: "CSP(CSP(P)) = CSP(P)"
  by (metis (no_types, hide_lams) RD1_RD2_commute RD1_R1_commute RD1_R2c_commute RD1_R3c_commute RD1_idem RD2_def RD2_idem R1_H2_commute R2c_H2_commute R3c_H2_commute RH_R2c_def RH_idem)

lemma CSP_Idempotent: "Idempotent CSP"
  by (simp add: CSP_idem Idempotent_def)

lemma RD1_via_H1: "R1(H1(P)) = R1(RD1(P))"
  by (rel_auto)

lemma RD1_R3c: "RD1(R3(P)) = R3c(RD1(P))"
  by (rel_auto)

lemma RD1_R1_H1:
  "RD1(R1(P)) = R1(H1(P))"
  by (rel_auto)

lemma RD1_algebraic_intro:
  assumes
    "P is R1" "(R1(true\<^sub>h) ;; P) = R1(true\<^sub>h)" "(II\<^sub>r ;; P) = P"
  shows "P is RD1"
proof -
  have "P = (II\<^sub>r ;; P)"
    by (simp add: assms(3))
  also have "... = (R1($ok \<Rightarrow> II) ;; P)"
    by (simp add: skip_rea_R1_lemma)
  also have "... = (((\<not> $ok \<and> R1(true)) ;; P) \<or> P)"
    by (metis (no_types, lifting) R1_def seqr_left_unit seqr_or_distl skip_rea_R1_lemma skip_rea_def utp_pred.inf_top_left utp_pred.sup_commute)
  also have "... = (((R1(\<not> $ok) ;; R1(true\<^sub>h)) ;; P) \<or> P)"
    by (rel_auto, metis order_trans)
  also have "... = ((R1(\<not> $ok) ;; (R1(true\<^sub>h) ;; P)) \<or> P)"
    by (simp add: seqr_assoc)
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
  shows "(II\<^sub>r ;; P) = P"
proof -
  have "(II\<^sub>r ;; R1(RD1(P))) = R1(RD1(P))"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms(1) assms(2))
qed

lemma RD1_alt_def:
  assumes "P is R1"
  shows "RD1(P) = (P \<triangleleft> $ok \<triangleright> R1(true))"
  using assms
proof -
  have "RD1(R1(P)) = (R1(P) \<triangleleft> $ok \<triangleright> R1(true))"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

theorem RD1_algebraic:
  assumes "P is R1"
  shows "P is RD1 \<longleftrightarrow> (R1(true\<^sub>h) ;; P) = R1(true\<^sub>h) \<and> (II\<^sub>r ;; P) = P"
  using RD1_algebraic_intro RD1_left_unit RD1_left_zero assms by blast

lemma RD1_reactive_design: "RD1(RH(P \<turnstile> Q)) = RH(P \<turnstile> Q)"
  by (rel_auto)

lemma RD2_reactive_design:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q"
  shows "RD2(RH(P \<turnstile> Q)) = RH(P \<turnstile> Q)"
  using assms
  by (simp add: RD2_def H2_R1_comm H2_R2_comm H2_R3_comm H2_design RH_def H2_R2s_comm)

lemma wait_false_design:
  "(P \<turnstile> Q) \<^sub>f = ((P \<^sub>f) \<turnstile> (Q \<^sub>f))"
  by (rel_auto)

lemma CSP_RH_design_form:
  "CSP(P) = RH((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
proof -
  have "CSP(P) = RD1(RD2(R1(R2s(R3c(P)))))"
    by (metis Healthy_def' RH_def assms)
  also have "... = RD1(H2(R1(R2s(R3c(P)))))"
    by (simp add: RD2_def)
  also have "... = RD1(R1(H2(R2s(R3c(P)))))"
    by (simp add: R1_H2_commute)
  also have "... = R1(H1(R1(H2(R2s(R3c(P))))))"
    by (simp add: RD1_R1_commute RD1_via_H1 R1_idem)
  also have "... = R1(H1(H2(R2s(R3c(R1(P))))))"
    by (metis (no_types, hide_lams) RD1_R1_H1 R1_H2_commute R1_R2_commute R1_idem R2_R3c_commute R2_def)
  also have "... = R1(R2s(H1(H2(R3c(R1(P))))))"
    by (simp add: R2s_H1_commute R2s_H2_commute)
  also have "... = R1(R2s(H1(R3c(H2(R1(P))))))"
    by (simp add: R3c_H2_commute)
  also have "... = R2(R1(H1(R3c(H2(R1(P))))))"
    by (metis R1_R2_commute R1_idem R2_def)
  also have "... = R2(R3c(R1(H1(H2(R1(P))))))"
    by (simp add: R1_H1_R3c_commute)
  also have "... = RH(H1_H2(R1(P)))"
    by (metis R1_R2_commute R1_idem R2_R3c_commute R2_def RH_def)
  also have "... = RH(H1_H2(P))"
    by (metis (no_types, hide_lams) RD1_R1_H1 R1_H2_commute R1_R2_commute R1_R3c_commute R1_idem RH_alt_def)
  also have "... = RH((\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
  proof -
    have 0:"(\<not> (H1_H2(P))\<^sup>f) = ($ok \<and> \<not> P\<^sup>f)"
      by (simp add: H1_def H2_split, pred_auto)
    have 1:"(H1_H2(P))\<^sup>t = ($ok \<Rightarrow> (P\<^sup>f \<or> P\<^sup>t))"
      by (simp add: H1_def H2_split, pred_auto)
    have "(\<not> (H1_H2(P))\<^sup>f) \<turnstile> (H1_H2(P))\<^sup>t = ((\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
      by (simp add: 0 1, pred_auto)
    thus ?thesis
      by (metis H1_H2_commute H1_H2_is_design H1_idem H2_idem Healthy_def')
  qed
  also have "... = RH((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (metis (no_types, lifting) RH_subst_wait subst_not wait_false_design)
  finally show ?thesis .
qed

lemma CSP_reactive_design:
  assumes "P is CSP"
  shows "RH((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = P"
  by (metis CSP_RH_design_form Healthy_def' assms)

lemma CSP_RH_design:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q"
  shows "CSP(RH(P \<turnstile> Q)) = RH(P \<turnstile> Q)"
  by (metis RD1_reactive_design RD2_reactive_design RH_idem assms(1) assms(2))

lemma RH_design_is_CSP:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q"
  shows "\<^bold>R(P \<turnstile> Q) is CSP"
  by (simp add: CSP_RH_design Healthy_def' assms(1) assms(2))

lemma CSP_R3_def: "CSP(P) = R1(R2c(\<^bold>H(R3(P))))"
  by (rel_auto)

lemma RD2_R3c_commute: "RD2(R3c(P)) = R3c(RD2(P))"
  by (rel_auto)

lemma RD2_R3h_commute: "RD2(R3h(P)) = R3h(RD2(P))"
  by (rel_auto)

lemma R3c_via_RD1_R3:
  "\<lbrakk> P is RD1; P is R3 \<rbrakk> \<Longrightarrow> P is R3c"
  by (metis RD1_R3c Healthy_def')

lemma R3c_RD1_form:
  "P is R1 \<Longrightarrow> R3c(RD1(P)) = (R1(true) \<triangleleft> \<not>$ok \<triangleright> (II \<triangleleft> $wait \<triangleright> P))"
  by (rel_blast)

lemma R3c_CSP: "R3c(CSP(P)) = CSP(P)"
  by (simp add: RD1_R3c_commute RD2_R3c_commute R2_R3c_commute R3c_idem RH_alt_def')

lemma CSP_R1_R2s: "P is CSP \<Longrightarrow> R1 (R2s P) = P"
  by (metis (no_types) CSP_reactive_design R1_R2c_is_R2 R1_R2s_R2c R2_idem RH_alt_def')

lemma CSP_healths:
  assumes "P is CSP"
  shows "P is R1" "P is R2" "P is R3c" "P is RD1" "P is RD2"
  apply (metis (mono_tags) CSP_R1_R2s Healthy_def' R1_idem assms(1))
  apply (metis CSP_R1_R2s Healthy_def R2_def assms)
  apply (metis Healthy_def R3c_CSP assms)
  apply (metis RD1_idem Healthy_def' assms)
  apply (metis RD1_RD2_commute RD2_idem Healthy_def' assms)
done

lemma CSP_intro:
  assumes "P is R1" "P is R2" "P is R3c" "P is RD1" "P is RD2"
  shows "P is CSP"
  by (metis Healthy_def RH_alt_def' assms(2) assms(3) assms(4) assms(5))

subsection {* Reactive design triples *}

definition wait'_cond :: "_ \<Rightarrow> _ \<Rightarrow> _" (infix "\<diamondop>" 65) where
[upred_defs]: "P \<diamondop> Q = (P \<triangleleft> $wait\<acute> \<triangleright> Q)"

lemma wait'_cond_unrest [unrest]:
  "\<lbrakk> out_var wait \<bowtie> x; x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> (P \<diamondop> Q)"
  by (simp add: wait'_cond_def unrest)

lemma wait'_cond_subst [usubst]:
  "$wait\<acute> \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<dagger> (P \<diamondop> Q) = (\<sigma> \<dagger> P) \<diamondop> (\<sigma> \<dagger> Q)"
  by (simp add: wait'_cond_def usubst unrest)

lemma wait'_cond_left_false: "false \<diamondop> P = (\<not> $wait\<acute> \<and> P)"
  by (rel_auto)

lemma wait'_cond_seq: "((P \<diamondop> Q) ;; R) = ((P ;; $wait \<and> R) \<or> (Q ;; \<not>$wait \<and> R))"
  by (simp add: wait'_cond_def cond_def seqr_or_distl, rel_blast)

lemma wait'_cond_true: "(P \<diamondop> Q \<and> $wait\<acute>) = (P \<and> $wait\<acute>)"
  by (rel_auto)

lemma wait'_cond_false: "(P \<diamondop> Q \<and> (\<not>$wait\<acute>)) = (Q \<and> (\<not>$wait\<acute>))"
  by (rel_auto)

lemma wait'_cond_idem: "P \<diamondop> P = P"
  by (rel_auto)

lemma wait'_cond_conj_exchange:
  "((P \<diamondop> Q) \<and> (R \<diamondop> S)) = (P \<and> R) \<diamondop> (Q \<and> S)"
  by (rel_auto)

lemma subst_wait'_cond_true [usubst]: "(P \<diamondop> Q)\<lbrakk>true/$wait\<acute>\<rbrakk> = P\<lbrakk>true/$wait\<acute>\<rbrakk>"
  by (rel_auto)

lemma subst_wait'_cond_false [usubst]: "(P \<diamondop> Q)\<lbrakk>false/$wait\<acute>\<rbrakk> = Q\<lbrakk>false/$wait\<acute>\<rbrakk>"
  by (rel_auto)

lemma subst_wait'_left_subst: "(P\<lbrakk>true/$wait\<acute>\<rbrakk> \<diamondop> Q) = (P \<diamondop> Q)"
  by (metis wait'_cond_def cond_def conj_comm conj_eq_out_var_subst upred_eq_true wait_vwb_lens)

lemma subst_wait'_right_subst: "(P \<diamondop> Q\<lbrakk>false/$wait\<acute>\<rbrakk>) = (P \<diamondop> Q)"
  by (metis cond_def conj_eq_out_var_subst upred_eq_false utp_pred.inf.commute wait'_cond_def wait_vwb_lens)

lemma wait'_cond_split: "P\<lbrakk>true/$wait\<acute>\<rbrakk> \<diamondop> P\<lbrakk>false/$wait\<acute>\<rbrakk> = P"
  by (simp add: wait'_cond_def cond_var_split)

lemma R1_wait'_cond: "R1(P \<diamondop> Q) = R1(P) \<diamondop> R1(Q)"
  by (rel_auto)

lemma R2s_wait'_cond: "R2s(P \<diamondop> Q) = R2s(P) \<diamondop> R2s(Q)"
  by (simp add: wait'_cond_def R2s_def R2s_def usubst)

lemma R2_wait'_cond: "R2(P \<diamondop> Q) = R2(P) \<diamondop> R2(Q)"
  by (simp add: R2_def R2s_wait'_cond R1_wait'_cond)

lemma RH_design_peri_R1: "RH(P \<turnstile> R1(Q) \<diamondop> R) = RH(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R1_idem R1_wait'_cond RH_design_export_R1)

lemma RH_design_post_R1: "RH(P \<turnstile> Q \<diamondop> R1(R)) = RH(P \<turnstile> Q \<diamondop> R)"
  by (metis R1_wait'_cond RH_design_export_R1 RH_design_peri_R1)

lemma RH_design_peri_R2s: "RH(P \<turnstile> R2s(Q) \<diamondop> R) = RH(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R2s_idem R2s_wait'_cond RH_design_export_R2s)

lemma RH_design_post_R2s: "RH(P \<turnstile> Q \<diamondop> R2s(R)) = RH(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R2s_idem R2s_wait'_cond RH_design_export_R2s)

lemma RH_design_peri_R2c: "RH(P \<turnstile> R2c(Q) \<diamondop> R) = RH(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R1_R2c_is_R2 R2_wait'_cond R2c_idem RH_design_export_R2)

lemma RH_design_post_R2c: "RH(P \<turnstile> Q \<diamondop> R2c(R)) = RH(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R1_R2c_is_R2 R2_wait'_cond R2c_idem RH_design_export_R2)

lemma RH_design_lemma1:
  "RH(P \<turnstile> (R1(R2c(Q)) \<or> R) \<diamondop> S) = RH(P \<turnstile> (Q \<or> R) \<diamondop> S)"
  by (simp add: design_def impl_alt_def wait'_cond_def RH_R2c_def R2c_R3c_commute R1_R3c_commute R1_disj R2c_disj R2c_and R1_cond R2c_condr R1_R2c_commute R2c_idem R1_extend_conj' R1_idem)

lemma RH_tri_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$ok \<sharp> R" "$ok \<sharp> S\<^sub>1" "$ok \<sharp> S\<^sub>2"
           "$wait\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> S\<^sub>1" "$wait \<sharp> S\<^sub>2"
  shows "(RH(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; RH(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)) =
       RH((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> (R1 (R2s Q\<^sub>2) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R))) \<turnstile>
                       ((Q\<^sub>1 \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> ((R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))))"
proof -
  have 1:"(\<not> (R1 (R2s (Q\<^sub>1 \<diamondop> Q\<^sub>2)) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R))) =
        (\<not> (R1 (R2s Q\<^sub>2) \<and> \<not> $wait\<acute> ;; R1 (\<not> R2s R)))"
    by (metis (no_types, hide_lams) R1_extend_conj R2s_conj R2s_not R2s_wait' wait'_cond_false)
  have 2: "(R1 (R2s (Q\<^sub>1 \<diamondop> Q\<^sub>2)) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s (S\<^sub>1 \<diamondop> S\<^sub>2)))) =
                 ((R1 (R2s Q\<^sub>1) \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))"
  proof -
    have "(R1 (R2s Q\<^sub>1) ;; $wait \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2)))
                       = (R1 (R2s Q\<^sub>1) \<and> $wait\<acute>)"
    proof -
      have "(R1 (R2s Q\<^sub>1) ;; $wait \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2)))
           = (R1 (R2s Q\<^sub>1) ;; $wait \<and> \<lceil>II\<rceil>\<^sub>D)"
        by (rel_auto)
      also have "... = ((R1 (R2s Q\<^sub>1) ;; \<lceil>II\<rceil>\<^sub>D) \<and> $wait\<acute>)"
        by (rel_auto)
      also from assms(2) have "... = ((R1 (R2s Q\<^sub>1)) \<and> $wait\<acute>)"
        by (simp add: lift_des_skip_dr_unit_unrest unrest)
      finally show ?thesis .
    qed

    moreover have "(R1 (R2s Q\<^sub>2) ;; \<not> $wait \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2)))
                  = ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2)))"
    proof -
      have "(R1 (R2s Q\<^sub>2) ;; \<not> $wait \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2)))
            = (R1 (R2s Q\<^sub>2) ;; \<not> $wait \<and> (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2)))"
        by (metis (no_types, lifting) cond_def conj_disj_not_abs utp_pred.double_compl utp_pred.inf.left_idem utp_pred.sup_assoc utp_pred.sup_inf_absorb)

      also have "... = ((R1 (R2s Q\<^sub>2))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))\<lbrakk>false/$wait\<rbrakk>)"
        by (metis false_alt_def seqr_right_one_point upred_eq_false wait_vwb_lens)

      also have "... = ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2)))"
        by (simp add: wait'_cond_def usubst unrest assms)

      finally show ?thesis .
    qed

    moreover
    have "((R1 (R2s Q\<^sub>1) \<and> $wait\<acute>) \<or> ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
          = (R1 (R2s Q\<^sub>1) \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> ((R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))"
      by (simp add: wait'_cond_def cond_seq_right_distr cond_and_T_integrate unrest)

    ultimately show ?thesis
      by (simp add: R2s_wait'_cond R1_wait'_cond wait'_cond_seq)
  qed

  show ?thesis
    apply (subst RH_design_composition)
    apply (simp_all add: assms)
    apply (simp add: assms wait'_cond_def unrest)
    apply (simp add: assms wait'_cond_def unrest)
    apply (simp add: 1 2)
    apply (simp add: R1_R2s_R2c RH_design_lemma1)
  done
qed

text {* Syntax for pre-, post-, and periconditions *}

abbreviation "pre\<^sub>s  \<equiv> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s false, $wait \<mapsto>\<^sub>s false]"
abbreviation "cmt\<^sub>s  \<equiv> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false]"
abbreviation "peri\<^sub>s \<equiv> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false, $wait\<acute> \<mapsto>\<^sub>s true]"
abbreviation "post\<^sub>s \<equiv> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false, $wait\<acute> \<mapsto>\<^sub>s false]"

abbreviation "npre\<^sub>R(P) \<equiv> pre\<^sub>s \<dagger> P"

definition [upred_defs]: "pre\<^sub>R(P)  = (\<not> (npre\<^sub>R(P)))"
definition [upred_defs]: "cmt\<^sub>R(P)  = (cmt\<^sub>s \<dagger> P)"
definition [upred_defs]: "peri\<^sub>R(P) = (peri\<^sub>s \<dagger> P)"
definition [upred_defs]: "post\<^sub>R(P) = (post\<^sub>s \<dagger> P)"

lemma ok_pre_unrest [unrest]: "$ok \<sharp> pre\<^sub>R P"
  by (simp add: pre\<^sub>R_def unrest usubst)

lemma ok_peri_unrest [unrest]: "$ok \<sharp> peri\<^sub>R P"
  by (simp add: peri\<^sub>R_def unrest usubst)

lemma ok_post_unrest [unrest]: "$ok \<sharp> post\<^sub>R P"
  by (simp add: post\<^sub>R_def unrest usubst)

lemma ok'_pre_unrest [unrest]: "$ok\<acute> \<sharp> pre\<^sub>R P"
  by (simp add: pre\<^sub>R_def unrest usubst)

lemma ok'_peri_unrest [unrest]: "$ok\<acute> \<sharp> peri\<^sub>R P"
  by (simp add: peri\<^sub>R_def unrest usubst)

lemma ok'_post_unrest [unrest]: "$ok\<acute> \<sharp> post\<^sub>R P"
  by (simp add: post\<^sub>R_def unrest usubst)

lemma wait_pre_unrest [unrest]: "$wait \<sharp> pre\<^sub>R P"
  by (simp add: pre\<^sub>R_def unrest usubst)

lemma wait_peri_unrest [unrest]: "$wait \<sharp> peri\<^sub>R P"
  by (simp add: peri\<^sub>R_def unrest usubst)

lemma wait_post_unrest [unrest]: "$wait \<sharp> post\<^sub>R P"
  by (simp add: post\<^sub>R_def unrest usubst)

lemma wait'_peri_unrest [unrest]: "$wait\<acute> \<sharp> peri\<^sub>R P"
  by (simp add: peri\<^sub>R_def unrest usubst)

lemma wait'_post_unrest [unrest]: "$wait\<acute> \<sharp> post\<^sub>R P"
  by (simp add: post\<^sub>R_def unrest usubst)

lemma pre\<^sub>s_design: "pre\<^sub>s \<dagger> (P \<turnstile> Q) = (\<not> pre\<^sub>s \<dagger> P)"
  by (simp add: design_def pre\<^sub>R_def usubst)

lemma peri\<^sub>s_design: "peri\<^sub>s \<dagger> (P \<turnstile> Q \<diamondop> R) = peri\<^sub>s \<dagger> (P \<Rightarrow> Q)"
  by (simp add: design_def usubst wait'_cond_def)

lemma post\<^sub>s_design: "post\<^sub>s \<dagger> (P \<turnstile> Q \<diamondop> R) = post\<^sub>s \<dagger> (P \<Rightarrow> R)"
  by (simp add: design_def usubst wait'_cond_def)

lemma pre\<^sub>s_R1 [usubst]: "pre\<^sub>s \<dagger> R1(P) = R1(pre\<^sub>s \<dagger> P)"
  by (simp add: R1_def usubst)

lemma pre\<^sub>s_R2c [usubst]: "pre\<^sub>s \<dagger> R2c(P) = R2c(pre\<^sub>s \<dagger> P)"
  by (simp add: R2c_def R2s_def usubst)

lemma peri\<^sub>s_R1 [usubst]: "peri\<^sub>s \<dagger> R1(P) = R1(peri\<^sub>s \<dagger> P)"
  by (simp add: R1_def usubst)

lemma peri\<^sub>s_R2c [usubst]: "peri\<^sub>s \<dagger> R2c(P) = R2c(peri\<^sub>s \<dagger> P)"
  by (simp add: R2c_def R2s_def usubst)

lemma post\<^sub>s_R1 [usubst]: "post\<^sub>s \<dagger> R1(P) = R1(post\<^sub>s \<dagger> P)"
  by (simp add: R1_def usubst)

lemma post\<^sub>s_R2c [usubst]: "post\<^sub>s \<dagger> R2c(P) = R2c(post\<^sub>s \<dagger> P)"
  by (simp add: R2c_def R2s_def usubst)

lemma rea_pre_RH_design: "pre\<^sub>R(RH(P \<turnstile> Q)) = (\<not> R1(R2c(pre\<^sub>s \<dagger> (\<not> P))))"
  by (simp add: RH_R2c_def usubst R3c_def pre\<^sub>R_def pre\<^sub>s_design)

lemma rea_peri_RH_design: "peri\<^sub>R(RH(P \<turnstile> Q \<diamondop> R)) = R1(R2c(peri\<^sub>s \<dagger> (P \<Rightarrow> Q)))"
  by (simp add:RH_R2c_def usubst peri\<^sub>R_def R3c_def peri\<^sub>s_design)

lemma rea_post_RH_design: "post\<^sub>R(RH(P \<turnstile> Q \<diamondop> R)) = R1(R2c(post\<^sub>s \<dagger> (P \<Rightarrow> R)))"
  by (simp add:RH_R2c_def usubst post\<^sub>R_def R3c_def post\<^sub>s_design)

lemma CSP_reactive_tri_design_lemma:
  assumes "P is CSP"
  shows "RH((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f\<lbrakk>true/$wait\<acute>\<rbrakk> \<diamondop> P\<^sup>t\<^sub>f\<lbrakk>false/$wait\<acute>\<rbrakk>) = P"
  by (simp add: CSP_reactive_design assms wait'_cond_split)

lemma CSP_reactive_tri_design:
  assumes "P is CSP"
  shows "RH(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) = P"
proof -
  have "P = RH((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f\<lbrakk>true/$wait\<acute>\<rbrakk> \<diamondop> P\<^sup>t\<^sub>f\<lbrakk>false/$wait\<acute>\<rbrakk>)"
    by (simp add: CSP_reactive_tri_design_lemma assms)
  also have "... = RH(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
    apply (simp add: usubst)
    apply (subst design_subst_ok_ok'[THEN sym])
    apply (simp add: pre\<^sub>R_def peri\<^sub>R_def post\<^sub>R_def usubst unrest)
  done
  finally show ?thesis ..
qed

lemma R1_neg_R2s_pre_RH:
  assumes "P is CSP"
  shows "R1 (\<not> R2s(pre\<^sub>R(P))) = (\<not> (pre\<^sub>R(P)))"
proof -
  have "(\<not> pre\<^sub>R(P)) = (\<not> pre\<^sub>R(RH(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))))"
    by (simp add: CSP_reactive_tri_design assms)
  also have "... = R1(R2s(\<not> pre\<^sub>R(RH(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))))"
    by (rel_auto)
  also have "... = R1 (\<not> R2s(pre\<^sub>R(RH(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))))"
    by (simp add: R2s_not)
  also have "... = R1 (\<not> R2s(pre\<^sub>R(P)))"
    by (simp add: CSP_reactive_tri_design assms)
  finally show ?thesis ..
qed


lemma CSP_composition:
  assumes "P is CSP" "Q is CSP"
  shows "(P ;; Q) = \<^bold>R ((\<not> (\<not> pre\<^sub>R P ;; R1 true) \<and> \<not> (post\<^sub>R P \<and> \<not> $wait\<acute> ;; \<not> pre\<^sub>R Q)) \<turnstile>
                       (peri\<^sub>R P \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; post\<^sub>R Q))"
proof -
  have "(P ;; Q) = (\<^bold>R(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) ;; \<^bold>R(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q)))"
    by (simp add: CSP_reactive_tri_design assms(1) assms(2))
  also from assms have "... = \<^bold>R ((\<not> (\<not> pre\<^sub>R P ;; R1 true) \<and> \<not> (post\<^sub>R P \<and> \<not> $wait\<acute> ;; \<not> pre\<^sub>R Q)) \<turnstile>
        (peri\<^sub>R P \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; post\<^sub>R Q))"
    by (simp add: RH_tri_design_composition unrest R1_R2s_peri_RH R1_R2s_post_RH R1_neg_R2s_pre_RH)
  finally show ?thesis .
qed

lemma CSP_seqr_closure:
  assumes "P is CSP" "Q is CSP"
  shows "(P ;; Q) is CSP"
proof -
  have "(P ;; Q) = \<^bold>R ((\<not> (\<not> pre\<^sub>R P ;; R1 true) \<and> \<not> (post\<^sub>R P \<and> \<not> $wait\<acute> ;; \<not> pre\<^sub>R Q)) \<turnstile>
                       (peri\<^sub>R P \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; post\<^sub>R Q))"
    by (simp add: CSP_composition assms(1) assms(2))
  also have "... is CSP"
    by (simp add: RH_design_is_CSP add: unrest)
  finally show ?thesis .
qed

lemma skip_rea_reactive_design:
  "II\<^sub>r = RH(true \<turnstile> II)"
proof -
  have "RH(true \<turnstile> II) = R1(R2c(R3c(true \<turnstile> II)))"
    by (metis RH_R2c_def)
  also have "... = R1(R3c(R2c(true \<turnstile> II)))"
    by (metis R2c_R3c_commute RH_R2c_def)
  also have "... = R1(R3c(true \<turnstile> II))"
    by (simp add: design_def impl_alt_def R2c_disj R2c_not R2c_ok R2c_and R2c_skip_r R2c_ok')
  also have "... = R1(II\<^sub>r \<triangleleft> $wait \<triangleright> true \<turnstile> II)"
    by (metis R3c_def)
  also have "... = II\<^sub>r"
    by (rel_auto)
  finally show ?thesis ..
qed

lemma skip_rea_reactive_design':
  "II\<^sub>r = RH(true \<turnstile> \<lceil>II\<rceil>\<^sub>D)"
  by (metis aext_true rdesign_def skip_d_alt_def skip_d_def skip_rea_reactive_design)

lemma skip_rea_RD1_skip: "II\<^sub>r = RD1(II)"
  by (rel_auto)

lemma RH_design_subst_wait: "RH(P \<^sub>f \<turnstile> Q \<^sub>f) = RH(P \<turnstile> Q)"
  by (metis RH_subst_wait wait_false_design)

lemma RH_design_subst_wait_pre: "RH(P \<^sub>f \<turnstile> Q) = RH(P \<turnstile> Q)"
  by (subst RH_design_subst_wait[THEN sym], simp add: usubst RH_design_subst_wait)

lemma RH_design_subst_wait_post: "RH(P \<turnstile> Q \<^sub>f) = RH(P \<turnstile> Q)"
  by (subst RH_design_subst_wait[THEN sym], simp add: usubst RH_design_subst_wait)

lemma RH_peri_subst_false_wait: "RH(P \<turnstile> Q \<^sub>f \<diamondop> R) = RH(P \<turnstile> Q \<diamondop> R)"
  apply (subst RH_design_subst_wait_post[THEN sym])
  apply (simp add: usubst unrest)
  apply (metis RH_design_subst_wait RH_design_subst_wait_pre out_in_indep out_var_uvar unrest_false unrest_usubst_id unrest_usubst_upd vwb_lens.axioms(2) wait'_cond_subst wait_vwb_lens)
done

lemma RH_post_subst_false_wait: "RH(P \<turnstile> Q \<diamondop> R \<^sub>f) = RH(P \<turnstile> Q \<diamondop> R)"
  apply (subst RH_design_subst_wait_post[THEN sym])
  apply (simp add: usubst unrest)
  apply (metis RH_design_subst_wait RH_design_subst_wait_pre out_in_indep out_var_uvar unrest_false unrest_usubst_id unrest_usubst_upd vwb_lens.axioms(2) wait'_cond_subst wait_vwb_lens)
done

lemma skip_rea_reactive_tri_design:
  "II\<^sub>r = RH(true \<turnstile> false \<diamondop> \<lceil>II\<rceil>\<^sub>D)" (is "?lhs = ?rhs")
proof -
  have "?rhs = RH (true \<turnstile> (\<not> $wait\<acute> \<and> \<lceil>II\<rceil>\<^sub>D))"
    by (simp add: wait'_cond_def cond_def)
  have "... = RH (true \<turnstile> (\<not> $wait \<and> \<lceil>II\<rceil>\<^sub>D))" (is "RH (true \<turnstile> ?Q1) = RH (true \<turnstile> ?Q2)")
  proof -
    have "?Q1 = ?Q2"
      by (rel_auto)
    thus ?thesis by simp
  qed
  also have "... = RH (true \<turnstile> \<lceil>II\<rceil>\<^sub>D)"
    by (rel_auto)
  finally show ?thesis
    by (simp add: skip_rea_reactive_design' wait'_cond_def cond_def)
qed

lemma skip_d_lift_rea:
  "\<lceil>II\<rceil>\<^sub>D = ($wait\<acute> =\<^sub>u $wait \<and> $tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R)"
  by (rel_auto)

lemma skip_rea_reactive_tri_design':
  "II\<^sub>r = RH(true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R))" (is "?lhs = ?rhs")
proof -
  have "?rhs = RH (true \<turnstile> (\<not> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R))"
    by (simp add: wait'_cond_def cond_def)
  also have "... = RH (true \<turnstile> ($wait\<acute> =\<^sub>u $wait \<and> $tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R))" (is "RH (true \<turnstile> ?Q1) = RH (true \<turnstile> ?Q2)")
  proof -
    have "?Q1 \<^sub>f = ?Q2 \<^sub>f"
      by (rel_auto)
    thus ?thesis
      by (metis RH_design_subst_wait)
  qed
  also have "... = RH (true \<turnstile> \<lceil>II\<rceil>\<^sub>D)"
    by (metis skip_d_lift_rea)
  finally show ?thesis
    by (simp add: skip_rea_reactive_design')
qed

lemma R1_neg_pre: "R1 (\<not> pre\<^sub>R P) = (\<not> pre\<^sub>R (R1(P)))"
  by (simp add: pre\<^sub>R_def R1_def usubst)

lemma R1_peri: "R1 (peri\<^sub>R P) = peri\<^sub>R (R1(P))"
  by (simp add: peri\<^sub>R_def R1_def usubst)

lemma R1_post: "R1 (post\<^sub>R P) = post\<^sub>R (R1(P))"
  by (simp add: post\<^sub>R_def R1_def usubst)

lemma R2s_pre:
  "R2s (pre\<^sub>R P) = pre\<^sub>R (R2s P)"
  by (simp add: pre\<^sub>R_def R2s_def usubst)

lemma R2s_peri: "R2s (peri\<^sub>R P) = peri\<^sub>R (R2s P)"
  by (simp add: peri\<^sub>R_def R2s_def usubst)

lemma R2s_post: "R2s (post\<^sub>R P) = post\<^sub>R (R2s P)"
  by (simp add: post\<^sub>R_def R2s_def usubst)

lemma RH_pre_RH_design:
  "$ok\<acute> \<sharp> P \<Longrightarrow> RH(pre\<^sub>R(RH(P \<turnstile> Q)) \<turnstile> R) = RH(P \<turnstile> R)"
  apply (simp add: rea_pre_RH_design RH_design_pre_neg_R1_R2c usubst)
  apply (subst subst_to_singleton)
  apply (simp add: unrest)
  apply (simp add: RH_design_subst_wait_pre)
  apply (simp add: usubst)
  apply (metis conj_pos_var_subst design_def vwb_lens_ok)
done

lemma RH_postcondition: "(RH(P \<turnstile> Q))\<^sup>t\<^sub>f = R1(R2s($ok \<and> P\<^sup>t\<^sub>f \<Rightarrow> Q\<^sup>t\<^sub>f))"
  by (simp add: RH_def R1_def R3c_def usubst R2s_def design_def)

lemma RH_postcondition_RH: "RH(P \<turnstile> (RH(P \<turnstile> Q))\<^sup>t\<^sub>f) = RH(P \<turnstile> Q)"
proof -
  have "RH(P \<turnstile> (RH(P \<turnstile> Q))\<^sup>t\<^sub>f) = RH (P \<turnstile> ($ok \<and> P\<^sup>t\<^sub>f \<Rightarrow> Q\<^sup>t\<^sub>f))"
    by (simp add: RH_postcondition RH_design_export_R1[THEN sym] RH_design_export_R2s[THEN sym])
  also have "... = RH (P \<turnstile> ($ok \<and> P\<^sup>t \<Rightarrow> Q\<^sup>t))"
    by (subst RH_design_subst_wait_post[THEN sym, of _ "($ok \<and> P\<^sup>t \<Rightarrow> Q\<^sup>t)"], simp add: usubst)
  also have "... = RH (P \<turnstile> (P\<^sup>t \<Rightarrow> Q\<^sup>t))"
    by (rel_auto)
  also have "... = RH (P \<turnstile> (P \<Rightarrow> Q))"
    by (subst design_subst_ok'[THEN sym, of _ "P \<Rightarrow> Q"], simp add: usubst)
  also have "... = RH (P \<turnstile> Q)"
    by (rel_auto)
  finally show ?thesis .
qed

lemma peri\<^sub>R_alt_def: "peri\<^sub>R(P) = (P\<^sup>t\<^sub>f)\<lbrakk>true/$ok\<rbrakk>\<lbrakk>true/$wait\<acute>\<rbrakk>"
  by (simp add: peri\<^sub>R_def usubst)

lemma post\<^sub>R_alt_def: "post\<^sub>R(P) = (P\<^sup>t\<^sub>f)\<lbrakk>true/$ok\<rbrakk>\<lbrakk>false/$wait\<acute>\<rbrakk>"
  by (simp add: post\<^sub>R_def usubst)

lemma design_export_ok_true: "P \<turnstile> Q\<lbrakk>true/$ok\<rbrakk> = P \<turnstile> Q"
  by (metis conj_pos_var_subst design_export_ok vwb_lens_ok)

lemma design_export_peri_ok_true: "P \<turnstile> Q\<lbrakk>true/$ok\<rbrakk> \<diamondop> R = P \<turnstile> Q \<diamondop> R"
  apply (subst design_export_ok_true[THEN sym])
  apply (simp add: usubst unrest)
  apply (metis design_export_ok_true out_in_indep out_var_uvar unrest_true unrest_usubst_id unrest_usubst_upd vwb_lens_mwb wait'_cond_subst wait_vwb_lens)
done

lemma design_export_post_ok_true: "P \<turnstile> Q \<diamondop> R\<lbrakk>true/$ok\<rbrakk> = P \<turnstile> Q \<diamondop> R"
  apply (subst design_export_ok_true[THEN sym])
  apply (simp add: usubst unrest)
  apply (metis design_export_ok_true out_in_indep out_var_uvar unrest_true unrest_usubst_id unrest_usubst_upd vwb_lens_mwb wait'_cond_subst wait_vwb_lens)
done

lemma RH_peri_RH_design:
  "RH(P \<turnstile> peri\<^sub>R(RH(P \<turnstile> Q \<diamondop> R)) \<diamondop> S) = RH(P \<turnstile> Q \<diamondop> S)"
  apply (simp add: peri\<^sub>R_alt_def subst_wait'_left_subst design_export_peri_ok_true RH_postcondition)
  apply (simp add: rea_peri_RH_design RH_design_peri_R1 RH_design_peri_R2s)
oops

lemma R1_R2s_tr_diff_conj: "(R1 (R2s ($tr\<acute> =\<^sub>u $tr \<and> P))) = ($tr\<acute> =\<^sub>u $tr \<and> R2s(P))"
  apply (rel_auto) using minus_zero_eq by blast

lemma R2s_state'_eq_state: "R2s ($\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R) = ($\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R)"
  by (simp add: R2s_def usubst)

lemma skip_r_rea: "II = ($ok\<acute> =\<^sub>u $ok \<and> $wait\<acute> =\<^sub>u $wait \<and> $tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R)"
  by (rel_auto)

lemma wait_pre_lemma:
  assumes "$wait\<acute> \<sharp> P"
  shows "(P \<and> \<not> $wait\<acute> ;; \<not> pre\<^sub>R Q) = (P ;; \<not> pre\<^sub>R Q)"
proof -
  have "(P \<and> \<not> $wait\<acute> ;; \<not> pre\<^sub>R Q) = (P \<and> $wait\<acute> =\<^sub>u false ;; \<not> pre\<^sub>R Q)"
    by (rel_auto)
  also have "... = (P\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (\<not> pre\<^sub>R Q)\<lbrakk>false/$wait\<rbrakk>)"
    by (metis false_alt_def seqr_left_one_point wait_vwb_lens)
  also have "... = (P ;; \<not> pre\<^sub>R Q)"
    by (simp add: usubst unrest assms)
  finally show ?thesis .
qed

lemma rea_left_unit_lemma:
  assumes "$ok  \<sharp> P" "$wait \<sharp> P"
  shows "(($tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R) ;; P) = P"
proof -
  have "P = (II ;; P)"
    by simp
  also have "... = (($ok\<acute> =\<^sub>u $ok \<and> $wait\<acute> =\<^sub>u $wait \<and> $tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R) ;; P)"
    by (metis skip_r_rea)
  also from assms have "... = (($tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R) ;; P)"
    by (simp add: seqr_insert_ident_left assms unrest)
  finally show ?thesis ..
qed

lemma rea_right_unit_lemma:
  assumes "$ok\<acute>  \<sharp> P" "$wait\<acute> \<sharp> P"
  shows "(P ;; ($tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R)) = P"
proof -
  have "P = (P ;; II)"
    by simp
  also have "... = (P ;; ($ok\<acute> =\<^sub>u $ok \<and> $wait\<acute> =\<^sub>u $wait \<and> $tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R))"
    by (metis skip_r_rea)
  also from assms have "... = (P ;; ($tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R))"
    by (simp add: seqr_insert_ident_right assms unrest)
  finally show ?thesis ..
qed

lemma skip_rea_left_unit:
  assumes "P is CSP"
  shows "(II\<^sub>r ;; P) = P"
proof -
  have "(II\<^sub>r ;; P) = (II\<^sub>r ;; RH (pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P))"
    by (metis CSP_reactive_tri_design assms)
  also have "... = (RH(true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and>  $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R)) ;; RH (pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P))"
    by (metis skip_rea_reactive_tri_design')
  also have "... = RH (pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)"
    apply (subst RH_tri_design_composition)
    apply (simp_all add: unrest R2s_true R1_false R1_neg_pre R1_peri R1_post R2s_pre R2s_peri R2s_post CSP_R1_R2s R1_R2s_tr_diff_conj assms)
    apply (simp add: R2s_conj R2s_state'_eq_state wait_pre_lemma rea_left_unit_lemma unrest)
  done
  also have "... = P"
    by (metis CSP_reactive_tri_design assms)
  finally show ?thesis .
qed

text {* This theorem tells us that processes consisting of a precondition and upward closed
  predicate over tr have R1(true) as a right unit. *}

lemma R1_true_right_unit_form:
  "out\<alpha> \<sharp> c \<Longrightarrow> (\<not> (c \<and> \<not> ($tr\<acute> \<ge>\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<guillemotright>)) ;; R1(true)) = (\<not> (c \<and> \<not> ($tr\<acute> \<ge>\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<guillemotright>)))"
  by (rel_auto, blast)

lemma skip_rea_left_semi_unit:
  assumes "P is CSP"
  shows "(P ;; II\<^sub>r) = RH ((\<not> (\<not> pre\<^sub>R P ;; R1 true)) \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)"
proof -
  have "(P ;; II\<^sub>r) = (RH (pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P) ;; II\<^sub>r)"
    by (metis CSP_reactive_tri_design assms)
  also have "... = (RH (pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P) ;; RH(true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R)))"
    by (metis skip_rea_reactive_tri_design')
  also have "... = RH ((\<not> (\<not> pre\<^sub>R P ;; R1 true)) \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)"
    apply (subst RH_tri_design_composition)
    apply (simp_all add: unrest R2s_true R1_false R2s_false R1_neg_pre R1_peri R1_post R2s_pre R2s_peri R2s_post CSP_R1_R2s R1_R2s_tr_diff_conj assms)
    apply (simp add: R2s_conj R2s_state'_eq_state wait_pre_lemma rea_right_unit_lemma unrest)
  done
  finally show ?thesis .
qed

lemma HR_design_wait_false: "RH(P \<^sub>f \<turnstile> Q \<^sub>f) = RH(P \<turnstile> Q)"
  by (metis R3c_subst_wait RH_R2c_def wait_false_design)

lemma RH_design_R1_neg_precond: "RH((\<not> R1(\<not> P)) \<turnstile> Q) = RH(P \<turnstile> Q)"
  by (rel_auto)

lemma RH_design_pre_neg_conj_R1: "RH((\<not> R1 P \<and> \<not> R1 Q) \<turnstile> R) = RH((\<not> P \<and> \<not> Q) \<turnstile> R)"
  by (rel_auto)

subsection {* Signature *}

definition [urel_defs]: "Miracle = RH(true \<turnstile> false \<diamondop> false)"

definition [urel_defs]: "Chaos = RH(false \<turnstile> true \<diamondop> true)"

definition [urel_defs]: "Term = RH(true \<turnstile> true \<diamondop> true)"

definition assigns_rea :: "'\<alpha> usubst \<Rightarrow> ('t::ordered_cancel_monoid_diff, '\<alpha>) hrel_rp" ("\<langle>_\<rangle>\<^sub>R") where
"assigns_rea \<sigma> = RH(true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>R))"

definition rea_design_sup :: "_ set \<Rightarrow> _" ("\<Sqinter>\<^sub>R") where
"\<Sqinter>\<^sub>R A = (if (A = {}) then Miracle else \<Sqinter> A)"

definition rea_design_inf :: "_ set \<Rightarrow> _" ("\<Squnion>\<^sub>R") where
"\<Squnion>\<^sub>R A = (if (A = {}) then Chaos else \<Squnion> A)"

definition rea_design_par :: "_ \<Rightarrow> _ \<Rightarrow> _" (infixr "\<parallel>\<^sub>R" 85) where
"P \<parallel>\<^sub>R Q = RH((pre\<^sub>R(P)  \<and> pre\<^sub>R(Q)) \<turnstile> (P\<^sup>t\<^sub>f \<and> Q\<^sup>t\<^sub>f))"

lemma Miracle_greatest:
  assumes "P is CSP"
  shows "P \<sqsubseteq> Miracle"
proof -
  have "P = RH (pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
    by (metis CSP_reactive_tri_design assms)
  also have "... \<sqsubseteq> RH(true \<turnstile> false)"
    by (rule RH_monotone, rel_auto)
  also have "RH(true \<turnstile> false) = RH(true \<turnstile> false \<diamondop> false)"
    by (simp add: wait'_cond_def cond_def)
  finally show ?thesis
    by (simp add: Miracle_def)
qed

lemma Chaos_least:
  assumes "P is CSP"
  shows "Chaos \<sqsubseteq> P"
proof -
  have "Chaos = RH(true)"
    by (simp add: Chaos_def design_def)
  also have "... \<sqsubseteq> RH(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
    by (simp add: RH_monotone)
  also have "RH(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) = P"
    by (metis CSP_reactive_tri_design assms)
  finally show ?thesis .
qed

lemma Miracle_left_zero:
  assumes "P is CSP"
  shows "(Miracle ;; P) = Miracle"
proof -
  have "(Miracle ;; P) = (RH(true \<turnstile> false \<diamondop> false) ;; RH (pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))"
    by (metis CSP_reactive_tri_design Miracle_def assms)
  also have "... = RH(true \<turnstile> false \<diamondop> false)"
    by (simp add: RH_tri_design_composition R1_false R2s_true R2s_false R2c_true R1_true_comp unrest usubst)
  also have "... = Miracle"
    by (simp add: Miracle_def)
  finally show ?thesis .
qed

lemma Chaos_def': "Chaos = RH(false \<turnstile> true)"
  by (simp add: Chaos_def design_false_pre)

lemma Miracle_CSP_false: "Miracle = CSP(false)"
  by (rel_auto)

lemma Chaos_CSP_true: "Chaos = CSP(true)"
  by (rel_auto)

lemma Chaos_left_zero:
  assumes "P is CSP"
  shows "(Chaos ;; P) = Chaos"
proof -
  have "(Chaos ;; P) = (RH(false \<turnstile> true \<diamondop> true) ;; RH (pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))"
    by (metis CSP_reactive_tri_design Chaos_def assms)
  also have "... = RH ((\<not> R1 true \<and> \<not> (R1 true \<and> \<not> $wait\<acute> ;; R1 (\<not> R2c (pre\<^sub>R P)))) \<turnstile>
                       (true \<or> (R1 true ;; R1 (R2c (peri\<^sub>R P)))) \<diamondop> (R1 true ;; R1 (R2c (post\<^sub>R P))))"
    by (simp add: RH_tri_design_composition R2s_true R1_true_comp R2s_false unrest, metis (no_types) R1_R2s_R2c R1_negate_R1)
  also have "... = RH ((\<not> $ok \<or> R1 true \<or> (R1 true \<and> \<not> $wait\<acute> ;; R1 (\<not> R2c (pre\<^sub>R P)))) \<or>
                       $ok\<acute> \<and> (true \<or> (R1 true ;; R1 (R2c (peri\<^sub>R P)))) \<diamondop> (R1 true ;; R1 (R2c (post\<^sub>R P))))"
    by (simp add: design_def impl_alt_def)
  also have "... = RH(R1((\<not> $ok \<or> R1 true \<or> (R1 true \<and> \<not> $wait\<acute> ;; R1 (\<not> R2c (pre\<^sub>R P)))) \<or>
                      $ok\<acute> \<and> (true \<or> (R1 true ;; R1 (R2c (peri\<^sub>R P)))) \<diamondop> (R1 true ;; R1 (R2c (post\<^sub>R P)))))"
    by (simp add: R1_R2c_commute R1_R3c_commute R1_idem RH_R2c_def)
  also have "... = RH(R1((\<not> $ok \<or> true \<or> (R1 true \<and> \<not> $wait\<acute> ;; R1 (\<not> R2c (pre\<^sub>R P)))) \<or>
                      $ok\<acute> \<and> (true \<or> (R1 true ;; R1 (R2c (peri\<^sub>R P)))) \<diamondop> (R1 true ;; R1 (R2c (post\<^sub>R P)))))"
    by (metis (no_types, hide_lams) R1_disj R1_idem)
  also have "... = RH(true)"
    by (simp add: R1_R2c_commute R1_R3c_commute R1_idem RH_R2c_def)
  also have "... = Chaos"
    by (simp add: Chaos_def design_def)
  finally show ?thesis .
qed

lemma RH_design_choice:
  "(RH(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) \<sqinter> RH(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)) = RH((P \<and> R) \<turnstile> ((Q\<^sub>1 \<or> S\<^sub>1) \<diamondop> (Q\<^sub>2 \<or> S\<^sub>2)))"
proof -
  have "(RH(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) \<sqinter> RH(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)) = RH((P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) \<sqinter> (R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2))"
    by (simp add: disj_upred_def[THEN sym] RH_disj[THEN sym])
  also have "... = RH ((P \<and> R) \<turnstile> (Q\<^sub>1 \<diamondop> Q\<^sub>2 \<or> S\<^sub>1 \<diamondop> S\<^sub>2))"
    by (simp add: design_choice)
  also have "... = RH ((P \<and> R) \<turnstile> ((Q\<^sub>1 \<or> S\<^sub>1) \<diamondop> (Q\<^sub>2 \<or> S\<^sub>2)))"
  proof -
    have "(Q\<^sub>1 \<diamondop> Q\<^sub>2 \<or> S\<^sub>1 \<diamondop> S\<^sub>2) = ((Q\<^sub>1 \<or> S\<^sub>1) \<diamondop> (Q\<^sub>2 \<or> S\<^sub>2))"
      by (rel_auto)
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma USUP_CSP_closed:
  assumes "A \<noteq> {}" "\<forall> P \<in> A. P is CSP"
  shows "(\<Sqinter> A) is CSP"
proof -
  from assms have A: "A = CSP ` A"
    by (auto simp add: Healthy_def rev_image_eqI)
  also have "(\<Sqinter> ...) = (\<Sqinter> P \<in> A. CSP(P))"
    by auto
  also have "... = (\<Sqinter> P \<in> A \<bullet> CSP(P))"
    by (simp add: USUP_as_Sup_collect)
  also have "... = (\<Sqinter> P \<in> A \<bullet> RH((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f))"
    by (metis (no_types) CSP_RH_design_form)
  also have "... = RH(\<Sqinter> P \<in> A \<bullet> (\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (simp add: RH_USUP assms(1))
  also have "... = RH((\<Squnion> P \<in> A \<bullet> \<not> P\<^sup>f\<^sub>f) \<turnstile> (\<Sqinter> P \<in> A \<bullet> P\<^sup>t\<^sub>f))"
    by (simp add: design_USUP assms)
  also have "... = CSP(...)"
    by (simp add: CSP_RH_design unrest)
  finally show ?thesis
    by (simp add: Healthy_def CSP_idem)
qed

lemma UINF_CSP_closed:
  assumes "A \<noteq> {}" "\<forall> P \<in> A. P is CSP"
  shows "(\<Squnion> A) is CSP"
proof -
  from assms have A: "A = CSP ` A"
    by (auto simp add: Healthy_def rev_image_eqI)
  also have "(\<Squnion> ...) = (\<Squnion> P \<in> A. CSP(P))"
    by auto
  also have "... = (\<Squnion> P \<in> A \<bullet> CSP(P))"
    by (simp add: UINF_as_Inf_collect)
  also have "... = (\<Squnion> P \<in> A \<bullet> RH((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f))"
    by (simp add: CSP_RH_design_form)
  also have "... = RH(\<Squnion> P \<in> A \<bullet> (\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (simp add: RH_UINF assms(1))
  also have "... = RH ((\<Sqinter> P \<in> A \<bullet> \<not> P\<^sup>f\<^sub>f) \<turnstile> (\<Squnion> P \<in> A \<bullet> \<not> P\<^sup>f\<^sub>f \<Rightarrow> P\<^sup>t\<^sub>f))"
    by (simp add: design_UINF)
  also have "... = CSP(...)"
    by (simp add: CSP_RH_design unrest)
  finally show ?thesis
    by (simp add: Healthy_def CSP_idem)
qed

lemma CSP_sup_closed:
  assumes "\<forall> P \<in> A. P is CSP"
  shows "(\<Sqinter>\<^sub>R A) is CSP"
proof (cases "A = {}")
  case True
  moreover have "Miracle is CSP"
    by (simp add: Miracle_def Healthy_def CSP_RH_design unrest)
  ultimately show ?thesis
    by (simp add: rea_design_sup_def)
next
  case False
  with USUP_CSP_closed assms show ?thesis
    by (auto simp add: rea_design_sup_def)
qed

lemma CSP_sup_below:
  assumes "\<forall> Q \<in> A. Q is CSP" "P \<in> A"
  shows "\<Sqinter>\<^sub>R A \<sqsubseteq> P"
  using assms
  by (auto simp add: rea_design_sup_def Sup_upper)

lemma CSP_sup_upper_bound:
  assumes "\<forall> Q \<in> A. Q is CSP" "\<forall> Q \<in> A. P \<sqsubseteq> Q" "P is CSP"
  shows "P \<sqsubseteq> \<Sqinter>\<^sub>R A"
proof (cases "A = {}")
  case True
  thus ?thesis
    by (simp add: rea_design_sup_def Miracle_greatest assms)
next
  case False
  thus ?thesis
    by (simp add: rea_design_sup_def cSup_least assms)
qed

lemma CSP_inf_closed:
  assumes "\<forall> P \<in> A. P is CSP"
  shows "(\<Squnion>\<^sub>R A) is CSP"
proof (cases "A = {}")
  case True
  moreover have "Chaos is CSP"
    by (simp add: Chaos_def Healthy_def CSP_RH_design unrest)
  ultimately show ?thesis
    by (simp add: rea_design_inf_def)
next
  case False
  with UINF_CSP_closed assms show ?thesis
    by (auto simp add: rea_design_inf_def)
qed

lemma CSP_inf_above:
  assumes "\<forall> Q \<in> A. Q is CSP" "P \<in> A"
  shows "P \<sqsubseteq> \<Squnion>\<^sub>R A"
  using assms
  by (auto simp add: rea_design_inf_def Inf_lower)

lemma CSP_inf_lower_bound:
  assumes "\<forall> P \<in> A. P is CSP" "\<forall> P \<in> A. P \<sqsubseteq> Q" "Q is CSP"
  shows "\<Squnion>\<^sub>R A \<sqsubseteq> Q"
proof (cases "A = {}")
  case True
  thus ?thesis
    by (simp add: rea_design_inf_def Chaos_least assms)
next
  case False
  thus ?thesis
    by (simp add: rea_design_inf_def cInf_greatest assms)
qed

lemma assigns_lift_rea_unfold:
  "($wait\<acute> =\<^sub>u $wait \<and> $tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>R) = \<lceil>\<langle>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>r\<rangle>\<^sub>a\<rceil>\<^sub>D"
  by (rel_auto)

lemma assigns_lift_des_unfold:
  "($ok\<acute> =\<^sub>u $ok \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>D) = \<langle>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>D\<rangle>\<^sub>a"
  by (rel_auto)

lemma assigns_rea_comp_lemma:
  assumes "$ok \<sharp> P" "$wait \<sharp> P"
  shows "(($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>R) ;; P) = (\<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> P)"
proof -
  have "(($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>R) ;; P) =
        (($ok\<acute> =\<^sub>u $ok \<and> $wait\<acute> =\<^sub>u $wait \<and> $tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>R) ;; P)"
    by (simp add: seqr_insert_ident_left unrest assms)
  also have "... = (\<langle>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rangle>\<^sub>a ;; P)"
    by (simp add: assigns_lift_rea_unfold assigns_lift_des_unfold, rel_auto)
  also have "... = (\<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> P)"
    by (simp add: assigns_r_comp)
  finally show ?thesis .
qed

lemma R1_R2s_frame:
  "R1 (R2s ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>P\<rceil>\<^sub>R)) = ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>P\<rceil>\<^sub>R)"
    apply (rel_auto)
    using minus_zero_eq apply blast
done

lemma assigns_rea_comp:
  assumes "$ok \<sharp> P" "$ok \<sharp> Q\<^sub>1" "$ok \<sharp> Q\<^sub>2" "$wait \<sharp> P" "$wait \<sharp> Q\<^sub>1" "$wait \<sharp> Q\<^sub>2"
          "Q\<^sub>1 is R1" "Q\<^sub>2 is R1" "P is R2s" "Q\<^sub>1 is R2s" "Q\<^sub>2 is R2s"
  shows "(\<langle>\<sigma>\<rangle>\<^sub>R ;; RH(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2)) = RH(\<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> P \<turnstile> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> Q\<^sub>1 \<diamondop> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> Q\<^sub>2)"
proof -
  have "(\<langle>\<sigma>\<rangle>\<^sub>R ;; RH(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2)) =
        (RH (true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>R)) ;; RH (P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2))"
    by (simp add: assigns_rea_def)
  also have "... = RH ((\<not> (($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>R) \<and> \<not> $wait\<acute> ;;
                       R1 (\<not> P))) \<turnstile> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> Q\<^sub>1 \<diamondop> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> Q\<^sub>2)"
    by (simp add: RH_tri_design_composition unrest assms R2s_true R1_false R1_R2s_frame Healthy_if assigns_rea_comp_lemma)
  also have "... = RH ((\<not> (($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>R) \<and> $wait\<acute> =\<^sub>u \<guillemotleft>False\<guillemotright> ;;
                       R1 (\<not> P))) \<turnstile> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> Q\<^sub>1 \<diamondop> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> Q\<^sub>2)"
    by (simp add: false_alt_def[THEN sym])
  also have "... = RH ((\<not> (($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>R)\<lbrakk>false/$wait\<acute>\<rbrakk> ;;
                       (R1 (\<not> P))\<lbrakk>false/$wait\<rbrakk>)) \<turnstile> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> Q\<^sub>1 \<diamondop> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> Q\<^sub>2)"
    by (simp add: seqr_left_one_point false_alt_def)
  also have "... = RH ((\<not> (($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>R) ;; (R1 (\<not> P)))) \<turnstile> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> Q\<^sub>1 \<diamondop> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> Q\<^sub>2)"
    by (simp add: R1_def usubst unrest assms)
  also have "... = RH ((\<not> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> R1 (\<not> P)) \<turnstile> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> Q\<^sub>1 \<diamondop> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> Q\<^sub>2)"
    by (simp add: assigns_rea_comp_lemma assms unrest)
  also have "... = RH ((\<not> R1 (\<not> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> P)) \<turnstile> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> Q\<^sub>1 \<diamondop> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> Q\<^sub>2)"
    by (simp add: R1_def usubst unrest)
  also have "... = RH ((\<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> P) \<turnstile> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> Q\<^sub>1 \<diamondop> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>R\<rceil>\<^sub>s \<dagger> Q\<^sub>2)"
    by (simp add: RH_design_R1_neg_precond)
  finally show ?thesis .
qed

lemma RH_design_par:
  assumes
    "$ok\<acute> \<sharp> P\<^sub>1" "$wait \<sharp> P\<^sub>1" "$ok\<acute> \<sharp> P\<^sub>2" "$wait \<sharp> P\<^sub>2"
    "$ok\<acute> \<sharp> Q\<^sub>1" "$wait \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> Q\<^sub>2"
  shows "RH(P\<^sub>1 \<turnstile> Q\<^sub>1) \<parallel>\<^sub>R RH(P\<^sub>2 \<turnstile> Q\<^sub>2) = RH((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<and> Q\<^sub>2))"
proof -
  have "RH(P\<^sub>1 \<turnstile> Q\<^sub>1) \<parallel>\<^sub>R RH(P\<^sub>2 \<turnstile> Q\<^sub>2) =
        RH ((\<not> R1 (R2c (\<not> P\<^sub>1\<lbrakk>true/$ok\<rbrakk>)) \<and> \<not> R1 (R2c (\<not> P\<^sub>2\<lbrakk>true/$ok\<rbrakk>))) \<turnstile>
            (R1 (R2s ($ok \<and> P\<^sub>1 \<Rightarrow> Q\<^sub>1)) \<and> R1 (R2s ($ok \<and> P\<^sub>2 \<Rightarrow> Q\<^sub>2))))"
    by (simp add: rea_design_par_def rea_pre_RH_design RH_postcondition, simp add: usubst assms)
  also have "... =
        RH ((P\<^sub>1\<lbrakk>true/$ok\<rbrakk> \<and> P\<^sub>2\<lbrakk>true/$ok\<rbrakk>) \<turnstile>
            (R1 (R2s ($ok \<and> P\<^sub>1 \<Rightarrow> Q\<^sub>1)) \<and> R1 (R2s ($ok \<and> P\<^sub>2 \<Rightarrow> Q\<^sub>2))))"
    by (metis (no_types, hide_lams) R2c_and R2c_not RH_design_pre_R2c RH_design_pre_neg_conj_R1 double_negation)
  also have "... = RH ((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (R1 (R2s ($ok \<and> P\<^sub>1 \<Rightarrow> Q\<^sub>1)) \<and> R1 (R2s ($ok \<and> P\<^sub>2 \<Rightarrow> Q\<^sub>2))))"
    by (metis conj_pos_var_subst design_def subst_conj vwb_lens_ok)
  also have "... = RH ((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (R1 (R2s (($ok \<and> P\<^sub>1 \<Rightarrow> Q\<^sub>1) \<and> ($ok \<and> P\<^sub>2 \<Rightarrow> Q\<^sub>2)))))"
    by (simp add: R1_conj R2s_conj)
  also have "... = RH ((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (($ok \<and> P\<^sub>1 \<Rightarrow> Q\<^sub>1) \<and> ($ok \<and> P\<^sub>2 \<Rightarrow> Q\<^sub>2)))"
        by (metis (mono_tags, lifting) RH_design_export_R1 RH_design_export_R2s)
  also have "... = RH ((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<and> Q\<^sub>2))"
    by (rel_auto)
  finally show ?thesis .
qed

lemma RH_tri_design_par:
  assumes
    "$ok\<acute> \<sharp> P\<^sub>1" "$wait \<sharp> P\<^sub>1" "$ok\<acute> \<sharp> P\<^sub>2" "$wait \<sharp> P\<^sub>2"
    "$ok\<acute> \<sharp> Q\<^sub>1" "$wait \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> Q\<^sub>2"
    "$ok\<acute> \<sharp> R\<^sub>1" "$wait \<sharp> R\<^sub>1" "$ok\<acute> \<sharp> R\<^sub>2" "$wait \<sharp> R\<^sub>2"
  shows "RH(P\<^sub>1 \<turnstile> Q\<^sub>1 \<diamondop> R\<^sub>1) \<parallel>\<^sub>R RH(P\<^sub>2 \<turnstile> Q\<^sub>2 \<diamondop> R\<^sub>2) = RH((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<and> Q\<^sub>2) \<diamondop> (R\<^sub>1 \<and> R\<^sub>2))"
  by (simp add: RH_design_par assms unrest wait'_cond_conj_exchange)

lemma RH_design_par_comm:
  "P \<parallel>\<^sub>R Q = Q \<parallel>\<^sub>R P"
  by (simp add: rea_design_par_def utp_pred.inf_commute)

lemma RH_design_par_zero:
  assumes "P is CSP"
  shows "Chaos \<parallel>\<^sub>R P = Chaos"
proof -
  have "Chaos \<parallel>\<^sub>R P = RH (false \<turnstile> true \<diamondop> true) \<parallel>\<^sub>R RH (pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
    by (simp add: Chaos_def CSP_reactive_tri_design assms)
  also have "... = RH (false \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)"
    by (simp add: RH_tri_design_par unrest)
  also have "... = Chaos"
    by (simp add: Chaos_def design_false_pre)
  finally show ?thesis .
qed

lemma RH_design_par_unit:
  assumes "P is CSP"
  shows "Term \<parallel>\<^sub>R P = P"
proof -
  have "Term \<parallel>\<^sub>R P = RH (true \<turnstile> true \<diamondop> true) \<parallel>\<^sub>R RH (pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
    by (simp add: Term_def CSP_reactive_tri_design assms)
  also have "... = RH (pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)"
    by (simp add: RH_tri_design_par unrest)
  also have "... = P"
    by (simp add: CSP_reactive_tri_design assms)
  finally show ?thesis .
qed

subsection {* Complete lattice *}

typedecl RDES
typedecl R1DES

abbreviation "R1DES \<equiv> UTHY(R1DES, ('t::ordered_cancel_monoid_diff,'\<alpha>) alphabet_rp)"

overloading
  r1des_hcond   == "utp_hcond :: (R1DES, ('t::ordered_cancel_monoid_diff,'\<alpha>) alphabet_rp) uthy \<Rightarrow> (('t,'\<alpha>) alphabet_rp \<times> ('t,'\<alpha>) alphabet_rp) Healthiness_condition"
begin
  definition r1des_hcond :: "(R1DES, ('t::ordered_cancel_monoid_diff,'\<alpha>) alphabet_rp) uthy \<Rightarrow> (('t,'\<alpha>) alphabet_rp \<times> ('t,'\<alpha>) alphabet_rp) Healthiness_condition" where
  [upred_defs]: "r1des_hcond T = R1 \<circ> \<^bold>H"
end

interpretation r1des_theory: utp_theory "UTHY(R1DES, ('t::ordered_cancel_monoid_diff,'\<alpha>) alphabet_rp)"
  by (unfold_locales, simp_all add: r1des_hcond_def, metis RD1_R1_H1 H1_H2_idempotent H2_R1_comm R1_idem)

abbreviation "RDES \<equiv> UTHY(RDES, ('t::ordered_cancel_monoid_diff,'\<alpha>) alphabet_rp)"

overloading
  rdes_hcond   == "utp_hcond :: (RDES, ('t::ordered_cancel_monoid_diff,'\<alpha>) alphabet_rp) uthy \<Rightarrow> (('t,'\<alpha>) alphabet_rp \<times> ('t,'\<alpha>) alphabet_rp) Healthiness_condition"
begin
  definition rdes_hcond :: "(RDES, ('t::ordered_cancel_monoid_diff,'\<alpha>) alphabet_rp) uthy \<Rightarrow> (('t,'\<alpha>) alphabet_rp \<times> ('t,'\<alpha>) alphabet_rp) Healthiness_condition" where
  [upred_defs]: "rdes_hcond T = CSP"
end

interpretation rdes_theory: utp_theory "UTHY(RDES, ('t::ordered_cancel_monoid_diff,'\<alpha>) alphabet_rp)"
  by (unfold_locales, simp_all add: rdes_hcond_def CSP_idem)

lemma Miracle_is_top: "\<^bold>\<top>\<^bsub>RDES\<^esub> = Miracle"
  apply (auto intro!:some_equality simp add: atop_def some_equality greatest_def utp_order_def rdes_hcond_def)
  apply (metis CSP_sup_closed emptyE rea_design_sup_def)
  using Miracle_greatest apply blast
  apply (metis CSP_sup_closed dual_order.antisym equals0D rea_design_sup_def Miracle_greatest)
done

lemma Chaos_is_bot: "\<^bold>\<bottom>\<^bsub>RDES\<^esub> = Chaos"
  apply (auto intro!:some_equality simp add: abottom_def some_equality least_def utp_order_def rdes_hcond_def)
  apply (metis CSP_inf_closed emptyE rea_design_inf_def)
  using Chaos_least apply blast
  apply (metis Chaos_least CSP_inf_closed dual_order.antisym equals0D rea_design_inf_def)
done

interpretation hrd_lattice: utp_theory_lattice "UTHY(RDES, ('t::ordered_cancel_monoid_diff,'\<alpha>) alphabet_rp)"
  rewrites "carrier (uthy_order RDES) = \<lbrakk>CSP\<rbrakk>\<^sub>H"
  and "\<top>\<^bsub>uthy_order RDES\<^esub> = Miracle"
  and "\<bottom>\<^bsub>uthy_order RDES\<^esub> = Chaos"
  apply (unfold_locales)
  apply (simp_all add: Miracle_is_top Chaos_is_bot)
  apply (simp_all add: utp_order_def rdes_hcond_def)
  apply (rename_tac A)
  apply (rule_tac x="\<Squnion>\<^sub>R A" in exI, auto intro:CSP_inf_above CSP_inf_lower_bound CSP_inf_closed simp add: least_def Upper_def CSP_inf_above)
  apply (rename_tac A)
  apply (rule_tac x="\<Sqinter>\<^sub>R A" in exI, auto intro:CSP_sup_below CSP_sup_upper_bound CSP_sup_closed simp add: greatest_def Lower_def CSP_inf_above)
done

abbreviation rdes_lfp :: "_ \<Rightarrow> _" ("\<mu>\<^sub>R") where
"\<mu>\<^sub>R F \<equiv> \<mu>\<^bsub>uthy_order RDES\<^esub> F"

abbreviation rdes_gfp :: "_ \<Rightarrow> _" ("\<nu>\<^sub>R") where
"\<nu>\<^sub>R F \<equiv> \<nu>\<^bsub>uthy_order RDES\<^esub> F"

lemma rdes_lfp_copy: "\<lbrakk> mono F; F \<in> \<lbrakk>CSP\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>CSP\<rbrakk>\<^sub>H \<rbrakk> \<Longrightarrow> \<mu>\<^sub>R F = F (\<mu>\<^sub>R F)"
  by (metis hrd_lattice.LFP_unfold mono_Monotone_utp_order)

lemma rdes_gfp_copy: "\<lbrakk> mono F; F \<in> \<lbrakk>CSP\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>CSP\<rbrakk>\<^sub>H \<rbrakk> \<Longrightarrow> \<nu>\<^sub>R F = F (\<nu>\<^sub>R F)"
  by (metis hrd_lattice.GFP_unfold mono_Monotone_utp_order)

lemma RH_H1_H2_eq_CSP: "\<^bold>R (\<^bold>H P) = CSP P"
  by (metis (no_types, lifting) RD1_R1_H1 RD1_R2c_commute RD1_R3c_commute RD2_def R1_H2_commute R1_R2c_commute R1_R2c_is_R2 R2_R3c_commute R2c_H2_commute R3c_H2_commute RH_alt_def'')

lemma Des_Rea_galois_lemma_1: "R1(\<^bold>H(R1(P))) \<sqsubseteq> R1(P)"
  by (rel_auto)

lemma "\<^bold>R(CSP(P)) = CSP(P)"
  by (rel_auto)

lemma "galois_connection (R2a' \<Leftarrow>\<langle>R2a',id\<rangle>\<Rightarrow> id)"
proof (simp add: mk_conn_def, rule galois_connectionI', simp_all add: utp_partial_order)
  show "id \<in> \<lbrakk>R2a'\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>id\<rbrakk>\<^sub>H"
    using Healthy_Idempotent Idempotent_id by blast
  show "R2a' \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>R2a'\<rbrakk>\<^sub>H"
    by (simp add: Healthy_def R2a'_idem)
  show "isotone (utp_order R2a') (utp_order id) id"
    by (simp add: isotone_utp_orderI)
  show "isotone (utp_order id) (utp_order R2a') R2a'"
  by (simp add: Monotonic_def R2a'_mono isotone_utp_orderI)
  show "\<And> X. X is id \<Longrightarrow> R2a' X \<sqsubseteq> X"
    using R2a'_weakening by blast
  show "\<And> X. X is R2a' \<Longrightarrow> X \<sqsubseteq> R2a' X"
    by (simp add: Healthy_def)
qed

lemma Des_Rea_galois_lemma_2: "CSP(P) \<sqsubseteq> \<^bold>H(\<^bold>R(CSP(P)))"
  apply (rel_auto)
oops

lemma R2c_H1_H2_commute: "R2c(\<^bold>H(P)) = \<^bold>H(R2c(P))"
  by (rel_auto)

lemma funcset_into_Idempotent: "Idempotent H \<Longrightarrow> H \<in> X \<rightarrow> \<lbrakk>H\<rbrakk>\<^sub>H"
  by (simp add: Healthy_def' Idempotent_def)

interpretation galois_connection "R1DES \<leftarrow>\<langle>id,R2c \<circ> R3c\<rangle>\<rightarrow> RDES"
proof (simp add: mk_conn_def, rule galois_connectionI', simp_all add: utp_partial_order r1des_hcond_def rdes_hcond_def)
  show "R2c \<circ> R3c \<in> \<lbrakk>R1 \<circ> \<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>CSP\<rbrakk>\<^sub>H"
    by (simp add: Pi_iff Healthy_def', metis R1_R2c_commute R1_R3c_commute R3c_idem RH_H1_H2_eq_CSP RH_absorbs_R2c RH_alt_def'')
  show "id \<in> \<lbrakk>CSP\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>R1 \<circ> \<^bold>H\<rbrakk>\<^sub>H"
    by (simp add: Pi_iff Healthy_def', metis RD1_via_H1 RD2_def RH_H1_H2_eq_CSP RH_alt_def RH_alt_def' RH_idem)
  show "isotone (utp_order (R1 \<circ> \<^bold>H)) (utp_order CSP) (R2c \<circ> R3c)"
    by (auto intro: isotone_utp_orderI Monotonic_comp R2c_Monotonic R3c_Monotonic)
  show "isotone (utp_order CSP) (utp_order (R1 \<circ> \<^bold>H)) id"
    by (auto intro: isotone_utp_orderI Monotonic_comp Monotonic_id)
  show "\<And> P. P is CSP \<Longrightarrow> R2c (R3c P) \<sqsubseteq> P"
    by (metis (no_types, lifting) CSP_R1_R2s CSP_healths(3) Healthy_def' R1_R2c_commute R2c_R2s_absorb eq_refl)
  show "\<And> P. P is R1 \<circ> \<^bold>H \<Longrightarrow> P \<sqsubseteq> R2c (R3c P)"
oops

interpretation Des_Rea_galois: galois_connection "DES \<leftarrow>\<langle>\<^bold>H,\<^bold>R\<rangle>\<rightarrow> RDES"
proof (simp add: mk_conn_def, rule galois_connectionI', simp_all add: utp_partial_order rdes_hcond_def des_hcond_def)
  show "\<^bold>R \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>CSP\<rbrakk>\<^sub>H"
    by (metis (no_types, lifting) CSP_idem Healthy_def' Pi_I' RH_H1_H2_eq_CSP mem_Collect_eq)
  show "\<^bold>H \<in> \<lbrakk>CSP\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
    by (rule funcset_into_Idempotent, rule H1_H2_Idempotent)
  show "isotone (utp_order \<^bold>H) (utp_order CSP) \<^bold>R"
    by (rule isotone_utp_orderI, metis rea_hcond_def rea_utp_theory_mono.HCond_Mono)
  show "isotone (utp_order CSP) (utp_order \<^bold>H) \<^bold>H"
    by (rule isotone_utp_orderI, simp add: H1_H2_monotonic)
  show "\<And> X. X is CSP \<Longrightarrow> \<^bold>R (\<^bold>H X) \<sqsubseteq> X"
    by (simp add: CSP_RH_design_form CSP_reactive_design RH_H1_H2_eq_CSP)
  show "\<And> X. X is \<^bold>H \<Longrightarrow> X \<sqsubseteq> \<^bold>H (\<^bold>R X)"
  proof -
    fix P :: "('t::ordered_cancel_monoid_diff,'\<alpha>) hrel_rp"
    assume "P is \<^bold>H"
    hence "(P \<sqsubseteq> \<^bold>H (\<^bold>R P)) \<longleftrightarrow> (\<^bold>H(P) \<sqsubseteq> \<^bold>H(\<^bold>R(\<^bold>H(P))))"
      by (simp add: Healthy_def')
    also have "... \<longleftrightarrow> (\<^bold>H(P) \<sqsubseteq> \<^bold>H(R1(\<^bold>H(P))))"
      oops

subsection {* Reactive design parallel-by-merge *}

definition [upred_defs]: "nil\<^sub>r\<^sub>m = (nil\<^sub>m \<triangleleft> $0-ok \<and> $1-ok \<triangleright> $tr\<^sub>< \<le>\<^sub>u $tr\<acute>)"

text {* @{term "nil\<^sub>r\<^sub>m"} is the parallel system which does nothing if the parallel predicates have both
  terminated ($0.ok \wedge 1.ok$), and otherwise guarantees only the merged trace gets longer. *}

definition [upred_defs]: "div\<^sub>m = ($tr \<le>\<^sub>u $0-tr\<acute> \<and> $tr \<le>\<^sub>u $1-tr\<acute> \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>)"

text {* @{term "div\<^sub>m"} is the parallel system where both sides traces get longer than the initial
  trace and identifies the before values of the variables. *}

definition [upred_defs]: "wait\<^sub>m = skip\<^sub>m\<lbrakk>true,true/$ok,$wait\<rbrakk>"

text {* @{term "wait\<^sub>m"} is the parallel system where ok and wait are both true and all other variables
  are identified .*}


text {* R3c implicitly depends on RD1, and therefore it requires that both sides be RD1. We also
  require that both sides are R3c, and that @{term "wait\<^sub>m"} is a quasi-unit, and @{term "div\<^sub>m"} yields
  divergence. *}

lemma R3c_par_by_merge:
  assumes
    "P is R1" "Q is R1" "P is RD1" "Q is RD1" "P is R3c" "Q is R3c"
    "(wait\<^sub>m ;; M) = II\<lbrakk>true,true/$ok,$wait\<rbrakk>" "(div\<^sub>m ;; M) = R1(true)"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is R3c"
proof -
  have "(P \<parallel>\<^bsub>M\<^esub> Q) = (((P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true/$ok\<rbrakk> \<triangleleft> $ok \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk>)\<lbrakk>true/$wait\<rbrakk> \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (metis cond_idem cond_var_subst_left cond_var_subst_right vwb_lens_ok wait_vwb_lens)
  also have "... = (((P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true,true/$ok,$wait\<rbrakk> \<triangleleft> $ok \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk>)\<lbrakk>true/$wait\<rbrakk> \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (rel_auto)
  also have "... = (((P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true,true/$ok,$wait\<rbrakk> \<triangleleft> $ok \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk>) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (metis cond_var_subst_left wait_vwb_lens)
  also have "... = ((II\<lbrakk>true,true/$ok,$wait\<rbrakk> \<triangleleft> $ok \<triangleright> R1(true)) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
  proof -
    have "(P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk> = R1(true)"
    proof -
      have "(P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk> = ((P \<triangleleft> $ok \<triangleright> R1(true)) \<parallel>\<^bsub>M\<^esub> (Q \<triangleleft> $ok \<triangleright> R1(true)))\<lbrakk>false/$ok\<rbrakk>"
        by (metis RD1_alt_def Healthy_if assms)
      also have "... = (R1(true) \<parallel>\<^bsub>M\<lbrakk>false/$ok\<^sub><\<rbrakk>\<^esub> R1(true))"
        by (rel_auto, metis, metis)
      also have "... = (div\<^sub>m ;; M)\<lbrakk>false/$ok\<rbrakk>"
        by (rel_auto, metis, metis)
      also have "... = (R1(true))\<lbrakk>false/$ok\<rbrakk>"
        by (simp add: assms(8))
      also have "... = (R1(true))"
        by (rel_auto)
      finally show ?thesis
        by simp
    qed
    moreover have "(P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true,true/$ok,$wait\<rbrakk> = II\<lbrakk>true,true/$ok,$wait\<rbrakk>"
    proof -
      have "(P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>true,true/$ok,$wait\<rbrakk> = (P\<lbrakk>true,true/$ok,$wait\<rbrakk> \<parallel>\<^bsub>M\<^esub> Q\<lbrakk>true,true/$ok,$wait\<rbrakk>)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
        by (rel_auto)
      also have "... = (((II \<triangleleft> $ok \<triangleright> R1(true)) \<triangleleft> $wait \<triangleright> P)\<lbrakk>true,true/$ok,$wait\<rbrakk> \<parallel>\<^bsub>M\<^esub> ((II \<triangleleft> $ok \<triangleright> R1(true)) \<triangleleft> $wait \<triangleright> Q)\<lbrakk>true,true/$ok,$wait\<rbrakk>)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
        by (metis Healthy_def' R3c_cases assms(5) assms(6))
      also have "... = (II\<lbrakk>true,true/$ok,$wait\<rbrakk> \<parallel>\<^bsub>M\<^esub> II\<lbrakk>true,true/$ok,$wait\<rbrakk>)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
        by (subst_tac)
      also have "... = (wait\<^sub>m ;; M)\<lbrakk>true,true/$ok,$wait\<rbrakk>"
        by (rel_auto)
      also have "... = II\<lbrakk>true,true/$ok,$wait\<rbrakk>"
        by (simp add: assms usubst)
      finally show ?thesis .
    qed
    ultimately show ?thesis by simp
  qed
  also have "... = ((II \<triangleleft> $ok \<triangleright> R1(true)) \<triangleleft> $wait \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q))"
    by (rel_auto)
  also have "... = R3c(P \<parallel>\<^bsub>M\<^esub> Q)"
    by (simp add: R3c_cases)
  finally show ?thesis
    by (simp add: Healthy_def')
qed

lemma RD1_par_by_merge:
  assumes "P is R1" "Q is R1" "P is RD1" "Q is RD1" "M is R1m" "(div\<^sub>m ;; M) = R1(true)"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RD1"
proof -
  have "(P \<parallel>\<^bsub>M\<^esub> Q) = ((P \<parallel>\<^bsub>M\<^esub> Q) \<triangleleft> $ok \<triangleright> (P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk>)"
    by (metis cond_idem cond_var_subst_right vwb_lens_ok)
  also have "... = ((P \<parallel>\<^bsub>M\<^esub> Q) \<triangleleft> $ok \<triangleright> R1(true))"
  proof -
    have "(P \<parallel>\<^bsub>M\<^esub> Q)\<lbrakk>false/$ok\<rbrakk> = ((P \<triangleleft> $ok \<triangleright> R1(true)) \<parallel>\<^bsub>M\<^esub> (Q \<triangleleft> $ok \<triangleright> R1(true)))\<lbrakk>false/$ok\<rbrakk>"
      by (metis RD1_alt_def Healthy_if assms)
    also have "... = (R1(true) \<parallel>\<^bsub>M\<lbrakk>false/$ok\<^sub><\<rbrakk>\<^esub> R1(true))"
      by (rel_auto, metis, metis)
    also have "... = (div\<^sub>m ;; M)\<lbrakk>false/$ok\<rbrakk>"
      by (rel_auto, metis, metis)
    also have "... = (R1(true))\<lbrakk>false/$ok\<rbrakk>"
      by (simp add: assms(6))
    also have "... = (R1(true))"
      by (rel_auto)
    finally show ?thesis
      by simp
  qed
  finally show ?thesis
    by (metis RD1_alt_def Healthy_def R1_par_by_merge assms(5))
qed

lemma RD2_par_by_merge:
  assumes "M is RD2"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q) is RD2"
proof -
  have "(P \<parallel>\<^bsub>M\<^esub> Q) = ((P \<parallel>\<^sub>s Q) ;; M)"
    by (simp add: par_by_merge_def)
  also from assms have "... = ((P \<parallel>\<^sub>s Q) ;; (M ;; J))"
    by (simp add: Healthy_def' RD2_def H2_def)
  also from assms have "... = (((P \<parallel>\<^sub>s Q) ;; M) ;; J)"
    by (meson seqr_assoc)
  also from assms have "... = RD2(P \<parallel>\<^bsub>M\<^esub> Q)"
    by (simp add: RD2_def H2_def par_by_merge_def)
  finally show ?thesis
    by (simp add: Healthy_def')
qed
*)