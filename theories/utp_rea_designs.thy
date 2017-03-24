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
  (type) "('s,'t,'\<alpha>) rsp" <= (type) "('t, ('s, '\<alpha>) rsp_vars_scheme) rp_vars_ext des"
  (type) "('s,'t,'\<alpha>,'\<beta>) rel_rp" <= (type) "(('s,'t,'\<alpha>) rsp, (_,_,'\<beta>) rsp) rel"

notation rsp_vars_child_lens\<^sub>a ("\<Sigma>\<^sub>s")
notation rsp_vars_child_lens ("\<Sigma>\<^sub>S")

abbreviation lift_state_rel ("\<lceil>_\<rceil>\<^sub>S")
where "\<lceil>P\<rceil>\<^sub>S \<equiv> P \<oplus>\<^sub>p (st \<times>\<^sub>L st)"

abbreviation lift_state_pre ("\<lceil>_\<rceil>\<^sub>S\<^sub><")
where "\<lceil>p\<rceil>\<^sub>S\<^sub>< \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub><\<rceil>\<^sub>S"

syntax
  "_svid_st_alpha"  :: "svid" ("\<Sigma>\<^sub>S")

translations
  "_svid_st_alpha" => "CONST rsp_vars_child_lens"

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
    
definition skip_rea :: "('t::ordered_cancel_monoid_diff, '\<alpha>) hrel_rp" ("II\<^sub>r") where
skip_rea_def [urel_defs]: "II\<^sub>r = (II \<or> (\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>))"

definition skip_srea :: "('s, 't::ordered_cancel_monoid_diff, '\<alpha>) hrel_rsp" ("II\<^sub>R") where
skip_srea_def [urel_defs]: "II\<^sub>R = ((\<exists> $st \<bullet> II\<^sub>r) \<triangleleft> $wait \<triangleright> II\<^sub>r)"
  
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

lemma skip_srea_form: "II\<^sub>R = ((\<exists> $st \<bullet> II) \<triangleleft> $wait \<triangleright> II) \<triangleleft> $ok \<triangleright> R1(true)"
  by (rel_auto)
    
lemma R2c_skip_srea: "R2c(II\<^sub>R) = II\<^sub>R"
  apply (rel_auto) using minus_zero_eq by blast+

lemma R3h_form: "R3h(P) = II\<^sub>R \<triangleleft> $wait \<triangleright> P"
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

lemma R2c_st'_eq_st:
  "R2c($st\<acute> =\<^sub>u $st) = ($st\<acute> =\<^sub>u $st)"
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

lemma RHS_design_export_R2: "\<^bold>R\<^sub>s(P \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> R2(Q))"
  by (rel_auto)

lemma RHS_design_ok_wait: "\<^bold>R\<^sub>s(P\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> Q\<lbrakk>true,false/$ok,$wait\<rbrakk>) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
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

definition wpR (infix "wp\<^sub>R" 60)
where [upred_defs]: "P wp\<^sub>R Q = (\<not> (P ;; R1(\<not> Q)))"

lemma wpR_true [wp]: "P wp\<^sub>R true = true"
  by (rel_auto)

lemma wpR_seq [wp]:
  "Q is R1 \<Longrightarrow>(P ;; Q) wp\<^sub>R R = P wp\<^sub>R (Q wp\<^sub>R R)"
  by (simp add: wpR_def, metis (no_types, hide_lams) Healthy_def' R1_seqr seqr_assoc)

theorem RHS_tri_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$ok \<sharp> R" "$ok \<sharp> S\<^sub>1" "$ok \<sharp> S\<^sub>2"
          "$wait \<sharp> R" "$wait\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> S\<^sub>1" "$wait \<sharp> S\<^sub>2"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)) =
       \<^bold>R\<^sub>s((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> (R1(R2s Q\<^sub>2) ;; R1 (\<not> R2s R))) \<turnstile>
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

  from assms(7,8) have 3: "(R1 (R2s Q\<^sub>2) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R) = R1 (R2s Q\<^sub>2) ;; R1 (\<not> R2s R)"
    by (rel_auto, blast, meson)

  show ?thesis
    apply (subst RHS_design_composition)
    apply (simp_all add: assms)
    apply (simp add: assms wait'_cond_def unrest)
    apply (simp add: assms wait'_cond_def unrest)
    apply (simp add: 1 2 3)
    apply (simp add: R1_R2s_R2c RHS_design_lemma1)
    apply (metis R1_R2c_ex_st RHS_design_lemma1)
  done
qed

lemma R1_R2s_R1_true_lemma:
  "R1(R2s(R1 (\<not> R2s P) ;; R1 true)) = R1(R2s((\<not> P) ;; R1 true))"
  by (rel_auto)

lemma R2c_healthy_R2s: "P is R2c \<Longrightarrow> R1(R2s(P)) = R1(P)"
  by (simp add: Healthy_def R1_R2s_R2c)

theorem RHS_tri_design_composition_wp:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$ok \<sharp> R" "$ok \<sharp> S\<^sub>1" "$ok \<sharp> S\<^sub>2"
          "$wait \<sharp> R" "$wait\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> S\<^sub>1" "$wait \<sharp> S\<^sub>2"
          "P is R2c" "Q\<^sub>1 is R1" "Q\<^sub>1 is R2c" "Q\<^sub>2 is R1" "Q\<^sub>2 is R2c"
          "R is R2c" "S\<^sub>1 is R1" "S\<^sub>1 is R2c" "S\<^sub>2 is R1" "S\<^sub>2 is R2c"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) =
          \<^bold>R\<^sub>s((R1(\<not> P) wp\<^sub>R false \<and> Q\<^sub>2 wp\<^sub>R R) \<turnstile> (((\<exists> $st\<acute> \<bullet> Q\<^sub>1) \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2)))"
  apply (simp add: RHS_tri_design_composition assms wpR_def Healthy_if R2c_healthy_R2s disj_upred_def)
  apply (metis (no_types, hide_lams) Healthy_if R1_R2c_is_R2 R1_negate_R1 R2_def assms(11) assms(16))
done

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

lemma wait'_cond_peri_post_cmt:
  "peri\<^sub>R P \<diamondop> post\<^sub>R P = cmt\<^sub>R P"
  by (rel_auto, (metis (full_types))+)

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
  shows "(P ;; Q) = \<^bold>R\<^sub>s ((\<not> ((\<not> pre\<^sub>R P) ;; R1 true) \<and> \<not> (post\<^sub>R P ;; (\<not> pre\<^sub>R Q))) \<turnstile>
                       ((\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; post\<^sub>R Q))"
proof -
  have "(P ;; Q) = (\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) ;; \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q)))"
    by (simp add: SRD_reactive_tri_design assms(1) assms(2))
  also from assms have "... = \<^bold>R\<^sub>s ((\<not> ((\<not> pre\<^sub>R P) ;; R1 true) \<and> \<not> (post\<^sub>R P ;; (\<not> pre\<^sub>R Q))) \<turnstile>
        ((\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; post\<^sub>R Q))"
    by (simp add: RHS_tri_design_composition unrest R1_R2s_peri_SRD R1_R2s_post_SRD R1_neg_R2s_pre_RHS)
  finally show ?thesis .
qed

lemma SRD_composition_wp:
  assumes "P is SRD" "Q is SRD"
  shows "(P ;; Q) = \<^bold>R\<^sub>s (((\<not> pre\<^sub>R P) wp\<^sub>R false \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<turnstile>
                       ((\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; post\<^sub>R Q))"
  using assms
  by (simp add: SRD_composition wpR_def, metis (no_types, lifting) R1_idem R1_neg_R2s_pre_RHS)

lemma SRD_seqr_closure:
  assumes "P is SRD" "Q is SRD"
  shows "(P ;; Q) is SRD"
proof -
  have "(P ;; Q) = \<^bold>R\<^sub>s ((\<not> ((\<not> pre\<^sub>R P) ;; R1 true) \<and> \<not> (post\<^sub>R P ;; (\<not> pre\<^sub>R Q))) \<turnstile>
                       ((\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; post\<^sub>R Q))"
    by (simp add: SRD_composition assms(1) assms(2))
  also have "... is SRD"
    by (simp add: RHS_design_is_SRD add: unrest)
  finally show ?thesis .
qed

subsection {* Reactive design signature *}
  
lemma srdes_skip_def: "II\<^sub>R = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> \<lceil>II\<rceil>\<^sub>R))"
  apply (rel_auto) using minus_zero_eq by blast+

text {* This additional healthiness condition is analogous to H3 *}

definition [upred_defs]: "RD3(P) = P ;; II\<^sub>R"

definition assigns_rea :: "'s usubst \<Rightarrow> ('s, 't::ordered_cancel_monoid_diff, '\<alpha>) hrel_rsp" ("\<langle>_\<rangle>\<^sub>R") where
[upred_defs]: "assigns_rea \<sigma> = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S \<and> $\<Sigma>\<^sub>S\<acute> =\<^sub>u $\<Sigma>\<^sub>S))"

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

lemma assigns_rea_RHS_tri_des:
  "\<langle>\<sigma>\<rangle>\<^sub>R = \<^bold>R\<^sub>s(true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S \<and> $\<Sigma>\<^sub>S\<acute> =\<^sub>u $\<Sigma>\<^sub>S))"
  by (rel_auto)

lemma preR_Miracle: "pre\<^sub>R(Miracle) = true"
  by (simp add: Miracle_def, rel_auto)

lemma periR_Miracle: "peri\<^sub>R(Miracle) = false"
  by (simp add: Miracle_def, rel_auto)

lemma postR_Miracle: "post\<^sub>R(Miracle) = false"
  by (simp add: Miracle_def, rel_auto)

lemma preR_srdes_skip: "pre\<^sub>R(II\<^sub>R) = true"
  by (rel_auto)

lemma periR_srdes_skip: "peri\<^sub>R(II\<^sub>R) = false"
  by (rel_auto)

lemma postR_srdes_skip: "post\<^sub>R(II\<^sub>R) = ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R)"
  by (rel_auto) 

lemma preR_assigns_rea: "pre\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>R) = true"
  by (simp add: assigns_rea_def rea_pre_RHS_design usubst R2c_false R1_false)

lemma periR_assigns_rea: "peri\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>R) = false"
  by (simp add: assigns_rea_RHS_tri_des rea_peri_RHS_design usubst R2c_false R1_false)

lemma postR_assigns_rea: "post\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>R) = ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S \<and> $\<Sigma>\<^sub>S\<acute> =\<^sub>u $\<Sigma>\<^sub>S)"
  apply (rel_auto) using minus_zero_eq by blast

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

lemma SRD_left_unit:
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

lemma SRD_right_unit_lemma:
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

lemma SRD_right_unit_tri_lemma:
  assumes "P is SRD"
  shows "P ;; II\<^sub>R = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> post\<^sub>R P))"
proof -
  have "((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<triangleleft> $wait\<acute> \<triangleright> cmt\<^sub>R P) = (\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<diamondop> post\<^sub>R P"
    by (rel_auto)
  thus ?thesis
    by (simp add: SRD_right_unit_lemma assms)
qed

lemma SRD_srdes_skip: "II\<^sub>R is SRD"
  by (simp add: srdes_skip_def RHS_design_is_SRD unrest)

lemma srdes_skip_tri_design: "II\<^sub>R = \<^bold>R\<^sub>s(true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R))"
  by (simp add: srdes_skip_def, rel_auto)
  
lemma SRD_right_Chaos_lemma:
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

lemma SRD_right_Chaos_tri_lemma:
  assumes "P is SRD"
  shows "P ;; Chaos = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true \<and> \<not> (post\<^sub>R P ;; R1 true)) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<diamondop> false))"
proof -
  have "(\<not> (cmt\<^sub>R P \<and> \<not> $wait\<acute>) ;; R1 true) = (\<not> (post\<^sub>R P ;; R1 true\<^sub>h))"
    by (rel_auto, blast)
  moreover have "((\<exists> $st\<acute> \<bullet> cmt\<^sub>R P) \<and> $wait\<acute>) = (\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<diamondop> false"
    by (rel_auto)
  ultimately show ?thesis
    by (simp add: SRD_right_Chaos_lemma[OF assms])
qed
 
lemma SRD_right_Miracle_lemma:
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

lemma SRD_right_Miracle_tri_lemma:
  assumes "P is SRD"
  shows "P ;; Miracle = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile> (\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<diamondop> false)"
  by (simp add: SRD_right_Miracle_lemma[OF assms], rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  
text {* Properties about healthiness condition RD3 *}

lemma RD3_idem: "RD3(RD3(P)) = RD3(P)"
proof -
  have a: "II\<^sub>R ;; II\<^sub>R = II\<^sub>R"
    by (simp add: SRD_left_unit SRD_srdes_skip)
  show ?thesis
    by (simp add: RD3_def seqr_assoc[THEN sym] a)
qed

lemma RD3_Idempotent: "Idempotent RD3"
  by (simp add: Idempotent_def RD3_idem)

lemma RD3_continuous: "RD3(\<Sqinter>A) = (\<Sqinter>P\<in>A. RD3(P))"
  by (simp add: RD3_def seq_Sup_distr)

lemma RD3_Continuous: "Continuous RD3"
  by (simp add: Continuous_def RD3_continuous)

lemma RD3_right_subsumes_RD2: "RD2(RD3(P)) = RD3(P)"
proof -
  have a:"II\<^sub>R ;; J = II\<^sub>R"
    by (rel_auto)
  show ?thesis
    by (metis (no_types, hide_lams) H2_def RD2_def RD3_def a seqr_assoc)
qed

lemma RD3_left_subsumes_RD2: "RD3(RD2(P)) = RD3(P)"
proof -
  have a:"J ;; II\<^sub>R = II\<^sub>R"
    by (rel_simp, safe, blast+)
  show ?thesis
    by (metis (no_types, hide_lams) H2_def RD2_def RD3_def a seqr_assoc)
qed

lemma RD3_implies_RD2: "P is RD3 \<Longrightarrow> P is RD2"
  by (metis Healthy_def RD3_right_subsumes_RD2)

lemma RD3_intro_pre:
  assumes "P is SRD" "(\<not> pre\<^sub>R(P)) ;; R1(true) = (\<not> pre\<^sub>R(P))" "$st\<acute> \<sharp> peri\<^sub>R(P)"
  shows "P is RD3"
proof -
  have "RD3(P) = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile> (\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<diamondop> post\<^sub>R P)"
    by (simp add: RD3_def SRD_right_unit_tri_lemma assms)
  also have "... = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)"
    by (simp add: assms(3) ex_unrest)
  also have "... = \<^bold>R\<^sub>s ((\<not> (\<not> pre\<^sub>R P) ;; R1 true) \<turnstile> cmt\<^sub>R P)"
    by (simp add: wait'_cond_peri_post_cmt)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> cmt\<^sub>R P)"
    by (simp add: assms(2))
  finally show ?thesis
    by (metis Healthy_def SRD_as_reactive_design assms(1))
qed

lemma RHS_tri_design_right_unit_lemma:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok\<acute> \<sharp> R" "$wait\<acute> \<sharp> R"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) ;; II\<^sub>R = \<^bold>R\<^sub>s((\<not> (\<not> P) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> Q) \<diamondop> R))"
proof -
  have "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) ;; II\<^sub>R = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) ;; \<^bold>R\<^sub>s(true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R))"
    by (simp add: srdes_skip_tri_design)
  also have "... = \<^bold>R\<^sub>s ((\<not> R1 (\<not> R2s P) ;; R1 true) \<turnstile> (\<exists> $st\<acute> \<bullet> Q) \<diamondop> (R1 (R2s R) ;; R1 (R2s ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R))))"
    by (simp_all add: RHS_tri_design_composition assms unrest R2s_true R1_false R2s_false)
  also have "... = \<^bold>R\<^sub>s ((\<not> R1 (\<not> R2s P) ;; R1 true) \<turnstile> (\<exists> $st\<acute> \<bullet> Q) \<diamondop> R1 (R2s R))"
  proof -
    from assms(3,4) have "(R1 (R2s R) ;; R1 (R2s ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R))) = R1 (R2s R)"
      by (rel_auto, metis (no_types, lifting) minus_zero_eq, meson order_refl ordered_cancel_monoid_diff_class.diff_cancel)
    thus ?thesis
      by simp
  qed
  also have "... = \<^bold>R\<^sub>s((\<not> (\<not> P) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> Q) \<diamondop> R))"
    by (metis (no_types, lifting) R1_R2s_R1_true_lemma R1_R2s_R2c R2c_not RHS_design_R2c_pre RHS_design_neg_R1_pre RHS_design_post_R1 RHS_design_post_R2s)
  finally show ?thesis .
qed

lemma RHS_tri_design_RD3_intro:
  assumes
    "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok\<acute> \<sharp> R" "$st\<acute> \<sharp> Q"  "$wait\<acute> \<sharp> R"
    "(\<not> P) ;; R1(true) = (\<not> P)"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) is RD3"
  apply (simp add: Healthy_def RD3_def)
  apply (subst RHS_tri_design_right_unit_lemma)
  apply (simp_all add:assms ex_unrest)
done

text {* RD3 reactive designs are those whose assumption can be written as a conjunction of a
  precondition on (undashed) program variables, and a negated statement about the trace. The latter
  allows us to state that certain events must not occur in the trace -- which are effectively safety
  properties. *}

lemma R1_right_unit_lemma:
  "\<lbrakk> out\<alpha> \<sharp> b; out\<alpha> \<sharp> e \<rbrakk> \<Longrightarrow> (b \<or> $tr ^\<^sub>u e \<le>\<^sub>u $tr\<acute>) ;; R1(true) = (b \<or> $tr ^\<^sub>u e \<le>\<^sub>u $tr\<acute>)"
  by (rel_auto, blast, metis (no_types, lifting) dual_order.trans)

lemma RHS_tri_design_RD3_intro_form:
  assumes
    "out\<alpha> \<sharp> b" "out\<alpha> \<sharp> e" "$ok\<acute> \<sharp> Q" "$st\<acute> \<sharp> Q" "$ok\<acute> \<sharp> R" "$wait\<acute> \<sharp> R"
  shows "\<^bold>R\<^sub>s((b \<and> \<not> $tr ^\<^sub>u e \<le>\<^sub>u $tr\<acute>) \<turnstile> Q \<diamondop> R) is RD3"
  apply (rule RHS_tri_design_RD3_intro)
  apply (simp_all add: assms unrest)
  apply (simp add: R1_right_unit_lemma assms(1) assms(2) unrest_not)
done

definition NSRD :: "('s,'t::ordered_cancel_monoid_diff,'\<alpha>) hrel_rsp \<Rightarrow> ('s,'t,'\<alpha>) hrel_rsp"
where [upred_defs]: "NSRD = RD1 \<circ> RD3 \<circ> RHS"

lemma RD1_RD3_commute: "RD1(RD3(P)) = RD3(RD1(P))"
  by (rel_auto, blast+)

lemma NSRD_is_SRD: "P is NSRD \<Longrightarrow> P is SRD"
  by (simp add: Healthy_def NSRD_def SRD_def, metis Healthy_def RD1_RD3_commute RD2_RHS_commute RD3_def RD3_right_subsumes_RD2 SRD_def SRD_idem SRD_seqr_closure SRD_srdes_skip)

lemma NSRD_Idempotent: "Idempotent NSRD"
  by (clarsimp simp add: Idempotent_def NSRD_def, metis (no_types, hide_lams) Healthy_def RD1_RD3_commute RD3_def RD3_idem RD3_left_subsumes_RD2 SRD_def SRD_idem SRD_seqr_closure SRD_srdes_skip)

lemma NSRD_Continuous: "Continuous NSRD"
  by (simp add: Continuous_comp NSRD_def RD1_Continuous RD3_Continuous RHS_Continuous)

lemma NSRD_form:
  "NSRD(P) = \<^bold>R\<^sub>s((\<not> (\<not> pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> post\<^sub>R(P)))"
proof -
  have "NSRD(P) = RD3(SRD(P))"
    by (metis (no_types, lifting) NSRD_def RD1_RD3_commute RD3_left_subsumes_RD2 SRD_def comp_def)
  also have "... = RD3(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))"
    by (simp add: SRD_as_reactive_tri_design)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) ;; II\<^sub>R"
    by (simp add: RD3_def)
  also have "... = \<^bold>R\<^sub>s((\<not> (\<not> pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> post\<^sub>R(P)))"
    by (simp add: RHS_tri_design_right_unit_lemma unrest)
  finally show ?thesis .
qed

lemma NSRD_healthy_form:
  assumes "P is NSRD"
  shows "\<^bold>R\<^sub>s((\<not> (\<not> pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> post\<^sub>R(P))) = P"
  by (metis Healthy_def NSRD_form assms)

lemma NSRD_intro:
  assumes "P is SRD" "(\<not> pre\<^sub>R(P)) ;; R1(true) = (\<not> pre\<^sub>R(P))" "$st\<acute> \<sharp> peri\<^sub>R(P)"
  shows "P is NSRD"
proof -
  have "NSRD(P) = \<^bold>R\<^sub>s((\<not> (\<not> pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> post\<^sub>R(P)))"
    by (simp add: NSRD_form)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)"
    by (simp add: assms ex_unrest)
  also have "... = P"
    by (simp add: SRD_reactive_tri_design assms(1))
  finally show ?thesis
    using Healthy_def by blast
qed

lemma SRD_RD3_implies_NSRD:
  "\<lbrakk> P is SRD; P is RD3 \<rbrakk> \<Longrightarrow> P is NSRD"
  by (metis (no_types, lifting) Healthy_def NSRD_def RHS_idem SRD_healths(4) SRD_reactive_design comp_apply)

lemma NSRD_neg_pre_unit:
  assumes "P is NSRD"
  shows "(\<not> pre\<^sub>R(P)) ;; R1(true) = (\<not> pre\<^sub>R(P))"
proof -
  have "(\<not> pre\<^sub>R(P)) = (\<not> pre\<^sub>R(\<^bold>R\<^sub>s((\<not> (\<not> pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> post\<^sub>R(P)))))"
    by (simp add: NSRD_healthy_form assms)
  also have "... = R1 (R2c ((\<not> pre\<^sub>R P) ;; R1 true))"
    by (simp add: rea_pre_RHS_design usubst unrest)
  also have "... = ((\<not> pre\<^sub>R P) ;; R1 true)"
    by (metis R1_seqr R2_R2c_def R2_def R2c_seq R2s_true calculation)
  finally show ?thesis ..
qed

lemma NSRD_st'_unrest_peri:
  assumes "P is NSRD"
  shows "$st\<acute> \<sharp> peri\<^sub>R(P)"
proof -
  have "peri\<^sub>R(P) = peri\<^sub>R(\<^bold>R\<^sub>s((\<not> (\<not> pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> post\<^sub>R(P))))"
    by (simp add: NSRD_healthy_form assms)
  also have "... = R1 (R2c (\<not> (\<not> pre\<^sub>R P) ;; R1 true \<Rightarrow> (\<exists> $st\<acute> \<bullet> peri\<^sub>R P)))"
    by (simp add: rea_peri_RHS_design usubst unrest)
  also have "$st\<acute> \<sharp> ..."
    by (simp add: R1_def R2c_def unrest)
  finally show ?thesis .
qed

lemma NSRD_wait'_unrest_pre:
  assumes "P is NSRD"
  shows "$wait\<acute> \<sharp> pre\<^sub>R(P)"
proof -
  have "pre\<^sub>R(P) = pre\<^sub>R(\<^bold>R\<^sub>s((\<not> (\<not> pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> post\<^sub>R(P))))"
    by (simp add: NSRD_healthy_form assms)
  also have "... = (\<not> R1 (R2c ((\<not> pre\<^sub>R P) ;; R1 true)))"
    by (simp add: rea_pre_RHS_design usubst unrest)
  also have "$wait\<acute> \<sharp> ..."
    by (simp add: R1_def R2c_def unrest)
  finally show ?thesis .
qed

lemma NSRD_st'_unrest_pre:
  assumes "P is NSRD"
  shows "$st\<acute> \<sharp> pre\<^sub>R(P)"
proof -
  have "pre\<^sub>R(P) = pre\<^sub>R(\<^bold>R\<^sub>s((\<not> (\<not> pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> post\<^sub>R(P))))"
    by (simp add: NSRD_healthy_form assms)
  also have "... = (\<not> R1 (R2c ((\<not> pre\<^sub>R P) ;; R1 true)))"
    by (simp add: rea_pre_RHS_design usubst unrest)
  also have "$st\<acute> \<sharp> ..."
    by (simp add: R1_def R2c_def unrest)
  finally show ?thesis .
qed

lemma NSRD_iff:
  "P is NSRD \<longleftrightarrow> ((P is SRD) \<and> (\<not> pre\<^sub>R(P)) ;; R1(true) = (\<not> pre\<^sub>R(P)) \<and> ($st\<acute> \<sharp> peri\<^sub>R(P)))"
  by (meson NSRD_intro NSRD_is_SRD NSRD_neg_pre_unit NSRD_st'_unrest_peri)

lemma NSRD_composition_wp:
  assumes "P is NSRD" "Q is SRD"
  shows "P ;; Q =
         \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>R pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; post\<^sub>R Q))"
  by (simp add: SRD_composition_wp assms NSRD_is_SRD wpR_def NSRD_neg_pre_unit NSRD_st'_unrest_peri ex_unrest)

lemma RHS_tri_normal_design_composition:
  assumes
    "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$ok \<sharp> R" "$ok \<sharp> S\<^sub>1" "$ok \<sharp> S\<^sub>2"
    "$wait \<sharp> R" "$wait\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> S\<^sub>1" "$wait \<sharp> S\<^sub>2"
    "P is R2c" "Q\<^sub>1 is R1" "Q\<^sub>1 is R2c" "Q\<^sub>2 is R1" "Q\<^sub>2 is R2c"
    "R is R2c" "S\<^sub>1 is R1" "S\<^sub>1 is R2c" "S\<^sub>2 is R1" "S\<^sub>2 is R2c"
    "R1 (\<not> P) ;; R1(true) = (\<not> P)" "$st\<acute> \<sharp> Q\<^sub>1"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)
         = \<^bold>R\<^sub>s((P \<and> Q\<^sub>2 wp\<^sub>R R) \<turnstile> (Q\<^sub>1 \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
proof -
  have "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) =
        \<^bold>R\<^sub>s ((R1 (\<not> P) wp\<^sub>R false \<and> Q\<^sub>2 wp\<^sub>R R) \<turnstile> ((\<exists> $st\<acute> \<bullet> Q\<^sub>1) \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
    by (simp_all add: RHS_tri_design_composition_wp assms unrest)
  also have "... = \<^bold>R\<^sub>s((P \<and> Q\<^sub>2 wp\<^sub>R R) \<turnstile> (Q\<^sub>1 \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
    by (simp add: assms wpR_def ex_unrest)
  finally show ?thesis .
qed

lemma NSRD_right_Miracle_tri_lemma:
  assumes "P is NSRD"
  shows "P ;; Miracle = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> false)"
  by (metis (no_types, lifting) Healthy_if NSRD_iff RD3_def RHS_tri_design_RD3_intro 
            RHS_tri_design_right_unit_lemma SRD_right_Miracle_tri_lemma assms ok'_peri_unrest 
            ok'_pre_unrest periR_srdes_skip postR_Miracle wait'_post_unrest)

lemma Miracle_right_zero_law:
  assumes "$ok\<acute> \<sharp> P"
  shows "\<^bold>R\<^sub>s(true \<turnstile> false \<diamondop> P) ;; Miracle = Miracle"
proof -
  have "\<^bold>R\<^sub>s(true \<turnstile> false \<diamondop> P) is SRD"
    by (simp add: RHS_tri_design_is_SRD assms unrest_false unrest_true)
  hence "\<^bold>R\<^sub>s(true \<turnstile> false \<diamondop> P) is NSRD"
    by (rule NSRD_intro, (rel_auto)+)
  thus ?thesis
    by (simp add: NSRD_right_Miracle_tri_lemma rea_pre_RHS_design rea_peri_RHS_design usubst R2c_false R1_false)
       (simp add: Miracle_def wait'_cond_idem)
qed

lemma NSRD_right_Chaos_tri_lemma:
  assumes "P is NSRD"
  shows "P ;; Chaos = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> \<not> (post\<^sub>R P ;; R1 true)) \<turnstile> peri\<^sub>R P \<diamondop> false)"
  by (simp add: SRD_right_Chaos_tri_lemma[OF NSRD_is_SRD[OF assms]] 
                NSRD_neg_pre_unit NSRD_st'_unrest_peri assms ex_unrest)
  
lemma assigns_rea_id: "\<langle>id\<rangle>\<^sub>R = II\<^sub>R"
  by (simp add: srdes_skip_def, rel_auto)
    
lemma SRD_assigns_rea [closure]: "\<langle>\<sigma>\<rangle>\<^sub>R is SRD"
  by (simp add: assigns_rea_def RHS_design_is_SRD unrest)

lemma RD3_assigns_rea: "\<langle>\<sigma>\<rangle>\<^sub>R is RD3"
  by (rule RD3_intro_pre, simp_all add: SRD_assigns_rea preR_assigns_rea periR_assigns_rea unrest)

lemma NSRD_assigns_rea [closure]: "\<langle>\<sigma>\<rangle>\<^sub>R is NSRD"
  by (simp add: NSRD_iff SRD_assigns_rea periR_assigns_rea preR_assigns_rea unrest_false)

lemma assigns_rea_comp: "\<langle>\<sigma>\<rangle>\<^sub>R ;; \<langle>\<rho>\<rangle>\<^sub>R = \<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>R"
proof -
  have a: "(($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S \<and> $\<Sigma>\<^sub>S\<acute> =\<^sub>u $\<Sigma>\<^sub>S) ;; ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<rho>\<rangle>\<^sub>a\<rceil>\<^sub>S \<and> $\<Sigma>\<^sub>S\<acute> =\<^sub>u $\<Sigma>\<^sub>S)) =
        ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S \<and> $\<Sigma>\<^sub>S\<acute> =\<^sub>u $\<Sigma>\<^sub>S)"
    by (rel_auto)
  have "\<langle>\<sigma>\<rangle>\<^sub>R ;; \<langle>\<rho>\<rangle>\<^sub>R = \<^bold>R\<^sub>s (true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S \<and> $\<Sigma>\<^sub>S\<acute> =\<^sub>u $\<Sigma>\<^sub>S))"
    by (simp add: NSRD_composition_wp closure preR_assigns_rea periR_assigns_rea postR_assigns_rea wp a)
  also have "... = \<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>R"
    by (simp add: assigns_rea_RHS_tri_des)
  finally show ?thesis .
qed

text {* Stateful reactive designs are left unital *}

overloading
  srdes_unit == "utp_unit :: (SRDES, ('s,'t::ordered_cancel_monoid_diff,'\<alpha>) rsp) uthy \<Rightarrow> ('s,'t,'\<alpha>) hrel_rsp"
begin
  definition srdes_unit :: "(SRDES, ('s,'t::ordered_cancel_monoid_diff,'\<alpha>) rsp) uthy \<Rightarrow> ('s,'t,'\<alpha>) hrel_rsp" where
  "srdes_unit T = II\<^sub>R"
end

interpretation srdes_left_unital: utp_theory_left_unital SRDES
  by (unfold_locales, simp_all add: srdes_hcond_def srdes_unit_def SRD_seqr_closure SRD_srdes_skip SRD_left_unit)

text {* Stateful reactive designs and assignment *}

overloading
  srdes_pvar == "pvar :: (SRDES, ('s,'t::ordered_cancel_monoid_diff,'\<alpha>) rsp) uthy \<Rightarrow> 's \<Longrightarrow> ('s,'t,'\<alpha>) rsp"
  srdes_pvar_assigns == "pvar_assigns :: (SRDES, ('s,'t::ordered_cancel_monoid_diff,'\<alpha>) rsp) uthy \<Rightarrow> 's usubst \<Rightarrow> ('s,'t,'\<alpha>) hrel_rsp"
begin
  definition srdes_pvar ::
    "(SRDES, ('s,'t::ordered_cancel_monoid_diff,'\<alpha>) rsp) uthy \<Rightarrow> 's \<Longrightarrow> ('s,'t,'\<alpha>) rsp" where
  [upred_defs]: "srdes_pvar T = st"
  definition srdes_pvar_assigns ::
    "(SRDES, ('s,'t::ordered_cancel_monoid_diff,'\<alpha>) rsp) uthy \<Rightarrow> 's usubst \<Rightarrow> ('s,'t,'\<alpha>) hrel_rsp" where
  [upred_defs]: "srdes_pvar_assigns T \<sigma> = \<langle>\<sigma>\<rangle>\<^sub>R"
end

interpretation srdes_local_var: utp_local_var "UTHY(SRDES, ('s,'t::ordered_cancel_monoid_diff,'\<alpha>) rsp)" "TYPE('s)"
proof -
  interpret vw: vwb_lens "pvar SRDES :: 's \<Longrightarrow> ('s,'t,'\<alpha>) rsp"
    by (simp add: srdes_pvar_def)
  show "utp_local_var TYPE('s) UTHY(SRDES, ('s,'t,'\<alpha>) rsp)"
  proof
    show "\<And>\<sigma>::'s \<Rightarrow> 's. \<^bold>\<langle>\<sigma>\<^bold>\<rangle>\<^bsub>UTHY(SRDES, ('s,'t,'\<alpha>) rsp)\<^esub> is \<H>\<^bsub>SRDES\<^esub>"
      by (simp add: srdes_pvar_assigns_def srdes_hcond_def SRD_assigns_rea)
    show "\<And>(\<sigma>::'s \<Rightarrow> 's) \<rho>. \<^bold>\<langle>\<sigma>\<^bold>\<rangle>\<^bsub>UTHY(SRDES, ('s,'t,'\<alpha>) rsp)\<^esub> ;; \<^bold>\<langle>\<rho>\<^bold>\<rangle>\<^bsub>SRDES\<^esub> = \<^bold>\<langle>\<rho> \<circ> \<sigma>\<^bold>\<rangle>\<^bsub>SRDES\<^esub>"
      by (simp add: srdes_pvar_assigns_def assigns_rea_comp)
    show "\<^bold>\<langle>id::'s \<Rightarrow> 's\<^bold>\<rangle>\<^bsub>UTHY(SRDES, ('s,'t,'\<alpha>) rsp)\<^esub> = \<I>\<I>\<^bsub>SRDES\<^esub>"
      by (simp add: srdes_pvar_assigns_def srdes_unit_def assigns_rea_id)
  qed
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
    "$ok\<acute> \<sharp> P\<^sub>1" "$ok\<acute> \<sharp> P\<^sub>2"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1) \<parallel>\<^sub>R \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2) = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<and> Q\<^sub>2))"
proof -
  have "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1) \<parallel>\<^sub>R \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2) =
        \<^bold>R\<^sub>s(P\<^sub>1\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> Q\<^sub>1\<lbrakk>true,false/$ok,$wait\<rbrakk>) \<parallel>\<^sub>R \<^bold>R\<^sub>s(P\<^sub>2\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> Q\<^sub>2\<lbrakk>true,false/$ok,$wait\<rbrakk>)"
    by (simp add: RHS_design_ok_wait)

  also from assms
  have "... =
        \<^bold>R\<^sub>s((\<not> R1 (R2c (\<not> P\<^sub>1)) \<and> \<not> R1 (R2c (\<not> P\<^sub>2)))\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile>
           (R1 (R2c (P\<^sub>1 \<Rightarrow> Q\<^sub>1)) \<and> R1 (R2c (P\<^sub>2 \<Rightarrow> Q\<^sub>2)))\<lbrakk>true,false/$ok,$wait\<rbrakk>)"
      apply (simp add: rea_design_par_def rea_pre_RHS_design rea_cmt_RHS_design usubst unrest assms)
      apply (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp)
      using assms apply (rel_auto)
  done
  also have "... =
        \<^bold>R\<^sub>s((\<not> R2c (\<not> P\<^sub>1) \<and> \<not> R2c (\<not> P\<^sub>2)) \<turnstile>
           (R1 (R2s (P\<^sub>1 \<Rightarrow> Q\<^sub>1)) \<and> R1 (R2s (P\<^sub>2 \<Rightarrow> Q\<^sub>2))))"
    by (metis (no_types, lifting) R1_R2s_R2c R1_disj RHS_design_neg_R1_pre RHS_design_ok_wait utp_pred.compl_sup)
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
  assumes "$ok\<acute> \<sharp> P\<^sub>1" "$ok\<acute> \<sharp> P\<^sub>2"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1 \<diamondop> R\<^sub>1) \<parallel>\<^sub>R \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2 \<diamondop> R\<^sub>2) = \<^bold>R\<^sub>s((P\<^sub>1 \<and> P\<^sub>2) \<turnstile> (Q\<^sub>1 \<and> Q\<^sub>2) \<diamondop> (R\<^sub>1 \<and> R\<^sub>2))"
  by (simp add: RHS_design_par assms unrest wait'_cond_conj_exchange)
end