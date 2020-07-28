section \<open> Normal Reactive Designs \<close>

theory utp_rdes_normal
  imports 
    utp_rdes_triples
    "UTP-KAT.utp_kleene"
begin

text \<open> These additional healthiness conditions are analogous to H3 \<close>

definition RD3 where
[upred_defs]: "RD3(P) = P ;; II\<^sub>R"

definition RD3c where
[upred_defs]: "RD3c(P) = P ;; II\<^sub>C"

lemma RD3_idem: "RD3(RD3(P)) = RD3(P)"
proof -
  have a: "II\<^sub>R ;; II\<^sub>R = II\<^sub>R"
    by (simp add: SRD_left_unit SRD_srdes_skip)
  show ?thesis
    by (simp add: RD3_def seqr_assoc a)
qed

lemma RD3_Idempotent [closure]: "Idempotent RD3"
  by (simp add: Idempotent_def RD3_idem)

lemma RD3_continuous: "RD3(\<Sqinter>A) = (\<Sqinter>P\<in>A. RD3(P))"
  by (simp add: RD3_def seq_Sup_distr)

lemma RD3_Continuous [closure]: "Continuous RD3"
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

lemma RD3c_left_subsumes_RD2: "RD3c(RD2(P)) = RD3c(P)"
proof -
  have a:"J ;; II\<^sub>C = II\<^sub>C"
    by (rel_auto)
  show ?thesis
    by (simp add: H2_def RD2_def RD3c_def a seqr_assoc)
qed

lemma RD3_implies_RD2: "P is RD3 \<Longrightarrow> P is RD2"
  by (metis Healthy_def RD3_right_subsumes_RD2)

lemma RD3_intro_pre:
  assumes "P is SRD" "(\<not>\<^sub>r pre\<^sub>R(P)) ;; true\<^sub>r = (\<not>\<^sub>r pre\<^sub>R(P))" "$st\<acute> \<sharp> peri\<^sub>R(P)"
  shows "P is RD3"
proof -
  have "RD3(P) = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false \<turnstile> (\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<diamondop> post\<^sub>R P)"
    by (simp add: RD3_def SRD_right_unit_tri_lemma assms)
  also have "... = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)"
    by (simp add: assms(3) ex_unrest)
  also have "... = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false \<turnstile> cmt\<^sub>R P)"
    by (simp add: wait'_cond_peri_post_cmt)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> cmt\<^sub>R P)"
    by (simp add: assms(2) rpred wp_rea_def R1_preR)
  finally show ?thesis
    by (metis Healthy_def SRD_as_reactive_design assms(1))
qed

lemma RHS_tri_design_RD3_intro:
  assumes
    "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok\<acute> \<sharp> R" "$st\<acute> \<sharp> Q"  "$wait\<acute> \<sharp> R"
    "P is R1" "(\<not>\<^sub>r P) ;; true\<^sub>r = (\<not>\<^sub>r P)"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) is RD3"
  apply (simp add: Healthy_def RD3_def)
  apply (subst RHS_tri_design_right_unit_lemma)
  apply (simp_all add:assms ex_unrest rpred)
done

text \<open> RD3 reactive designs are those whose assumption can be written as a conjunction of a
  precondition on (undashed) program variables, and a negated statement about the trace. The latter
  allows us to state that certain events must not occur in the trace -- which are effectively safety
  properties. \<close>

lemma R1_right_unit_lemma:
  "\<lbrakk> out\<alpha> \<sharp> b; out\<alpha> \<sharp> e \<rbrakk> \<Longrightarrow> (\<not>\<^sub>r b \<or> $tr ^\<^sub>u e \<le>\<^sub>u $tr\<acute>) ;; R1(true) = (\<not>\<^sub>r b\<or> $tr ^\<^sub>u e \<le>\<^sub>u $tr\<acute>)"
  by (rel_auto, blast, metis (no_types, lifting) dual_order.trans)

lemma RHS_tri_design_RD3_intro_form:
  assumes
    "out\<alpha> \<sharp> b" "out\<alpha> \<sharp> e" "$ok\<acute> \<sharp> Q" "$st\<acute> \<sharp> Q" "$ok\<acute> \<sharp> R" "$wait\<acute> \<sharp> R"
  shows "\<^bold>R\<^sub>s((b \<and> \<not>\<^sub>r $tr ^\<^sub>u e \<le>\<^sub>u $tr\<acute>) \<turnstile> Q \<diamondop> R) is RD3"
  apply (rule RHS_tri_design_RD3_intro)
        apply (simp_all add: assms unrest closure rpred)
  apply (subst R1_right_unit_lemma)
    apply (simp_all add: assms unrest)
  done

definition NSRD :: "('s,'t::trace,'\<alpha>) hrel_rsp \<Rightarrow> ('s,'t,'\<alpha>) hrel_rsp"
where [upred_defs]: "NSRD = RD1 \<circ> RD3 \<circ> RHS"

definition NRD :: "('t::trace,'\<alpha>) hrel_rp \<Rightarrow> ('t,'\<alpha>) hrel_rp"
where [upred_defs]: "NRD = RD1 \<circ> RD3c \<circ> RH"

lemma RD1_RD3_commute: "RD1(RD3(P)) = RD3(RD1(P))"
  by (rel_auto, blast+)

lemma RD1_RD3c_commute: "RD1(RD3c(P)) = RD3c(RD1(P))"
  by (rel_auto)

lemma NSRD_is_SRD [closure]: "P is NSRD \<Longrightarrow> P is SRD"
  by (simp add: Healthy_def NSRD_def SRD_def, metis Healthy_def RD1_RD3_commute RD2_RHS_commute RD3_def RD3_right_subsumes_RD2 SRD_def SRD_idem SRD_seqr_closure SRD_srdes_skip)

lemma NSRD_elim [RD_elim]: 
  "\<lbrakk> P is NSRD; Q(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))) \<rbrakk> \<Longrightarrow> Q(P)"
  by (simp add: RD_elim closure)

lemma NSRD_idem: "NSRD(NSRD(P)) = NSRD(P)"
  by (metis (no_types, hide_lams) Healthy_def NSRD_def RD1_RD2_commute RD1_RD3_commute RD1_RHS_commute RD1_idem RD2_RHS_commute RD2_idem RD3_def RD3_idem RD3_left_subsumes_RD2 RHS_idem SRD_def comp_apply fun.map_comp srdes_left_unital.Healthy_Sequence srdes_left_unital.Healthy_Unit)
  
lemma NSRD_Idempotent [closure]: "Idempotent NSRD"
  by (simp add: Idempotent_def NSRD_idem)

lemma NSRD_Continuous [closure]: "Continuous NSRD"
  by (simp add: Continuous_comp NSRD_def RD1_Continuous RD3_Continuous RHS_Continuous)

lemma NRD_form:
  "NRD(P) = \<^bold>R((\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R(P)) ;; R1 true) \<turnstile> (peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))"
proof -
  have "NRD(P) = RD3c(RD(P))"
    by (metis NRD_def RD1_RD3c_commute RD3c_left_subsumes_RD2 RD_alt_def comp_eq_dest_lhs)
  also have "... = RD3c(\<^bold>R(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))"
    by (simp add: RD_as_reactive_tri_design)
  also have "... = \<^bold>R(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) ;; II\<^sub>C"
    by (simp add: RD3c_def)
  also have "... = \<^bold>R((\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R(P)) ;; R1 true) \<turnstile> (peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))"
    by (simp add: RH_tri_design_right_unit_lemma unrest)
  finally show ?thesis .
qed

lemma NSRD_form:
  "NSRD(P) = \<^bold>R\<^sub>s((\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> post\<^sub>R(P)))"
proof -
  have "NSRD(P) = RD3(SRD(P))"
    by (metis (no_types, lifting) NSRD_def RD1_RD3_commute RD3_left_subsumes_RD2 SRD_def comp_def)
  also have "... = RD3(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))"
    by (simp add: SRD_as_reactive_tri_design)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) ;; II\<^sub>R"
    by (simp add: RD3_def)
  also have "... = \<^bold>R\<^sub>s((\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> post\<^sub>R(P)))"
    by (simp add: RHS_tri_design_right_unit_lemma unrest)
  finally show ?thesis .
qed
      
lemma NSRD_healthy_form:
  assumes "P is NSRD"
  shows "\<^bold>R\<^sub>s((\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> post\<^sub>R(P))) = P"
  by (metis Healthy_def NSRD_form assms)

lemma NSRD_Sup_closure [closure]:
  assumes "A \<subseteq> \<lbrakk>NSRD\<rbrakk>\<^sub>H" "A \<noteq> {}"
  shows "\<Sqinter> A is NSRD"
proof -
  have "NSRD (\<Sqinter> A) = (\<Sqinter> (NSRD `A))"
    by (simp add: ContinuousD NSRD_Continuous assms(2))
  also have "... = (\<Sqinter> A)"
    by (simp only: Healthy_carrier_image assms)
  finally show ?thesis by (simp add: Healthy_def)
qed

lemma intChoice_NSRD_closed [closure]:
  assumes "P is NSRD" "Q is NSRD"
  shows "P \<sqinter> Q is NSRD"
  using NSRD_Sup_closure[of "{P, Q}"] by (simp add: assms)

lemma NRSD_SUP_closure [closure]:
  "\<lbrakk> \<And> i. i \<in> A \<Longrightarrow> P(i) is NSRD; A \<noteq> {} \<rbrakk> \<Longrightarrow> (\<Sqinter>i\<in>A. P(i)) is NSRD"
  by (rule NSRD_Sup_closure, auto)
    
lemma NSRD_neg_pre_unit:
  assumes "P is NSRD"
  shows "(\<not>\<^sub>r pre\<^sub>R(P)) ;; true\<^sub>r = (\<not>\<^sub>r pre\<^sub>R(P))"
proof -
  have "(\<not>\<^sub>r pre\<^sub>R(P)) = (\<not>\<^sub>r pre\<^sub>R(\<^bold>R\<^sub>s((\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> post\<^sub>R(P)))))"
    by (simp add: NSRD_healthy_form assms)
  also have "... = R1 (R2c ((\<not>\<^sub>r pre\<^sub>R P) ;; R1 true))"
    by (simp add: rea_pre_RHS_design R1_negate_R1 R1_idem R1_rea_not' R2c_rea_not usubst rpred unrest closure)
  also have "... = (\<not>\<^sub>r pre\<^sub>R P) ;; R1 true"
    by (simp add: R1_R2c_seqr_distribute closure assms)
  finally show ?thesis
    by (simp add: rea_not_def)
qed

lemma NSRD_neg_pre_left_zero:
  assumes "P is NSRD" "Q is R1" "Q is RD1"
  shows "(\<not>\<^sub>r pre\<^sub>R(P)) ;; Q = (\<not>\<^sub>r pre\<^sub>R(P))"
  by (metis (no_types, hide_lams) NSRD_neg_pre_unit RD1_left_zero assms(1) assms(2) assms(3) seqr_assoc)

lemma NSRD_st'_unrest_peri [unrest]:
  assumes "P is NSRD"
  shows "$st\<acute> \<sharp> peri\<^sub>R(P)"
proof -
  have "peri\<^sub>R(P) = peri\<^sub>R(\<^bold>R\<^sub>s((\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> post\<^sub>R(P))))"
    by (simp add: NSRD_healthy_form assms)
  also have "... = R1 (R2c (\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R P) ;; R1 true \<Rightarrow>\<^sub>r (\<exists> $st\<acute> \<bullet> peri\<^sub>R P)))"
    by (simp add: rea_peri_RHS_design usubst unrest)
  also have "$st\<acute> \<sharp> ..."
    by (simp add: R1_def R2c_def unrest)
  finally show ?thesis .
qed

lemma NSRD_wait'_unrest_pre [unrest]:
  assumes "P is NSRD"
  shows "$wait\<acute> \<sharp> pre\<^sub>R(P)"
proof -
  have "pre\<^sub>R(P) = pre\<^sub>R(\<^bold>R\<^sub>s((\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> post\<^sub>R(P))))"
    by (simp add: NSRD_healthy_form assms)
  also have "... = (R1 (R2c (\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R P) ;; R1 true)))"
    by (simp add: rea_pre_RHS_design usubst unrest)
  also have "$wait\<acute> \<sharp> ..."
    by (simp add: R1_def R2c_def unrest)
  finally show ?thesis .
qed

lemma NSRD_st'_unrest_pre [unrest]:
  assumes "P is NSRD"
  shows "$st\<acute> \<sharp> pre\<^sub>R(P)"
proof -
  have "pre\<^sub>R(P) = pre\<^sub>R(\<^bold>R\<^sub>s((\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> post\<^sub>R(P))))"
    by (simp add: NSRD_healthy_form assms)
  also have "... = R1 (R2c (\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R P) ;; R1 true))"
    by (simp add: rea_pre_RHS_design usubst unrest)
  also have "$st\<acute> \<sharp> ..."
    by (simp add: R1_def R2c_def unrest)
  finally show ?thesis .
qed

lemma NSRD_peri_under_pre [rpred]:
  "P is NSRD \<Longrightarrow> (pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) = peri\<^sub>R P"
  by (simp add: SRD_peri_under_pre unrest closure)

lemma NSRD_post_under_pre [rpred]:
  "P is NSRD \<Longrightarrow> (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) = post\<^sub>R P"
  by (simp add: SRD_post_under_pre unrest closure)

lemma NSRD_peri_seq_under_pre:
  assumes "P is NSRD" "Q is NSRD"
  shows "(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q) = (peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q)"
  by (metis NSRD_peri_under_pre assms(1) rea_impl_def utp_pred_laws.disj_assoc)

lemma NSRD_postR_seq_periR_impl:
  assumes "P is NSRD" "Q is NSRD"
  shows "(post\<^sub>R P wp\<^sub>r pre\<^sub>R Q \<Rightarrow>\<^sub>r (post\<^sub>R P ;; peri\<^sub>R Q)) = (post\<^sub>R P ;; peri\<^sub>R Q)"
  by (metis NSRD_is_SRD NSRD_peri_under_pre assms postR_RR wpR_impl_post_spec)
  
lemma NSRD_postR_seq_postR_impl:
  assumes "P is NSRD" "Q is NSRD"
  shows "(post\<^sub>R P wp\<^sub>r pre\<^sub>R Q \<Rightarrow>\<^sub>r (post\<^sub>R P ;; post\<^sub>R Q)) = (post\<^sub>R P ;; post\<^sub>R Q)"
  by (metis NSRD_is_SRD NSRD_post_under_pre assms postR_RR wpR_impl_post_spec)

lemma NSRD_peri_under_assms:
  assumes "P is NSRD" "Q is NSRD"
  shows "(pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q) = (peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q)"
  by (metis (no_types, lifting) NSRD_peri_seq_under_pre assms NSRD_postR_seq_periR_impl rea_impl_conj rea_impl_disj)

lemma NSRD_peri_under_assms':
  assumes "P is NSRD" "Q is NSRD"
  shows "(post\<^sub>R P wp\<^sub>r pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q) = (peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q)"
  by (simp add: NSRD_postR_seq_periR_impl assms rea_impl_disj)

lemma NSRD_post_under_assms:
  assumes "P is NSRD" "Q is NSRD"
  shows "(pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R Q \<Rightarrow>\<^sub>r post\<^sub>R P ;; post\<^sub>R Q) = (pre\<^sub>R P \<Rightarrow>\<^sub>r (post\<^sub>R P ;; post\<^sub>R Q))"
  by (metis NSRD_postR_seq_postR_impl assms(1) assms(2) rea_impl_conj)

lemma NSRD_alt_def: "NSRD(P) = RD3(SRD(P))"
  by (metis NSRD_def RD1_RD3_commute RD3_left_subsumes_RD2 SRD_def comp_eq_dest_lhs)

lemma preR_RR [closure]: "P is NSRD \<Longrightarrow> pre\<^sub>R(P) is RR"
  by (rule RR_intro, simp_all add: closure unrest)

lemma NSRD_neg_pre_RC [closure]:
  assumes "P is NSRD"
  shows "pre\<^sub>R(P) is RC"
  by (rule RC_intro, simp_all add: closure assms NSRD_neg_pre_unit rpred)

lemma NSRD_intro:
  assumes "P is SRD" "(\<not>\<^sub>r pre\<^sub>R(P)) ;; true\<^sub>r = (\<not>\<^sub>r pre\<^sub>R(P))" "$st\<acute> \<sharp> peri\<^sub>R(P)"
  shows "P is NSRD"
proof -
  have "NSRD(P) = \<^bold>R\<^sub>s((\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R(P)) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> peri\<^sub>R(P)) \<diamondop> post\<^sub>R(P)))"
    by (simp add: NSRD_form)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)"
    by (simp add: assms ex_unrest rpred closure)
  also have "... = P"
    by (simp add: SRD_reactive_tri_design assms(1))
  finally show ?thesis
    using Healthy_def by blast
qed

lemma NSRD_intro':
  assumes "P is R2" "P is R3h" "P is RD1" "P is RD3"
  shows "P is NSRD"
  by (metis (no_types, hide_lams) Healthy_def NSRD_def R1_R2c_is_R2 RHS_def assms comp_apply)

lemma NSRD_RC_intro:
  assumes "P is SRD" "pre\<^sub>R(P) is RC" "$st\<acute> \<sharp> peri\<^sub>R(P)"
  shows "P is NSRD"
  by (metis Healthy_def NSRD_form SRD_reactive_tri_design assms(1) assms(2) assms(3) 
      ex_unrest rea_not_false  wp_rea_RC_false wp_rea_def)
    
lemma NSRD_rdes_intro [closure]:
  assumes "P is RC" "Q is RR" "R is RR" "$st\<acute> \<sharp> Q"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) is NSRD"
  by (rule NSRD_RC_intro, simp_all add: rdes closure assms unrest)
    
lemma SRD_RD3_implies_NSRD:
  "\<lbrakk> P is SRD; P is RD3 \<rbrakk> \<Longrightarrow> P is NSRD"
  by (metis (no_types, lifting) Healthy_def NSRD_def RHS_idem SRD_healths(4) SRD_reactive_design comp_apply)


lemma NSRD_iff:
  "P is NSRD \<longleftrightarrow> ((P is SRD) \<and> (\<not>\<^sub>r pre\<^sub>R(P)) ;; R1(true) = (\<not>\<^sub>r pre\<^sub>R(P)) \<and> ($st\<acute> \<sharp> peri\<^sub>R(P)))"
  by (meson NSRD_intro NSRD_is_SRD NSRD_neg_pre_unit NSRD_st'_unrest_peri)
    
lemma NSRD_is_RD3 [closure]:
  assumes "P is NSRD"
  shows "P is RD3"
  by (simp add: NSRD_is_SRD NSRD_neg_pre_unit NSRD_st'_unrest_peri RD3_intro_pre assms)    

lemma NSRD_refine_elim:
  assumes
    "P \<sqsubseteq> Q" "P is NSRD" "Q is NSRD"
    "\<lbrakk> `pre\<^sub>R(P) \<Rightarrow> pre\<^sub>R(Q)`; `pre\<^sub>R(P) \<and> peri\<^sub>R(Q) \<Rightarrow> peri\<^sub>R(P)`; `pre\<^sub>R(P) \<and> post\<^sub>R(Q) \<Rightarrow> post\<^sub>R(P)` \<rbrakk> \<Longrightarrow> R"
  shows "R"
proof -
  have "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) \<sqsubseteq> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q))"
    by (simp add: NSRD_is_SRD SRD_reactive_tri_design assms(1) assms(2) assms(3))
  hence 1:"`pre\<^sub>R P \<Rightarrow> pre\<^sub>R Q`" and 2:"`pre\<^sub>R P \<and> peri\<^sub>R Q \<Rightarrow> peri\<^sub>R P`" and 3:"`pre\<^sub>R P \<and> post\<^sub>R Q \<Rightarrow> post\<^sub>R P`"
    by (simp_all add: RHS_tri_design_refine assms closure)
  with assms(4) show ?thesis
    by simp
qed
  
lemma NSRD_right_unit: "P is NSRD \<Longrightarrow> P ;; II\<^sub>R = P"
  by (metis Healthy_if NSRD_is_RD3 RD3_def)
  
lemma NSRD_composition_wp:
  assumes "P is NSRD" "Q is SRD"
  shows "P ;; Q =
         \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; post\<^sub>R Q))"
  by (simp add: SRD_composition_wp assms NSRD_is_SRD wp_rea_def NSRD_neg_pre_unit NSRD_st'_unrest_peri R1_negate_R1 R1_preR ex_unrest rpred)

lemma preR_NSRD_seq_lemma:
  assumes "P is NSRD" "Q is SRD"
  shows "R1 (R2c (post\<^sub>R P ;; (\<not>\<^sub>r pre\<^sub>R Q))) = post\<^sub>R P ;; (\<not>\<^sub>r pre\<^sub>R Q)"
proof -
  have "post\<^sub>R P ;; (\<not>\<^sub>r pre\<^sub>R Q) = R1(R2c(post\<^sub>R P)) ;; R1(R2c(\<not>\<^sub>r pre\<^sub>R Q))"
    by (simp add: NSRD_is_SRD R1_R2c_post_RHS R1_rea_not R2c_preR R2c_rea_not assms(1) assms(2))
  also have "... = R1 (R2c (post\<^sub>R P ;; (\<not>\<^sub>r pre\<^sub>R Q)))"
    by (simp add: R1_seqr R2c_R1_seq calculation)
  finally show ?thesis ..
qed
  
lemma preR_NSRD_seq [rdes]:
  assumes "P is NSRD" "Q is SRD"
  shows "pre\<^sub>R(P ;; Q) = (pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R Q)"
  by (simp add: NSRD_composition_wp assms rea_pre_RHS_design usubst unrest wp_rea_def R2c_disj
      R1_disj R2c_and R2c_preR R1_R2c_commute[THEN sym] R1_extend_conj' R1_idem R2c_not closure)
     (metis (no_types, lifting) Healthy_def Healthy_if NSRD_is_SRD R1_R2c_commute 
      R1_R2c_seqr_distribute R1_seqr_closure assms(1) assms(2) postR_R2c_closed postR_SRD_R1 
      preR_R2c_closed rea_not_R1 rea_not_R2c)
  
lemma periR_NSRD_seq [rdes]:
  assumes "P is NSRD" "Q is NSRD"
  shows "peri\<^sub>R(P ;; Q) = ((pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R Q) \<Rightarrow>\<^sub>r (peri\<^sub>R P \<or> (post\<^sub>R P ;; peri\<^sub>R Q)))"
  by (simp add: NSRD_composition_wp assms closure rea_peri_RHS_design usubst unrest wp_rea_def
      R1_extend_conj' R1_disj R1_R2c_seqr_distribute R2c_disj R2c_and R2c_rea_impl R1_rea_impl' 
      R2c_preR R2c_periR R1_rea_not' R2c_rea_not R1_peri_SRD)

lemma postR_NSRD_seq [rdes]:
  assumes "P is NSRD" "Q is NSRD"
  shows "post\<^sub>R(P ;; Q) = ((pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R Q) \<Rightarrow>\<^sub>r (post\<^sub>R P ;; post\<^sub>R Q))"
  by (simp add: NSRD_composition_wp assms closure rea_post_RHS_design usubst unrest wp_rea_def
      R1_extend_conj' R1_disj R1_R2c_seqr_distribute R2c_disj R2c_and R2c_rea_impl R1_rea_impl' 
      R2c_preR R2c_periR R1_rea_not' R2c_rea_not)

lemma NSRD_seqr_closure [closure]:
  assumes "P is NSRD" "Q is NSRD"
  shows "(P ;; Q) is NSRD"
proof -
  have "(\<not>\<^sub>r post\<^sub>R P wp\<^sub>r pre\<^sub>R Q) ;; true\<^sub>r = (\<not>\<^sub>r post\<^sub>R P wp\<^sub>r pre\<^sub>R Q)"
    by (simp add: wp_rea_def rpred assms closure seqr_assoc NSRD_neg_pre_unit)
  moreover have "$st\<acute> \<sharp> pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R Q \<Rightarrow>\<^sub>r peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R Q"
    by (simp add: unrest assms wp_rea_def)
  ultimately show ?thesis
    by (rule_tac NSRD_intro, simp_all add: seqr_or_distl NSRD_neg_pre_unit assms closure rdes unrest)
qed

lemma RHS_tri_normal_design_composition:
  assumes
    "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$ok \<sharp> R" "$ok \<sharp> S\<^sub>1" "$ok \<sharp> S\<^sub>2"
    "$wait \<sharp> R" "$wait\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> S\<^sub>1" "$wait \<sharp> S\<^sub>2"
    "P is R2c" "Q\<^sub>1 is R1" "Q\<^sub>1 is R2c" "Q\<^sub>2 is R1" "Q\<^sub>2 is R2c"
    "R is R2c" "S\<^sub>1 is R1" "S\<^sub>1 is R2c" "S\<^sub>2 is R1" "S\<^sub>2 is R2c"
    "R1 (\<not> P) ;; R1(true) = R1(\<not> P)" "$st\<acute> \<sharp> Q\<^sub>1"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)
         = \<^bold>R\<^sub>s((P \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (Q\<^sub>1 \<or> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
proof -
  have "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) =
        \<^bold>R\<^sub>s ((R1 (\<not> P) wp\<^sub>r false \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> ((\<exists> $st\<acute> \<bullet> Q\<^sub>1) \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
    by (simp_all add: RHS_tri_design_composition_wp rea_not_def assms unrest)
  also have "... = \<^bold>R\<^sub>s((P \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (Q\<^sub>1 \<or> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
    by (simp add: assms wp_rea_def ex_unrest, rel_auto)
  finally show ?thesis .
qed
  
lemma RHS_tri_normal_design_composition' [rdes_def]:
  assumes "P is RC" "Q\<^sub>1 is RR" "$st\<acute> \<sharp> Q\<^sub>1" "Q\<^sub>2 is RR" "R is RR" "S\<^sub>1 is RR" "S\<^sub>2 is RR"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)
         = \<^bold>R\<^sub>s((P \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (Q\<^sub>1 \<or> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
proof -
  have "R1 (\<not> P) ;; R1 true = R1(\<not> P)"
    using RC_implies_RC1[OF assms(1)]
    by (simp add: Healthy_def RC1_def rea_not_def)
       (metis R1_negate_R1 R1_seqr utp_pred_laws.double_compl)
  thus ?thesis
    by (simp add: RHS_tri_normal_design_composition assms closure unrest RR_implies_R2c)
qed

text \<open> If a normal reactive design has postcondition false, then it is a left zero for sequential
  composition. \<close>

lemma NSRD_seq_post_false:
  assumes "P is NSRD" "Q is SRD" "post\<^sub>R(P) = false"
  shows "P ;; Q = P"
  apply (simp add: NSRD_composition_wp assms wp rpred closure)
  using NSRD_is_SRD SRD_reactive_tri_design assms(1,3) apply fastforce
done

lemma NSRD_srd_skip [closure]: "II\<^sub>R is NSRD"
  by (rule NSRD_intro, simp_all add: rdes closure unrest)
  
lemma NSRD_Chaos [closure]: "Chaos is NSRD"
  by (rule NSRD_intro, simp_all add: closure rdes unrest)

lemma NSRD_Miracle [closure]: "Miracle is NSRD"
  by (rule NSRD_intro, simp_all add: closure rdes unrest)

text \<open> Post-composing a miracle filters out the non-terminating behaviours \<close>

lemma NSRD_right_Miracle_tri_lemma:
  assumes "P is NSRD"
  shows "P ;; Miracle = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> false)"
  by (simp add: NSRD_composition_wp closure assms rdes wp rpred)

lemma Miracle_right_anhil_iff:
  assumes "P is NSRD"
  shows "P ;; Miracle = Miracle \<longleftrightarrow> pre\<^sub>R P = true\<^sub>r \<and> (\<exists> $st\<acute> \<bullet> peri\<^sub>R P) = false"
  by (simp add: SRD_right_Miracle_tri_lemma assms closure, simp add: rdes_def srdes_tri_eq_iff closure assms wp rpred, fastforce)

text \<open> The set of non-terminating behaviours is a subset \<close>

lemma NSRD_right_Miracle_refines:
  assumes "P is NSRD"
  shows "P \<sqsubseteq> P ;; Miracle"
proof -
  have "\<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P) \<sqsubseteq> \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> false)"
    by (rule srdes_tri_refine_intro, rel_auto+)
  thus ?thesis
    by (simp add: NSRD_elim NSRD_right_Miracle_tri_lemma assms)
qed

text \<open> @{term Chaos} is a right zero of @{term P} precisely when the conjunction of the precondition
  of @{term P} with the weakest precondition under which @{term "post\<^sub>R P"} yields @{term false} 
  reduces to @{term false}. This is effectively a feasibility check for reactive designs. \<close>

lemma Chaos_right_anhil_iff:
  assumes "P is NSRD"
  shows "P ;; Chaos = Chaos \<longleftrightarrow> (pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r false) = false"
  by (simp add: SRD_right_Chaos_tri_lemma assms closure, simp add: rdes_def srdes_tri_eq_iff closure assms wp)

lemma upower_Suc_NSRD_closed [closure]:
  "P is NSRD \<Longrightarrow> P \<^bold>^ Suc n is NSRD"
proof (induct n)
  case 0
  then show ?case
    by (simp)
next
  case (Suc n)
  then show ?case
    by (simp add: NSRD_seqr_closure upred_semiring.power_Suc) 
qed

lemma NSRD_power_Suc [closure]:
  "P is NSRD \<Longrightarrow> P ;; P \<^bold>^ n is NSRD"
  by (metis upower_Suc_NSRD_closed upred_semiring.power_Suc)

lemma uplus_NSRD_closed [closure]: "P is NSRD \<Longrightarrow> P\<^sup>+ is NSRD"
  by (simp add: uplus_power_def closure)

lemma preR_power:
  assumes "P is NSRD"
  shows "pre\<^sub>R(P ;; P\<^bold>^n) = (\<Squnion> i\<in>{0..n}. (post\<^sub>R(P) \<^bold>^ i) wp\<^sub>r (pre\<^sub>R(P)))"
proof (induct n)
  case 0
  then show ?case
    by (simp add: wp closure)
next
  case (Suc n) note hyp = this
  have "pre\<^sub>R (P \<^bold>^ (Suc n + 1)) = pre\<^sub>R (P ;; P \<^bold>^ (n+1))"
    by (simp add: upred_semiring.power_Suc)
  also have "... = (pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R (P \<^bold>^ (Suc n)))"
    using NSRD_iff assms preR_NSRD_seq upower_Suc_NSRD_closed by fastforce
  also have "... = (pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r (\<Squnion>i\<in>{0..n}. post\<^sub>R P \<^bold>^ i wp\<^sub>r pre\<^sub>R P))"
    by (simp add: hyp upred_semiring.power_Suc)
  also have "... = (pre\<^sub>R P \<and> (\<Squnion>i\<in>{0..n}. post\<^sub>R P wp\<^sub>r (post\<^sub>R P \<^bold>^ i wp\<^sub>r pre\<^sub>R P)))"
    by (simp add: wp)
  also have "... = (pre\<^sub>R P \<and> (\<Squnion>i\<in>{0..n}. (post\<^sub>R P \<^bold>^ (i+1) wp\<^sub>r pre\<^sub>R P)))"
  proof -
    have "\<And> i. R1 (post\<^sub>R P \<^bold>^ i ;; (\<not>\<^sub>r pre\<^sub>R P)) = (post\<^sub>R P \<^bold>^ i ;; (\<not>\<^sub>r pre\<^sub>R P))"
      by (induct_tac i, simp_all add: closure Healthy_if assms)
    thus ?thesis
      by (simp add: wp_rea_def upred_semiring.power_Suc seqr_assoc rpred closure assms)
  qed
  also have "... = (post\<^sub>R P \<^bold>^ 0 wp\<^sub>r pre\<^sub>R P \<and> (\<Squnion>i\<in>{0..n}. (post\<^sub>R P \<^bold>^ (i+1) wp\<^sub>r pre\<^sub>R P)))"
    by (simp add: wp assms closure)
  also have "... = (post\<^sub>R P \<^bold>^ 0 wp\<^sub>r pre\<^sub>R P \<and> (\<Squnion>i\<in>{1..Suc n}. (post\<^sub>R P \<^bold>^ i wp\<^sub>r pre\<^sub>R P)))"
  proof -
    have "(\<Squnion>i\<in>{0..n}. (post\<^sub>R P \<^bold>^ (i+1) wp\<^sub>r pre\<^sub>R P)) = (\<Squnion>i\<in>{1..Suc n}. (post\<^sub>R P \<^bold>^ i wp\<^sub>r pre\<^sub>R P))"
      by (rule cong[of Inf], simp_all add: fun_eq_iff)
         (metis (no_types, lifting) image_Suc_atLeastAtMost image_cong image_image)
    thus ?thesis by simp
  qed
  also have "... = (\<Squnion>i\<in>insert 0 {1..Suc n}. (post\<^sub>R P \<^bold>^ i wp\<^sub>r pre\<^sub>R P))"
    by (simp add: conj_upred_def)
  also have "... = (\<Squnion>i\<in>{0..Suc n}. post\<^sub>R P \<^bold>^ i wp\<^sub>r pre\<^sub>R P)"
    by (simp add: atLeast0_atMost_Suc_eq_insert_0)
  finally show ?case by (simp add: upred_semiring.power_Suc)
qed

lemma preR_power' [rdes]:
  assumes "P is NSRD"
  shows "pre\<^sub>R(P ;; P\<^bold>^n) = (\<Squnion> i\<in>{0..n} \<bullet> (post\<^sub>R(P) \<^bold>^ i) wp\<^sub>r (pre\<^sub>R(P)))"
  by (simp add: preR_power assms USUP_as_Inf[THEN sym], simp add: USUP_as_Inf_image)

lemma preR_power_Suc [rdes]:
  assumes "P is NSRD"
  shows "pre\<^sub>R(P\<^bold>^(Suc n)) = (\<Squnion> i\<in>{0..n} \<bullet> (post\<^sub>R(P) \<^bold>^ i) wp\<^sub>r (pre\<^sub>R(P)))"
  by (simp add: upred_semiring.power_Suc rdes assms)

declare upred_semiring.power_Suc [simp]

lemma periR_power:
  assumes "P is NSRD"
  shows "peri\<^sub>R(P ;; P\<^bold>^n) = (pre\<^sub>R(P\<^bold>^(Suc n)) \<Rightarrow>\<^sub>r (\<Sqinter> i\<in>{0..n}. post\<^sub>R(P) \<^bold>^ i) ;; peri\<^sub>R(P))"
proof (induct n)
  case 0
  then show ?case
    by (simp add: NSRD_is_SRD NSRD_wait'_unrest_pre SRD_peri_under_pre assms)
next
  case (Suc n) note hyp = this
  have "peri\<^sub>R (P \<^bold>^ (Suc n + 1)) = peri\<^sub>R (P ;; P \<^bold>^ (n+1))"
    by (simp)
  also have "... = (pre\<^sub>R(P \<^bold>^ (Suc n + 1)) \<Rightarrow>\<^sub>r (peri\<^sub>R P \<or> post\<^sub>R P ;; peri\<^sub>R (P ;; P \<^bold>^ n)))"
    by (simp add: closure assms rdes)
  also have "... = (pre\<^sub>R(P \<^bold>^ (Suc n + 1)) \<Rightarrow>\<^sub>r (peri\<^sub>R P \<or> post\<^sub>R P ;; (pre\<^sub>R (P \<^bold>^ (Suc n)) \<Rightarrow>\<^sub>r (\<Sqinter>i\<in>{0..n}. post\<^sub>R P \<^bold>^ i) ;; peri\<^sub>R P)))"
    by (simp only: hyp)
  also
  have "... = (pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P \<or> (post\<^sub>R P wp\<^sub>r pre\<^sub>R (P ;; P \<^bold>^ n) \<Rightarrow>\<^sub>r post\<^sub>R P ;; (pre\<^sub>R (P ;; P \<^bold>^ n) \<Rightarrow>\<^sub>r (\<Sqinter>i\<in>{0..n}. post\<^sub>R P \<^bold>^ i) ;; peri\<^sub>R P)))"
    by (simp add: rdes closure assms, rel_blast)
  also
  have "... = (pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P \<or> (post\<^sub>R P wp\<^sub>r pre\<^sub>R (P ;; P \<^bold>^ n) \<Rightarrow>\<^sub>r post\<^sub>R P ;; ((\<Sqinter>i\<in>{0..n}. post\<^sub>R P \<^bold>^ i) ;; peri\<^sub>R P)))"
  proof -
    have "(\<Sqinter>i\<in>{0..n}. post\<^sub>R P \<^bold>^ i) is R1"
      by (simp add: NSRD_is_SRD R1_Continuous R1_power Sup_Continuous_closed assms postR_SRD_R1)
    hence 1:"((\<Sqinter>i\<in>{0..n}. post\<^sub>R P \<^bold>^ i) ;; peri\<^sub>R P) is R1"
      by (simp add: closure assms)
    hence "(pre\<^sub>R (P ;; P \<^bold>^ n) \<Rightarrow>\<^sub>r (\<Sqinter>i\<in>{0..n}. post\<^sub>R P \<^bold>^ i) ;; peri\<^sub>R P) is R1"
      by (simp add: closure)
    hence "(post\<^sub>R P wp\<^sub>r pre\<^sub>R (P ;; P \<^bold>^ n) \<Rightarrow>\<^sub>r post\<^sub>R P ;; (pre\<^sub>R (P ;; P \<^bold>^ n) \<Rightarrow>\<^sub>r (\<Sqinter>i\<in>{0..n}. post\<^sub>R P \<^bold>^ i) ;; peri\<^sub>R P))
          = (post\<^sub>R P wp\<^sub>r pre\<^sub>R (P ;; P \<^bold>^ n) \<Rightarrow>\<^sub>r R1(post\<^sub>R P) ;; R1(pre\<^sub>R (P ;; P \<^bold>^ n) \<Rightarrow>\<^sub>r (\<Sqinter>i\<in>{0..n}. post\<^sub>R P \<^bold>^ i) ;; peri\<^sub>R P))"
      by (simp add: Healthy_if R1_post_SRD assms closure)
    thus ?thesis
      by (simp only: wp_rea_impl_lemma, simp add: Healthy_if 1, simp add: R1_post_SRD assms closure)
  qed
  also
  have "... = (pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R (P ;; P \<^bold>^ n) \<Rightarrow>\<^sub>r peri\<^sub>R P \<or> post\<^sub>R P ;; ((\<Sqinter>i\<in>{0..n}. post\<^sub>R P \<^bold>^ i) ;; peri\<^sub>R P))"
    by (pred_auto)
  also
  have "... = (pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R (P ;; P \<^bold>^ n) \<Rightarrow>\<^sub>r peri\<^sub>R P \<or> ((\<Sqinter>i\<in>{0..n}. post\<^sub>R P \<^bold>^ (Suc i)) ;; peri\<^sub>R P))"
    by (simp add: seq_Sup_distl seqr_assoc[THEN sym])
  also
  have "... = (pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R (P ;; P \<^bold>^ n) \<Rightarrow>\<^sub>r peri\<^sub>R P \<or> ((\<Sqinter>i\<in>{1..Suc n}. post\<^sub>R P \<^bold>^ i) ;; peri\<^sub>R P))"
  proof -
    have "(\<Sqinter>i\<in>{0..n}. post\<^sub>R P \<^bold>^ Suc i) = (\<Sqinter>i\<in>{1..Suc n}. post\<^sub>R P \<^bold>^ i)"
      apply (rule cong[of Sup], auto)
      apply (metis atLeast0AtMost atMost_iff image_Suc_atLeastAtMost rev_image_eqI upred_semiring.power_Suc)
      using Suc_le_D apply fastforce
    done
    thus ?thesis by simp
  qed
  also
  have "... = (pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R (P ;; P \<^bold>^ n) \<Rightarrow>\<^sub>r ((\<Sqinter>i\<in>{0..Suc n}. post\<^sub>R P \<^bold>^ i)) ;; peri\<^sub>R P)"
    by (simp add: SUP_atLeastAtMost_first uinf_or seqr_or_distl seqr_or_distr)
  also
  have "... = (pre\<^sub>R(P\<^bold>^(Suc (Suc n))) \<Rightarrow>\<^sub>r ((\<Sqinter>i\<in>{0..Suc n}. post\<^sub>R P \<^bold>^ i) ;; peri\<^sub>R P))"
    by (simp add: rdes closure assms)
  finally show ?case by (simp)
qed

lemma periR_power' [rdes]:
  assumes "P is NSRD"
  shows "peri\<^sub>R(P ;; P\<^bold>^n) = (pre\<^sub>R(P\<^bold>^(Suc n)) \<Rightarrow>\<^sub>r (\<Sqinter> i\<in>{0..n} \<bullet> post\<^sub>R(P) \<^bold>^ i) ;; peri\<^sub>R(P))"
  by (simp add: periR_power assms UINF_as_Sup[THEN sym], simp add: UINF_as_Sup_image)

lemma periR_power_Suc [rdes]:
  assumes "P is NSRD"
  shows "peri\<^sub>R(P\<^bold>^(Suc n)) = (pre\<^sub>R(P\<^bold>^(Suc n)) \<Rightarrow>\<^sub>r (\<Sqinter> i\<in>{0..n} \<bullet> post\<^sub>R(P) \<^bold>^ i) ;; peri\<^sub>R(P))"
  by (simp add: rdes assms)

lemma postR_power [rdes]:
  assumes "P is NSRD"
  shows "post\<^sub>R(P ;; P\<^bold>^n) = (pre\<^sub>R(P\<^bold>^(Suc n)) \<Rightarrow>\<^sub>r post\<^sub>R(P) \<^bold>^ Suc n)"
proof (induct n)
  case 0
  then show ?case
    by (simp add: NSRD_is_SRD NSRD_wait'_unrest_pre SRD_post_under_pre assms)
next
  case (Suc n) note hyp = this
  have "post\<^sub>R (P \<^bold>^ (Suc n + 1)) = post\<^sub>R (P ;; P \<^bold>^ (n+1))"
    by (simp)
  also have "... = (pre\<^sub>R(P \<^bold>^ (Suc n + 1)) \<Rightarrow>\<^sub>r (post\<^sub>R P ;; post\<^sub>R (P ;; P \<^bold>^ n)))"
    by (simp add: closure assms rdes)
  also have "... = (pre\<^sub>R(P \<^bold>^ (Suc n + 1)) \<Rightarrow>\<^sub>r (post\<^sub>R P ;; (pre\<^sub>R (P \<^bold>^ Suc n) \<Rightarrow>\<^sub>r post\<^sub>R P \<^bold>^ Suc n)))"
    by (simp only: hyp)
  also
  have "... = (pre\<^sub>R P \<Rightarrow>\<^sub>r (post\<^sub>R P wp\<^sub>r pre\<^sub>R (P \<^bold>^ Suc n) \<Rightarrow>\<^sub>r post\<^sub>R P ;; (pre\<^sub>R (P \<^bold>^ Suc n) \<Rightarrow>\<^sub>r post\<^sub>R P \<^bold>^ Suc n)))"
    by (simp add: rdes closure assms, pred_auto)
  also
  have "... = (pre\<^sub>R P \<Rightarrow>\<^sub>r (post\<^sub>R P wp\<^sub>r pre\<^sub>R (P \<^bold>^ Suc n) \<Rightarrow>\<^sub>r post\<^sub>R P ;; post\<^sub>R P \<^bold>^ Suc n))"
    by (metis (no_types, lifting) Healthy_if NSRD_is_SRD NSRD_power_Suc R1_power assms hyp postR_SRD_R1 upred_semiring.power_Suc wp_rea_impl_lemma)
  also
  have "... = (pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R (P \<^bold>^ Suc n) \<Rightarrow>\<^sub>r post\<^sub>R P \<^bold>^ Suc (Suc n))"
    by (pred_auto)
  also have "... = (pre\<^sub>R(P\<^bold>^(Suc (Suc n))) \<Rightarrow>\<^sub>r post\<^sub>R P \<^bold>^ Suc (Suc n))"
    by (simp add: rdes closure assms)
  finally show ?case by (simp)
qed

lemma postR_power_Suc [rdes]:
  assumes "P is NSRD"
  shows "post\<^sub>R(P\<^bold>^(Suc n)) = (pre\<^sub>R(P\<^bold>^(Suc n)) \<Rightarrow>\<^sub>r post\<^sub>R(P) \<^bold>^ Suc n)"
  by (simp add: rdes assms)

lemma power_rdes_def [rdes_def]:
  assumes "P is RC" "Q is RR" "R is RR" "$st\<acute> \<sharp> Q"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R))\<^bold>^(Suc n) 
        = \<^bold>R\<^sub>s((\<Squnion> i\<in>{0..n} \<bullet> (R \<^bold>^ i) wp\<^sub>r P) \<turnstile> ((\<Sqinter> i\<in>{0..n} \<bullet> R \<^bold>^ i) ;; Q) \<diamondop> (R \<^bold>^ Suc n))"
proof (induct n)
  case 0
  then show ?case
    by (simp add: wp assms closure)
next
  case (Suc n)

  have 1: "(P \<and> (\<Squnion> i \<in> {0..n} \<bullet> R wp\<^sub>r (R \<^bold>^ i wp\<^sub>r P))) = (\<Squnion> i \<in> {0..Suc n} \<bullet> R \<^bold>^ i wp\<^sub>r P)"
    (is "?lhs = ?rhs")
  proof -
    have "?lhs = (P \<and> (\<Squnion> i \<in> {0..n} \<bullet> (R \<^bold>^ Suc i wp\<^sub>r P)))"
      by (simp add: wp closure assms)
    also have "... = (P \<and> (\<Squnion> i \<in> {0..n}. (R \<^bold>^ Suc i wp\<^sub>r P)))"
      by (simp only: USUP_as_Inf_collect)
    also have "... = (P \<and> (\<Squnion> i \<in> {1..Suc n}. (R \<^bold>^ i wp\<^sub>r P)))"
      by (metis (no_types, lifting) INF_cong One_nat_def image_Suc_atLeastAtMost image_image)
    also have "... = (\<Squnion> i \<in> insert 0 {1..Suc n}. (R \<^bold>^ i wp\<^sub>r P))"
      by (simp add: wp assms closure conj_upred_def)
    also have "... = (\<Squnion> i \<in> {0..Suc n}. (R \<^bold>^ i wp\<^sub>r P))"        
      by (simp add: atLeastAtMost_insertL)      
    finally show ?thesis
      by (simp add: USUP_as_Inf_collect)
  qed

  have 2: "(Q \<or> R ;; (\<Sqinter> i \<in> {0..n} \<bullet> R \<^bold>^ i) ;; Q) = (\<Sqinter> i \<in> {0..Suc n} \<bullet> R \<^bold>^ i) ;; Q"
    (is "?lhs = ?rhs")
  proof -
    have "?lhs = (Q \<or> (\<Sqinter> i \<in> {0..n} \<bullet> R \<^bold>^ Suc i) ;; Q)"
      by (simp add: seqr_assoc[THEN sym] seq_UINF_distl)
    also have "... = (Q \<or> (\<Sqinter> i \<in> {0..n}. R \<^bold>^ Suc i) ;; Q)"        
      by (simp only: UINF_as_Sup_collect)
    also have "... = (Q \<or> (\<Sqinter> i \<in> {1..Suc n}. R \<^bold>^ i) ;; Q)"
      by (metis One_nat_def image_Suc_atLeastAtMost image_image)        
    also have "... = ((\<Sqinter> i \<in> insert 0 {1..Suc n}. R \<^bold>^ i) ;; Q)"      
      by (simp add: disj_upred_def[THEN sym] seqr_or_distl)
    also have "... = ((\<Sqinter> i \<in> {0..Suc n}. R \<^bold>^ i) ;; Q)"    
      by (simp add: atLeastAtMost_insertL)
    finally show ?thesis
      by (simp add: UINF_as_Sup_collect)
  qed

  have 3: "(\<Sqinter> i \<in> {0..n} \<bullet> R \<^bold>^ i) ;; Q is RR"
  proof -
    have "(\<Sqinter> i \<in> {0..n} \<bullet> R \<^bold>^ i) ;; Q = (\<Sqinter> i \<in> {0..n}. R \<^bold>^ i) ;; Q"
      by (simp add: UINF_as_Sup_collect)
    also have "... = (\<Sqinter> i \<in> insert 0 {1..n}. R \<^bold>^ i) ;; Q"
      by (simp add: atLeastAtMost_insertL)
    also have "... = (Q \<or> (\<Sqinter> i \<in> {1..n}. R \<^bold>^ i) ;; Q)"
      by (metis (no_types, lifting) SUP_insert disj_upred_def seqr_left_unit seqr_or_distl upred_semiring.power_0)
    also have "... = (Q \<or> (\<Sqinter> i \<in> {0..<n}. R \<^bold>^ Suc i) ;; Q)"
      by (metis One_nat_def atLeastLessThanSuc_atLeastAtMost image_Suc_atLeastLessThan image_image)
    also have "... = (Q \<or> (\<Sqinter> i \<in> {0..<n} \<bullet> R \<^bold>^ Suc i) ;; Q)"
      by (simp add: UINF_as_Sup_collect)
    also have "... is RR"
      by (simp_all add: closure assms)
    finally show ?thesis .
  qed
  from 1 2 3 Suc show ?case
    by (simp add: Suc RHS_tri_normal_design_composition' closure assms wp)
qed

declare upred_semiring.power_Suc [simp del]

theorem uplus_rdes_def [rdes_def]:
  assumes "P is RC" "Q is RR" "R is RR" "$st\<acute> \<sharp> Q"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R))\<^sup>+ = \<^bold>R\<^sub>s(R\<^sup>\<star>\<^sup>r wp\<^sub>r P \<turnstile> (R\<^sup>\<star>\<^sup>r ;; Q) \<diamondop> R\<^sup>+)"
proof -
  have 1:"(\<Sqinter> i \<bullet> R \<^bold>^ i) ;; Q = R\<^sup>\<star>\<^sup>r ;; Q"
    by (metis (no_types) RA1 assms(2) rea_skip_unit(2) rrel_theory.Star_def ustar_alt_def)
  show ?thesis
    by (simp add: uplus_power_def seq_UINF_distr wp closure assms rdes_def)
       (metis "1" seq_UINF_distr')       
qed

subsection \<open> UTP theory \<close>

lemma NSRD_false: "NSRD false = Miracle"
  by (metis Healthy_if NSRD_Miracle NSRD_alt_def NSRD_is_RD3 srdes_theory.healthy_top)

lemma NSRD_true: "NSRD true = Chaos"
  by (metis Healthy_if NSRD_Chaos NSRD_alt_def NSRD_is_RD3 srdes_theory.healthy_bottom)
 
interpretation nsrdes_theory: utp_theory_kleene NSRD II\<^sub>R
  rewrites "P \<in> carrier nsrdes_theory.thy_order \<longleftrightarrow> P is NSRD"
  and "carrier nsrdes_theory.thy_order \<rightarrow> carrier nsrdes_theory.thy_order \<equiv> \<lbrakk>NSRD\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>NSRD\<rbrakk>\<^sub>H"
  and "le nsrdes_theory.thy_order = (\<sqsubseteq>)"
  and "eq nsrdes_theory.thy_order = (=)"
  and nsrdes_top: "nsrdes_theory.utp_top = Miracle" 
  and nsrdes_bottom: "nsrdes_theory.utp_bottom = Chaos"
proof -
  have "utp_theory_continuous NSRD"
    by (unfold_locales, simp_all add: NSRD_idem NSRD_Continuous)
  then interpret utp_theory_continuous NSRD
    by simp
  show t: "utp_top = Miracle" and b:"utp_bottom = Chaos"
    by (simp_all add: healthy_top healthy_bottom NSRD_false NSRD_true)
  show "utp_theory_kleene NSRD II\<^sub>R"
    by (unfold_locales, simp_all add: closure srdes_left_unital.Unit_Left NSRD_right_unit Miracle_left_zero t)
qed (simp_all)

abbreviation TestR ("test\<^sub>R") where
"test\<^sub>R P \<equiv> nsrdes_theory.utp_test P"

definition StarR :: "('s, 't::trace, '\<alpha>) hrel_rsp \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp" ("_\<^sup>\<star>\<^sup>R" [999] 999) where
"StarR \<equiv> nsrdes_theory.utp_star"

text \<open> We also show how to calculate the Kleene closure of a reactive design. \<close>

thm rdes_def

lemma StarR_rdes_def [rdes_def]:
  assumes "P is RC" "Q is RR" "R is RR" "$st\<acute> \<sharp> Q"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R))\<^sup>\<star>\<^sup>R = \<^bold>R\<^sub>s((R\<^sup>\<star>\<^sup>r wp\<^sub>r P) \<turnstile> (R\<^sup>\<star>\<^sup>r ;; Q) \<diamondop> R\<^sup>\<star>\<^sup>r)"
  by (simp add: StarR_def rrel_theory.Star_alt_def nsrdes_theory.Star_alt_def closure assms)
     (simp add: rrel_theory.Star_alt_def assms closure rdes_def unrest rpred disj_upred_def)

end