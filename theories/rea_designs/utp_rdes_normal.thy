section \<open> Normal Reactive Designs \<close>

theory utp_rdes_normal
  imports utp_rdes_triples
begin

text \<open> This additional healthiness condition is analogous to H3 \<close>

definition RD3 :: "('s, 't::trace, '\<alpha>, '\<beta>) rel_rsp \<Rightarrow> ('s, 't, '\<alpha>, '\<beta>) rel_rsp" where
[upred_defs]: "RD3(P) = P ;; II\<^sub>R"

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

lemma RHS_tri_design_right_unit_lemma:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok\<acute> \<sharp> R" "$wait\<acute> \<sharp> R"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) ;; II\<^sub>R = \<^bold>R\<^sub>s((\<not>\<^sub>r (\<not>\<^sub>r P) ;; true\<^sub>r) \<turnstile> ((\<exists> $st\<acute> \<bullet> Q) \<diamondop> R))"
proof -
  have "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) ;; II\<^sub>R = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) ;; \<^bold>R\<^sub>s(true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R))"
    by (simp add: srdes_skip_tri_design, rel_auto)
  also have "... = \<^bold>R\<^sub>s ((\<not> R1 (\<not> R2s P) ;; R1 true) \<turnstile> (\<exists> $st\<acute> \<bullet> Q) \<diamondop> (R1 (R2s R) ;; R1 (R2s ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R))))"
    by (simp_all add: RHS_tri_design_composition assms unrest R2s_true R1_false R2s_false)
  also have "... = \<^bold>R\<^sub>s ((\<not> R1 (\<not> R2s P) ;; R1 true) \<turnstile> (\<exists> $st\<acute> \<bullet> Q) \<diamondop> R1 (R2s R))"
  proof -
    from assms(3,4) have "(R1 (R2s R) ;; R1 (R2s ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R))) = R1 (R2s R)"
      by (rel_auto, metis (no_types, lifting) minus_zero_eq, meson order_refl trace_class.diff_cancel)
    thus ?thesis
      by simp
  qed
  also have "... = \<^bold>R\<^sub>s((\<not> (\<not> P) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> Q) \<diamondop> R))"
    by (metis (no_types, lifting) R1_R2s_R1_true_lemma R1_R2s_R2c R2c_not RHS_design_R2c_pre RHS_design_neg_R1_pre RHS_design_post_R1 RHS_design_post_R2s)
  also have "... = \<^bold>R\<^sub>s((\<not>\<^sub>r (\<not>\<^sub>r P) ;; true\<^sub>r) \<turnstile> ((\<exists> $st\<acute> \<bullet> Q) \<diamondop> R))"
    by (rel_auto)
  finally show ?thesis .
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

text {* RD3 reactive designs are those whose assumption can be written as a conjunction of a
  precondition on (undashed) program variables, and a negated statement about the trace. The latter
  allows us to state that certain events must not occur in the trace -- which are effectively safety
  properties. *}

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

lemma RD1_RD3_commute: "RD1(RD3(P)) = RD3(RD1(P))"
  by (rel_auto, blast+)

lemma NSRD_is_SRD [closure]: "P is NSRD \<Longrightarrow> P is SRD"
  by (simp add: Healthy_def NSRD_def SRD_def, metis Healthy_def RD1_RD3_commute RD2_RHS_commute RD3_def RD3_right_subsumes_RD2 SRD_def SRD_idem SRD_seqr_closure SRD_srdes_skip)

lemma NSRD_elim [RD_elim]: 
  "\<lbrakk> P is NSRD; Q(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))) \<rbrakk> \<Longrightarrow> Q(P)"
  by (simp add: RD_elim closure)
    
lemma NSRD_Idempotent [closure]: "Idempotent NSRD"
  by (clarsimp simp add: Idempotent_def NSRD_def, metis (no_types, hide_lams) Healthy_def RD1_RD3_commute RD3_def RD3_idem RD3_left_subsumes_RD2 SRD_def SRD_idem SRD_seqr_closure SRD_srdes_skip)

lemma NSRD_Continuous [closure]: "Continuous NSRD"
  by (simp add: Continuous_comp NSRD_def RD1_Continuous RD3_Continuous RHS_Continuous)
    
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

lemma preR_RR [closure]: "P is NSRD \<Longrightarrow> pre\<^sub>R(P) is RR"
  by (rule RR_intro, simp_all add: closure unrest)

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

lemma NSRD_refine_intro:
  assumes
    "P is NSRD" "Q is NSRD"
    "`pre\<^sub>R(P) \<Rightarrow>\<^sub>r pre\<^sub>R(Q)`" "`peri\<^sub>R(Q) \<Rightarrow>\<^sub>r peri\<^sub>R(P)`" "`post\<^sub>R(Q) \<Rightarrow>\<^sub>r post\<^sub>R(P)`"
  shows "P \<sqsubseteq> Q"
proof -
  have 1:"`pre\<^sub>R(P) \<and> peri\<^sub>R(Q) \<Rightarrow>\<^sub>r peri\<^sub>R(P)` = `peri\<^sub>R(Q) \<Rightarrow>\<^sub>r (pre\<^sub>R(P) \<Rightarrow>\<^sub>r peri\<^sub>R(P))`"
    by (rel_blast)
  have 2:"`pre\<^sub>R(P) \<and> post\<^sub>R(Q) \<Rightarrow>\<^sub>r post\<^sub>R(P)` = `post\<^sub>R(Q) \<Rightarrow>\<^sub>r (pre\<^sub>R(P) \<Rightarrow>\<^sub>r post\<^sub>R(P))`"      
    by (rel_blast)
  show ?thesis
    by (rule SRD_refine_intro', simp_all add: closure assms 1 2 SRD_post_under_pre SRD_peri_under_pre unrest)
qed

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

lemma NSRD_srd_skip [closure]: "II\<^sub>R is NSRD"
  by (rule NSRD_intro, simp_all add: rdes closure unrest)
  
lemma NSRD_Chaos [closure]: "Chaos is NSRD"
  by (rule NSRD_intro, simp_all add: closure rdes unrest)

lemma NSRD_Miracle [closure]: "Miracle is NSRD"
  by (rule NSRD_intro, simp_all add: closure rdes unrest)

lemma NSRD_right_Miracle_tri_lemma:
  assumes "P is NSRD"
  shows "P ;; Miracle = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> false)"
  by (simp add: NSRD_composition_wp closure assms rdes wp rpred)

end