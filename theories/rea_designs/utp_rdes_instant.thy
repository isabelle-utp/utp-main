section \<open> Instantaneous Reactive Designs \<close>

theory utp_rdes_instant
  imports utp_rdes_prog
begin
  
definition ISRD1 :: "('s,'t::trace,'\<alpha>) hrel_rsp \<Rightarrow> ('s,'t,'\<alpha>) hrel_rsp" where
[upred_defs]: "ISRD1(P) = P \<parallel>\<^sub>R choose\<^sub>R"

definition ISRD :: "('s,'t::trace,'\<alpha>) hrel_rsp \<Rightarrow> ('s,'t,'\<alpha>) hrel_rsp" where
[upred_defs]: "ISRD = ISRD1 \<circ> NSRD"

lemma ISRD1_idem: "ISRD1(ISRD1(P)) = ISRD1(P)"
  by (rel_auto)
    
lemma ISRD1_monotonic: "P \<sqsubseteq> Q \<Longrightarrow> ISRD1(P) \<sqsubseteq> ISRD1(Q)"
  by (rel_auto)

lemma ISRD1_rdes_def [rdes_def]: 
  "\<lbrakk> P is RR; R is RR \<rbrakk> \<Longrightarrow> ISRD1(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = \<^bold>R\<^sub>s(P \<turnstile> false \<diamondop> R)"
  by (simp add: ISRD1_def rdes_def closure rpred)
    
lemma ISRD_intro: 
  assumes "P is NSRD" "peri\<^sub>R(P) = (\<not>\<^sub>r pre\<^sub>R(P))"
  shows "P is ISRD"
proof -
  have "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) is ISRD1"
    by (simp add: Healthy_def rdes_def closure assms, rel_auto)
  hence "P is ISRD1"
    by (simp add: SRD_reactive_tri_design closure assms(1))
  thus ?thesis
    by (simp add: ISRD_def Healthy_comp assms(1))
qed

lemma ISRD_rdes_intro [closure]:
  assumes "P is RC" "Q is RR"
  shows "\<^bold>R\<^sub>s(P \<turnstile> false \<diamondop> Q) is ISRD"
  by (simp_all add: ISRD_intro closure assms unrest rdes)
  
lemma ISRD_implies_ISRD1:
  assumes "P is ISRD"
  shows "P is ISRD1"
proof -
  have "ISRD(P) is ISRD1"
    by (simp add: ISRD_def Healthy_def ISRD1_idem)
  thus ?thesis
    by (simp add: assms Healthy_if)
qed
  
lemma ISRD_implies_SRD: 
  assumes "P is ISRD"
  shows "P is SRD"
proof -
  have 1:"ISRD(P) = \<^bold>R\<^sub>s((\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R P) ;; R1 true \<and> R1 true) \<turnstile> false \<diamondop> (post\<^sub>R P \<and> R1 true))"
    by (simp add: NSRD_form ISRD1_def ISRD_def RHS_tri_design_par rdes_def unrest closure)
  moreover have "... is SRD"
    by (simp add: closure unrest)
  ultimately have "ISRD(P) is SRD"
    by (simp)
  with assms show ?thesis
    by (simp add: Healthy_def)
qed
    
lemma ISRD_implies_NSRD [closure]: 
  assumes "P is ISRD"
  shows "P is NSRD"
proof -
  have 1:"ISRD(P) = ISRD1(RD3(SRD(P)))"
    by (simp add: ISRD_def NSRD_def SRD_def, metis RD1_RD3_commute RD3_left_subsumes_RD2)
  also have "... = ISRD1(RD3(P))"
    by (simp add: assms ISRD_implies_SRD Healthy_if)
  also have "... = ISRD1 (\<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false\<^sub>h \<turnstile> (\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<diamondop> post\<^sub>R P))"
    by (simp add: RD3_def, subst SRD_right_unit_tri_lemma, simp_all add: assms ISRD_implies_SRD)
  also have "... = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false\<^sub>h \<turnstile> false \<diamondop> post\<^sub>R P)"
    by (simp add: RHS_tri_design_par ISRD1_def unrest choose_srd_def rpred closure ISRD_implies_SRD assms)
  also have "... = (... ;; II\<^sub>R)"
    by (rdes_simp, simp add: RHS_tri_normal_design_composition' closure assms unrest ISRD_implies_SRD wp rpred wp_rea_false_RC)
  also have "... is RD3"
    by (simp add: Healthy_def RD3_def seqr_assoc, simp add: NSRD_right_unit closure)
  finally show ?thesis
    by (simp add: SRD_RD3_implies_NSRD Healthy_if assms ISRD_implies_SRD)
qed
  
lemma ISRD_form:
  assumes "P is ISRD"
  shows "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> false \<diamondop> post\<^sub>R(P)) = P"
proof -
  have "P = ISRD1(P)"
    by (simp add: ISRD_implies_ISRD1 assms Healthy_if)
  also have "... = ISRD1(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))"
    by (simp add: SRD_reactive_tri_design ISRD_implies_SRD assms)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> false \<diamondop> post\<^sub>R(P))"
    by (simp add: ISRD1_rdes_def closure assms ISRD_implies_NSRD)
  finally show ?thesis ..
qed
    
lemma ISRD_elim: 
  "\<lbrakk> P is ISRD; Q(\<^bold>R\<^sub>s (pre\<^sub>R(P) \<turnstile> false \<diamondop> post\<^sub>R(P))) \<rbrakk> \<Longrightarrow> Q(P)"
  by (simp add: ISRD_form)
  
lemma skip_srd_ISRD [closure]: "II\<^sub>R is ISRD"
  by (rule ISRD_intro, simp_all add: rdes closure)
    
lemma assigns_srd_ISRD [closure]: "\<langle>\<sigma>\<rangle>\<^sub>R is ISRD"
  by (rule ISRD_intro, simp_all add: rdes closure)
     
lemma seq_ISRD_closed:
  assumes "P is ISRD" "Q is ISRD"
  shows "P ;; Q is ISRD"
  apply (insert assms)
  apply (erule ISRD_elim)+
  apply (simp add: rdes_def closure assms unrest)
done

end