section \<open> Stateful-Failure Reactive Relations \<close>

theory utp_sfrd_rel
  imports utp_sfrd_core
begin

subsection \<open> Healthiness Conditions \<close>
  
text \<open> CSP Reactive Relations \<close>
    
definition CRR :: "('s,'e) action \<Rightarrow> ('s,'e) action" where
[upred_defs]: "CRR(P) = (\<exists> $ref \<bullet> RR(P))"

lemma CRR_idem: "CRR(CRR(P)) = CRR(P)"
  by (rel_auto)

lemma Idempotent_CRR [closure]: "Idempotent CRR"
  by (simp add: CRR_idem Idempotent_def)

lemma Continuous_CRR [closure]: "Continuous CRR"
  by (rel_blast)

lemma CRR_intro:
  assumes "$ref \<sharp> P" "P is RR"
  shows "P is CRR"
  by (simp add: CRR_def Healthy_def, simp add: Healthy_if assms ex_unrest)

lemma CRR_form: "CRR(P) = (\<exists> {$ok, $ok\<acute>, $wait, $wait\<acute>, $ref} \<bullet> (\<^bold>\<exists> tt\<^sub>0 \<bullet> P\<lbrakk>\<guillemotleft>[]\<guillemotright>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>))"
  by (rel_auto; fastforce)

lemma CRR_seqr_form: 
  "CRR(P) ;; CRR(Q) = 
    (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((\<exists> {$ok, $ok\<acute>, $wait, $wait\<acute>, $ref} \<bullet> P)\<lbrakk>\<guillemotleft>[]\<guillemotright>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; 
                      (\<exists> {$ok, $ok\<acute>, $wait, $wait\<acute>, $ref} \<bullet> Q)\<lbrakk>\<guillemotleft>[]\<guillemotright>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>))"
  by (simp add: CRR_form, rel_auto; fastforce)

text \<open> CSP Reactive Finalisers \<close>
    
definition CRF :: "('s,'e) action \<Rightarrow> ('s,'e) action" where
[upred_defs]: "CRF(P) = (\<exists> $ref\<acute> \<bullet> CRR(P))"

lemma CRF_idem: "CRF(CRF(P)) = CRF(P)"
  by (rel_auto)

lemma Idempotent_CRF [closure]: "Idempotent CRF"
  by (simp add: CRF_idem Idempotent_def)

lemma Continuous_CRF [closure]: "Continuous CRF"
  by (rel_blast)

lemma CRF_intro:
  assumes "$ref \<sharp> P" "$ref\<acute> \<sharp> P" "P is RR"
  shows "P is CRF"
  by (simp add: CRF_def CRR_def Healthy_def, simp add: Healthy_if assms ex_unrest)

lemma CRF_implies_CRR [closure]:
  assumes "P is CRF" shows "P is CRR"
proof -
  have "CRR(CRF(P)) = CRF(P)"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def assms)
qed

definition crel_skip :: "('s, 'e) action" ("II\<^sub>c") where
[upred_defs]: "crel_skip = ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st)"

lemma crel_skip_CRR [closure]: "II\<^sub>c is CRF"
  by (rel_auto)

lemma crel_skip_via_rrel: "II\<^sub>c = CRR(II\<^sub>r)"
  by (rel_auto)

lemma crel_skip_left_unit [rpred]:  
  assumes "P is CRR" 
  shows "II\<^sub>c ;; P = P"
proof -
  have "II\<^sub>c ;; CRR(P) = CRR(P)" by (rel_auto)
  thus ?thesis by (simp add: Healthy_if assms)
qed

lemma crel_skip_right_unit [rpred]:  
  assumes "P is CRF" 
  shows "P ;; II\<^sub>c = P"
proof -
  have "CRF(P) ;; II\<^sub>c = CRF(P)" by (rel_auto)
  thus ?thesis by (simp add: Healthy_if assms)
qed

text \<open> CSP Reactive Conditions \<close>

definition CRC :: "('s,'e) action \<Rightarrow> ('s,'e) action" where
[upred_defs]: "CRC(P) = (\<exists> $ref \<bullet> RC(P))"
    
lemma CRC_intro:
  assumes "$ref \<sharp> P" "P is RC"
  shows "P is CRC"
  by (simp add: CRC_def Healthy_def, simp add: Healthy_if assms ex_unrest)

lemma CRC_intro':
  assumes "P is CRR" "P is RC"
  shows "P is CRC"
  by (metis CRC_def CRR_def Healthy_def RC_implies_RR assms)

lemma ref_unrest_RR [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> RR P"
  by (rel_auto, blast+)

lemma ref_unrest_RC1 [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> RC1 P"
  by (rel_auto, blast+)

lemma ref_unrest_RC [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> RC P"
  by (simp add: RC_R2_def ref_unrest_RC1 ref_unrest_RR)

lemma RR_ex_ref: "RR (\<exists> $ref \<bullet> RR P) = (\<exists> $ref \<bullet> RR P)"
  by (rel_auto)

lemma RC1_ex_ref: "RC1 (\<exists> $ref \<bullet> RC1 P) = (\<exists> $ref \<bullet> RC1 P)"
  by (rel_auto, meson dual_order.trans)

lemma ex_ref'_RR_closed [closure]: 
  assumes "P is RR"
  shows "(\<exists> $ref\<acute> \<bullet> P) is RR"
proof -
  have "RR (\<exists> $ref\<acute> \<bullet> RR(P)) = (\<exists> $ref\<acute> \<bullet> RR(P))"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma CRC_idem: "CRC(CRC(P)) = CRC(P)"
  apply (simp add: CRC_def ex_unrest  unrest)
  apply (simp add: RC_def RR_ex_ref)
  apply (metis (no_types, opaque_lifting) Healthy_def RC1_RR_closed RC1_ex_ref RR_ex_ref RR_idem)
done

lemma Idempotent_CRC [closure]: "Idempotent CRC"
  by (simp add: CRC_idem Idempotent_def)

subsection \<open> Closure Properties \<close>

lemma CRR_implies_RR [closure]: 
  assumes "P is CRR"
  shows "P is RR"
proof -
  have "RR(CRR(P)) = CRR(P)"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def' assms)
qed

lemma CRC_intro'':
  assumes "P is CRR" "P is RC1"
  shows "P is CRC"
  by (simp add: CRC_intro' CRR_implies_RR RC_intro' assms)

lemma CRC_implies_RR [closure]: 
  assumes "P is CRC" 
  shows "P is RR"
proof -
  have "RR(CRC(P)) = CRC(P)"
    by (rel_auto)
       (metis (no_types, lifting) Prefix_Order.prefixE Prefix_Order.prefixI append.assoc append_minus)+
  thus ?thesis
    by (metis Healthy_def assms)
qed
  
lemma CRC_implies_RC [closure]: 
  assumes "P is CRC"
  shows "P is RC"
proof -
  have "RC1(CRC(P)) = CRC(P)"
    by (rel_auto, meson dual_order.trans)
  thus ?thesis
    by (simp add: CRC_implies_RR Healthy_if RC1_def RC_intro assms)
qed

lemma CRR_unrest_ref [unrest]: "P is CRR \<Longrightarrow> $ref \<sharp> P"
  by (metis CRR_def CRR_implies_RR Healthy_def in_var_uvar ref_vwb_lens unrest_as_exists)

lemma CRF_unrest_ref' [unrest]: 
  assumes "P is CRF"
  shows "$ref\<acute> \<sharp> P"
proof -
  have "$ref\<acute> \<sharp> CRF(P)" by (simp add: CRF_def unrest)
  thus ?thesis by (simp add: assms Healthy_if)
qed

lemma CRC_implies_CRR [closure]:
  assumes "P is CRC"
  shows "P is CRR"
  apply (rule CRR_intro)
   apply (simp_all add: unrest assms closure)
  apply (metis CRC_def CRC_implies_RC Healthy_def assms in_var_uvar ref_vwb_lens unrest_as_exists)
  done

lemma unrest_ref'_neg_RC [unrest]:
  assumes "P is RR" "P is RC"
  shows "$ref\<acute> \<sharp> P"
proof -
  have "P = (\<not>\<^sub>r \<not>\<^sub>r P)"
    by (simp add: closure rpred assms)
  also have "... = (\<not>\<^sub>r (\<not>\<^sub>r P) ;; true\<^sub>r)"
    by (metis Healthy_if RC1_def RC_implies_RC1 assms(2) calculation)
  also have "$ref\<acute> \<sharp> ..."
    by (rel_auto)
  finally show ?thesis .
qed

lemma rea_true_CRR [closure]: "true\<^sub>r is CRR"
  by (rel_auto)

lemma rea_true_CRC [closure]: "true\<^sub>r is CRC"
  by (rel_auto)

lemma false_CRR [closure]: "false is CRR"
  by (rel_auto)

lemma false_CRC [closure]: "false is CRC"
  by (rel_auto)

lemma st_pred_CRR [closure]: "[P]\<^sub>S\<^sub>< is CRR"
  by (rel_auto)

lemma st_post_unrest_ref' [unrest]: "$ref\<acute> \<sharp> [b]\<^sub>S\<^sub>>"
  by (rel_auto)

lemma st_post_CRR [closure]: "[b]\<^sub>S\<^sub>> is CRR"
  by (rel_auto)

lemma st_cond_CRC [closure]: "[P]\<^sub>S\<^sub>< is CRC"
  by (rel_auto)

lemma st_cond_CRF [closure]: "[b]\<^sub>S\<^sub>< is CRF"
  by (rel_auto)

lemma rea_rename_CRR_closed [closure]: 
  assumes "P is CRR"
  shows "P\<lparr>f\<rparr>\<^sub>r is CRR"
proof -
  have "$ref \<sharp> (CRR P)\<lparr>f\<rparr>\<^sub>r"
    by (rel_auto)
  thus ?thesis
    by (rule_tac CRR_intro, simp_all add: closure Healthy_if assms)
qed

lemma st_subst_CRR_closed [closure]:
  assumes "P is CRR"
  shows "(\<sigma> \<dagger>\<^sub>S P) is CRR"
  by (rule CRR_intro, simp_all add: unrest closure assms)

lemma st_subst_CRC_closed [closure]:
  assumes "P is CRC"
  shows "(\<sigma> \<dagger>\<^sub>S P) is CRC"
  by (rule CRC_intro, simp_all add: closure assms unrest)

lemma conj_CRC_closed [closure]:
  "\<lbrakk> P is CRC; Q is CRC \<rbrakk> \<Longrightarrow> (P \<and> Q) is CRC"
  by (rule CRC_intro, simp_all add: unrest closure)

lemma conj_CRF_closed [closure]: "\<lbrakk> P is CRF; Q is CRF \<rbrakk> \<Longrightarrow> (P \<and> Q) is CRF"
  by (rule CRF_intro, simp_all add: unrest closure)

lemma disj_CRC_closed [closure]:
  "\<lbrakk> P is CRC; Q is CRC \<rbrakk> \<Longrightarrow> (P \<or> Q) is CRC"
  by (rule CRC_intro, simp_all add: unrest closure)

lemma st_cond_left_impl_CRC_closed [closure]: 
  "P is CRC \<Longrightarrow> ([b]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P) is CRC"
  by (rule CRC_intro, simp_all add: unrest closure)

lemma unrest_ref_map_st [unrest]: "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> P \<oplus>\<^sub>r map_st\<^sub>L[a]"
  by (rel_auto)

lemma unrest_ref'_map_st [unrest]: "$ref\<acute> \<sharp> P \<Longrightarrow> $ref\<acute> \<sharp> P \<oplus>\<^sub>r map_st\<^sub>L[a]"
  by (rel_auto)

lemma unrest_ref_rdes_frame_ext [unrest]: 
  "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> a:[P]\<^sub>r\<^sup>+"
  by (rel_blast)

lemma unrest_ref'_rdes_frame_ext [unrest]: 
  "$ref\<acute> \<sharp> P \<Longrightarrow> $ref\<acute> \<sharp> a:[P]\<^sub>r\<^sup>+"
  by (rel_blast)

lemma map_st_ext_CRR_closed [closure]:
  assumes "P is CRR"
  shows "P \<oplus>\<^sub>r map_st\<^sub>L[a] is CRR"
  by (rule CRR_intro, simp_all add: closure unrest assms)

lemma map_st_ext_CRC_closed [closure]:
  assumes "P is CRC"
  shows "P \<oplus>\<^sub>r map_st\<^sub>L[a] is CRC"
  by (rule CRC_intro, simp_all add: closure unrest assms)

 lemma rdes_frame_ext_CRR_closed [closure]:
  assumes "P is CRR"
  shows "a:[P]\<^sub>r\<^sup>+ is CRR"
  by (rule CRR_intro, simp_all add: closure unrest assms)

lemma USUP_CRC_closed [closure]: "\<lbrakk> A \<noteq> {}; \<And> i. i \<in> A \<Longrightarrow> P i is CRC \<rbrakk> \<Longrightarrow> (\<Squnion> i \<in> A \<bullet> P i) is CRC"
  by (rule CRC_intro, simp_all add: unrest closure)

lemma UINF_CRR_closed [closure]: "\<lbrakk> \<And> i. i \<in> A \<Longrightarrow> P i is CRR \<rbrakk> \<Longrightarrow> (\<Sqinter> i \<in> A \<bullet> P i) is CRR"
  by (rule CRR_intro, simp_all add: unrest closure)

lemma cond_CRC_closed [closure]:
  assumes "P is CRC" "Q is CRC"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is CRC"
  by (rule CRC_intro, simp_all add: closure assms unrest)

lemma shEx_CRR_closed [closure]: 
  assumes "\<And> x. P x is CRR"
  shows "(\<^bold>\<exists> x \<bullet> P(x)) is CRR"
proof -
  have "CRR(\<^bold>\<exists> x \<bullet> CRR(P(x))) = (\<^bold>\<exists> x \<bullet> CRR(P(x)))"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def assms shEx_cong)
qed
    
lemma USUP_ind_CRR_closed [closure]:
  assumes "\<And> i. P i is CRR"
  shows "(\<Squnion> i \<bullet> P(i)) is CRR"
  by (rule CRR_intro, simp_all add: assms unrest closure)

lemma UINF_ind_CRR_closed [closure]:
  assumes "\<And> i. P i is CRR"
  shows "(\<Sqinter> i \<bullet> P(i)) is CRR"
  by (rule CRR_intro, simp_all add: assms unrest closure)
   
lemma cond_tt_CRR_closed [closure]: 
  assumes "P is CRR" "Q is CRR"
  shows "P \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> Q is CRR"
  by (rule CRR_intro, simp_all add: unrest assms closure)
    
lemma rea_implies_CRR_closed [closure]:
  "\<lbrakk> P is CRR; Q is CRR \<rbrakk> \<Longrightarrow> (P \<Rightarrow>\<^sub>r Q) is CRR"
  by (simp_all add: CRR_intro closure unrest)

lemma conj_CRR_closed [closure]:
  "\<lbrakk> P is CRR; Q is CRR \<rbrakk> \<Longrightarrow> (P \<and> Q) is CRR"
  by (simp_all add: CRR_intro closure unrest)

lemma disj_CRR_closed [closure]: 
  "\<lbrakk> P is CRR; Q is CRR \<rbrakk> \<Longrightarrow> (P \<or> Q) is CRR"
  by (rule CRR_intro, simp_all add: unrest closure)

lemma rea_not_CRR_closed [closure]:
  "P is CRR \<Longrightarrow> (\<not>\<^sub>r P) is CRR"
  using false_CRR rea_implies_CRR_closed by fastforce
    
lemma cond_st_CRR_closed [closure]:
  "\<lbrakk> P is CRR; Q is CRR \<rbrakk> \<Longrightarrow> (P \<triangleleft> b \<triangleright>\<^sub>R Q) is CRR"
  by (simp_all add: CRR_intro closure unrest)

lemma seq_CRR_closed [closure]:
  assumes "P is CRR" "Q is RR"
  shows "(P ;; Q) is CRR"
  by (rule CRR_intro, simp_all add: unrest assms closure)

lemma seq_CRF_closed [closure]:
  assumes "P is CRF" "Q is CRF"
  shows "(P ;; Q) is CRF"
  by (rule CRF_intro, simp_all add: unrest assms closure)

lemma rea_st_cond_CRF [closure]: "[b]\<^sub>S\<^sub>< is CRF"
  by (rel_auto)

lemma conj_CRF [closure]: "\<lbrakk> P is CRF; Q is CRF \<rbrakk> \<Longrightarrow> (P \<and> Q) is CRF"
  by (simp add: CRF_implies_CRR CRF_intro CRF_unrest_ref' CRR_implies_RR CRR_unrest_ref conj_RR unrest_conj)

lemma wp_rea_CRC [closure]: "\<lbrakk> P is CRR; Q is RC \<rbrakk> \<Longrightarrow> P wp\<^sub>r Q is CRC"
  by (rule CRC_intro, simp_all add: unrest closure)

lemma USUP_ind_CRC_closed [closure]: 
  "\<lbrakk> \<And> i. P i is CRC \<rbrakk> \<Longrightarrow> (\<Squnion> i \<bullet> P i) is CRC"
  by (metis CRC_implies_CRR CRC_implies_RC USUP_ind_CRR_closed USUP_ind_RC_closed false_CRC rea_not_CRR_closed wp_rea_CRC wp_rea_RC_false)

lemma tr_extend_seqr_lit [rdes]:
  fixes P :: "('s, 'e) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P" "$ref \<sharp> P"
  shows "U($tr\<acute> = $tr @ [\<guillemotleft>a\<guillemotright>] \<and> $st\<acute> = $st) ;; P = P\<lbrakk>U($tr @ [\<guillemotleft>a\<guillemotright>])/$tr\<rbrakk>"
  using assms by (rel_auto, meson)

lemma tr_assign_comp [rdes]:
  fixes P :: "('s, 'e) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P" "$ref \<sharp> P"
  shows "($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S) ;; P = \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P"
  using assms by (rel_auto, meson)    

lemma RR_msubst_tt: "RR((P t)\<lbrakk>t\<rightarrow>&tt\<rbrakk>) = (RR (P t))\<lbrakk>t\<rightarrow>&tt\<rbrakk>"
  by (rel_auto)

lemma RR_msubst_ref': "RR((P r)\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk>) = (RR (P r))\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk>"
  by (rel_auto)
    
lemma msubst_tt_RR [closure]: "\<lbrakk> \<And> t. P t is RR \<rbrakk> \<Longrightarrow> (P t)\<lbrakk>t\<rightarrow>&tt\<rbrakk> is RR"
  by (simp add: Healthy_def RR_msubst_tt)
    
lemma msubst_ref'_RR [closure]: "\<lbrakk> \<And> r. P r is RR \<rbrakk> \<Longrightarrow> (P r)\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk> is RR"
  by (simp add: Healthy_def RR_msubst_ref')  

lemma conj_less_tr_RR_closed [closure]:
  assumes "P is CRR"
  shows "(P \<and> $tr <\<^sub>u $tr\<acute>) is CRR"
proof -
  have "CRR(CRR(P) \<and> $tr <\<^sub>u $tr\<acute>) = (CRR(P) \<and> $tr <\<^sub>u $tr\<acute>)"
    apply (rel_auto, blast+)
    using less_le apply fastforce+
    done
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma R4_CRR_closed [closure]: "P is CRR \<Longrightarrow> R4(P) is CRR"
  by (simp add: R4_def conj_less_tr_RR_closed)

lemma R5_CRR_closed [closure]: 
  assumes "P is CRR"
  shows "R5(P) is CRR"
proof -
  have "R5(CRR(P)) is CRR"
    by (rel_auto; blast)
  thus ?thesis
    by (simp add: assms Healthy_if)
qed

lemma conj_eq_tr_RR_closed [closure]:
  assumes "P is CRR"
  shows "(P \<and> $tr\<acute> =\<^sub>u $tr) is CRR"
proof -
  have "CRR(CRR(P) \<and> $tr\<acute> =\<^sub>u $tr) = (CRR(P) \<and> $tr\<acute> =\<^sub>u $tr)"
    by (rel_auto, blast+)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma all_ref_CRC_closed [closure]: 
  "P is CRC \<Longrightarrow> (\<forall> $ref \<bullet> P) is CRC"
  by (simp add: CRC_implies_CRR CRR_unrest_ref all_unrest)

lemma ex_ref_CRR_closed [closure]: 
  "P is CRR \<Longrightarrow> (\<exists> $ref \<bullet> P) is CRR"
  by (simp add: CRR_unrest_ref ex_unrest)

lemma ex_st'_CRR_closed [closure]: 
  "P is CRR \<Longrightarrow> (\<exists> $st\<acute> \<bullet> P) is CRR"
  by (rule CRR_intro, simp_all add: closure unrest)

lemma ex_ref'_CRR_closed [closure]: 
  "P is CRR \<Longrightarrow> (\<exists> $ref\<acute> \<bullet> P) is CRR"
  using CRR_implies_RR CRR_intro CRR_unrest_ref ex_ref'_RR_closed out_in_indep unrest_ex_diff by blast

subsection \<open> Introduction laws \<close>

text \<open> Extensionality principles for introducing refinement and equality of Circus reactive 
  relations. It is necessary only to consider a subset of the variables that are present. \<close>

lemma CRR_refine_ext:
  assumes 
    "P is CRR" "Q is CRR"
    "\<And> t s s' r'. P\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/$tr,$tr\<acute>,$st,$st\<acute>,$ref\<acute>\<rbrakk> \<sqsubseteq> Q\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/$tr,$tr\<acute>,$st,$st\<acute>,$ref\<acute>\<rbrakk>"
  shows "P \<sqsubseteq> Q"
proof -
  have "\<And> t s s' r'. (CRR P)\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/$tr,$tr\<acute>,$st,$st\<acute>,$ref\<acute>\<rbrakk> 
                    \<sqsubseteq> (CRR Q)\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/$tr,$tr\<acute>,$st,$st\<acute>,$ref\<acute>\<rbrakk>"
    using assms by (simp add: Healthy_if)
  hence "CRR P \<sqsubseteq> CRR Q"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_if assms(1) assms(2))
qed

lemma CRR_eq_ext:
  assumes 
    "P is CRR" "Q is CRR"
    "\<And> t s s' r'. P\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/$tr,$tr\<acute>,$st,$st\<acute>,$ref\<acute>\<rbrakk> = Q\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/$tr,$tr\<acute>,$st,$st\<acute>,$ref\<acute>\<rbrakk>"
  shows "P = Q"
proof -
  have "\<And> t s s' r'. (CRR P)\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/$tr,$tr\<acute>,$st,$st\<acute>,$ref\<acute>\<rbrakk> 
                    = (CRR Q)\<lbrakk>\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/$tr,$tr\<acute>,$st,$st\<acute>,$ref\<acute>\<rbrakk>"
    using assms by (simp add: Healthy_if)
  hence "CRR P = CRR Q"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_if assms(1) assms(2))
qed

lemma CRR_refine_impl_prop:
  assumes "P is CRR" "Q is CRR" 
    "\<And> t s s' r'. `Q\<lbrakk>\<guillemotleft>r'\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>/$ref\<acute>,$st,$st\<acute>,$tr,$tr\<acute>\<rbrakk>` \<Longrightarrow> `P\<lbrakk>\<guillemotleft>r'\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<guillemotright>/$ref\<acute>,$st,$st\<acute>,$tr,$tr\<acute>\<rbrakk>`"
  shows "P \<sqsubseteq> Q"
  by (rule CRR_refine_ext, simp_all add: assms closure unrest usubst)
     (rule refine_prop_intro, simp_all add: unrest unrest_all_circus_vars closure assms)

subsection \<open> UTP Theory \<close>

interpretation crf_theory: utp_theory_kleene CRF II\<^sub>c
  rewrites "P \<in> carrier crf_theory.thy_order \<longleftrightarrow> P is CRF"
  and "le rrel_theory.thy_order = (\<sqsubseteq>)"
  and "eq rrel_theory.thy_order = (=)"  
  and crf_top: "crf_theory.utp_top = false"
  and crf_bottom: "crf_theory.utp_bottom = true\<^sub>r"
proof -
  interpret utp_theory_continuous CRF
    by (unfold_locales, simp_all add: add: CRF_idem Continuous_CRF)
  show top:"utp_top = false"
    by (simp add: healthy_top, rel_auto)
  show bot:"utp_bottom = true\<^sub>r"
    by (simp add: healthy_bottom, rel_auto)
  show "utp_theory_kleene CRF II\<^sub>c"
    by (unfold_locales, simp_all add: closure rpred top)
qed (simp_all)
  
abbreviation crf_star :: "_ \<Rightarrow> _"  ("_\<^sup>\<star>\<^sup>c" [999] 999) where
"P\<^sup>\<star>\<^sup>c \<equiv> crf_theory.utp_star P"

lemma crf_star_as_rea_star:
  "P is CRF \<Longrightarrow> P\<^sup>\<star>\<^sup>c = P\<^sup>\<star>\<^sup>r ;; II\<^sub>c"
  by (simp add: crf_theory.Star_alt_def rrel_theory.Star_alt_def closure rpred unrest)

lemma crf_star_inductl: "R is CRR \<Longrightarrow> Q \<sqsubseteq> (P ;; Q) \<sqinter> R \<Longrightarrow> Q \<sqsubseteq> P\<^sup>\<star>\<^sup>c ;; R"
  by (simp add: crel_skip_left_unit crf_theory.utp_star_def upred_semiring.mult_assoc urel_ka.star_inductl)

subsection \<open> Weakest Precondition \<close>

lemma nil_least [simp]:
  "\<guillemotleft>[]\<guillemotright> \<le>\<^sub>u x = true" by rel_auto

lemma minus_nil [simp]:
  "xs - \<guillemotleft>[]\<guillemotright> = xs" by rel_auto

lemma wp_rea_circus_lemma_1:
  assumes "P is CRR" "$ref\<acute> \<sharp> P"
  shows "out\<alpha> \<sharp> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk>"
proof -
  have "out\<alpha> \<sharp> (CRR (\<exists> $ref\<acute> \<bullet> P))\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk>"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms(1) assms(2) ex_unrest)
qed

lemma wp_rea_circus_lemma_2:
  assumes "P is CRR"
  shows "in\<alpha> \<sharp> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk>"
proof -
  have "in\<alpha> \<sharp> (CRR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk>"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms ex_unrest)
qed

text \<open> The meaning of reactive weakest precondition for Circus. @{term "P wp\<^sub>r Q"} means that,
  whenever $P$ terminates in a state @{term s\<^sub>0} having done the interaction trace @{term t\<^sub>0}, which 
  is a prefix of the overall trace, then $Q$ must be satisfied. This in particular means that
  the remainder of the trace after @{term t\<^sub>0} must not be a divergent behaviour of $Q$. \<close>

lemma wp_rea_circus_form:
  assumes "P is CRR" "$ref\<acute> \<sharp> P" "Q is CRC"
  shows "(P wp\<^sub>r Q) = (\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> \<Rightarrow>\<^sub>r Q\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk>)"
proof -
  have "(P wp\<^sub>r Q) = (\<not>\<^sub>r (\<^bold>\<exists> t\<^sub>0 \<bullet> P\<lbrakk>\<guillemotleft>t\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; (\<not>\<^sub>r Q)\<lbrakk>\<guillemotleft>t\<^sub>0\<guillemotright>/$tr\<rbrakk> \<and> \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>))"
    by (simp_all add: wp_rea_def R2_tr_middle closure assms)
  also have "... = (\<not>\<^sub>r (\<^bold>\<exists> (s\<^sub>0,t\<^sub>0) \<bullet> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> ;; (\<not>\<^sub>r Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk> \<and> \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>))"
    by (rel_blast)
  also have "... = (\<not>\<^sub>r (\<^bold>\<exists> (s\<^sub>0,t\<^sub>0) \<bullet> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> \<and> (\<not>\<^sub>r Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk> \<and> \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>))"
    by (simp add: seqr_to_conj add: wp_rea_circus_lemma_1 wp_rea_circus_lemma_2 assms closure conj_assoc)
  also have "... = (\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> \<not>\<^sub>r P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> \<or> \<not>\<^sub>r (\<not>\<^sub>r Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk> \<or> \<not>\<^sub>r \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>)"
    by (rel_auto)
  also have "... = (\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> \<not>\<^sub>r P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> \<or> \<not>\<^sub>r (\<not>\<^sub>r RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk> \<or> \<not>\<^sub>r \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>)"
    by (simp add: Healthy_if assms closure)
  also have "... = (\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> \<not>\<^sub>r P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> \<or> (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk> \<or> \<not>\<^sub>r \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute>)"
    by (rel_auto)
  also have "... = (\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> \<Rightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk>)"
    by (rel_auto)
  also have "... = (\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> \<Rightarrow>\<^sub>r Q\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr\<rbrakk>)"
    by (simp add: Healthy_if assms closure)
  finally show ?thesis .
qed

lemma wp_rea_circus_form_alt:
  assumes "P is CRR" "$ref\<acute> \<sharp> P" "Q is CRC"
  shows "(P wp\<^sub>r Q) = (\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> $tr ^\<^sub>u \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                               \<Rightarrow>\<^sub>r R1(Q\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,(&tt-\<guillemotleft>t\<^sub>0\<guillemotright>)/$st,$tr,$tr\<acute>\<rbrakk>))"
proof -
  have "(P wp\<^sub>r Q) = R2(P wp\<^sub>r Q)"
    by (simp add: CRC_implies_RR CRR_implies_RR Healthy_if RR_implies_R2 assms wp_rea_R2_closed)
  also have "... = R2(\<^bold>\<forall> (s\<^sub>0,tr\<^sub>0) \<bullet> \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> \<Rightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st,$tr\<rbrakk>)"
    by (simp add: wp_rea_circus_form assms closure Healthy_if)
  also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> (\<^bold>\<forall> (s\<^sub>0,tr\<^sub>0) \<bullet> \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                                        \<Rightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$st,$tr,$tr\<acute>\<rbrakk>) 
                                         \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>)"
    by (simp add: R2_form, rel_auto)
  also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> (\<^bold>\<forall> (s\<^sub>0,tr\<^sub>0) \<bullet> \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                                        \<Rightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tt\<^sub>0-tr\<^sub>0\<guillemotright>/$st,$tr,$tr\<acute>\<rbrakk>) 
                                         \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>)"
    by (rel_auto)
  also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> (\<^bold>\<forall> (s\<^sub>0,tr\<^sub>0) \<bullet> $tr ^\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                                        \<Rightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,(&tt-\<guillemotleft>tr\<^sub>0\<guillemotright>)/$st,$tr,$tr\<acute>\<rbrakk>) 
                                         \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>)"
    by (rel_auto, (metis list_concat_minus_list_concat)+)
  also have "... = (\<^bold>\<forall> (s\<^sub>0,tr\<^sub>0) \<bullet> $tr ^\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                                        \<Rightarrow>\<^sub>r R1((RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,(&tt-\<guillemotleft>tr\<^sub>0\<guillemotright>)/$st,$tr,$tr\<acute>\<rbrakk>))"
    by (rel_auto, blast+)
  also have "... = (\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> $tr ^\<^sub>u \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                               \<Rightarrow>\<^sub>r R1(Q\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,(&tt-\<guillemotleft>t\<^sub>0\<guillemotright>)/$st,$tr,$tr\<acute>\<rbrakk>))"
    by (simp add: Healthy_if assms closure)
  finally show ?thesis .
qed

lemma wp_rea_circus_form_alt:
  assumes "P is CRR" "$ref\<acute> \<sharp> P" "Q is CRC"
  shows "(P wp\<^sub>r Q) = (\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> $tr ^\<^sub>u \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                               \<Rightarrow>\<^sub>r R1(Q\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,(&tt-\<guillemotleft>t\<^sub>0\<guillemotright>)/$st,$tr,$tr\<acute>\<rbrakk>))"
  oops

subsection \<open> Trace Substitution \<close>

definition trace_subst ("_\<lbrakk>_\<rbrakk>\<^sub>t" [999,0] 999) 
where [upred_defs]: "P\<lbrakk>v\<rbrakk>\<^sub>t = (P\<lbrakk>(&tt-\<lceil>v\<rceil>\<^sub>S\<^sub><)/&tt\<rbrakk> \<and> $tr + \<lceil>v\<rceil>\<^sub>S\<^sub>< \<le>\<^sub>u $tr\<acute>)"

lemma unrest_trace_subst [unrest]:
  "\<lbrakk> mwb_lens x; x \<bowtie> ($tr)\<^sub>v; x \<bowtie> ($tr\<acute>)\<^sub>v; x \<bowtie> ($st)\<^sub>v; x \<sharp> P \<rbrakk> \<Longrightarrow> x \<sharp> P\<lbrakk>v\<rbrakk>\<^sub>t"
  by (simp add: trace_subst_def lens_indep_sym unrest)
  
lemma trace_subst_RR_closed [closure]:
  assumes "P is RR"
  shows "P\<lbrakk>v\<rbrakk>\<^sub>t is RR"
proof -
  have "(RR P)\<lbrakk>v\<rbrakk>\<^sub>t is RR"
    apply (rel_auto)
    apply (metis diff_add_cancel_left' trace_class.add_left_mono)
    apply (metis le_add minus_cancel_le trace_class.add_diff_cancel_left)
    using le_add order_trans apply blast
  done
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma trace_subst_CRR_closed [closure]:
  assumes "P is CRR"
  shows "P\<lbrakk>v\<rbrakk>\<^sub>t is CRR"
  by (rule CRR_intro, simp_all add: closure assms unrest)

lemma tsubst_nil [usubst]: 
  assumes "P is CRR"
  shows "P\<lbrakk>\<guillemotleft>[]\<guillemotright>\<rbrakk>\<^sub>t = P"
proof -
  have "(CRR P)\<lbrakk>\<guillemotleft>[]\<guillemotright>\<rbrakk>\<^sub>t = CRR P"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma tsubst_false [usubst]: "false\<lbrakk>y\<rbrakk>\<^sub>t = false"
  by rel_auto

lemma cond_rea_tt_subst [usubst]:
  "(P \<triangleleft> b \<triangleright>\<^sub>R Q)\<lbrakk>v\<rbrakk>\<^sub>t = (P\<lbrakk>v\<rbrakk>\<^sub>t \<triangleleft> b \<triangleright>\<^sub>R Q\<lbrakk>v\<rbrakk>\<^sub>t)"
  by (rel_auto)
        
lemma tsubst_conj [usubst]: "(P \<and> Q)\<lbrakk>v\<rbrakk>\<^sub>t = (P\<lbrakk>v\<rbrakk>\<^sub>t \<and> Q\<lbrakk>v\<rbrakk>\<^sub>t)"
  by (rel_auto)

lemma tsubst_disj [usubst]: "(P \<or> Q)\<lbrakk>v\<rbrakk>\<^sub>t = (P\<lbrakk>v\<rbrakk>\<^sub>t \<or> Q\<lbrakk>v\<rbrakk>\<^sub>t)"
  by (rel_auto)
    
lemma rea_subst_R1_closed [closure]: "P\<lbrakk>v\<rbrakk>\<^sub>t is R1"
  apply (rel_auto) using le_add order.trans by blast
  
lemma tsubst_UINF_ind [usubst]: "(\<Sqinter> i \<bullet> P(i))\<lbrakk>v\<rbrakk>\<^sub>t = (\<Sqinter> i \<bullet> (P(i))\<lbrakk>v\<rbrakk>\<^sub>t)"
  by (rel_auto)

subsection \<open> Initial Interaction \<close>

definition rea_init :: "'s upred \<Rightarrow> ('t::trace, 's) uexpr \<Rightarrow> ('s, 't, '\<alpha>, '\<beta>) rel_rsp" ("\<I>'(_,_')") where
[upred_defs]: "\<I>(s,t) = (\<lceil>s\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r \<not>\<^sub>r $tr + \<lceil>t\<rceil>\<^sub>S\<^sub>< \<le>\<^sub>u $tr\<acute>)"
  
lemma usubst_rea_init' [usubst]:
  "\<sigma> \<dagger>\<^sub>S \<I>(s,t) = \<I>(\<sigma>\<dagger>s,\<sigma>\<dagger>t)"
  by (rel_auto)

lemma unrest_rea_init [unrest]:
  "\<lbrakk> x \<bowtie> ($tr)\<^sub>v; x \<bowtie> ($tr\<acute>)\<^sub>v; x \<bowtie> ($st)\<^sub>v \<rbrakk> \<Longrightarrow> x \<sharp> \<I>(s,t)"
  by (simp add: rea_init_def unrest lens_indep_sym)

lemma rea_init_R1 [closure]: "\<I>(s,t) is R1"
  by (rel_auto)

lemma rea_init_R2c [closure]: "\<I>(s,t) is R2c"
  apply (rel_auto)
  apply (metis le_add minus_cancel_le trace_class.add_diff_cancel_left)
  apply (metis diff_add_cancel_left' trace_class.add_left_mono)
done

lemma rea_init_R2 [closure]: "\<I>(s,t) is R2"
  by (metis Healthy_def R1_R2c_is_R2 rea_init_R1 rea_init_R2c)
 
lemma csp_init_RR [closure]: "\<I>(s,t) is RR"
  apply (rel_auto)
  apply (metis le_add minus_cancel_le trace_class.add_diff_cancel_left)
  apply (metis diff_add_cancel_left' trace_class.add_left_mono)
done

lemma csp_init_CRR [closure]: "\<I>(s,t) is CRR"
  by (rule CRR_intro, simp_all add: unrest closure)

lemma rea_init_RC [closure]: "\<I>(s,t) is CRC"
  apply (rel_auto) by fastforce

lemma rea_init_false [rpred]: "\<I>(false, t) = true\<^sub>r"
  by (rel_auto)

lemma rea_init_nil [rpred]: "\<I>(s,\<guillemotleft>[]\<guillemotright>) = [\<not> s]\<^sub>S\<^sub><"
  by (rel_auto)

lemma rea_not_init [rpred]: "(\<not>\<^sub>r \<I>(P,\<guillemotleft>[]\<guillemotright>)) = \<I>(\<not>P,\<guillemotleft>[]\<guillemotright>)"
  by (rel_auto)
       
lemma rea_init_conj [rpred]:
  "(\<I>(s\<^sub>1,t) \<and> \<I>(s\<^sub>2,t)) = \<I>(s\<^sub>1\<or>s\<^sub>2,t)"
  by (rel_auto)
    
lemma rea_init_disj_same [rpred]: "(\<I>(s\<^sub>1,t) \<or> \<I>(s\<^sub>2,t)) = \<I>(s\<^sub>1 \<and> s\<^sub>2, t)"
  by (rel_auto)

(*
lemma R4_csp_init [rpred]: "R4(\<I>(s,bop Cons x xs)) = \<I>(s,bop Cons x xs)"
  using less_list_def apply (rel_auto)

lemma R5_csp_init [rpred]: "R5(\<I>(s,bop Cons x xs)) = false"
  by (rel_auto)

lemma R4_trace_subst [rpred]:
  "R4 (P\<lbrakk>bop Cons x xs\<rbrakk>\<^sub>t) = P\<lbrakk>bop Cons x xs\<rbrakk>\<^sub>t"
  using le_imp_less_or_eq by (rel_blast)

lemma R5_trace_subst [rpred]:
  "R5 (P\<lbrakk>bop Cons x xs\<rbrakk>\<^sub>t) = false"
  by (rel_auto)
*)

subsection \<open> Enabled Events \<close>

definition csp_enable :: "'s upred \<Rightarrow> ('e list, 's) uexpr \<Rightarrow> ('e set, 's) uexpr \<Rightarrow> ('s, 'e) action" ("\<E>'(_,_, _')") where
[upred_defs]: "\<E>(s,t,E) = (\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub>< \<and> (\<^bold>\<forall> e\<in>\<lceil>E\<rceil>\<^sub>S\<^sub>< \<bullet> \<guillemotleft>e\<guillemotright> \<notin>\<^sub>u $ref\<acute>))"

text \<open> Predicate @{term "\<E>(s, t, E)"} states that, if the initial state satisfies predicate @{term s},
  then @{term t} is a possible (failure) trace, such that the events in the set @{term E} are enabled
  after the given interaction. \<close>

lemma csp_enable_R1_closed [closure]: "\<E>(s,t,E) is R1"
  by (rel_auto)

lemma csp_enable_R2_closed [closure]: "\<E>(s,t,E) is R2c"
  by (rel_auto)
    
lemma csp_enable_RR [closure]: "\<E>(s,t,E) is CRR"
  by (rel_auto)

lemma tsubst_csp_enable [usubst]: "\<E>(s,t\<^sub>2,e)\<lbrakk>t\<^sub>1\<rbrakk>\<^sub>t = \<E>(s,t\<^sub>1^\<^sub>ut\<^sub>2,e)"
  apply (rel_auto)
  apply (metis append.assoc less_eq_list_def prefix_concat_minus)
  apply (simp add: list_concat_minus_list_concat)
done

lemma csp_enable_unrests [unrest]:
  "\<lbrakk> x \<bowtie> ($tr)\<^sub>v; x \<bowtie> ($tr\<acute>)\<^sub>v; x \<bowtie> ($st)\<^sub>v; x \<bowtie> ($ref\<acute>)\<^sub>v \<rbrakk> \<Longrightarrow> x \<sharp> \<E>(s,t,e)"
  by (simp add: csp_enable_def R1_def lens_indep_sym unrest)

lemma st_unrest_csp_enable [unrest]: "\<lbrakk> &\<^bold>v \<sharp> s; &\<^bold>v \<sharp> t; &\<^bold>v \<sharp> E \<rbrakk> \<Longrightarrow> $st \<sharp> \<E>(s, t, E)" 
  by (simp add: csp_enable_def unrest)

lemma csp_enable_tr'_eq_tr [rpred]: 
  "\<E>(s,\<guillemotleft>[]\<guillemotright>,r) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> false = \<E>(s,\<guillemotleft>[]\<guillemotright>,r)"
  by (rel_auto)
    
lemma csp_enable_st_pred [rpred]: 
  "([s\<^sub>1]\<^sub>S\<^sub>< \<and> \<E>(s\<^sub>2,t,E)) = \<E>(s\<^sub>1 \<and> s\<^sub>2,t,E)"
  by (rel_auto)

lemma csp_enable_conj [rpred]:
  "(\<E>(s, t, E\<^sub>1) \<and> \<E>(s, t, E\<^sub>2)) = \<E>(s, t, E\<^sub>1 \<union>\<^sub>u E\<^sub>2)"
  by (rel_auto)

lemma csp_enable_cond [rpred]:
  "\<E>(s\<^sub>1, t\<^sub>1, E\<^sub>1) \<triangleleft> b \<triangleright>\<^sub>R \<E>(s\<^sub>2, t\<^sub>2, E\<^sub>2) = \<E>(s\<^sub>1 \<triangleleft> b \<triangleright> s\<^sub>2, t\<^sub>1 \<triangleleft> b \<triangleright> t\<^sub>2, E\<^sub>1 \<triangleleft> b \<triangleright> E\<^sub>2)"
  by (rel_auto)

lemma csp_enable_rea_assm [rpred]: 
  "[b]\<^sup>\<top>\<^sub>r ;; \<E>(s,t,E) = \<E>(b\<and>s,t,E)"
  by (rel_auto)

lemma csp_enable_tr_empty: "\<E>(true,\<guillemotleft>[]\<guillemotright>,{v}\<^sub>u) = ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>v\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>)"
  by (rel_auto)

lemma csp_enable_nothing: "\<E>(true,\<guillemotleft>[]\<guillemotright>, {}\<^sub>u) = ($tr\<acute> =\<^sub>u $tr)"
  by (rel_auto)

lemma msubst_nil_csp_enable [usubst]: 
  "\<E>(s(x),t(x),E(x))\<lbrakk>x\<rightarrow>\<guillemotleft>[]\<guillemotright>\<rbrakk> = \<E>(s(x)\<lbrakk>x\<rightarrow>\<guillemotleft>[]\<guillemotright>\<rbrakk>,t(x)\<lbrakk>x\<rightarrow>\<guillemotleft>[]\<guillemotright>\<rbrakk>,E(x)\<lbrakk>x\<rightarrow>\<guillemotleft>[]\<guillemotright>\<rbrakk>)"
  by (pred_auto)

lemma msubst_csp_enable [usubst]: 
  "\<E>(s(x),t(x),E(x))\<lbrakk>x\<rightarrow>\<lceil>v\<rceil>\<^sub>S\<^sub>\<leftarrow>\<rbrakk> = \<E>(s(x)\<lbrakk>x\<rightarrow>v\<rbrakk>,t(x)\<lbrakk>x\<rightarrow>v\<rbrakk>,E(x)\<lbrakk>x\<rightarrow>v\<rbrakk>)"
  by (rel_auto)

lemma csp_enable_false [rpred]: "\<E>(false,t,E) = false"
  by (rel_auto)

lemma conj_csp_enable [rpred]: "(\<E>(b\<^sub>1, t, E\<^sub>1) \<and> \<E>(b\<^sub>2, t, E\<^sub>2)) = \<E>(b\<^sub>1 \<and> b\<^sub>2, t, E\<^sub>1 \<union>\<^sub>u E\<^sub>2)"
  by (rel_auto)

lemma refine_csp_enable: "\<E>(b\<^sub>1, t, E\<^sub>1) \<sqsubseteq> \<E>(b\<^sub>2, t, E\<^sub>2) \<longleftrightarrow> (`b\<^sub>2 \<Rightarrow> b\<^sub>1 \<and> E\<^sub>1 \<subseteq>\<^sub>u E\<^sub>2`)"
  by (rel_blast)

lemma USUP_csp_enable [rpred]:
  "(\<Squnion> x \<bullet> \<E>(s, t, A(x))) = \<E>(s, t, (\<Or> x \<bullet> A(x)))"
  by (rel_auto)

lemma R4_csp_enable_nil [rpred]:
  "R4(\<E>(s, \<guillemotleft>[]\<guillemotright>, E)) = false"
  by (rel_auto)

lemma R5_csp_enable_nil [rpred]:
  "R5(\<E>(s, \<guillemotleft>[]\<guillemotright>, E)) = \<E>(s, \<guillemotleft>[]\<guillemotright>, E)"
  by (rel_auto)

lemma R4_csp_enable_Cons [rpred]: 
  "R4(\<E>(s,bop Cons x xs, E)) = \<E>(s,bop Cons x xs, E)"
  by (rel_auto, simp add: Prefix_Order.strict_prefixI')

lemma R5_csp_enable_Cons [rpred]: 
  "R5(\<E>(s,bop Cons x xs, E)) = false"
  by (rel_auto)

lemma rel_aext_csp_enable [alpha]: 
  "vwb_lens a \<Longrightarrow> \<E>(s, t, E) \<oplus>\<^sub>r map_st\<^sub>L[a] = \<E>(s \<oplus>\<^sub>p a, t \<oplus>\<^sub>p a, E \<oplus>\<^sub>p a)"
  by (rel_auto)

subsection \<open> Completed Trace Interaction \<close>

definition csp_do :: "'s upred \<Rightarrow> ('s usubst) \<Rightarrow> ('e list, 's) uexpr \<Rightarrow> ('s, 'e) action" ("\<Phi>'(_,_,_')") where
[upred_defs]: "\<Phi>(s,\<sigma>,t) = (\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S)"

lemma csp_do_eq_intro:
  assumes "s\<^sub>1 = s\<^sub>2" "\<sigma>\<^sub>1 = \<sigma>\<^sub>2" "t\<^sub>1 = t\<^sub>2"
  shows "\<Phi>(s\<^sub>1, \<sigma>\<^sub>1, t\<^sub>1) = \<Phi>(s\<^sub>2, \<sigma>\<^sub>2, t\<^sub>2)"
  by (simp add: assms)

text \<open> Predicate @{term "\<Phi>(s,\<sigma>,t)"} states that if the initial state satisfies @{term s}, and
  the trace @{term t} is performed, then afterwards the state update @{term \<sigma>} is executed. \<close>

lemma unrest_csp_do [unrest]: 
  "\<lbrakk> x \<bowtie> ($tr)\<^sub>v; x \<bowtie> ($tr\<acute>)\<^sub>v; x \<bowtie> ($st)\<^sub>v; x \<bowtie> ($st\<acute>)\<^sub>v \<rbrakk> \<Longrightarrow> x \<sharp> \<Phi>(s,\<sigma>,t)"
  by (simp_all add: csp_do_def alpha_in_var alpha_out_var prod_as_plus unrest lens_indep_sym)
    
lemma csp_do_CRF [closure]: "\<Phi>(s,\<sigma>,t) is CRF"
  by (rel_auto)

lemma csp_do_R4_closed [closure]:
  "\<Phi>(b,\<sigma>,bop Cons x xs) is R4"
  by (rel_auto, simp add: Prefix_Order.strict_prefixI')

lemma st_pred_conj_csp_do [rpred]: 
  "([b]\<^sub>S\<^sub>< \<and> \<Phi>(s,\<sigma>,t)) = \<Phi>(b \<and> s,\<sigma>,t)"
  by (rel_auto)

lemma trea_subst_csp_do [usubst]:
  "(\<Phi>(s,\<sigma>,t\<^sub>2))\<lbrakk>t\<^sub>1\<rbrakk>\<^sub>t = \<Phi>(s,\<sigma>,t\<^sub>1 ^\<^sub>u t\<^sub>2)"
  apply (rel_auto)
  apply (metis append.assoc less_eq_list_def prefix_concat_minus)
  apply (simp add: list_concat_minus_list_concat)
done

lemma st_subst_csp_do [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> \<Phi>(s,\<rho>,t) = \<Phi>(\<sigma> \<dagger> s,\<rho> \<circ>\<^sub>s \<sigma>,\<sigma> \<dagger> t)"
  by (rel_auto)

lemma csp_do_nothing: "\<Phi>(true,id\<^sub>s,\<guillemotleft>[]\<guillemotright>) = II\<^sub>c"
  by (rel_auto)

lemma csp_do_nothing_0: "\<Phi>(true,id\<^sub>s,0) = II\<^sub>c"
  by (rel_auto)

lemma csp_do_false [rpred]: "\<Phi>(false,s,t) = false"
  by (rel_auto)
            
lemma subst_state_csp_enable [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> \<E>(s,t\<^sub>2,e) = \<E>(\<sigma> \<dagger> s, \<sigma> \<dagger> t\<^sub>2, \<sigma> \<dagger> e)"
  by (rel_auto)
    
lemma csp_do_assign_enable [rpred]: 
  "\<Phi>(s\<^sub>1,\<sigma>,t\<^sub>1) ;; \<E>(s\<^sub>2,t\<^sub>2,e) = \<E>(s\<^sub>1 \<and> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1^\<^sub>u(\<sigma> \<dagger> t\<^sub>2), (\<sigma> \<dagger> e))"
  by (rel_auto)

lemma csp_do_assign_do [rpred]: 
  "\<Phi>(s\<^sub>1,\<sigma>,t\<^sub>1) ;; \<Phi>(s\<^sub>2,\<rho>,t\<^sub>2) = \<Phi>(s\<^sub>1 \<and> (\<sigma> \<dagger> s\<^sub>2), \<rho> \<circ>\<^sub>s \<sigma>, t\<^sub>1^\<^sub>u(\<sigma> \<dagger> t\<^sub>2))"
  by (rel_auto)

lemma csp_do_cond [rpred]:
  "\<Phi>(s\<^sub>1,\<sigma>,t\<^sub>1) \<triangleleft> b \<triangleright>\<^sub>R \<Phi>(s\<^sub>2,\<rho>,t\<^sub>2) = \<Phi>(s\<^sub>1 \<triangleleft> b \<triangleright> s\<^sub>2, \<sigma> \<triangleleft> b \<triangleright> \<rho>, t\<^sub>1 \<triangleleft> b \<triangleright> t\<^sub>2)"
  by (rel_auto)

lemma rea_assm_csp_do [rpred]: 
  "[b]\<^sup>\<top>\<^sub>r ;; \<Phi>(s,\<sigma>,t) = \<Phi>(b\<and>s,\<sigma>,t)"
  by (rel_auto)

lemma csp_do_comp:
  assumes "P is CRR"
  shows "\<Phi>(s,\<sigma>,t) ;; P = ([s]\<^sub>S\<^sub>< \<and> (\<sigma> \<dagger>\<^sub>S P)\<lbrakk>t\<rbrakk>\<^sub>t)"
proof -
  have "\<Phi>(s,\<sigma>,t) ;; (CRR P) = ([s]\<^sub>S\<^sub>< \<and> ((\<sigma> \<dagger>\<^sub>S CRR P))\<lbrakk>t\<rbrakk>\<^sub>t)"
    by (rel_auto; blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma wp_rea_csp_do_lemma:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P" "$ref \<sharp> P"
  shows "(\<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub><) ;; P = (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P)\<lbrakk>$tr ^\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub></$tr\<rbrakk>"
  using assms by (rel_auto, meson)

text \<open> This operator sets an upper bound on the permissible traces, when starting from a particular state \<close>

lemma wp_rea_csp_do [wp]:
  "\<Phi>(s\<^sub>1,\<sigma>,t\<^sub>1) wp\<^sub>r \<I>(s\<^sub>2,t\<^sub>2) = \<I>(s\<^sub>1 \<and> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1 ^\<^sub>u \<sigma> \<dagger> t\<^sub>2)"
  by (rel_auto)

lemma wp_rea_csp_do_false' [wp]:
  "\<Phi>(s\<^sub>1,\<sigma>,t\<^sub>1) wp\<^sub>r false = \<I>(s\<^sub>1, t\<^sub>1)"
  by (rel_auto)

lemma st_pred_impl_csp_do_wp [rpred]:
  "([s\<^sub>1]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r \<Phi>(s\<^sub>2,\<sigma>,t) wp\<^sub>r P) = \<Phi>(s\<^sub>1\<and>s\<^sub>2,\<sigma>,t) wp\<^sub>r P"
  by (rel_auto)

lemma csp_do_seq_USUP_distl [rpred]:
  assumes "\<And> i. i \<in> A \<Longrightarrow> P(i) is CRR" "A \<noteq> {}"
  shows "\<Phi>(s,\<sigma>,t) ;; (\<And> i\<in>A \<bullet> P(i)) = (\<And> i\<in>A \<bullet> \<Phi>(s,\<sigma>,t) ;; P(i))"
proof -
  from assms(2) have "\<Phi>(s,\<sigma>,t) ;; (\<Squnion> i\<in>A \<bullet> CRR(P(i))) = (\<Squnion> i\<in>A \<bullet> \<Phi>(s,\<sigma>,t) ;; CRR(P(i)))"
    by (rel_blast)    
  thus ?thesis
    by (simp cong: USUP_cong add: assms(1) Healthy_if)
qed

lemma csp_do_seq_conj_distl:
  assumes "P is CRR" "Q is CRR"
  shows "\<Phi>(s,\<sigma>,t) ;; (P \<and> Q) = (\<Phi>(s,\<sigma>,t) ;; P \<and> \<Phi>(s,\<sigma>,t) ;; Q)"
proof -
  have "\<Phi>(s,\<sigma>,t) ;; (CRR(P) \<and> CRR(Q)) = ((\<Phi>(s,\<sigma>,t) ;; (CRR P)) \<and> (\<Phi>(s,\<sigma>,t) ;; (CRR Q)))"
    by (rel_blast)
  thus ?thesis
    by (simp add: assms Healthy_if)
qed

lemma csp_do_power_Suc [rpred]:
  "\<Phi>(true, id\<^sub>s, t) \<^bold>^ (Suc i) = \<Phi>(true, id\<^sub>s, iter[Suc i](t))"
  by (induct i, (rel_auto)+)

lemma csp_power_do_comp [rpred]:
  assumes "P is CRR"
  shows "\<Phi>(true, id\<^sub>s, t) \<^bold>^ i ;; P = \<Phi>(true, id\<^sub>s, iter[i](t)) ;; P"
  apply (cases i)
   apply (simp_all add: csp_do_comp rpred usubst assms closure)
  done

lemma csp_do_id [rpred]:
  "P is CRR \<Longrightarrow> \<Phi>(b,id\<^sub>s,\<guillemotleft>[]\<guillemotright>) ;; P = ([b]\<^sub>S\<^sub>< \<and> P)"
  by (simp add: csp_do_comp usubst)

lemma csp_do_id_wp [wp]: 
  "P is CRR \<Longrightarrow> \<Phi>(b,id\<^sub>s,\<guillemotleft>[]\<guillemotright>) wp\<^sub>r P = ([b]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P)"
  by (metis (no_types, lifting) CRR_implies_RR RR_implies_R1 csp_do_id rea_impl_conj rea_impl_false rea_not_CRR_closed rea_not_not wp_rea_def)

lemma wp_rea_csp_do_st_pre [wp]: "\<Phi>(s\<^sub>1,\<sigma>,t\<^sub>1) wp\<^sub>r [s\<^sub>2]\<^sub>S\<^sub>< = \<I>(s\<^sub>1 \<and> \<not> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1)"
  by (rel_auto)

lemma wp_rea_csp_do_skip [wp]:
  fixes Q :: "('\<sigma>, '\<phi>) action"
  assumes "P is CRR"
  shows "\<Phi>(s,\<sigma>,t) wp\<^sub>r P = (\<I>(s,t) \<and> (\<sigma> \<dagger>\<^sub>S P)\<lbrakk>t\<rbrakk>\<^sub>t)"
  apply (simp add: wp_rea_def)
  apply (subst csp_do_comp)
  apply (simp_all add: closure assms usubst)
  oops

lemma msubst_csp_do [usubst]: 
  "\<Phi>(s(x),\<sigma>,t(x))\<lbrakk>x\<rightarrow>\<lceil>v\<rceil>\<^sub>S\<^sub>\<leftarrow>\<rbrakk> = \<Phi>(s(x)\<lbrakk>x\<rightarrow>v\<rbrakk>,\<sigma>,t(x)\<lbrakk>x\<rightarrow>v\<rbrakk>)"
  by (rel_auto)

lemma rea_frame_ext_csp_do [frame]: 
  "vwb_lens a \<Longrightarrow> a:[\<Phi>(s,\<sigma>,t)]\<^sub>r\<^sup>+ = \<Phi>(s \<oplus>\<^sub>p a,\<sigma> \<oplus>\<^sub>s a ,t \<oplus>\<^sub>p a)"
  by (rel_auto)

lemma R5_csp_do_nil [rpred]: "R5(\<Phi>(s,\<sigma>,\<guillemotleft>[]\<guillemotright>)) = \<Phi>(s,\<sigma>,\<guillemotleft>[]\<guillemotright>)"
  by (rel_auto)

lemma R5_csp_do_Cons [rpred]: "R5(\<Phi>(s,\<sigma>,x #\<^sub>u xs)) = false"
  by (rel_auto)

text \<open> Iterated do relations \<close>

fun titr :: "nat \<Rightarrow> 's usubst \<Rightarrow> ('a list, 's) uexpr \<Rightarrow> ('a list, 's) uexpr" where
"titr 0 \<sigma> t = 0" |
"titr (Suc n) \<sigma> t = (titr n \<sigma> t) + (\<sigma> ^\<^sub>s n) \<dagger> t"

lemma titr_as_list_sum: "titr n \<sigma> t = list_sum (map (\<lambda> i. (\<sigma> ^\<^sub>s i) \<dagger> t) [0..<n])"
  apply (induct n)
   apply (auto simp add: usubst fold_plus_sum_list_rev foldr_conv_fold)
  done
        
lemma titr_as_foldr: "titr n \<sigma> t = foldr (\<lambda> i e. (\<sigma> ^\<^sub>s i) \<dagger> t + e) [0..<n] 0"
  by (simp add: titr_as_list_sum foldr_map comp_def)

lemma list_sum_uexpr_rep_eq: "\<lbrakk>list_sum xs\<rbrakk>\<^sub>e s = list_sum (map (\<lambda> e. \<lbrakk>e\<rbrakk>\<^sub>e s) xs)"
  apply (induct xs)
   apply (simp_all)
   apply (pred_simp+)
  done

lemma titr_rep_eq: "\<lbrakk>titr n \<sigma> t\<rbrakk>\<^sub>e s = foldr (@) (map (\<lambda>x. \<lbrakk>t\<rbrakk>\<^sub>e ((\<lbrakk>\<sigma>\<rbrakk>\<^sub>e ^^ x) s)) [0..<n]) []"
  by (simp add: titr_as_list_sum list_sum_uexpr_rep_eq comp_def, rel_simp)

update_uexpr_rep_eq_thms

lemma titr_lemma:
  "t + (\<sigma> \<dagger> titr n \<sigma> t) + (\<sigma> ^\<^sub>s n \<circ>\<^sub>s \<sigma>) \<dagger> t = (titr n \<sigma> t + (\<sigma> ^\<^sub>s n) \<dagger> t) + (\<sigma> \<circ>\<^sub>s \<sigma> ^\<^sub>s n) \<dagger> t"
  by (induct n, simp_all add: usubst add.assoc, metis subst_monoid.power_Suc subst_monoid.power_Suc2)

lemma csp_do_power [rpred]:
  "\<Phi>(s, \<sigma>, t)\<^bold>^(Suc n) = \<Phi>(\<And> i\<in>{0..n} \<bullet> (\<sigma>^\<^sub>si) \<dagger> s, \<sigma>^\<^sub>sSuc n, titr (Suc n) \<sigma> t)"
  apply (induct n)
   apply (rel_auto)
  apply (simp add: power.power.power_Suc rpred usubst)
  apply (thin_tac "_")
  apply (rule csp_do_eq_intro)
    apply (rel_auto)
     apply (case_tac "x=0")
  apply (simp_all add: titr_lemma)
  apply (metis Suc_le_mono funpow_simps_right(2) gr0_implies_Suc o_def)
  apply force
  apply (metis Suc_leI funpow_simps_right(2) less_Suc_eq_le o_apply)
  apply (metis subst_monoid.power_Suc subst_monoid.power_Suc2)
  apply (metis add.assoc plus_list_def plus_uexpr_def titr_lemma)
  done

lemma csp_do_rea_star [rpred]:
  "\<Phi>(s, \<sigma>, t)\<^sup>\<star>\<^sup>r = II\<^sub>r \<sqinter> (\<Sqinter> n \<bullet> \<Phi>(\<And> i\<in>{0..n} \<bullet> (\<sigma>^\<^sub>si) \<dagger> s, \<sigma>^\<^sub>sSuc n, titr (Suc n) \<sigma> t))"
  by (simp add: rrel_theory.Star_alt_def closure uplus_power_def rpred)

lemma csp_do_csp_star [rpred]:
  "\<Phi>(s, \<sigma>, t)\<^sup>\<star>\<^sup>c = (\<Sqinter> n \<bullet> \<Phi>(\<Squnion> i \<in> {0..<n} \<bullet> (\<sigma> ^\<^sub>s i) \<dagger> s,\<sigma> ^\<^sub>s n,titr n \<sigma> t))"
  (is "?lhs = (\<Sqinter> n \<bullet> ?G(n))")
proof -
  have "?lhs = II\<^sub>c \<sqinter> (\<Sqinter> n \<bullet> \<Phi>(\<And> i\<in>{0..n} \<bullet> (\<sigma>^\<^sub>si) \<dagger> s, \<sigma>^\<^sub>sSuc n, titr (Suc n) \<sigma> t))"
    (is "_ = II\<^sub>c \<sqinter> (\<Sqinter> n \<bullet> ?F(n))")
    by (simp add: crf_theory.Star_alt_def closure uplus_power_def rpred)
  also have "... = II\<^sub>c \<sqinter> (\<Sqinter> n\<in>{1..} \<bullet> ?F(n - 1))"
    by (simp add: UINF_atLeast_Suc)
  also have "... = II\<^sub>c \<sqinter> (\<Sqinter> n \<in> {1..} \<bullet> \<Phi>(\<Squnion> i \<in> {0..<n} \<bullet> (\<sigma> ^\<^sub>s i) \<dagger> s,\<sigma> ^\<^sub>s n,titr n \<sigma> t))"
  proof -
    have "(\<Sqinter> n\<in>{1..} \<bullet> ?F(n - 1)) = (\<Sqinter> n \<in> {1..} \<bullet> ?G(n))"
      by (rule UINF_cong, simp, metis (no_types, lifting) Suc_diff_le atLeastLessThanSuc_atLeastAtMost cancel_comm_monoid_add_class.diff_zero diff_Suc_Suc)
    thus ?thesis by simp
  qed
  also have "... = ?G(0) \<sqinter> (\<Sqinter> n \<in> {1..} \<bullet> ?G(n))"
    by (simp add: usubst csp_do_nothing_0)
  also have "... = (\<Sqinter> n \<in> insert 0 {1..} \<bullet> ?G(n))"
    by (simp)
  also have "... = (\<Sqinter> n \<bullet> ?G(n))"
  proof -                                     
    have "insert (0::nat) {1..} = {0..}" by auto
    thus ?thesis
      by simp
  qed
  finally show ?thesis .
qed

subsection \<open> Assumptions \<close>

abbreviation crf_assume :: "'s upred \<Rightarrow> ('s, 'e) action" ("[_]\<^sub>c") where
"[b]\<^sub>c \<equiv> \<Phi>(b, id\<^sub>s, \<guillemotleft>[]\<guillemotright>)"

lemma crf_assume_true [rpred]: "P is CRR \<Longrightarrow> [true]\<^sub>c ;; P = P"
  by (simp add: crel_skip_left_unit csp_do_nothing)

subsection \<open> Downward closure of refusals \<close>

text \<open> We define downward closure of the pericondition by the following healthiness condition \<close>

definition CDC :: "('s, 'e) action \<Rightarrow> ('s, 'e) action" where
[upred_defs]: "CDC(P) = (\<^bold>\<exists> ref\<^sub>0 \<bullet> P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<acute>\<rbrakk> \<and> $ref\<acute> \<subseteq>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>)"

lemma CDC_idem: "CDC(CDC(P)) = CDC(P)"
  by (rel_auto)

lemma CDC_Continuous [closure]: "Continuous CDC"
  by (rel_auto)

lemma CDC_RR_commute: "CDC(RR(P)) = RR(CDC(P))"
  by (rel_blast)

lemma CDC_RR_closed [closure]: "P is RR \<Longrightarrow> CDC(P) is RR"
  by (metis CDC_RR_commute Healthy_def)

lemma CDC_CRR_commute: "CDC (CRR P) = CRR (CDC P)"
  by (rel_blast)

lemma CDC_CRR_closed [closure]:
  assumes "P is CRR"
  shows "CDC(P) is CRR"
  by (rule CRR_intro, simp add: CDC_def unrest assms closure, simp add: unrest assms closure)

lemma CDC_unrest [unrest]: "\<lbrakk> vwb_lens x; ($ref\<acute>)\<^sub>v \<bowtie> x; x \<sharp> P \<rbrakk> \<Longrightarrow> x \<sharp> CDC(P)"
  by (simp add: CDC_def unrest usubst lens_indep_sym)

lemma CDC_R4_commute: "CDC(R4(P)) = R4(CDC(P))"
  by (rel_auto)

lemma R4_CDC_closed [closure]: "P is CDC \<Longrightarrow> R4(P) is CDC"
  by (simp add: CDC_R4_commute Healthy_def)

lemma CDC_R5_commute: "CDC(R5(P)) = R5(CDC(P))"
  by (rel_auto)

lemma R5_CDC_closed [closure]: "P is CDC \<Longrightarrow> R5(P) is CDC"
  by (simp add: CDC_R5_commute Healthy_def)

lemma rea_true_CDC [closure]: "true\<^sub>r is CDC"
  by (rel_auto)

lemma false_CDC [closure]: "false is CDC"
  by (rel_auto)

lemma CDC_UINF_closed [closure]:
  assumes "\<And> i. i \<in> I \<Longrightarrow> P i is CDC"
  shows "(\<Sqinter> i \<in> I \<bullet> P i) is CDC"
  using assms by (rel_blast)

lemma CDC_disj_closed [closure]:
  assumes "P is CDC" "Q is CDC"
  shows "(P \<or> Q) is CDC"
proof -
  have "CDC(P \<or> Q) = (CDC(P) \<or> CDC(Q))"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def assms(1) assms(2))
qed

lemma CDC_USUP_closed [closure]:
  assumes "\<And> i. i \<in> I \<Longrightarrow> P i is CDC"
  shows "(\<Squnion> i \<in> I \<bullet> P i) is CDC"
  using assms by (rel_blast)

lemma CDC_conj_closed [closure]:
  assumes "P is CDC" "Q is CDC"
  shows "(P \<and> Q) is CDC"
  using assms by (rel_auto, blast, meson)

lemma CDC_rea_impl [rpred]:
  "$ref\<acute> \<sharp> P \<Longrightarrow> CDC(P \<Rightarrow>\<^sub>r Q) = (P \<Rightarrow>\<^sub>r CDC(Q))"
  by (rel_auto)

lemma rea_impl_CDC_closed [closure]:
  assumes "$ref\<acute> \<sharp> P" "Q is CDC"
  shows "(P \<Rightarrow>\<^sub>r Q) is CDC"
  using assms by (simp add: CDC_rea_impl Healthy_def)

lemma seq_CDC_closed [closure]:
  assumes "Q is CDC"
  shows "(P ;; Q) is CDC"
proof -
  have "CDC(P ;; Q) = P ;; CDC(Q)"
    by (rel_blast)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma st_subst_CDC_closed [closure]:
  assumes "P is CDC"
  shows "(\<sigma> \<dagger>\<^sub>S P) is CDC"
proof -
  have "(\<sigma> \<dagger>\<^sub>S CDC P) is CDC"
    by (rel_auto)
  thus ?thesis
    by (simp add: assms Healthy_if)
qed

lemma rea_st_cond_CDC [closure]: "[g]\<^sub>S\<^sub>< is CDC"
  by (rel_auto)

lemma csp_enable_CDC [closure]: "\<E>(s,t,E) is CDC"
  by (rel_auto)

lemma state_srea_CDC_closed [closure]:
  assumes "P is CDC"
  shows "state 'a \<bullet> P is CDC"
proof -
  have "state 'a \<bullet> CDC(P) is CDC"
    by (rel_blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

subsection \<open> Renaming \<close>

abbreviation "pre_image f B \<equiv> {x. f(x) \<in> B}"

definition csp_rename :: "('s, 'e) action \<Rightarrow> ('e \<Rightarrow> 'f) \<Rightarrow> ('s, 'f) action" ("(_)\<lparr>_\<rparr>\<^sub>c" [999, 0] 999) where
[upred_defs]: "P\<lparr>f\<rparr>\<^sub>c = R2(($tr\<acute> =\<^sub>u \<guillemotleft>[]\<guillemotright> \<and> $st\<acute> =\<^sub>u $st) ;; P ;; ($tr\<acute> =\<^sub>u map\<^sub>u \<guillemotleft>f\<guillemotright> $tr \<and> $st\<acute> =\<^sub>u $st \<and> uop (pre_image f) $ref\<acute> \<subseteq>\<^sub>u $ref))"

lemma csp_rename_CRR_closed [closure]: 
  assumes "P is CRR"
  shows "P\<lparr>f\<rparr>\<^sub>c is CRR"
proof -
  have "(CRR P)\<lparr>f\<rparr>\<^sub>c is CRR"
    by (rel_auto)
  thus ?thesis by (simp add: assms Healthy_if)
qed

lemma csp_rename_disj [rpred]: "(P \<or> Q)\<lparr>f\<rparr>\<^sub>c = (P\<lparr>f\<rparr>\<^sub>c \<or> Q\<lparr>f\<rparr>\<^sub>c)"
  by (rel_blast)

lemma csp_rename_UINF_ind [rpred]: "(\<Sqinter> i \<bullet> P i)\<lparr>f\<rparr>\<^sub>c = (\<Sqinter> i \<bullet> (P i)\<lparr>f\<rparr>\<^sub>c)"
  by (rel_blast)

lemma csp_rename_UINF_mem [rpred]: "(\<Sqinter> i \<in> A \<bullet> P i)\<lparr>f\<rparr>\<^sub>c = (\<Sqinter> i \<in> A \<bullet> (P i)\<lparr>f\<rparr>\<^sub>c)"
  by (rel_blast)

text \<open> Renaming distributes through conjunction only when both sides are downward closed \<close>

lemma csp_rename_conj [rpred]: 
  assumes "inj f" "P is CRR" "Q is CRR" "P is CDC" "Q is CDC"
  shows "(P \<and> Q)\<lparr>f\<rparr>\<^sub>c = (P\<lparr>f\<rparr>\<^sub>c \<and> Q\<lparr>f\<rparr>\<^sub>c)"
proof -
  from assms(1) have "((CDC (CRR P)) \<and> (CDC (CRR Q)))\<lparr>f\<rparr>\<^sub>c = ((CDC (CRR P))\<lparr>f\<rparr>\<^sub>c \<and> (CDC (CRR Q))\<lparr>f\<rparr>\<^sub>c)"
    apply (rel_auto)
    apply blast
    apply blast
    apply (meson order_refl order_trans)
    done
  thus ?thesis
    by (simp add: assms Healthy_if)
qed
  
lemma csp_rename_seq [rpred]:
  assumes "P is CRR" "Q is CRR"
  shows "(P ;; Q)\<lparr>f\<rparr>\<^sub>c = P\<lparr>f\<rparr>\<^sub>c ;; Q\<lparr>f\<rparr>\<^sub>c"
  oops

lemma csp_rename_R4 [rpred]:
  "(R4(P))\<lparr>f\<rparr>\<^sub>c = R4(P\<lparr>f\<rparr>\<^sub>c)"
  apply (rel_auto, blast)
  using less_le apply fastforce
  apply (metis (mono_tags, lifting) Prefix_Order.Nil_prefix append_Nil2 diff_add_cancel_left' less_le list.simps(8) plus_list_def)
  done

lemma csp_rename_R5 [rpred]:
  "(R5(P))\<lparr>f\<rparr>\<^sub>c = R5(P\<lparr>f\<rparr>\<^sub>c)"
  apply (rel_auto, blast)
  using less_le apply fastforce
  done

lemma csp_rename_do [rpred]: "\<Phi>(s,\<sigma>,t)\<lparr>f\<rparr>\<^sub>c = \<Phi>(s,\<sigma>,map\<^sub>u \<guillemotleft>f\<guillemotright> t)"
  by (rel_auto)

lemma csp_rename_enable [rpred]: "\<E>(s,t,E)\<lparr>f\<rparr>\<^sub>c = \<E>(s,map\<^sub>u \<guillemotleft>f\<guillemotright> t, uop (image f) E)"
  by (rel_auto)

lemma st'_unrest_csp_rename [unrest]: "$st\<acute> \<sharp> P \<Longrightarrow> $st\<acute> \<sharp> P\<lparr>f\<rparr>\<^sub>c"
  by (rel_blast)

lemma ref'_unrest_csp_rename [unrest]: "$ref\<acute> \<sharp> P \<Longrightarrow> $ref\<acute> \<sharp> P\<lparr>f\<rparr>\<^sub>c"
  by (rel_blast)

lemma csp_rename_CDC_closed [closure]:
  "P is CDC \<Longrightarrow> P\<lparr>f\<rparr>\<^sub>c is CDC"
  by (rel_blast)

lemma csp_do_CDC [closure]: "\<Phi>(s,\<sigma>,t) is CDC"
  by (rel_auto)

end