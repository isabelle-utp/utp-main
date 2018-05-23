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

lemma CRR_intro:
  assumes "$ref \<sharp> P" "P is RR"
  shows "P is CRR"
  by (simp add: CRR_def Healthy_def, simp add: Healthy_if assms ex_unrest)

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
  apply (metis (no_types, hide_lams) Healthy_def RC1_RR_closed RC1_ex_ref RR_ex_ref RR_idem)
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

lemma st_cond_CRC [closure]: "[P]\<^sub>S\<^sub>< is CRC"
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

lemma rea_rename_CRR_closed [closure]: 
  assumes "additive f" "P is CRC"
  shows "P\<lparr>f\<rparr>\<^sub>r is CRC"
  oops

lemma conj_CRC_closed [closure]:
  "\<lbrakk> P is CRC; Q is CRC \<rbrakk> \<Longrightarrow> (P \<and> Q) is CRC"
  by (rule CRC_intro, simp_all add: unrest closure)

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

lemma disj_R1_closed [closure]: "\<lbrakk> P is R1; Q is R1 \<rbrakk> \<Longrightarrow> (P \<or> Q) is R1"
  by (rel_blast)
    
lemma st_cond_R1_closed [closure]: "\<lbrakk> P is R1; Q is R1 \<rbrakk> \<Longrightarrow> (P \<triangleleft> b \<triangleright>\<^sub>R Q) is R1"
  by (rel_blast)
    
lemma cond_st_RR_closed [closure]:
  assumes "P is RR" "Q is RR"
  shows "(P \<triangleleft> b \<triangleright>\<^sub>R Q) is RR"
  apply (rule RR_intro, simp_all add: unrest closure assms, simp add: Healthy_def R2c_condr)
  apply (simp add: Healthy_if assms RR_implies_R2c)
  apply (rel_auto)
done
    
lemma cond_st_CRR_closed [closure]:
  "\<lbrakk> P is CRR; Q is CRR \<rbrakk> \<Longrightarrow> (P \<triangleleft> b \<triangleright>\<^sub>R Q) is CRR"
  by (simp_all add: CRR_intro closure unrest)

lemma seq_CRR_closed [closure]:
  assumes "P is CRR" "Q is RR"
  shows "(P ;; Q) is CRR"
  by (rule CRR_intro, simp_all add: unrest assms closure)

lemma wp_rea_CRC [closure]: "\<lbrakk> P is CRR; Q is RC \<rbrakk> \<Longrightarrow> P wp\<^sub>r Q is CRC"
  by (rule CRC_intro, simp_all add: unrest closure)

lemma USUP_ind_CRC_closed [closure]: 
  "\<lbrakk> \<And> i. P i is CRC \<rbrakk> \<Longrightarrow> (\<Squnion> i \<bullet> P i) is CRC"
  by (metis CRC_implies_CRR CRC_implies_RC USUP_ind_CRR_closed USUP_ind_RC_closed false_CRC rea_not_CRR_closed wp_rea_CRC wp_rea_RC_false)

lemma tr_extend_seqr_lit [rdes]:
  fixes P :: "('s, 'e) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P" "$ref \<sharp> P"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<guillemotleft>a\<guillemotright>\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; P = P\<lbrakk>$tr ^\<^sub>u \<langle>\<guillemotleft>a\<guillemotright>\<rangle>/$tr\<rbrakk>"
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

lemma conj_eq_tr_RR_closed [closure]:
  assumes "P is CRR"
  shows "(P \<and> $tr\<acute> =\<^sub>u $tr) is CRR"
proof -
  have "CRR(CRR(P) \<and> $tr\<acute> =\<^sub>u $tr) = (CRR(P) \<and> $tr\<acute> =\<^sub>u $tr)"
    by (rel_auto, blast+)
  thus ?thesis
    by (metis Healthy_def assms)
qed

subsection \<open> Introduction laws \<close>

text \<open> Extensionality principles for introducing refinement and equality of Circus reactive 
  relations. It is necessary only to consider a subset of the variables that are present. \<close>

lemma CRR_refine_ext:
  assumes 
    "P is CRR" "Q is CRR"
    "\<And> t s s' r'. P\<lbrakk>\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/$tr,$tr\<acute>,$st,$st\<acute>,$ref\<acute>\<rbrakk> \<sqsubseteq> Q\<lbrakk>\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/$tr,$tr\<acute>,$st,$st\<acute>,$ref\<acute>\<rbrakk>"
  shows "P \<sqsubseteq> Q"
proof -
  have "\<And> t s s' r'. (CRR P)\<lbrakk>\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/$tr,$tr\<acute>,$st,$st\<acute>,$ref\<acute>\<rbrakk> 
                    \<sqsubseteq> (CRR Q)\<lbrakk>\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/$tr,$tr\<acute>,$st,$st\<acute>,$ref\<acute>\<rbrakk>"
    by (simp add: assms Healthy_if)
  hence "CRR P \<sqsubseteq> CRR Q"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_if assms(1) assms(2))
qed

lemma CRR_eq_ext:
  assumes 
    "P is CRR" "Q is CRR"
    "\<And> t s s' r'. P\<lbrakk>\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/$tr,$tr\<acute>,$st,$st\<acute>,$ref\<acute>\<rbrakk> = Q\<lbrakk>\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/$tr,$tr\<acute>,$st,$st\<acute>,$ref\<acute>\<rbrakk>"
  shows "P = Q"
proof -
  have "\<And> t s s' r'. (CRR P)\<lbrakk>\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/$tr,$tr\<acute>,$st,$st\<acute>,$ref\<acute>\<rbrakk> 
                    = (CRR Q)\<lbrakk>\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<guillemotleft>r'\<guillemotright>/$tr,$tr\<acute>,$st,$st\<acute>,$ref\<acute>\<rbrakk>"
    by (simp add: assms Healthy_if)
  hence "CRR P = CRR Q"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_if assms(1) assms(2))
qed

lemma CRR_refine_impl_prop:
  assumes "P is CRR" "Q is CRR" 
    "\<And> t s s' r'. `Q\<lbrakk>\<guillemotleft>r'\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>/$ref\<acute>,$st,$st\<acute>,$tr,$tr\<acute>\<rbrakk>` \<Longrightarrow> `P\<lbrakk>\<guillemotleft>r'\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>/$ref\<acute>,$st,$st\<acute>,$tr,$tr\<acute>\<rbrakk>`"
  shows "P \<sqsubseteq> Q"
  by (rule CRR_refine_ext, simp_all add: assms closure unrest usubst)
     (rule refine_prop_intro, simp_all add: unrest unrest_all_circus_vars closure assms)

subsection \<open> Weakest Precondition \<close>

lemma nil_least [simp]:
  "\<langle>\<rangle> \<le>\<^sub>u x = true" by rel_auto

lemma minus_nil [simp]:
  "xs - \<langle>\<rangle> = xs" by rel_auto

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
  shows "(P wp\<^sub>r Q) = (\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> $tr ^\<^sub>u \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                               \<Rightarrow>\<^sub>r R1(Q\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,&tt-\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr,$tr\<acute>\<rbrakk>))"
proof -
  have "(P wp\<^sub>r Q) = R2(P wp\<^sub>r Q)"
    by (simp add: CRC_implies_RR CRR_implies_RR Healthy_if RR_implies_R2 assms wp_rea_R2_closed)
  also have "... = R2(\<^bold>\<forall> (s\<^sub>0,tr\<^sub>0) \<bullet> \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st\<acute>,$tr\<acute>\<rbrakk> \<Rightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st,$tr\<rbrakk>)"
    by (simp add: wp_rea_circus_form assms closure Healthy_if)
  also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> (\<^bold>\<forall> (s\<^sub>0,tr\<^sub>0) \<bullet> \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                                        \<Rightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<guillemotleft>tr\<^sub>0\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>/$st,$tr,$tr\<acute>\<rbrakk>) 
                                         \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>)"
    by (simp add: R2_form, rel_auto)
  also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> (\<^bold>\<forall> (s\<^sub>0,tr\<^sub>0) \<bullet> \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                                        \<Rightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tt\<^sub>0-tr\<^sub>0\<guillemotright>/$st,$tr,$tr\<acute>\<rbrakk>) 
                                         \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>)"
    by (rel_auto)
  also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> (\<^bold>\<forall> (s\<^sub>0,tr\<^sub>0) \<bullet> $tr ^\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                                        \<Rightarrow>\<^sub>r (RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,&tt-\<guillemotleft>tr\<^sub>0\<guillemotright>/$st,$tr,$tr\<acute>\<rbrakk>) 
                                         \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>)"
    by (rel_auto, (metis list_concat_minus_list_concat)+)
  also have "... = (\<^bold>\<forall> (s\<^sub>0,tr\<^sub>0) \<bullet> $tr ^\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> (RR P)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>tr\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                                        \<Rightarrow>\<^sub>r R1((RR Q)\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,&tt-\<guillemotleft>tr\<^sub>0\<guillemotright>/$st,$tr,$tr\<acute>\<rbrakk>))"
    by (rel_auto, blast+)
  also have "... = (\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> $tr ^\<^sub>u \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                               \<Rightarrow>\<^sub>r R1(Q\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,&tt-\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr,$tr\<acute>\<rbrakk>))"
    by (simp add: Healthy_if assms closure)
  finally show ?thesis .
qed

lemma wp_rea_circus_form_alt:
  assumes "P is CRR" "$ref\<acute> \<sharp> P" "Q is CRC"
  shows "(P wp\<^sub>r Q) = (\<^bold>\<forall> (s\<^sub>0,t\<^sub>0) \<bullet> $tr ^\<^sub>u \<guillemotleft>t\<^sub>0\<guillemotright> \<le>\<^sub>u $tr\<acute> \<and> P\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<^sub>0\<guillemotright>/$st\<acute>,$tr,$tr\<acute>\<rbrakk> 
                               \<Rightarrow>\<^sub>r R1(Q\<lbrakk>\<guillemotleft>s\<^sub>0\<guillemotright>,\<langle>\<rangle>,&tt-\<guillemotleft>t\<^sub>0\<guillemotright>/$st,$tr,$tr\<acute>\<rbrakk>))"
  oops

subsection \<open> Trace Substitution \<close>

definition trace_subst ("_\<lbrakk>_\<rbrakk>\<^sub>t" [999,0] 999) 
where [upred_defs]: "P\<lbrakk>v\<rbrakk>\<^sub>t = (P\<lbrakk>&tt-\<lceil>v\<rceil>\<^sub>S\<^sub></&tt\<rbrakk> \<and> $tr + \<lceil>v\<rceil>\<^sub>S\<^sub>< \<le>\<^sub>u $tr\<acute>)"

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
  shows "P\<lbrakk>\<langle>\<rangle>\<rbrakk>\<^sub>t = P"
proof -
  have "(CRR P)\<lbrakk>\<langle>\<rangle>\<rbrakk>\<^sub>t = CRR P"
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
[upred_defs]: "\<I>(s,t) = (\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> $tr + \<lceil>t\<rceil>\<^sub>S\<^sub>< \<le>\<^sub>u $tr\<acute>)"

text \<open> @{term "\<I>(s, t)"} is a predicate stating that, if the initial state satisfies state predicate
  @{term s}, then the trace @{term t} is an initial trace. \<close>

lemma unrest_rea_init [unrest]:
  "\<lbrakk> x \<bowtie> ($tr)\<^sub>v; x \<bowtie> ($tr\<acute>)\<^sub>v; x \<bowtie> ($st)\<^sub>v \<rbrakk> \<Longrightarrow> x \<sharp> \<I>(s,t)"
  by (simp add: rea_init_def unrest lens_indep_sym)

lemma rea_init_R1 [closure]: "\<I>(s,t) is R1"
  apply (rel_auto) using dual_order.trans le_add by blast

lemma rea_init_R2c [closure]: "\<I>(s,t) is R2c"
  apply (rel_auto)
  apply (metis diff_add_cancel_left' trace_class.add_left_mono)
  apply (metis le_add minus_cancel_le trace_class.add_diff_cancel_left)
done

lemma rea_init_R2 [closure]: "\<I>(s,t) is R2"
  by (metis Healthy_def R1_R2c_is_R2 rea_init_R1 rea_init_R2c)
 
lemma csp_init_RR [closure]: "\<I>(s,t) is RR"
  apply (rel_auto)
  apply (metis diff_add_cancel_left' trace_class.add_left_mono)
  apply (metis le_add minus_cancel_le trace_class.add_diff_cancel_left)
  apply (metis le_add less_le less_le_trans)
done

lemma csp_init_CRR [closure]: "\<I>(s,t) is CRR"
  by (rule CRR_intro, simp_all add: unrest closure)
    
lemma rea_init_impl_st [closure]: "(\<I>(b,t) \<Rightarrow>\<^sub>r [c]\<^sub>S\<^sub><) is RC"
  apply (rule RC_intro)
  apply (simp add: closure)
  apply (rel_auto)
  using order_trans by auto
    
lemma rea_init_RC1: 
  "\<not>\<^sub>r \<I>(P,t) is RC1"
  apply (rel_auto) using dual_order.trans by blast

lemma init_acts_empty [rpred]: "\<I>(true,\<langle>\<rangle>) = true\<^sub>r"
  by (rel_auto)
    
lemma rea_not_init [rpred]: 
  "(\<not>\<^sub>r \<I>(P,\<langle>\<rangle>)) = \<I>(\<not>P,\<langle>\<rangle>)"
  by (rel_auto)
       
lemma rea_init_conj [rpred]:
  "(\<I>(P,t) \<and> \<I>(Q,t)) = \<I>(P\<and>Q,t)"
  by (rel_auto)

lemma rea_init_empty_trace [rpred]: "\<I>(s,\<langle>\<rangle>) = [s]\<^sub>S\<^sub><"
  by (rel_auto)
    
lemma rea_init_disj_same [rpred]: "(\<I>(s\<^sub>1,t) \<or> \<I>(s\<^sub>2,t)) = \<I>(s\<^sub>1 \<or> s\<^sub>2, t)"
  by (rel_auto)

lemma rea_init_impl_same [rpred]: "(\<I>(s\<^sub>1,t) \<Rightarrow>\<^sub>r \<I>(s\<^sub>2,t)) = (\<I>(s\<^sub>1, t) \<Rightarrow>\<^sub>r [s\<^sub>2]\<^sub>S\<^sub><)"
  apply (rel_auto) using dual_order.trans le_add by blast+

lemma tsubst_st_cond [usubst]: "[P]\<^sub>S\<^sub><\<lbrakk>t\<rbrakk>\<^sub>t = \<I>(P,t)"
  by (rel_auto)

lemma tsubst_rea_init [usubst]: "(\<I>(s,x))\<lbrakk>y\<rbrakk>\<^sub>t = \<I>(s,y+x)"
  apply (rel_auto)
  apply (metis add.assoc diff_add_cancel_left' trace_class.add_le_imp_le_left trace_class.add_left_mono)
  apply (metis add.assoc diff_add_cancel_left' le_add trace_class.add_le_imp_le_left trace_class.add_left_mono)+
done

lemma tsubst_rea_not [usubst]: "(\<not>\<^sub>r P)\<lbrakk>v\<rbrakk>\<^sub>t = ((\<not>\<^sub>r P\<lbrakk>v\<rbrakk>\<^sub>t) \<and> \<I>(true,v))"
  apply (rel_auto)
  using le_add order_trans by blast
    
lemma tsubst_true [usubst]: "true\<^sub>r\<lbrakk>v\<rbrakk>\<^sub>t = \<I>(true,v)"
  by (rel_auto)

lemma R4_csp_init [rpred]: "R4(\<I>(s,bop Cons x xs)) = \<I>(s,bop Cons x xs)"
  using less_list_def by (rel_blast)

lemma R5_csp_init [rpred]: "R5(\<I>(s,bop Cons x xs)) = false"
  by (rel_auto)

lemma R4_trace_subst [rpred]:
  "R4 (P\<lbrakk>bop Cons x xs\<rbrakk>\<^sub>t) = P\<lbrakk>bop Cons x xs\<rbrakk>\<^sub>t"
  using le_imp_less_or_eq by (rel_blast)

lemma R5_trace_subst [rpred]:
  "R5 (P\<lbrakk>bop Cons x xs\<rbrakk>\<^sub>t) = false"
  by (rel_auto)

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
    
lemma csp_enable_tr'_eq_tr [rpred]: 
  "\<E>(s,\<langle>\<rangle>,r) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> false = \<E>(s,\<langle>\<rangle>,r)"
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

lemma csp_enable_tr_empty: "\<E>(true,\<langle>\<rangle>,{v}\<^sub>u) = ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>v\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>)"
  by (rel_auto)

lemma csp_enable_nothing: "\<E>(true,\<langle>\<rangle>, {}\<^sub>u) = ($tr\<acute> =\<^sub>u $tr)"
  by (rel_auto)

lemma msubst_nil_csp_enable [usubst]: 
  "\<E>(s(x),t(x),E(x))\<lbrakk>x\<rightarrow>\<langle>\<rangle>\<rbrakk> = \<E>(s(x)\<lbrakk>x\<rightarrow>\<langle>\<rangle>\<rbrakk>,t(x)\<lbrakk>x\<rightarrow>\<langle>\<rangle>\<rbrakk>,E(x)\<lbrakk>x\<rightarrow>\<langle>\<rangle>\<rbrakk>)"
  by (pred_auto)

lemma msubst_csp_enable [usubst]: 
  "\<E>(s(x),t(x),E(x))\<lbrakk>x\<rightarrow>\<lceil>v\<rceil>\<^sub>S\<^sub>\<leftarrow>\<rbrakk> = \<E>(s(x)\<lbrakk>x\<rightarrow>v\<rbrakk>,t(x)\<lbrakk>x\<rightarrow>v\<rbrakk>,E(x)\<lbrakk>x\<rightarrow>v\<rbrakk>)"
  by (rel_auto)

lemma csp_enable_false [rpred]: "\<E>(false,t,E) = false"
  by (rel_auto)

lemma conj_csp_enable [rpred]: "(\<E>(b\<^sub>1, t, E\<^sub>1) \<and> \<E>(b\<^sub>2, t, E\<^sub>2)) = \<E>(b\<^sub>1 \<and> b\<^sub>2, t, E\<^sub>1 \<union>\<^sub>u E\<^sub>2)"
  by (rel_auto)

lemma USUP_csp_enable [rpred]:
  "(\<Squnion> x \<bullet> \<E>(s, t, A(x))) = \<E>(s, t, (\<Or> x \<bullet> A(x)))"
  by (rel_auto)

lemma R4_csp_enable_nil [rpred]:
  "R4(\<E>(s, \<langle>\<rangle>, E)) = false"
  by (rel_auto)

lemma R5_csp_enable_nil [rpred]:
  "R5(\<E>(s, \<langle>\<rangle>, E)) = \<E>(s, \<langle>\<rangle>, E)"
  by (rel_auto)

lemma R4_csp_enable_Cons [rpred]: 
  "R4(\<E>(s,bop Cons x xs, E)) = \<E>(s,bop Cons x xs, E)"
  by (rel_auto, simp add: Prefix_Order.strict_prefixI')

lemma R5_csp_enable_Cons [rpred]: 
  "R5(\<E>(s,bop Cons x xs, E)) = false"
  by (rel_auto)

subsection \<open> Completed Trace Interaction \<close>

definition csp_do :: "'s upred \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('e list, 's) uexpr \<Rightarrow> ('s, 'e) action" ("\<Phi>'(_,_,_')") where
[upred_defs]: "\<Phi>(s,\<sigma>,t) = (\<lceil>s\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S)"

text \<open> Predicate @{term "\<Phi>(s,\<sigma>,t)"} states that if the initial state satisfies @{term s}, and
  the trace @{term t} is performed, then afterwards the state update @{term \<sigma>} is executed. \<close>

lemma unrest_csp_do [unrest]: 
  "\<lbrakk> x \<bowtie> ($tr)\<^sub>v; x \<bowtie> ($tr\<acute>)\<^sub>v; x \<bowtie> ($st)\<^sub>v; x \<bowtie> ($st\<acute>)\<^sub>v \<rbrakk> \<Longrightarrow> x \<sharp> \<Phi>(s,\<sigma>,t)"
  by (simp_all add: csp_do_def alpha_in_var alpha_out_var prod_as_plus unrest lens_indep_sym)
    
lemma csp_do_CRR [closure]: "\<Phi>(s,\<sigma>,t) is CRR"
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
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> \<Phi>(s,\<rho>,t) = \<Phi>(\<sigma> \<dagger> s,\<rho> \<circ> \<sigma>,\<sigma> \<dagger> t)"
  by (rel_auto)
  
lemma csp_init_do [rpred]: "(\<I>(s1,t) \<and> \<Phi>(s2,\<sigma>,t)) = \<Phi>(s1 \<and> s2, \<sigma>, t)"
  by (rel_auto)

lemma csp_do_false [rpred]: "\<Phi>(false,s,t) = false"
  by (rel_auto)

lemma csp_do_assign [rpred]:
  assumes "P is CRR"
  shows "\<Phi>(s, \<sigma>, t) ;; P = ([s]\<^sub>S\<^sub>< \<and> (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P)\<lbrakk>t\<rbrakk>\<^sub>t)"
proof -
  have "\<Phi>(s,\<sigma>,t) ;; CRR(P) = ([s]\<^sub>S\<^sub>< \<and> (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> CRR(P))\<lbrakk>t\<rbrakk>\<^sub>t)"
    by (rel_blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed
            
lemma subst_state_csp_enable [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> \<E>(s,t\<^sub>2,e) = \<E>(\<sigma> \<dagger> s, \<sigma> \<dagger> t\<^sub>2, \<sigma> \<dagger> e)"
  by (rel_auto)
    
lemma csp_do_assign_enable [rpred]: 
  "\<Phi>(s\<^sub>1,\<sigma>,t\<^sub>1) ;; \<E>(s\<^sub>2,t\<^sub>2,e) = \<E>(s\<^sub>1 \<and> \<sigma> \<dagger> s\<^sub>2, t\<^sub>1^\<^sub>u(\<sigma> \<dagger> t\<^sub>2), (\<sigma> \<dagger> e))"
  by (simp add: rpred closure usubst)

lemma csp_do_assign_do [rpred]: 
  "\<Phi>(s\<^sub>1,\<sigma>,t\<^sub>1) ;; \<Phi>(s\<^sub>2,\<rho>,t\<^sub>2) = \<Phi>(s\<^sub>1 \<and> (\<sigma> \<dagger> s\<^sub>2), \<rho> \<circ> \<sigma>, t\<^sub>1^\<^sub>u(\<sigma> \<dagger> t\<^sub>2))"
  by (rel_auto)

lemma csp_do_cond [rpred]:
  "\<Phi>(s\<^sub>1,\<sigma>,t\<^sub>1) \<triangleleft> b \<triangleright>\<^sub>R \<Phi>(s\<^sub>2,\<rho>,t\<^sub>2) = \<Phi>(s\<^sub>1 \<triangleleft> b \<triangleright> s\<^sub>2, \<sigma> \<triangleleft> b \<triangleright>\<^sub>s \<rho>, t\<^sub>1 \<triangleleft> b \<triangleright> t\<^sub>2)"
  by (rel_auto)

lemma rea_assm_csp_do [rpred]: 
  "[b]\<^sup>\<top>\<^sub>r ;; \<Phi>(s,\<sigma>,t) = \<Phi>(b\<and>s,\<sigma>,t)"
  by (rel_auto)

lemma csp_do_skip [rpred]:
  assumes "P is CRR"
  shows "\<Phi>(true,id,t) ;; P = P\<lbrakk>t\<rbrakk>\<^sub>t"
proof -
  have "\<Phi>(true,id,t) ;; CRR(P) = (CRR P)\<lbrakk>t\<rbrakk>\<^sub>t"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma wp_rea_csp_do_lemma:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P" "$ref \<sharp> P"
  shows "(\<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub><) ;; P = (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P)\<lbrakk>$tr ^\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub></$tr\<rbrakk>"
  using assms by (rel_auto, meson)

lemma wp_rea_csp_do [wp]:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "P is CRR"
  shows "\<Phi>(s,\<sigma>,t) wp\<^sub>r P = (\<I>(s,t) \<Rightarrow>\<^sub>r (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P)\<lbrakk>t\<rbrakk>\<^sub>t)"
proof -
  have "\<Phi>(s,\<sigma>,t) wp\<^sub>r CRR(P) = (\<I>(s,t) \<Rightarrow>\<^sub>r (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> CRR(P))\<lbrakk>t\<rbrakk>\<^sub>t)"
    by (rel_blast)
  thus ?thesis 
    by (simp add: assms Healthy_if)
qed

lemma csp_do_power_Suc [rpred]:
  "\<Phi>(true, id, t) \<^bold>^ (Suc i) = \<Phi>(true, id, iter[Suc i](t))"
  by (induct i, (rel_auto)+)

lemma csp_power_do_comp [rpred]:
  assumes "P is CRR"
  shows "\<Phi>(true, id, t) \<^bold>^ i ;; P = \<Phi>(true, id, iter[i](t)) ;; P"
  apply (cases i)
   apply (simp_all add: rpred usubst assms closure)
  done

lemma wp_rea_csp_do_skip [wp]:
  fixes Q :: "('\<sigma>, '\<phi>) action"
  assumes "P is CRR"
  shows "\<Phi>(s,id,t) wp\<^sub>r P = (\<I>(s,t) \<Rightarrow>\<^sub>r P\<lbrakk>t\<rbrakk>\<^sub>t)"
proof -
  have "\<Phi>(s,id,t) wp\<^sub>r P = \<Phi>(s,id,t) wp\<^sub>r P"
    by (simp add: skip_r_def)
  thus ?thesis by (simp add: wp assms usubst alpha)
qed

lemma msubst_csp_do [usubst]: 
  "\<Phi>(s(x),\<sigma>,t(x))\<lbrakk>x\<rightarrow>\<lceil>v\<rceil>\<^sub>S\<^sub>\<leftarrow>\<rbrakk> = \<Phi>(s(x)\<lbrakk>x\<rightarrow>v\<rbrakk>,\<sigma>,t(x)\<lbrakk>x\<rightarrow>v\<rbrakk>)"
  by (rel_auto)

end