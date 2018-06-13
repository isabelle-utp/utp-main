section \<open> Semantic Model for Stateful-Failures \<close>

theory utp_action_circus
  imports "UTP-Stateful-Failures.utp_sf_rdes" utp_action_language
begin

fun sfrd_sem :: "('s, 'e) Action \<Rightarrow> ('s, 'e) action" ("\<lbrakk>_\<rbrakk>\<^sub>C") where
"\<lbrakk>P ; Q\<rbrakk>\<^sub>C = \<lbrakk>P\<rbrakk>\<^sub>C ;; \<lbrakk>Q\<rbrakk>\<^sub>C" |
"\<lbrakk>if b then P else Q end\<rbrakk>\<^sub>C = \<lbrakk>P\<rbrakk>\<^sub>C \<triangleleft> b \<triangleright>\<^sub>R \<lbrakk>Q\<rbrakk>\<^sub>C" |
"\<lbrakk>intchoice P Q\<rbrakk>\<^sub>C = \<lbrakk>P\<rbrakk>\<^sub>C \<sqinter> \<lbrakk>Q\<rbrakk>\<^sub>C" |
"\<lbrakk>assigns \<sigma>\<rbrakk>\<^sub>C = \<langle>\<sigma>\<rangle>\<^sub>C" |
"\<lbrakk>stop\<rbrakk>\<^sub>C = Stop" |
"\<lbrakk>event E\<rbrakk>\<^sub>C = (\<box> e\<in>UNIV \<bullet> ev_pred E e &\<^sub>u do\<^sub>C(\<guillemotleft>e\<guillemotright>) ;; \<langle>ev_update E e\<rangle>\<^sub>C)" |
"\<lbrakk>extchoice P Q\<rbrakk>\<^sub>C = (\<lbrakk>P\<rbrakk>\<^sub>C \<box> \<lbrakk>Q\<rbrakk>\<^sub>C)" |
"\<lbrakk>guard b P\<rbrakk>\<^sub>C = (b &\<^sub>u \<lbrakk>P\<rbrakk>\<^sub>C)"

lemma sfrd_sem_NCSP [closure]: "\<lbrakk>A\<rbrakk>\<^sub>C is NCSP"
  by (induct A, simp_all add: closure)

definition sfrd_semantics :: "('s, 'e, ('s, 'e) st_csp \<times> ('s, 'e) st_csp) Action_Semantics" where
"sfrd_semantics = \<lparr> act_sem = sfrd_sem, act_hcond = NCSP \<rparr>"

interpretation sfrd_semantic: action_semantics sfrd_semantics
  by (unfold_locales, 
      simp_all add: sfrd_semantics_def asem_eq_def skips_def csp_theory.Unit_Left 
      csp_theory.Unit_Right AssignsCSP_id seqr_assoc cond_st_true cond_st_false closure)

end