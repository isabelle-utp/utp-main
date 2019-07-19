section \<open> Dynamic Logic \<close>

theory utp_dynlog
  imports utp_sequent utp_wp
begin

subsection \<open> Definitions \<close>

named_theorems dynlog_simp and dynlog_intro

definition dBox :: "('\<alpha>, '\<beta>) urel \<Rightarrow> '\<beta> upred \<Rightarrow> '\<alpha> upred" ("\<^bold>[_\<^bold>]_" [0,999] 999)
where [upred_defs]: "dBox A \<Phi> = A wlp \<Phi>"

definition dDia :: "('\<alpha>, '\<beta>) urel \<Rightarrow> '\<beta> upred \<Rightarrow> '\<alpha> upred" ("\<^bold><_\<^bold>>_" [0,999] 999)
where [upred_defs]: "dDia A \<Phi> = A wp \<Phi>"

lemma dDia_dBox_def: "\<^bold><A\<^bold>>\<Phi> = (\<not> \<^bold>[A\<^bold>](\<not> \<Phi>))"
  by (simp add: dBox_def dDia_def wp_wlp_conjugate)

text \<open> Correspondence between Hoare logic and Dynamic Logic \<close>

lemma hoare_as_dynlog: "\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>u = (p \<tturnstile> \<^bold>[Q\<^bold>]r)"
  by (rel_auto)

subsection \<open> Box Laws \<close>

lemma dBox_false [dynlog_simp]: "\<^bold>[false\<^bold>]\<Phi> = true"
  by (rel_auto)

lemma dBox_skip [dynlog_simp]: "\<^bold>[II\<^bold>]\<Phi> = \<Phi>"
  by (rel_auto)

lemma dBox_assigns [dynlog_simp]: "\<^bold>[\<langle>\<sigma>\<rangle>\<^sub>a\<^bold>]\<Phi> = (\<sigma> \<dagger> \<Phi>)"
  by (simp add: dBox_def wlp_assigns_r)

lemma dBox_choice [dynlog_simp]: "\<^bold>[P \<sqinter> Q\<^bold>]\<Phi> = (\<^bold>[P\<^bold>]\<Phi> \<and> \<^bold>[Q\<^bold>]\<Phi>)"
  by (rel_auto)

lemma dBox_seq: "\<^bold>[P ;; Q\<^bold>]\<Phi> = \<^bold>[P\<^bold>]\<^bold>[Q\<^bold>]\<Phi>"
  by (simp add: dBox_def wlp_seq_r)

lemma dBox_star_unfold: "\<^bold>[P\<^sup>\<star>\<^bold>]\<Phi> = (\<Phi> \<and> \<^bold>[P\<^bold>]\<^bold>[P\<^sup>\<star>\<^bold>]\<Phi>)"
  by (metis dBox_choice dBox_seq dBox_skip ustar_unfoldl)

lemma dBox_star_induct: "`(\<Phi> \<and> \<^bold>[P\<^sup>\<star>\<^bold>](\<Phi> \<Rightarrow> \<^bold>[P\<^bold>]\<Phi>)) \<Rightarrow> \<^bold>[P\<^sup>\<star>\<^bold>]\<Phi>`"
  by (rel_simp, metis (mono_tags, lifting) mem_Collect_eq rtrancl_induct)

lemma dBox_test: "\<^bold>[?[p]\<^bold>]\<Phi> = (p \<Rightarrow> \<Phi>)"
  by (rel_auto)

subsection \<open> Diamond Laws \<close>

lemma dDia_false [dynlog_simp]: "\<^bold><false\<^bold>>\<Phi> = false"
  by (simp add: dBox_false dDia_dBox_def)

lemma dDia_skip [dynlog_simp]: "\<^bold><II\<^bold>>\<Phi> = \<Phi>"
  by (simp add: dBox_skip dDia_dBox_def)

lemma dDia_assigns [dynlog_simp]: "\<^bold><\<langle>\<sigma>\<rangle>\<^sub>a\<^bold>>\<Phi> = (\<sigma> \<dagger> \<Phi>)"
  by (simp add: dBox_assigns dDia_dBox_def subst_not)

lemma dDia_choice: "\<^bold><P \<sqinter> Q\<^bold>>\<Phi> = (\<^bold><P\<^bold>>\<Phi> \<or> \<^bold><Q\<^bold>>\<Phi>)"
  by (simp add: dBox_def dDia_dBox_def wlp_choice)

lemma dDia_seq: "\<^bold><P ;; Q\<^bold>>\<Phi> = \<^bold><P\<^bold>>\<^bold><Q\<^bold>>\<Phi>"
  by (simp add: dBox_def dDia_dBox_def wlp_seq_r)

lemma dDia_test: "\<^bold><?[p]\<^bold>>\<Phi> = (p \<and> \<Phi>)"
  by (rel_auto)

subsection \<open> Sequent Laws \<close>

lemma sBoxSeq [dynlog_simp]: "\<Gamma> \<tturnstile> \<^bold>[P ;; Q\<^bold>]\<Phi> \<equiv> \<Gamma> \<tturnstile> \<^bold>[P\<^bold>]\<^bold>[Q\<^bold>]\<Phi>"
  by (simp add: dBox_def wlp_seq_r)

lemma sBoxTest [dynlog_intro]: "\<Gamma> \<tturnstile> (b \<Rightarrow> \<Psi>) \<Longrightarrow> \<Gamma> \<tturnstile> \<^bold>[?[b]\<^bold>]\<Psi>"
  by (rel_auto)

lemma sBoxAssignFwd [dynlog_intro]: 
  assumes "vwb_lens x" "\<And> x\<^sub>0. ((\<Gamma>\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/&x\<rbrakk> \<and> &x =\<^sub>u v\<lbrakk>\<guillemotleft>x\<^sub>0\<guillemotright>/&x\<rbrakk>) \<tturnstile> \<Phi>)"
  shows "(\<Gamma> \<tturnstile> \<^bold>[x := v\<^bold>]\<Phi>)"
proof -
  have "\<lbrace>\<Gamma>\<rbrace> x := v ;; II \<lbrace>\<Phi>\<rbrace>\<^sub>u"
    by (metis (no_types) assigns_init_hoare_general assms(1) assms(2) dBox_skip hoare_as_dynlog utp_pred_laws.inf_commute)
  then show ?thesis
    by (simp add: hoare_as_dynlog)
qed

lemma sBoxAssignFwd_simp [dynlog_simp]: "\<lbrakk> vwb_lens x; x \<sharp> v; x \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> (\<Gamma> \<tturnstile> \<^bold>[x := v\<^bold>]\<Phi>) = ((&x =\<^sub>u v \<and> \<Gamma>) \<tturnstile> \<Phi>)"
  by (rel_auto, metis vwb_lens_wb wb_lens.get_put)

lemma sBoxIndStar: "\<tturnstile> [\<Phi> \<Rightarrow> \<^bold>[P\<^bold>]\<Phi>]\<^sub>u \<Longrightarrow> \<Phi> \<tturnstile> \<^bold>[P\<^sup>\<star>\<^bold>]\<Phi>"
  by (rel_simp, metis (mono_tags, lifting) mem_Collect_eq rtrancl_induct)

end