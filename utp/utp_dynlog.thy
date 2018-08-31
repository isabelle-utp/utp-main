section \<open> Dynamic Logic \<close>

theory utp_dynlog
  imports utp_sequent utp_wp
begin

named_theorems dynlog_simp and dynlog_intro

definition dBox :: "'s hrel \<Rightarrow> 's upred \<Rightarrow> 's upred" ("\<^bold>[_\<^bold>]_" [0,999] 999)
where [upred_defs]: "dBox A \<Phi> = A wp \<Phi>"

definition dDia :: "'s hrel \<Rightarrow> 's upred \<Rightarrow> 's upred" ("\<^bold><_\<^bold>>_" [0,999] 999)
where [upred_defs]: "dDia A \<Phi> = (\<not> \<^bold>[A\<^bold>] (\<not> \<Phi>))"

lemma sBoxSeq [dynlog_simp]: "\<Gamma> \<tturnstile> \<^bold>[P ;; Q\<^bold>]\<Phi> \<equiv> \<Gamma> \<tturnstile> \<^bold>[P\<^bold>]\<^bold>[Q\<^bold>]\<Phi>"
  by (simp add: dBox_def wp_seq_r)

lemma sBoxTest [dynlog_intro]: "\<Gamma> \<tturnstile> (b \<Rightarrow> \<Psi>) \<Longrightarrow> \<Gamma> \<tturnstile> \<^bold>[?[b]\<^bold>]\<Psi>"
  by (rel_auto)

lemma sBoxAssigns: "\<Gamma> \<tturnstile> \<^bold>[\<langle>\<sigma>\<rangle>\<^sub>a\<^bold>]\<Phi> \<equiv> \<Gamma> \<tturnstile> (\<sigma> \<dagger> \<Phi>)"
  by (simp add: dBox_def wp_assigns_r)

lemma sBoxAssignFwd [dynlog_simp]: "\<lbrakk> vwb_lens x; x \<sharp> v; x \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> (\<Gamma> \<tturnstile> \<^bold>[x := v\<^bold>]\<Phi>) = ((&x =\<^sub>u v \<and> \<Gamma>) \<tturnstile> \<Phi>)"
  by (rel_auto, metis vwb_lens_wb wb_lens.get_put)

lemma sBoxChoice [dynlog_simp]: "\<Gamma> \<tturnstile> \<^bold>[P \<sqinter> Q\<^bold>]\<Phi> \<equiv> \<Gamma> \<tturnstile> \<^bold>[P\<^bold>]\<Phi> \<and> \<^bold>[Q\<^bold>]\<Phi>"
  by (simp add: dBox_def wp_choice)

lemma sBoxIndStar: "\<tturnstile> [\<Phi> \<Rightarrow> \<^bold>[P\<^bold>]\<Phi>]\<^sub>u \<Longrightarrow> \<Phi> \<tturnstile> \<^bold>[P\<^sup>\<star>\<^bold>]\<Phi>"
  by (rel_simp, metis (mono_tags, lifting) mem_Collect_eq rtrancl_induct)

lemma hoare_as_dynlog: "\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>u = (p \<tturnstile> \<^bold>[Q\<^bold>]r)"
  by (rel_auto)

end