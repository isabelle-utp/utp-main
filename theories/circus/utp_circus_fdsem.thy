section \<open> Linking to the Failures-Divergences Model \<close>

theory utp_circus_fdsem
  imports utp_circus_parallel utp_circus_recursion
begin

subsection {* Failures-Divergences Semantics *}

definition divergences :: "('\<sigma>,'\<phi>) action \<Rightarrow> '\<sigma> \<Rightarrow> '\<phi> list set" ("dv\<lbrakk>_\<rbrakk>_" [0,100] 100) where
[upred_defs]: "divergences P s = {t | t. `(\<not>\<^sub>r pre\<^sub>R(P))\<lbrakk>(\<guillemotleft>s\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>)\<^sub>u/{$st,$tr,$tr\<acute>}\<rbrakk>`}"
  
definition traces :: "('\<sigma>,'\<phi>) action \<Rightarrow> '\<sigma> \<Rightarrow> ('\<phi> list \<times> '\<sigma>) set" ("tr\<lbrakk>_\<rbrakk>_" [0,100] 100) where
[upred_defs]: "traces P s = {(t,s') | t s'. `(pre\<^sub>R(P) \<and> post\<^sub>R(P))\<lbrakk>\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>/$st,$st\<acute>,$tr,$tr\<acute>\<rbrakk>`}"

definition failures :: "('\<sigma>,'\<phi>) action \<Rightarrow> '\<sigma> \<Rightarrow> ('\<phi> list \<times> '\<phi> set) set" ("fl\<lbrakk>_\<rbrakk>_" [0,100] 100) where
[upred_defs]: "failures P s = {(t,r) | t r. `(pre\<^sub>R(P) \<and> peri\<^sub>R(P))\<lbrakk>\<guillemotleft>r\<guillemotright>,\<guillemotleft>s\<guillemotright>,\<langle>\<rangle>,\<guillemotleft>t\<guillemotright>/$ref\<acute>,$st,$tr,$tr\<acute>\<rbrakk>`}"
   
lemma traces_Skip:
  "tr\<lbrakk>Skip\<rbrakk>s = {([], s)}"
  by (simp add: traces_def rdes alpha closure, rel_simp)

lemma failures_Skip:
  "fl\<lbrakk>Skip\<rbrakk>s = {}"
  by (simp add: failures_def, rdes_calc)

lemma divergences_Skip:
  "dv\<lbrakk>Skip\<rbrakk>s = {}"
  by (simp add: divergences_def, rdes_calc)

lemma traces_AssignsCSP:
  "tr\<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>C\<rbrakk>s = {([], \<sigma>(s))}"
  by (simp add: traces_def rdes closure usubst alpha, rel_auto)

lemma failures_AssignsCSP:
  "fl\<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>C\<rbrakk>s = {}"
  by (simp add: failures_def, rdes_calc)

lemma divergences_AssignsCSP:
  "dv\<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>C\<rbrakk>s = {}"
  by (simp add: divergences_def, rdes_calc)

lemma "fl\<lbrakk>Miracle\<rbrakk>s = {}"
  by (simp add: failures_def rdes closure usubst)

lemma "dv\<lbrakk>Miracle\<rbrakk>s = {}"
  by (simp add: divergences_def rdes closure usubst)

lemma "dv\<lbrakk>Chaos\<rbrakk>s = UNIV"
  by (simp add: divergences_def rdes, rel_auto)

lemma "tr\<lbrakk>Chaos\<rbrakk>s = {}"
  by (simp add: traces_def rdes closure usubst)

subsection {* Deadlock Freedom *}
  
definition DF :: "'e set \<Rightarrow> ('s, 'e) action" where
"DF(A) = (\<mu>\<^sub>C X \<bullet> (\<Sqinter> a\<in>A \<bullet> a \<^bold>\<rightarrow> Skip) ;; X)"
 
lemma DF_CSP [closure]: "A \<noteq> {} \<Longrightarrow> DF(A) is CSP"
  by (simp add: DF_def closure unrest)

end