section \<open> Weakest Precondition Calculus \<close>

theory utp_wp
  imports utp_wlp
begin

text \<open> This calculus is like the liberal version, but also accounts for termination. It is equivalent
  to the relational preimage.  \<close>

consts
  uwp :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" 

syntax
  "_uwp" :: "logic \<Rightarrow> uexp \<Rightarrow> logic" (infix "wp" 60)

translations
  "_uwp P b" == "CONST uwp P b"

definition wp_upred :: "'a hrel \<Rightarrow> 'a upred \<Rightarrow> 'a upred" where
[upred_defs]: "wp_upred P b = Dom(P ;; ?[b])"

adhoc_overloading
  uwp wp_upred

lemma wp_true: "P wp true = Dom(P)"
  by (rel_auto)

lemma wp_false [wp]: "P wp false = false"
  by (rel_auto)

lemma wp_abort [wp]: "false wp b = false"
  by (rel_auto)

lemma wp_seq [wp]: "(P ;; Q) wp b = P wp (Q wp b)"
  by (simp add: wp_upred_def, metis Dom_seq RA1)

lemma wp_disj [wp]: "(P \<or> Q) wp b = (P wp b \<or> Q wp b)"
  by (rel_auto)

lemma wp_UINF_mem [wp]: "(\<Sqinter> i\<in>I \<bullet> P(i)) wp b = (\<Sqinter> i\<in>I \<bullet> P(i) wp b)"
  by (rel_auto)

lemma wp_UINF_ind [wp]: "(\<Sqinter> i \<bullet> P(i)) wp b = (\<Sqinter> i \<bullet> P(i) wp b)"
  by (rel_auto)

lemma wp_test [wp]: "?[b] wp c = (b \<and> c)"
  by (rel_auto)

lemma wp_gcmd [wp]: "(b \<longrightarrow>\<^sub>r P) wp c = (b \<and> P wp c)"
  by (rel_auto)

lemma wp_assigns [wp]: "\<langle>\<sigma>\<rangle>\<^sub>a wp b = \<sigma> \<dagger> b"
  by (rel_auto)

text \<open> Weakest Precondition and Weakest Liberal Precondition are equivalent for total deterministic
  programs \<close>

lemma wlp_wp_equiv_total_det: "\<lbrakk> Dom(P) = true; ufunctional P \<rbrakk> \<Longrightarrow> P wp b = P wlp b"
  by (rel_blast)

end