section \<open> Weakest Liberal Precondition Calculus \<close>

theory utp_wlp
imports utp_hoare
begin

text \<open> The calculus we here define is termed ``weakest precondition'' in the UTP book, however
  it is in reality the liberal version that does not account for termination. \<close>

named_theorems wp

method wp_tac = (simp add: wp)

consts
  uwlp :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" 

syntax
  "_uwlp" :: "logic \<Rightarrow> uexp \<Rightarrow> logic" (infix "wlp" 60)

translations
  "_uwlp P b" == "CONST uwlp P b"

definition wlp_upred :: "('\<alpha>, '\<beta>) urel \<Rightarrow> '\<beta> cond \<Rightarrow> '\<alpha> cond" where
"wlp_upred Q r = \<lfloor>\<not> (Q ;; (\<not> \<lceil>r\<rceil>\<^sub><)) :: ('\<alpha>, '\<beta>) urel\<rfloor>\<^sub><"

adhoc_overloading
  uwlp wlp_upred

declare wlp_upred_def [urel_defs]

lemma wlp_true [wp]: "p wlp true = true"
  by (rel_simp)  
  
theorem wlp_assigns_r [wp]:
  "\<langle>\<sigma>\<rangle>\<^sub>a wlp r = \<sigma> \<dagger> r"
  by rel_auto

theorem wlp_assign_nd [wp]:
  "x := * wlp r = (\<forall> x \<bullet> r)"
  by (rel_auto)

theorem wlp_skip_r [wp]:
  "II wlp r = r"
  by rel_auto

theorem wlp_abort [wp]:
  "r \<noteq> true \<Longrightarrow> true wlp r = false"
  by rel_auto

theorem wlp_conj [wp]:
  "P wlp (q \<and> r) = (P wlp q \<and> P wlp r)"
  by rel_auto

theorem wlp_seq_r [wp]: "(P ;; Q) wlp r = P wlp (Q wlp r)"
  by rel_auto

theorem wlp_choice [wp]: "(P \<sqinter> Q) wlp R = (P wlp R \<and> Q wlp R)"
  by (rel_auto)

theorem wlp_choice' [wp]: "(P \<or> Q) wlp R = (P wlp R \<and> Q wlp R)"
  by (rel_auto)

theorem wlp_cond [wp]: "(P \<triangleleft> b \<triangleright>\<^sub>r Q) wlp r = ((b \<Rightarrow> P wlp r) \<and> ((\<not> b) \<Rightarrow> Q wlp r))"
  by rel_auto

lemma wlp_test [wp]: "?[b] wlp c = (b \<Rightarrow> c)"
  by (rel_auto)
 
lemma wlp_gcmd [wp]: "(b \<longrightarrow>\<^sub>r P) wlp c = (b \<Rightarrow> P wlp c)"
  by (simp add: rgcmd_def wp)

lemma wlp_USUP_pre [wp]: "P wlp (\<Squnion>i\<in>{0..n} \<bullet> Q(i)) = (\<Squnion>i\<in>{0..n} \<bullet> P wlp Q(i))"
  by (rel_auto)

theorem wlp_hoare_link:
  "\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>u \<longleftrightarrow> (Q wlp r \<sqsubseteq> p)"
  by rel_auto

text {* If two programs have the same weakest precondition for any postcondition then the programs
  are the same. *}

theorem wlp_eq_intro: "\<lbrakk> \<And> r. P wlp r = Q wlp r \<rbrakk> \<Longrightarrow> P = Q"
  by (rel_auto robust, fastforce+)
end