section \<open> Symbolic Evaluation of Relational Programs \<close>

theory utp_sym_eval
  imports utp_rel_opsem
begin

text \<open> The following operator applies a variable context $\Gamma$ as an assignment, and composes 
  it with a relation $P$ for the purposes of evaluation. \<close>

definition utp_sym_eval :: "'s usubst \<Rightarrow> 's hrel \<Rightarrow> 's hrel" (infixr "\<Turnstile>" 55) where
[upred_defs]: "utp_sym_eval \<Gamma> P = (\<langle>\<Gamma>\<rangle>\<^sub>a ;; P)"

named_theorems symeval

lemma seq_symeval [symeval]: "\<Gamma> \<Turnstile> P ;; Q = (\<Gamma> \<Turnstile> P) ;; Q"
  by (rel_auto)

lemma assigns_symeval [symeval]: "\<Gamma> \<Turnstile> \<langle>\<sigma>\<rangle>\<^sub>a = (\<sigma> \<circ> \<Gamma>) \<Turnstile> II"
  by (rel_auto)

lemma term_symeval [symeval]: "(\<Gamma> \<Turnstile> II) ;; P = \<Gamma> \<Turnstile> P"
  by (rel_auto)

lemma if_true_symeval [symeval]: "\<lbrakk> \<Gamma> \<dagger> b = true \<rbrakk> \<Longrightarrow> \<Gamma> \<Turnstile> (P \<triangleleft> b \<triangleright>\<^sub>r Q) = \<Gamma> \<Turnstile> P"
  by (simp add: utp_sym_eval_def usubst assigns_r_comp)

lemma if_false_symeval [symeval]: "\<lbrakk> \<Gamma> \<dagger> b = false \<rbrakk> \<Longrightarrow> \<Gamma> \<Turnstile> (P \<triangleleft> b \<triangleright>\<^sub>r Q) = \<Gamma> \<Turnstile> Q"
  by (simp add: utp_sym_eval_def usubst assigns_r_comp)

lemma while_true_symeval [symeval]: "\<lbrakk> \<Gamma> \<dagger> b = true \<rbrakk> \<Longrightarrow> \<Gamma> \<Turnstile> while b do P od = \<Gamma> \<Turnstile> (P ;; while b do P od)"
  by (subst while_unfold, simp add: symeval)

lemma while_false_symeval [symeval]: "\<lbrakk> \<Gamma> \<dagger> b = false \<rbrakk> \<Longrightarrow> \<Gamma> \<Turnstile> while b do P od = \<Gamma> \<Turnstile> II"
  by (subst while_unfold, simp add: symeval)

lemma while_inv_true_symeval [symeval]: "\<lbrakk> \<Gamma> \<dagger> b = true \<rbrakk> \<Longrightarrow> \<Gamma> \<Turnstile> while b invr S do P od = \<Gamma> \<Turnstile> (P ;; while b do P od)"
  by (metis while_inv_def while_true_symeval)

lemma while_inv_false_symeval [symeval]: "\<lbrakk> \<Gamma> \<dagger> b = false \<rbrakk> \<Longrightarrow> \<Gamma> \<Turnstile> while b invr S do P od = \<Gamma> \<Turnstile> II"
  by (metis while_false_symeval while_inv_def)

method sym_eval = (simp add: symeval usubst lit_simps[THEN sym]), (simp del: One_nat_def add: One_nat_def[THEN sym])?

syntax
  "_terminated" :: "logic \<Rightarrow> logic" ("terminated: _" [999] 999)

translations
  "terminated: \<Gamma>" == "\<Gamma> \<Turnstile> II"

text \<open> Below are some theorems linking symbolic evaluation and Hoare logic. \<close>

lemma hoare_symeval_link_1: "\<lbrace>b\<rbrace>P\<lbrace>c\<rbrace>\<^sub>u = (\<forall> s\<^sub>1 s\<^sub>2. `s\<^sub>1 \<dagger> b` \<and> ((s\<^sub>1 \<Turnstile> P) \<sqsubseteq> (s\<^sub>2 \<Turnstile> II)) \<longrightarrow> `s\<^sub>2 \<dagger> c`)"
  by (simp add: utp_sym_eval_def usubst hoare_opsem_link trel.simps)

lemma hoare_symeval_link_2: "\<lbrace>b\<rbrace>P\<lbrace>c\<rbrace>\<^sub>u \<Longrightarrow> `s\<^sub>1 \<dagger> b` \<and> ((s\<^sub>1 \<Turnstile> P) = (s\<^sub>2 \<Turnstile> II)) \<longrightarrow> `s\<^sub>2 \<dagger> c`"
  by (rel_blast)

end