section \<open> Sequent Calculus \<close>

theory utp_sequent
  imports utp_pred_laws
begin

definition sequent :: "'\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> bool" (infixr "\<tturnstile>" 15) where
[upred_defs]: "sequent P Q = (Q \<sqsubseteq> P)"

utp_lift_notation sequent

abbreviation sequent_triv ("\<tturnstile> _" [15] 15) where "\<tturnstile> P \<equiv> (true \<tturnstile> P)"

translations
  "\<tturnstile> P" <= "true \<tturnstile> P"

text \<open> Conversion of UTP sequent to Isabelle proposition \<close>

lemma sequentI: "\<lbrakk> \<And> s. \<lbrakk>\<Gamma>\<rbrakk>\<^sub>e s \<Longrightarrow> \<lbrakk>\<phi>\<rbrakk>\<^sub>e s \<rbrakk> \<Longrightarrow> \<Gamma> \<tturnstile> \<phi>"
  by (rel_auto)

lemma sTrue: "P \<tturnstile> true"
  by pred_auto

lemma sAx: "P \<tturnstile> P"
  by pred_auto

lemma sNotI: "\<Gamma> \<and> P \<tturnstile> false \<Longrightarrow> \<Gamma> \<tturnstile> \<not> P"
  by pred_auto

lemma sConjI: "\<lbrakk> \<Gamma> \<tturnstile> P; \<Gamma> \<tturnstile> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<tturnstile> P \<and> Q"
  by pred_auto

lemma sImplI: "\<lbrakk> P \<and> \<Gamma> \<tturnstile> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<tturnstile> (P \<Rightarrow> Q)"
  by pred_auto 

lemma sAsmDisj: 
  "\<lbrakk> A \<tturnstile> C; B \<tturnstile> C \<rbrakk> \<Longrightarrow> A \<or> B \<tturnstile> C"
  by (rel_auto)

lemma sDisjI1: "P \<tturnstile> Q \<Longrightarrow> P \<tturnstile> (Q \<or> R)"
  by (rel_auto)

lemma sDisjI2: "P \<tturnstile> R \<Longrightarrow> P \<tturnstile> (Q \<or> R)"
  by (rel_auto)

lemma sVarEqI:
  assumes "wb_lens x" "(&x = v \<and> P) \<tturnstile> (Q\<lbrakk>v/&x\<rbrakk>)"
  shows "(&x = v \<and> P) \<tturnstile> Q"
  using assms by (rel_simp, metis wb_lens.get_put)

lemma sWk: "\<lbrakk> `Q \<Rightarrow> P`; P \<tturnstile> R \<rbrakk> \<Longrightarrow> Q \<tturnstile> R"
  by (rel_auto)

lemma sWk1: "P \<tturnstile> R \<Longrightarrow> P \<and> Q \<tturnstile> R"
  by (rel_auto)

lemma sWk2: "Q \<tturnstile> R \<Longrightarrow> P \<and> Q \<tturnstile> R"
  by (rel_auto)

end