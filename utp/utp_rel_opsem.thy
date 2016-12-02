section {* Relational operational semantics *}

theory utp_rel_opsem
  imports utp_rel
begin

fun trel :: "'\<alpha> usubst \<times> '\<alpha> hrelation \<Rightarrow> '\<alpha> usubst \<times> '\<alpha> hrelation \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>u" 85) where
"(\<sigma>, P) \<rightarrow>\<^sub>u (\<rho>, Q) \<longleftrightarrow> (\<langle>\<sigma>\<rangle>\<^sub>a ;; P) \<sqsubseteq> (\<langle>\<rho>\<rangle>\<^sub>a ;; Q)"

lemma trans_trel:
  "\<lbrakk> (\<sigma>, P) \<rightarrow>\<^sub>u (\<rho>, Q); (\<rho>, Q) \<rightarrow>\<^sub>u (\<phi>, R) \<rbrakk> \<Longrightarrow> (\<sigma>, P) \<rightarrow>\<^sub>u (\<phi>, R)"
  by auto

lemma skip_trel: "(\<sigma>, II) \<rightarrow>\<^sub>u (\<sigma>, II)"
  by simp

lemma assigns_trel: "(\<sigma>, \<langle>\<rho>\<rangle>\<^sub>a) \<rightarrow>\<^sub>u (\<rho> \<circ> \<sigma>, II)"
  by (simp add: assigns_comp)

lemma assign_trel: 
  fixes x :: "('a, '\<alpha>) uvar"
  assumes "uvar x"
  shows "(\<sigma>, x := v) \<rightarrow>\<^sub>u (\<sigma>(x \<mapsto>\<^sub>s \<sigma> \<dagger> v), II)"
  by (simp add: assigns_comp subst_upd_comp)

lemma seq_trel:
  assumes "(\<sigma>, P) \<rightarrow>\<^sub>u (\<rho>, Q)"
  shows "(\<sigma>, P ;; R) \<rightarrow>\<^sub>u (\<rho>, Q ;; R)"
  by (metis (no_types, lifting) assms seqr_assoc trel.simps upred_quantale.mult_isor)
 
lemma seq_skip_trel:
  "(\<sigma>, II ;; P) \<rightarrow>\<^sub>u (\<sigma>, P)"
  by simp

lemma nondet_left_trel:
  "(\<sigma>, P \<sqinter> Q) \<rightarrow>\<^sub>u (\<sigma>, P)"
  by (simp add: upred_quantale.subdistl)

lemma nondet_right_trel:
  "(\<sigma>, P \<sqinter> Q) \<rightarrow>\<^sub>u (\<sigma>, Q)"
  using nondet_left_trel by force

lemma rcond_true_trel:
  assumes "\<sigma> \<dagger> b = true"
  shows "(\<sigma>, P \<triangleleft> b \<triangleright>\<^sub>r Q) \<rightarrow>\<^sub>u (\<sigma>, P)"
  using assms
  by (simp add: assigns_r_comp usubst aext_true cond_unit_T)

lemma rcond_false_trel:
  assumes "\<sigma> \<dagger> b = false"
  shows "(\<sigma>, P \<triangleleft> b \<triangleright>\<^sub>r Q) \<rightarrow>\<^sub>u (\<sigma>, Q)"
  using assms
  by (simp add: assigns_r_comp usubst aext_false cond_unit_F)

lemma while_true_trel:
  assumes "\<sigma> \<dagger> b = true"
  shows "(\<sigma>, while b do P od) \<rightarrow>\<^sub>u (\<sigma>, P ;; while b do P od)"
  by (metis assms rcond_true_trel while_unfold)

lemma while_false_trel:
  assumes "\<sigma> \<dagger> b = false"
  shows "(\<sigma>, while b do P od) \<rightarrow>\<^sub>u (\<sigma>, II)"
  by (metis assms rcond_false_trel while_unfold)

declare trel.simps [simp del]

end