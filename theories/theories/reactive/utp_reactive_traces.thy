(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_reactive.thy                                                     *)
(* Authors: Simon Foster, University of York                                  *)
(******************************************************************************)

header {* Traces of Reactive Processes *}

theory utp_reactive_traces
imports 
  utp_reactive_laws
begin

subsection {* Traces *}

definition traces :: "'a upred \<Rightarrow> 'a event list set" where
"traces(P) = {Rep_ULIST (MinusUL (\<langle>b\<rangle>\<^sub>* tr) (\<langle>b\<rangle>\<^sub>* tr\<acute>)) | b. \<lbrakk>P\<rbrakk>b \<and> \<not> \<langle>b\<rangle>\<^sub>* wait}" 

lemma traces_rel_def:
  "traces(P) = {Rep_ULIST (MinusUL (\<langle>b1\<rangle>\<^sub>* tr) (\<langle>b2\<rangle>\<^sub>* tr)) | b1 b2. (b1, b2) \<in> \<lbrakk>P\<rbrakk>R \<and> \<not> \<langle>b1\<rangle>\<^sub>* wait}"
  apply (simp add:traces_def)
  apply (unfold EvalR_as_EvalP')
  apply (auto)
  apply (rule_tac x="fst (BindR b)" in exI)
  apply (rule_tac x="snd (BindR b)" in exI)
  apply (simp add:urename closure BindR_def RenameB_override_distr1)
  apply (metis SS_equiv_NON_REL_VAR binding_equiv_idem binding_override_left_eq)
  apply (rule_tac x="BindP (b1, b2)" in exI)
  apply (simp add:BindP_def typing defined closure)
  apply (metis MkPlainP_UNDASHED PermPV_app_inv SS_PDASHED SS_VAR_RENAME_INV)
done

lemma SkipR_traces:
  "traces(II) = {[]}"
  apply (auto simp add: traces_def eval)
  apply (drule_tac x="tr\<down>" in bspec, simp add:closure)
  apply (simp add:Rep_binding_ty_def)
  apply (rule_tac x="\<B>(wait :=\<^sub>* False, wait\<acute> :=\<^sub>* False, tr :=\<^sub>* NilUL, tr\<acute> :=\<^sub>* NilUL)" in exI)
  apply (simp add:typing closure defined)
  apply (auto)
  apply (case_tac "v = tr\<down>")
  apply (auto simp add:Rep_binding_ty_def binding_upd_ty_def typing inju)
done

lemma ChoiceP_traces: "traces (P \<sqinter>\<^sub>p Q) = traces P \<union> traces Q"
  by (auto simp add:traces_def eval)
end