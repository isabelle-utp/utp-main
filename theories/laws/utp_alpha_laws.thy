(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alpha_laws.thy                                                   *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Alphabetised Predicate and Relation Laws *}

theory utp_alpha_laws
imports 
  "../alpha/utp_alpha_pred"
  "../alpha/utp_alpha_expr"
  "../alpha/utp_alpha_rel"
  "../tactics/utp_alpha_tac"
  "../tactics/utp_alpha_expr_tac"
  utp_pred_laws
  utp_rename_laws
  utp_subst_laws
  utp_rel_laws
begin

theorem SemiA_extract_variable:
  assumes 
    "x \<in> D\<^sub>0" "x\<acute> \<in>\<^sub>f \<alpha> P" "x \<in>\<^sub>f \<alpha> Q"
    "x\<acute>\<acute> \<notin>\<^sub>f \<alpha> P" "x\<acute>\<acute> \<notin>\<^sub>f \<alpha> Q"
  shows "P ;\<^sub>\<alpha> Q = (\<exists>-\<^sub>\<alpha> \<lbrace>x\<acute>\<acute>\<rbrace>. P[$\<^sub>\<alpha>x\<acute>\<acute>/\<^sub>\<alpha>x\<acute>] ;\<^sub>\<alpha> Q[$\<^sub>\<alpha>x\<acute>\<acute>/\<^sub>\<alpha>x])"
  using assms
  apply (utp_alpha_tac)
  apply (auto)[1]
  apply (rule SemiR_extract_variable)
  apply (simp_all add:unrest)
done



end
