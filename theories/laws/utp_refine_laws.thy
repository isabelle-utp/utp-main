(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_rel_laws.thy                                                     *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Relation Laws *}

theory utp_rel_laws
imports 
  "../core/utp_pred" 
  "../core/utp_rename"
  "../core/utp_expr"
  "../core/utp_rel"
  "../core/utp_lattice"
  "../tactics/utp_pred_tac"
  "../tactics/utp_expr_tac"
  "../tactics/utp_rel_tac"
  "../tactics/utp_xrel_tac"
  "../parser/utp_pred_parser"
  utp_pred_laws
  utp_rename_laws
  utp_subst_laws
  utp_rel_laws
begin

lemma RefineP_CondR:
  "P \<sqsubseteq> `Q \<lhd> b \<rhd> R` \<longleftrightarrow> (P \<sqsubseteq> `b \<and> Q`) \<and>  (P \<sqsubseteq> `\<not> b \<and> R`)"
  by (utp_pred_auto_tac)

lemma RefineP_choice1:
  "(P \<sqinter> Q) \<sqsubseteq> (P :: 'a WF_PREDICATE)"
  by (utp_pred_tac)

lemma RefineP_choice2:
  "(P \<sqinter> Q) \<sqsubseteq> (Q :: 'a WF_PREDICATE)"
  by (utp_pred_tac)

lemma RefineP_seperation:
  "`P \<and> Q` \<sqsubseteq> R \<longleftrightarrow> (P \<sqsubseteq> R) \<and> (Q \<sqsubseteq> R)"
  by (utp_pred_auto_tac)

end