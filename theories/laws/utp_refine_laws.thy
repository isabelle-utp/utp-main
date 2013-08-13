(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_refine_laws.thy                                                  *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Basic Refinement Laws *}

theory utp_refine_laws
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

theorem RefineP_TrueP_refine [refine]:
  "true \<sqsubseteq> P"
  by (utp_pred_tac)

theorem RefineP_FalseP_refine [refine]:
  "P \<sqsubseteq> false"
  by (utp_pred_tac)

theorem RefineP_CondR:
  "P \<sqsubseteq> Q \<lhd> b \<rhd> R \<longleftrightarrow> `P \<sqsubseteq> b \<and> Q` \<and> `P \<sqsubseteq> \<not> b \<and> R`"
  by (utp_pred_auto_tac)

theorem RefineP_CondR_refine [refine]:
  "\<lbrakk> P \<sqsubseteq> `b \<and> Q`; P \<sqsubseteq> `\<not> b \<and> R` \<rbrakk> \<Longrightarrow> P \<sqsubseteq> Q \<lhd> b \<rhd> R"
  by (utp_pred_auto_tac)

theorem RefineP_choice1:
  "(P \<sqinter> Q) \<sqsubseteq> (P :: 'a WF_PREDICATE)"
  by (utp_pred_tac)

theorem RefineP_choice2:
  "(P \<sqinter> Q) \<sqsubseteq> (Q :: 'a WF_PREDICATE)"
  by (utp_pred_tac)

theorem RefineP_seperation:
  "`P \<and> Q` \<sqsubseteq> R \<longleftrightarrow> (P \<sqsubseteq> R) \<and> (Q \<sqsubseteq> R)"
  by (utp_pred_auto_tac)

theorem RefineP_seperation_refine [refine]:
  "\<lbrakk> P \<sqsubseteq> R; Q \<sqsubseteq> R \<rbrakk> \<Longrightarrow> `P \<and> Q` \<sqsubseteq> R"
  by (utp_pred_auto_tac)

theorem AndP_mono_refine [refine]:
  "\<lbrakk> P1 \<sqsubseteq> P2; Q1 \<sqsubseteq> Q2 \<rbrakk> \<Longrightarrow> P1 \<and>\<^sub>p Q1 \<sqsubseteq> P2 \<and>\<^sub>p Q2"
  by (utp_pred_tac)

theorem OrP_mono_refine [refine]:
  "\<lbrakk> P1 \<sqsubseteq> P2; Q1 \<sqsubseteq> Q2 \<rbrakk> \<Longrightarrow> P1 \<or>\<^sub>p Q1 \<sqsubseteq> P2 \<or>\<^sub>p Q2"
  by (utp_pred_tac)

theorem SemiR_mono_refine [refine]:
  "\<lbrakk> P1 \<sqsubseteq> P2; Q1 \<sqsubseteq> Q2 \<rbrakk> \<Longrightarrow> P1 ; Q1 \<sqsubseteq> P2 ; Q2"
  by (utp_rel_auto_tac)

theorem SemiR_spec_inter_refine:
  assumes "p \<in> WF_CONDITION" "q \<in> WF_CONDITION" "r \<in> WF_CONDITION"
  shows "`p \<Rightarrow> r\<acute>` \<sqsubseteq> `(p \<Rightarrow> q\<acute>) ; (q \<Rightarrow> r\<acute>)`"
proof -
  from assms have "p ; true = p" "q ; true = q" "r ; true = r"
    by (auto dest:SemiR_TrueP_precond)
  with assms show ?thesis
    by (utp_xrel_auto_tac)
qed

end