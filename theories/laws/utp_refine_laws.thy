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


lemma SeqR_disjunctive2: 
  "disjunctive2 (op ;)"
  apply (simp add: disjunctive2_def)
  apply (utp_rel_auto_tac)
done



theorem RefineP_TrueP_refine [refine]:
  "true \<sqsubseteq> P"
  by (utp_pred_tac)

theorem RefineP_FalseP_refine [refine]:
  "P \<sqsubseteq> false"
  by (utp_pred_tac)

theorem RefineP_by_TrueP_refine [refine]:
  "[P] \<Longrightarrow> P \<sqsubseteq> true"
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

theorem SemiR_spec_refine [refine]:
  "Q \<sqsubseteq> `P \<and> R` \<Longrightarrow> `P \<Rightarrow> Q` \<sqsubseteq> R"
  by (utp_pred_tac)

theorem OrP_refine [refine]:
  "\<lbrakk> P \<sqsubseteq> Q; P \<sqsubseteq> R \<rbrakk> \<Longrightarrow> P \<sqsubseteq> `Q \<or> R`"
  by (utp_pred_tac)

theorem ChoiceP_refine [refine]:
  "\<lbrakk> (P :: 'a WF_PREDICATE) \<sqsubseteq> Q; P \<sqsubseteq> R \<rbrakk> \<Longrightarrow> P \<sqsubseteq> `Q \<sqinter> R`"
  by (utp_pred_tac)

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

lemma AndP_refines_1 [refine]:
  "X \<sqsubseteq> Y \<Longrightarrow> X \<sqsubseteq> `Y \<and> Z`"
  by (utp_pred_tac)

lemma AndP_refines_2 [refine]:
  "X \<sqsubseteq> Z \<Longrightarrow> X \<sqsubseteq> `Y \<and> Z`"
  by (utp_pred_tac)

lemma RefineP_equal_right_trans:
  "\<lbrakk> X \<sqsubseteq> Y; Y = Z \<rbrakk> \<Longrightarrow> X \<sqsubseteq> Z"
  by (simp)

lemma RefineP_equal_left_trans:
  "\<lbrakk> X = Y; Y \<sqsubseteq> Z \<rbrakk> \<Longrightarrow> X \<sqsubseteq> Z"
  by (simp)

lemma AssignR_refinement [refine]:
  assumes
    "p \<in> WF_CONDITION" "q \<in> WF_POSTCOND"
    "x \<in> UNDASHED" "v \<rhd>\<^sub>e x" "DASHED \<sharp> v" "q[v/\<^sub>px\<acute>] \<sqsubseteq> p"
  shows "(p \<Rightarrow>\<^sub>p q) \<sqsubseteq> x :=\<^sub>R v"
  using assms
    apply (utp_pred_auto_tac)
    apply (auto simp add:AssignF_upd_rep_eq EvalE_def)
    apply (metis (full_types) binding_upd_simps(2))
done

end