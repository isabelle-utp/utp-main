(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_opsem.thy                                                        *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Operational Semantics *}

theory utp_opsem
imports 
  utp_pred 
  utp_expr 
  utp_rename 
  utp_unrest 
  utp_rel
  "../laws/utp_rel_laws"
  "../laws/utp_refine_laws"
begin

type_synonym 'a WF_STATE = "('a upred * 'a upred)"

fun StepP :: "'a WF_STATE \<Rightarrow> 'a WF_STATE \<Rightarrow> bool" (infix "~>" 50) where
"(s,P) ~> (t,Q) \<longleftrightarrow> (s\<acute>;\<^sub>RP) \<sqsubseteq> (t\<acute>;\<^sub>RQ)"

lemma SkipR_step:
  "(s, II;\<^sub>R P) ~> (s, P)"
  by simp

lemma SeqR_step:
  "(s,P) ~> (t,P') \<Longrightarrow> (s, P;\<^sub>RQ) ~> (t, P';\<^sub>RQ)"
  apply (simp)
  apply (simp add:SemiR_assoc)
  apply (rule refine)
  apply (assumption)
  apply (rule order_refl)
done

lemma ChoiceP_step1:
  "(s, P \<sqinter> Q) ~> (s, P)"
  apply (simp)
  apply (metis RefineP_choice1 SemiR_mono_refine order_refl)
done

lemma ChoiceP_step2:
  "(s, P \<sqinter> Q) ~> (s, Q)"
  apply (simp)
  apply (metis RefineP_choice2 SemiR_mono_refine order_refl)
done

(*
lemma 
  assumes 
    "P \<in> WF_RELATION" 
    "Q \<in> WF_RELATION"
    "- vs \<sharp> P"
    "- vs \<sharp> Q"
    "\<And> s t. \<lbrakk> s \<in> WF_ASSIGN vs; t \<in> WF_ASSIGN vs; (s ; P) \<sqsubseteq> t \<rbrakk> \<Longrightarrow> (s ; Q) \<sqsubseteq> t" 
  shows "P \<sqsubseteq> Q"
  using assms
  apply (utp_xrel_auto_tac)


lemma 
  assumes 
    "s \<in> WF_POSTCOND"
    "P \<in> WF_RELATION"
    "Q \<in> WF_RELATION"
  shows "`s ; (P \<and> Q)` = `(s ; P) \<and> (s ; Q)`"
  nitpick
  apply (simp add:closure SemiR_algebraic_rel assms urename)
proof -
  have "`s ; (P \<and> Q)` = `true ; (s\<acute> \<and> P \<and> Q)`"
    by (metis AndP_rel_closure SemiR_AndP_left_postcond TrueP_rel_closure assms(1) assms(2) assms(3) utp_pred_simps(6))

  have "... = `true ; ((s\<acute> \<and> P) \<and> (s\<acute> \<and> Q))`"
    by (smt AndP_comm AndP_idem AndP_assoc)

  using assms
  

  apply (frule_tac SemiR_TrueP_postcond)
  apply (utp_xrel_auto_tac)
  apply (utp_rel_auto_tac)

lemma CondR_true_step:
  "[s\<acute>;b] \<Longrightarrow> (s, P \<lhd> b \<rhd> Q) ~> (s, P)"
  apply (simp add:CondR_def SemiR_OrP_distl)
  apply (utp_rel_auto_tac)
  apply (rule refine)

  by (simp)

lemma CondR_false_step:
  "[\<not>(s\<acute>;b)] \<Longrightarrow> (s, P \<lhd> b \<rhd> Q) ~> (s, Q)"
  by (simp)
*)

end