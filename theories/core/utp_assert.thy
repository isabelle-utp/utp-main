(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_assert.thy                                                       *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Assertions and Assumptions *}

theory utp_assert
imports 
  utp_lattice
begin

definition AssertR ::
"'VALUE WF_PREDICATE \<Rightarrow>
 'VALUE WF_PREDICATE" ("_\<^sub>\<bottom>" [200] 200) where
"c\<^sub>\<bottom> \<equiv> II \<lhd> c \<rhd> \<bottom>"

definition AssumeR ::
"'VALUE WF_PREDICATE \<Rightarrow>
 'VALUE WF_PREDICATE" ("_\<^sup>\<top>" [200] 200) where
"c\<^sup>\<top> \<equiv> II \<lhd> c \<rhd> \<top>"

syntax
  "_upred_assert" :: "upred \<Rightarrow> upred" ("_\<^sub>\<bottom>" [900] 900)
  "_upred_assume" :: "upred \<Rightarrow> upred" ("_\<^sup>\<top>" [899] 899)

translations
  "_upred_assert c" == "CONST AssertR c"
  "_upred_assume c" == "CONST AssumeR c"

lemma UNREST_AssumeR_DASHED_TWICE [unrest]:
  "UNREST DASHED_TWICE c \<Longrightarrow> UNREST DASHED_TWICE (c\<^sup>\<top>)"
  by (force intro:unrest simp add: AssumeR_def)

lemma UNREST_AssertR_DASHED_TWICE [unrest]:
  "UNREST DASHED_TWICE c \<Longrightarrow> UNREST DASHED_TWICE (c\<^sub>\<bottom>)"
  by (force intro:unrest simp add: AssertR_def)

declare AssumeR_def [eval, evalr, evalrr, evalrx]
declare AssertR_def [eval, evalr, evalrr, evalrx]

lemma AssertR_SemiR:
  "\<lbrakk> b \<in> WF_CONDITION; c \<in> WF_CONDITION \<rbrakk> \<Longrightarrow> b\<^sub>\<bottom> ;\<^sub>R c\<^sub>\<bottom> = (b \<and>\<^sub>p c)\<^sub>\<bottom>"
  apply (frule SemiR_TrueP_precond, frule SemiR_TrueP_precond) back
  apply (utp_xrel_auto_tac)
done

theorem AssertR_AndP:
  assumes "b \<in> WF_CONDITION" "P \<in> WF_RELATION"
  shows "`b\<^sup>\<top> ; P` = `b\<^sup>\<top> ; (P \<and> b)`"
  using assms
  apply (frule_tac SemiR_TrueP_precond)
  apply (utp_xrel_auto_tac)
done

theorem AssertR_CondR:
  assumes "b \<in> WF_CONDITION" "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "b\<^sup>\<top> ;\<^sub>R (P \<lhd> b \<rhd> Q) = b\<^sup>\<top> ;\<^sub>R P"
proof -
  have "`b\<^sup>\<top> ; (P \<lhd> b \<rhd> Q)` = `b\<^sup>\<top> ; (b \<and> (P \<lhd> b \<rhd> Q))`"
    by (metis AndP_comm AssertR_AndP CondR_rel_closure WF_CONDITION_WF_RELATION assms)

  also have "... = `b\<^sup>\<top> ; (b \<and> P)`"
    by (metis CondR_true_cond)

  also have "... = `b\<^sup>\<top> ; P`"
    by (metis AndP_comm AssertR_AndP assms)

  finally show ?thesis .
qed

end