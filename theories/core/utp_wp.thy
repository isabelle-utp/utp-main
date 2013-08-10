(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_wp.thy                                                           *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Weakest Precondition Calculus *}

theory utp_wp
imports 
  utp_lattice 
  utp_recursion
  "../laws/utp_pred_laws"
  "../laws/utp_rel_laws"
  "../parser/utp_pred_parser"
begin

ML {*
  structure wp =
    Named_Thms (val name = @{binding wp} val description = "weakest precondition theorems")
*}

setup wp.setup

definition WeakPrecondP :: 
  "'VALUE WF_PREDICATE \<Rightarrow> 'VALUE WF_PREDICATE \<Rightarrow> 'VALUE WF_PREDICATE" (infixr "wp" 150) where
"Q wp r \<equiv> \<not>\<^sub>p (Q ; (\<not>\<^sub>p r))"

declare WeakPrecondP_def [eval,evalr,evalrx]

syntax
  "_upred_wp" :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "wp" 50)

translations
  "_upred_wp p q"  == "CONST WeakPrecondP p q"

lemma ConjP_wp [wp]:
  "`P wp (q \<and> r)` = `(P wp q) \<and> (P wp r)`"
  by (metis (hide_lams, no_types) SemiR_OrP_distl WeakPrecondP_def demorgan1 demorgan2)

lemma SemiR_wp [wp]: 
  "(P ; Q) wp r = P wp (Q wp r)"
  apply (simp add: WeakPrecondP_def)
  apply (metis SemiR_assoc)
done

lemma AssignR_wp [wp]:
  "\<lbrakk> x \<in> UNDASHED; v \<rhd>\<^sub>e x; UNREST_EXPR (DASHED \<union> NON_REL_VAR) v; r \<in> WF_RELATION \<rbrakk> 
     \<Longrightarrow> (x :=\<^sub>R v) wp r = r[v/\<^sub>px]"
  apply (subgoal_tac "UNREST_EXPR NON_REL_VAR v")
  apply (simp add: WeakPrecondP_def)
oops

lemma CondP_wp [wp]:
  "\<lbrakk> P \<in> WF_RELATION; Q \<in> WF_RELATION; b \<in> WF_CONDITION; r \<in> WF_RELATION \<rbrakk> \<Longrightarrow>
  (P \<lhd> b \<rhd> Q) wp r = (P wp r) \<lhd> b \<rhd> (Q wp r)"
  apply (simp add: WeakPrecondP_def)
  apply (simp add:CondR_SemiR_distr closure)
  apply (utp_pred_auto_tac)
done

lemma OrP_wp [wp]:
  "`(P \<or> Q) wp r` = `(P wp r) \<and> (Q wp r)`"
  by (metis (no_types) SemiR_OrP_distr WeakPrecondP_def demorgan1)

lemma ChoiceP_wp [wp]:
  "(P \<sqinter> Q) wp r = (P wp r) \<and>\<^sub>p (Q wp r)"
  by (simp add:sup_WF_PREDICATE_def wp)

lemma ImpliesP_precond_wp: "`[r \<Rightarrow> s]` \<Longrightarrow> `[(Q wp r) \<Rightarrow> (Q wp s)]`"
  by (metis ConjP_wp RefP_AndP RefP_def less_eq_WF_PREDICATE_def)

lemma ImpliesP_pred_wp: "`[Q \<Rightarrow> S]` \<Longrightarrow> `[(S wp r) \<Rightarrow> (Q wp r)]`"
  by (metis OrP_comm OrP_wp RefP_def inf_WF_PREDICATE_def le_iff_inf le_iff_sup less_eq_WF_PREDICATE_def sup_WF_PREDICATE_def)

lemma RefineP_precond_wp: "`[r \<Rightarrow> s]` \<Longrightarrow> Q wp s \<sqsubseteq> Q wp r"
  by (metis ImpliesP_precond_wp RefP_def less_eq_WF_PREDICATE_def)

lemma RefineP_pred_wp: "S \<sqsubseteq> Q \<Longrightarrow> Q wp r \<sqsubseteq> S wp r"
  by (metis OrP_wp RefP_AndP le_iff_sup sup_WF_PREDICATE_def)

lemma FalseP_wp [wp]: "Q ; true = true \<Longrightarrow> Q wp false = false"
  by (simp add:WeakPrecondP_def)

lemma VarOpenP_wp: "\<lbrakk> x \<in> UNDASHED; r \<in> WF_RELATION \<rbrakk> 
  \<Longrightarrow> (var x) wp r = (\<forall>\<^sub>p {x}. r)"
  apply (simp add:WeakPrecondP_def VarOpenP_def ExistsP_UNDASHED_expand_SemiR closure)
  apply (utp_pred_tac)
done

text {* I don't think the following statement is provable... *}


lemma weakest_prespec:
  "\<lbrakk>P \<in> WF_RELATION; Q \<in> WF_RELATION; S \<in> WF_RELATION \<rbrakk> \<Longrightarrow>
  `(P ; Q) \<Rightarrow> S` \<longleftrightarrow> `P \<Rightarrow> (Q wp S)`"
oops

(* Counterexample:

lemma "P \<subseteq> -(Q O -S) \<Longrightarrow> (P O Q) \<subseteq> S"
  nitpick

*)

theorem WeakPrecondP_transfer: 
  "(P = Q) \<longleftrightarrow> (\<forall> r. P wp r = Q wp r)"
  by (metis SemiR_SkipR_right WeakPrecondP_def NotP_NotP)

end