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
  utp_hoare
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
"Q wp r \<equiv> \<not>\<^sub>p (Q ;\<^sub>R (\<not>\<^sub>p r))"

declare WeakPrecondP_def [eval,evalr,evalrx]

syntax
  "_upred_wp" :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "wp" 50)

translations
  "_upred_wp p q"  == "CONST WeakPrecondP p q"

theorem ConjP_wp [wp]:
  "`P wp (q \<and> r)` = `(P wp q) \<and> (P wp r)`"
  by (metis (hide_lams, no_types) SemiR_OrP_distl WeakPrecondP_def demorgan1 demorgan2)

theorem SemiR_wp [wp]: 
  "(P ;\<^sub>R Q) wp r = P wp (Q wp r)"
  apply (simp add: WeakPrecondP_def)
  apply (metis SemiR_assoc)
done

theorem AssignR_wp [wp]:
  "\<lbrakk> x \<in> D\<^sub>0; v \<rhd>\<^sub>e x; D\<^sub>1 \<sharp> v; R \<in> REL \<rbrakk> 
     \<Longrightarrow> (x :=\<^sub>R v) wp R = R[v/\<^sub>px]"
  by (simp add: WeakPrecondP_def AssignR_SemiR_left usubst)

lemma CondP_wp [wp]:
  "\<lbrakk> P \<in> REL; Q \<in> REL; b \<in> COND; r \<in> REL \<rbrakk> \<Longrightarrow>
  (P \<lhd> b \<rhd> Q) wp r = (P wp r) \<lhd> b \<rhd> (Q wp r)"
  apply (simp add: WeakPrecondP_def)
  apply (simp add:CondR_SemiR_distr closure)
  apply (utp_pred_auto_tac)
done

theorem OrP_wp [wp]:
  "`(P \<or> Q) wp r` = `(P wp r) \<and> (Q wp r)`"
  by (metis (no_types) SemiR_OrP_distr WeakPrecondP_def demorgan1)

theorem ChoiceP_wp [wp]:
  "(P \<sqinter> Q) wp r = (P wp r) \<and>\<^sub>p (Q wp r)"
  by (simp add:sup_WF_PREDICATE_def wp)

theorem ImpliesP_precond_wp: "`[r \<Rightarrow> s]` \<Longrightarrow> `[(Q wp r) \<Rightarrow> (Q wp s)]`"
  by (metis ConjP_wp RefP_AndP RefP_def less_eq_WF_PREDICATE_def)

theorem ImpliesP_pred_wp: "`[Q \<Rightarrow> S]` \<Longrightarrow> `[(S wp r) \<Rightarrow> (Q wp r)]`"
  by (metis OrP_comm OrP_wp RefP_def inf_WF_PREDICATE_def le_iff_inf le_iff_sup less_eq_WF_PREDICATE_def sup_WF_PREDICATE_def)

theorem RefineP_precond_wp: "`[r \<Rightarrow> s]` \<Longrightarrow> Q wp s \<sqsubseteq> Q wp r"
  by (metis ImpliesP_precond_wp RefP_def less_eq_WF_PREDICATE_def)

theorem RefineP_pred_wp: "S \<sqsubseteq> Q \<Longrightarrow> Q wp r \<sqsubseteq> S wp r"
  by (metis OrP_wp RefP_AndP le_iff_sup sup_WF_PREDICATE_def)

theorem TrueP_wp [wp]:
  "Q wp true = true"
  by (simp add:WeakPrecondP_def)

theorem FalseP_wp [wp]: 
  "Q ;\<^sub>R true = true \<Longrightarrow> Q wp false = false"
  by (simp add:WeakPrecondP_def)

theorem VarOpenP_wp: "\<lbrakk> x \<in> UNDASHED; r \<in> WF_RELATION \<rbrakk> 
  \<Longrightarrow> (var x) wp r = (\<forall>\<^sub>p {x}. r)"
  apply (simp add:WeakPrecondP_def VarOpenP_def ExistsP_UNDASHED_expand_SemiR closure)
  apply (utp_pred_tac)
done

text {* wp gives the weakest solution to a Hoare triple *}

theorem HoareP_extreme_solution:
  assumes "p \<in> WF_CONDITION" "Q \<in> WF_RELATION" "r \<in> WF_CONDITION"
  shows "`{p}Q{r}` = `[p \<Rightarrow> \<not> (Q ; \<not> r)]`"
proof -
  have "`{p}Q{r}` = `[Q \<Rightarrow> (p \<Rightarrow> r\<acute>)]`"
    by (utp_pred_tac)

  also have "... = `[p \<Rightarrow> (Q \<Rightarrow> r\<acute>)]`"
    by (utp_pred_auto_tac)

  also from assms have "... = [p \<Rightarrow>\<^sub>p (\<forall>\<^sub>p DASHED. (Q \<Rightarrow>\<^sub>p r\<acute>))]\<^sub>p"
    apply (utp_pred_auto_tac)
    apply (metis (lifting, no_types) EvalP_UNREST_override WF_CONDITION_def mem_Collect_eq)
    apply (metis binding_override_simps(2))
  done

  also from assms have "... = [p \<Rightarrow>\<^sub>p \<not>\<^sub>p (\<exists>\<^sub>p DASHED. (Q \<and>\<^sub>p \<not>\<^sub>p r\<acute>))]\<^sub>p"
    by (utp_pred_tac)

  also from assms have "... = [p \<Rightarrow>\<^sub>p \<not>\<^sub>p (\<exists>\<^sub>p DASHED_TWICE. ((SS1\<bullet>Q) \<and>\<^sub>p \<not>\<^sub>p (SS2\<bullet>r)))]\<^sub>p"
    apply (simp add: ExistsP_alpha_convert[OF dash_DASHED_rename_func[where xs="DASHED"], where P = "(Q \<and>\<^sub>p \<not>\<^sub>p r\<acute>)", simplified] unrest closure urename)
    apply (subgoal_tac "prime on DASHED \<bullet> r\<acute> = (prime \<circ> prime) on UNDASHED \<bullet> r")
    apply (auto simp add:ConvR_def RenameP_compose intro:RenameP_equiv UNREST_WF_CONDITION SS1_SS_eq_SS2)
  done

  also from assms have "... = `[p \<Rightarrow> \<not> (Q ; \<not> r)]`"
    by (simp add:SemiR_algebraic assms closure urename)

  finally show ?thesis .
qed

theorem HoareP_weakest_precondition [refine]:
  assumes 
    "p \<in> WF_CONDITION" 
    "Q \<in> WF_RELATION" 
    "r \<in> WF_CONDITION"
  shows "`{p}Q{r}` \<Longrightarrow> Q wp r \<sqsubseteq> p"
  by (simp add:HoareP_extreme_solution assms WeakPrecondP_def RefP_def less_eq_WF_PREDICATE_def)

theorem HoareP_WeakPrecondP:
  assumes "Q \<in> WF_RELATION" "r \<in> WF_CONDITION"
  shows "`{Q wp r}Q{r}`"
  using assms
  apply (frule_tac SemiR_TrueP_precond)
  apply (utp_xrel_auto_tac)
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