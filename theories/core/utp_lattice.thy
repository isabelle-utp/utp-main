(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_lattice.thy                                                      *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Predicate Lattice *}

theory utp_lattice
imports utp_pred (* utp_function *) "../tactics/utp_pred_tac"
begin

context PRED
begin

subsection {* Top and Bottom *}

definition BotP :: "('VALUE, 'TYPE) PREDICATE" ("\<bottom>p") where
"BotP = TrueP"

definition TopP :: "('VALUE, 'TYPE) PREDICATE" ("\<top>p") where
"TopP = FalseP"

subsection {* Supremum and Infimum *}

definition SupP ::
  "('VALUE, 'TYPE) PREDICATE set \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"ps \<subseteq> WF_PREDICATE \<longrightarrow>
 SupP ps = (if ps = {} then \<bottom>p else \<Inter> ps)"

notation SupP ("\<Squnion>p")

definition InfP ::
  "('VALUE, 'TYPE) PREDICATE set \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"ps \<subseteq> WF_PREDICATE \<longrightarrow>
 InfP ps = (if ps = {} then \<top>p else \<Union> ps)"

notation InfP ("\<Sqinter>p")

subsection {* Fixed Points *}

definition WFP ::
  "('VALUE, 'TYPE) FUNCTION \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" ("\<mu>") where
"f \<in> WF_FUNCTION \<longrightarrow>
 WFP f = \<Squnion>p {p \<in> WF_PREDICATE . f p \<sqsubseteq> p}"

definition SFP ::
  "('VALUE, 'TYPE) FUNCTION \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" ("\<nu>") where
"f \<in> WF_FUNCTION \<longrightarrow>
 SFP f = \<Sqinter>p {p \<in> WF_PREDICATE . p \<sqsubseteq> f p}"

subsection {* Theorems *}

theorem WF_PREDICATE_Union [closure] :
"ps \<subseteq> WF_PREDICATE \<Longrightarrow>
 \<Union> ps \<in> WF_PREDICATE"
apply (simp add: Union_eq)
apply (simp add: WF_PREDICATE_def)
apply (auto)
done

theorem WF_PREDICATE_Inter [closure] :
"\<lbrakk>ps \<subseteq> WF_PREDICATE; ps \<noteq> {}\<rbrakk> \<Longrightarrow>
 \<Inter> ps \<in> WF_PREDICATE"
apply (simp add: Inter_eq)
apply (simp add: WF_PREDICATE_def)
apply (clarify)
apply (drule_tac x = "SOME x . x \<in> ps" in bspec)
apply (rule someI_ex)
apply (auto) [1]
apply (subgoal_tac "(SOME x . x \<in> ps) \<in> ps")
apply (auto) [1]
apply (rule someI_ex)
apply (auto) [1]
done

subsubsection {* Closure Theorems *}

theorem BotP_closure [closure] :
"\<bottom>p \<in> WF_PREDICATE"
apply (simp add: BotP_def)
apply (simp add: closure)
done

theorem TopP_closure [closure] :
"\<top>p \<in> WF_PREDICATE"
apply (simp add: TopP_def)
apply (simp add: closure)
done

theorem SupP_closure [closure] :
"ps \<subseteq> WF_PREDICATE \<Longrightarrow>
 \<Squnion>p ps \<in> WF_PREDICATE"
apply (simp add: SupP_def)
apply (case_tac "ps = {}")
apply (simp_all)
apply (simp add: closure)
apply (simp add: closure)
done

theorem InfP_closure [closure] :
"ps \<subseteq> WF_PREDICATE \<Longrightarrow>
 \<Sqinter>p ps \<in> WF_PREDICATE"
apply (simp add: InfP_def)
apply (case_tac "ps = {}")
apply (simp_all)
apply (simp add: closure)
apply (simp add: closure)
done

theorem WFP_closure [closure] :
"f \<in> WF_FUNCTION \<Longrightarrow>
 \<mu> f \<in> WF_PREDICATE"
apply (simp add: WFP_def)
apply (rule SupP_closure)
apply (auto)
done

theorem SFP_closure [closure] :
"f \<in> WF_FUNCTION \<Longrightarrow>
 \<nu> f \<in> WF_PREDICATE"
apply (simp add: SFP_def)
apply (rule InfP_closure)
apply (auto)
done

subsubsection {* Evaluation Theorems *}

declare BotP_def [eval]
declare TopP_def [eval]

theorem EvalP_InfP [eval] :
"\<lbrakk>ps \<subseteq> WF_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>\<Sqinter>p ps\<rbrakk>b = (\<exists> p \<in> ps . \<lbrakk>p\<rbrakk>b)"
apply (simp add: EvalP_def closure)
apply (simp add: InfP_def)
apply (clarify)
apply (simp add: TopP_def FalseP_def)
done

theorem EvalP_SupP [eval] :
"\<lbrakk>ps \<subseteq> WF_PREDICATE;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>\<Squnion>p ps\<rbrakk>b = (\<forall> p \<in> ps . \<lbrakk>p\<rbrakk>b)"
apply (simp add: EvalP_def closure)
apply (simp add: SupP_def)
apply (clarify)
apply (simp add: BotP_def TrueP_def)
done

declare WFP_def [eval]
declare SFP_def [eval]

subsubsection {* Lattice Interpretation *}

abbreviation pred_gorder ::
  "('VALUE, 'TYPE) PREDICATE gorder" where
"pred_gorder \<equiv>
 \<lparr> partial_object.carrier = WF_PREDICATE,
   eq = (\<lambda> x y . x = y),
   le = (\<lambda> x y . x \<sqsubseteq> y) \<rparr>"

lemma SupP_lub :
"ps \<subseteq> WF_PREDICATE \<Longrightarrow>
 least pred_gorder (\<Squnion>p ps) (Upper pred_gorder ps)"
apply (simp add: least_def Upper_def)
apply (safe)
apply (utp_pred_auto_tac)
apply (simp add: closure)
apply (utp_pred_auto_tac)
done

lemma InfP_glb:
"ps \<subseteq> WF_PREDICATE \<Longrightarrow>
 greatest pred_gorder (\<Sqinter>p ps) (Lower pred_gorder ps)"
apply (simp add: greatest_def Lower_def)
apply (safe)
apply (utp_pred_auto_tac)
apply (simp add: closure)
apply (utp_pred_auto_tac)
done

theorem pred_complete_lattice [simp, intro!] :
"complete_lattice pred_gorder"
apply (unfold_locales)
apply (utp_pred_auto_tac)+
-- {* Subgoal 1 *}
apply (rule_tac x = "x \<and>p y" in exI)
apply (simp add: least_def Upper_def)
apply (safe)
apply (utp_pred_tac)+
-- {* Subgoal 2 *}
apply (rule_tac x = "x \<or>p y" in exI)
apply (simp add: greatest_def Lower_def)
apply (safe)
apply (utp_pred_tac)+
-- {* Subgoal 3 *}
apply (rule_tac x = "\<Squnion>p A" in exI)
apply (insert SupP_lub)
apply (auto) [1]
-- {* Subgoal 4 *}
apply (rule_tac x = "\<Sqinter>p A" in exI)
apply (insert InfP_glb)
apply (auto) [1]
done

subsubsection {* Algebraic Laws *}

text {* Not sure whether the following theorem might be dangerous. *}

theorem WF_PREDICATE_subset [closure] :
"\<lbrakk>ps \<subseteq> WF_PREDICATE; p \<in> ps\<rbrakk> \<Longrightarrow> p \<in> WF_PREDICATE"
apply (auto)
done

theorem InfP_Ref :
"\<lbrakk>ps \<subseteq> WF_PREDICATE;
 p \<in> ps\<rbrakk> \<Longrightarrow>
 (\<Sqinter>p ps) \<sqsubseteq> p"
apply (utp_pred_auto_tac)
done

theorem SupP_Ref :
"\<lbrakk>ps \<subseteq> WF_PREDICATE;
 p \<in> ps\<rbrakk> \<Longrightarrow>
 p \<sqsubseteq> (\<Squnion>p ps)"
apply (utp_pred_auto_tac)
done
end
end
