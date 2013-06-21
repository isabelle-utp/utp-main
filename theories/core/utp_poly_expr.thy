(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_poly_expr.thy                                                    *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Somewhat Polymorphic Expressions *}

theory utp_poly_expr
imports utp_expr
begin

type_synonym 'a PEXPRESSION = "'a UTYPE \<Rightarrow> 'a WF_EXPRESSION"

definition WF_PEXPRESSION :: "'VALUE PEXPRESSION set" where
"WF_PEXPRESSION = {f. \<forall> t. f t :\<^sub>e t}"

typedef 'VALUE WF_PEXPRESSION = "WF_PEXPRESSION :: 'VALUE PEXPRESSION set"
  apply (simp add:WF_PEXPRESSION_def)
  apply (rule_tac x="(\<lambda> t. DefaultE t)" in exI)
  apply (auto intro:typing)
done

declare Rep_WF_PEXPRESSION [simp]
declare Rep_WF_PEXPRESSION_inverse [simp]
declare Abs_WF_PEXPRESSION_inverse [simp]

lemma Rep_WF_PEXPRESSION_intro [intro]:
  "Rep_WF_PEXPRESSION x = Rep_WF_PEXPRESSION y \<Longrightarrow> x = y"
  by (simp add:Rep_WF_PEXPRESSION_inject)

lemma Rep_WF_PEXPRESSION_elim [elim]:
  "\<lbrakk> x = y; Rep_WF_PEXPRESSION x = Rep_WF_PEXPRESSION y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

setup_lifting type_definition_WF_PEXPRESSION

notation Rep_WF_PEXPRESSION ("\<langle>_\<rangle>\<^sub>~")

lemma Rep_WF_EXPRESSION_typed [typing]:
  "\<langle>e\<rangle>\<^sub>~ t :\<^sub>e t"
  apply (insert Rep_WF_PEXPRESSION[of e])
  apply (auto simp add:WF_PEXPRESSION_def)
done

definition CoercePE :: "'a WF_PEXPRESSION \<Rightarrow> 'a UTYPE \<Rightarrow> 'a WF_EXPRESSION" where
"CoercePE e t = \<langle>e\<rangle>\<^sub>~ t"

subsection {* List Expressions *}

lift_definition NilPE :: "'a::{BOT_SORT, LIST_SORT} WF_PEXPRESSION" 
is "\<lambda> a. if (isListType a \<and> ListParam a \<in> ListPerm) 
         then NilE (ListParam a) else BotE a"
  by (force intro:typing simp add:WF_PEXPRESSION_def)

lift_definition ConsPE :: 
  "'a::{BOT_SORT, LIST_SORT} WF_PEXPRESSION \<Rightarrow> 'a WF_PEXPRESSION \<Rightarrow> 'a WF_PEXPRESSION" 
is "\<lambda> x xs a. if (isListType a \<and> ListParam a \<in> ListPerm \<and> \<D> (x (ListParam a)) \<and> \<D> (xs a))
              then ConsE (ListParam a) (x (ListParam a)) (xs a) else BotE a"
  by (force intro:typing simp add:WF_PEXPRESSION_def)

(* Convert to an fully disambiguated polymorphic expression to a basic expression *)
definition PExprE :: "'a WF_PEXPRESSION \<Rightarrow> 'a WF_EXPRESSION" where
"PExprE e = \<langle>e\<rangle>\<^sub>~ (THE t. \<D> (\<langle>e\<rangle>\<^sub>~ t))"

end