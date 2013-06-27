(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_deep_poly_expr.thy                                               *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Deeply Polymorphic Expressions *}

theory utp_deep_poly_expr
imports utp_expr
begin

text {* This was an expriment in creating a mechanism for performing type inference
        directly on UTP types. It turned out to be too hard so for the time
        being this is mothballed *}

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

notation Rep_WF_PEXPRESSION ("\<langle>_\<rangle>\<^sub>*")

lemma Rep_WF_EXPRESSION_typed [typing]:
  "\<langle>e\<rangle>\<^sub>* t :\<^sub>e t"
  apply (insert Rep_WF_PEXPRESSION[of e])
  apply (auto simp add:WF_PEXPRESSION_def)
done

subsection {* Core syntax *}

default_sort BOT_SORT

definition monopexpr :: "'a WF_PEXPRESSION \<Rightarrow> bool" where
"monopexpr e = (\<exists>! t. \<D> (\<langle>e\<rangle>\<^sub>* t))"

definition petype_rel :: "'a WF_PEXPRESSION \<Rightarrow> 'a UTYPE \<Rightarrow> bool" (infix ":\<^sub>*" 50) where
"petype_rel e t \<equiv> \<D> (\<langle>e\<rangle>\<^sub>* t)"

definition pexpr_type :: "'a WF_PEXPRESSION \<Rightarrow> 'a UTYPE" ("\<tau>\<^sub>*") where
"pexpr_type e = (THE t. \<D> (\<langle>e\<rangle>\<^sub>* t))"

lift_definition CoercePE :: "'a WF_PEXPRESSION \<Rightarrow> 'a UTYPE \<Rightarrow> 'a WF_PEXPRESSION" is
"\<lambda> e t t'. (if (t = t') then \<langle>e\<rangle>\<^sub>* t else BotE t')"
  by (auto intro:typing simp add:WF_PEXPRESSION_def)

(* Convert to an fully disambiguated polymorphic expression to a basic expression *)
definition PExprE :: "'a WF_PEXPRESSION \<Rightarrow> 'a WF_EXPRESSION" where
"PExprE e = \<langle>e\<rangle>\<^sub>* (pexpr_type e)"

lift_definition LitPE :: "'a::BOT_SORT \<Rightarrow> 'a WF_PEXPRESSION" is
"\<lambda> v t. if (v : t) then LitE v else BotE t"
  by (auto simp add:WF_PEXPRESSION_def typing)

subsubsection {* Laws *}

lemma LitPE_type [typing]:
  "v :! t \<Longrightarrow> LitPE v :\<^sub>* t"
  by (simp add: petype_rel_def LitPE.rep_eq defined typing)

lemma LitPE_monopexpr [closure]:
  "\<lbrakk> v :! t; monotype t \<rbrakk> \<Longrightarrow> monopexpr (LitPE v)"
  apply (simp add:monopexpr_def LitPE.rep_eq defined monotype_def)
  apply (rule_tac a="t" in ex1I)
  apply (auto simp add:dtype_rel_def)
done

lemma CoercePE_monopexpr [closure]: 
  "\<D> (\<langle>e\<rangle>\<^sub>* t) \<Longrightarrow> monopexpr (CoercePE e t)"
  apply (simp add: monopexpr_def CoercePE.rep_eq)
  apply (rule_tac a="t" in ex1I)
  apply (auto simp add:defined)
done

lemma monopexpr_tau [simp]: "\<lbrakk> x :\<^sub>* t; monopexpr x \<rbrakk> \<Longrightarrow> \<tau>\<^sub>* x = t"
  apply (simp add: petype_rel_def pexpr_type_def monotype_def monopexpr_def)
  apply (rule the_equality)
  apply (auto)
done

subsection {* Boolean Expressions *}

abbreviation "TruePE \<equiv> LitPE (MkBool True)"
abbreviation "FalsePE \<equiv> LitPE (MkBool False)"

subsubsection {* Laws *}

lemma TruePE_monopexpr [closure]:
  "monopexpr TruePE"
  by (auto intro:closure typing)

lemma FalsePE_monopexpr [closure]:
  "monopexpr FalsePE"
  by (auto intro:closure typing)

subsection {* List Expressions *}

default_sort "{BOT_SORT, LIST_SORT}"

lift_definition NilPE :: "'a WF_PEXPRESSION" 
is "\<lambda> a. if (isListType a \<and> ListParam a \<in> ListPerm) 
         then NilE (ListParam a) else BotE a"
  by (force intro:typing simp add:WF_PEXPRESSION_def)

lift_definition ConsPE :: 
  "'a WF_PEXPRESSION \<Rightarrow> 'a WF_PEXPRESSION \<Rightarrow> 'a WF_PEXPRESSION" 
is "\<lambda> x xs a. if (isListType a \<and> ListParam a \<in> ListPerm \<and> \<D> (x (ListParam a)) \<and> \<D> (xs a))
              then ConsE (ListParam a) (x (ListParam a)) (xs a) else BotE a"
  by (force intro:typing simp add:WF_PEXPRESSION_def)

lift_definition ConcatPE ::
  "'a WF_PEXPRESSION \<Rightarrow> 'a WF_PEXPRESSION \<Rightarrow> 'a WF_PEXPRESSION"
is "\<lambda> xs ys a. if (isListType a \<and> ListParam a \<in> ListPerm \<and> \<D> (xs a) \<and> \<D> (ys a))
               then ConcatE (ListParam a) (xs a) (ys a) else BotE a"
  by (force intro:typing simp add:WF_PEXPRESSION_def)

lemma NilPE_type [typing]: "a \<in> ListPerm \<Longrightarrow> NilPE :\<^sub>* ListType a"
  by (simp add:petype_rel_def NilPE.rep_eq typing defined)

lemma ConsPE_type [typing]: 
  "\<lbrakk> a \<in> ListPerm; x :\<^sub>* a; xs :\<^sub>* ListType a \<rbrakk> \<Longrightarrow> ConsPE x xs :\<^sub>* ListType a"
  by (force intro:typing defined simp add:petype_rel_def ConsPE.rep_eq typing defined)

lemma ConcatPE_type [typing]: 
  "\<lbrakk> a \<in> ListPerm; xs :\<^sub>* ListType a; ys :\<^sub>* ListType a \<rbrakk> 
   \<Longrightarrow> ConcatPE xs ys :\<^sub>* ListType a"
  by (force intro:typing defined simp add:petype_rel_def ConcatPE.rep_eq typing defined)

lemma ConsE_monopexpr [typing]:
  "\<lbrakk> monopexpr x; x :\<^sub>* t; xs :\<^sub>* ListType t; t \<in> ListPerm \<rbrakk> \<Longrightarrow> monopexpr (ConsPE x xs)"
  apply (simp add:monopexpr_def ConsPE.rep_eq defined typing petype_rel_def)
  apply (rule_tac a="ListType t" in ex1I)
  apply (auto intro:typing defined)
  apply (metis ListParam isListType_elim)
done

end