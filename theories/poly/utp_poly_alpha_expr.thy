(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_poly_alpha_expr.thy                                              *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Shallowly Embedded Polymorphic Alphabetised Expressions *}

theory utp_poly_alpha_expr
imports 
  utp_poly_expr
  "../alpha/utp_alpha_pred"
  "../alpha/utp_alpha_expr"
  "../alpha/utp_alpha_rel"
begin

text {* In theory we could have a single unified type for both predicates and expressions.
        This might have some advantages, but a big disadvantage is that we would no longer
        be able to give specific class instances for predicates, such as showing that
        refinement forms a partial order, or that predicates form a Kleene Algebra. As
        a result we opt for keeping the types separate. *}

default_sort DEFINED

subsection {* Polymorphic Expression Basic Syntax *}

typedef ('a :: DEFINED, 'm :: TYPED_MODEL) paexpr = 
  "{(a :: 'm alpha, e :: ('a, 'm) pexpr). - \<langle>a\<rangle>\<^sub>f \<sharp> e}" 
morphisms DestAPExpr MkAPExpr 
  apply (rule_tac x="(\<lbrace>\<rbrace>, LitPE undefined)" in exI)
  apply (auto intro:unrest)
done

setup_lifting type_definition_paexpr

definition "ape_alphabet e = fst (DestAPExpr e)"

definition EvalAPE :: "('a, 'm::TYPED_MODEL) paexpr \<Rightarrow> ('a, 'm) pexpr" ("\<lbrakk>_\<rbrakk>\<epsilon>\<^sub>*") where
"EvalAPE e = snd (DestAPExpr e)"

adhoc_overloading
  alphabet ape_alphabet

definition paexpr_REL :: "('a :: DEFINED, 'm::TYPED_MODEL) paexpr set" where
"paexpr_REL = {e. \<langle>\<alpha>(e)\<rangle>\<^sub>f \<subseteq> REL_VAR}" 

definition paexpr_COND :: "('a :: DEFINED, 'm::TYPED_MODEL) paexpr set" where
"paexpr_COND = {e \<in> paexpr_REL. D\<^sub>1 \<sharp> \<lbrakk>e\<rbrakk>\<epsilon>\<^sub>*}"

adhoc_overloading
  REL paexpr_REL

adhoc_overloading
  COND paexpr_COND

lift_definition LitAPE :: "'a \<Rightarrow> ('a :: DEFINED, 'm :: TYPED_MODEL) paexpr"
is "\<lambda> v :: 'a. (\<lbrace>\<rbrace>, LitPE v)" by (auto intro:unrest)

lift_definition VarAPE :: "('a :: DEFINED, 'm :: TYPED_MODEL) pvar \<Rightarrow> ('a, 'm) paexpr"
is "\<lambda> x. (\<lbrace>x\<down>\<rbrace>, PVarPE x)" by (auto intro:unrest)

lift_definition ProdAPE ::
  "('a :: DEFINED, 'm :: TYPED_MODEL) paexpr \<Rightarrow> 
   ('b :: DEFINED, 'm :: TYPED_MODEL) paexpr \<Rightarrow>
   (('a * 'b), 'm) paexpr" ("'(_, _')\<^sub>\<alpha>")
is "\<lambda> (a, e) (b, f). (a \<union>\<^sub>f b, ProdPE e f)" by (force intro:unrest UNREST_PEXPR_subset)

lift_definition Op1APE :: 
  "('a :: DEFINED \<Rightarrow> 'b :: DEFINED) \<Rightarrow> ('a, 'm :: TYPED_MODEL) paexpr \<Rightarrow> ('b, 'm) paexpr"
is "\<lambda> f (a :: 'm alpha, v). (a, Op1PE f v)" by (auto intro:unrest)

lift_definition Op2APE :: 
  "('a :: DEFINED \<Rightarrow> 'b :: DEFINED \<Rightarrow> 'c :: DEFINED) \<Rightarrow> 
   ('a, 'm :: TYPED_MODEL) paexpr \<Rightarrow> ('b, 'm) paexpr \<Rightarrow> ('c, 'm) paexpr"
is "\<lambda> f (a :: 'm alpha, v) (b :: 'm alpha, w). (a \<union>\<^sub>f b, Op2PE f v w)" by (force intro:unrest UNREST_PEXPR_subset)

lift_definition Op3APE :: 
  "('a :: DEFINED \<Rightarrow> 'b :: DEFINED \<Rightarrow> 'c :: DEFINED \<Rightarrow> 'd :: DEFINED) \<Rightarrow> 
   ('a, 'm :: TYPED_MODEL) paexpr \<Rightarrow> ('b, 'm) paexpr \<Rightarrow> 
   ('c, 'm) paexpr \<Rightarrow> ('d, 'm) paexpr"
is "\<lambda> f (a :: 'm alpha, v) (b :: 'm alpha, w) (c :: 'm alpha, x). (a \<union>\<^sub>f b \<union>\<^sub>f c, Op3PE f v w x)" 
by (force intro:unrest UNREST_PEXPR_subset)

definition APExprAE :: 
  "('a :: DEFINED, 'm :: TYPED_MODEL) paexpr \<Rightarrow> 'm uaexpr" where
"APExprAE e = MkExprA (\<alpha> e, \<lbrakk>e\<rbrakk>\<epsilon>\<^sub>*\<down>)"

lemma APExprAE_rep_eq:
  fixes e :: "('a :: DEFINED, 'm :: TYPED_MODEL) paexpr"
  assumes "TYPEUSOUND('a, 'm)"
  shows "DestExprA (APExprAE e) = (\<alpha> e, \<lbrakk>e\<rbrakk>\<epsilon>\<^sub>*\<down>)"
  using assms
  apply (subgoal_tac "(\<alpha> e, \<lbrakk>e\<rbrakk>\<epsilon>\<^sub>*\<down>) \<in> WF_ALPHA_EXPR")
  apply (simp add:APExprAE_def)
  apply (simp add:WF_ALPHA_EXPR_def WF_EXPR_OVER_def)
  apply (rule unrest, simp)
  apply (insert DestAPExpr[of "e"])
  apply (auto simp add:EvalAPE_def)
  apply (metis ape_alphabet_def fst_conv)
done

adhoc_overloading
  erase APExprAE

lift_definition APExprA :: 
  "(bool, 'm :: TYPED_MODEL) paexpr \<Rightarrow> 'm uapred" is
"\<lambda> (a :: 'm alpha, v). (a, PExprP v)"
  by (auto simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def unrest)

declare [[coercion APExprA]]

adhoc_overloading
  erase APExprA

abbreviation VarAP :: "(bool, 'm :: BOOL_SORT) pvar \<Rightarrow> 'm uapred" where
"VarAP x \<equiv> APExprA (VarAPE x)"

abbreviation PSubstA :: 
"('m :: TYPED_MODEL) uapred \<Rightarrow> 
 ('b :: DEFINED, 'm) paexpr \<Rightarrow> 
 ('b, 'm) pvar \<Rightarrow> 
 'm uapred" where
"PSubstA p e x \<equiv> SubstA p e\<down> x\<down>"

abbreviation "TrueAPE  \<equiv> LitAPE True :: (bool, 'm::BOOL_SORT) paexpr"
abbreviation "FalseAPE \<equiv> LitAPE False :: (bool, 'm::BOOL_SORT) paexpr"

abbreviation APEqualA ::
  "('a, 'm :: TYPED_MODEL) paexpr \<Rightarrow> ('a, 'm) paexpr \<Rightarrow>
   'm uapred" where
"APEqualA e f \<equiv> e\<down> ==\<^sub>\<alpha> f\<down>"

subsection {* Alphabet theorems *}

lemma LitAPE_alphabet [alphabet]:
  "\<alpha> (LitAPE v) = \<lbrace>\<rbrace>"
  by (simp add:ape_alphabet_def LitAPE.rep_eq)

lemma VarAPE_alphabet [alphabet]:
  "\<alpha> (VarAPE x) = \<lbrace>x\<down>\<rbrace>"
  by (simp add:ape_alphabet_def VarAPE.rep_eq)

lemma Op1APE_alphabet [alphabet]:
  "\<alpha> (Op1APE f v) = \<alpha> v"
  by (simp add:ape_alphabet_def Op1APE.rep_eq, case_tac "DestAPExpr v", simp)

lemma Op2APE_alphabet [alphabet]:
  "\<alpha> (Op2APE f v w) = \<alpha> v \<union>\<^sub>f \<alpha> w"
  by (simp add:ape_alphabet_def Op2APE.rep_eq, case_tac "DestAPExpr v", case_tac "DestAPExpr w", simp)

lemma Op3APE_alphabet [alphabet]:
  "\<alpha> (Op3APE f v w x) = \<alpha> v \<union>\<^sub>f \<alpha> w \<union>\<^sub>f \<alpha> x"
  by (simp add:ape_alphabet_def Op3APE.rep_eq, case_tac "DestAPExpr v", case_tac "DestAPExpr w", case_tac "DestAPExpr x", simp)

lemma APExprAE_alphabet [alphabet]:
  fixes e :: "('a :: DEFINED, 'm :: TYPED_MODEL) paexpr"
  assumes "TYPEUSOUND('a, 'm)"
  shows "\<alpha> (APExprAE e) = \<alpha> e"
  using assms by (simp add:ape_alphabet_def expr_alpha_def APExprAE_rep_eq)

lemma APExprP_alphabet [alphabet]:
  "\<alpha> (APExprA e) = \<alpha> e"
  apply (simp add:ape_alphabet_def pred_alphabet_def APExprA.rep_eq)
  apply (case_tac "DestAPExpr e", simp)
done

subsection {* EvalAPE theorems *}

lemma EvalAPE_LitAPE [evala]:
  "\<lbrakk>LitAPE v\<rbrakk>\<epsilon>\<^sub>* = LitPE v"
  by (simp add:EvalAPE_def LitAPE.rep_eq)

lemma EvalAPE_VarAPE [evala]:
  "\<lbrakk>VarAPE x\<rbrakk>\<epsilon>\<^sub>* = PVarPE x"
  by (simp add:EvalAPE_def VarAPE.rep_eq)

lemma EvalAPE_Op1APE [evala]:
  "\<lbrakk>Op1APE f v\<rbrakk>\<epsilon>\<^sub>* = Op1PE f \<lbrakk>v\<rbrakk>\<epsilon>\<^sub>*"
  by (simp add:EvalAPE_def Op1APE.rep_eq, case_tac "DestAPExpr v", simp)

lemma EvalAPE_Op2APE [evala]:
  "\<lbrakk>Op2APE f v w\<rbrakk>\<epsilon>\<^sub>* = Op2PE f \<lbrakk>v\<rbrakk>\<epsilon>\<^sub>* \<lbrakk>w\<rbrakk>\<epsilon>\<^sub>*"
  by (simp add:EvalAPE_def Op2APE.rep_eq, case_tac "DestAPExpr v", case_tac "DestAPExpr w", simp)

lemma EvalAPE_Op3APE [evala]:
  "\<lbrakk>Op3APE f v w x\<rbrakk>\<epsilon>\<^sub>* = Op3PE f \<lbrakk>v\<rbrakk>\<epsilon>\<^sub>* \<lbrakk>w\<rbrakk>\<epsilon>\<^sub>* \<lbrakk>x\<rbrakk>\<epsilon>\<^sub>*"
  by (simp add:EvalAPE_def Op3APE.rep_eq, case_tac "DestAPExpr v", case_tac "DestAPExpr w", case_tac "DestAPExpr x", simp)

lemma EvalAPE_APExprAE [evala]:
  fixes e :: "('a :: DEFINED, 'm :: TYPED_MODEL) paexpr"
  assumes "TYPEUSOUND('a, 'm)"
  shows "\<lbrakk>e\<down>\<rbrakk>\<epsilon> = \<lbrakk>e\<rbrakk>\<epsilon>\<^sub>*\<down>"
  using assms by (simp add:EvalAPE_def EvalAE_def APExprAE_rep_eq)

lemma EvalA_APExprA [evala]:
  "\<lbrakk>APExprA v\<rbrakk>\<pi> = PExprP \<lbrakk>v\<rbrakk>\<epsilon>\<^sub>*"
  apply (simp add:EvalA_def EvalAPE_def APExprA.rep_eq)
  apply (case_tac "DestAPExpr v", simp)
done

subsection {* Polymorphic Relational Operators *}

abbreviation PAssignA ::
  "('a :: DEFINED, 'm :: TYPED_MODEL) pvar \<Rightarrow> 'm alpha \<Rightarrow> ('a, 'm) paexpr \<Rightarrow> 'm uapred" where
"PAssignA x a v \<equiv> AssignA x\<down> a v\<down>"

subsection {* Numeric Expressions *}

abbreviation IntAPE :: "int \<Rightarrow> (int, 'a :: INT_SORT) paexpr" where
"IntAPE \<equiv> LitAPE"

abbreviation RealAPE :: "int \<Rightarrow> (int, 'a :: REAL_SORT) paexpr" where
"RealAPE \<equiv> LitAPE"

abbreviation "LessAPE     \<equiv> Op2APE uless"
abbreviation "LessEqAPE   \<equiv> Op2APE uless_eq"
abbreviation "PlusAPE u v \<equiv> Op2APE (op +) u v"
abbreviation "MultAPE u v \<equiv> Op2APE (op *) u v"
abbreviation "MinusAPE u v \<equiv> Op2APE (op -) u v"
abbreviation "DivAPE  u v \<equiv> Op2APE (op /) u v"
abbreviation "MaxAPE  u v \<equiv> Op2APE max u v"
abbreviation "MinAPE  u v \<equiv> Op2APE min u v"

subsection {* Closure Laws *}

lemma LitAPE_rel_closure [closure]:
  "LitAPE v \<in> REL"
  by (simp add:paexpr_REL_def alphabet)

lemma LitAPE_cond_closure [closure]:
  "LitAPE v \<in> COND"
  by (simp add:paexpr_COND_def LitAPE_rel_closure EvalAPE_LitAPE UNREST_LitPE)

lemma VarAPE_rel_closure [closure]:
  "x\<down> \<in> REL_VAR \<Longrightarrow> VarAPE x \<in> REL"
  by (simp add:paexpr_REL_def alphabet)

lemma VarAPE_cond_closure [closure]:
  "x\<down> \<in> D\<^sub>0 \<Longrightarrow> VarAPE x \<in> COND"
  by (simp add:paexpr_COND_def VarAPE_rel_closure EvalAPE_VarAPE UNREST_PVarPE)

lemma Op1APE_rel_closure [closure]:
  "v \<in> REL \<Longrightarrow> Op1APE f v \<in> REL"
  by (simp add:paexpr_REL_def alphabet)

lemma Op1APE_cond_closure [closure]:
  "v \<in> COND \<Longrightarrow> Op1APE f v \<in> COND"
  by (simp add:paexpr_COND_def Op1APE_rel_closure EvalAPE_Op1APE UNREST_Op1PE)

lemma Op2APE_rel_closure [closure]:
  "\<lbrakk> u \<in> REL; v \<in> REL \<rbrakk> \<Longrightarrow> Op2APE f u v \<in> REL"
  by (simp add:paexpr_REL_def alphabet)

lemma Op2APE_cond_closure [closure]:
  "\<lbrakk> u \<in> COND; v \<in> COND \<rbrakk> \<Longrightarrow> Op2APE f u v \<in> COND"
  by (simp add:paexpr_COND_def Op2APE_rel_closure EvalAPE_Op2APE UNREST_Op2PE)

lemma APExprA_rel_closure [closure]:
  "v \<in> REL \<Longrightarrow> APExprA v \<in> REL"
  by (simp add:paexpr_REL_def WF_ALPHA_REL_def REL_ALPHABET_def alphabet)

lemma APExprA_cond_closure [closure]:
  "v \<in> COND \<Longrightarrow> APExprA v \<in> COND"
  apply (simp add:paexpr_COND_def WF_ALPHA_COND_def APExprA_rel_closure)
  apply (metis EvalA_APExprA EvalA_def UNREST_PExprP)
done

lemma APExprAE_rel_closure [closure]:
  fixes v :: "('a :: DEFINED, 'm :: TYPED_MODEL) paexpr"
  assumes "TYPEUSOUND('a, 'm)" "v \<in> REL"
  shows "APExprAE v \<in> REL"
  using assms by (simp add:paexpr_REL_def WF_ALPHA_EXPR_REL_def alphabet REL_ALPHABET_def)


lemma APExprAE_cond_closure [closure]:
  fixes v :: "('a :: DEFINED, 'm :: TYPED_MODEL) paexpr"
  assumes "TYPEUSOUND('a, 'm)" "v \<in> COND"
  shows "APExprAE v \<in> COND"
  using assms 
    apply (simp add: paexpr_COND_def WF_ALPHA_EXPR_COND_def closure)
    apply (metis EvalAE_expr EvalAPE_APExprAE UNREST_PExprE)
done
  

end