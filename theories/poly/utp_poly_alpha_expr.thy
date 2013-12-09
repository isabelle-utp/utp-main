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

typedef ('a :: DEFINED, 'm :: VALUE) WF_ALPHA_PEXPR = 
  "{(a :: 'm ALPHABET, e :: ('a, 'm) WF_PEXPRESSION). VAR - \<langle>a\<rangle>\<^sub>f \<sharp> e}" 
morphisms DestAPExpr MkAPExpr 
  apply (rule_tac x="(\<lbrace>\<rbrace>, LitPE undefined)" in exI)
  apply (auto intro:unrest)
done

setup_lifting type_definition_WF_ALPHA_PEXPR

definition "ape_alphabet e = fst (DestAPExpr e)"
definition "ape_pexpr e = snd (DestAPExpr e)"

setup {*
Adhoc_Overloading.add_variant @{const_name alphabet} @{const_name ape_alphabet}
*}

lift_definition LitAPE :: "'a \<Rightarrow> ('a :: DEFINED, 'm :: VALUE) WF_ALPHA_PEXPR"
is "\<lambda> v :: 'a. (\<lbrace>\<rbrace>, LitPE v)" by (auto intro:unrest)

lift_definition VarAPE :: "('a :: DEFINED, 'm :: VALUE) PVAR \<Rightarrow> ('a, 'm) WF_ALPHA_PEXPR"
is "\<lambda> x. (\<lbrace>x\<down>\<rbrace>, PVarPE x)" by (auto intro:unrest)

lift_definition ProdAPE ::
  "('a :: DEFINED, 'm :: VALUE) WF_ALPHA_PEXPR \<Rightarrow> 
   ('b :: DEFINED, 'm :: VALUE) WF_ALPHA_PEXPR \<Rightarrow>
   (('a * 'b), 'm) WF_ALPHA_PEXPR" ("'(_, _')\<^sub>\<alpha>")
is "\<lambda> (a, e) (b, f). (a \<union>\<^sub>f b, ProdPE e f)" by (force intro:unrest UNREST_PEXPR_subset)

lift_definition Op1APE :: 
  "('a :: DEFINED \<Rightarrow> 'b :: DEFINED) \<Rightarrow> ('a, 'm :: VALUE) WF_ALPHA_PEXPR \<Rightarrow> ('b, 'm) WF_ALPHA_PEXPR"
is "\<lambda> f (a :: 'm ALPHABET, v). (a, Op1PE f v)" by (auto intro:unrest)

lift_definition Op2APE :: 
  "('a :: DEFINED \<Rightarrow> 'b :: DEFINED \<Rightarrow> 'c :: DEFINED) \<Rightarrow> 
   ('a, 'm :: VALUE) WF_ALPHA_PEXPR \<Rightarrow> ('b, 'm) WF_ALPHA_PEXPR \<Rightarrow> ('c, 'm) WF_ALPHA_PEXPR"
is "\<lambda> f (a :: 'm ALPHABET, v) (b :: 'm ALPHABET, w). (a \<union>\<^sub>f b, Op2PE f v w)" by (force intro:unrest UNREST_PEXPR_subset)

lift_definition Op3APE :: 
  "('a :: DEFINED \<Rightarrow> 'b :: DEFINED \<Rightarrow> 'c :: DEFINED \<Rightarrow> 'd :: DEFINED) \<Rightarrow> 
   ('a, 'm :: VALUE) WF_ALPHA_PEXPR \<Rightarrow> ('b, 'm) WF_ALPHA_PEXPR \<Rightarrow> 
   ('c, 'm) WF_ALPHA_PEXPR \<Rightarrow> ('d, 'm) WF_ALPHA_PEXPR"
is "\<lambda> f (a :: 'm ALPHABET, v) (b :: 'm ALPHABET, w) (c :: 'm ALPHABET, x). (a \<union>\<^sub>f b \<union>\<^sub>f c, Op3PE f v w x)" 
by (force intro:unrest UNREST_PEXPR_subset)

definition APExprAE :: 
  "('a :: DEFINED, 'm :: VALUE) WF_ALPHA_PEXPR \<Rightarrow> 'm WF_ALPHA_EXPRESSION" where
"APExprAE e = MkExprA (\<alpha> e, (ape_pexpr e)\<down>)"

lemma APExprAE_rep_eq:
  fixes e :: "('a :: DEFINED, 'm :: VALUE) WF_ALPHA_PEXPR"
  assumes "TYPEUSOUND('a, 'm)"
  shows "DestExprA (APExprAE e) = (\<alpha> e, (ape_pexpr e)\<down>)"
  using assms
  apply (subgoal_tac "(\<alpha> e, (ape_pexpr e)\<down>) \<in> WF_ALPHA_EXPRESSION")
  apply (simp add:APExprAE_def)
  apply (simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)
  apply (rule unrest, simp)
  apply (insert DestAPExpr[of "e"])
  apply (auto simp add:ape_pexpr_def)
  apply (metis ape_alphabet_def fst_conv)
done

setup {*
Adhoc_Overloading.add_variant @{const_name erase} @{const_name APExprAE}
*}

lift_definition APExprP :: 
  "(bool, 'm :: VALUE) WF_ALPHA_PEXPR \<Rightarrow> 'm WF_ALPHA_PREDICATE" is
"\<lambda> (a :: 'm ALPHABET, v). (a, PExprP v)"
  by (auto simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def unrest)

declare [[coercion APExprP]]

setup {*
Adhoc_Overloading.add_variant @{const_name erase} @{const_name APExprP}
*}

abbreviation PSubstA :: 
"('m :: VALUE) WF_ALPHA_PREDICATE \<Rightarrow> 
 ('b :: DEFINED, 'm) WF_ALPHA_PEXPR \<Rightarrow> 
 ('b, 'm) PVAR \<Rightarrow> 
 'm WF_ALPHA_PREDICATE" where
"PSubstA p e x \<equiv> SubstA p e\<down> x\<down>"

abbreviation "TrueAPE  \<equiv> LitAPE True :: (bool, 'm::BOOL_SORT) WF_ALPHA_PEXPR"
abbreviation "FalseAPE \<equiv> LitAPE False :: (bool, 'm::BOOL_SORT) WF_ALPHA_PEXPR"

abbreviation APEqualA ::
  "('a, 'm :: VALUE) WF_ALPHA_PEXPR \<Rightarrow> ('a, 'm) WF_ALPHA_PEXPR \<Rightarrow>
   'm WF_ALPHA_PREDICATE" where
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
  fixes e :: "('a :: DEFINED, 'm :: VALUE) WF_ALPHA_PEXPR"
  assumes "TYPEUSOUND('a, 'm)"
  shows "\<alpha> (APExprAE e) = \<alpha> e"
  using assms by (simp add:ape_alphabet_def expr_alpha_def APExprAE_rep_eq)

lemma APExprP_alphabet [alphabet]:
  "\<alpha> (APExprP e) = \<alpha> e"
  apply (simp add:ape_alphabet_def pred_alphabet_def APExprP.rep_eq)
  apply (case_tac "DestAPExpr e", simp)
done

subsection {* Polymorphic Relational Operators *}

abbreviation PAssignA ::
  "('a :: DEFINED, 'm :: VALUE) PVAR \<Rightarrow> 'm ALPHABET \<Rightarrow> ('a, 'm) WF_ALPHA_PEXPR \<Rightarrow> 'm WF_ALPHA_PREDICATE" where
"PAssignA x a v \<equiv> AssignA x\<down> a v\<down>"

end