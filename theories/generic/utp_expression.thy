(******************************************************************************)
(* Project: Deep Mechanisation of the UTP                                     *)
(* File: utp/generic/utp_expression.thy                                       *)
(* Author: Simon Foster and Frank Zeyda, University of York                   *)
(******************************************************************************)

header {* Generic Expressions *}

theory utp_expression
imports "../utp_types" utp_gen_pred utp_eval_tactic utp_value
begin

type_synonym ('VALUE, 'TYPE) EXPRESSION =
  "(('VALUE, 'TYPE) BINDING \<Rightarrow> 'VALUE option) \<times> 'TYPE"

type_synonym ('VALUE, 'TYPE) ALPHA_EXPRESSION =
  "('TYPE ALPHABET) \<times> ('VALUE, 'TYPE) EXPRESSION"

abbreviation expr_body :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> (('VALUE, 'TYPE) BINDING \<Rightarrow> 'VALUE option)" where
"expr_body x \<equiv> fst (snd x)"

abbreviation expr_type :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> 'TYPE" where
"expr_type x \<equiv> snd (snd x)"

abbreviation expr_alpha :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('TYPE ALPHABET)" where
"expr_alpha \<equiv> fst"

notation expr_alpha ("\<alpha>e")

context GEN_PRED
begin

subsection {* Expressions *}

text {* We require expressions to be defined for well formed bindings. *}

definition WF_ALPHA_EXPR :: "('VALUE, 'TYPE) ALPHA_EXPRESSION set" where
"WF_ALPHA_EXPR \<equiv> {e. \<alpha>e e \<in> WF_ALPHABET 
                   \<and> (\<forall> b \<in> WF_BINDING. \<exists> v. expr_body e b = Some v \<and> v : expr_type e)
                   \<and> (\<forall> b1 \<in> WF_BINDING. \<forall> b2 \<in> WF_BINDING. 
                      b1 \<cong> b2 on \<alpha>e e \<longrightarrow> expr_body e b1 = expr_body e b2)}"

subsection {* Operators *}

definition VarE :: "'TYPE VAR \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION" where
"VarE v \<equiv> ({v}, (\<lambda> b. Some (b v), var_type v))"

subsection {* Predicates *}

(*
definition ExprP :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"expr_type e = BoolType \<longrightarrow> ExprP e \<equiv> e" 
*)

definition EqualP :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"e \<in> WF_ALPHA_EXPR \<and> f \<in> WF_ALPHA_EXPR \<longrightarrow> 
 EqualP e f = (\<alpha>e e \<union> \<alpha>e f, {b. b \<in> WF_BINDING \<and> (expr_body e b = expr_body f b)})"

notation EqualP (infixr "==p" 150)

abbreviation EqualVP :: "'TYPE VAR \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"EqualVP v e \<equiv> EqualP (VarE v) e"

notation EqualVP (infixr "=p" 150)

subsubsection {* Alphabet Theorems *}

lemma VarP_alphabet [simp]: "\<alpha>e (VarE v) = {v}"
  by (simp add:VarE_def)

lemma EqualP_alphabet [simp]: 
"\<lbrakk> e \<in> WF_ALPHA_EXPR; f \<in> WF_ALPHA_EXPR \<rbrakk> \<Longrightarrow> \<alpha> (e ==p f) = \<alpha>e e \<union> \<alpha>e f"
  by (simp add:EqualP_def)

subsubsection {* Closure Theorems *}

lemma VarE_closure[simp]:
"VarE v \<in> WF_ALPHA_EXPR"
  by (simp add:VarE_def WF_ALPHA_EXPR_def WF_BINDING_def beta_equiv_def alpha_closure var)

lemma EqualP_closure[simp]: 
"\<lbrakk> e \<in> WF_ALPHA_EXPR; f \<in> WF_ALPHA_EXPR \<rbrakk> \<Longrightarrow>
 e ==p f \<in> WF_ALPHA_PREDICATE"
  apply (simp add:EqualP_def WF_ALPHA_EXPR_def WF_ALPHA_PREDICATE_def WF_BINDING_SET_def)
  apply (simp add:alpha_closure var beta_equiv_union)
  apply (auto)
done
  
subsubsection {* Equality Theorems *}

lemma EqualP_refl: "e \<in> WF_ALPHA_EXPR \<Longrightarrow> taut (e ==p e)"
  apply(insert EqualP_closure [where e="e" and f="e"])
  apply(simp add:Tautology_def EqualP_def WF_ALPHA_PREDICATE_def TrueP_def)
done

lemma EqualP_sym: 
"\<lbrakk> e \<in> WF_ALPHA_EXPR; f \<in> WF_ALPHA_EXPR; taut (e ==p f)\<rbrakk> 
 \<Longrightarrow> taut (f ==p e)"
  apply(insert EqualP_closure [where e="e" and f="f"])
  apply(insert EqualP_closure [where e="f" and f="e"])
  apply(simp add:Tautology_def EqualP_def WF_ALPHA_PREDICATE_def TrueP_def)
  apply(force)
done

lemma EqualP_trans: 
"\<lbrakk> e \<in> WF_ALPHA_EXPR; f \<in> WF_ALPHA_EXPR; g \<in> WF_ALPHA_EXPR; taut (e ==p f); taut (f ==p g)\<rbrakk> 
 \<Longrightarrow> taut (e ==p g)"
  apply(insert EqualP_closure [where e="e" and f="f"])
  apply(insert EqualP_closure [where e="f" and f="g"])
  apply(insert EqualP_closure [where e="e" and f="g"])
  apply(simp add:Tautology_def EqualP_def WF_ALPHA_PREDICATE_def TrueP_def)
  apply(force)
done

declare EqualP_def [eval]
declare VarE_def [eval]

end
end