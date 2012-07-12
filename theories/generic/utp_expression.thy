(******************************************************************************)
(* Project: Deep Mechanisation of the UTP                                     *)
(* File: utp/generic/utp_expression.thy                                       *)
(* Author: Simon Foster and Frank Zeyda, University of York                   *)
(******************************************************************************)

header {* Generic Expressions *}

theory utp_expression
imports "../utp_types" "../utp_sorts" utp_gen_pred utp_eval_tactic utp_value
begin

type_synonym ('VALUE, 'TYPE) BINDING_VAL =
  "('VALUE, 'TYPE) BINDING \<Rightarrow> 'VALUE option"

type_synonym ('VALUE, 'TYPE) EXPRESSION =
  "('VALUE, 'TYPE) BINDING_VAL \<times> 'TYPE"

type_synonym ('VALUE, 'TYPE) ALPHA_EXPRESSION =
  "('TYPE ALPHABET) \<times> ('VALUE, 'TYPE) EXPRESSION"

abbreviation expr_body :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) BINDING_VAL" where
"expr_body x \<equiv> fst (snd x)"

abbreviation expr_type :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> 'TYPE" where
"expr_type x \<equiv> snd (snd x)"

abbreviation expr_alpha :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('TYPE ALPHABET)" where
"expr_alpha \<equiv> fst"

notation expr_alpha ("\<alpha>e")

locale GEN_EXPR = GEN_PRED "type_rel" + BOOL_VALUE "type_rel"
  for type_rel :: "'VALUE :: BOOL_SORT \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50)
begin

subsection {* Expressions *}

text {* We require expressions to be defined for well formed bindings. *}

definition WF_ALPHA_EXPR :: "('VALUE, 'TYPE) ALPHA_EXPRESSION set" where
"WF_ALPHA_EXPR \<equiv> {e. \<alpha>e e \<in> WF_ALPHABET 
                   \<and> (\<forall> b \<in> WF_BINDING. \<exists> v. expr_body e b = Some v \<and> v : expr_type e)
                   \<and> (\<forall> b1 \<in> WF_BINDING. \<forall> b2 \<in> WF_BINDING. 
                      b1 \<cong> b2 on \<alpha>e e \<longrightarrow> expr_body e b1 = expr_body e b2)}"

definition wfexpr_body :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> (('VALUE, 'TYPE) BINDING \<Rightarrow> 'VALUE)" ("\<beta>e") where
"x \<in> WF_ALPHA_EXPR \<longrightarrow> wfexpr_body x v = the (expr_body x v)"

subsection {* Operators *}

definition VarE :: "'TYPE VAR \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION" where
"VarE v \<equiv> ({v}, (\<lambda> b. Some (b v), var_type v))"

(* Should this definition using the definite description operator or should we be
   able to infer a type? *)
definition LitE :: "'VALUE \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION" where
"LitE v \<equiv> ({}, (\<lambda> b. Some v, SOME t. v : t))"

definition TrueE :: "('VALUE, 'TYPE) ALPHA_EXPRESSION" ("true") where
"TrueE \<equiv> LitE (MkBool True)"

definition FalseE :: "('VALUE, 'TYPE) ALPHA_EXPRESSION" ("false") where
"FalseE \<equiv> LitE (MkBool False)"

(* These functions for the time being are assumed to be closed, but this should change *)
definition UopE :: "('VALUE \<Rightarrow> 'VALUE) \<Rightarrow>
                    ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> 
                    ('VALUE, 'TYPE) ALPHA_EXPRESSION" where
"UopE f x = (\<alpha>e x, (\<lambda> b. Option.map f (expr_body x b), expr_type x))"

definition BopE :: "('VALUE \<Rightarrow> 'VALUE \<Rightarrow> 'VALUE) \<Rightarrow>
                    ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> 
                    ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow>
                    ('VALUE, 'TYPE) ALPHA_EXPRESSION" where
"BopE f x y = (\<alpha>e x \<union> \<alpha>e y, (\<lambda> b. case (expr_body x b,expr_body y b) 
                                    of (Some a,Some b) \<Rightarrow> Some (f a b)
                                       | _ \<Rightarrow> None), expr_type x)"

definition PredE :: "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION" where
"p \<in> WF_ALPHA_PREDICATE \<longrightarrow> PredE p = (\<alpha> p, (\<lambda> b. Some (MkBool (b \<in> \<beta> p))), BoolType)"

subsection {* Predicates *}

definition ExprP :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"(expr_type e = BoolType) \<longrightarrow> ExprP e = (\<alpha>e e , {b. b \<in> WF_BINDING \<and> (\<exists> t. (expr_body e) b = Some t \<and> DestBool t = True)})"

abbreviation VarP ::  "'TYPE VAR \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("&") where
"VarP v \<equiv> ExprP (VarE v)"

definition EqualP :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"e \<in> WF_ALPHA_EXPR \<and> f \<in> WF_ALPHA_EXPR \<longrightarrow> 
 EqualP e f = (\<alpha>e e \<union> \<alpha>e f, {b. b \<in> WF_BINDING \<and> (\<beta>e e b = \<beta>e f b)})"

notation EqualP (infixr "==p" 150)

abbreviation EqualVP :: "'TYPE VAR \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"EqualVP v e \<equiv> EqualP (VarE v) e"

notation EqualVP (infixr "=p" 150)

(* Coarse substitution *)
definition SubsP :: "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> 'TYPE VAR \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_[_|_]" [200]) where
"x \<notin> \<alpha>e e \<longrightarrow> SubsP p e x = (\<exists>-p {x} . p \<and>p (x =p e))"

subsubsection {* Closure Theorems *}

lemma ExprP_closure[closure]:
"\<lbrakk> e \<in> WF_ALPHA_EXPR; expr_type e = BoolType \<rbrakk> \<Longrightarrow> 
 ExprP e \<in> WF_ALPHA_PREDICATE"
  by (auto simp add:ExprP_def WF_ALPHA_EXPR_def WF_ALPHA_PREDICATE_def WF_BINDING_SET_def)

lemma VarE_closure[closure]:
"VarE v \<in> WF_ALPHA_EXPR"
  by (simp add:VarE_def WF_ALPHA_EXPR_def WF_BINDING_def beta_equiv_def alpha_closure var)

lemma LitE_closure[closure]:
"LitE v \<in> WF_ALPHA_EXPR"
proof -
  obtain t where "v : t" by (metis type_rel_total)
  hence "op : v (Eps (op : v))"
    by (auto intro:someI)

  thus ?thesis
    by (simp add:LitE_def alpha_closure WF_ALPHA_EXPR_def)
qed

lemma EqualP_closure[closure]: 
"\<lbrakk> e \<in> WF_ALPHA_EXPR; f \<in> WF_ALPHA_EXPR \<rbrakk> \<Longrightarrow>
 e ==p f \<in> WF_ALPHA_PREDICATE"
  apply (simp add:EqualP_def WF_ALPHA_EXPR_def WF_ALPHA_PREDICATE_def WF_BINDING_SET_def wfexpr_body_def)
  apply (simp add:alpha_closure var beta_equiv_union)
  apply (auto)
done

lemma EqualVP_closure[closure]: 
"\<lbrakk> e \<in> WF_ALPHA_EXPR; x \<notin> \<alpha>e e \<rbrakk> \<Longrightarrow>
 x =p e \<in> WF_ALPHA_PREDICATE"
  by (simp add:closure)

lemma SubsP_closure[closure]:
"\<lbrakk> p \<in> WF_ALPHA_PREDICATE; e \<in> WF_ALPHA_EXPR; x \<notin> \<alpha>e e \<rbrakk> \<Longrightarrow>
 p[e|x] \<in> WF_ALPHA_PREDICATE"
  by (simp add:SubsP_def closure alpha_closure)

subsubsection {* Alphabet Theorems *}

lemma VarP_alphabet [alphabet]: "\<alpha>e (VarE v) = {v}"
  by (simp add:VarE_def)

lemma EqualP_alphabet [alphabet]: 
"\<lbrakk> e \<in> WF_ALPHA_EXPR; f \<in> WF_ALPHA_EXPR \<rbrakk> \<Longrightarrow> \<alpha> (e ==p f) = \<alpha>e e \<union> \<alpha>e f"
  by (simp add:EqualP_def)

lemma LitE_alphabet [alphabet]:
"\<alpha>e (LitE v) = {}" by (simp add:LitE_def)

lemma ExprP_alphabet [alphabet]:
"\<lbrakk> e \<in> WF_ALPHA_EXPR; expr_type e = BoolType \<rbrakk> \<Longrightarrow> \<alpha> (ExprP e) = \<alpha>e e"
  by (simp add:ExprP_def)

lemma SubsP_alphabet [alphabet]:
"\<lbrakk> p \<in> WF_ALPHA_PREDICATE; e \<in> WF_ALPHA_EXPR; x \<notin> \<alpha>e e \<rbrakk> \<Longrightarrow> 
 \<alpha> (p[e|x]) = (\<alpha> p \<union> \<alpha>e e) - {x}"
  by (simp add:SubsP_def alphabet closure alpha_closure)

subsubsection {* Binding Theorems *}

lemma VarE_binding[simp]: "b \<in> WF_BINDING \<Longrightarrow> \<beta>e (VarE x) b = b x"
  apply(simp add:wfexpr_body_def closure)
  apply(simp add:VarE_def)
done
  
subsubsection {* Typing Theorems *}

lemma VarE_type: "expr_type (VarE v) = type v"
  by (simp add:VarE_def)

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

(*
declare EqualP_def [eval]
declare VarE_def [eval]
*)

lemma EvalP_EqualVP[eval]: "\<lbrakk> e \<in> WF_ALPHA_EXPR; b \<in> WF_BINDING \<rbrakk> \<Longrightarrow> EvalP (x =p e) b \<longleftrightarrow> (b x = \<beta>e e b)"
  apply(simp add:EvalP_def closure)
  apply(simp add:EqualP_def alpha_closure closure)
done

lemma expr_body_weaken[simp]: "\<lbrakk> e \<in> WF_ALPHA_EXPR; v \<notin> \<alpha>e e; b \<in> WF_BINDING; b' \<in> WF_BINDING \<rbrakk> \<Longrightarrow> \<beta>e e (b \<oplus> b' on {v}) = \<beta>e e b"
  apply(simp add:wfexpr_body_def)
  apply(auto simp add: WF_ALPHA_EXPR_def)
  apply(subgoal_tac "b \<oplus> b' on {v} \<cong> b on \<alpha>e e")
  apply(erule_tac ballE)
  apply(erule_tac x="b \<oplus> b' on {v}" in ballE)
  apply(erule_tac x="b" in ballE)
  apply(auto)
  apply (metis Int_empty_left Int_insert_left beta_equiv_override_2)
done

(* Quick sanity check *)
lemma SubsP_AndP: "\<lbrakk> p \<in> WF_ALPHA_PREDICATE; q \<in> WF_ALPHA_PREDICATE; e \<in> WF_ALPHA_EXPR; x \<notin> \<alpha>e e \<rbrakk> \<Longrightarrow>
       (p \<and>p q)[e|x] = p[e|x] \<and>p q[e|x]"
  apply(simp add:SubsP_def)
  apply(intro eval_intro)
  apply(blast intro:closure alpha_closure)
  apply(blast intro:closure alpha_closure)
  apply(force simp add:alphabet closure alpha_closure)
  apply(simp add:eval closure alpha_closure)
  apply(auto)
  apply(rule_tac x="b'" in bexI)
  apply(auto)
  apply(subgoal_tac "b' \<cong> b'a on {x}")
  apply (metis (hide_lams, no_types) beta_equiv_override beta_equiv_override_3 override_on_cancel3')
  apply(auto)
done

lemma SubsP_VarP: 
"\<lbrakk> e \<in> WF_ALPHA_EXPR; x \<notin> \<alpha>e e; expr_type e = BoolType; type x = BoolType \<rbrakk> 
\<Longrightarrow> (VarP x)[e|x] = ExprP e"
  apply(rule eval_intro)
  apply(simp add:closure alpha_closure VarE_type)
  apply(simp add:closure alpha_closure VarE_type)
  apply(simp add:alphabet closure alpha_closure VarE_type)
  apply(simp add:eval closure alpha_closure VarE_type SubsP_def)
  apply(rule ballI)
  apply(rule iffI)
  apply(simp add:VarE_def VarE_type)
sorry


end
end