(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alpha_expr.thy                                                   *)
(* Author: Frank Zeyda and Simon Foster, University of York (UK)              *)
(******************************************************************************)

header {* Alphabetised Expressions *}

theory utp_alpha_expr
imports "../core/utp_pred" "../core/utp_expr" "../core/utp_laws" "../core/utp_synonyms" utp_alphabet utp_alpha_pred
begin

type_synonym ('VALUE, 'TYPE) ALPHA_EXPRESSION =
  "('TYPE ALPHABET) \<times> ('VALUE, 'TYPE) EXPRESSION"

context ALPHA_PRED
begin

abbreviation ealphabet ::
  "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow>
   ('TYPE ALPHABET)" where
"ealphabet e \<equiv> (fst e)"

notation ealphabet ("\<alpha>\<epsilon>")

abbreviation expression ::
  "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow>
   ('VALUE, 'TYPE) EXPRESSION" where
"expression e \<equiv> (snd e)"

notation expression ("\<epsilon>")

definition WF_ALPHA_EXPRESSION ::
  "('VALUE, 'TYPE) ALPHA_EXPRESSION set" where
"WF_ALPHA_EXPRESSION =
 {e . (\<alpha>\<epsilon> e) \<in> WF_ALPHABET \<and> (\<epsilon> e) \<in> WF_EXPRESSION_OVER (\<alpha>\<epsilon> e)}"

subsection {* Operators *}

definition EqualA :: 
"('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> 
 ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> 
 ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"e \<in> WF_ALPHA_EXPRESSION \<and> f \<in> WF_ALPHA_EXPRESSION \<longrightarrow>
EqualA e f = (\<alpha>\<epsilon> e \<union> \<alpha>\<epsilon> f, EqualP (\<epsilon> e) (\<epsilon> f))"

notation EqualA (infixr "==\<alpha>" 150)

definition VarAE ::
"'TYPE VAR \<Rightarrow>
 ('VALUE, 'TYPE) ALPHA_EXPRESSION" where
"VarAE x = ({x}, VarE x)"

definition LitAE :: "'TYPE \<Rightarrow> 'VALUE \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION" where
"LitAE t v \<equiv> ({}, LitE t v)"

definition SubstA ::
"('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> 
 ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> 
 'TYPE VAR \<Rightarrow> 
 ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_[_|_]\<alpha>" [200]) where
"p[v|x]\<alpha> \<equiv> (\<exists>-\<alpha> {x} . p \<and>\<alpha> (VarAE x ==\<alpha> v))"

definition SubstAE ::
"('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> 
 ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> 
 'TYPE VAR \<Rightarrow> 
 ('VALUE, 'TYPE) ALPHA_EXPRESSION" ("_[_|_]\<alpha>\<epsilon>" [200]) where
"f[v|x]\<alpha>\<epsilon> \<equiv> ((\<alpha>\<epsilon> f - {x}) \<union> \<alpha>\<epsilon> v, \<epsilon> f [\<epsilon> v|x])"

subsection {* Theorems *}

subsubsection {* Closure Theorems *}

theorem WF_EXPRESSION_WF_ALPHA_EXPRESSION [closure] :
"e \<in> WF_ALPHA_EXPRESSION \<Longrightarrow> \<epsilon> e \<in> WF_EXPRESSION"
  by (simp add: WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)

theorem WF_ALPHA_EXPRESSION_UNREST_EXPR [closure] :
"e \<in> WF_ALPHA_EXPRESSION \<Longrightarrow> UNREST_EXPR (VAR - \<alpha>\<epsilon> e) (\<epsilon> e)"
apply (simp add: WF_ALPHA_EXPRESSION_def)
apply (simp add: WF_EXPRESSION_OVER_def)
done

theorem EqualA_closure [closure]: 
"\<lbrakk> e \<in> WF_ALPHA_EXPRESSION; f \<in> WF_ALPHA_EXPRESSION \<rbrakk> \<Longrightarrow> 
 e ==\<alpha> f \<in> WF_ALPHA_PREDICATE"
  apply (simp add:EqualA_def WF_ALPHA_PREDICATE_def WF_ALPHA_EXPRESSION_def)
  apply (auto intro:unrest closure simp add:WF_PREDICATE_OVER_def WF_EXPRESSION_OVER_def)
done

theorem VarAE_closure [closure]:
"VarAE x \<in> WF_ALPHA_EXPRESSION"
  by (simp add:VarAE_def WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def UNREST_EXPR_VarE, simp add:closure)

theorem LitAE_closure [closure]:
"v : t \<Longrightarrow> LitAE t v \<in> WF_ALPHA_EXPRESSION"
  by (simp add:LitAE_def WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def unrest, simp add:closure)

theorem SubstA_closure [closure]:
"\<lbrakk> p \<in> WF_ALPHA_PREDICATE; 
   v \<in> WF_ALPHA_EXPRESSION;
   \<epsilon> v :e: type x \<rbrakk> \<Longrightarrow>
  p[v|x]\<alpha> \<in> WF_ALPHA_PREDICATE"
  by (simp add:SubstA_def closure)

theorem SubstAE_closure [closure]:
"\<lbrakk> f \<in> WF_ALPHA_EXPRESSION; 
   v \<in> WF_ALPHA_EXPRESSION;
   \<epsilon> v :e: type x \<rbrakk> \<Longrightarrow>
  f[v|x]\<alpha>\<epsilon> \<in> WF_ALPHA_EXPRESSION"
  apply (simp add:SubstAE_def WF_ALPHA_PREDICATE_def WF_ALPHA_EXPRESSION_def closure)
  apply (auto intro:unrest closure simp add:WF_PREDICATE_OVER_def WF_EXPRESSION_OVER_def)
done

subsubsection {* Alphabet Theorems *}

theorem EqualA_alphabet [alphabet]:
"\<lbrakk>e \<in> WF_ALPHA_EXPRESSION; 
 f \<in> WF_ALPHA_EXPRESSION\<rbrakk> \<Longrightarrow>
 \<alpha> (e ==\<alpha> f) = \<alpha>\<epsilon> e \<union> \<alpha>\<epsilon> f"
  by (simp add:EqualA_def)

theorem VarAE_alphabet [alphabet]:
"\<alpha>\<epsilon> (VarAE x) = {x}"
  by (simp add:VarAE_def)

theorem LitAE_alphabet [alphabet]:
"\<alpha>\<epsilon> (LitAE t v) = {}"
  by (simp add:LitAE_def)

theorem SubstA_alphabet [alphabet]:
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE; 
 v \<in> WF_ALPHA_EXPRESSION\<rbrakk> \<Longrightarrow>
\<alpha>(p[v|x]\<alpha>) = (\<alpha> p \<union> \<alpha>\<epsilon> v) - {x}"
  by (simp add:SubstA_def alphabet closure)

theorem SubstAE_alphabet [alphabet]:
"\<lbrakk>f \<in> WF_ALPHA_EXPRESSION; 
 v \<in> WF_ALPHA_EXPRESSION\<rbrakk> \<Longrightarrow>
\<alpha>\<epsilon>(f[v|x]\<alpha>\<epsilon>) = (\<alpha>\<epsilon> f - {x}) \<union> \<alpha>\<epsilon> v"
  by (simp add:SubstAE_def)

subsubsection {* Typing theorems *}

theorem expr_type [typing]: "e \<in> WF_ALPHA_EXPRESSION \<Longrightarrow> \<epsilon> e :e: \<tau>e (\<epsilon> e)"
  by (simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def typing)

end

subsection {* Boolean Expressions *}

context ALPHA_PRED_BOOL
begin

subsubsection {* Operators *}

definition TrueAE :: "('VALUE, 'TYPE) ALPHA_EXPRESSION" ("true") where
"TrueAE \<equiv> ({}, TrueE)"

definition FalseAE :: "('VALUE, 'TYPE) ALPHA_EXPRESSION" ("false") where
"FalseAE \<equiv> ({}, FalseE)"

definition PredAE :: 
"('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> 
('VALUE, 'TYPE) ALPHA_EXPRESSION" where
"p \<in> WF_ALPHA_PREDICATE \<longrightarrow> 
PredAE p = (\<alpha> p, PredE (\<pi> p))"

definition VarA :: 
"'TYPE VAR \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("&_") where
"VarA x \<equiv> ({x}, VarP x)"

subsubsection {* Closure theorems *}

theorem TrueAE_closure [closure]: "TrueAE \<in> WF_ALPHA_EXPRESSION"
  by (simp add:TrueAE_def WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def unrest, simp add:closure)

theorem FalseAE_closure [closure]: "FalseAE \<in> WF_ALPHA_EXPRESSION"
  by (simp add:FalseAE_def WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def unrest, simp add:closure)

theorem PredAE_closure [closure]: "p \<in> WF_ALPHA_PREDICATE \<Longrightarrow> PredAE p \<in> WF_ALPHA_EXPRESSION"
  apply (simp add:PredAE_def WF_ALPHA_EXPRESSION_def WF_ALPHA_PREDICATE_def WF_EXPRESSION_OVER_def WF_PREDICATE_OVER_def)
  apply (auto intro:unrest closure)
done

theorem VarA_closure [closure]: "VarA x \<in> WF_ALPHA_PREDICATE"
  apply (simp add:VarA_def WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (simp add:closure unrest)
done

subsubsection {* Alphabet Theorems *}

theorem TrueAE_alphabet [alphabet]: "\<alpha>\<epsilon> TrueAE = {}"
  by (simp add:TrueAE_def)

theorem FalseAE_alphabet [alphabet]: "\<alpha>\<epsilon> FalseAE = {}"
  by (simp add:FalseAE_def)

theorem PredAE_alphabet [alphabet]: 
"p \<in> WF_ALPHA_PREDICATE \<Longrightarrow> 
\<alpha>\<epsilon> (PredAE p) = \<alpha> p"
  by (simp add:PredAE_def)

theorem VarA_alphabet [alphabet]: "\<alpha> (VarA x) = {x}"
  by (simp add:VarA_def)

end
end