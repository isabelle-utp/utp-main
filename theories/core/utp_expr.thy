(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_pred.thy                                                         *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Basic Expressions *}

theory utp_expr
imports  utp_pred utp_unrest utp_sorts
begin

text {* The type which an expression holds should be the maximal type, if such a notion exists *}
type_synonym ('VALUE, 'TYPE) EXPRESSION = "('TYPE * ('VALUE, 'TYPE) BINDING_FUN)"

context PRED
begin

definition expr_type :: "('VALUE, 'TYPE) EXPRESSION \<Rightarrow> 'TYPE" ("\<tau>e") where
"expr_type e = fst e"

definition expr_bfun :: "('VALUE, 'TYPE) EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) BINDING_FUN" where
"expr_bfun = snd"

lemma expr_simps [simp]:
  "expr_bfun (t,f) = f"
  "expr_type (t,f) = t"
  by (simp_all add:expr_type_def expr_bfun_def)

definition etype_rel :: "('VALUE, 'TYPE) EXPRESSION \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":e:" 50) where
"etype_rel e t \<equiv> \<forall>b\<in>WF_BINDING. expr_bfun e b : t"

definition UNREST_EXPR :: "('TYPE VAR) set \<Rightarrow> ('VALUE, 'TYPE) EXPRESSION \<Rightarrow> bool" where
"UNREST_EXPR vs f \<equiv> (\<forall> b1 \<in> WF_BINDING . \<forall> b2 \<in> WF_BINDING . expr_bfun f (b1 \<oplus> b2 on vs) = expr_bfun f b1)" 

text {* A well-formed expression must produce a well-typed value for every binding, and non well-formed bindings yield an fixed arbitrary well-typed value *}

definition WF_EXPRESSION :: "('VALUE, 'TYPE) EXPRESSION set" where
"WF_EXPRESSION = {f. \<forall>b. if (b \<in> WF_BINDING) then expr_bfun f b : (expr_type f) else expr_bfun f b = default (expr_type f)}"

definition WF_EXPRESSION_OVER ::
  "('TYPE VAR) set \<Rightarrow>
   ('VALUE, 'TYPE) EXPRESSION set" where
"WF_EXPRESSION_OVER vs = {e . e \<in> WF_EXPRESSION \<and> UNREST_EXPR (VAR - vs) e}"

subsection {* Operators *}

subsubsection {* Well-formed expression builders *}

definition wfexpr ::
"('VALUE, 'TYPE) EXPRESSION \<Rightarrow> 
 ('VALUE, 'TYPE) EXPRESSION" where
"wfexpr f \<equiv> (expr_type f, \<lambda> b. if (b \<in> WF_BINDING) then expr_bfun f b else default (expr_type f))"

subsubsection {* Equality *}

definition EqualP :: 
"('VALUE, 'TYPE) EXPRESSION \<Rightarrow> 
 ('VALUE, 'TYPE) EXPRESSION \<Rightarrow> 
 ('VALUE, 'TYPE) PREDICATE" where
"e \<in> WF_EXPRESSION \<and> f \<in> WF_EXPRESSION \<longrightarrow>
EqualP e f = {b \<in> WF_BINDING. expr_bfun e b = expr_bfun f b}"

notation EqualP (infixr "==p" 200)

definition VarE :: "'TYPE VAR \<Rightarrow> ('VALUE, 'TYPE) EXPRESSION" where
"VarE x \<equiv> wfexpr (type x, \<lambda> b. b x)"

definition LitE :: "'TYPE \<Rightarrow> 'VALUE \<Rightarrow> ('VALUE, 'TYPE) EXPRESSION" where
"LitE t v \<equiv> wfexpr (t, \<lambda> b. v)"

definition DefaultE :: "'TYPE \<Rightarrow> ('VALUE, 'TYPE) EXPRESSION" where
"DefaultE t \<equiv> LitE t (default t)"

definition SubstE :: 
"('VALUE, 'TYPE) EXPRESSION \<Rightarrow> 
 ('VALUE, 'TYPE) EXPRESSION \<Rightarrow> 
 'TYPE VAR \<Rightarrow> 
 ('VALUE, 'TYPE) EXPRESSION" ("_[_|_]" [200]) where
"f \<in> WF_EXPRESSION \<and> v \<in> WF_EXPRESSION \<longrightarrow>
SubstE f v x = wfexpr (expr_type f, \<lambda> b. expr_bfun f (b(x := expr_bfun v b)))"

definition SubstPE ::
"('VALUE, 'TYPE) PREDICATE \<Rightarrow> 
 ('VALUE, 'TYPE) EXPRESSION \<Rightarrow> 
 'TYPE VAR \<Rightarrow> 
 ('VALUE, 'TYPE) PREDICATE" ("_[_|_]" [200]) where
"p[v|x] \<equiv> (\<exists>p {x} . p \<and>p (VarE x ==p v))"

subsection {* Theorems *}

subsubsection {* Well-formed expression properties *}

lemma WF_EXPRESSION_bfun [simp]:
  "e \<in> WF_EXPRESSION \<Longrightarrow> expr_bfun e b : expr_type e"
  apply (simp add:WF_EXPRESSION_def, case_tac "b \<in> WF_BINDING")
  apply (simp_all add:default_type)
done

lemma EXPRESSION_eqI [intro]:
  "\<lbrakk> expr_type e = expr_type f; \<forall> b. expr_bfun e b = expr_bfun f b \<rbrakk> \<Longrightarrow>
  e = f"
  by (case_tac e, case_tac f, auto)

(* It would be nice to have this as a typing rule, but it
   confuses the HO unifier... *)

theorem WF_EXPRESSION_type: 
"\<lbrakk> e \<in> WF_EXPRESSION; e :e: t; b \<in> WF_BINDING \<rbrakk> \<Longrightarrow>
expr_bfun e b : t"
  by (simp add:WF_EXPRESSION_def etype_rel_def)

theorem WF_EXPRESSION_has_type [typing]: 
"\<lbrakk> e \<in> WF_EXPRESSION \<rbrakk> \<Longrightarrow> \<exists> t. e :e: t"
  apply (rule_tac x="expr_type e" in exI)
  apply (auto simp add: etype_rel_def)
done

theorem WF_EXPRESSION_default [simp]:
"\<lbrakk> e \<in> WF_EXPRESSION; b \<notin> WF_BINDING \<rbrakk> \<Longrightarrow>
 expr_bfun e b = default (expr_type e)"
  by (auto simp add:WF_EXPRESSION_def)

theorem WF_EXPRESSION_wfexpr_bfun [simp]:
"\<lbrakk> b \<in> WF_BINDING \<rbrakk> \<Longrightarrow> expr_bfun (wfexpr e) b = expr_bfun e b"
  by (simp add:wfexpr_def)

lemma WF_EXPRESSION_value_exists:
  "e \<in> WF_EXPRESSION \<Longrightarrow> \<forall> b. \<exists> v. v : \<tau>e e \<and> expr_bfun e b = v"
  apply (case_tac e)
  apply (auto simp add:WF_EXPRESSION_def LitE_def wfexpr_def)
  apply (case_tac "ba \<in> WF_BINDING")
  apply (drule_tac x="ba" in spec)
  apply (simp)
  apply (drule_tac x="ba" in spec)
  apply (simp add:default_type)
done

lemma WF_EXPRESSION_value_elim [elim]:
  "\<lbrakk> e \<in> WF_EXPRESSION;
     \<And> v b. \<lbrakk> v : \<tau>e e; expr_bfun e b = v \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow>
   P"
  by (metis WF_EXPRESSION_bfun)
 
subsubsection {* Closure Theorems *}

theorem WF_EXPRESSION_wfexpr [closure]:
"e :e: expr_type e \<Longrightarrow> wfexpr e \<in> WF_EXPRESSION"
  by (unfold WF_EXPRESSION_def wfexpr_def, auto simp add:etype_rel_def)


theorem WF_EXPRESSION_BODY_wfexpr_drop [simp]:
"e \<in> WF_EXPRESSION \<Longrightarrow> wfexpr e = e"
  apply (rule EXPRESSION_eqI)
  apply (simp_all add:WF_EXPRESSION_def wfexpr_def)
done

theorem wfexpr_idem [simp]: "wfexpr (wfexpr e) = wfexpr e"
  by (auto simp add: wfexpr_def)

theorem EqualP_closure[closure]: "\<lbrakk> e \<in> WF_EXPRESSION; f \<in> WF_EXPRESSION \<rbrakk> \<Longrightarrow> e ==p f \<in> WF_PREDICATE"
  by (auto intro:closure simp add:EqualP_def WF_EXPRESSION_def WF_PREDICATE_def WF_BINDING_def)

theorem VarE_closure[closure]: "VarE x \<in> WF_EXPRESSION"
  by (auto intro!:closure simp add:VarE_def closure WF_BINDING_def etype_rel_def)

theorem LitE_closure[closure]: 
assumes "v : t"
shows "LitE t v \<in> WF_EXPRESSION"
  by (auto intro:closure simp add:LitE_def WF_BINDING_def etype_rel_def assms)
 
theorem DefaultE_closure[closure]:
"DefaultE t \<in> WF_EXPRESSION"
  by (simp add:DefaultE_def closure default_type)

theorem SubstE_closure[closure]:
 assumes "e \<in> WF_EXPRESSION" "v \<in> WF_EXPRESSION" "v :e: type x"
 shows "(e::('VALUE,'TYPE) EXPRESSION)[v|x] \<in> WF_EXPRESSION"
  by (auto intro:closure simp add:SubstE_def WF_BINDING_def etype_rel_def assms)

theorem SubstPE_closure[closure]:
 assumes "p \<in> WF_PREDICATE" "v \<in> WF_EXPRESSION" "v :e: type x"
 shows "SubstPE p v x \<in> WF_PREDICATE"
  by (simp add:SubstPE_def closure assms)

subsubsection {* Typing Theorems *}

theorem expr_type [typing]: "e \<in> WF_EXPRESSION \<Longrightarrow> e :e: \<tau>e e"
  by (simp add:etype_rel_def)

theorem wfexpr_tau [simp]: "\<tau>e (wfexpr e) = \<tau>e e"
  by (simp add:wfexpr_def)

theorem VarE_type [typing]: "VarE x :e: type x"
  by (simp add:VarE_def WF_BINDING_def typing etype_rel_def)

theorem VarE_tau [simp]: "\<tau>e (VarE x) = type x"
  by (simp add:VarE_def)

theorem LitE_type [typing]: 
"v : t \<Longrightarrow> LitE t v :e: t"
  by (simp add:LitE_def etype_rel_def typing)

theorem LitE_tau [simp]:
"\<tau>e (LitE t e) = t"
  by (simp add:LitE_def)

theorem DefaultE_type [typing]:
"DefaultE t :e: t"
  by (simp add:DefaultE_def typing)

theorem DefaultE_tau [typing]:
"\<tau>e (DefaultE t) = t"
  by (simp add:DefaultE_def)

theorem SubstE_type [typing]:
"\<lbrakk> e \<in> WF_EXPRESSION; v \<in> WF_EXPRESSION; v :e: type x; e :e: t \<rbrakk> \<Longrightarrow>
 e[v|x] :e: t"
  by (simp add:SubstE_def etype_rel_def WF_BINDING_update1)

theorem SubstE_tau [simp]:
"\<lbrakk>e \<in> WF_EXPRESSION; v \<in> WF_EXPRESSION\<rbrakk> \<Longrightarrow> \<tau>e (SubstE e v x) = \<tau>e e"
  by (simp add:SubstE_def)

subsubsection {* @{term UNREST_EXPR} Theorems *}

theorem UNREST_EXPR_member [unrest] :
"\<lbrakk>f \<in> WF_EXPRESSION; 
 UNREST_EXPR vs f;
 b \<in> WF_BINDING;
 b' \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 expr_bfun f b = expr_bfun f (b \<oplus> b' on vs)"
  apply (simp only:WF_EXPRESSION_def)
  apply (unfold UNREST_EXPR_def)
  apply (erule_tac x="b" in ballE)
  apply (erule_tac x="b'" in ballE)
  apply (auto)
done

theorem UNREST_EXPR_empty [unrest] :
"e \<in> WF_EXPRESSION \<Longrightarrow> UNREST_EXPR {} e"
  by (simp add: UNREST_EXPR_def)

theorem UNREST_EXPR_subset [unrest] :
"\<lbrakk>UNREST_EXPR vs1 e;
 vs2 \<subseteq> vs1;
 e \<in> WF_EXPRESSION\<rbrakk> \<Longrightarrow>
 UNREST_EXPR vs2 e"
  apply (simp add:UNREST_EXPR_def)
  apply (clarify)
  apply (subgoal_tac "expr_bfun e b1 = expr_bfun e (b1 \<oplus> b2 on vs1)")
  apply (drule_tac x = "b1 \<oplus> b2 on vs2" in bspec)
  apply (simp add:closure)
  apply (drule_tac x = "b2" in bspec)
  apply (simp add:closure)
  apply (simp add:override_on_assoc)
  apply (subgoal_tac "vs2 \<union> vs1 = vs1")
  apply (auto)
done

theorem UNREST_EqualP [unrest] :
"\<lbrakk> e \<in> WF_EXPRESSION; f \<in> WF_EXPRESSION;
 UNREST_EXPR vs1 e; UNREST_EXPR vs2 f \<rbrakk> \<Longrightarrow>
 UNREST (vs1 \<inter> vs2) (e ==p f)"
  apply (auto simp add:EqualP_def)
  apply (drule_tac ?vs2.0="vs1 \<inter> vs2" in UNREST_EXPR_subset)
  apply (simp_all)
  apply (drule_tac ?vs2.0="vs1 \<inter> vs2" in UNREST_EXPR_subset)
  apply (simp_all)
  apply (simp add:UNREST_EXPR_def UNREST_def)
  apply (safe)
  apply (rule closure)
  apply (simp_all)
done

theorem UNREST_EXPR_wfexpr [unrest]:
"UNREST_EXPR vs e \<Longrightarrow> UNREST_EXPR vs (wfexpr e)"
  by (simp add:wfexpr_def UNREST_EXPR_def closure)

theorem UNREST_EXPR_VarE [unrest] :
"UNREST_EXPR (vs - {x}) (VarE x)"
  apply (simp add:VarE_def)
  apply (rule unrest)
  apply (simp add:UNREST_EXPR_def)
done

theorem UNREST_EXPR_LitE [unrest] :
"UNREST_EXPR vs (LitE t v)"
  apply (simp add:LitE_def)
  apply (rule unrest)
  apply (simp add:UNREST_EXPR_def)
done

theorem UNREST_EXPR_SubstE [unrest] :
"\<lbrakk> f \<in> WF_EXPRESSION; v \<in> WF_EXPRESSION; v :e: type x;
   UNREST_EXPR vs1 f; UNREST_EXPR vs2 v \<rbrakk> \<Longrightarrow>
 UNREST_EXPR ((vs1 \<union> {x}) \<inter> vs2) (f[v|x])"
apply (subgoal_tac "UNREST_EXPR (vs1 \<inter> vs2) f")
apply (subgoal_tac "UNREST_EXPR ((vs1 \<union> {x}) \<inter> vs2) v")
apply (subgoal_tac "UNREST_EXPR ((vs1 \<union> {x}) \<inter> vs2 - {x}) f")
apply (simp add:SubstE_def)
apply (rule unrest)
apply (simp add:UNREST_EXPR_def)
apply (clarify)
apply (subgoal_tac "b1(x := expr_bfun v b1) \<in> WF_BINDING")
apply (simp)
apply (simp add:etype_rel_def closure)
apply (force intro:UNREST_EXPR_subset)+
done

end

subsection {* Boolean Expressions *}

context PRED_BOOL
begin

definition TrueE :: "('VALUE, 'TYPE) EXPRESSION" where
"TrueE \<equiv> LitE BoolType (MkBool True)"

definition FalseE :: "('VALUE, 'TYPE) EXPRESSION" where
"FalseE \<equiv> LitE BoolType (MkBool False)"

definition ExprP :: "('VALUE, 'TYPE) EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) PREDICATE" where
"ExprP e = LiftP (DestBool \<circ> expr_bfun e)"

definition PredE :: "('VALUE, 'TYPE) PREDICATE \<Rightarrow> ('VALUE, 'TYPE) EXPRESSION" where
"p \<in> WF_PREDICATE \<longrightarrow> 
PredE p = wfexpr (BoolType, \<lambda> b. MkBool (b \<in> p))"

definition VarP ::  "'TYPE VAR \<Rightarrow> ('VALUE, 'TYPE) PREDICATE" where
"VarP v \<equiv> LiftP (DestBool \<circ> expr_bfun (VarE v))"

subsubsection {* Closure Theorems *}

theorem TrueE_closed [closure]: "TrueE \<in> WF_EXPRESSION"
  by (auto intro:closure typing simp add:TrueE_def)

theorem FalseE_closed [closure]: "FalseE \<in> WF_EXPRESSION"
  by (auto intro:closure typing simp add:FalseE_def)

theorem ExprP_closed [closure]: 
"ExprP e \<in> WF_PREDICATE"
  by (simp add: ExprP_def closure)

theorem PredE_closed [closure]: "p \<in> WF_PREDICATE \<Longrightarrow> PredE p \<in> WF_EXPRESSION"
  apply (simp add:PredE_def)
  apply (rule closure)
  apply (simp add:etype_rel_def typing)
done

theorem VarP_closed [closure]: "VarP x \<in> WF_PREDICATE"
  by (simp add:VarP_def, rule closure)

subsubsection {* Typing Theorems *}

theorem TrueE_type [typing]: "TrueE :e: BoolType"
  apply (simp add: TrueE_def)
  apply (rule typing)+
done

theorem FalseE_type [typing]: "FalseE :e: BoolType"
  apply (simp add: FalseE_def)
  apply (rule typing)+
done

theorem PredE_type [typing]:
"p \<in> WF_PREDICATE \<longrightarrow>
PredE p :e: BoolType"
  by (auto intro:typing simp add:PredE_def etype_rel_def)

subsubsection {* Laws about booleans *}

lemma notext [elim]: "\<lbrakk> f \<noteq> g; \<And> x. f x \<noteq> g x \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

 
lemma ExprP_TrueE [simp]: "ExprP TrueE = true"
  by (simp add:ExprP_def TrueE_def LiftP_def expr_bfun_def LitE_def wfexpr_def TrueP_def)

lemma ExprP_FalseE [simp]: "ExprP FalseE = false"
  by (simp add:ExprP_def FalseE_def LiftP_def expr_bfun_def LitE_def wfexpr_def FalseP_def)


subsubsection {* @{term UNREST_EXPR} Theorems *}

theorem UNREST_EXPR_TrueE [unrest]: "UNREST_EXPR vs TrueE"
  by (simp add:TrueE_def unrest)

theorem UNREST_EXPR_FalseE [unrest]: "UNREST_EXPR vs FalseE"
  by (simp add:FalseE_def unrest)

theorem UNREST_ExprP [unrest]:
"\<lbrakk> e \<in> WF_EXPRESSION; UNREST_EXPR vs e; e :e: BoolType \<rbrakk> \<Longrightarrow> UNREST vs (ExprP e)"
  apply (simp add:ExprP_def)
  apply (rule unrest)
  oops

theorem UNREST_EXPR_PredE [unrest]: 
"\<lbrakk>p \<in> WF_PREDICATE; UNREST vs p\<rbrakk> \<Longrightarrow> UNREST_EXPR vs (PredE p)"
  apply (simp add:PredE_def)
  apply (rule unrest)
  apply (simp add:UNREST_EXPR_def UNREST_def WF_PREDICATE_def)
  apply (safe)
  apply (rule_tac f="MkBool" and g="MkBool" in cong, simp)
  apply (auto)
  apply (metis override_on_cancel1 override_on_cancel2)
done
  
theorem UNREST_VarP [unrest]:
"UNREST (vs - {x}) (VarP x)"
apply (simp add:VarP_def)
apply (rule_tac ?vs1.0="{x}" in UNREST_LiftP_alt)
apply (auto)
apply (simp add:WF_BINDING_PRED_def VarE_def wfexpr_def binding_equiv_def) 
done


end
end