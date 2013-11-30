(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alpha_expr.thy                                                   *)
(* Author: Frank Zeyda and Simon Foster, University of York (UK)              *)
(******************************************************************************)

header {* Alphabetised Expressions *}

theory utp_alpha_expr
imports 
  "../core/utp_pred" 
  "../core/utp_expr" 
  "../laws/utp_pred_laws" 
  "../core/utp_synonyms" 
  utp_alphabet 
  utp_alpha_pred 
  "../tactics/utp_alpha_tac" 
  "../tactics/utp_expr_tac"
begin

type_synonym 'VALUE ALPHA_EXPRESSION =
  "('VALUE ALPHABET) \<times> 'VALUE WF_EXPRESSION"

definition WF_ALPHA_EXPRESSION ::
  "'VALUE ALPHA_EXPRESSION set" where
"WF_ALPHA_EXPRESSION =
 {e . snd e \<in> WF_EXPRESSION_OVER \<langle>fst e\<rangle>\<^sub>f}"

typedef 'VALUE WF_ALPHA_EXPRESSION = "WF_ALPHA_EXPRESSION :: 'VALUE ALPHA_EXPRESSION set"
  morphisms DestExprA MkExprA
  apply (auto simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)
  apply (rule_tac x="(\<lbrace>\<rbrace>, DefaultE someType)" in exI)
  apply (auto intro:unrest simp add:DefaultE_def)
done

declare DestExprA [simp]
declare DestExprA_inverse [simp]
declare MkExprA_inverse [simp]

lemma DestExprA_intro [intro]:
  "DestExprA x = DestExprA y \<Longrightarrow> x = y"
  by (simp add:DestExprA_inject)

lemma DestExprA_elim [elim]:
  "\<lbrakk> x = y; DestExprA x = DestExprA y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

setup_lifting type_definition_WF_ALPHA_EXPRESSION

definition expr_alpha ::
  "'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 'VALUE ALPHABET" where
"expr_alpha e = fst (DestExprA e)"

abbreviation expression ::
  "'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 'VALUE WF_EXPRESSION" ("\<epsilon>") where
"expression e \<equiv> snd (DestExprA e)"

(*
definition alpha_expr_type ::
  "'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 'VALUE UTYPE" ("\<tau>\<^sub>\<alpha>") where
"alpha_expr_type e = \<tau>\<^sub>e (\<epsilon> e)"
*)

definition eatype_rel :: 
  "'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 'VALUE UTYPE \<Rightarrow> bool" (infix ":\<^sub>\<alpha>" 50) where
"eatype_rel e t \<equiv> \<epsilon> e :\<^sub>e t"

definition eavar_compat :: "'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 'VALUE VAR \<Rightarrow> bool" (infix "\<rhd>\<^sub>\<alpha>" 50) where
"eavar_compat e x \<equiv> \<epsilon> e \<rhd>\<^sub>e x"

setup {*
Adhoc_Overloading.add_variant @{const_name alphabet} @{const_name expr_alpha}
*}

instantiation WF_ALPHA_EXPRESSION :: (VALUE) DEFINED
begin

definition Defined_WF_ALPHA_EXPRESSION :: "'a WF_ALPHA_EXPRESSION \<Rightarrow> bool" where
"Defined_WF_ALPHA_EXPRESSION e \<equiv> \<D> (\<epsilon> e)"

instance ..

end

lemma eavar_compat_intros [intro]:
  "\<lbrakk> v :\<^sub>\<alpha> vtype x; \<D> v \<rbrakk> \<Longrightarrow> v \<rhd>\<^sub>\<alpha> x"
  "\<lbrakk> v :\<^sub>\<alpha> vtype x; \<not> aux x \<rbrakk> \<Longrightarrow> v \<rhd>\<^sub>\<alpha> x"
  by (auto simp add:eavar_compat_def eatype_rel_def Defined_WF_ALPHA_EXPRESSION_def)

lemma eavar_compat_cases [elim]:
  "\<lbrakk> v \<rhd>\<^sub>\<alpha> x; \<lbrakk> v :\<^sub>\<alpha> vtype x; \<D> v \<rbrakk> \<Longrightarrow> P
           ; \<lbrakk> v :\<^sub>\<alpha> vtype x; \<not> aux x \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto simp add:eavar_compat_def eatype_rel_def Defined_WF_ALPHA_EXPRESSION_def)

theorem WF_ALPHA_EXPRESSION_intro [intro] :
  "\<lbrakk>\<alpha> e1 = \<alpha> e2; \<epsilon> e1 = \<epsilon> e2\<rbrakk> \<Longrightarrow> e1 = e2"
  apply (case_tac e1, case_tac e2)
  apply (case_tac y, case_tac ya)
  apply (simp add:expr_alpha_def)
done

theorem WF_ALPHA_EXPRESSION_UNREST_EXPR [unrest] :
"UNREST_EXPR (VAR - \<langle>\<alpha> e\<rangle>\<^sub>f) (\<epsilon> e)"
apply (insert DestExprA[of e])
apply (simp add:WF_ALPHA_EXPRESSION_def expr_alpha_def WF_EXPRESSION_OVER_def)
done

(* We can always generate a fresh variable within the context of alphabets *)
(*
theorem WF_ALPHA_EXPRESSION_is_SubstP_var:
  "\<exists> x'. is_SubstP_var (\<pi> p) (\<epsilon> v) x x'"
proof -
  obtain x' where "x' \<notin> \<langle>\<alpha> p \<union>\<^sub>f \<alpha> v\<rangle>\<^sub>f" "x' \<noteq> x" "vtype x' = vtype x" "aux x' = aux x"
    apply (insert fresh_var[of "finsert x (\<alpha> p \<union>\<^sub>f \<alpha> v)"])
    apply (auto)
  done

  thus ?thesis
    apply (simp add:is_SubstP_var_def)
    apply (rule_tac x="x'" in exI)
    apply (auto)
    apply (insert WF_ALPHA_EXPRESSION_UNREST_EXPR[of v])
    apply (auto intro: unrest)
  done
qed
*)

subsection {* Operators *}

lift_definition EqualA :: 
"'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 
 'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 
 'VALUE WF_ALPHA_PREDICATE" is
"\<lambda> e f. (\<alpha> e \<union>\<^sub>f \<alpha> f, (\<epsilon> e) ==\<^sub>p (\<epsilon> f))"
proof -
  fix e1 e2
  show "(\<alpha> e1 \<union>\<^sub>f \<alpha> e2, \<epsilon> e1 ==\<^sub>p \<epsilon> e2) \<in> WF_ALPHA_PREDICATE"
    apply (insert WF_ALPHA_EXPRESSION_UNREST_EXPR[of e1])
    apply (insert WF_ALPHA_EXPRESSION_UNREST_EXPR[of e2])
    apply (auto intro:unrest simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def WF_EXPRESSION_def)
  done
qed

notation EqualA (infixr "==\<^sub>\<alpha>" 150)

lift_definition VarAE ::
"'VALUE VAR \<Rightarrow>
 'VALUE WF_ALPHA_EXPRESSION" ("$\<^sub>\<alpha>_" [999] 999)  is
"\<lambda> x. (finsert x \<lbrace>\<rbrace>, VarE x)"
  by (auto intro:unrest simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)

lift_definition LitAE :: 
  "'VALUE \<Rightarrow> 'VALUE WF_ALPHA_EXPRESSION" is
"\<lambda> v. (\<lbrace>\<rbrace>, LitE v)"
  by (auto intro:unrest simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)

lift_definition CoerceAE ::
  "'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 'VALUE UTYPE \<Rightarrow> 'VALUE WF_ALPHA_EXPRESSION" is
"\<lambda> e t. (\<alpha> e, CoerceE (\<epsilon> e) t)"
  by (auto intro:unrest simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)

(*
definition AppAE ::
  "'VALUE::FUNCTION_SORT WF_ALPHA_EXPRESSION \<Rightarrow> 
   'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 
   'VALUE WF_ALPHA_EXPRESSION" where
"AppAE f v = MkExprA (\<alpha> f \<union>\<^sub>f \<alpha> v, AppE (\<epsilon> f) (\<epsilon> v))"

lemma AppAE_rep_eq:
  "\<lbrakk> f :\<^sub>\<alpha> FuncType a b; v :\<^sub>\<alpha> a; \<D> f \<rbrakk> \<Longrightarrow> DestExprA (AppAE f v) = (\<alpha> f \<union>\<^sub>f \<alpha> v, AppE (\<epsilon> f) (\<epsilon> v))"
  apply (subgoal_tac "(\<alpha> f \<union>\<^sub>f \<alpha> v, AppE (\<epsilon> f) (\<epsilon> v)) \<in> WF_ALPHA_EXPRESSION")
  apply (simp add:AppAE_def)
  apply (auto intro:unrest UNREST_EXPR_subset simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def eatype_rel_def Defined_WF_ALPHA_EXPRESSION_def)
done
*)

definition ExprA ::
  "'VALUE::BOOL_SORT WF_ALPHA_EXPRESSION \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" where
"ExprA e = MkPredA (\<alpha> e, ExprP (\<epsilon> e))"

lemma ExprA_rep_eq:
  "e :\<^sub>\<alpha> BoolType \<Longrightarrow> DestPredA (ExprA e) = (\<alpha> e, ExprP (\<epsilon> e))"
  apply (subgoal_tac "(\<alpha> e, ExprP (\<epsilon> e)) \<in> WF_ALPHA_PREDICATE")
  apply (auto intro: unrest simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def ExprA_def eatype_rel_def)
done

lift_definition PermAE ::
  "'VALUE VAR_RENAME \<Rightarrow>
   'VALUE WF_ALPHA_EXPRESSION \<Rightarrow>
   'VALUE WF_ALPHA_EXPRESSION" is
"\<lambda> ss e. (\<langle>ss\<rangle>\<^sub>s `\<^sub>f \<alpha> e, ss\<bullet>(\<epsilon> e))"
  apply (auto intro:unrest simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)
  apply (rule UNREST_EXPR_RenameE_alt)
  apply (auto)
  apply (metis (mono_tags) RenameP_image_minus Rep_VAR_RENAME_VAR Rep_VAR_RENAME_inj WF_ALPHA_EXPRESSION_UNREST_EXPR image_inv_f_f)
done

setup {*
Adhoc_Overloading.add_variant @{const_name permute} @{const_name PermAE}
*}

(*
lift_definition SubstA ::
"'VALUE WF_ALPHA_PREDICATE \<Rightarrow> 
 'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 
 'VALUE UTYPE VAR \<Rightarrow> 
 'VALUE WF_ALPHA_PREDICATE" ("_[_|_]\<alpha>" [200]) is
"\<lambda> p v x. (\<alpha> p \<union>\<^sub>f \<alpha> v, (\<pi> p)[\<epsilon> v|x])"
proof -
  fix p v x
  show "(\<alpha> p \<union>\<^sub>f \<alpha> v, (\<pi> p)[\<epsilon> v|x]) \<in> WF_ALPHA_PREDICATE"
    apply (insert WF_ALPHA_PREDICATE_UNREST[of p])
    apply (insert WF_ALPHA_EXPRESSION_UNREST_EXPR[of v])
    apply (auto intro:unrest WF_ALPHA_EXPRESSION_is_SubstPE_var simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
 *) 

lift_definition SubstA ::
"'VALUE WF_ALPHA_PREDICATE \<Rightarrow> 
 'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 
 'VALUE VAR \<Rightarrow> 
 'VALUE WF_ALPHA_PREDICATE" ("_[_'/\<^sub>\<alpha>_]" [200] 200) is
"\<lambda> p v x. (if (x \<in>\<^sub>f \<alpha> p) 
              then (\<alpha> p -\<^sub>f \<lbrace>x\<rbrace>) \<union>\<^sub>f \<alpha> v
              else \<alpha> p , (\<pi> p)[\<epsilon> v/\<^sub>px])"
  apply (auto simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (rule UNREST_SubstP_simple)
  apply (rule UNREST_EXPR_subset)
  apply (rule unrest)
  apply (auto)
  apply (subst SubstP_VarP_single_UNREST)
  apply (auto)
done

lemma UNREST_SubstE_simple [unrest]: 
  assumes "vs \<sharp> v" "vs - {x} \<sharp> e"
  shows "vs \<sharp> e[v/\<^sub>ex]"
  using assms by (auto simp add:UNREST_EXPR_def SubstE.rep_eq)

lemma SubstE_VarE_single_UNREST [usubst]:
  "{x} \<sharp> v \<Longrightarrow> v[e/\<^sub>ex] = v"
  by (utp_expr_tac)

lift_definition SubstAE ::
"'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 
 'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 
 'VALUE VAR \<Rightarrow> 
 'VALUE WF_ALPHA_EXPRESSION" ("_[_'/\<^sub>\<epsilon>_]" [200] 200) is
"\<lambda> e v x. (if (x \<in>\<^sub>f \<alpha> e) 
              then (\<alpha> e -\<^sub>f \<lbrace>x\<rbrace>) \<union>\<^sub>f \<alpha> v
              else \<alpha> e , (\<epsilon> e)[\<epsilon> v/\<^sub>ex])"
  apply (auto simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)
  apply (rule UNREST_SubstE_simple)
  apply (rule UNREST_EXPR_subset)
  apply (rule unrest)
  apply (auto)
  apply (rule UNREST_EXPR_subset)
  apply (rule unrest)
  apply (auto)
  apply (subst SubstE_VarE_single_UNREST)
  apply (rule UNREST_EXPR_subset)
  apply (rule unrest)
  apply (force)
  apply (rule UNREST_EXPR_subset)
  apply (rule unrest)
  apply (force)
done

lift_definition TrueAE :: 
  "('VALUE :: BOOL_SORT) WF_ALPHA_EXPRESSION" ("true") is "(\<lbrace>\<rbrace>, TrueE)"
  by (auto intro:unrest simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)

lift_definition FalseAE :: 
  "('VALUE :: BOOL_SORT) WF_ALPHA_EXPRESSION" ("false") is "(\<lbrace>\<rbrace>, FalseE)"
  by (auto intro:unrest simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)

lift_definition PredAE :: 
"('VALUE :: BOOL_SORT) WF_ALPHA_PREDICATE \<Rightarrow> 
 'VALUE WF_ALPHA_EXPRESSION" is "\<lambda> p. (\<alpha> p, PredE (\<pi> p))"
  by (auto intro:unrest simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)

lift_definition VarA :: 
"('VALUE::BOOL_SORT) VAR \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" ("&_") is
"\<lambda> x. (\<lbrace>x\<rbrace>, VarP x)"
  by (auto intro:unrest simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)

subsection {* Theorems *}

subsubsection {* Closure Theorems *}

lemma WF_ALPHA_EXPRESSION_OVER [closure]: 
  "\<epsilon> f \<in> WF_EXPRESSION_OVER \<langle>\<alpha> f\<rangle>\<^sub>f"
  by (simp add:WF_EXPRESSION_OVER_def unrest)

subsubsection {* Alphabet Theorems *}

declare expr_alpha_def [simp]
declare pred_alphabet_def [simp]

theorem EqualA_alphabet [alphabet]:
"\<alpha> (e ==\<^sub>\<alpha> f) = \<alpha> e \<union>\<^sub>f \<alpha> f"
  by (simp add:EqualA.rep_eq)

theorem VarAE_alphabet [alphabet]:
"\<alpha> (VarAE x) = \<lbrace>x\<rbrace>"
  by (simp add:VarAE.rep_eq)

theorem LitAE_alphabet [alphabet]:
"\<alpha> (LitAE v) = \<lbrace>\<rbrace>"
  by (simp add:LitAE.rep_eq)

theorem CoerceAE_alphabet [alphabet]:
"\<alpha> (CoerceAE e t) = \<alpha> e"
  by (simp add:CoerceAE.rep_eq)

(*
theorem AppAE_alphabet [alphabet]:
"\<lbrakk> f :\<^sub>\<alpha> FuncType a b; v :\<^sub>\<alpha> a; \<D> f \<rbrakk> \<Longrightarrow> 
 \<alpha> (AppAE f v) = \<alpha> f \<union>\<^sub>f \<alpha> v"
  by (simp add:AppAE_rep_eq)
*)

theorem ExprA_alphabet [alphabet]:
"e :\<^sub>\<alpha> BoolType \<Longrightarrow> \<alpha> (ExprA e) = \<alpha> e"
  by (simp add:ExprA_rep_eq)

theorem PermAE_alphabet [alphabet]:
  fixes e :: "'a WF_ALPHA_EXPRESSION" 
  shows "\<alpha> (ss\<bullet>e) = \<langle>ss\<rangle>\<^sub>s `\<^sub>f \<alpha> e"
  by (simp add:PermAE.rep_eq)

theorem SubstA_alphabet [alphabet]:
  "\<alpha>(p[v/\<^sub>\<alpha>x]) = (if (x \<in>\<^sub>f \<alpha> p) 
                    then (\<alpha> p -\<^sub>f \<lbrace>x\<rbrace>) \<union>\<^sub>f \<alpha> v
                    else \<alpha> p)"
  by (auto simp add:SubstA.rep_eq)

theorem SubstAE_alphabet [alphabet]:
  "\<alpha>(e[v/\<^sub>\<epsilon>x]) = (if (x \<in>\<^sub>f \<alpha> e) 
                    then (\<alpha> e -\<^sub>f \<lbrace>x\<rbrace>) \<union>\<^sub>f \<alpha> v
                    else \<alpha> e)"
  by (simp add:SubstAE.rep_eq)

theorem TrueAE_alphabet [alphabet]: "\<alpha> TrueAE = \<lbrace>\<rbrace>"
  by (simp add:TrueAE.rep_eq)

theorem FalseAE_alphabet [alphabet]: "\<alpha> FalseAE = \<lbrace>\<rbrace>"
  by (simp add:FalseAE.rep_eq)

theorem PredAE_alphabet [alphabet]: 
"\<alpha> (PredAE p) = \<alpha> p"
  by (simp add:PredAE.rep_eq)

theorem VarA_alphabet [alphabet]: "\<alpha> (VarA x) = finsert x \<lbrace>\<rbrace>"
  by (simp add:VarA.rep_eq)

subsubsection {* Typing Theorems *}

theorem TrueAE_type [typing]: "TrueAE :\<^sub>\<alpha> BoolType"
  by (simp add:eatype_rel_def TrueAE.rep_eq typing)

theorem FalseAE_type [typing]: "FalseAE :\<^sub>\<alpha> BoolType"
  by (simp add:eatype_rel_def FalseAE.rep_eq typing)

theorem PredAE_type [typing]:
"PredAE p :\<^sub>\<alpha> BoolType"
  by (simp add: PredAE.rep_eq typing eatype_rel_def)

theorem LitAE_type [typing]:
"v : t \<Longrightarrow> LitAE v :\<^sub>\<alpha> t"
  by (simp add:LitAE.rep_eq eatype_rel_def typing)

theorem CoerceAE_type [typing]:
"CoerceAE e t :\<^sub>\<alpha> t"
  by (simp add:eatype_rel_def CoerceAE.rep_eq typing)

(*
theorem AppAE_type [typing]:
"\<lbrakk> f :\<^sub>\<alpha> FuncType a b; v :\<^sub>\<alpha> a; \<D> f \<rbrakk> \<Longrightarrow>
   AppAE f v :\<^sub>\<alpha> b" 
  by (simp add:eatype_rel_def AppAE_rep_eq typing Defined_WF_ALPHA_EXPRESSION_def)
*)

theorem VarAE_type [typing]:
"t = vtype x \<Longrightarrow> VarAE x :\<^sub>\<alpha> t"
  by (simp add:VarAE.rep_eq eatype_rel_def typing)

theorem RenameAE_type:
  "e :\<^sub>\<alpha> t \<Longrightarrow> (ss\<bullet>e) :\<^sub>\<alpha> t" 
  by (simp add:PermAE.rep_eq eatype_rel_def typing)

theorem alpha_expr_type [typing]: "\<exists> t. e :\<^sub>\<alpha> t"
  by (simp add:typing eatype_rel_def)

subsubsection {* Definedness Theorems *}

theorem LitAE_defined [defined]: "\<D> v \<Longrightarrow> \<D> (LitAE v)"
  by (auto simp add:LitAE.rep_eq Defined_WF_ALPHA_EXPRESSION_def defined)

theorem CoerceAE_defined [defined]: "\<D> e \<Longrightarrow> \<D> (CoerceAE e t)"
  by (auto simp add:CoerceAE.rep_eq Defined_WF_ALPHA_EXPRESSION_def defined)

theorem TrueAE_defined [defined]: "\<D> TrueAE"
  by (auto simp add:TrueAE.rep_eq Defined_WF_ALPHA_EXPRESSION_def defined)

theorem FalseAE_defined [defined]: "\<D> FalseAE"
  by (auto simp add:FalseAE.rep_eq Defined_WF_ALPHA_EXPRESSION_def defined)

theorem VarAE_defined [defined]: "aux x \<Longrightarrow> \<D> (VarAE x)"
  by (simp add:VarAE.rep_eq Defined_WF_ALPHA_EXPRESSION_def defined)

(*
theorem RenameAE_defined [defined]: "\<D> (e[ss]\<alpha>\<epsilon>) = \<D> e"
  apply (simp add:RenameAE.rep_eq Defined_WF_ALPHA_EXPRESSION_def defined)
*)

declare expr_alpha_def [simp del]
declare pred_alphabet_def [simp del]

end
