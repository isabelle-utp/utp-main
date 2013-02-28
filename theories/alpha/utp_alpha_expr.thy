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
  "../core/utp_laws" 
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

typedef (open) 'VALUE WF_ALPHA_EXPRESSION = "WF_ALPHA_EXPRESSION :: 'VALUE ALPHA_EXPRESSION set"
  apply (auto simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)
  apply (rule_tac x="(\<lbrace>\<rbrace>, DefaultE someType)" in exI)
  apply (auto intro:unrest simp add:DefaultE_def)
done

declare Rep_WF_ALPHA_EXPRESSION [simp]
declare Rep_WF_ALPHA_EXPRESSION_inverse [simp]
declare Abs_WF_ALPHA_EXPRESSION_inverse [simp]

lemma Rep_WF_ALPHA_EXPRESSION_intro [intro]:
  "Rep_WF_ALPHA_EXPRESSION x = Rep_WF_ALPHA_EXPRESSION y \<Longrightarrow> x = y"
  by (simp add:Rep_WF_ALPHA_EXPRESSION_inject)

lemma Rep_WF_ALPHA_EXPRESSION_elim [elim]:
  "\<lbrakk> x = y; Rep_WF_ALPHA_EXPRESSION x = Rep_WF_ALPHA_EXPRESSION y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

setup_lifting type_definition_WF_ALPHA_EXPRESSION

definition expr_alpha ::
  "'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 'VALUE ALPHABET" where
"expr_alpha e = fst (Rep_WF_ALPHA_EXPRESSION e)"

abbreviation expression ::
  "'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 'VALUE WF_EXPRESSION" ("\<epsilon>") where
"expression e \<equiv> snd (Rep_WF_ALPHA_EXPRESSION e)"

definition alpha_expr_type ::
  "'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 'VALUE UTYPE" ("\<tau>\<^sub>\<alpha>") where
"alpha_expr_type e = \<tau>\<^sub>e (\<epsilon> e)"

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
apply (insert Rep_WF_ALPHA_EXPRESSION[of e])
apply (simp add:WF_ALPHA_EXPRESSION_def expr_alpha_def WF_EXPRESSION_OVER_def)
done

(* We can always generate a fresh variable within the context of alphabets *)
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

subsection {* Operators *}

lift_definition EqualA :: 
"'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 
 'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 
 'VALUE WF_ALPHA_PREDICATE" is
"\<lambda> e f. (\<alpha> e \<union>\<^sub>f \<alpha> f, EqualP (\<epsilon> e) (\<epsilon> f))"
proof -
  fix e1 e2
  show "(\<alpha> e1 \<union>\<^sub>f \<alpha> e2, \<epsilon> e1 ==p \<epsilon> e2) \<in> WF_ALPHA_PREDICATE"
    apply (insert WF_ALPHA_EXPRESSION_UNREST_EXPR[of e1])
    apply (insert WF_ALPHA_EXPRESSION_UNREST_EXPR[of e2])
    apply (auto intro:unrest simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def WF_EXPRESSION_def)
  done
qed

notation EqualA (infixr "==\<alpha>" 150)

lift_definition VarAE ::
"'VALUE VAR \<Rightarrow>
 'VALUE WF_ALPHA_EXPRESSION" is
"\<lambda> x. (finsert x \<lbrace>\<rbrace>, VarE x)"
  by (auto intro:unrest simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)

lift_definition LitAE :: 
  "'VALUE UTYPE \<Rightarrow> 'VALUE \<Rightarrow> 'VALUE WF_ALPHA_EXPRESSION" is
"\<lambda> t v. (\<lbrace>\<rbrace>, LitE t v)"
  by (auto intro:unrest simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)

definition ExprA ::
  "'VALUE::BOOL_SORT WF_ALPHA_EXPRESSION \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" where
"ExprA e = Abs_WF_ALPHA_PREDICATE (\<alpha> e, ExprP (\<epsilon> e))"

lemma ExprA_rep_eq:
  "e :\<^sub>\<alpha> BoolType \<Longrightarrow> Rep_WF_ALPHA_PREDICATE (ExprA e) = (\<alpha> e, ExprP (\<epsilon> e))"
  apply (subgoal_tac "(\<alpha> e, ExprP (\<epsilon> e)) \<in> WF_ALPHA_PREDICATE")
  apply (auto intro: unrest simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def ExprA_def eatype_rel_def)
done

lift_definition RenameAE ::
  "'VALUE WF_ALPHA_EXPRESSION \<Rightarrow>
   'VALUE VAR_RENAME \<Rightarrow>
   'VALUE WF_ALPHA_EXPRESSION" ("_[_]\<alpha>\<epsilon>" [200]) is
"\<lambda> e ss. (\<langle>ss\<rangle>\<^sub>s `\<^sub>f \<alpha> e, (\<epsilon> e)[ss]\<epsilon>)"
  apply (auto intro:unrest simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)
  apply (rule unrest)+
  apply (auto)
  apply (metis Diff_iff RenameP_VAR RenameP_image_minus VAR_member)
done


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

definition SubstA ::
"'VALUE WF_ALPHA_PREDICATE \<Rightarrow> 
 'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 
 'VALUE VAR \<Rightarrow> 
 'VALUE WF_ALPHA_PREDICATE" ("_[_|_]\<alpha>" [200]) where
"p[v|x]\<alpha> \<equiv> 
  Abs_WF_ALPHA_PREDICATE 
    (if (x \<in>\<^sub>f \<alpha> p) then (\<alpha> p -\<^sub>f finsert x \<lbrace>\<rbrace>) \<union>\<^sub>f \<alpha> v
                 else \<alpha> p
    , (\<pi> p)[\<epsilon> v|x])"

definition SubstAE ::
"'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 
 'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 
 'VALUE VAR \<Rightarrow> 
 'VALUE WF_ALPHA_EXPRESSION" ("_[_|_]\<alpha>\<epsilon>" [200]) where
"f[v|x]\<alpha>\<epsilon> \<equiv> 
  Abs_WF_ALPHA_EXPRESSION 
    ( (\<alpha> f -\<^sub>f finsert x \<lbrace>\<rbrace>) \<union>\<^sub>f \<alpha> v
    , SubstE (\<epsilon> f) (\<epsilon> v) x)"

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
"\<lambda> x. (finsert x \<lbrace>\<rbrace>, VarP x)"
  by (auto intro:unrest simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)

subsection {* Theorems *}

subsubsection {* Closure Theorems *}

lemma WF_ALPHA_EXPRESSION_OVER [closure]: 
  "\<epsilon> f \<in> WF_EXPRESSION_OVER \<langle>\<alpha> f\<rangle>\<^sub>f"
  by (simp add:WF_EXPRESSION_OVER_def unrest)

lemma SubstA_closure [closure]: 
  "\<lbrakk> v \<rhd>\<^sub>\<alpha> x; x \<notin>\<^sub>f \<alpha> v \<rbrakk> \<Longrightarrow> 
  (if (x \<in>\<^sub>f \<alpha> p) then (\<alpha> p -\<^sub>f finsert x \<lbrace>\<rbrace>) \<union>\<^sub>f \<alpha> v
                 else \<alpha> p
  , (\<pi> p)[\<epsilon> v|x]) \<in> WF_ALPHA_PREDICATE"
    apply (simp add: eavar_compat_def)
    apply (case_tac "x \<in>\<^sub>f \<alpha> p")
    apply (simp)
    apply (insert WF_ALPHA_PREDICATE_UNREST[of p])
    apply (insert WF_ALPHA_EXPRESSION_UNREST_EXPR[of v])
    apply (auto intro:unrest WF_ALPHA_EXPRESSION_is_SubstP_var simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
    apply (frule_tac ?vs1.0="VAR - \<langle>\<alpha> p\<rangle>\<^sub>f - {x}" and ?vs2.0="VAR - \<langle>\<alpha> v\<rangle>\<^sub>f" and p="\<pi> p" in UNREST_SubstP)
    apply (simp_all)
    apply (simp add:WF_ALPHA_EXPRESSION_is_SubstP_var)
    apply (frule_tac ?vs1.0="VAR - \<langle>\<alpha> p\<rangle>\<^sub>f - {x}" and ?vs2.0="VAR - \<langle>\<alpha> v\<rangle>\<^sub>f" and p="\<pi> p" in UNREST_SubstP_var)
    apply (auto)
    apply (metis WF_ALPHA_EXPRESSION_is_SubstP_var)
    apply (subgoal_tac "(VAR - (\<langle>\<alpha> p\<rangle>\<^sub>f - {x} \<union> \<langle>\<alpha> v\<rangle>\<^sub>f)) = ((VAR - \<langle>\<alpha> p\<rangle>\<^sub>f - {x}) \<inter> (VAR - \<langle>\<alpha> v\<rangle>\<^sub>f)) \<union> {x}")
    apply (auto)
    apply (drule UNREST_union) back
    apply (simp)
    apply (simp)
    apply (subgoal_tac "\<pi> p[\<epsilon> v|x] = \<pi> p")
    apply (simp)
    apply (rule SubstP_no_var)
    apply (simp)
    apply (simp add:WF_ALPHA_EXPRESSION_is_SubstP_var)
    apply (force intro:unrest)
    apply (force intro:unrest)
done

lemma SubstA_rep_eq:
  "\<lbrakk> v \<rhd>\<^sub>\<alpha> x; x \<notin>\<^sub>f \<alpha> v \<rbrakk> \<Longrightarrow> 
  Rep_WF_ALPHA_PREDICATE (p[v|x]\<alpha>) = 
  (if (x \<in>\<^sub>f \<alpha> p) then (\<alpha> p -\<^sub>f finsert x \<lbrace>\<rbrace>) \<union>\<^sub>f \<alpha> v
                 else \<alpha> p

  , (\<pi> p)[\<epsilon> v|x])"
  by (simp only: SubstA_def SubstA_closure Abs_WF_ALPHA_PREDICATE_inverse)

theorem SubstAE_closure [closure]:
"\<lbrakk> v \<rhd>\<^sub>\<alpha> x \<rbrakk> \<Longrightarrow>
  ( (\<alpha> f -\<^sub>f finsert x \<lbrace>\<rbrace>) \<union>\<^sub>f \<alpha> v
  , SubstE (\<epsilon> f) (\<epsilon> v) x) \<in> WF_ALPHA_EXPRESSION"
  apply (insert WF_ALPHA_EXPRESSION_UNREST_EXPR[of f])
  apply (insert WF_ALPHA_EXPRESSION_UNREST_EXPR[of v])
  apply (simp add:SubstAE_def WF_ALPHA_PREDICATE_def WF_ALPHA_EXPRESSION_def closure)
  apply (auto intro:unrest closure simp add:WF_PREDICATE_OVER_def WF_EXPRESSION_OVER_def eavar_compat_def)[1]
done

lemma SubstAE_rep_eq:
  "\<lbrakk> v \<rhd>\<^sub>\<alpha> x \<rbrakk> \<Longrightarrow>
   Rep_WF_ALPHA_EXPRESSION (f[v|x]\<alpha>\<epsilon>) = ((\<alpha> f -\<^sub>f finsert x \<lbrace>\<rbrace>) \<union>\<^sub>f \<alpha> v, SubstE (\<epsilon> f) (\<epsilon> v) x)"
  by (simp add:SubstAE_def SubstAE_closure)

subsubsection {* Alphabet Theorems *}

declare expr_alpha_def [simp]
declare pred_alphabet_def [simp]

theorem EqualA_alphabet [alphabet]:
"\<alpha> (e ==\<alpha> f) = \<alpha> e \<union>\<^sub>f \<alpha> f"
  by (simp add:EqualA.rep_eq)

theorem VarAE_alphabet [alphabet]:
"\<alpha> (VarAE x) = finsert x \<lbrace>\<rbrace>"
  by (simp add:VarAE.rep_eq)

theorem LitAE_alphabet [alphabet]:
"\<alpha> (LitAE t v) = \<lbrace>\<rbrace>"
  by (simp add:LitAE.rep_eq)

theorem ExprA_alphabet [alphabet]:
"e :\<^sub>\<alpha> BoolType \<Longrightarrow> \<alpha> (ExprA e) = \<alpha> e"
  by (simp add:ExprA_rep_eq)

theorem RenameAE_alphabet [alphabet]:
"\<alpha> e[ss]\<alpha>\<epsilon> = \<langle>ss\<rangle>\<^sub>s `\<^sub>f \<alpha> e"
  by (simp add:RenameAE.rep_eq)

theorem SubstA_alphabet [alphabet]:
"\<lbrakk> v \<rhd>\<^sub>\<alpha> x; x \<notin>\<^sub>f \<alpha> v \<rbrakk> 
  \<Longrightarrow>  \<alpha>(p[v|x]\<alpha>) = (if (x \<in>\<^sub>f \<alpha> p) then (\<alpha> p -\<^sub>f finsert x \<lbrace>\<rbrace>) \<union>\<^sub>f \<alpha> v
                     else \<alpha> p)"
  by (auto simp add:SubstA_rep_eq)

theorem SubstAE_alphabet [alphabet]:
"v \<rhd>\<^sub>\<alpha> x \<Longrightarrow> \<alpha>(f[v|x]\<alpha>\<epsilon>) = (\<alpha> f -\<^sub>f finsert x \<lbrace>\<rbrace>) \<union>\<^sub>f \<alpha> v"
  by (simp add:SubstAE_rep_eq)

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
"v : t \<Longrightarrow> LitAE t v :\<^sub>\<alpha> t"
  by (simp add:LitAE.rep_eq eatype_rel_def typing)

theorem VarAE_type [typing]:
"t = vtype x \<Longrightarrow> VarAE x :\<^sub>\<alpha> t"
  by (simp add:VarAE.rep_eq eatype_rel_def typing)

theorem RenameAE_type:
  "e :\<^sub>\<alpha> t \<Longrightarrow> e[ss]\<alpha>\<epsilon> :\<^sub>\<alpha> t" 
  by (simp add:RenameAE.rep_eq eatype_rel_def typing)

theorem expr_type [typing]: "\<epsilon> e :\<^sub>e \<tau>\<^sub>e (\<epsilon> e)"
  by (simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def typing)

theorem alpha_expr_type [typing]: "e :\<^sub>\<alpha> \<tau>\<^sub>\<alpha> e"
  by (simp add:alpha_expr_type_def typing eatype_rel_def)

subsubsection {* Definedness Theorems *}

theorem LitAE_defined [defined]: "\<lbrakk> \<D> v; v :t \<rbrakk> \<Longrightarrow> \<D> (LitAE t v)"
  by (auto simp add:LitAE.rep_eq Defined_WF_ALPHA_EXPRESSION_def defined)

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
