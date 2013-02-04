(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alpha_expr.thy                                                   *)
(* Author: Frank Zeyda and Simon Foster, University of York (UK)              *)
(******************************************************************************)

header {* Alphabetised Expressions *}

theory utp_alpha_expr_2
imports "../core/utp_pred_2" "../core/utp_expr_2" "../core/utp_laws_2" "../core/utp_synonyms" utp_alphabet_2 utp_alpha_pred_2 "../tactics/utp_alpha_tac_2" "../tactics/utp_expr_tac_2"
begin

type_synonym 'VALUE ALPHA_EXPRESSION =
  "('VALUE ALPHABET) \<times> 'VALUE WF_EXPRESSION"

definition WF_ALPHA_EXPRESSION ::
  "'VALUE ALPHA_EXPRESSION set" where
"WF_ALPHA_EXPRESSION =
 {e . snd e \<in> WF_EXPRESSION_OVER \<langle>fst e\<rangle>\<^sub>f}"

typedef (open) 'VALUE WF_ALPHA_EXPRESSION = "WF_ALPHA_EXPRESSION :: 'VALUE ALPHA_EXPRESSION set"
  apply (auto simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)
  apply (rule_tac x="({}\<^sub>f, DefaultE someType)" in exI)
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

setup {*
Adhoc_Overloading.add_variant @{const_name alphabet} @{const_name expr_alpha}
*}

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
theorem WF_ALPHA_EXPRESSION_is_SubstPE_var:
  "\<exists> x'. is_SubstPE_var (\<pi> p) (\<epsilon> v) x x'"
proof -
  obtain x' where "x' \<notin> \<langle>\<alpha> p \<union>\<^sub>f \<alpha> v\<rangle>\<^sub>f" "x' \<noteq> x" "type x' = type x" "control x' = control x"
    apply (insert fresh_var[of "finsert x (\<alpha> p \<union>\<^sub>f \<alpha> v)"])
    apply (auto)
  done

  thus ?thesis
    apply (simp add:is_SubstPE_var_def)
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
"\<lambda> x. (finsert x {}\<^sub>f, VarE x)"
  by (auto intro:unrest simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)

lift_definition LitAE :: 
  "'VALUE UTYPE \<Rightarrow> 'VALUE \<Rightarrow> 'VALUE WF_ALPHA_EXPRESSION" is
"\<lambda> t v. ({}\<^sub>f, LitE t v)"
  by (auto intro:unrest simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)

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
    (if (x \<in>\<^sub>f \<alpha> p) then (\<alpha> p -\<^sub>f finsert x {}\<^sub>f) \<union>\<^sub>f \<alpha> v
                 else \<alpha> p
    , (\<pi> p)[\<epsilon> v|x])"

definition SubstAE ::
"'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 
 'VALUE WF_ALPHA_EXPRESSION \<Rightarrow> 
 'VALUE VAR \<Rightarrow> 
 'VALUE WF_ALPHA_EXPRESSION" ("_[_|_]\<alpha>\<epsilon>" [200]) where
"f[v|x]\<alpha>\<epsilon> \<equiv> 
  Abs_WF_ALPHA_EXPRESSION 
    ( (\<alpha> f -\<^sub>f finsert x {}\<^sub>f) \<union>\<^sub>f \<alpha> v
    , SubstE (\<epsilon> f) (\<epsilon> v) x)"

lift_definition TrueAE :: 
  "('VALUE :: BOOL_SORT) WF_ALPHA_EXPRESSION" ("true") is "({}\<^sub>f, TrueE)"
  by (auto intro:unrest simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)

lift_definition FalseAE :: 
  "('VALUE :: BOOL_SORT) WF_ALPHA_EXPRESSION" ("false") is "({}\<^sub>f, FalseE)"
  by (auto intro:unrest simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)

lift_definition PredAE :: 
"('VALUE :: BOOL_SORT) WF_ALPHA_PREDICATE \<Rightarrow> 
 'VALUE WF_ALPHA_EXPRESSION" is "\<lambda> p. (\<alpha> p, PredE (\<pi> p))"
  by (auto intro:unrest simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def)

lift_definition VarA :: 
"('VALUE::BOOL_SORT) VAR \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" ("&_") is
"\<lambda> x. (finsert x {}\<^sub>f, VarP x)"
  by (auto intro:unrest simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)

subsection {* Theorems *}

subsubsection {* Closure Theorems *}

lemma WF_ALPHA_EXPRESSION_OVER [closure]: 
  "\<epsilon> f \<in> WF_EXPRESSION_OVER \<langle>\<alpha> f\<rangle>\<^sub>f"
  by (simp add:WF_EXPRESSION_OVER_def unrest)

lemma SubstA_closure [closure]: 
  "\<lbrakk> \<epsilon> v \<rhd>\<^sub>e x; x \<notin> \<langle>\<alpha> v\<rangle>\<^sub>f \<rbrakk> \<Longrightarrow> 
  (if (x \<in>\<^sub>f \<alpha> p) then (\<alpha> p -\<^sub>f finsert x {}\<^sub>f) \<union>\<^sub>f \<alpha> v
                 else \<alpha> p
  , (\<pi> p)[\<epsilon> v|x]) \<in> WF_ALPHA_PREDICATE"
    apply (case_tac "x \<in>\<^sub>f \<alpha> p")
    apply (simp)
    apply (insert WF_ALPHA_PREDICATE_UNREST[of p])
    apply (insert WF_ALPHA_EXPRESSION_UNREST_EXPR[of v])
    apply (auto intro:unrest WF_ALPHA_EXPRESSION_is_SubstPE_var simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
    apply (frule_tac ?vs1.0="VAR - \<langle>\<alpha> p\<rangle>\<^sub>f - {x}" and ?vs2.0="VAR - \<langle>\<alpha> v\<rangle>\<^sub>f" and p="\<pi> p" in UNREST_SubstPE)
    apply (simp_all)
    apply (simp add:WF_ALPHA_EXPRESSION_is_SubstPE_var)
    apply (frule_tac ?vs1.0="VAR - \<langle>\<alpha> p\<rangle>\<^sub>f - {x}" and ?vs2.0="VAR - \<langle>\<alpha> v\<rangle>\<^sub>f" and p="\<pi> p" in UNREST_SubstPE_var)
    apply (auto)
    apply (metis WF_ALPHA_EXPRESSION_is_SubstPE_var)
    apply (subgoal_tac "(VAR - (\<langle>\<alpha> p\<rangle>\<^sub>f - {x} \<union> \<langle>\<alpha> v\<rangle>\<^sub>f)) = ((VAR - \<langle>\<alpha> p\<rangle>\<^sub>f - {x}) \<inter> (VAR - \<langle>\<alpha> v\<rangle>\<^sub>f)) \<union> {x}")
    apply (auto)
    apply (drule UNREST_union) back
    apply (simp)
    apply (simp)
    apply (subgoal_tac "\<pi> p[\<epsilon> v|x] = \<pi> p")
    apply (simp)
    apply (rule SubstPE_no_var)
    apply (simp)
    apply (simp add:WF_ALPHA_EXPRESSION_is_SubstPE_var)
    apply (force intro:unrest)
    apply (force intro:unrest)
done

lemma SubstA_rep_eq:
  "\<lbrakk> \<epsilon> v \<rhd>\<^sub>e x; x \<notin> \<langle>\<alpha> v\<rangle>\<^sub>f \<rbrakk> \<Longrightarrow> 
  Rep_WF_ALPHA_PREDICATE (p[v|x]\<alpha>) = 
  (if (x \<in>\<^sub>f \<alpha> p) then (\<alpha> p -\<^sub>f finsert x {}\<^sub>f) \<union>\<^sub>f \<alpha> v
                 else \<alpha> p

  , (\<pi> p)[\<epsilon> v|x])"
  apply (simp only: SubstA_def SubstA_closure Abs_WF_ALPHA_PREDICATE_inverse)
  apply (rule_tac Abs_WF_ALPHA_PREDICATE_inverse)
  apply (metis SubstA_closure)
done

theorem SubstAE_closure [closure]:
"\<lbrakk> \<epsilon> v \<rhd>\<^sub>e x \<rbrakk> \<Longrightarrow>
  ( (\<alpha> f -\<^sub>f finsert x {}\<^sub>f) \<union>\<^sub>f \<alpha> v
  , SubstE (\<epsilon> f) (\<epsilon> v) x) \<in> WF_ALPHA_EXPRESSION"
  apply (insert WF_ALPHA_EXPRESSION_UNREST_EXPR[of f])
  apply (insert WF_ALPHA_EXPRESSION_UNREST_EXPR[of v])
  apply (simp add:SubstAE_def WF_ALPHA_PREDICATE_def WF_ALPHA_EXPRESSION_def closure)
  apply (auto intro:unrest closure simp add:WF_PREDICATE_OVER_def WF_EXPRESSION_OVER_def)[1]
done

lemma SubstAE_rep_eq:
  "\<lbrakk> \<epsilon> v \<rhd>\<^sub>e x \<rbrakk> \<Longrightarrow>
   Rep_WF_ALPHA_EXPRESSION (f[v|x]\<alpha>\<epsilon>) = ((\<alpha> f -\<^sub>f finsert x {}\<^sub>f) \<union>\<^sub>f \<alpha> v, SubstE (\<epsilon> f) (\<epsilon> v) x)"
  by (simp add:SubstAE_def SubstAE_closure)

subsubsection {* Alphabet Theorems *}

declare expr_alpha_def [simp]
declare pred_alphabet_def [simp]

theorem EqualA_alphabet [alphabet]:
"\<alpha> (e ==\<alpha> f) = \<alpha> e \<union>\<^sub>f \<alpha> f"
  by (simp add:EqualA.rep_eq)

theorem VarAE_alphabet [alphabet]:
"\<alpha> (VarAE x) = finsert x {}\<^sub>f"
  by (simp add:VarAE.rep_eq)

theorem LitAE_alphabet [alphabet]:
"\<alpha> (LitAE t v) = {}\<^sub>f"
  by (simp add:LitAE.rep_eq)

theorem SubstA_alphabet [alphabet]:
"\<lbrakk> \<epsilon> v \<rhd>\<^sub>e x; x \<notin> \<langle>\<alpha> v\<rangle>\<^sub>f \<rbrakk> 
  \<Longrightarrow>  \<alpha>(p[v|x]\<alpha>) = (if (x \<in>\<^sub>f \<alpha> p) then (\<alpha> p -\<^sub>f finsert x {}\<^sub>f) \<union>\<^sub>f \<alpha> v
                     else \<alpha> p)"
  by (auto simp add:SubstA_rep_eq)

theorem SubstAE_alphabet [alphabet]:
"\<epsilon> v \<rhd>\<^sub>e x \<Longrightarrow> \<alpha>(f[v|x]\<alpha>\<epsilon>) = (\<alpha> f -\<^sub>f finsert x {}\<^sub>f) \<union>\<^sub>f \<alpha> v"
  by (simp add:SubstAE_rep_eq)

theorem TrueAE_alphabet [alphabet]: "\<alpha> TrueAE = {}\<^sub>f"
  by (simp add:TrueAE.rep_eq)

theorem FalseAE_alphabet [alphabet]: "\<alpha> FalseAE = {}\<^sub>f"
  by (simp add:FalseAE.rep_eq)

theorem PredAE_alphabet [alphabet]: 
"\<alpha> (PredAE p) = \<alpha> p"
  by (simp add:PredAE.rep_eq)

theorem VarA_alphabet [alphabet]: "\<alpha> (VarA x) = finsert x {}\<^sub>f"
  by (simp add:VarA.rep_eq)

subsubsection {* Typing theorems *}

theorem expr_type [typing]: "\<epsilon> e :\<^sub>e \<tau>\<^sub>e (\<epsilon> e)"
  by (simp add:WF_ALPHA_EXPRESSION_def WF_EXPRESSION_OVER_def typing)

declare expr_alpha_def [simp del]
declare pred_alphabet_def [simp del]

end
