(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_shallow_expr.thy                                                 *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Shallowly Embedded Polymorphic Expressions *}

theory utp_poly_expr
imports 
  "../core/utp_pred"
  "../tactics/utp_pred_tac"
  "../core/utp_expr"
  "../tactics/utp_expr_tac"
  "../core/utp_rel"
  utp_poly_value
  utp_poly_var
begin

ML {*
  structure evalp =
    Named_Thms (val name = @{binding evalp} val description = "evalp theorems")
*}

setup evalp.setup


text {* In theory we could have a single unified type for both predicates and expressions.
        This might have some advantages, but a big disadvantage is that we would no longer
        be able to give specific class instances for predicates, such as showing that
        refinement forms a partial order, or that predicates form a Kleene Algebra. As
        a result we opt for keeping the types separate. *}

default_sort type

subsection {* Polymorphic Expression Basic Syntax *}

typedef ('a, 'm) WF_PEXPRESSION = "UNIV :: ('m WF_BINDING \<Rightarrow> 'a) set" ..

declare Rep_WF_PEXPRESSION [simp]
declare Rep_WF_PEXPRESSION_inverse [simp]
declare Abs_WF_PEXPRESSION_inverse [simp]

notation Rep_WF_PEXPRESSION ("\<lbrakk>_\<rbrakk>\<^sub>*")

lemma Rep_WF_PEXPRESSION_intro [intro]:
  "(\<And> b. \<lbrakk>x\<rbrakk>\<^sub>*b = \<lbrakk>y\<rbrakk>\<^sub>*b) \<Longrightarrow> x = y"
  by (auto simp add: Rep_WF_PEXPRESSION_inject[THEN sym])

definition WF_PEXPRESSION_type :: 
  "('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 'm UTYPE" ("\<tau>\<^sub>*") where
"WF_PEXPRESSION_type e = TypeU(TYPE('a))"

text {* The lifting package allows us to define operators on a typedef
by lifting operators on the underlying type. The following command sets
up the @{term "WF_PREDICATE"} type for lifting. *}

setup_lifting type_definition_WF_PEXPRESSION

definition UNREST_PEXPR :: "('m VAR) set \<Rightarrow> ('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> bool" where
"UNREST_PEXPR vs e \<equiv> (\<forall> b1 b2. \<lbrakk>e\<rbrakk>\<^sub>*(b1 \<oplus>\<^sub>b b2 on vs) = \<lbrakk>e\<rbrakk>\<^sub>* b1)" 

definition LitPE :: "'a \<Rightarrow> ('a, 'm :: VALUE) WF_PEXPRESSION" where
"LitPE v = Abs_WF_PEXPRESSION (\<lambda> b. v)"

lemma EvalPE_LitPE [eval]:
  "\<lbrakk>LitPE v\<rbrakk>\<^sub>*b = v"
  by (simp add:LitPE_def)

lemma UNREST_LitPE [unrest]:
  "UNREST_PEXPR vs (LitPE v)"
  by (simp add:UNREST_PEXPR_def LitPE_def)

lemma WF_PEXPRESSION_tau [typing]:
  fixes v :: "('a, 'm :: VALUE) WF_PEXPRESSION"
  shows "\<tau>\<^sub>*(v) = TypeU(TYPE('a))"
  by (simp add:WF_PEXPRESSION_type_def)

definition pevar_compat :: 
  "('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 'm VAR \<Rightarrow> bool" (infix "\<rhd>\<^sub>*" 50) where
"pevar_compat e x \<equiv> \<forall>b. InjU (\<lbrakk>e\<rbrakk>\<^sub>* b) \<rhd> x"

lemma PVAR_VAR_compat [typing]:
  fixes e :: "('a, 'm :: VALUE) WF_PEXPRESSION" 
  and   x :: "('a, 'm) PVAR"
  assumes "TYPEUSOUND('a, 'm)"
  shows "e \<rhd>\<^sub>* [x]\<^sub>*"
  apply (auto simp add:pevar_compat_def PVAR_VAR_def assms typing var_compat_def)
  apply (simp add:assms defined)
done

definition WVarPE :: "'m VAR \<Rightarrow> ('m SIGTYPE, 'm :: VALUE) WF_PEXPRESSION" where
"WVarPE x = Abs_WF_PEXPRESSION (\<lambda> b. \<Sigma> \<langle>b\<rangle>\<^sub>b x : vtype x)"

lemma EvalPE_WVarPE [eval]:
  "\<lbrakk>WVarPE x\<rbrakk>\<^sub>*b = (\<Sigma> \<langle>b\<rangle>\<^sub>b x : vtype x)"
  by (simp add:WVarPE_def)

lemma UNREST_WVarPE [unrest]:
  "x \<notin> vs \<Longrightarrow> UNREST_PEXPR vs (WVarPE x)"
  by (simp add:WVarPE_def UNREST_PEXPR_def)

definition VarPE :: "'m VAR \<Rightarrow> ('a, 'm :: VALUE) WF_PEXPRESSION" where
"VarPE x = Abs_WF_PEXPRESSION (\<lambda> b. ProjU (\<langle>b\<rangle>\<^sub>b x))"

lemma EvalPE_VarPE [eval]:
  "\<lbrakk>VarPE x\<rbrakk>\<^sub>*b = ProjU (\<langle>b\<rangle>\<^sub>b x)"
  by (simp add:VarPE_def)

lemma UNREST_VarPE [unrest]:
  "x \<notin> vs \<Longrightarrow> UNREST_PEXPR vs (VarPE x)"
  by (simp add:VarPE_def UNREST_PEXPR_def)

abbreviation PVarPE :: "('a, 'm :: VALUE) PVAR \<Rightarrow> ('a, 'm) WF_PEXPRESSION" where
"PVarPE x \<equiv> VarPE [x]\<^sub>*"

lemma EvalPE_PVarPE [eval]:
  "\<lbrakk>PVarPE x\<rbrakk>\<^sub>*b = ProjU (\<langle>b\<rangle>\<^sub>b (PVAR_VAR x))"
  by (simp add:VarPE_def)

definition ErasePE :: 
  "('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> ('m SIGTYPE, 'm) WF_PEXPRESSION" where
"ErasePE v = Abs_WF_PEXPRESSION (\<lambda> b. \<Sigma> (InjU (\<lbrakk>v\<rbrakk>\<^sub>*b)) : TYPEU('a))"

(*  *)

lemma EvalPE_ErasePE [eval]:
  fixes v :: "('a, 'm :: VALUE) WF_PEXPRESSION"
  shows "\<lbrakk>ErasePE v\<rbrakk>\<^sub>*b = (\<Sigma> (InjU (\<lbrakk>v\<rbrakk>\<^sub>*b)) : TYPEU('a))"
  by (simp add:ErasePE_def)

lemma UNREST_ErasePE [unrest]:
  "UNREST_PEXPR vs v \<Longrightarrow> UNREST_PEXPR vs (ErasePE v)"
  by (simp add:UNREST_PEXPR_def ErasePE_def)

definition Op1PE :: 
  "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> ('b, 'm) WF_PEXPRESSION" where
"Op1PE f u = Abs_WF_PEXPRESSION (\<lambda> b. f (\<lbrakk>u\<rbrakk>\<^sub>*b))"

lemma EvalPE_Op1PE [eval]:
  "\<lbrakk>Op1PE f u\<rbrakk>\<^sub>*b = f (\<lbrakk>u\<rbrakk>\<^sub>*b)"
  by (simp add:Op1PE_def)

lemma UNREST_Op1PE [unrest]:
  "UNREST_PEXPR vs u \<Longrightarrow> UNREST_PEXPR vs (Op1PE f u)"
  by (simp add:UNREST_PEXPR_def Op1PE_def)

definition 
  Op2PE :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 
            ('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 
            ('b, 'm) WF_PEXPRESSION \<Rightarrow> 
            ('c, 'm) WF_PEXPRESSION" where
"Op2PE f u v = Abs_WF_PEXPRESSION (\<lambda> b. f (\<lbrakk>u\<rbrakk>\<^sub>*b) (\<lbrakk>v\<rbrakk>\<^sub>*b))"

lemma EvalPE_Op2PE [eval]:
  "\<lbrakk>Op2PE f u v\<rbrakk>\<^sub>*b = f (\<lbrakk>u\<rbrakk>\<^sub>*b) (\<lbrakk>v\<rbrakk>\<^sub>*b)"
  by (simp add:Op2PE_def)

definition 
  Op3PE :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 
            ('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 
            ('b, 'm) WF_PEXPRESSION \<Rightarrow> 
            ('c, 'm) WF_PEXPRESSION \<Rightarrow>
            ('d, 'm) WF_PEXPRESSION" where
"Op3PE f u v w = Abs_WF_PEXPRESSION (\<lambda> b. f (\<lbrakk>u\<rbrakk>\<^sub>*b) (\<lbrakk>v\<rbrakk>\<^sub>*b) (\<lbrakk>w\<rbrakk>\<^sub>*b))"

lemma EvalPE_Op3PE [eval]:
  "\<lbrakk>Op3PE f u v w\<rbrakk>\<^sub>*b = f (\<lbrakk>u\<rbrakk>\<^sub>*b) (\<lbrakk>v\<rbrakk>\<^sub>*b) (\<lbrakk>w\<rbrakk>\<^sub>*b)"
  by (simp add:Op3PE_def)

abbreviation "EqualPE \<equiv> Op2PE (op =)"

definition PExprE :: 
"('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 'm WF_EXPRESSION" ("\<lbrakk>_\<rbrakk>\<down>\<^sub>e") where
"PExprE f = Abs_WF_EXPRESSION (InjU \<circ> Rep_WF_PEXPRESSION f)"

lemma PExprE_rep_eq:
  fixes e :: "('a, 'm :: VALUE) WF_PEXPRESSION" 
  assumes "TYPEUSOUND('a, 'm)"
  shows "\<langle>PExprE e\<rangle>\<^sub>e b = InjU (Rep_WF_PEXPRESSION e b)"
  apply (subgoal_tac "(InjU \<circ> Rep_WF_PEXPRESSION e) \<in> WF_EXPRESSION")
  apply (simp add:PExprE_def)
  apply (auto simp add:WF_EXPRESSION_def)
  apply (rule_tac x="TYPEU('a)" in exI)
  apply (insert assms)
  apply (auto simp add:TypeUSound_def)
done

lemma EvalE_PExprE [evale]:
  fixes e :: "('a, 'm :: VALUE) WF_PEXPRESSION" 
  assumes "TYPEUSOUND('a, 'm)"
  shows "\<lbrakk>PExprE e\<rbrakk>\<epsilon>b = InjU (\<lbrakk>e\<rbrakk>\<^sub>*b)"
  by (simp add:EvalE_def PExprE_rep_eq assms)

lemma PExprE_type [typing]:
  fixes e :: "('a, 'm :: VALUE) WF_PEXPRESSION" 
  assumes "TYPEUSOUND('a, 'm)" 
  and "t = \<tau>\<^sub>* e"
  shows "PExprE e :\<^sub>e t"
  apply (simp add: etype_rel_def PExprE_rep_eq assms WF_PEXPRESSION_type_def)
  apply (metis TypeUSound_def assms dtype_type)
done

lemma UNREST_PExprE [unrest]:
  fixes e :: "('a, 'm :: VALUE) WF_PEXPRESSION" 
  assumes "TYPEUSOUND('a, 'm)" "UNREST_PEXPR vs e"
  shows "UNREST_EXPR vs (PExprE e)"
  apply (insert assms)
  apply (simp add:UNREST_PEXPR_def UNREST_EXPR_def PExprE_rep_eq)
done

text {* The following functions and rules mechanise marshalling between predicates
        and boolean valued expressions *}

definition PExprP :: 
  "(bool, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 'm WF_PREDICATE" ("\<lbrakk>_\<rbrakk>\<down>") where
"PExprP e = mkPRED {b. \<lbrakk>e\<rbrakk>\<^sub>* b}"

declare [[coercion PExprP]]

lemma EvalP_PExprP [eval]:
  "\<lbrakk>\<lbrakk>e\<rbrakk>\<down>\<rbrakk>b = \<lbrakk>e\<rbrakk>\<^sub>* b"
  by (simp add:PExprP_def EvalP_def)

abbreviation PVarP ::
  "(bool, 'm :: BOOL_SORT) PVAR \<Rightarrow> 'm WF_PREDICATE" where
"PVarP x \<equiv> PExprP (PVarPE x)" 

definition PredPE ::
  "'m WF_PREDICATE \<Rightarrow> (bool, 'm :: VALUE) WF_PEXPRESSION" where
"PredPE p = Abs_WF_PEXPRESSION (\<lambda> b. b \<in> destPRED p)"

lemma EvalPE_PExprP [eval]:
  "\<lbrakk>PredPE p\<rbrakk>\<^sub>*b = \<lbrakk>p\<rbrakk>b"
  by (simp add:PredPE_def EvalP_def)

lemma PExprP_inv [evalp]: "PredPE (PExprP p) = p"
  by (simp add: PExprP_def PredPE_def)

lemma PredPE_inv [evalp]: "\<lbrakk>PredPE e\<rbrakk>\<down> = e"
  by (simp add: PExprP_def PredPE_def)

lemma PExprP_VarPE [evalp]: 
  "\<lbrakk>VarPE x\<rbrakk>\<down> = VarP x"
  by (utp_pred_tac, utp_expr_tac)



abbreviation PredOp1PE :: 
  "('m WF_PREDICATE \<Rightarrow> 'm WF_PREDICATE) \<Rightarrow>
   (bool, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> (bool, 'm) WF_PEXPRESSION" where
"PredOp1PE f v \<equiv> PredPE (f (PExprP v))"

abbreviation PredOp2PE :: 
  "('m WF_PREDICATE \<Rightarrow> 'm WF_PREDICATE \<Rightarrow> 'm WF_PREDICATE) \<Rightarrow>
   (bool, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 
   (bool, 'm) WF_PEXPRESSION \<Rightarrow> 
   (bool, 'm) WF_PEXPRESSION" where
"PredOp2PE f u v \<equiv> PredPE (f (PExprP u) (PExprP v))"

abbreviation PredOp3PE :: 
  "('m WF_PREDICATE \<Rightarrow> 'm WF_PREDICATE \<Rightarrow> 'm WF_PREDICATE \<Rightarrow> 'm WF_PREDICATE) \<Rightarrow>
   (bool, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 
   (bool, 'm) WF_PEXPRESSION \<Rightarrow> 
   (bool, 'm) WF_PEXPRESSION \<Rightarrow>
   (bool, 'm) WF_PEXPRESSION" where
"PredOp3PE f u v w \<equiv> PredPE (f (PExprP u) (PExprP v) (PExprP w))"

subsection {* Polymorphic Relational Operators *}

abbreviation AssignRPE ::
  "('a, 'm :: VALUE) PVAR \<Rightarrow> ('a, 'm) WF_PEXPRESSION \<Rightarrow> (bool, 'm) WF_PEXPRESSION" where
"AssignRPE x v \<equiv> PredPE (AssignR [x]\<^sub>* (PExprE v))"

abbreviation WAssignRPE ::
  "('m :: VALUE) VAR \<Rightarrow> 'm WF_EXPRESSION \<Rightarrow> (bool, 'm) WF_PEXPRESSION" where
"WAssignRPE x v \<equiv> PredPE (AssignR x v)"

lemma PExprE_compat [typing]:
fixes x :: "('a, 'm :: VALUE) PVAR" and e :: "('a, 'm) WF_PEXPRESSION"
assumes "TYPEUSOUND('a, 'm)"
shows "PExprE e \<rhd>\<^sub>e [x]\<^sub>*"
  apply (simp add:evar_compat_def assms PExprE_rep_eq typing)
  apply (auto simp add:pevar_compat_def PVAR_VAR_def assms typing var_compat_def)
  apply (simp add:assms defined)
done

subsection {* Boolean Expressions *}

text {* Boolean values are the only values for which we do not postulate the
        existence of BOOL_SORT. This is so that the predicate model depends
        only on VALUE. We defined them by simply lifting the associated
        predicate operators. *}

abbreviation "NotPE       \<equiv> PredOp1PE NotP"
abbreviation "AndPE       \<equiv> PredOp2PE AndP"
abbreviation "OrPE        \<equiv> PredOp2PE OrP"
abbreviation "ImpliesPE   \<equiv> PredOp2PE ImpliesP"
abbreviation "IffPE       \<equiv> PredOp2PE IffP"
abbreviation "RefPE       \<equiv> PredOp2PE RefP"
abbreviation "ClosurePE   \<equiv> PredOp1PE ClosureP"
abbreviation "ExistsPE xs \<equiv> PredOp1PE (CONST ExistsP xs)"
abbreviation "ForallPE xs \<equiv> PredOp1PE (CONST ForallP xs)"

abbreviation TruePE :: "(bool, 'm :: BOOL_SORT) WF_PEXPRESSION" where
"TruePE \<equiv> LitPE True"

abbreviation FalsePE :: "(bool, 'm :: BOOL_SORT) WF_PEXPRESSION" where
"FalsePE \<equiv> LitPE False"

lemma TruePE_tau: "\<tau>\<^sub>* TruePE = BoolType"
  by (simp add:WF_PEXPRESSION_type_def)

lemma FalsePE_tau: "\<tau>\<^sub>* FalsePE = BoolType"
  by (simp add:WF_PEXPRESSION_type_def)

lemma PExprP_TruePE [evalp]: 
  "\<lbrakk>TruePE\<rbrakk>\<down> = TrueP"
  by (utp_pred_tac)

lemma PExprP_FalsePE [evalp]: 
  "\<lbrakk>FalsePE\<rbrakk>\<down> = FalseP"
  by (utp_pred_tac)

subsection {* Less than class *}

class LESS_THAN =
  fixes uless    :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and   uless_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

abbreviation "LessPE \<equiv> Op2PE uless"
abbreviation "LessEqPE \<equiv> Op2PE uless_eq"

subsection {* Minus class *}

class MINUS =
  fixes utminus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

abbreviation "MinusPE \<equiv> Op2PE utminus"

subsection {* Integer Expressions *}

abbreviation IntPE :: "int \<Rightarrow> (int, 'a :: INT_SORT) WF_PEXPRESSION" where
"IntPE \<equiv> LitPE"

abbreviation PlusPE :: "(int, 'm :: INT_SORT) WF_PEXPRESSION \<Rightarrow>
                        (int, 'm) WF_PEXPRESSION \<Rightarrow>
                        (int, 'm) WF_PEXPRESSION" where
"PlusPE u v \<equiv> Op2PE (op +) u v"

subsection {* List Expressions *}

abbreviation NilPE :: "('a list, 'm :: LIST_SORT) WF_PEXPRESSION" where
"NilPE \<equiv> LitPE []"

abbreviation ConsPE :: 
  "('a, 'm :: LIST_SORT) WF_PEXPRESSION \<Rightarrow> 
   ('a list, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a list, 'm) WF_PEXPRESSION" where
"ConsPE \<equiv> Op2PE (op #)"

abbreviation ConcatPE ::
  "('a list, 'm :: LIST_SORT) WF_PEXPRESSION \<Rightarrow> 
   ('a list, 'm :: LIST_SORT) WF_PEXPRESSION \<Rightarrow> 
   ('a list, 'm :: LIST_SORT) WF_PEXPRESSION" where
"ConcatPE \<equiv> Op2PE (op @)"

abbreviation PrefixPE::
  "('a list, 'm :: {BOOL_SORT, LIST_SORT}) WF_PEXPRESSION \<Rightarrow> 
   ('a list, 'm) WF_PEXPRESSION \<Rightarrow> (bool, 'm) WF_PEXPRESSION" where
"PrefixPE \<equiv> Op2PE prefixeq"

instantiation list :: (type) LESS_THAN
begin

definition uless_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"uless_list xs ys = prefix xs ys"

definition uless_eq_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"uless_eq_list xs ys = prefixeq xs ys"

instance ..
end

declare uless_list_def [simp]
declare uless_eq_list_def [simp]

instantiation list :: (type) MINUS
begin

definition utminus_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"utminus_list xs ys = drop (length ys) xs"

instance ..
end

declare utminus_list_def [simp]

subsection {* Finite Set Expressions *}

abbreviation FEmptyPE :: "('a fset, 'm :: FSET_SORT) WF_PEXPRESSION" where
"FEmptyPE \<equiv> LitPE \<lbrace>\<rbrace>"

abbreviation FInsertPE :: 
  "('a, 'm :: FSET_SORT) WF_PEXPRESSION \<Rightarrow> 
   ('a fset, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a fset, 'm) WF_PEXPRESSION" where
"FInsertPE \<equiv> Op2PE finsert"

abbreviation FUnionPE ::
  "('a fset, 'm :: FSET_SORT) WF_PEXPRESSION \<Rightarrow> 
   ('a fset, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a fset, 'm) WF_PEXPRESSION" where
"FUnionPE \<equiv> Op2PE funion"

abbreviation FInterPE ::
  "('a fset, 'm :: FSET_SORT) WF_PEXPRESSION \<Rightarrow> 
   ('a fset, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a fset, 'm) WF_PEXPRESSION" where
"FInterPE \<equiv> Op2PE finter"

abbreviation FMemberPE ::
  "('a, 'm :: {BOOL_SORT, FSET_SORT}) WF_PEXPRESSION \<Rightarrow> 
   ('a fset, 'm) WF_PEXPRESSION \<Rightarrow> 
   (bool, 'm) WF_PEXPRESSION" where
"FMemberPE \<equiv> Op2PE fmember"

abbreviation FNotMemberPE ::
  "('a, 'm :: {BOOL_SORT, FSET_SORT}) WF_PEXPRESSION \<Rightarrow> 
   ('a fset, 'm) WF_PEXPRESSION \<Rightarrow> 
   (bool, 'm) WF_PEXPRESSION" where
"FNotMemberPE \<equiv> Op2PE fnmember"

abbreviation IntersyncPE ::
  "('a fset, 'm :: {FSET_SORT, LIST_SORT}) WF_PEXPRESSION \<Rightarrow>
   ('a list, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a list, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a list fset, 'm) WF_PEXPRESSION" where
"IntersyncPE \<equiv> Op3PE intersync"

lemma FUnionPE_type: 
  "\<tau>\<^sub>* (FUnionPE (xs :: ('a fset, 'm :: FSET_SORT) WF_PEXPRESSION) ys) 
   = FSetType TYPEU('a)"
  by (simp add: WF_PEXPRESSION_type_def)

subsection {* Action Expressions *}

definition PEV :: "'a CHANNEL \<Rightarrow> 'a \<Rightarrow> ('m :: EVENT_SORT) EVENT" where
"PEV c v = EV (fst c) TYPEU('a) (InjU v)"

abbreviation EventPE ::
  "'a CHANNEL \<Rightarrow> ('a, 'm :: EVENT_SORT) WF_PEXPRESSION 
              \<Rightarrow> ('m EVENT, 'm) WF_PEXPRESSION" where
"EventPE n v \<equiv> Op1PE (PEV n) v"

subsection {* Renaming *}

definition RenamePE ::
  "('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow>
   'm VAR_RENAME \<Rightarrow>
   ('a, 'm) WF_PEXPRESSION" where
"RenamePE e ss = Abs_WF_PEXPRESSION (\<lbrakk>e\<rbrakk>\<^sub>* \<circ> (RenameB (inv\<^sub>s ss)))"

lemma EvalPE_RenamePE [eval]:
  "\<lbrakk>RenamePE e ss\<rbrakk>\<^sub>* = \<lbrakk>e\<rbrakk>\<^sub>* \<circ> (RenameB (inv\<^sub>s ss))"
  by (simp add:RenamePE_def)

lemma RenamePE_PVarPE [urename]:
  "RenamePE (VarPE x) ss = VarPE (\<langle>ss\<rangle>\<^sub>s x)"
  by (auto simp add:eval)

(*
lemma RenamePE_PVarPE [urename]:
  "RenamePE (PVarPE x) ss = PVarPE (\<langle>ss\<rangle>\<^sub>s\<^sub>* x)"
  apply (simp add:urename)
  by (auto simp add:evale)
*)

lemma RenamePE_LitPE [urename]:
  "RenamePE (LitPE v) ss = LitPE v"
  by (auto simp add:eval)

lemma RenamePE_Op1PE [urename]:
  "RenamePE (Op1PE f v) ss = Op1PE f (RenamePE v ss)"
  by (auto simp add:eval)

lemma RenamePE_Op2PE [urename]:
  "RenamePE (Op2PE f u v) ss = Op2PE f (RenamePE u ss) (RenamePE v ss)"
  by (auto simp add:eval)

lemma RenamePE_Op3PE [urename]:
  "RenamePE (Op3PE f u v w) ss = Op3PE f (RenamePE u ss) (RenamePE v ss) (RenamePE w ss)"
  by (auto simp add:eval)

subsection {* Substitution *}

definition SubstPE :: 
"('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 
 ('b, 'm) WF_PEXPRESSION \<Rightarrow> 
 'm VAR \<Rightarrow> 
 ('a, 'm) WF_PEXPRESSION" where
"SubstPE f v x = Abs_WF_PEXPRESSION (\<lambda> b. \<lbrakk>f\<rbrakk>\<^sub>* (b(x :=\<^sub>b InjU (\<lbrakk>v\<rbrakk>\<^sub>* b))))"

abbreviation PSubstPE :: 
"('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 
 ('b, 'm) WF_PEXPRESSION \<Rightarrow> 
 ('b, 'm) PVAR \<Rightarrow> 
 ('a, 'm) WF_PEXPRESSION" where
"PSubstPE f v x \<equiv> SubstPE f v (PVAR_VAR x)"

lemma EvalPE_SubstPE [eval]:
  "\<lbrakk>SubstPE e v x\<rbrakk>\<^sub>*b = \<lbrakk>e\<rbrakk>\<^sub>* (b(x :=\<^sub>b InjU (\<lbrakk>v\<rbrakk>\<^sub>* b)))"
  by (simp add:SubstPE_def)

lemma PExprP_SubstPE [evalp]:
  fixes v :: "('a, 'm :: VALUE) WF_PEXPRESSION"
  assumes "v \<rhd>\<^sub>* x" "TYPEUSOUND('a, 'm)"
  shows "\<lbrakk>SubstPE e v x\<rbrakk>\<down> = SubstP \<lbrakk>e\<rbrakk>\<down> \<lbrakk>v\<rbrakk>\<down>\<^sub>e x"
  by (simp add:SubstPE_def PExprP_def SubstP_def PExprE_rep_eq assms)

lemma SubstPE_VarPE [usubst]:
  fixes v :: "('a, 'm :: VALUE) WF_PEXPRESSION"
  assumes "v \<rhd>\<^sub>* x" "TYPEUSOUND('a, 'm)"
  shows "SubstPE (VarPE x) v x = v"
  using assms by (auto simp add:eval pevar_compat_def)

lemma PSubstPE_PVarPE [usubst]:
  fixes v :: "('a, 'm :: VALUE) WF_PEXPRESSION"
  assumes "TYPEUSOUND('a, 'm)"
  shows "PSubstPE (PVarPE x) v x = v"
  using assms by (simp add:usubst typing)

lemma SubstPE_LitPE [usubst]:
  "SubstPE (LitPE v) x e = LitPE v"
  by (auto simp add:eval)

lemma SubstPE_Op1PE [usubst]:
  "SubstPE (Op1PE f v) x e = Op1PE f (SubstPE v x e)"
  by (auto simp add:eval)

lemma SubstPE_Op2PE [usubst]:
  "SubstPE (Op2PE f u v) e x = Op2PE f (SubstPE u e x) (SubstPE v e x)"
  by (auto simp add:eval)

lemma SubstPE_Op3PE [usubst]:
  "SubstPE (Op3PE f u v w) e x= Op3PE f (SubstPE u e x) (SubstPE v e x) (SubstPE w e x)"
  by (auto simp add:eval)

subsection {* Anciliary Laws *}

lemma MkBool_compat_bool [typing]:
  "MkBool v \<rhd> [x :: (bool, 'm :: BOOL_SORT) PVAR]\<^sub>*"
  by (simp add:var_compat_def typing defined)

lemma MkInt_compat_int [typing]:
  "MkInt v \<rhd> [x :: (int, 'm :: INT_SORT) PVAR]\<^sub>*"
  by (simp add:var_compat_def typing defined)

end