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

typedef ('a, 'm) WF_PEXPRESSION = "UNIV :: ('m WF_BINDING \<Rightarrow> 'a) set" 
morphisms DestPExpr MkPExpr ..

declare DestPExpr [simp]
declare DestPExpr_inverse [simp]
declare MkPExpr_inverse [simp]

notation DestPExpr ("\<lbrakk>_\<rbrakk>\<^sub>*")

lemma DestPExpr_intro [intro]:
  "(\<And> b. \<lbrakk>x\<rbrakk>\<^sub>*b = \<lbrakk>y\<rbrakk>\<^sub>*b) \<Longrightarrow> x = y"
  by (auto simp add: DestPExpr_inject[THEN sym])

definition WF_PEXPRESSION_type :: 
  "('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 'm UTYPE" ("\<tau>\<^sub>*") where
"WF_PEXPRESSION_type e = TYPEU('a)"

text {* The lifting package allows us to define operators on a typedef
by lifting operators on the underlying type. The following command sets
up the @{term "WF_PREDICATE"} type for lifting. *}

setup_lifting type_definition_WF_PEXPRESSION

instantiation WF_PEXPRESSION :: (DEFINED,VALUE) DEFINED
begin

definition Defined_WF_PEXPRESSION :: "('a, 'b) WF_PEXPRESSION \<Rightarrow> bool" where
"Defined_WF_PEXPRESSION e = (\<forall> b. \<D> (\<lbrakk>e\<rbrakk>\<^sub>* b))"

instance ..
end

definition UNREST_PEXPR :: "('m VAR) set \<Rightarrow> ('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> bool" where
"UNREST_PEXPR vs e \<equiv> (\<forall> b1 b2. \<lbrakk>e\<rbrakk>\<^sub>*(b1 \<oplus>\<^sub>b b2 on vs) = \<lbrakk>e\<rbrakk>\<^sub>* b1)" 

definition LitPE :: "'a \<Rightarrow> ('a, 'm :: VALUE) WF_PEXPRESSION" where
"LitPE v = MkPExpr (\<lambda> b. v)"

lemma EvalPE_LitPE [eval,evalp]:
  "\<lbrakk>LitPE v\<rbrakk>\<^sub>*b = v"
  by (simp add:LitPE_def)

lemma LitPE_range [simp]:
  "range \<lbrakk>LitPE v\<rbrakk>\<^sub>* = {v}"
  by (auto simp add:eval)

lemma LitPE_defined [defined]:
  "\<D> x \<Longrightarrow> \<D> (LitPE x)"
  by (simp add:Defined_WF_PEXPRESSION_def LitPE_def)

lemma UNREST_LitPE [unrest]:
  "UNREST_PEXPR vs (LitPE v)"
  by (simp add:UNREST_PEXPR_def LitPE_def)

lemma WF_PEXPRESSION_tau [typing]:
  fixes v :: "('a, 'm :: VALUE) WF_PEXPRESSION"
  shows "\<tau>\<^sub>*(v) = TypeU(TYPE('a))"
  by (simp add:WF_PEXPRESSION_type_def)

definition pevar_compat :: 
  "('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> ('a, 'm) PVAR \<Rightarrow> bool" (infix "\<rhd>\<^sub>*" 50) where
"pevar_compat e x \<equiv> \<forall>b. InjU (\<lbrakk>e\<rbrakk>\<^sub>* b) \<rhd> x\<down>"

lemma PVAR_VAR_compat_naux [typing]:
  fixes e :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION" 
  and   x :: "('a, 'm) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "\<not> pvaux x"
  shows "e \<rhd>\<^sub>* x"
  by (auto simp add:pevar_compat_def PVAR_VAR_def assms typing var_compat_def)

lemma PVAR_VAR_compat [typing]:
  fixes e :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION" 
  and   x :: "('a, 'm) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "\<D> e"
  shows "e \<rhd>\<^sub>* x"
  using assms
  apply (auto simp add:pevar_compat_def var_compat_def Defined_WF_PEXPRESSION_def)
  apply (auto intro: typing defined)
done

definition WVarPE :: "'m VAR \<Rightarrow> ('m SIGTYPE, 'm :: VALUE) WF_PEXPRESSION" where
"WVarPE x = MkPExpr (\<lambda> b. \<Sigma> \<langle>b\<rangle>\<^sub>b x : vtype x)"

lemma EvalPE_WVarPE [eval,evalp]:
  "\<lbrakk>WVarPE x\<rbrakk>\<^sub>*b = (\<Sigma> \<langle>b\<rangle>\<^sub>b x : vtype x)"
  by (simp add:WVarPE_def)

lemma UNREST_WVarPE [unrest]:
  "x \<notin> vs \<Longrightarrow> UNREST_PEXPR vs (WVarPE x)"
  by (simp add:WVarPE_def UNREST_PEXPR_def)

definition VarPE :: "'m VAR \<Rightarrow> ('a, 'm :: VALUE) WF_PEXPRESSION" where
"VarPE x = MkPExpr (\<lambda> b. ProjU (\<langle>b\<rangle>\<^sub>b x))"

lemma EvalPE_VarPE [eval,evalp]:
  "\<lbrakk>VarPE x\<rbrakk>\<^sub>*b = ProjU (\<langle>b\<rangle>\<^sub>b x)"
  by (simp add:VarPE_def)

lemma UNREST_VarPE [unrest]:
  "x \<notin> vs \<Longrightarrow> UNREST_PEXPR vs (VarPE x)"
  by (simp add:VarPE_def UNREST_PEXPR_def)

definition PVarPE :: "('a, 'm :: VALUE) PVAR \<Rightarrow> ('a, 'm) WF_PEXPRESSION" where
"PVarPE x \<equiv> VarPE x\<down>"

lemma EvalPE_PVarPE [eval,evalp]:
  "\<lbrakk>PVarPE x\<rbrakk>\<^sub>*b = ProjU (\<langle>b\<rangle>\<^sub>b x\<down>)"
  by (simp add:VarPE_def PVarPE_def)

lemma PVarPE_defined_aux [defined]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "pvaux x"
  shows "\<D> (PVarPE x)"
  using assms by (auto intro:defined typing simp add:Defined_WF_PEXPRESSION_def eval)

definition ErasePE :: 
  "('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> ('m SIGTYPE, 'm) WF_PEXPRESSION" where
"ErasePE v = MkPExpr (\<lambda> b. \<Sigma> (InjU (\<lbrakk>v\<rbrakk>\<^sub>*b)) : TYPEU('a))"

lemma EvalPE_ErasePE [eval]:
  fixes v :: "('a, 'm :: VALUE) WF_PEXPRESSION"
  shows "\<lbrakk>ErasePE v\<rbrakk>\<^sub>*b = (\<Sigma> (InjU (\<lbrakk>v\<rbrakk>\<^sub>*b)) : TYPEU('a))"
  by (simp add:ErasePE_def)

lemma UNREST_ErasePE [unrest]:
  "UNREST_PEXPR vs v \<Longrightarrow> UNREST_PEXPR vs (ErasePE v)"
  by (simp add:UNREST_PEXPR_def ErasePE_def)

definition ProdPE ::
  "('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 
   ('b, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow>
   (('a * 'b), 'm) WF_PEXPRESSION" where
"ProdPE x y = MkPExpr (\<lambda> b. (\<lbrakk>x\<rbrakk>\<^sub>* b, \<lbrakk>y\<rbrakk>\<^sub>* b))"

lemma EvalPE_ProdPE [eval]:
  "\<lbrakk>ProdPE x y\<rbrakk>\<^sub>*b = (\<lbrakk>x\<rbrakk>\<^sub>* b, \<lbrakk>y\<rbrakk>\<^sub>* b)"
  by (simp add:ProdPE_def)

lemma UNREST_ProdPE [unrest]:
  "\<lbrakk> UNREST_PEXPR vs x; UNREST_PEXPR vs y \<rbrakk> \<Longrightarrow> UNREST_PEXPR vs (ProdPE x y)"
  by (simp add:UNREST_PEXPR_def EvalPE_ProdPE)

lemma ProdPE_defined [defined]:
  "\<lbrakk> \<D> x; \<D> y \<rbrakk> \<Longrightarrow> \<D> (ProdPE x y)"
  by (simp add:Defined_WF_PEXPRESSION_def EvalPE_ProdPE defined)

lemma ProdPE_range:
  "range \<lbrakk>ProdPE x y\<rbrakk>\<^sub>* = {(\<lbrakk>x\<rbrakk>\<^sub>*b, \<lbrakk>y\<rbrakk>\<^sub>*b)|b. True}"
  by (simp add:image_def EvalPE_ProdPE)

lemma ProdPE_Dom_uncurry [defined]:
  "\<lbrakk> \<And>b. \<D> (f (\<lbrakk>x\<rbrakk>\<^sub>* b) (\<lbrakk>y\<rbrakk>\<^sub>* b)) \<rbrakk> \<Longrightarrow>
   range \<lbrakk>ProdPE x y\<rbrakk>\<^sub>* \<subseteq> Dom (uncurry f)"
  by (auto simp add:Dom_def EvalPE_ProdPE)

definition Op1PE :: 
  "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> ('b, 'm) WF_PEXPRESSION" where
"Op1PE f u = MkPExpr (\<lambda> b. f (\<lbrakk>u\<rbrakk>\<^sub>*b))"

lemma EvalPE_Op1PE [eval]:
  "\<lbrakk>Op1PE f u\<rbrakk>\<^sub>*b = f (\<lbrakk>u\<rbrakk>\<^sub>*b)"
  by (simp add:Op1PE_def)

lemma UNREST_Op1PE [unrest]:
  "UNREST_PEXPR vs u \<Longrightarrow> UNREST_PEXPR vs (Op1PE f u)"
  by (simp add:UNREST_PEXPR_def Op1PE_def)

lemma Op1PE_defined [defined]:
  "\<lbrakk> \<D> x; range \<lbrakk>x\<rbrakk>\<^sub>* \<subseteq> Dom f \<rbrakk> \<Longrightarrow> \<D> (Op1PE f x)"
  by (auto simp add:Defined_WF_PEXPRESSION_def EvalPE_Op1PE Dom_def)

abbreviation 
  Op2PE :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 
            ('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 
            ('b, 'm) WF_PEXPRESSION \<Rightarrow> 
            ('c, 'm) WF_PEXPRESSION" where
"Op2PE f u v \<equiv> Op1PE (uncurry f) (ProdPE u v)"

abbreviation 
  Op3PE :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 
            ('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 
            ('b, 'm) WF_PEXPRESSION \<Rightarrow> 
            ('c, 'm) WF_PEXPRESSION \<Rightarrow>
            ('d, 'm) WF_PEXPRESSION" where
"Op3PE f u v w \<equiv> Op1PE (uncurry (uncurry f)) (ProdPE (ProdPE u v) w)"

abbreviation "EqualPE \<equiv> Op2PE (op =)"

definition PExprE :: 
"('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 'm WF_EXPRESSION" where
"PExprE f = Abs_WF_EXPRESSION (InjU \<circ> DestPExpr f)"

setup {*
Adhoc_Overloading.add_variant @{const_name erase} @{const_name PExprE}
*}

lemma PExprE_rep_eq:
  fixes e :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION" 
  assumes "TYPEUSOUND('a, 'm)"
  shows "\<langle>PExprE e\<rangle>\<^sub>e b = InjU (DestPExpr e b)"
  apply (subgoal_tac "(InjU \<circ> DestPExpr e) \<in> WF_EXPRESSION")
  apply (simp add:PExprE_def)
  apply (auto simp add:WF_EXPRESSION_def)
  apply (rule_tac x="TYPEU('a)" in exI)
  apply (insert assms)
  apply (auto intro:typing)
done

lemma EvalE_PExprE [eval, evale]:
  fixes e :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION" 
  assumes "TYPEUSOUND('a, 'm)"
  shows "\<lbrakk>e\<down>\<rbrakk>\<^sub>eb = InjU (\<lbrakk>e\<rbrakk>\<^sub>*b)"
  by (simp add:EvalE_def PExprE_rep_eq assms)

lemma PExprE_type [typing]:
  fixes e :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION" 
  assumes "TYPEUSOUND('a, 'm)" 
  and "t = \<tau>\<^sub>* e"
  shows "PExprE e :\<^sub>e t"
  apply (simp add: etype_rel_def PExprE_rep_eq assms WF_PEXPRESSION_type_def)
  apply (metis TypeUSound_def assms dtype_type)
done

lemma UNREST_PExprE [unrest]:
  fixes e :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION" 
  assumes "TYPEUSOUND('a, 'm)" "UNREST_PEXPR vs e"
  shows "UNREST_EXPR vs (PExprE e)"
  apply (insert assms)
  apply (simp add:UNREST_PEXPR_def UNREST_EXPR_def PExprE_rep_eq)
done

lemma LitPE_erasure [erasure]:
  fixes v :: "'a :: DEFINED" 
  assumes "TYPEUSOUND('a, 'm :: VALUE)"
  shows "(LitPE v)\<down> = (LitE (InjU v) :: 'm WF_EXPRESSION)"
  using assms
  apply (utp_expr_tac)
  apply (subgoal_tac "(InjU v :: 'm) : TYPEU('a)")
  apply (simp add:evale LitPE_def)
  apply (simp add:typing)
done

text {* The following functions and rules mechanise marshalling between predicates
        and boolean valued expressions *}

definition PExprP :: 
  "(bool, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 'm WF_PREDICATE" where
"PExprP e = mkPRED {b. \<lbrakk>e\<rbrakk>\<^sub>* b}"

declare [[coercion PExprP]]

setup {*
Adhoc_Overloading.add_variant @{const_name erase} @{const_name PExprP}
*}

lemma EvalP_PExprP [eval]:
  "\<lbrakk>e\<down>\<rbrakk>b = \<lbrakk>e\<rbrakk>\<^sub>* b"
  by (simp add:PExprP_def EvalP_def)

abbreviation PVarP ::
  "(bool, 'm :: BOOL_SORT) PVAR \<Rightarrow> 'm WF_PREDICATE" where
"PVarP x \<equiv> PExprP (PVarPE x)" 

definition PredPE ::
  "'m WF_PREDICATE \<Rightarrow> (bool, 'm :: VALUE) WF_PEXPRESSION" where
"PredPE p = MkPExpr (\<lambda> b. b \<in> destPRED p)"

lemma EvalPE_PExprP [eval]:
  "\<lbrakk>PredPE p\<rbrakk>\<^sub>*b = \<lbrakk>p\<rbrakk>b"
  by (simp add:PredPE_def EvalP_def)

lemma PExprP_inv [evalp]: "PredPE (PExprP p) = p"
  by (simp add: PExprP_def PredPE_def)

lemma PredPE_inv [evalp]: "(PredPE e)\<down> = e"
  by (simp add: PExprP_def PredPE_def)

lemma PExprP_VarPE [evalp]: 
  "(VarPE x)\<down> = VarP x"
  by (utp_pred_tac)

abbreviation PEqualP ::
  "('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> ('a, 'm) WF_PEXPRESSION \<Rightarrow>
   'm WF_PREDICATE" where
"PEqualP e f \<equiv> e\<down> ==\<^sub>p f\<down>"

(*
lemma PExprP_EqualPE [evalp]: 
  fixes e :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION" 
  assumes "TYPEUSOUND('a, 'm)"
  shows "(EqualPE e f)\<down> = (e\<down>) ==\<^sub>p (f\<down>)"
  by (force intro:assms simp add:EqualP_def Op2PE_def PExprP_def PExprE_rep_eq assms)
*)

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

abbreviation PAssignR ::
  "('a, 'm :: VALUE) PVAR \<Rightarrow> ('a, 'm) WF_PEXPRESSION \<Rightarrow> 'm WF_PREDICATE" where
"PAssignR x v \<equiv> x\<down> :=\<^sub>R v\<down>"

abbreviation AssignRPE ::
  "('a, 'm :: VALUE) PVAR \<Rightarrow> ('a, 'm) WF_PEXPRESSION \<Rightarrow> (bool, 'm) WF_PEXPRESSION" where
"AssignRPE x v \<equiv> PredPE (PAssignR x v)"

abbreviation WAssignRPE ::
  "('m :: VALUE) VAR \<Rightarrow> 'm WF_EXPRESSION \<Rightarrow> (bool, 'm) WF_PEXPRESSION" where
"WAssignRPE x v \<equiv> PredPE (x :=\<^sub>R v)"

lemma PExprE_compat [typing]:
  fixes e :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION" 
  and   x :: "('a, 'm) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "e \<rhd>\<^sub>* x"
  shows "e\<down> \<rhd>\<^sub>e x\<down>"
  using assms by (simp add: pevar_compat_def evar_compat_def PExprE_rep_eq)

lemma PExprE_compat_naux [typing]:
fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR" and e :: "('a, 'm) WF_PEXPRESSION"
assumes "TYPEUSOUND('a, 'm)" "\<not> pvaux x"
shows "e\<down> \<rhd>\<^sub>e x\<down>"
  apply (simp add:evar_compat_def assms PExprE_rep_eq typing)
  apply (auto simp add:pevar_compat_def PVAR_VAR_def assms typing var_compat_def)
done

lemma PExprE_compat_def [typing]:
fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR" and e :: "('a, 'm) WF_PEXPRESSION"
assumes "TYPEUSOUND('a, 'm)" "\<D> e"
shows "e\<down> \<rhd>\<^sub>e x\<down>"
  using assms
  apply (simp add:evar_compat_def assms PExprE_rep_eq typing Defined_WF_PEXPRESSION_def)
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

lemma TruePE_erasure [erasure]:
  "TruePE\<down> = TrueE"
  by (simp add:erasure typing TrueE_def)

lemma FalsePE_erasure [erasure]:
  "FalsePE\<down> = FalseE"
  by (simp add:erasure typing FalseE_def)

lemma PExprP_TruePE [evalp]: 
  "TruePE\<down> = TrueP"
  by (utp_pred_tac)

lemma PExprP_FalsePE [evalp]: 
  "FalsePE\<down> = FalseP"
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

abbreviation NilPE :: "('a::DEFINED ULIST, 'm :: LIST_SORT) WF_PEXPRESSION" where
"NilPE \<equiv> LitPE NilUL"

abbreviation ConsPE :: 
  "('a :: DEFINED, 'm :: LIST_SORT) WF_PEXPRESSION \<Rightarrow> 
   ('a ULIST, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a ULIST, 'm) WF_PEXPRESSION" where
"ConsPE \<equiv> Op2PE (op #\<^sub>u)"

abbreviation ConcatPE ::
  "('a ::DEFINED ULIST, 'm :: LIST_SORT) WF_PEXPRESSION \<Rightarrow> 
   ('a ULIST, 'm :: LIST_SORT) WF_PEXPRESSION \<Rightarrow> 
   ('a ULIST, 'm :: LIST_SORT) WF_PEXPRESSION" where
"ConcatPE \<equiv> Op2PE (op @\<^sub>u)"

abbreviation PrefixPE::
  "('a ::DEFINED ULIST, 'm :: {BOOL_SORT, LIST_SORT}) WF_PEXPRESSION \<Rightarrow> 
   ('a ULIST, 'm) WF_PEXPRESSION \<Rightarrow> (bool, 'm) WF_PEXPRESSION" where
"PrefixPE \<equiv> Op2PE PrefixUL"

abbreviation PrefixeqPE::
  "('a ::DEFINED ULIST, 'm :: {BOOL_SORT, LIST_SORT}) WF_PEXPRESSION \<Rightarrow> 
   ('a ULIST, 'm) WF_PEXPRESSION \<Rightarrow> (bool, 'm) WF_PEXPRESSION" where
"PrefixeqPE \<equiv> Op2PE PrefixeqUL"

instantiation ULIST :: (DEFINED) LESS_THAN
begin

definition uless_ULIST :: "'a ULIST \<Rightarrow> 'a ULIST \<Rightarrow> bool" where
"uless_ULIST xs ys = PrefixUL xs ys"

definition uless_eq_ULIST :: "'a ULIST \<Rightarrow> 'a ULIST \<Rightarrow> bool" where
"uless_eq_ULIST xs ys = PrefixeqUL xs ys"

instance ..
end

declare uless_ULIST_def [simp]
declare uless_eq_ULIST_def [simp]

instantiation ULIST :: (DEFINED) MINUS
begin

definition utminus_ULIST :: "'a ULIST \<Rightarrow> 'a ULIST \<Rightarrow> 'a ULIST" where
"utminus_ULIST xs ys = MinusUL xs ys"

instance ..
end

declare utminus_ULIST_def [simp]

subsection {* Finite Set Expressions *}

abbreviation FEmptyPE :: "('a::DEFINED UFSET, 'm :: FSET_SORT) WF_PEXPRESSION" where
"FEmptyPE \<equiv> LitPE EmptyUF"

abbreviation FInsertPE :: 
  "('a :: DEFINED, 'm :: FSET_SORT) WF_PEXPRESSION \<Rightarrow> 
   ('a UFSET, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a UFSET, 'm) WF_PEXPRESSION" where
"FInsertPE \<equiv> Op2PE InsertUF"

abbreviation FUnionPE ::
  "('a :: DEFINED UFSET, 'm :: FSET_SORT) WF_PEXPRESSION \<Rightarrow> 
   ('a UFSET, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a UFSET, 'm) WF_PEXPRESSION" where
"FUnionPE \<equiv> Op2PE UnionUF"

abbreviation FInterPE ::
  "('a :: DEFINED UFSET, 'm :: FSET_SORT) WF_PEXPRESSION \<Rightarrow> 
   ('a UFSET, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a UFSET, 'm) WF_PEXPRESSION" where
"FInterPE \<equiv> Op2PE InterUF"

abbreviation FMemberPE ::
  "('a :: DEFINED, 'm :: {BOOL_SORT, FSET_SORT}) WF_PEXPRESSION \<Rightarrow> 
   ('a UFSET, 'm) WF_PEXPRESSION \<Rightarrow> 
   (bool, 'm) WF_PEXPRESSION" where
"FMemberPE \<equiv> Op2PE MemberUF"

abbreviation FNotMemberPE ::
  "('a :: DEFINED, 'm :: {BOOL_SORT, FSET_SORT}) WF_PEXPRESSION \<Rightarrow> 
   ('a UFSET, 'm) WF_PEXPRESSION \<Rightarrow> 
   (bool, 'm) WF_PEXPRESSION" where
"FNotMemberPE \<equiv> Op2PE NMemberUF"

abbreviation IntersyncPE ::
  "('a :: DEFINED UFSET, 'm :: {FSET_SORT, LIST_SORT}) WF_PEXPRESSION \<Rightarrow>
   ('a ULIST, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a ULIST, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a ULIST UFSET, 'm) WF_PEXPRESSION" where
"IntersyncPE \<equiv> Op3PE IntersyncUF"

(*
lemma FUnionPE_type: 
  "\<tau>\<^sub>* (FUnionPE (xs :: ('a :: DEFINED UFSET , 'm :: FSET_SORT) WF_PEXPRESSION) ys) 
   = FSetType TYPEU('a)"
  by (simp add: WF_PEXPRESSION_type_def)
*)

subsection {* Action Expressions *}

definition PEV :: "'a CHANNEL \<Rightarrow> 'a \<Rightarrow> ('m :: EVENT_SORT) EVENT" where
"PEV c v = EV (fst c) TYPEU('a) (InjU v)"

abbreviation EventPE ::
  "'a CHANNEL \<Rightarrow> ('a, 'm :: EVENT_SORT) WF_PEXPRESSION 
              \<Rightarrow> ('m EVENT, 'm) WF_PEXPRESSION" where
"EventPE n v \<equiv> Op1PE (PEV n) v"

subsection {* Permutation *}

definition PermPE ::
  "('m :: VALUE) VAR_RENAME \<Rightarrow>
   ('a, 'm) WF_PEXPRESSION \<Rightarrow>   
   ('a, 'm) WF_PEXPRESSION" where
"PermPE ss e = MkPExpr (\<lbrakk>e\<rbrakk>\<^sub>* \<circ> (RenameB (inv\<^sub>s ss)))"

setup {*
Adhoc_Overloading.add_variant @{const_name permute} @{const_name PermPE}
*}

lemma EvalPE_RenamePE [eval]:
  "\<lbrakk>ss\<bullet>e\<rbrakk>\<^sub>*b = \<lbrakk>e\<rbrakk>\<^sub>*((inv\<^sub>s ss)\<bullet>b)"
  by (simp add:PermPE_def)

lemma RenamePE_PVarPE [urename]:
  "ss\<bullet>(VarPE x) = VarPE (ss\<bullet>x)"
  by (auto simp add:eval)

(*
lemma RenamePE_PVarPE [urename]:
  "RenamePE (PVarPE x) ss = PVarPE (\<langle>ss\<rangle>\<^sub>s\<^sub>* x)"
  apply (simp add:urename)
  by (auto simp add:evale)
*)

lemma RenamePE_LitPE [urename]:
  "ss\<bullet>(LitPE v) = LitPE v"
  by (auto simp add:eval)

lemma RenamePE_Op1PE [urename]:
  "ss\<bullet>(Op1PE f v) = Op1PE f (ss\<bullet>v)"
  by (auto simp add:eval)

lemma RenamePE_Op2PE [urename]:
  "ss\<bullet>(Op2PE f u v) = Op2PE f (ss\<bullet>u) (ss\<bullet>v)"
  by (auto simp add:eval)

lemma RenamePE_Op3PE [urename]:
  "ss\<bullet>(Op3PE f u v w) = Op3PE f (ss\<bullet>u) (ss\<bullet>v) (ss\<bullet>w)"
  by (auto simp add:eval)

subsection {* Substitution *}

definition SubstPE :: 
"('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 
 ('b, 'm) WF_PEXPRESSION \<Rightarrow> 
 'm VAR \<Rightarrow> 
 ('a, 'm) WF_PEXPRESSION" where
"SubstPE f v x = MkPExpr (\<lambda> b. \<lbrakk>f\<rbrakk>\<^sub>* (b(x :=\<^sub>b InjU (\<lbrakk>v\<rbrakk>\<^sub>* b))))"

definition PSubstPE :: 
"('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 
 ('b, 'm) WF_PEXPRESSION \<Rightarrow> 
 ('b, 'm) PVAR \<Rightarrow> 
 ('a, 'm) WF_PEXPRESSION" ("_[_'/\<^sub>*_]" [200] 200) where
"PSubstPE f v x \<equiv> SubstPE f v x\<down>"

abbreviation PSubstP :: 
"('m :: VALUE) WF_PREDICATE \<Rightarrow> 
 ('b, 'm) WF_PEXPRESSION \<Rightarrow> 
 ('b, 'm) PVAR \<Rightarrow> 
 'm WF_PREDICATE" where
"PSubstP p e x \<equiv> SubstP p e\<down> x\<down>"

lemma EvalPE_SubstPE [eval,evalp]:
  "\<lbrakk>SubstPE e v x\<rbrakk>\<^sub>*b = \<lbrakk>e\<rbrakk>\<^sub>* (b(x :=\<^sub>b InjU (\<lbrakk>v\<rbrakk>\<^sub>* b)))"
  by (simp add:SubstPE_def)

lemma EvalPE_PSubstPE [eval,evalp]:
  "\<lbrakk>PSubstPE e v x\<rbrakk>\<^sub>*b = \<lbrakk>e\<rbrakk>\<^sub>* (b(x\<down> :=\<^sub>b InjU (\<lbrakk>v\<rbrakk>\<^sub>* b)))"
  by (simp add:PSubstPE_def SubstPE_def)

lemma PExprP_SubstPE [evalp]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "v \<rhd>\<^sub>* x" "TYPEUSOUND('a, 'm)"
  shows "(PSubstPE e v x)\<down> = SubstP e\<down> v\<down> x\<down>"
  by (simp add:SubstPE_def PSubstPE_def PExprP_def SubstP_def PExprE_rep_eq assms)

lemma PSubstPE_PVarPE [usubst]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "v \<rhd>\<^sub>* x" "TYPEUSOUND('a, 'm)"
  shows "PSubstPE (PVarPE x) v x = v"
  using assms by (auto simp add:eval pevar_compat_def PSubstPE_def)

lemma PSubstPE_LitPE [usubst]:
  "PSubstPE (LitPE v) x e = LitPE v"
  by (auto simp add:eval)

lemma PSubstPE_Op1PE [usubst]:
  "(Op1PE f v)[x/\<^sub>*e] = Op1PE f (v[x/\<^sub>*e])"
  by (auto simp add:eval)

lemma PSubstPE_Op2PE [usubst]:
  "(Op2PE f u v)[e/\<^sub>*x] = Op2PE f (u[e/\<^sub>*x]) (v[e/\<^sub>*x])"
  by (auto simp add:eval)

lemma PSubstPE_Op3PE [usubst]:
  "(Op3PE f u v w)[e/\<^sub>*x] = Op3PE f (u[e/\<^sub>*x]) (v[e/\<^sub>*x]) (w[e/\<^sub>*x])"
  by (auto simp add:eval)

lemma SubstP_PSubstPE [usubst]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "TYPEUSOUND('a, 'm)"
  shows "e\<down>[v\<down>/\<^sub>px\<down>] = (PSubstPE e v x)\<down>"
  using assms by (utp_pred_tac)

lemma SubstP_PSubstPE_dash [usubst]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "TYPEUSOUND('a, 'm)"
  shows "e\<down>[v\<down>/\<^sub>px\<down>\<acute>] = (PSubstPE e v x\<acute>)\<down>"
  using assms by (utp_pred_tac)

lemma SubstP_PSubstPE_dash_dash [usubst]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "TYPEUSOUND('a, 'm)"
  shows "e\<down>[v\<down>/\<^sub>px\<down>\<acute>\<acute>] = (PSubstPE e v x\<acute>\<acute>)\<down>"
  using assms by (utp_pred_tac)

lemma PSubstPE_PVarPE_neq [usubst]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  and   x :: "('b :: DEFINED, 'm :: VALUE) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "x\<down> \<noteq> y\<down>" "v \<rhd>\<^sub>* y"
  shows "PSubstPE (PVarPE x) v y = PVarPE x"
  using assms by (auto simp add:eval typing defined pevar_compat_def)

lemma SubstE_PSubstPE [usubst]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  and   e :: "('b :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "TYPEUSOUND('a, 'm)" "TYPEUSOUND('b, 'm)" "v \<rhd>\<^sub>* x"
  shows "e\<down>[v\<down>/\<^sub>ex\<down>] = (PSubstPE e v x)\<down>"
  using assms by (auto simp add:evale typing defined evalp)

lemma SubstP_PSubstPE_TrueE [usubst]:
  fixes e :: "(bool, 'm :: BOOL_SORT) WF_PEXPRESSION"
  and   x :: "(bool, 'm) PVAR"
  shows "e\<down>[TrueE/\<^sub>px\<down>] = (PSubstPE e TruePE x)\<down>"
  using assms by utp_pred_tac

lemma SubstP_PSubstPE_FalseE [usubst]:
  fixes e :: "(bool, 'm :: BOOL_SORT) WF_PEXPRESSION"
  and   x :: "(bool, 'm) PVAR"
  shows "e\<down>[FalseE/\<^sub>px\<down>] = (PSubstPE e FalsePE x)\<down>"
  using assms by utp_pred_tac

lemma PVarPE_VarP [simp]:
  fixes x :: "(bool, 'm::BOOL_SORT) PVAR"
  shows "((PVarPE x)\<down> ==\<^sub>p (TruePE\<down>)) = VarP (x\<down>)"
  apply (utp_pred_auto_tac)
  apply (metis BOOL_SORT_class.Inverse)
done


(*
subsection {* Anciliary Laws *}

lemma MkBool_compat_bool [typing]:
  "MkBool v \<rhd> [x :: (bool, 'm :: BOOL_SORT) PVAR]\<^sub>*"
  by (simp add:var_compat_def typing defined)

lemma MkInt_compat_int [typing]:
  "MkInt v \<rhd> [x :: (int, 'm :: INT_SORT) PVAR]\<^sub>*"
  by (simp add:var_compat_def typing defined)
*)
 
end