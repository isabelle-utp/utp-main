(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_poly_expr.thy                                                    *)
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
  "../tactics/utp_rel_tac"
  "../tactics/utp_xrel_tac"
  "../laws/utp_pred_laws"
  utp_poly_value
  utp_poly_var
  utp_poly_binding
  utp_poly_tac
begin

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

lemma DestPExpr_transfer [evalp]:
  "x = y \<longleftrightarrow> (\<forall> b. \<lbrakk>x\<rbrakk>\<^sub>*b = \<lbrakk>y\<rbrakk>\<^sub>*b)"
  by (auto)

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

setup {*
Adhoc_Overloading.add_variant @{const_name unrest} @{const_name UNREST_PEXPR}
*}

lemma EvalPE_UNREST_assign [evalp]:
  "{x\<down>} \<sharp> e \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>*(b(x :=\<^sub>* v)) = \<lbrakk>e\<rbrakk>\<^sub>*b"
  apply (simp add:UNREST_PEXPR_def binding_upd_ty_def)
  apply (drule_tac x="b" in spec)
  apply (drule_tac x="b(x\<down> :=\<^sub>b InjU v)" in spec)
  apply (simp add:typing)
done

definition LitPE :: "'a \<Rightarrow> ('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION" where
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

lemma UNREST_PEXPR_subset:
  "\<lbrakk> UNREST_PEXPR vs1 v; vs2 \<subseteq> vs1 \<rbrakk> \<Longrightarrow> UNREST_PEXPR vs2 v"
  apply (auto simp add:UNREST_PEXPR_def)
  apply (metis Int_absorb2 binding_override_simps(6))
done

lemma UNREST_LitPE [unrest]:
  "UNREST_PEXPR vs (LitPE v)"
  by (simp add:UNREST_PEXPR_def LitPE_def)

lemma WF_PEXPRESSION_tau [typing]:
  fixes v :: "('a, 'm :: VALUE) WF_PEXPRESSION"
  shows "\<tau>\<^sub>*(v) = TypeU(TYPE('a))"
  by (simp add:WF_PEXPRESSION_type_def)

definition pevar_compat :: 
  "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> ('a, 'm) PVAR \<Rightarrow> bool" (infix "\<rhd>\<^sub>*" 50) where
"pevar_compat e x \<equiv> \<forall>b. (\<lbrakk>e\<rbrakk>\<^sub>* b) \<rhd>\<^sub>p x"

lemma pevar_compat_TYPEUSOUND:
  fixes e :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  and   x :: "('a, 'm) PVAR"
  assumes "e \<rhd>\<^sub>* x"
  shows "TYPEUSOUND('a,'m)"
  by (metis assms pevar_compat_def pvar_compat_def)

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
  by (auto simp add:pevar_compat_def defined typing Defined_WF_PEXPRESSION_def)

lemma EvalPE_compat [typing]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "v \<rhd>\<^sub>* x"
  shows "\<lbrakk>v\<rbrakk>\<^sub>* b \<rhd>\<^sub>p x"
  using assms by (simp add: pevar_compat_def)

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

definition PVarPE :: "('a :: DEFINED, 'm :: VALUE) PVAR \<Rightarrow> ('a, 'm) WF_PEXPRESSION" where
"PVarPE x \<equiv> VarPE x\<down>"

(* FIXME: Maybe this law should be removed in favour of the following one... *)
lemma EvalPE_PVarPE:
  "\<lbrakk>PVarPE x\<rbrakk>\<^sub>*b = ProjU (\<langle>b\<rangle>\<^sub>b x\<down>)"
  by (simp add:VarPE_def PVarPE_def)

lemma EvalPE_PVarPE_ty [eval,evalp]:
  "\<lbrakk>PVarPE x\<rbrakk>\<^sub>*b = \<langle>b\<rangle>\<^sub>* x"
  by (simp add: EvalPE_PVarPE Rep_binding_ty_def)

lemma PVarPE_defined_aux [defined]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "pvaux x"
  shows "\<D> (PVarPE x)"
  using assms by (auto intro:defined typing simp add:Defined_WF_PEXPRESSION_def eval)

lemma UNREST_PVarPE [unrest]:
  "x\<down> \<notin> vs \<Longrightarrow> UNREST_PEXPR vs (PVarPE x)"
  by (metis PVarPE_def UNREST_VarPE)

definition ErasePE :: 
  "('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> ('m SIGTYPE, 'm) WF_PEXPRESSION" where
"ErasePE v = MkPExpr (\<lambda> b. \<Sigma> (InjU (\<lbrakk>v\<rbrakk>\<^sub>*b)) : TYPEU('a))"

lemma EvalPE_ErasePE:
  fixes v :: "('a, 'm :: VALUE) WF_PEXPRESSION"
  shows "\<lbrakk>ErasePE v\<rbrakk>\<^sub>*b = (\<Sigma> (InjU (\<lbrakk>v\<rbrakk>\<^sub>*b)) : TYPEU('a))"
  by (simp add:ErasePE_def)

lemma UNREST_ErasePE [unrest]:
  "UNREST_PEXPR vs v \<Longrightarrow> UNREST_PEXPR vs (ErasePE v)"
  by (simp add:UNREST_PEXPR_def ErasePE_def)

definition ProdPE ::
  "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 
   ('b :: DEFINED, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow>
   (('a * 'b), 'm) WF_PEXPRESSION" ("'(_, _')\<^sub>*") where
"ProdPE x y = MkPExpr (\<lambda> b. (\<lbrakk>x\<rbrakk>\<^sub>* b, \<lbrakk>y\<rbrakk>\<^sub>* b))"

lemma EvalPE_ProdPE [eval,evale,evalp]:
  "\<lbrakk>(x,y)\<^sub>*\<rbrakk>\<^sub>*b = (\<lbrakk>x\<rbrakk>\<^sub>* b, \<lbrakk>y\<rbrakk>\<^sub>* b)"
  by (simp add:ProdPE_def)

lemma UNREST_ProdPE [unrest]:
  "\<lbrakk> UNREST_PEXPR vs x; UNREST_PEXPR vs y \<rbrakk> \<Longrightarrow> UNREST_PEXPR vs (x, y)\<^sub>*"
  by (simp add:UNREST_PEXPR_def EvalPE_ProdPE)

lemma ProdPE_defined [defined]:
  "\<lbrakk> \<D> x; \<D> y \<rbrakk> \<Longrightarrow> \<D> (x, y)\<^sub>*"
  by (simp add:Defined_WF_PEXPRESSION_def EvalPE_ProdPE defined)

lemma ProdPE_range:
  "range \<lbrakk>(x, y)\<^sub>*\<rbrakk>\<^sub>* = {(\<lbrakk>x\<rbrakk>\<^sub>*b, \<lbrakk>y\<rbrakk>\<^sub>*b)|b. True}"
  by (simp add:image_def EvalPE_ProdPE)

lemma ProdPE_Dom_uncurry [defined]:
  "\<lbrakk> \<And>b. \<D> (f (\<lbrakk>x\<rbrakk>\<^sub>* b) (\<lbrakk>y\<rbrakk>\<^sub>* b)) \<rbrakk> \<Longrightarrow>
   range \<lbrakk>(x, y)\<^sub>*\<rbrakk>\<^sub>* \<subseteq> Dom (uncurry f)"
  by (auto simp add:Dom_def EvalPE_ProdPE)

definition Op1PE :: 
  "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> ('b, 'm) WF_PEXPRESSION" where
"Op1PE f u = MkPExpr (\<lambda> b. f (\<lbrakk>u\<rbrakk>\<^sub>*b))"

lemma EvalPE_Op1PE [eval,evale,evalp]:
  "\<lbrakk>Op1PE f u\<rbrakk>\<^sub>*b = f (\<lbrakk>u\<rbrakk>\<^sub>*b)"
  by (simp add:Op1PE_def)

lemma UNREST_Op1PE [unrest]:
  "UNREST_PEXPR vs u \<Longrightarrow> UNREST_PEXPR vs (Op1PE f u)"
  by (simp add:UNREST_PEXPR_def Op1PE_def)

lemma Op1PE_defined [defined]:
  "\<lbrakk> \<D> x; range \<lbrakk>x\<rbrakk>\<^sub>* \<subseteq> Dom f \<rbrakk> \<Longrightarrow> \<D> (Op1PE f x)"
  by (auto simp add:Defined_WF_PEXPRESSION_def EvalPE_Op1PE Dom_def)

definition 
  Op2PE :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 
            ('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 
            ('b :: DEFINED, 'm) WF_PEXPRESSION \<Rightarrow> 
            ('c :: DEFINED, 'm) WF_PEXPRESSION" where
"Op2PE f u v \<equiv> Op1PE (uncurry f) (u, v)\<^sub>*"

declare Op2PE_def [eval, evale, evalp]

lemma UNREST_Op2PE [unrest]:
  "\<lbrakk> UNREST_PEXPR vs u; UNREST_PEXPR vs v \<rbrakk> \<Longrightarrow> UNREST_PEXPR vs (Op2PE f u v)"
  by (simp add:Op2PE_def unrest)

lemma Op2PE_defined [defined]:
  "\<lbrakk> \<D> x; \<D> y; range \<lbrakk>(x, y)\<^sub>*\<rbrakk>\<^sub>* \<subseteq> Dom (uncurry f) \<rbrakk> \<Longrightarrow> \<D> (Op2PE f x y)"
  by (simp add:Op2PE_def defined)

definition
  Op3PE :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 
            ('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 
            ('b :: DEFINED, 'm) WF_PEXPRESSION \<Rightarrow> 
            ('c :: DEFINED, 'm) WF_PEXPRESSION \<Rightarrow>
            ('d :: DEFINED, 'm) WF_PEXPRESSION" where
"Op3PE f u v w \<equiv> Op1PE (uncurry (uncurry f)) (ProdPE (ProdPE u v) w)"

declare Op3PE_def [eval, evale, evalp]

lemma UNREST_Op3PE [unrest]:
  "\<lbrakk> UNREST_PEXPR vs u; UNREST_PEXPR vs v; UNREST_PEXPR vs w \<rbrakk> 
   \<Longrightarrow> UNREST_PEXPR vs (Op3PE f u v w)"
  by (simp add:Op3PE_def unrest)

lemma Op3PE_defined [defined]:
  "\<lbrakk> \<D> x; \<D> y; \<D> z; range \<lbrakk>((x, y)\<^sub>*,z)\<^sub>*\<rbrakk>\<^sub>* \<subseteq> Dom (uncurry (uncurry f)) \<rbrakk> 
   \<Longrightarrow> \<D> (Op3PE f x y z)"
  by (simp add:Op3PE_def defined)

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

lemma PVarPE_erasure [erasure]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR" 
  assumes "TYPEUSOUND('a, 'm :: VALUE)" "pvaux x"
  shows "(PVarPE x)\<down> = VarE (x\<down>)"
  using assms
  apply (auto simp add:evale defined typing evalp)
  apply (simp add:Rep_binding_ty_def)
  apply (metis MkVar_def PVAR_VAR_def TypeUSound_ProjU_inv aux_defined binding_type dtype_relI fst_conv snd_conv)
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

lemma EvalP_PExprP [evalp]:
  "\<lbrakk>e\<down>\<rbrakk>b = \<lbrakk>e\<rbrakk>\<^sub>* b"
  by (simp add:PExprP_def EvalP_def)

lemma EvalP_EqualP_ty [evalp]:
  fixes e1 e2 :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION" 
  assumes "TYPEUSOUND('a, 'm)"
  shows "\<lbrakk>e1\<down> ==\<^sub>p e2\<down>\<rbrakk>b = (\<lbrakk>e1\<rbrakk>\<^sub>*b = \<lbrakk>e2\<rbrakk>\<^sub>*b)"
  apply (auto simp add:eval evale evalp assms)
  apply (drule TypeUSound_InjU_inj[OF assms(1)], simp)
done

lemma EvalP_VarP_ty [evalp]:
  fixes x :: "(bool, 'm :: BOOL_SORT) PVAR" 
  shows "\<lbrakk>$\<^sub>p(x\<down>)\<rbrakk>b = \<langle>b\<rangle>\<^sub>* x"
  apply (utp_pred_tac)
  apply (simp add:Rep_binding_ty_def inju)
done

lemma EvalP_VarP_dash1_ty [evalp]:
  fixes x :: "(bool, 'm :: BOOL_SORT) PVAR" 
  shows "\<lbrakk>$\<^sub>p(x\<down>)\<acute>\<rbrakk>b = \<langle>b\<rangle>\<^sub>* x\<acute>"
  apply (utp_pred_tac)
  apply (simp add:Rep_binding_ty_def inju)
done

lemma EvalP_VarP_dash2_ty [evalp]:
  fixes x :: "(bool, 'm :: BOOL_SORT) PVAR" 
  shows "\<lbrakk>$\<^sub>p(x\<down>)\<acute>\<acute>\<rbrakk>b = \<langle>b\<rangle>\<^sub>* x\<acute>\<acute>"
  apply (utp_pred_tac)
  apply (simp add:Rep_binding_ty_def inju)
done

lemma EvalP_VarP_dash3_ty [evalp]:
  fixes x :: "(bool, 'm :: BOOL_SORT) PVAR" 
  shows "\<lbrakk>$\<^sub>p(x\<down>)\<acute>\<acute>\<acute>\<rbrakk>b = \<langle>b\<rangle>\<^sub>* x\<acute>\<acute>\<acute>"
  apply (utp_pred_tac)
  apply (simp add:Rep_binding_ty_def inju)
done

lemma PExprP_VarPE [evalp]: 
  "(VarPE x)\<down> = VarP x"
  by (simp add:eval evalp inju)

lemma EvalP_ExprP_ty [evalp]:
  fixes e :: "(bool, 'm :: BOOL_SORT) WF_PEXPRESSION" 
  shows "\<lbrakk>ExprP e\<down>\<rbrakk>b = \<lbrakk>e\<rbrakk>\<^sub>*b"
  apply (utp_pred_tac)
  apply (simp add:inju)
done

lemma EvalP_SubstP_ty [evalp]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION" 
  assumes "v \<rhd>\<^sub>* x"
  shows "\<lbrakk>p[v\<down>/\<^sub>px\<down>]\<rbrakk>b = \<lbrakk>p\<rbrakk>(b(x :=\<^sub>* \<lbrakk>v\<rbrakk>\<^sub>*b))"
  apply (utp_pred_tac)
  apply (subst evale)
  apply (metis assms pevar_compat_TYPEUSOUND)
  apply (simp add:binding_upd_ty_def)
done

lemma EvalP_SubstP_dash1_ty [evalp]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION" 
  assumes "v \<rhd>\<^sub>* x"
  shows "\<lbrakk>p[v\<down>/\<^sub>px\<down>\<acute>]\<rbrakk>b = \<lbrakk>p\<rbrakk>(b(x\<acute> :=\<^sub>* \<lbrakk>v\<rbrakk>\<^sub>*b))"
  apply (utp_pred_tac)
  apply (subst evale)
  apply (metis assms pevar_compat_TYPEUSOUND)
  apply (simp add:binding_upd_ty_def)
done

lemma EvalP_SubstP_dash2_ty [evalp]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION" 
  assumes "v \<rhd>\<^sub>* x"
  shows "\<lbrakk>p[v\<down>/\<^sub>px\<down>\<acute>\<acute>]\<rbrakk>b = \<lbrakk>p\<rbrakk>(b(x\<acute>\<acute> :=\<^sub>* \<lbrakk>v\<rbrakk>\<^sub>*b))"
  apply (utp_pred_tac)
  apply (subst evale)
  apply (metis assms pevar_compat_TYPEUSOUND)
  apply (simp add:binding_upd_ty_def)
done

lemma EvalP_SubstP_dash3_ty [evalp]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION" 
  assumes "v \<rhd>\<^sub>* x"
  shows "\<lbrakk>p[v\<down>/\<^sub>px\<down>\<acute>\<acute>\<acute>]\<rbrakk>b = \<lbrakk>p\<rbrakk>(b(x\<acute>\<acute>\<acute> :=\<^sub>* \<lbrakk>v\<rbrakk>\<^sub>*b))"
  apply (utp_pred_tac)
  apply (subst evale)
  apply (metis assms pevar_compat_TYPEUSOUND)
  apply (simp add:binding_upd_ty_def)
done

lemma EvalP_ExistsP_singleton_pvaux_ty [evalp]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "pvaux x"
  shows "\<lbrakk>\<exists>\<^sub>p {x\<down>} . p\<rbrakk>b = (\<exists> v . v \<rhd>\<^sub>p x \<and> \<lbrakk>p\<rbrakk>(b(x :=\<^sub>* v)))"
  apply (auto simp add:eval)
  apply (rule_tac x="\<langle>b'\<rangle>\<^sub>* x" in exI)
  apply (auto)
  apply (rule typing)
  apply (simp_all add:assms defined)
  apply (simp add:Rep_binding_ty_def binding_upd_ty_def assms typing defined)
  apply (subst TypeUSound_ProjU_inv)
  apply (simp_all add:typing defined assms)
  apply (rule typing)
  apply (simp_all add:typing defined assms pvaux_aux[THEN sym])
  apply (metis binding_upd_eq binding_upd_ty_def binding_upd_vcoerce)
done

lemma EvalP_ExistsP_singleton_d1_pvaux_ty [evalp]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "pvaux x"
  shows "\<lbrakk>\<exists>\<^sub>p {x\<down>\<acute>} . p\<rbrakk>b = (\<exists> v . v \<rhd>\<^sub>p x\<acute> \<and> \<lbrakk>p\<rbrakk>(b(x\<acute> :=\<^sub>* v)))"
  apply (subst EvalP_ExistsP_singleton_pvaux_ty[THEN sym])
  apply (simp_all add:assms)
done

lemma EvalP_ExistsP_singleton_d2_pvaux_ty [evalp]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "pvaux x"
  shows "\<lbrakk>\<exists>\<^sub>p {x\<down>\<acute>\<acute>} . p\<rbrakk>b = (\<exists> v . v \<rhd>\<^sub>p x\<acute>\<acute> \<and> \<lbrakk>p\<rbrakk>(b(x\<acute>\<acute> :=\<^sub>* v)))"
  apply (subst EvalP_ExistsP_singleton_pvaux_ty[THEN sym])
  apply (simp_all add:assms)
done

lemma EvalP_ExistsP_singleton_d3_pvaux_ty [evalp]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "pvaux x"
  shows "\<lbrakk>\<exists>\<^sub>p {x\<down>\<acute>\<acute>\<acute>} . p\<rbrakk>b = (\<exists> v . v \<rhd>\<^sub>p x\<acute>\<acute>\<acute> \<and> \<lbrakk>p\<rbrakk>(b(x\<acute>\<acute>\<acute> :=\<^sub>* v)))"
  apply (subst EvalP_ExistsP_singleton_pvaux_ty[THEN sym])
  apply (simp_all add:assms)
done

lemma UNREST_PExprP [unrest]:
  "UNREST_PEXPR vs v \<Longrightarrow> UNREST vs v\<down>"
  by (auto simp add:UNREST_def UNREST_PEXPR_def PExprP_def)

lemma WF_CONDITION_PExprP [closure]:
  "UNREST_PEXPR (NON_REL_VAR \<union> DASHED) v \<Longrightarrow> PExprP v \<in> WF_CONDITION"
  by (metis (lifting, no_types) UNREST_PExprP UNREST_unionE WF_CONDITION_def WF_RELATION_def mem_Collect_eq)

abbreviation PVarP ::
  "(bool, 'm :: BOOL_SORT) PVAR \<Rightarrow> 'm WF_PREDICATE" where
"PVarP x \<equiv> PExprP (PVarPE x)" 

definition PredPE ::
  "'m WF_PREDICATE \<Rightarrow> (bool, 'm :: VALUE) WF_PEXPRESSION" where
"PredPE p = MkPExpr (\<lambda> b. b \<in> destPRED p)"

lemma EvalPE_PExprP [eval, evalp]:
  "\<lbrakk>PredPE p\<rbrakk>\<^sub>*b = \<lbrakk>p\<rbrakk>b"
  by (simp add:PredPE_def EvalP_def)

lemma PExprP_inv [evalp]: "PredPE (PExprP p) = p"
  by (simp add: PExprP_def PredPE_def)

lemma PredPE_inv [evalp]: "(PredPE e)\<down> = e"
  by (simp add: PExprP_def PredPE_def)

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

abbreviation PAssignF_upd :: "'m AssignF \<Rightarrow> ('a::DEFINED, 'm::VALUE) PVAR \<Rightarrow> ('a, 'm) WF_PEXPRESSION \<Rightarrow> 'm AssignF" where
"PAssignF_upd f x v \<equiv> AssignF_upd f (x\<down>) (v\<down>)"

abbreviation AssignRPE ::
  "('a, 'm :: VALUE) PVAR \<Rightarrow> ('a, 'm) WF_PEXPRESSION \<Rightarrow> (bool, 'm) WF_PEXPRESSION" where
"AssignRPE x v \<equiv> PredPE (PAssignR x v)"

abbreviation WAssignRPE ::
  "('m :: VALUE) VAR \<Rightarrow> 'm WF_EXPRESSION \<Rightarrow> (bool, 'm) WF_PEXPRESSION" where
"WAssignRPE x v \<equiv> PredPE (x :=\<^sub>R v)"

lemma PExprE_compat [typing]:
  fixes e :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION" 
  and   x :: "('a, 'm) PVAR"
  assumes "e \<rhd>\<^sub>* x"
  shows "e\<down> \<rhd>\<^sub>e x\<down>"
  using assms
  apply (auto simp add: pevar_compat_def evar_compat_def pvar_compat_def PExprE_rep_eq)
  apply (metis pvar_compat_def var_compat_pvar)
done

lemma pevar_compat_dash_simp [simp]: "e \<rhd>\<^sub>* x\<acute> \<longleftrightarrow> e \<rhd>\<^sub>* x"
  by (metis pevar_compat_def pvar_compat_def pvaux_pvdash)

lemma evar_compat_dash_simp [simp]: "e \<rhd>\<^sub>e x\<acute> \<longleftrightarrow> e \<rhd>\<^sub>e x"
  by (metis (full_types) evar_compat_dash evar_compat_undash undash_dash)

lemma PExprE_compat_dash [typing]:
  fixes e :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION" 
  and   x :: "('a, 'm) PVAR"
  assumes "e \<rhd>\<^sub>* x\<acute>"
  shows "e\<down> \<rhd>\<^sub>e x\<down>\<acute>"
  using assms by (simp add:typing)

lemma PExprE_compat_dash_dash [typing]:
  fixes e :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION" 
  and   x :: "('a, 'm) PVAR"
  assumes "e \<rhd>\<^sub>* x\<acute>\<acute>"
  shows "e\<down> \<rhd>\<^sub>e x\<down>\<acute>\<acute>"
  using assms by (simp add:typing)

lemma PExprE_compat_naux [typing]:
fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR" and e :: "('a, 'm) WF_PEXPRESSION"
assumes "TYPEUSOUND('a, 'm)" "\<not> pvaux x"
shows "e\<down> \<rhd>\<^sub>e x\<down>"
  by (simp add:typing assms)

lemma PExprE_compat_def [typing]:
fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR" and e :: "('a, 'm) WF_PEXPRESSION"
assumes "TYPEUSOUND('a, 'm)" "\<D> e"
shows "e\<down> \<rhd>\<^sub>e x\<down>"
  using assms
  by (simp add:evar_compat_def assms PExprE_rep_eq typing Defined_WF_PEXPRESSION_def)

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
  by (simp add:WF_PEXPRESSION_type_def inju)

lemma FalsePE_tau: "\<tau>\<^sub>* FalsePE = BoolType"
  by (simp add:WF_PEXPRESSION_type_def inju)

lemma TruePE_erasure [erasure]:
  "TruePE\<down> = TrueE"
  by (simp add:erasure typing TrueE_def inju)

lemma FalsePE_erasure [erasure]:
  "FalsePE\<down> = FalseE"
  by (simp add:erasure typing FalseE_def inju)

lemma PExprP_TruePE [evalp]: 
  "TruePE\<down> = TrueP"
  by (utp_poly_tac)

lemma PExprP_FalsePE [evalp]: 
  "FalsePE\<down> = FalseP"
  by (utp_poly_tac)

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

subsection {* Restriction Operator *}

consts
  restrict  :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" 

setup {*
  Adhoc_Overloading.add_overloaded @{const_name restrict}
*}

subsection {* Numeric Expressions *}

abbreviation IntPE :: "int \<Rightarrow> (int, 'a :: INT_SORT) WF_PEXPRESSION" where
"IntPE \<equiv> LitPE"

abbreviation RealPE :: "int \<Rightarrow> (int, 'a :: REAL_SORT) WF_PEXPRESSION" where
"RealPE \<equiv> LitPE"

abbreviation "PlusPE u v \<equiv> Op2PE (op +) u v"
abbreviation "MultPE u v \<equiv> Op2PE (op *) u v"
abbreviation "DivPE  u v \<equiv> Op2PE (op /) u v"

instantiation int :: LESS_THAN
begin

definition uless_int :: "int \<Rightarrow> int \<Rightarrow> bool" where
"uless_int x y = (x < y)"

definition uless_eq_int :: "int \<Rightarrow> int \<Rightarrow> bool" where
"uless_eq_int x y = (x \<le> y)"

instance ..
end

declare uless_int_def [eval,evalp]
declare uless_eq_int_def [eval,evalp]

instantiation int :: MINUS
begin

definition utminus_int :: "int \<Rightarrow> int \<Rightarrow> int" where
"utminus_int x y = x - y"

instance ..
end

declare utminus_int_def [eval,evalp]

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

abbreviation FSetPE ::
  "('a ::DEFINED ULIST, 'm :: {FSET_SORT, LIST_SORT}) WF_PEXPRESSION \<Rightarrow> 
   ('a UFSET, 'm) WF_PEXPRESSION" where
"FSetPE \<equiv> Op1PE FSetUF"

abbreviation SetPE ::
  "('a ::DEFINED ULIST, 'm :: {SET_SORT, LIST_SORT}) WF_PEXPRESSION \<Rightarrow> 
   ('a USET, 'm) WF_PEXPRESSION" where
"SetPE \<equiv> Op1PE SetUS"

abbreviation PrefixPE::
  "('a ::DEFINED ULIST, 'm :: {BOOL_SORT, LIST_SORT}) WF_PEXPRESSION \<Rightarrow> 
   ('a ULIST, 'm) WF_PEXPRESSION \<Rightarrow> (bool, 'm) WF_PEXPRESSION" where
"PrefixPE \<equiv> Op2PE PrefixUL"

abbreviation PrefixeqPE::
  "('a ::DEFINED ULIST, 'm :: {BOOL_SORT, LIST_SORT}) WF_PEXPRESSION \<Rightarrow> 
   ('a ULIST, 'm) WF_PEXPRESSION \<Rightarrow> (bool, 'm) WF_PEXPRESSION" where
"PrefixeqPE \<equiv> Op2PE PrefixeqUL"

definition RestrictPE :: 
  "('a ::DEFINED ULIST, 'm :: {BOOL_SORT, LIST_SORT}) WF_PEXPRESSION \<Rightarrow> 
   ('a USET, 'm) WF_PEXPRESSION \<Rightarrow>
   ('a ULIST, 'm) WF_PEXPRESSION" where
"RestrictPE \<equiv> Op2PE RestrictUS"

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

setup {*
Adhoc_Overloading.add_variant @{const_name restrict} @{const_name RestrictPE}
*}

declare RestrictPE_def [simp]

lemma MinusUL_left_nil [simp]: 
  fixes x :: "('a::DEFINED ULIST, 'm::LIST_SORT) WF_PEXPRESSION"
  shows "MinusPE NilPE x = NilPE"
  by (utp_poly_auto_tac)

lemma MinusUL_right_nil [simp]: 
  fixes x :: "('a::DEFINED ULIST, 'm::LIST_SORT) WF_PEXPRESSION"
  shows "MinusPE x NilPE = x"
  by (utp_poly_auto_tac)

subsection {* Set Expressions *}

abbreviation EmptyPE :: "('a::DEFINED USET, 'm :: SET_SORT) WF_PEXPRESSION" where
"EmptyPE \<equiv> LitPE EmptyUS"

abbreviation InsertPE :: 
  "('a :: DEFINED, 'm :: FSET_SORT) WF_PEXPRESSION \<Rightarrow> 
   ('a USET, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a USET, 'm) WF_PEXPRESSION" where
"InsertPE \<equiv> Op2PE InsertUS"

abbreviation UnionPE ::
  "('a :: DEFINED USET, 'm :: SET_SORT) WF_PEXPRESSION \<Rightarrow> 
   ('a USET, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a USET, 'm) WF_PEXPRESSION" where
"UnionPE \<equiv> Op2PE UnionUS"

abbreviation InterPE ::
  "('a :: DEFINED USET, 'm :: SET_SORT) WF_PEXPRESSION \<Rightarrow> 
   ('a USET, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a USET, 'm) WF_PEXPRESSION" where
"InterPE \<equiv> Op2PE InterUS"

abbreviation SMinusPE ::
  "('a :: DEFINED USET, 'm :: SET_SORT) WF_PEXPRESSION \<Rightarrow> 
   ('a USET, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a USET, 'm) WF_PEXPRESSION" where
"SMinusPE \<equiv> Op2PE MinusUS"

abbreviation MemberPE ::
  "('a :: DEFINED, 'm :: {BOOL_SORT, SET_SORT}) WF_PEXPRESSION \<Rightarrow> 
   ('a USET, 'm) WF_PEXPRESSION \<Rightarrow> 
   (bool, 'm) WF_PEXPRESSION" where
"MemberPE \<equiv> Op2PE MemberUS"

abbreviation NotMemberPE ::
  "('a :: DEFINED, 'm :: {BOOL_SORT, SET_SORT}) WF_PEXPRESSION \<Rightarrow> 
   ('a USET, 'm) WF_PEXPRESSION \<Rightarrow> 
   (bool, 'm) WF_PEXPRESSION" where
"NotMemberPE \<equiv> Op2PE NMemberUS"

abbreviation SubsetPE ::
  "('a :: DEFINED USET, 'm :: {BOOL_SORT, SET_SORT}) WF_PEXPRESSION \<Rightarrow> 
   ('a USET, 'm) WF_PEXPRESSION \<Rightarrow> 
   (bool, 'm) WF_PEXPRESSION" where
"SubsetPE \<equiv> Op2PE SubsetUS"

abbreviation SubseteqPE ::
  "('a :: DEFINED USET, 'm :: {BOOL_SORT, SET_SORT}) WF_PEXPRESSION \<Rightarrow> 
   ('a USET, 'm) WF_PEXPRESSION \<Rightarrow> 
   (bool, 'm) WF_PEXPRESSION" where
"SubseteqPE \<equiv> Op2PE SubseteqUS"

abbreviation IntersyncPE ::
  "('a :: DEFINED USET, 'm :: {LIST_SORT, SET_SORT}) WF_PEXPRESSION \<Rightarrow>
   ('a ULIST, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a ULIST, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a ULIST USET, 'm) WF_PEXPRESSION" where
"IntersyncPE \<equiv> Op3PE IntersyncUS"

instantiation USET :: (DEFINED) MINUS
begin

definition utminus_USET :: "'a USET \<Rightarrow> 'a USET \<Rightarrow> 'a USET" where
"utminus_USET xs ys = MinusUS xs ys"

instance ..
end

declare utminus_USET_def [simp]

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

abbreviation FMinusPE ::
  "('a :: DEFINED UFSET, 'm :: FSET_SORT) WF_PEXPRESSION \<Rightarrow> 
   ('a UFSET, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a UFSET, 'm) WF_PEXPRESSION" where
"FMinusPE \<equiv> Op2PE MinusUF"

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

abbreviation FSubsetPE ::
  "('a :: DEFINED UFSET, 'm :: {BOOL_SORT, FSET_SORT}) WF_PEXPRESSION \<Rightarrow> 
   ('a UFSET, 'm) WF_PEXPRESSION \<Rightarrow> 
   (bool, 'm) WF_PEXPRESSION" where
"FSubsetPE \<equiv> Op2PE SubsetUF"

abbreviation FSubseteqPE ::
  "('a :: DEFINED UFSET, 'm :: {BOOL_SORT, FSET_SORT}) WF_PEXPRESSION \<Rightarrow> 
   ('a UFSET, 'm) WF_PEXPRESSION \<Rightarrow> 
   (bool, 'm) WF_PEXPRESSION" where
"FSubseteqPE \<equiv> Op2PE SubseteqUF"

(*
abbreviation IntersyncPE ::
  "('a :: DEFINED set, 'm :: {FSET_SORT, LIST_SORT, SET_SORT}) WF_PEXPRESSION \<Rightarrow>
   ('a ULIST, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a ULIST, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('a ULIST UFSET, 'm) WF_PEXPRESSION" where
"IntersyncPE \<equiv> Op3PE IntersyncUF"

abbreviation FilterPE ::
  "('a ULIST, 'm :: {FSET_SORT, LIST_SORT, SET_SORT}) WF_PEXPRESSION \<Rightarrow> 
   ('a :: DEFINED set, 'm) WF_PEXPRESSION \<Rightarrow>

   ('a ULIST, 'm) WF_PEXPRESSION" where
"FilterPE \<equiv> Op2PE FilterUL"
*)

instantiation UFSET :: (DEFINED) MINUS
begin

definition utminus_UFSET :: "'a UFSET \<Rightarrow> 'a UFSET \<Rightarrow> 'a UFSET" where
"utminus_UFSET xs ys = MinusUF xs ys"

instance ..
end

declare utminus_UFSET_def [simp]


(*
lemma FUnionPE_type: 
  "\<tau>\<^sub>* (FUnionPE (xs :: ('a :: DEFINED UFSET , 'm :: FSET_SORT) WF_PEXPRESSION) ys) 
   = FSetType TYPEU('a)"
  by (simp add: WF_PEXPRESSION_type_def)
*)

subsection {* Action Expressions *}

definition PEV :: "'a CHAN \<Rightarrow> 'a \<Rightarrow> ('m :: EVENT_SORT) EVENT" where
"PEV c v = EV (chan_name c) TYPEU('a) (InjU v)"

abbreviation EventPE ::
  "'a CHAN \<Rightarrow> ('a, 'm :: EVENT_SORT) WF_PEXPRESSION 
           \<Rightarrow> ('m EVENT, 'm) WF_PEXPRESSION" where
"EventPE n v \<equiv> Op1PE (PEV n) v"

(*
abbreviation ReceivePE ::
  "'a CHANNEL \<Rightarrow> ('a \<Rightarrow> ('b, 'm :: EVENT_SORT) WF_PEXPRESSION)
*)

abbreviation ChannelPE ::
  "('m::EVENT_SORT EVENT, 'm) WF_PEXPRESSION \<Rightarrow> 
   ('m UCHAN, 'm) WF_PEXPRESSION" where
"ChannelPE \<equiv> Op1PE EVENT_chan"

text {* Channel type erasure *}

definition CHAN_UCHAN :: "'a::type CHAN \<Rightarrow> ('m :: VALUE) UCHAN" where
"CHAN_UCHAN c = MkUCHAN ((chan_name c), TYPEU('a))"

setup {*
Adhoc_Overloading.add_variant @{const_name erase} @{const_name CHAN_UCHAN}
*}

subsection {* Permutation *}

definition PermPE ::
  "('m :: VALUE) VAR_RENAME \<Rightarrow>
   ('a, 'm) WF_PEXPRESSION \<Rightarrow>   
   ('a, 'm) WF_PEXPRESSION" where
"PermPE ss e = MkPExpr (\<lbrakk>e\<rbrakk>\<^sub>* \<circ> (RenameB (inv\<^sub>s ss)))"

setup {*
Adhoc_Overloading.add_variant @{const_name permute} @{const_name PermPE}
*}

lemma EvalPE_RenamePE [eval,evale,evalp]:
  "\<lbrakk>ss\<bullet>e\<rbrakk>\<^sub>*b = \<lbrakk>e\<rbrakk>\<^sub>*((inv\<^sub>s ss)\<bullet>b)"
  by (simp add:PermPE_def)

lemma RenamePE_VarPE [urename]:
  "ss\<bullet>(VarPE x) = VarPE (ss\<bullet>x)"
  by (auto simp add:eval)

lemma SS_PUNDASHED_app [urename]:
  "x \<in> PUNDASHED \<Longrightarrow> SS\<bullet>x = x\<acute>"
  by (simp add:PermPV_def urename closure)

lemma SS_PDASHED_app [urename]:
  "x \<in> PDASHED \<Longrightarrow> SS\<bullet>x = x~"
  apply (simp add:PermPV_def urename closure)
  apply (metis PVAR_VAR_inv PVAR_VAR_pvundash)
done

lemma SS_PDASHED_TWICE_app [urename]:
  "x \<in> PDASHED_TWICE \<Longrightarrow> SS\<bullet>x = x"
  by (simp add:PermPV_def urename closure)

lemma RenameB_rep_eq_ty [simp]:
  "\<langle>ss \<bullet> b\<rangle>\<^sub>* = \<langle>b\<rangle>\<^sub>* \<circ> inv \<langle>ss\<rangle>\<^sub>s\<^sub>*"
  apply (rule)
  apply (simp add:Rep_binding_ty_def)
  apply (metis (hide_lams, no_types) PVAR_VAR_RENAME Rep_VAR_RENAME_surj UNIV_I VAR_PVAR_erase_simps(1) f_inv_into_f rangeI rename_inv_rep_eq)
done

lemma PermPV_inv [simp]: 
  "\<langle>inv\<^sub>s ss\<rangle>\<^sub>s\<^sub>* = inv \<langle>ss\<rangle>\<^sub>s\<^sub>*"
  apply (rule)
  apply (simp add:PermPV_def)
  apply (metis (hide_lams, no_types) PVAR_VAR_RENAME PVAR_VAR_inv Rep_VAR_RENAME_surj f_inv_into_f rangeI rename_inv_inv rename_inv_rep_eq surj_iff_all)
done
  
lemma PermPV_app_inv [urename]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "ss \<in> VAR_RENAME_INV"
  shows "inv (op \<bullet> ss) x = ss\<bullet>x"
  using assms by (metis PermPV_inv VAR_RENAME_INV_inv)

lemma SS_PUNDASHED [urename]:
  "x \<in> PUNDASHED \<Longrightarrow> SS\<bullet>x = x\<acute>"
  by (simp add:PermPV_def urename closure)

lemma SS_PDASHED [urename]:
  "x \<in> PUNDASHED \<Longrightarrow> SS\<bullet>x\<acute> = x"
  by (simp add:PermPV_def urename closure)

lemma RenamePE_PVarPE [urename]:
  "ss\<bullet>(PVarPE x) = PVarPE (\<langle>ss\<rangle>\<^sub>s\<^sub>* x)"
  apply (auto simp add:evalp)
  apply (metis PermPV_inv rename_inv_inv)
done

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

lemma RenameE_RenamePE [urename]:
  fixes e :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "TYPEUSOUND('a, 'm)"
  shows "ss \<bullet> (e\<down>) = (ss \<bullet> e)\<down>"
  by (simp add:evale evalp closure typing defined assms)

lemma RenameP_RenamePE [urename]:
  fixes e :: "(bool, 'm :: VALUE) WF_PEXPRESSION"
  assumes "TYPEUSOUND(bool, 'm)"
  shows "ss \<bullet> (PExprP e) = PExprP (ss \<bullet> e)"
  apply (utp_pred_tac)
  apply (utp_poly_tac)
done

lemma RenamePE_PExprPE [urename]:
  fixes e :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "TYPEUSOUND('a, 'm)"
  shows "ss\<bullet>(PExprE e) = PExprE (ss\<bullet>e)"
  by (auto simp add:evale assms)

subsection {* Variable Priming *}

definition PrimePE ::
   "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow>   
   ('a, 'm) WF_PEXPRESSION" where
"PrimePE e = PermPE SS e"

setup {*
Adhoc_Overloading.add_variant @{const_name prime} @{const_name PrimePE}
*}

lemma PrimePE_PExprE [urename]:  
  fixes e :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "TYPEUSOUND('a, 'm)"
  shows "(PExprE e)\<acute> = (PExprE e\<acute>)"
  by (simp add:PrimePE_def PrimeE_def urename assms)

subsection {* Substitution *}

definition SubstPE :: 
"('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 
 ('b, 'm) WF_PEXPRESSION \<Rightarrow> 
 'm VAR \<Rightarrow> 
 ('a, 'm) WF_PEXPRESSION" where
"SubstPE f v x = MkPExpr (\<lambda> b. \<lbrakk>f\<rbrakk>\<^sub>* (b(x :=\<^sub>b InjU (\<lbrakk>v\<rbrakk>\<^sub>* b))))"

definition PSubstPE :: 
"('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 
 ('b :: DEFINED, 'm) WF_PEXPRESSION \<Rightarrow> 
 ('b, 'm) PVAR \<Rightarrow> 
 ('a, 'm) WF_PEXPRESSION" ("_[_'/\<^sub>*_]" [200] 200) where
"PSubstPE f v x \<equiv> SubstPE f v x\<down>"

abbreviation PSubstP :: 
"('m :: VALUE) WF_PREDICATE \<Rightarrow> 
 ('b, 'm) WF_PEXPRESSION \<Rightarrow> 
 ('b, 'm) PVAR \<Rightarrow> 
 'm WF_PREDICATE" where
"PSubstP p e x \<equiv> SubstP p e\<down> x\<down>"

lemma EvalPE_SubstPE [eval,evale,evalp]:
  "\<lbrakk>SubstPE e v x\<rbrakk>\<^sub>*b = \<lbrakk>e\<rbrakk>\<^sub>* (b(x :=\<^sub>b InjU (\<lbrakk>v\<rbrakk>\<^sub>* b)))"
  by (simp add:SubstPE_def)

lemma EvalPE_PSubstPE:
  "\<lbrakk>PSubstPE e v x\<rbrakk>\<^sub>*b = \<lbrakk>e\<rbrakk>\<^sub>* (b(x\<down> :=\<^sub>b InjU (\<lbrakk>v\<rbrakk>\<^sub>* b)))"
  by (simp add:PSubstPE_def SubstPE_def)

lemma EvalPE_PSubstPE_typed [eval,evale,evalp]:
  "\<lbrakk>PSubstPE e v x\<rbrakk>\<^sub>*b = \<lbrakk>e\<rbrakk>\<^sub>* (b(x :=\<^sub>* \<lbrakk>v\<rbrakk>\<^sub>* b))"
  by (simp add:eval EvalPE_PSubstPE binding_upd_ty_def)

lemma PExprP_SubstPE [evalp]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "v \<rhd>\<^sub>* x"
  shows "(PSubstPE e v x)\<down> = SubstP e\<down> v\<down> x\<down>"
  apply (insert assms)
  apply (frule pevar_compat_TYPEUSOUND)
  apply (simp add:SubstPE_def PSubstPE_def PExprP_def SubstP_def PExprE_rep_eq)
done

lemma InjU_EvalPE_compat [typing]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "v \<rhd>\<^sub>* x"
  shows "InjU (\<lbrakk>v\<rbrakk>\<^sub>* b) \<rhd> x\<down>"
  by (simp add: typing assms)

lemma PSubstPE_PVarPE [usubst]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "v \<rhd>\<^sub>* x"
  shows "PSubstPE (PVarPE x) v x = v"
  apply (insert assms)
  apply (frule pevar_compat_TYPEUSOUND)
  apply (auto simp add: evalp binding_upd_ty_def Rep_binding_ty_def typing)
done

lemma PSubstPE_PVarPE_different [usubst]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "v \<rhd>\<^sub>* x" "x\<down> \<noteq> y\<down>"
  shows "PSubstPE (PVarPE y) v x = PVarPE y"
  using assms by (auto simp add: evalp binding_upd_ty_def Rep_binding_ty_def typing)

lemma PSubstPE_ProdPE [usubst]:
  "ProdPE u v[e/\<^sub>*x] = ProdPE (u[e/\<^sub>*x]) (v[e/\<^sub>*x])"
  by (auto simp add:evalp)

lemma PSubstPE_LitPE [usubst]:
  "PSubstPE (LitPE v) x e = LitPE v"
  by (auto simp add:evalp)

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
  assumes "v \<rhd>\<^sub>* x"
  shows "e\<down>[v\<down>/\<^sub>px\<down>] = (PSubstPE e v x)\<down>" 
  using assms by (utp_poly_tac)

lemma SubstP_PSubstPE_dash [usubst]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "v \<rhd>\<^sub>* x"
  shows "e\<down>[v\<down>/\<^sub>px\<down>\<acute>] = (PSubstPE e v x\<acute>)\<down>"
  using assms 
  by (utp_poly_tac)

lemma SubstP_PSubstPE_dash_dash [usubst]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "v \<rhd>\<^sub>* x"
  shows "e\<down>[v\<down>/\<^sub>px\<down>\<acute>\<acute>] = (PSubstPE e v x\<acute>\<acute>)\<down>" 
  using assms
  by (utp_poly_tac)

lemma SubstP_PSubstPE_dash_dash_dash [usubst]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "v \<rhd>\<^sub>* x"
  shows "e\<down>[v\<down>/\<^sub>px\<down>\<acute>\<acute>\<acute>] = (PSubstPE e v x\<acute>\<acute>\<acute>)\<down>"
  using assms  
  by (utp_poly_tac)

lemma PSubstPE_PVarPE_neq [usubst]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  and   x :: "('b :: DEFINED, 'm :: VALUE) PVAR"
  assumes "x\<down> \<noteq> y\<down>" "v \<rhd>\<^sub>* y"
  shows "PSubstPE (PVarPE x) v y = PVarPE x"
  using assms by (utp_poly_auto_tac)

lemma PSubstPE_VarP_single_UNREST:
  "{x\<down>} \<sharp> v \<Longrightarrow> v[e/\<^sub>*x] = v"
  by (auto simp add:evalp unrest UNREST_PEXPR_def)

lemma SubstE_PSubstPE [usubst]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  and   e :: "('b :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "TYPEUSOUND('a, 'm)" "TYPEUSOUND('b, 'm)" "v \<rhd>\<^sub>* x"
  shows "e\<down>[v\<down>/\<^sub>ex\<down>] = (PSubstPE e v x)\<down>"
  using assms 
  by (auto simp add:evale typing defined evalp binding_upd_ty_def)

lemma SubstE_PSubstPE_dash [usubst]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  and   e :: "('b :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "TYPEUSOUND('a, 'm)" "TYPEUSOUND('b, 'm)" "v \<rhd>\<^sub>* x\<acute>"
  shows "e\<down>[v\<down>/\<^sub>ex\<down>\<acute>] = (PSubstPE e v x\<acute>)\<down>"
  using assms by (auto simp add:evale typing defined evalp erasure  binding_upd_ty_def)

lemma SubstE_PSubstPE_dash_dash [usubst]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  and   e :: "('b :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "TYPEUSOUND('a, 'm)" "TYPEUSOUND('b, 'm)" "v \<rhd>\<^sub>* x\<acute>\<acute>"
  shows "e\<down>[v\<down>/\<^sub>ex\<down>\<acute>\<acute>] = (PSubstPE e v x\<acute>\<acute>)\<down>"
  using assms by (auto simp add:evale typing defined evalp erasure binding_upd_ty_def)

lemma SubstE_PSubstPE_dash_dash_dash [usubst]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  and   e :: "('b :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "TYPEUSOUND('a, 'm)" "TYPEUSOUND('b, 'm)" "v \<rhd>\<^sub>* x\<acute>\<acute>\<acute>"
  shows "e\<down>[v\<down>/\<^sub>ex\<down>\<acute>\<acute>\<acute>] = (PSubstPE e v x\<acute>\<acute>\<acute>)\<down>"
  using assms by (auto simp add:evale typing defined evalp erasure binding_upd_ty_def)

lemma SubstP_PSubstPE_TrueE [usubst]:
  fixes e :: "(bool, 'm :: BOOL_SORT) WF_PEXPRESSION"
  and   x :: "(bool, 'm) PVAR"
  shows "e\<down>[TrueE/\<^sub>px\<down>] = (PSubstPE e TruePE x)\<down>"
  using assms 
  by (simp add:EvalP_SubstP eval evalp binding_upd_ty_def inju)

lemma SubstP_PSubstPE_FalseE [usubst]:
  fixes e :: "(bool, 'm :: BOOL_SORT) WF_PEXPRESSION"
  and   x :: "(bool, 'm) PVAR"
  shows "e\<down>[FalseE/\<^sub>px\<down>] = (PSubstPE e FalsePE x)\<down>"
  using assms 
  by (simp add:EvalP_SubstP eval evalp binding_upd_ty_def inju)

lemma PVarPE_VarP [simp]:
  fixes x :: "(bool, 'm::BOOL_SORT) PVAR"
  shows "((PVarPE x)\<down> ==\<^sub>p (TruePE\<down>)) = VarP (x\<down>)"
  by (utp_poly_tac)

lemma NotP_PVarPE_VarP [simp]:
  fixes x :: "(bool, 'm::BOOL_SORT) PVAR"
  shows "((PVarPE x)\<down> ==\<^sub>p (FalsePE\<down>)) = \<not>\<^sub>p $\<^sub>p(x\<down>)"
  by (utp_poly_tac)

lemma binding_upd_drop_ty [simp]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "\<langle>b\<rangle>\<^sub>*x = v" "pvaux x"
  shows "b(x :=\<^sub>* v) = b"
  using assms
  apply (simp add:binding_upd_ty_def Rep_binding_ty_def)
  apply (drule sym, simp add:closure typing defined)
  apply (subst TypeUSound_ProjU_inv)
  apply (simp_all add:defined typing)
  apply (metis PVAR_binding_defined_aux PVAR_binding_type dtype_relI)
done

ML {* simp_tac *}

lemma PVarPE_PSubstPE:
  fixes x :: "(bool, 'm :: BOOL_SORT) PVAR"
  assumes "pvaux x"
  shows "($\<^sub>p(x\<down>) \<and>\<^sub>p P) = ($\<^sub>p(x\<down>) \<and>\<^sub>p (PSubstP P TruePE x))"
  using assms by (utp_poly_auto_tac)

lemma NotP_PVarPE_PSubstPE:
  fixes x :: "(bool, 'm :: BOOL_SORT) PVAR"
  assumes "TYPEUSOUND(bool, 'm)" "pvaux x"
  shows "(\<not>\<^sub>p $\<^sub>p(x\<down>) \<and>\<^sub>p P) = (\<not>\<^sub>p $\<^sub>p(x\<down>) \<and>\<^sub>p (PSubstP P FalsePE x))"
  using assms by (utp_poly_auto_tac)

lemma ExprP_TruePE [simp]:
  "ExprP (TruePE\<down>) = TrueP"
  by (simp add:eval closure typing inju)

lemma ExprP_FalsePE [simp]:
  "ExprP (FalsePE\<down>) = FalseP"
  by (simp add:eval closure typing inju)

lemma PUNDASHED_WF_CONDITION[closure]: 
  "x \<in> PUNDASHED \<Longrightarrow> VarP (x\<down>) \<in> WF_CONDITION"
  by (metis PVAR_VAR_PUNDASHED_UNDASHED VarP_cond_closure)

(* Add support for polymorphic expressions to the relational tactic *)

lemma EvalR_PExprP [evalr,evalpr]: 
  "NON_REL_VAR \<sharp> e \<Longrightarrow>
   \<lbrakk>e\<down>\<rbrakk>R = {(b, b'). \<lbrakk>e\<rbrakk>\<^sub>* (b \<oplus>\<^sub>b SS\<bullet>b' on DASHED) \<and> b \<in> WF_REL_BINDING \<and> b' \<in> WF_REL_BINDING \<and> b \<cong> b' on NON_REL_VAR}"
  apply (simp add:EvalR_as_EvalP EvalP_PExprP)
  apply (auto simp add:BindR_def urename typing defined closure RenameB_override_distr1)
  apply (metis RenameB_equiv_VAR_RENAME_ON_2 SS_VAR_RENAME_ON UNDASHED_DASHED_inter(16) binding_override_left_eq)
  apply (rule_tac x="xa \<oplus>\<^sub>b SS\<bullet>y on DASHED" in exI)
  apply (auto simp add:BindR_def urename typing defined closure RenameB_override_distr1)
  apply (metis WF_REL_BINDING_bc_DASHED binding_override_equiv)
  apply (metis (lifting, no_types) NON_REL_VAR_def SS_REL_VAR_overshadow WF_REL_BINDING_bc_DASHED binding_override_assoc binding_override_equiv binding_override_overshadow2 binding_override_simps(2))
done

lemma EvalR_AssignR_typed [evalpr]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "x \<in> PUNDASHED" "D\<^sub>1 \<sharp> e" "TYPEUSOUND('a, 'm)"
  shows "\<lbrakk>x\<down> :=\<^sub>R e\<down>\<rbrakk>R = {(b, b(x:=\<^sub>* (\<lbrakk>e\<rbrakk>\<^sub>* b))) | b. b \<in> WF_REL_BINDING}"
  using assms
  apply (subst EvalR_AssignR)
  apply (simp add:closure typing unrest)
  apply (metis UNREST_PExprE)
  apply (simp_all add: unrest binding_upd_ty_def evale pevar_compat_TYPEUSOUND)
done

theorem EvalR_SubstP_UNDASHED_ty [evalr, evalpr] :
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes 
    "TYPEUSOUND('a, 'm)"
    "x \<in> PUNDASHED" 
    "DASHED \<sharp> e"
  shows "\<lbrakk>p[e\<down>/\<^sub>px\<down>]\<rbrakk>R = {(b1, b2) | b1 b2. (b1(x :=\<^sub>* \<lbrakk>e\<rbrakk>\<^sub>*b1), b2) \<in> \<lbrakk>p\<rbrakk>R}"
  apply (subst SubstP_rel_UNDASHED)
  apply (simp_all add:evale typing closure defined assms unrest binding_upd_ty_def)
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
 
declare NilUL.rep_eq [evalp]
declare ConsUL_rep_eq [evalp]
declare AppendUL.rep_eq [evalp]
declare MinusUL.rep_eq [evalp]
declare PrefixUL.rep_eq [evalp]
declare PrefixeqUL.rep_eq [evalp]

declare drop_map [eval,evalr,evalp]

end