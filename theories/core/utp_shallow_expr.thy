(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_shallow_expr.thy                                                 *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Shallowly Embedded Polymorphic Expressions *}

theory utp_shallow_expr
imports 
  utp_expr
  "../tactics/utp_expr_tac"
  "../laws/utp_subst_laws"
  utp_event
  utp_rel
begin

default_sort type

subsection {* Polymorphic constants *}

consts 
  TypeU :: "'a itself \<Rightarrow> ('m :: VALUE) UTYPE"
  InjU  :: "'a \<Rightarrow> 'm :: VALUE"
  ProjU :: "'m :: VALUE \<Rightarrow> 'a"

syntax
  "_TYPEU" :: "type => logic"  ("(1TYPEU/(1'(_')))")

translations "TYPEU('a)" == "CONST TypeU TYPE('a)"

definition MkPEvent :: "'a PEvent \<Rightarrow> 'm :: EVENT_SORT" where
"MkPEvent e = MkEvent (Abs_EVENT ((fst e, TypeU TYPE('a)), InjU (snd e)))"

definition DestPEvent :: "'m :: EVENT_SORT \<Rightarrow> 'a PEvent" where
"DestPEvent x = (fst (EVENT_channel (DestEvent x)), ProjU (EVENT_value (DestEvent x)))"

defs (overloaded)
  InjU_bool [simp]:  "InjU (x :: bool) \<equiv> MkBool x"
  ProjU_bool [simp]: "ProjU (x :: ('a :: BOOL_SORT)) \<equiv> DestBool x"
  TypeU_bool [simp]: "TypeU (x :: bool itself) \<equiv> BoolType"

  InjU_int [simp]:  "InjU (x :: int) \<equiv> MkInt x"
  ProjU_int [simp]: "ProjU (x :: ('a :: INT_SORT)) \<equiv> DestInt x"
  TypeU_int [simp]: "TypeU (x :: int itself) \<equiv> IntType"

  InjU_event [simp]:  "InjU (x :: 'a PEvent) \<equiv> MkPEvent x"
  ProjU_event [simp]: "ProjU (x :: ('a :: EVENT_SORT)) \<equiv> DestPEvent x"
  TypeU_event [simp]: "TypeU (x :: 'a PEvent itself) \<equiv> EventType"

  InjU_list [simp]: "InjU (xs :: 'a list) \<equiv> MkList (TypeU (TYPE('a))) (map InjU xs)"
  ProjU_list [simp]: "ProjU (xs :: ('a :: LIST_SORT)) \<equiv> map ProjU (DestList xs)"
  TypeU_list [simp]: "TypeU (x :: ('a list) itself) \<equiv> ListType (TypeU TYPE('a))"

  InjU_fset [simp]: "InjU (xs :: 'a fset) \<equiv> MkFSet (TypeU (TYPE('a))) (InjU `\<^sub>f xs)"
  ProjU_fset [simp]: "ProjU (xs :: ('a :: FSET_SORT)) \<equiv> ProjU `\<^sub>f (DestFSet xs)"
  TypeU_fset [simp]: "TypeU (x :: ('a fset) itself) \<equiv> FSetType (TypeU TYPE('a))"  

text {* TypeUSound can be thought of as a two-parameter type class which stores
        the properties of the above polymorphic constants, namely that the
        given Isabelle type can be constructed under the given sort constraints *}

definition TypeUSound :: "'a itself \<Rightarrow> 'm::VALUE itself \<Rightarrow> bool" where
"TypeUSound a m \<longleftrightarrow> (\<forall> (x :: 'a). (InjU x :: 'm) :! TypeU a) \<and>
                    (\<forall> (x :: 'a). (ProjU (InjU x :: 'm) = x))"

syntax
  "_TYPEUSOUND" :: "type \<Rightarrow> type => logic"  ("(1TYPEUSOUND/(1'(_, _')))")

translations "TYPEUSOUND('a, 'm)" == "CONST TypeUSound TYPE('a) TYPE('m)"

lemma TypeUSound_intro [intro]:
  "\<lbrakk> \<And> (x :: 'a). (InjU x :: 'm) :! TYPEU('a)
   ; \<And> (x :: 'a). (ProjU (InjU x :: 'm) = x) \<rbrakk> \<Longrightarrow>
   TYPEUSOUND('a, 'm :: VALUE)"
  by (simp add:TypeUSound_def)

lemma TypeUSound_InjU_type [typing]:
  fixes x :: "'a"
  assumes "TYPEUSOUND('a, 'm :: VALUE)"
  shows "(InjU x :: 'm) :! TYPEU('a)"
  using assms by (auto simp add:TypeUSound_def)

lemma TypeUSound_InjU_defined [defined]:
  fixes x :: "'a"
  assumes "TYPEUSOUND('a, 'm :: VALUE)"
  shows "\<D> (InjU x :: 'm)"
  by (auto intro:assms typing defined)

lemma TypeUSound_InjU_inv [simp]:
  fixes x :: "'a"
  assumes "TYPEUSOUND('a, 'm :: VALUE)"
  shows "ProjU (InjU x :: 'm) = x"
  using assms by (auto simp add:TypeUSound_def)

lemma TypeUSound_bool [typing]: "TYPEUSOUND(bool, 'm :: BOOL_SORT)"
  by (simp add:TypeUSound_def typing)

lemma TypeUSound_int [typing]: "TYPEUSOUND(int, 'm :: INT_SORT)"
  by (simp add:TypeUSound_def typing)

lemma TypeUSound_list [typing]: 
  "\<lbrakk> (TYPEU('a) :: 'm UTYPE) \<in> ListPerm; TYPEUSOUND('a, 'm) \<rbrakk> 
     \<Longrightarrow> TYPEUSOUND('a list, 'm :: LIST_SORT)"
  apply (auto simp add:dcarrier_def TypeUSound_def)
  apply (rule typing, auto)
  apply (subgoal_tac "set (map InjU x) \<subseteq> dcarrier (TYPEU('a) :: 'm UTYPE)")
  apply (auto simp add:comp_def)
done

lemma TypeUSound_fset [typing]: 
  "\<lbrakk> (TYPEU('a) :: 'm UTYPE) \<in> FSetPerm; TYPEUSOUND('a, 'm) \<rbrakk> 
     \<Longrightarrow> TYPEUSOUND('a fset, 'm :: FSET_SORT)"
  apply (simp add:dcarrier_def TypeUSound_def)
  apply (rule)
  apply (clarify)
  apply (rule typing)
  apply (force)
  apply (force)
  apply (clarify)
  apply (subgoal_tac "\<langle>InjU `\<^sub>f x\<rangle>\<^sub>f \<subseteq> dcarrier (TYPEU('a) :: 'm UTYPE)")
  apply (auto simp add:image_def)
done

lemma TypeUSound_PEvent [typing]:
  "\<lbrakk> (TYPEU('a) :: 'm UTYPE) \<in> EventPerm; TYPEUSOUND('a, 'm) \<rbrakk>
     \<Longrightarrow> TYPEUSOUND('a PEvent, 'm :: EVENT_SORT)"
  by (auto simp add:MkPEvent_def typing DestPEvent_def)

subsection {* Polymorphic Expression Basic Syntax *}

typedef ('a, 'm :: VALUE) WF_PEXPRESSION = "UNIV :: ('m WF_BINDING \<Rightarrow> 'a) set" ..

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

definition LitPE :: "'a \<Rightarrow> ('a, 'm :: VALUE) WF_PEXPRESSION" where
"LitPE v = Abs_WF_PEXPRESSION (\<lambda> b. v)"

lemma EvalPE_LitPE [evale]:
  "\<lbrakk>LitPE v\<rbrakk>\<^sub>*b = v"
  by (simp add:LitPE_def)

lemma WF_PEXPRESSION_tau [typing]:
  fixes v :: "('a, 'm :: VALUE) WF_PEXPRESSION"
  shows "\<tau>\<^sub>*(v) = TypeU(TYPE('a))"
  by (simp add:WF_PEXPRESSION_type_def)

definition pevar_compat :: 
  "('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 'm VAR \<Rightarrow> bool" (infix "\<rhd>\<^sub>*" 50) where
"pevar_compat e x \<equiv> \<forall>b. InjU (\<lbrakk>e\<rbrakk>\<^sub>* b) \<rhd> x"

typedef ('a, 'm :: VALUE) PVAR = "UNIV :: (NAME * bool) set"
  by auto

declare Rep_PVAR [simp]
declare Rep_PVAR_inverse [simp]
declare Abs_PVAR_inverse [simp]

definition MkPVAR :: "NAME \<Rightarrow> bool \<Rightarrow> 'a itself \<Rightarrow> 'm itself \<Rightarrow> ('a, 'm :: VALUE) PVAR" where
"MkPVAR n s a t = Abs_PVAR (n, s)"

abbreviation pvname :: "('a, 'm :: VALUE) PVAR \<Rightarrow> NAME" where
"pvname x \<equiv> fst (Rep_PVAR x)"

abbreviation pvaux :: "('a, 'm :: VALUE) PVAR \<Rightarrow> bool" where
"pvaux x \<equiv> snd (Rep_PVAR x)"

lemma pvname_MkPVAR [simp]:
  "pvname (MkPVAR n s a m) = n"
  by (simp add:MkPVAR_def)

lemma pvaux_MkPVAR [simp]:
  "pvaux (MkPVAR n s a m) = s"
  by (simp add:MkPVAR_def)

definition pvundash :: "('a, 'm :: VALUE) PVAR \<Rightarrow> ('a, 'm :: VALUE) PVAR" where
"pvundash v = Abs_PVAR (MkName (name_str (pvname v)) (dashes (pvname v) - 1) (subscript (pvname v)), pvaux v)"

definition pvdash :: "('a, 'm :: VALUE) PVAR \<Rightarrow> ('a, 'm :: VALUE) PVAR" where
"pvdash v = Abs_PVAR (MkName (name_str (pvname v)) (dashes (pvname v) + 1) (subscript (pvname v)), pvaux v)"

definition PVAR_VAR :: "('a, 'm) PVAR \<Rightarrow> ('m :: VALUE) VAR" where
"PVAR_VAR v = MkVar (pvname v) (TypeU TYPE('a)) (pvaux v)"

definition VAR_PVAR :: "('m :: VALUE) VAR \<Rightarrow> ('a, 'm) PVAR" where
"VAR_PVAR v = Abs_PVAR (name v, aux v)"

lemma PVAR_VAR_inv [simp]: 
  "VAR_PVAR (PVAR_VAR v) = v"
  by (simp add:PVAR_VAR_def VAR_PVAR_def)

lemma VAR_PVAR_inv [simp]: 
  "vtype x = TYPEU('a) \<Longrightarrow> PVAR_VAR (VAR_PVAR x :: ('a, 'm :: VALUE) PVAR) = x"
  apply (case_tac x)
  apply (auto simp add:PVAR_VAR_def VAR_PVAR_def MkVar_def)
done

lemma PVAR_VAR_pvdash [simp]:
  "PVAR_VAR (pvdash x) = dash (PVAR_VAR x)"
  by (auto simp add:PVAR_VAR_def dash_def pvdash_def)

lemma PVAR_VAR_compat [typing]:
  fixes e :: "('a, 'm :: VALUE) WF_PEXPRESSION" 
  and   x :: "('a, 'm) PVAR"
  assumes "TYPEUSOUND('a, 'm)"
  shows "e \<rhd>\<^sub>* PVAR_VAR x"
  apply (auto simp add:pevar_compat_def PVAR_VAR_def assms typing var_compat_def)
  apply (simp add:assms defined)
done

abbreviation "PUNDASHED     \<equiv> {x. PVAR_VAR x \<in> UNDASHED}"
abbreviation "PDASHED       \<equiv> {x. PVAR_VAR x \<in> DASHED}"
abbreviation "PDASHED_TWICE \<equiv> {x. PVAR_VAR x \<in> DASHED_TWICE}"

definition "VarPE x = Abs_WF_PEXPRESSION (\<lambda> b. ProjU (\<langle>b\<rangle>\<^sub>b x))"

abbreviation PVarPE :: "('a, 'm :: VALUE) PVAR \<Rightarrow> ('a, 'm) WF_PEXPRESSION" where
"PVarPE x \<equiv> VarPE (PVAR_VAR x)"

lemma EvalPE_VarPE [evale]:
  "\<lbrakk>VarPE x\<rbrakk>\<^sub>*b = ProjU (\<langle>b\<rangle>\<^sub>b x)"
  by (simp add:VarPE_def)

lemma EvalPE_PVarPE [evale]:
  "\<lbrakk>PVarPE x\<rbrakk>\<^sub>*b = ProjU (\<langle>b\<rangle>\<^sub>b (PVAR_VAR x))"
  by (simp add:VarPE_def)

definition "Op1PE f u = Abs_WF_PEXPRESSION (\<lambda> b. f (Rep_WF_PEXPRESSION u b))"

lemma EvalPE_Op1PE [evale]:
  "\<lbrakk>Op1PE f u\<rbrakk>\<^sub>*b = f (\<lbrakk>u\<rbrakk>\<^sub>*b)"
  by (simp add:Op1PE_def)

definition "Op2PE f u v = Abs_WF_PEXPRESSION (\<lambda> b. f (Rep_WF_PEXPRESSION u b) (Rep_WF_PEXPRESSION v b))"

lemma EvalPE_Op2PE [evale]:
  "\<lbrakk>Op2PE f u v\<rbrakk>\<^sub>*b = f (\<lbrakk>u\<rbrakk>\<^sub>*b) (\<lbrakk>v\<rbrakk>\<^sub>*b)"
  by (simp add:Op2PE_def)

definition "Op3PE f u v w = Abs_WF_PEXPRESSION (\<lambda> b. f (Rep_WF_PEXPRESSION u b) (Rep_WF_PEXPRESSION v b) (Rep_WF_PEXPRESSION w b))"

lemma EvalPE_Op3PE [evale]:
  "\<lbrakk>Op3PE f u v w\<rbrakk>\<^sub>*b = f (\<lbrakk>u\<rbrakk>\<^sub>*b) (\<lbrakk>v\<rbrakk>\<^sub>*b) (\<lbrakk>w\<rbrakk>\<^sub>*b)"
  by (simp add:Op3PE_def)

abbreviation "EqualPE \<equiv> Op2PE (op =)"

definition PExprE :: "('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 'm WF_EXPRESSION" where
"PExprE f = Abs_WF_EXPRESSION (InjU \<circ> Rep_WF_PEXPRESSION f)"

lemma PExprE_rep_eq:
  fixes e :: "('a, 'm :: VALUE) WF_PEXPRESSION" 
  assumes "TypeUSound TYPE('a) TYPE('m)"
  shows "\<langle>PExprE e\<rangle>\<^sub>e b = InjU (Rep_WF_PEXPRESSION e b)"
  apply (subgoal_tac "(InjU \<circ> Rep_WF_PEXPRESSION e) \<in> WF_EXPRESSION")
  apply (simp add:PExprE_def)
  apply (auto simp add:WF_EXPRESSION_def)
  apply (rule_tac x="TypeU TYPE('a)" in exI)
  apply (insert assms)
  apply (auto simp add:TypeUSound_def)
done

lemma EvalE_PExprE [evale]:
  fixes e :: "('a, 'm :: VALUE) WF_PEXPRESSION" 
  assumes "TypeUSound TYPE('a) TYPE('m)"
  shows "\<lbrakk>PExprE e\<rbrakk>\<epsilon>b = InjU (\<lbrakk>e\<rbrakk>\<^sub>*b)"
  by (simp add:EvalE_def PExprE_rep_eq assms)

lemma PExprE_type [typing]:
  fixes e :: "('a, 'm :: VALUE) WF_PEXPRESSION" 
  assumes "TypeUSound TYPE('a) TYPE('m)" 
  and "t = \<tau>\<^sub>* e"
  shows "PExprE e :\<^sub>e t"
  apply (simp add: etype_rel_def PExprE_rep_eq assms WF_PEXPRESSION_type_def)
  apply (metis TypeUSound_def assms dtype_type)
done

subsection {* Boolean Expressions *}

abbreviation TruePE :: "(bool, 'm :: BOOL_SORT) WF_PEXPRESSION" where
"TruePE \<equiv> LitPE True"

abbreviation FalsePE :: "(bool, 'm :: BOOL_SORT) WF_PEXPRESSION" where
"FalsePE \<equiv> LitPE False"

lemma TruePE_tau: "\<tau>\<^sub>* TruePE = BoolType"
  by (simp add:WF_PEXPRESSION_type_def)

lemma FalsePE_tau: "\<tau>\<^sub>* FalsePE = BoolType"
  by (simp add:WF_PEXPRESSION_type_def)

subsection {* Integer Expressions *}

abbreviation IntPE :: "int \<Rightarrow> (int, 'a :: INT_SORT) WF_PEXPRESSION" where
"IntPE \<equiv> LitPE"

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
   = FSetType (TypeU TYPE('a))"
  by (simp add: WF_PEXPRESSION_type_def)

subsection {* Action Expressions *}

abbreviation EventPE ::
  "NAME \<Rightarrow> ('a, 'm :: EVENT_SORT) WF_PEXPRESSION 
        \<Rightarrow> ('a PEvent, 'm) WF_PEXPRESSION" where
"EventPE n v \<equiv> Op1PE (\<lambda> v. (n, v)) v"

subsection {* Renaming *}

definition RenamePE ::
  "('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow>
   'm VAR_RENAME \<Rightarrow>
   ('a, 'm) WF_PEXPRESSION" where
"RenamePE e ss = Abs_WF_PEXPRESSION (\<lbrakk>e\<rbrakk>\<^sub>* \<circ> (RenameB (inv\<^sub>s ss)))"

lemma EvalPE_RenamePE [evale]:
  "\<lbrakk>RenamePE e ss\<rbrakk>\<^sub>* = \<lbrakk>e\<rbrakk>\<^sub>* \<circ> (RenameB (inv\<^sub>s ss))"
  by (simp add:RenamePE_def)

definition Rep_VAR_RENAME_poly :: 
  "'m VAR_RENAME \<Rightarrow> ('a, 'm :: VALUE) PVAR \<Rightarrow> ('a, 'm) PVAR" where
"Rep_VAR_RENAME_poly ss x \<equiv> VAR_PVAR (Rep_VAR_RENAME ss (PVAR_VAR x))"

notation Rep_VAR_RENAME_poly ("\<langle>_\<rangle>\<^sub>s\<^sub>*")

lemma PVAR_VAR_vtype [simp]:
  "vtype (PVAR_VAR (x :: ('a, 'm :: VALUE) PVAR)) = TYPEU('a)"
  by (simp add:PVAR_VAR_def)

lemma PVAR_VAR_RENAME [simp]: 
  "PVAR_VAR (\<langle>ss\<rangle>\<^sub>s\<^sub>* x) = \<langle>ss\<rangle>\<^sub>s (PVAR_VAR x)"
  by (simp add:Rep_VAR_RENAME_poly_def)

lemma RenamePE_PVarPE [urename]:
  "RenamePE (VarPE x) ss = VarPE (\<langle>ss\<rangle>\<^sub>s x)"
  by (auto simp add:evale)

(*
lemma RenamePE_PVarPE [urename]:
  "RenamePE (PVarPE x) ss = PVarPE (\<langle>ss\<rangle>\<^sub>s\<^sub>* x)"
  apply (simp add:urename)
  by (auto simp add:evale)
*)

lemma RenamePE_LitPE [urename]:
  "RenamePE (LitPE v) ss = LitPE v"
  by (auto simp add:evale)

lemma RenamePE_Op1PE [urename]:
  "RenamePE (Op1PE f v) ss = Op1PE f (RenamePE v ss)"
  by (auto simp add:evale)

lemma RenamePE_Op2PE [urename]:
  "RenamePE (Op2PE f u v) ss = Op2PE f (RenamePE u ss) (RenamePE v ss)"
  by (auto simp add:evale)

lemma RenamePE_Op3PE [urename]:
  "RenamePE (Op3PE f u v w) ss = Op3PE f (RenamePE u ss) (RenamePE v ss) (RenamePE w ss)"
  by (auto simp add:evale)

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

lemma EvalPE_SubstPE [evale]:
  "\<lbrakk>SubstPE e v x\<rbrakk>\<^sub>*b = \<lbrakk>e\<rbrakk>\<^sub>* (b(x :=\<^sub>b InjU (\<lbrakk>v\<rbrakk>\<^sub>* b)))"
  by (simp add:SubstPE_def)

lemma SubstPE_VarPE [usubst]:
  fixes v :: "('a, 'm :: VALUE) WF_PEXPRESSION"
  assumes "v \<rhd>\<^sub>* x" "TYPEUSOUND('a, 'm)"
  shows "SubstPE (VarPE x) v x = v"
  using assms by (auto simp add:evale pevar_compat_def)

lemma PSubstPE_PVarPE [usubst]:
  fixes v :: "('a, 'm :: VALUE) WF_PEXPRESSION"
  assumes "TYPEUSOUND('a, 'm)"
  shows "PSubstPE (PVarPE x) v x = v"
  using assms by (simp add:usubst typing)

lemma SubstPE_LitPE [usubst]:
  "SubstPE (LitPE v) x e = LitPE v"
  by (auto simp add:evale)

lemma SubstPE_Op1PE [usubst]:
  "SubstPE (Op1PE f v) x e = Op1PE f (SubstPE v x e)"
  by (auto simp add:evale)

lemma SubstPE_Op2PE [usubst]:
  "SubstPE (Op2PE f u v) e x = Op2PE f (SubstPE u e x) (SubstPE v e x)"
  by (auto simp add:evale)

lemma SubstPE_Op3PE [usubst]:
  "SubstPE (Op3PE f u v w) e x= Op3PE f (SubstPE u e x) (SubstPE v e x) (SubstPE w e x)"
  by (auto simp add:evale)

subsection {* Parser *}

abbreviation "okay \<equiv> MkPVAR (bName ''okay'') True TYPE(bool) TYPE('m :: BOOL_SORT)"

lemma [closure]: "PVAR_VAR okay \<in> UNDASHED"
  apply (simp add:PVAR_VAR_def)
  apply (metis MkPlain_UNDASHED MkPlain_def)
done


nonterminal pexpr and pexprs

syntax
  "_pexprs"             :: "[pexpr, pexprs] => pexprs" ("_,/ _")
  ""                    :: "pexpr => pexprs" ("_")
  "_pexpr_brack"        :: "pexpr \<Rightarrow> pexpr" ("'(_')")
  "_expr_quote"         :: "pexpr \<Rightarrow> 'a WF_EXPRESSION" ("(1|_|)")
  "_pexpr_quote"        :: "pexpr \<Rightarrow> ('a, 'm) WF_PEXPRESSION" ("(1\<parallel>_\<parallel>)")
  "_pexpr_true"         :: "pexpr" ("true")
  "_pexpr_false"        :: "pexpr" ("false")
  "_pexpr_int"          :: "int \<Rightarrow> pexpr" ("_")
  "_pexpr_evar"         :: "('a, 'm) PVAR \<Rightarrow> pexpr" ("$_" [999] 999)
  "_pexpr_list"         :: "pexprs \<Rightarrow> pexpr" ("\<langle>_\<rangle>")
  "_pexpr_list_nil"     :: "pexpr" ("\<langle>\<rangle>")
  "_pexpr_list_append"  :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "^" 65)
  "_pexpr_fset"         :: "pexprs \<Rightarrow> pexpr" ("{_}")
  "_pexpr_fset_empty"   :: "pexpr" ("{}")
  "_pexpr_fset_union"   :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "\<union>" 65)
  "_pexpr_fset_inter"   :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "\<inter>" 70)

translations
  "_pexpr_brack e"             => "e"
  "_expr_quote e"              => "CONST PExprE e"
  "_pexpr_quote e"             => "e"
  "_pexpr_true"                == "CONST TruePE"
  "_pexpr_false"               == "CONST FalsePE"
  "_pexpr_int x"               == "CONST IntPE x"
  "_pexpr_evar x"              == "CONST PVarPE x"
  "_pexpr_list_nil"            == "CONST NilPE"
  "_pexpr_list_append e f"     == "CONST ConcatPE e f"
  "_pexpr_list (_pexprs x xs)" == "CONST ConsPE x (_pexpr_list xs)"
  "_pexpr_list x"              == "CONST ConsPE x (CONST NilPE)"
  "_pexpr_fset (_pexprs x xs)" == "CONST FInsertPE x (_pexpr_fset xs)"
  "_pexpr_fset x" == "CONST FInsertPE x CONST FEmptyPE"
  "_pexpr_fset_empty" == "CONST FEmptyPE"
  "_pexpr_fset_union xs ys" == "CONST FUnionPE xs ys"
  "_pexpr_fset_inter xs ys" == "CONST FInterPE xs ys"

class MY_SORT = LIST_SORT + INT_SORT + BOOL_SORT +
  assumes IntType_ListPerm [typing]: "IntType \<in> ListPerm"

abbreviation "tr \<equiv> MkPVAR (bName ''tr'') True TYPE(int list) TYPE('m :: MY_SORT)"

lemma "|\<langle>1,2\<rangle> ^ \<langle>3,4\<rangle> ^ $tr| = |\<langle>1,2,3,4\<rangle> ^ $tr|"
  by (simp add:evale typing)
 
term "|{1,3} \<union> {1,2}|"

end