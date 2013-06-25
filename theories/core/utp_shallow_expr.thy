(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_shallow_expr.thy                                                 *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Shallow Expressions *}

theory utp_shallow_expr
imports 
  utp_expr
  "../tactics/utp_expr_tac"
  utp_event
begin

default_sort type

consts 
  TypeU :: "'a itself \<Rightarrow> ('m :: VALUE) UTYPE"
  InjU  :: "'a \<Rightarrow> 'm :: VALUE"
  ProjU :: "'m :: VALUE \<Rightarrow> 'a"

type_synonym 'a PEvent = "(NAME * 'a)"

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
        the properties of the above polymorphic constants *}

definition TypeUSound :: "'a itself \<Rightarrow> 'm::VALUE itself \<Rightarrow> bool" where
"TypeUSound a m = (\<forall> (x :: 'a). (InjU x :: 'm) :! TypeU a)"

lemma TypeUSound_bool [typing]: "TypeUSound TYPE(bool) TYPE('m :: BOOL_SORT)"
  by (simp add:TypeUSound_def typing)

lemma TypeUSound_int [typing]: "TypeUSound TYPE(int) TYPE('m :: INT_SORT)"
  by (simp add:TypeUSound_def typing)

lemma TypeUSound_list [typing]: 
  "\<lbrakk> (TypeU TYPE('a) :: 'm UTYPE) \<in> ListPerm; TypeUSound TYPE('a) TYPE('m :: LIST_SORT) \<rbrakk> 
     \<Longrightarrow> TypeUSound TYPE('a list) TYPE('m)"
  by (force intro:typing simp add:dcarrier_def TypeUSound_def)

lemma TypeUSound_fset [typing]: 
  "\<lbrakk> (TypeU TYPE('a) :: 'm UTYPE) \<in> FSetPerm; TypeUSound TYPE('a) TYPE('m :: FSET_SORT) \<rbrakk> 
     \<Longrightarrow> TypeUSound TYPE('a fset) TYPE('m)"
  by (force intro:typing simp add:dcarrier_def TypeUSound_def)

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

definition "LitPE v = Abs_WF_PEXPRESSION (\<lambda> b. v)"

lemma EvalPE_LitPE [evale]:
  "\<lbrakk>LitPE v\<rbrakk>\<^sub>*b = v"
  by (simp add:LitPE_def)

record ('a, 'm :: VALUE) PVAR = 
  pvname  :: NAME
  pvaux   :: bool
  pvtype  :: "'a itself"
  pvmodel :: "'m itself"

definition "myvar \<equiv> \<lparr> pvname = bName ''myvar'', pvaux = True, pvtype = TYPE(bool), pvmodel = TYPE('a :: BOOL_SORT) \<rparr>"

definition PVAR_VAR :: "('a, 'm) PVAR \<Rightarrow> ('m :: VALUE) VAR" where
"PVAR_VAR v = MkVar (pvname v) (TypeU TYPE('a)) (pvaux v)"

definition "VarPE x = Abs_WF_PEXPRESSION (\<lambda> b. ProjU (\<langle>b\<rangle>\<^sub>b x))"

abbreviation PVarPE :: "('a, 'm :: VALUE) PVAR \<Rightarrow> ('a, 'm) WF_PEXPRESSION" where
"PVarPE x \<equiv> VarPE (PVAR_VAR x)"

lemma EvalPE_VarPE [evale]:
  "\<lbrakk>VarPE x\<rbrakk>\<^sub>*b = ProjU (\<langle>b\<rangle>\<^sub>b x)"
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
  shows "PExprE e :\<^sub>e \<tau>\<^sub>* e"
  apply (simp add: etype_rel_def PExprE_rep_eq assms WF_PEXPRESSION_type_def)
  apply (metis TypeUSound_def assms dtype_type)
done

definition SubstPE :: 
"('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 
 ('b, 'm) WF_PEXPRESSION \<Rightarrow> 
 'm VAR \<Rightarrow> 
 ('a, 'm) WF_PEXPRESSION" where
"SubstPE f v x = Abs_WF_PEXPRESSION (\<lambda> b. \<lbrakk>f\<rbrakk>\<^sub>* (b(x :=\<^sub>b InjU (\<lbrakk>v\<rbrakk>\<^sub>* b))))"

lemma EvalPE_SubstPE [evale]:
  "\<lbrakk>SubstPE e v x\<rbrakk>\<^sub>*b = \<lbrakk>e\<rbrakk>\<^sub>* (b(x :=\<^sub>b InjU (\<lbrakk>v\<rbrakk>\<^sub>* b)))"
  by (simp add:SubstPE_def)

abbreviation PSubstPE :: 
"('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 
 ('b, 'm) WF_PEXPRESSION \<Rightarrow> 
 ('b, 'm) PVAR \<Rightarrow> 
 ('a, 'm) WF_PEXPRESSION" where
"PSubstPE f v x \<equiv> SubstPE f v (PVAR_VAR x)"

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

end