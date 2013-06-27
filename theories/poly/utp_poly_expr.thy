(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_shallow_expr.thy                                                 *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Shallowly Embedded Polymorphic Expressions *}

theory utp_poly_expr
imports 
(*
  "../core/utp_expr"
  "../tactics/utp_expr_tac"
*)
  utp_poly_value
  utp_poly_var
begin

text {* Theorem Attribute *}

ML {*
  structure evale =
    Named_Thms (val name = @{binding evale} val description = "evale theorems")
*}

setup evale.setup

ML {*
  structure unrest =
    Named_Thms (val name = @{binding unrest} val description = "unrest theorems")
*}

setup unrest.setup

default_sort type

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

definition UNREST_PEXPR :: "('m VAR) set \<Rightarrow> ('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> bool" where
"UNREST_PEXPR vs e \<equiv> (\<forall> b1 b2. \<lbrakk>e\<rbrakk>\<^sub>*(b1 \<oplus>\<^sub>b b2 on vs) = \<lbrakk>e\<rbrakk>\<^sub>* b1)" 

definition LitPE :: "'a \<Rightarrow> ('a, 'm :: VALUE) WF_PEXPRESSION" where
"LitPE v = Abs_WF_PEXPRESSION (\<lambda> b. v)"

lemma EvalPE_LitPE [evale]:
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

definition VarPE :: "'m VAR \<Rightarrow> ('a, 'm :: VALUE) WF_PEXPRESSION" where
"VarPE x = Abs_WF_PEXPRESSION (\<lambda> b. ProjU (\<langle>b\<rangle>\<^sub>b x))"

lemma EvalPE_VarPE [evale]:
  "\<lbrakk>VarPE x\<rbrakk>\<^sub>*b = ProjU (\<langle>b\<rangle>\<^sub>b x)"
  by (simp add:VarPE_def)

lemma UNREST_VarPE [unrest]:
  "x \<notin> vs \<Longrightarrow> UNREST_PEXPR vs (VarPE x)"
  by (simp add:VarPE_def UNREST_PEXPR_def)

abbreviation PVarPE :: "('a, 'm :: VALUE) PVAR \<Rightarrow> ('a, 'm) WF_PEXPRESSION" where
"PVarPE x \<equiv> VarPE [x]\<^sub>*"

lemma EvalPE_PVarPE [evale]:
  "\<lbrakk>PVarPE x\<rbrakk>\<^sub>*b = ProjU (\<langle>b\<rangle>\<^sub>b (PVAR_VAR x))"
  by (simp add:VarPE_def)

definition Op1PE :: 
  "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> ('b, 'm) WF_PEXPRESSION" where
"Op1PE f u = Abs_WF_PEXPRESSION (\<lambda> b. f (\<lbrakk>u\<rbrakk>\<^sub>*b))"

lemma EvalPE_Op1PE [evale]:
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

lemma EvalPE_Op2PE [evale]:
  "\<lbrakk>Op2PE f u v\<rbrakk>\<^sub>*b = f (\<lbrakk>u\<rbrakk>\<^sub>*b) (\<lbrakk>v\<rbrakk>\<^sub>*b)"
  by (simp add:Op2PE_def)

definition 
  Op3PE :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 
            ('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 
            ('b, 'm) WF_PEXPRESSION \<Rightarrow> 
            ('c, 'm) WF_PEXPRESSION \<Rightarrow>
            ('d, 'm) WF_PEXPRESSION" where
"Op3PE f u v w = Abs_WF_PEXPRESSION (\<lambda> b. f (\<lbrakk>u\<rbrakk>\<^sub>*b) (\<lbrakk>v\<rbrakk>\<^sub>*b) (\<lbrakk>w\<rbrakk>\<^sub>*b))"

lemma EvalPE_Op3PE [evale]:
  "\<lbrakk>Op3PE f u v w\<rbrakk>\<^sub>*b = f (\<lbrakk>u\<rbrakk>\<^sub>*b) (\<lbrakk>v\<rbrakk>\<^sub>*b) (\<lbrakk>w\<rbrakk>\<^sub>*b)"
  by (simp add:Op3PE_def)

abbreviation "EqualPE \<equiv> Op2PE (op =)"

(*
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

definition PExprP :: 
  "(bool, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow> 'm WF_PREDICATE" where
"PExprP e = mkPRED {b. \<lbrakk>e\<rbrakk>\<^sub>* b}"
*)

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

definition PEV :: "NAME \<Rightarrow> 'a \<Rightarrow> ('m :: EVENT_SORT) EVENT" where
"PEV n v = EV n TYPEU('a) (InjU v)"

abbreviation EventPE ::
  "NAME \<Rightarrow> ('a, 'm :: EVENT_SORT) WF_PEXPRESSION 
        \<Rightarrow> ('m EVENT, 'm) WF_PEXPRESSION" where
"EventPE n v \<equiv> Op1PE (PEV n) v"

subsection {* Renaming *}

definition RenamePE ::
  "('a, 'm :: VALUE) WF_PEXPRESSION \<Rightarrow>
   'm VAR_RENAME \<Rightarrow>
   ('a, 'm) WF_PEXPRESSION" where
"RenamePE e ss = Abs_WF_PEXPRESSION (\<lbrakk>e\<rbrakk>\<^sub>* \<circ> (RenameB (inv\<^sub>s ss)))"

lemma EvalPE_RenamePE [evale]:
  "\<lbrakk>RenamePE e ss\<rbrakk>\<^sub>* = \<lbrakk>e\<rbrakk>\<^sub>* \<circ> (RenameB (inv\<^sub>s ss))"
  by (simp add:RenamePE_def)

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
(*  "_expr_quote"         :: "pexpr \<Rightarrow> 'a WF_EXPRESSION" ("(1|_|)") *)
  "_pexpr_quote"        :: "pexpr \<Rightarrow> ('a, 'm) WF_PEXPRESSION" ("(1\<parallel>_\<parallel>)")
  "_pexpr_equal"        :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "=" 50)
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
  "_pexpr_event"        :: "NAME \<Rightarrow> pexpr \<Rightarrow> pexpr" ("_?_" 50)

translations
  "_pexpr_brack e"             => "e"
(*  "_expr_quote e"              => "CONST PExprE e" *)
  "_pexpr_quote e"             => "e"
  "_pexpr_equal e f"           == "CONST EqualPE e f"
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
  "_pexpr_event n v" == "CONST EventPE n v"

lemma "\<parallel>6 = 7\<parallel> = \<parallel>false\<parallel>"
  by (auto simp add:evale)

term "\<parallel>\<langle>n?5, m?{1}\<rangle> ^ \<langle>\<rangle>\<parallel>"

class MY_SORT = LIST_SORT + INT_SORT + BOOL_SORT +
  assumes IntType_ListPerm [typing]: "IntType \<in> ListPerm"

abbreviation "tr \<equiv> MkPVAR (bName ''tr'') True TYPE(int list) TYPE('m :: MY_SORT)"

lemma "\<parallel>\<langle>1,2\<rangle> ^ \<langle>3,4\<rangle> ^ $tr\<parallel> = \<parallel>\<langle>1,2,3,4\<rangle> ^ $tr\<parallel>"
  by (auto simp add:evale typing)
 
term "\<parallel>{1,3} \<union> {1,2}\<parallel>"

end