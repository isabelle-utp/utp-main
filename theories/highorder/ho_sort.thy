(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: ho_sort.thy                                                          *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)
(* LAST REVIEWED: 25 April 2014 *)

header {* Higher-Order Sorts *}

theory ho_sort
imports "../utils/maxset"
  "../core/utp_model"
  "../core/utp_sorts_new"
  "../core/utp_var"
 "../alphapred/utp_pred"
begin

default_sort type

subsection {* Theorem Attribute *}

ML {*
  structure ranks = Named_Thms
    (val name = @{binding ranks} val description = "rank theorems")
*}

setup ranks.setup

subsection {* Pre-HO Model *}

class PRE_HO_MODEL = TYPED_MODEL +
-- {* Maximum rank of values admitted by the model. *}
  fixes MaxRank :: "'a::TYPED_MODEL itself \<Rightarrow> nat"
-- {* Rank of a UTP type. *}
  fixes RankType :: "'a utype \<Rightarrow> nat"
begin

subsubsection {* Value Tests *}

definition IsBaseType :: "'a utype \<Rightarrow> bool" where
"IsBaseType t \<longleftrightarrow> RankType t = 0"

definition IsProgType :: "'a utype \<Rightarrow> bool" where
"IsProgType t \<longleftrightarrow> RankType t \<noteq> 0"

declare IsBaseType_def [ranks]
declare IsProgType_def [ranks]

paragraph {* Theorems *}

theorem not_IsBaseType_iff [simp] :
"\<not> IsBaseType t \<longleftrightarrow> IsProgType t"
apply (unfold IsBaseType_def IsProgType_def)
apply (simp)
done

theorem not_IsProgType_iff [simp] :
"\<not> IsProgType t \<longleftrightarrow> IsBaseType t"
apply (unfold IsBaseType_def IsProgType_def)
apply (simp)
done

subsubsection {* Type Tests *}

definition IsBaseVal :: "'a uval \<Rightarrow> bool" where
"IsBaseVal v \<longleftrightarrow> (\<exists> t . v : t \<and> IsBaseType t)"

definition IsProgVal :: "'a uval \<Rightarrow> bool" where
"IsProgVal v \<longleftrightarrow> (\<exists> t . v : t \<and> IsProgType t)"

abbreviation IsBaseVar :: "'a uvar \<Rightarrow> bool" where
"IsBaseVar x \<equiv> IsBaseType (type x)"

abbreviation IsProgVar :: "'a uvar \<Rightarrow> bool" where
"IsProgVar x \<equiv> IsProgType (type x)"

text {* Should the following two be safe introduction rules? *}

theorem IsBaseValI [simp, intro] :
"v : t \<Longrightarrow> IsBaseType t \<Longrightarrow> IsBaseVal v"
apply (simp add: IsBaseVal_def)
apply (rule_tac x = "t" in exI)
apply (simp)
done

theorem IsProgValI [simp, intro] :
"v : t \<Longrightarrow> IsProgType t \<Longrightarrow> IsProgVal v"
apply (simp add: IsProgVal_def)
apply (rule_tac x = "t" in exI)
apply (simp)
done

subsubsection {* Restrictions *}

definition RANK :: "nat \<Rightarrow> 'a utype set" where
"RANK n = {t . RankType t \<le> n}"

theorem RANK_member [iff] :
"t \<in> RANK n \<longleftrightarrow> RankType t \<le> n"
apply (unfold RANK_def)
apply (simp)
done

subsubsection {* Derived Ranks *}

definition RankVal :: "'a uval \<Rightarrow> nat" where
"RankVal x = MaxSet {RankType t | t . x : t}"

definition RankVar :: "'a uvar \<Rightarrow> nat" where
"RankVar v = RankType (type v)"

definition RankAlpha :: "'a uvar fset \<Rightarrow> nat" where
"RankAlpha a = MaxSet (RankVar ` \<sim>a)"

definition RankP :: "'a PRED \<Rightarrow> nat" where
"RankP p = RankAlpha (\<alpha> p)"

declare RankVal_def [ranks]
declare RankVar_def [ranks]
declare RankAlpha_def [ranks]
declare RankP_def [ranks]

subsubsection {* Bounded Values *}

definition bounded_value :: "'a uval \<Rightarrow> bool" ("\<B>") where
"\<B> v \<longleftrightarrow> RankVal v \<le> MaxRank TYPE('a)"

declare bounded_value_def [ranks]

theorem bounded_valueI [simp, intro] :
"RankVal v \<le> MaxRank TYPE('a) \<Longrightarrow> \<B> v"
apply (simp add: bounded_value_def RankVal_def)
done

theorem bounded_valueD [simp, intro] :
"\<B> v \<Longrightarrow> RankVal v \<le> MaxRank TYPE('a)"
apply (simp add: bounded_value_def RankVal_def)
done

subsubsection {* Bounded Types *}

text {* Not yet sure we need this notion. Maybe subsequently remove. *}

definition bounded_type :: "'a utype \<Rightarrow> bool" ("\<B>\<^sub>t") where
"\<B>\<^sub>t t \<longleftrightarrow> RankType t \<le> MaxRank TYPE('a)"

theorem bounded_typeI [simp, intro] :
"RankType t \<le> MaxRank TYPE('a) \<Longrightarrow> \<B>\<^sub>t t"
apply (simp add: bounded_type_def RankVal_def)
done

theorem bounded_typeD [simp, intro] :
"\<B>\<^sub>t t \<Longrightarrow> RankType t \<le> MaxRank TYPE('a)"
apply (simp add: bounded_type_def RankVal_def)
done

declare bounded_type_def [ranks]
end

subsection {* HO Model *}

class HO_MODEL = PRE_HO_MODEL +
  assumes BaseType_exists :
    "\<exists> t . IsBaseType t"
  assumes BaseVal_non_empty [dest] :
    "IsBaseType t \<Longrightarrow> \<exists> v . IsBaseVal v \<and> v : t \<and> \<D> v"
  assumes ProgType_monotype [simp] :
    "IsProgType t1 \<Longrightarrow> v : t1 \<Longrightarrow> v : t2 \<Longrightarrow> t1 = t2"
begin

subsection {* Theorems *}

theorem BaseVal_exists :
"\<exists> v . IsBaseVal v"
apply (metis BaseType_exists BaseVal_non_empty)
done

theorem defined_BaseVal_exists :
"\<exists> v . IsBaseVal v \<and> \<D> v"
apply (metis BaseType_exists BaseVal_non_empty)
done

theorem not_IsBaseVal_iff [simp] :
"\<D> v \<Longrightarrow> \<not> IsBaseVal v \<longleftrightarrow> IsProgVal v"
apply (unfold IsBaseVal_def IsProgVal_def)
apply (simp)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "utype_of v" in exI)
apply (simp add: defined)
-- {* Subgoal 2 *}
apply (rename_tac t1 t2)
apply (metis ProgType_monotype)
done

theorem not_IsProgVal_iff [simp] :
"\<D> v \<Longrightarrow> \<not> IsProgVal v \<longleftrightarrow> IsBaseVal v"
apply (unfold IsBaseVal_def IsProgVal_def)
apply (simp)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "utype_of v" in exI)
apply (simp add: defined)
-- {* Subgoal 2 *}
apply (rename_tac t1 t2)
apply (fold not_IsProgType_iff)
apply (erule_tac Q = "IsProgType t1" in contrapos_nn)
apply (metis ProgType_monotype)
done
end

(***********************)
(* REVIEWED UNTIL HERE *)
(***********************)

subsection {* HO Value Sort *}

class HO_SORT =
  fixes MkProg :: "'a::HO_MODEL PRED \<Rightarrow> 'a VALUE" ("\<lbrace>_\<rbrace>")
  fixes DestProg :: "'a VALUE \<Rightarrow> 'a PRED"
  fixes ProgType :: "'a VAR fset \<Rightarrow> 'a UTYPE"
  fixes DestProgType :: "'a UTYPE \<Rightarrow> 'a VAR fset" ("\<alpha>\<^sub>p\<^sub>t")
  assumes IsProgVal_defined [defined] : "IsProgVal v \<Longrightarrow> \<D> v"
  assumes MkProg_typed [typing] : "\<lbrace>p\<rbrace> : ProgType (\<alpha> p)"
  assumes MkProg_inverse [simp] : "\<B> \<lbrace>p\<rbrace> \<Longrightarrow> DestProg \<lbrace>p\<rbrace> = p"
  assumes DestProg_inverse [simp] : "IsProgVal v \<Longrightarrow> \<B> v \<Longrightarrow> \<lbrace>DestProg v\<rbrace> = v"
  assumes ProgType_rank [ranks] : "RankType (ProgType a) = (RankAlpha a) + 1"
  assumes ProgType_inverse [simp] : "\<alpha>\<^sub>p\<^sub>t (ProgType a) = a"
  assumes DestProgType_inverse [simp] : "IsProgType t \<Longrightarrow> ProgType (\<alpha>\<^sub>p\<^sub>t t) = t"
begin

subsubsection {* Typing Theorems *}

theorem DestProgType_inject [typing] :
"IsProgType t1 \<Longrightarrow> IsProgType t2 \<Longrightarrow> t1 = t2 \<longleftrightarrow> \<alpha>\<^sub>p\<^sub>t t1 = \<alpha>\<^sub>p\<^sub>t t2"
apply (metis DestProgType_inverse)
done

theorem MkProg_typedI [typing] :
"(\<alpha> p) = a \<Longrightarrow> \<lbrace>p\<rbrace> : (ProgType a)"
apply (metis MkProg_typed)
done

theorem IsProgType_ProgType [typing] :
"IsProgType (ProgType a)"
apply (unfold IsProgType_def)
apply (unfold ProgType_rank)
apply (simp)
done

theorem IsProgType_iff :
"IsProgType t \<longleftrightarrow> (\<exists> p . \<lbrace>p\<rbrace> : t)"
apply (rule iffI)
-- {* Subgoal 1 *}
apply (subgoal_tac "\<exists> a . t = ProgType a")
-- {* Subgoal 1.1 *}
apply (clarify)
apply (rule_tac x = "False\<^sub>p a" in exI)
apply (rule MkProg_typedI)
apply (simp add: alphabet)
-- {* Subgoal 1.2 *}
apply (rule_tac x = "\<alpha>\<^sub>p\<^sub>t t" in exI)
apply (simp)
-- {* Subgoal 2 *}
apply (clarify)
apply (metis IsProgType_ProgType MkProg_typed ProgType_monotype)
done

theorem IsProgTypeI [typing] :
"\<lbrace>p\<rbrace> : t \<Longrightarrow> IsProgType t"
apply (unfold IsProgType_iff)
apply (rule_tac x = "p" in exI)
apply (assumption)
done

theorem IsProgTypeD [elim] :
"IsProgType t \<Longrightarrow> (\<And> a . t = ProgType a \<Longrightarrow> P) \<Longrightarrow> P"
apply (drule_tac x = "\<alpha>\<^sub>p\<^sub>t t" in meta_spec)
apply (simp)
done

subsubsection {* Program Values *}

theorem IsProgVal_MkProg [simp] :
"IsProgVal \<lbrace>p\<rbrace>"
apply (unfold IsProgVal_def)
apply (rule_tac x = "ProgType (\<alpha> p)" in exI)
apply (simp add: typing)
done

theorem IsProgVal_iff :
"IsProgVal v \<longleftrightarrow> (\<exists> a . v : ProgType a)"
apply (unfold IsProgVal_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "\<alpha>\<^sub>p\<^sub>t t" in exI)
apply (simp)
-- {* Subgoal 2 *}
apply (rule_tac x = "ProgType a" in exI)
apply (simp add: typing)
done

theorem IsProgValI [simp] :
"v : ProgType a \<Longrightarrow> IsProgVal v"
apply (unfold IsProgVal_iff)
apply (rule_tac x = "a" in exI)
apply (assumption)
done

theorem IsProgValD [elim] :
fixes v :: "'a VALUE"
shows "IsProgVal v \<Longrightarrow> \<B> v \<Longrightarrow> (\<And> p . v = \<lbrace>p\<rbrace> \<Longrightarrow> P) \<Longrightarrow> P"
apply (drule_tac x = "DestProg v" in meta_spec)
apply (simp)
done

subsubsection {* Alphabet Theorems *}

text {* Not sure yet whether to make the following an alphabet theorem. *}

theorem DestProgType_alphabet [alphabet] :
"\<lbrace>p\<rbrace> : t \<Longrightarrow> (\<alpha> p) = (\<alpha>\<^sub>p\<^sub>t t)"
apply (insert MkProg_typed [of p])
apply (subgoal_tac "t = ProgType (\<alpha> p)")
apply (erule ssubst)
apply (simp)
apply (metis IsProgTypeI ProgType_monotype)
done

subsubsection {* Rank Theorems *}

lemma Setcompr_remove :
"{f x |x. P x} = f ` {x . P x}"
apply (auto)
done

lemma Collect_types_MkType [simp] :
"{t. \<lbrace>p\<rbrace> : t} = {ProgType (\<alpha> p)}"
apply (safe)
apply (simp_all add: typing)
done

theorem RankVal_MkProg [ranks] :
"(* \<D> \<lbrace>p\<rbrace> \<Longrightarrow> *) RankVal \<lbrace>p\<rbrace> = (RankP p) + 1"
apply (unfold RankVal_def)
apply (simp add: Setcompr_remove)
apply (simp add: ranks)
done
end

subsection {* Fixed-bound HO Sorts *}

class HO_SORT0 = HO_SORT +
  assumes MaxRank_zero [simp] :
    "MaxRank TYPE('a::HO_MODEL) = 0"

class HO_SORT1 = HO_SORT +
  assumes MaxRank_zero [simp] :
    "MaxRank TYPE('a::HO_MODEL) = 1"

class HO_SORT2 = HO_SORT +
  assumes MaxRank_zero [simp] :
    "MaxRank TYPE('a::HO_MODEL) = 2"

class HO_SORT3 = HO_SORT +
  assumes MaxRank_zero [simp] :
    "MaxRank TYPE('a::HO_MODEL) = 3"

class HO_SORT4 = HO_SORT +
  assumes MaxRank_zero [simp] :
    "MaxRank TYPE('a::HO_MODEL) = 4"

subsection {* Augmented Value Sorts *}

text {* Augmentation of the value sorts is still somewhat an open issue. *}

class HO_INT_SORT = INT_SORT +
  assumes IsBaseType_IntType [simp] :
    "IsBaseType (IntType :: 'a::{INT_SORT,HO_MODEL} UTYPE)"

class HO_BOOL_SORT = BOOL_SORT +
  assumes IsBaseType_BoolType [simp] :
    "IsBaseType (BoolType :: 'a::{BOOL_SORT,HO_MODEL} UTYPE)"

class HO_STR_SORT = STR_SORT +
  assumes IsBaseType_StrType [simp] :
    "IsBaseType (StrType :: 'a::{STR_SORT,HO_MODEL} UTYPE)"

class HO_REAL_SORT = REAL_SORT +
  assumes IsBaseType_RealType [simp] :
    "IsBaseType (RealType :: 'a::{REAL_SORT,HO_MODEL} UTYPE)"

text {* Do we need the @{term "IsBaseType t"} terms in the antecedents? *}

class HO_PAIR_SORT = PAIR_SORT +
  assumes IsBaseType_PairType [simp] :
    "IsBaseType t1 \<Longrightarrow>
     IsBaseType t2 \<Longrightarrow>
     IsBaseType ((PairType t1 t2) :: 'a::{PAIR_SORT,HO_MODEL} UTYPE)"

class HO_PAIR_SET = PAIR_SORT +
  assumes IsBaseType_SetType [simp] :
    "IsBaseType t \<Longrightarrow>
     IsBaseType ((SetType t) :: 'a::{SET_SORT,HO_MODEL} UTYPE)"

class HO_PAIR_LIST = LIST_SORT +
  assumes IsBaseType_ListType [simp] :
    "IsBaseType t \<Longrightarrow>
     IsBaseType ((ListType t) :: 'a::{LIST_SORT,HO_MODEL} UTYPE)"
end
