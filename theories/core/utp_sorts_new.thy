(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utp_sorts_new.thy                                                    *)
(* Authors: Simon Foster & Frank Zeyda, University of York (UK)               *)
(******************************************************************************)
(* LAST REVIEWED: 17 July 2014 *)

theory utp_sorts_new
imports utp_model
begin

default_sort type

subsubsection {* Utility Locales *}

subsubsection {* Locale for Basic Sorts *}

locale UTP_BASIC_SORT =
  fixes MkVal :: "'a \<Rightarrow> 'm::TYPED_MODEL uval"
  fixes DestVal :: "'m uval \<Rightarrow> 'a"
  fixes Domain :: "'a set"
  fixes Type :: "'m utype"
  assumes MkVal_defined : "\<D>\<^sub>v (MkVal x) \<longleftrightarrow> (x \<in> Domain)"
  assumes MkVal_typed : "x \<in> Domain \<Longrightarrow> (MkVal x) : Type"
  assumes MkVal_inverse : "x \<in> Domain \<Longrightarrow> DestVal (MkVal x) = x"
  assumes DestVal_inverse : "v :! Type \<Longrightarrow> MkVal (DestVal v) = v"
  assumes Domain_non_empty : "Domain \<noteq> {}"
begin

subsubsection {* Operators *}

definition IsVal :: "'m uval \<Rightarrow> bool" where
"IsVal v \<longleftrightarrow> (v : Type)"

subsubsection {* Theorems *}

theorem dcarrier_Type :
"(dcarrier Type) = MkVal ` Domain"
apply (rule Set.set_eqI)
apply (simp add: image_def)
apply (safe)
apply (simp_all)
-- {* Subgoal 1 *}
apply (metis DestVal_inverse MkVal_defined strict_type_rel_def)
-- {* Subgoal 2 *}
apply (metis MkVal_typed)
-- {* Subgoal 3 *}
apply (metis MkVal_defined)
done

theorem DestVal_dcarrier_image :
"DestVal ` (dcarrier Type) = Domain"
apply (simp add: image_def)
apply (simp add: dcarrier_def)
apply (safe)
apply (simp_all)
-- {* Subgoal 1 *}
apply (metis DestVal_inverse MkVal_defined strict_type_rel_def)
-- {* Subgoal 2 *}
apply (metis MkVal_defined MkVal_inverse MkVal_typed)
done

theorem in_image_MkVal :
"v :! Type \<Longrightarrow> v \<in> (MkVal ` Domain)"
apply (fold dcarrier_Type)
apply (simp add: dcarrier_def)
done

theorem MkVal_inj_on :
"inj_on MkVal Domain"
apply (rule inj_onI)
apply (metis MkVal_inverse)
done

theorem DestVal_inj_on :
"inj_on DestVal (dcarrier Type)"
apply (rule inj_onI)
apply (unfold dcarrier_member)
apply (metis DestVal_inverse)
done
end

subsubsection {* Locale for Paramatric Sorts *}

locale UTP_PARAM_SORT =
  fixes MkVal :: "'m::TYPED_MODEL utype \<Rightarrow> ('a \<Rightarrow> 'm uval)"
  fixes DestVal :: "'m uval \<Rightarrow> 'a"
  fixes Domain :: "'m utype \<Rightarrow>'a set"
  fixes MkType :: "'m utype \<Rightarrow> 'm utype"
  assumes MkVal_defined : "\<D>\<^sub>v (MkVal t x) \<longleftrightarrow> x \<in> Domain t"
  assumes MkVal_typed : "x \<in> Domain t \<Longrightarrow> (MkVal t x) : (MkType t)"
  assumes MkVal_inverse : "x \<in> Domain t \<Longrightarrow> DestVal (MkVal t x) = x"
  assumes DestVal_inverse : "v :! (MkType t) \<Longrightarrow> MkVal t (DestVal v) = v"
  assumes Domain_non_empty : "Domain t \<noteq> {}"
  assumes MkType_inj : "inj MkType"
begin

subsubsection {* Derived Operators *}

definition IsType :: "'m utype \<Rightarrow> bool" where
"IsType t = (\<exists> t' . t = MkType t')"

definition DestType :: "'m utype \<Rightarrow> 'm utype" where
"DestType t = (THE t' . t = MkType t')"

subsubsection {* Theorems *}

theorem MkVal_definedI :
"x \<in> Domain t \<Longrightarrow> \<D>\<^sub>v (MkVal t x)"
apply (metis MkVal_defined)
done

theorem MkVal_strictly_typed :
"x \<in> Domain t \<Longrightarrow> (MkVal t x) :! (MkType t)"
apply (unfold strict_type_rel_def)
apply (rule conjI)
apply (metis MkVal_typed)
apply (metis MkVal_defined)
done

theorem MkVal_witness :
"x :! MkType t \<Longrightarrow> \<exists> y . y \<in> Domain t \<and> x = MkVal t y"
apply (metis DestVal_inverse MkVal_defined strict_type_rel_def)
done

theorem MkVal_unique_witness :
"x :! MkType t \<Longrightarrow> \<exists>! y . y \<in> Domain t \<and> x = MkVal t y"
apply (safe)
apply (metis MkVal_witness strict_type_rel_def)
apply (rename_tac x y)
apply (metis MkVal_inverse)
done

theorem IsType_MkType :
"IsType (MkType t)"
apply (unfold IsType_def)
apply (auto)
done

theorem IsType_elim :
"IsType t \<Longrightarrow> (\<And> t' . t = MkType t' \<Longrightarrow> P) \<Longrightarrow> P"
apply (unfold IsType_def)
apply (auto)
done

theorem MkType_elim :
"x :! MkType t \<Longrightarrow> (\<And> y . \<lbrakk>x = MkVal t y; y \<in> Domain t\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
apply (metis MkVal_witness)
done

theorem MkType_inverse :
"DestType (MkType t) = t"
apply (unfold DestType_def)
apply (rule the_equality)
apply (clarify)
apply (metis MkType_inj injD)
done

theorem DestType_inverse :
"IsType t \<Longrightarrow> MkType (DestType t) = t"
apply (unfold IsType_def)
apply (metis MkType_inverse)
done
end

subsection {* Bottom Value Sort *}

class BOT_SORT = PRE_TYPED_MODEL +
  fixes ubot :: "'a utype \<Rightarrow> 'a uval" ("\<bottom>\<^bsub>_\<^esub>")
  assumes ubot_undefined [defined] : "\<D>\<^sub>v (\<bottom>\<^bsub>t\<^esub>) = False"
  and ubot_typed [typing] : "\<bottom>\<^bsub>t\<^esub> : t"

subsubsection {* Theorems *}

theorem Defined_not_eq_bot [simp] :
"\<D>\<^sub>v x \<Longrightarrow> x \<noteq> \<bottom>\<^bsub>t\<^esub>"
apply (metis ubot_undefined)
done

subsection {* Boolean Sort *}

class BOOL_SORT =
  fixes MkBool :: "bool \<Rightarrow> 'a::TYPED_MODEL uval"
  fixes DestBool :: "'a uval \<Rightarrow> bool"
  fixes BoolType :: "'a utype"
  assumes INSTANCE : "UTP_BASIC_SORT MkBool DestBool UNIV BoolType"
begin

subsubsection {* Locale Imports *}

abbreviation IsBool :: "'a uval \<Rightarrow> bool" where
"IsBool \<equiv> UTP_BASIC_SORT.IsVal BoolType"

theorems
  IsBool_def [simp] = UTP_BASIC_SORT.IsVal_def [OF INSTANCE]

theorems
  MkBool_defined [defined] = UTP_BASIC_SORT.MkVal_defined [OF INSTANCE] and
  MkBool_typed [simplified, typing] = UTP_BASIC_SORT.MkVal_typed [OF INSTANCE] and
  MkBool_inverse [simplified, simp] = UTP_BASIC_SORT.MkVal_inverse [OF INSTANCE] and
  DestBool_inverse [simp] = UTP_BASIC_SORT.DestVal_inverse [OF INSTANCE] and
  MkBool_inj_on [simp] = UTP_BASIC_SORT.MkVal_inj_on [OF INSTANCE] and
  DestBool_inj_on [simp] = UTP_BASIC_SORT.DestVal_inj_on [OF INSTANCE]

theorems
  dcarrier_BoolType = UTP_BASIC_SORT.dcarrier_Type [OF INSTANCE] and
  DestBool_dcarrier_image = UTP_BASIC_SORT.DestVal_dcarrier_image [OF INSTANCE] and
  in_image_BoolVal = UTP_BASIC_SORT.in_image_MkVal [OF INSTANCE]

subsubsection {* Boolean Values *}

definition BOOL_VALUE :: "'a uval set" where
"BOOL_VALUE = dcarrier BoolType"

subsubsection {* Constants *}

definition TrueV :: "'a uval" ("True\<^sub>v")where
"TrueV = MkBool True"

definition FalseV :: "'a uval" ("False\<^sub>v") where
"FalseV = MkBool False"

subsubsection {* Operators *}

definition NegV :: "'a uval \<Rightarrow> 'a uval" where
"NegV v = MkBool(\<not> DestBool(v))"
notation NegV ("\<not>\<^sub>v _" [40] 40)

definition AndV :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"AndV v1 v2 = MkBool(DestBool(v1) \<and> DestBool(v2))"
notation AndV (infixr "\<and>\<^sub>v" 35)

definition OrV :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"OrV v1 v2 = MkBool(DestBool(v1) \<or> DestBool(v2))"
notation OrV (infixr "\<or>\<^sub>v" 30)

definition ImpV :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"ImpV v1 v2 = MkBool(DestBool(v1) \<longrightarrow> DestBool(v2))"
notation ImpV (infixr "\<Rightarrow>\<^sub>v" 25)

definition IffV :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"IffV v1 v2 = MkBool(DestBool(v1) \<longleftrightarrow> DestBool(v2))"
notation IffV (infixr "\<Leftrightarrow>\<^sub>v" 25)

subsubsection {* Proof Support *}

theorem MkBool_eqI [intro] :
"x = y \<Longrightarrow> MkBool x = MkBool y"
apply (erule arg_cong)
done

paragraph {* Default Simplifications *}

declare TrueV_def [simp]
declare FalseV_def [simp]
declare NegV_def [simp]
declare AndV_def [simp]
declare OrV_def [simp]
declare ImpV_def [simp]
declare IffV_def [simp]
end

subsection {* Integer Sort *}

class INT_SORT =
  fixes MkInt :: "int \<Rightarrow> 'a::TYPED_MODEL uval"
  fixes DestInt :: "'a uval \<Rightarrow> int"
  fixes IntType :: "'a utype"
  assumes INSTANCE : "UTP_BASIC_SORT MkInt DestInt UNIV IntType"
begin

subsubsection {* Locale Imports *}

abbreviation IsInt :: "'a uval \<Rightarrow> bool" where
"IsInt \<equiv> UTP_BASIC_SORT.IsVal IntType"

theorems
  IsInt_def [simp] = UTP_BASIC_SORT.IsVal_def [OF INSTANCE]

theorems
  MkInt_defined [defined] = UTP_BASIC_SORT.MkVal_defined [OF INSTANCE] and
  MkInt_typed [simplified, typing] = UTP_BASIC_SORT.MkVal_typed [OF INSTANCE] and
  MkInt_inverse [simplified, simp] = UTP_BASIC_SORT.MkVal_inverse [OF INSTANCE] and
  DestInt_inverse [simp] = UTP_BASIC_SORT.DestVal_inverse [OF INSTANCE] and
  MkInt_inj_on [simp] = UTP_BASIC_SORT.MkVal_inj_on [OF INSTANCE] and
  DestInt_inj_on [simp] = UTP_BASIC_SORT.DestVal_inj_on [OF INSTANCE]

theorems
  dcarrier_IntType = UTP_BASIC_SORT.dcarrier_Type [OF INSTANCE] and
  DestInt_dcarrier_image = UTP_BASIC_SORT.DestVal_dcarrier_image [OF INSTANCE] and
  in_image_IntVal = UTP_BASIC_SORT.in_image_MkVal [OF INSTANCE]

subsubsection {* Integer Values *}

definition INT_VALUE :: "'a uval set" where
"INT_VALUE = dcarrier IntType"

subsubsection {* Constants *}

subsubsection {* Operators *}

definition UnaryMinusV :: "'a uval \<Rightarrow> 'a uval" where
"UnaryMinusV v = MkInt(-DestInt(v))"
notation UnaryMinusV ("-\<^sub>v _" [81] 80)

definition PlusV :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"PlusV v1 v2 = MkInt(DestInt(v1) + DestInt(v2))"
notation PlusV (infixl "+\<^sub>v" 65)

definition MinusV :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"MinusV v1 v2 = MkInt(DestInt(v1) - DestInt(v2))"
notation MinusV (infixl "-\<^sub>v" 65)

definition TimesV :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"TimesV v1 v2 = MkInt(DestInt(v1) * DestInt(v2))"
notation TimesV (infixl "*\<^sub>v" 70)

definition DivideV :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"DivideV v1 v2 = MkInt(DestInt(v1) div DestInt(v2))"
notation DivideV (infixl "div\<^sub>v" 70)

definition ModV :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"ModV v1 v2 = MkInt(DestInt(v1) mod DestInt(v2))"
notation ModV (infixl "mod\<^sub>v" 70)

subsubsection {* Proof Support *}

theorem MkInt_eqI [intro] :
"x = y \<Longrightarrow> MkInt x = MkInt y"
apply (erule arg_cong)
done

paragraph {* Default Simplifications *}

declare UnaryMinusV_def [simp]
declare PlusV_def [simp]
declare MinusV_def [simp]
declare TimesV_def [simp]
declare DivideV_def [simp]
declare ModV_def [simp]
end

subsection {* Real Sort *}

class REAL_SORT =
  fixes MkReal :: "real \<Rightarrow> 'a::TYPED_MODEL uval"
  fixes DestReal :: "'a uval \<Rightarrow> real"
  fixes RealType :: "'a utype" (* ("\<real>") *)
  assumes INSTANCE : "UTP_BASIC_SORT MkReal DestReal UNIV RealType"
begin

subsubsection {* Locale Imports *}

abbreviation IsReal :: "'a uval \<Rightarrow> bool" where
"IsReal \<equiv> UTP_BASIC_SORT.IsVal RealType"

theorems
  IsReal_def [simp] = UTP_BASIC_SORT.IsVal_def [OF INSTANCE]

theorems
  MkReal_defined [defined] = UTP_BASIC_SORT.MkVal_defined [OF INSTANCE] and
  MkReal_typed [simplified, typing] = UTP_BASIC_SORT.MkVal_typed [OF INSTANCE] and
  MkReal_inverse [simplified, simp] = UTP_BASIC_SORT.MkVal_inverse [OF INSTANCE] and
  DestReal_inverse [simp] = UTP_BASIC_SORT.DestVal_inverse [OF INSTANCE] and
  MkReal_inj_on [simp] = UTP_BASIC_SORT.MkVal_inj_on [OF INSTANCE] and
  DestReal_inj_on [simp] = UTP_BASIC_SORT.DestVal_inj_on [OF INSTANCE]

theorems
  dcarrier_RealType = UTP_BASIC_SORT.dcarrier_Type [OF INSTANCE] and
  DestReal_dcarrier_image = UTP_BASIC_SORT.DestVal_dcarrier_image [OF INSTANCE] and
  in_image_RealVal = UTP_BASIC_SORT.in_image_MkVal [OF INSTANCE]

subsubsection {* Real Values *}

definition REAL_VALUE :: "'a uval set" where
"REAL_VALUE = dcarrier RealType"

subsubsection {* Constants *}

subsubsection {* Operators *}

definition UnaryMinusR :: "'a uval \<Rightarrow> 'a uval" where
"UnaryMinusR v = MkReal(-DestReal(v))"
notation UnaryMinusR ("-\<^sub>r _" [81] 80)

definition PlusR :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"PlusR v1 v2 = MkReal(DestReal(v1) + DestReal(v2))"
notation PlusR (infixl "+\<^sub>r" 65)

definition MinusR :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"MinusR v1 v2 = MkReal(DestReal(v1) - DestReal(v2))"
notation MinusR (infixl "-\<^sub>r" 65)

definition TimesR :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"TimesR v1 v2 = MkReal(DestReal(v1) * DestReal(v2))"
notation TimesR (infixl "*\<^sub>r" 70)

definition DivideR :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"DivideR v1 v2 = MkReal(DestReal(v1) / DestReal(v2))"
notation DivideR (infixl "/\<^sub>r" 70)

subsubsection {* Theorems *}

theorem MkReal_strictly_typed [typing] :
"MkReal n :! RealType"
apply (metis MkReal_defined MkReal_typed UNIV_I strict_type_rel_def)
done

text {* TODO: Prove this theorem already in class @{text UTP_BASIC_SORT}. *}

theorem MkReal_cases [elim] :
"\<lbrakk>v :! RealType; \<And> i . v = MkReal i \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
apply (metis DestReal_inverse)
done
subsubsection {* Proof Support *}

theorem MkReal_eqI [intro] :
"x = y \<Longrightarrow> MkReal x = MkReal y"
apply (erule arg_cong)
done

paragraph {* Default Simplifications *}

declare UnaryMinusR_def [simp]
declare PlusR_def [simp]
declare MinusR_def [simp]
declare TimesR_def [simp]
declare DivideR_def [simp]
end

subsection {* List Sort *}

text {* We require lists to be well-typed. *}

definition WT_LIST ::
  "'m::TYPED_MODEL utype \<Rightarrow> 'm::TYPED_MODEL uval list set" where
"WT_LIST t = {l . \<forall> x \<in> set l . x :! t}"

theorem WT_LIST_member [iff] :
"l \<in> WT_LIST t \<longleftrightarrow> (\<forall> x \<in> set l . x :! t)"
apply (simp add: WT_LIST_def)
done

class LIST_SORT =
  fixes MkList :: "'a::TYPED_MODEL utype \<Rightarrow> 'a uval list \<Rightarrow> 'a uval"
  fixes DestList :: "'a uval \<Rightarrow> 'a uval list"
  fixes ListType :: "'a utype \<Rightarrow> 'a utype"
  assumes INSTANCE : "UTP_PARAM_SORT MkList DestList WT_LIST ListType"
begin

subsubsection {* Locale Imports *}

abbreviation IsListType :: "'a utype \<Rightarrow> bool" where
"IsListType \<equiv> UTP_PARAM_SORT.IsType ListType"

abbreviation DestListType :: "'a utype \<Rightarrow> 'a utype" where
"DestListType \<equiv> UTP_PARAM_SORT.DestType ListType"

theorems
  MkList_defined [defined] = UTP_PARAM_SORT.MkVal_defined [OF INSTANCE] and
  MkList_typed [typing] = UTP_PARAM_SORT.MkVal_typed [OF INSTANCE] and
  MkList_inverse [simp] = UTP_PARAM_SORT.MkVal_inverse [OF INSTANCE] and
  DestList_inverse [simp] = UTP_PARAM_SORT.DestVal_inverse [OF INSTANCE] and
  (* WT_LIST_non_empty = UTP_PARAM_SORT.Domain_non_empty [OF INSTANCE] and *)
  ListType_inj = UTP_PARAM_SORT.MkType_inj [OF INSTANCE]

theorems
  MkList_definedI = UTP_PARAM_SORT.MkVal_definedI [OF INSTANCE] and
  MkList_strictly_typed = UTP_PARAM_SORT.MkVal_strictly_typed [OF INSTANCE] and
  MkList_witness = UTP_PARAM_SORT.MkVal_witness [OF INSTANCE] and
  MkList_unique_witness = UTP_PARAM_SORT.MkVal_unique_witness [OF INSTANCE] and
  IsListType_ListType = UTP_PARAM_SORT.IsType_MkType [OF INSTANCE] and
  IsListType_elim = UTP_PARAM_SORT.IsType_elim [OF INSTANCE] and
  ListType_elim = UTP_PARAM_SORT.MkType_elim [OF INSTANCE] and
  ListType_inverse = UTP_PARAM_SORT.MkType_inverse [OF INSTANCE] and
  DestListType_inverse = UTP_PARAM_SORT.DestType_inverse [OF INSTANCE]

subsubsection {* List Operators *}

definition NilV :: "'a utype \<Rightarrow> 'a uval" where
"NilV t = MkList t []"
notation NilV ("[]\<^bsub>_\<^esub>")

definition ConsV :: "'a utype \<Rightarrow> 'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"ConsV t x xs = MkList t (x # DestList xs)"

abbreviation ConsV_syn :: "'a uval \<Rightarrow> 'a utype \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"ConsV_syn xs t ys \<equiv> ConsV t xs ys"
notation ConsV_syn (infixr "#\<^bsub>_\<^esub>" 65)

definition ConcatV :: "'a utype \<Rightarrow> 'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"ConcatV t xs ys = MkList t (DestList xs @ DestList ys)"

abbreviation ConcatV_syn :: "'a uval \<Rightarrow> 'a utype \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"ConcatV_syn xs t ys \<equiv> ConcatV t xs ys"
notation ConcatV_syn (infixr "@\<^bsub>_\<^esub>" 65)

definition PrefixV ::
  "'b::{LIST_SORT,BOOL_SORT} uval \<Rightarrow> 'b uval \<Rightarrow> 'b uval" where
"PrefixV xs ys = MkBool (prefixeq (DestList xs) (DestList ys))"

paragraph {* Default Simplifications *}

declare NilV_def [simp]
declare ConsV_def [simp]
declare ConcatV_def [simp]
declare PrefixV_def [simp]

subsubsection {* Theorems *}

paragraph {* Well-typed Lists *}

theorem empty_WT_LIST :
"[] \<in> WT_LIST t"
apply (simp)
done

theorem Cons_WT_LIST :
"(x # l) \<in> WT_LIST t \<longleftrightarrow> (x :! t) \<and> (l \<in> WT_LIST t)"
apply (simp)
done

theorem concat_WT_LIST :
"(l1 @ l2) \<in> WT_LIST t \<longleftrightarrow> (l1 \<in> WT_LIST t) \<and> (l2 \<in> WT_LIST t)"
apply (induct_tac l1)
apply (simp_all)
done

theorem WT_LIST_non_empty :
"WT_LIST t \<noteq> {}"
apply (fold ex_in_conv)
apply (rule_tac x = "[]" in exI)
apply (rule empty_WT_LIST)
done

theorem NilV_defined [defined] :
"\<D>\<^sub>v (NilV t)"
apply (unfold NilV_def)
apply (rule MkList_definedI)
apply (rule empty_WT_LIST)
done

theorem NilV_typed [typing] :
"(NilV t) : (ListType t)"
apply (unfold NilV_def)
apply (rule MkList_typed)
apply (rule empty_WT_LIST)
done

theorem ConsV_typed [typing] :
"\<lbrakk>x :! t; xs :! ListType t\<rbrakk> \<Longrightarrow> (x #\<^bsub>t\<^esub> xs) :! ListType t"
apply (metis ConsV_def Cons_WT_LIST
  DestList_inverse MkList_defined MkList_strictly_typed strict_type_rel_def)
done

theorem ConcatV_typed [typing] :
"\<lbrakk>xs :! ListType t; ys :! ListType t\<rbrakk> \<Longrightarrow> (xs @\<^bsub>t\<^esub> ys) :! ListType t"
apply (metis ConcatV_def concat_WT_LIST
  DestList_inverse MkList_defined MkList_strictly_typed strict_type_rel_def)
done

theorem ListType_cases :
  assumes "xs :! ListType t"
  shows "(xs = []\<^bsub>t\<^esub>) \<or> (\<exists> y ys . y :! t \<and> ys :! ListType t \<and> xs = y #\<^bsub>t\<^esub> ys)"
proof -
  from assms have "xs \<in> (MkList t) ` {l . set l \<subseteq> dcarrier t}"
    apply (simp add: image_def)
    apply (rule_tac x = "DestList xs" in exI)
    apply (simp)
    apply (rule subsetI)
    apply (unfold dcarrier_member)
    apply (metis DestList_inverse MkList_defined WT_LIST_member assms(1))
  done

  then obtain ys where ys_facts :
      "xs = MkList t ys" and ys_carrier : "set ys \<subseteq> dcarrier t"
    by (auto)

  from assms(1) and ys_carrier
  have "MkList t ys = []\<^bsub>t\<^esub> \<or>
    (\<exists> z zs . z :! t \<and> zs :! ListType t \<and> MkList t ys = z #\<^bsub>t\<^esub> zs)"
  proof (induct ys)
    case Nil thus ?case
      by (simp)
  next
    case (Cons y ys) thus ?case
      apply (rule_tac disjI2)
      apply (rule_tac x = "y" in exI)
      apply (rule_tac x = "MkList t ys" in exI)
      apply (clarify)
      apply (simp add: typing defined)
      apply (metis ConsV_def MkList_inverse MkList_typed WT_LIST_member
        dcarrier_member set_rev_mp strict_type_rel_def)
    done
  qed

  with ys_facts show ?thesis by (simp)
qed

(***********************)
(* REVIEWED UNTIL HERE *)
(***********************)

theorem DestList_subset_dcarrier :
"xs :! ListType t \<Longrightarrow> set (DestList xs) \<subseteq> dcarrier t"
apply (metis ListType_elim MkList_inverse WT_LIST_member dcarrier_member subsetI)
done

theorem in_DestList_strictly_typed :
"\<lbrakk>x \<in> set (DestList xs); xs :! ListType t\<rbrakk> \<Longrightarrow> x :! t"
apply (metis DestList_subset_dcarrier dcarrier_member set_rev_mp)
done

theorem subset_dcarrier_WT_LIST :
"set xs \<subseteq> dcarrier t \<Longrightarrow> xs \<in> WT_LIST t"
apply (metis WT_LIST_member dcarrier_member subset_code(1))
done

theorem MkList_inject [simp]:
"\<lbrakk>set xs \<subseteq> dcarrier t; set ys \<subseteq> dcarrier t\<rbrakk> \<Longrightarrow>
  (MkList t xs = MkList t ys) \<longleftrightarrow> xs = ys"
apply (metis MkList_inverse subset_dcarrier_WT_LIST)
done

subsubsection {* Proof Support *}

theorem MkList_eqI [intro!] :
"x = y \<Longrightarrow> MkList x = MkList y"
apply (erule arg_cong)
done
end

subsection {* Set Sort *}

text {* TODO: Use cardinality-bound sets here! *}

text {* We require sets to be well-typed. *}

definition WT_SET ::
  "'m::TYPED_MODEL utype \<Rightarrow> 'm::TYPED_MODEL uval set set" where
"WT_SET t = {fs . \<forall> x \<in> fs . x :! t}"

theorem WT_SET_member [iff] :
"fs \<in> WT_SET t \<longleftrightarrow> (\<forall> x \<in> fs . x :! t)"
apply (simp add: WT_SET_def)
done

class SET_SORT = BOOL_SORT +
  fixes MkSet :: "'a::TYPED_MODEL utype \<Rightarrow> 'a uval set \<Rightarrow> 'a uval"
  fixes DestSet :: "'a uval \<Rightarrow> 'a uval set"
  fixes SetType :: "'a utype \<Rightarrow> 'a utype"
  assumes INSTANCE: "UTP_PARAM_SORT MkSet DestSet WT_SET SetType"
begin

subsubsection {* Locale Imports *}

abbreviation IsSetType :: "'a utype \<Rightarrow> bool" where
"IsSetType \<equiv> UTP_PARAM_SORT.IsType SetType"

abbreviation DestSetType :: "'a utype \<Rightarrow> 'a utype" where
"DestSetType \<equiv> UTP_PARAM_SORT.DestType SetType"

theorems
  MkSet_defined [defined] = UTP_PARAM_SORT.MkVal_defined [OF INSTANCE] and
  MkSet_typed [typing] = UTP_PARAM_SORT.MkVal_typed [OF INSTANCE] and
  MkSet_inverse [simp] = UTP_PARAM_SORT.MkVal_inverse [OF INSTANCE] and
  DestSet_inverse [simp] = UTP_PARAM_SORT.DestVal_inverse [OF INSTANCE] and
  (* WT_SET_non_empty = UTP_PARAM_SORT.Domain_non_empty [OF INSTANCE] and *)
  SetType_inj = UTP_PARAM_SORT.MkType_inj [OF INSTANCE]

theorems
  MkSet_definedI = UTP_PARAM_SORT.MkVal_definedI [OF INSTANCE] and
  MkSet_strictly_typed = UTP_PARAM_SORT.MkVal_strictly_typed [OF INSTANCE] and
  MkSet_witness = UTP_PARAM_SORT.MkVal_witness [OF INSTANCE] and
  MkSet_unique_witness = UTP_PARAM_SORT.MkVal_unique_witness [OF INSTANCE] and
  IsSetType_SetType = UTP_PARAM_SORT.IsType_MkType [OF INSTANCE] and
  IsSetType_elim = UTP_PARAM_SORT.IsType_elim [OF INSTANCE] and
  SetType_elim = UTP_PARAM_SORT.MkType_elim [OF INSTANCE] and
  SetType_inverse = UTP_PARAM_SORT.MkType_inverse [OF INSTANCE] and
  DestSetType_inverse = UTP_PARAM_SORT.DestType_inverse [OF INSTANCE]

subsubsection {* Set Operators *}

definition EmptyV  :: "'a utype \<Rightarrow> 'a uval" where
"EmptyV t = MkSet t {}"

definition InsertV :: "'a utype \<Rightarrow> 'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"InsertV t x xs = MkSet t (insert x (DestSet xs))"

definition UnionV  :: "'a utype \<Rightarrow> 'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"UnionV t xs ys = MkSet t (DestSet xs \<union> DestSet ys)"

definition InterV  :: "'a utype \<Rightarrow> 'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"InterV t xs ys = MkSet t (DestSet xs \<inter> DestSet ys)"

definition MinusV  :: "'a utype \<Rightarrow> 'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"MinusV t xs ys = MkSet t (DestSet xs - DestSet ys)"

definition SubsetV :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"SubsetV xs ys = MkBool (DestSet xs \<subseteq> DestSet ys)"

definition MemberV :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"MemberV x xs = MkBool (x \<in> DestSet xs)"

definition NotMemberV :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"NotMemberV x xs = MkBool (x \<notin> DestSet xs)"
end

subsection {* Finite Set Sort *}

text {* We require finite sets to be well-typed. *}

definition WT_FSET ::
  "'m::TYPED_MODEL utype \<Rightarrow> 'm::TYPED_MODEL uval fset set" where
"WT_FSET t = {fs . \<forall> x \<in>\<^sub>f fs . x :! t}"

theorem WT_FSET_member [iff] :
"fs \<in> WT_FSET t \<longleftrightarrow> (\<forall> x \<in>\<^sub>f fs . x :! t)"
apply (simp add: WT_FSET_def)
done

class FSET_SORT = BOOL_SORT +
  fixes MkFSet :: "'a::TYPED_MODEL utype \<Rightarrow> 'a uval fset \<Rightarrow> 'a uval"
  fixes DestFSet :: "'a uval \<Rightarrow> 'a uval fset"
  fixes FSetType :: "'a utype \<Rightarrow> 'a utype"
  assumes INSTANCE: "UTP_PARAM_SORT MkFSet DestFSet WT_FSET FSetType"
begin

subsubsection {* Locale Imports *}

abbreviation IsFSetType :: "'a utype \<Rightarrow> bool" where
"IsFSetType \<equiv> UTP_PARAM_SORT.IsType FSetType"

abbreviation DestFSetType :: "'a utype \<Rightarrow> 'a utype" where
"DestFSetType \<equiv> UTP_PARAM_SORT.DestType FSetType"

theorems
  MkFSet_defined [defined] = UTP_PARAM_SORT.MkVal_defined [OF INSTANCE] and
  MkFSet_typed [typing] = UTP_PARAM_SORT.MkVal_typed [OF INSTANCE] and
  MkFSet_inverse [simp] = UTP_PARAM_SORT.MkVal_inverse [OF INSTANCE] and
  DestFSet_inverse [simp] = UTP_PARAM_SORT.DestVal_inverse [OF INSTANCE] and
  (* WT_FSET_non_empty = UTP_PARAM_SORT.Domain_non_empty [OF INSTANCE] and *)
  FSetType_inj = UTP_PARAM_SORT.MkType_inj [OF INSTANCE]

theorems
  MkFSet_definedI = UTP_PARAM_SORT.MkVal_definedI [OF INSTANCE] and
  MkFSet_strictly_typed = UTP_PARAM_SORT.MkVal_strictly_typed [OF INSTANCE] and
  MkFSet_witness = UTP_PARAM_SORT.MkVal_witness [OF INSTANCE] and
  MkFSet_unique_witness = UTP_PARAM_SORT.MkVal_unique_witness [OF INSTANCE] and
  IsFSetType_FSetType = UTP_PARAM_SORT.IsType_MkType [OF INSTANCE] and
  IsFSetType_elim = UTP_PARAM_SORT.IsType_elim [OF INSTANCE] and
  FSetType_elim = UTP_PARAM_SORT.MkType_elim [OF INSTANCE] and
  FSetType_inverse = UTP_PARAM_SORT.MkType_inverse [OF INSTANCE] and
  DestFSetType_inverse = UTP_PARAM_SORT.DestType_inverse [OF INSTANCE]

subsubsection {* Finite Set Operators *}

definition FEmptyV  :: "'a utype \<Rightarrow> 'a uval" where
"FEmptyV t = MkFSet t \<lbrace>\<rbrace>"

definition FInsertV :: "'a utype \<Rightarrow> 'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"FInsertV t x xs = MkFSet t (finsert x (DestFSet xs))"

definition FUnionV  :: "'a utype \<Rightarrow> 'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"FUnionV t xs ys = MkFSet t (DestFSet xs \<union>\<^sub>f DestFSet ys)"

definition FInterV  :: "'a utype \<Rightarrow> 'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"FInterV t xs ys = MkFSet t (DestFSet xs \<inter>\<^sub>f DestFSet ys)"

definition FMinusV  :: "'a utype \<Rightarrow> 'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"FMinusV t xs ys = MkFSet t (DestFSet xs -\<^sub>f DestFSet ys)"

definition FSubsetV :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"FSubsetV xs ys = MkBool (DestFSet xs \<subseteq>\<^sub>f DestFSet ys)"

definition FMemberV :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"FMemberV x xs = MkBool (x \<in>\<^sub>f DestFSet xs)"

definition FNotMemberV :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"FNotMemberV x xs = MkBool (x \<notin>\<^sub>f DestFSet xs)"
end

(***********************)
(* REVIEWED AFTER HERE *)
(***********************)

subsection {* Function Sort *}

class FUNC_SORT = BOT_SORT +
  fixes MkFunc :: "('a::TYPED_MODEL uval \<Rightarrow> 'a uval) \<Rightarrow> 'a uval"
  fixes DestFunc :: "'a uval \<Rightarrow> ('a uval \<Rightarrow> 'a uval)"
  fixes IsFunc :: "('a uval \<Rightarrow> 'a uval) \<Rightarrow> bool"
  fixes FuncType :: "'a utype \<Rightarrow> 'a utype \<Rightarrow> 'a utype"
  assumes MkFunc_inverse [simp] : "IsFunc f \<Longrightarrow> DestFunc (MkFunc f) = f"
  assumes MkFunc_defined [simp] : "IsFunc f \<Longrightarrow> \<D>\<^sub>v (MkFunc f)"
  assumes MkFunc_range :
    "{MkFunc f | f . \<forall> x : a . (f x) : b \<and> IsFunc f} = dcarrier (FuncType a b)"
  assumes FuncType_inj1 : "FuncType a1 b1 = FuncType a2 b2 \<Longrightarrow> a1 = a2"
  assumes FuncType_inj2 : "FuncType a1 b1 = FuncType a2 b2 \<Longrightarrow> b1 = b2"
begin

subsubsection {* Type Destructors *}

definition func_inp_type :: "'a utype \<Rightarrow> 'a utype" where
"func_inp_type t = (THE a . \<exists> b . t = FuncType a b)"

definition func_out_type :: "'a utype \<Rightarrow> 'a utype" where
"func_out_type t = (THE b . \<exists> a . t = FuncType a b)"

theorem func_inp_type [simp] :
"func_inp_type (FuncType a b) = a"
apply (unfold func_inp_type_def)
apply (rule the1_equality)
apply (safe)
-- {* Subgoal 1 *}
apply (metis)
-- {* Subgoal 2 *}
apply (metis FuncType_inj1)
-- {* Subgoal 3 *}
apply (metis)
done

theorem func_out_type [simp]:
"func_out_type (FuncType a b) = b"
apply (unfold func_out_type_def)
apply (rule the1_equality)
apply (safe)
-- {* Subgoal 1 *}
apply (metis)
-- {* Subgoal 2 *}
apply (metis FuncType_inj2)
-- {* Subgoal 3 *}
apply (metis)
done

subsubsection {* Function Operators *}

definition AppV :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"AppV f = DestFunc f"

definition CompV :: "'a uval \<Rightarrow> 'a uval \<Rightarrow> 'a uval" where
"CompV f g = MkFunc (DestFunc f \<circ> DestFunc g)"

subsubsection {* Default Simplifications *}

declare AppV_def [simp]
declare CompV_def [simp]

subsubsection {* Theorems *}

lemma MkFunc_typed [typing] :
"\<lbrakk>\<forall> x : a . (f x) : b; IsFunc f\<rbrakk> \<Longrightarrow> (MkFunc f) : (FuncType a b)"
apply (insert MkFunc_range [of a b])
apply (simp add: set_eq_iff)
apply (metis)
done

lemma DestFunc_app_typed [typing] :
"\<lbrakk>f : FuncType a b; x : a; \<D>\<^sub>v f\<rbrakk> \<Longrightarrow> (DestFunc f) x : b"
apply (insert MkFunc_range [of a b])
apply (simp add: set_eq_iff)
apply (metis MkFunc_inverse)
done
end
end
