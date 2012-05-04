(******************************************************************************)
(* Title: utp/models/utp_ho1_value.thy                                        *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory utp_ho1_value
imports "../GLOBAL" "../utp_sorts" "../generic/utp_composite_value"
  utp_default_value
  utp_std_pred
begin

section {* HO1 Values *}

subsection {* Program Encoding *}

text {* We might not need a type for @{text "STD_PREDICATE"}. *}

typedef (open) STD_PREDICATE_T = "STD.WF_ALPHA_PREDICATE"
  morphisms Dest_STD_PREDICATE Mk_STD_PREDICATE
apply (rule_tac x = "FALSE" in exI)
apply (auto)
done

typedef (open) STD_ALPHABET_T = "STD.WF_ALPHABET"
  morphisms Dest_STD_ALPHABET Mk_STD_ALPHABET
apply (rule_tac x = "{}" in exI)
apply (auto)
done

subsubsection {* Default Simplifications *}

declare Mk_STD_PREDICATE_inverse [simp]
declare Dest_STD_PREDICATE_inverse [simp]
declare Mk_STD_PREDICATE_inject [simp, intro!]
declare Dest_STD_PREDICATE_inject [simp, intro!]
declare Dest_STD_PREDICATE [simp]

declare Mk_STD_ALPHABET_inverse [simp]
declare Dest_STD_ALPHABET_inverse [simp]
declare Mk_STD_ALPHABET_inject [simp, intro!]
declare Dest_STD_ALPHABET_inject [simp, intro!]
declare Dest_STD_ALPHABET [simp]

subsection {* Value Encoding *}

types BASE_VALUE = "STD_VALUE"
types PROG_VALUE = "STD_PREDICATE_T"

datatype HO1_VALUE =
  BaseVal "BASE_VALUE" |
  ProgVal "PROG_VALUE"

types BASE_TYPE = "STD_TYPE"
types PROG_TYPE = "STD_ALPHABET_T"

datatype HO1_TYPE =
  BaseType "BASE_TYPE" |
  ProgType "PROG_TYPE"

subsubsection {* Destructors *}

primrec BaseOf :: "HO1_VALUE \<Rightarrow> BASE_VALUE" where
"BaseOf (BaseVal v) = v"

primrec ProgOf :: "HO1_VALUE \<Rightarrow> PROG_VALUE" where
"ProgOf (ProgVal p) = p"

primrec BaseTypeOf :: "HO1_TYPE \<Rightarrow> BASE_TYPE" where
"BaseTypeOf (BaseType t) = t"

primrec ProgTypeOf :: "HO1_TYPE \<Rightarrow> PROG_TYPE" where
"ProgTypeOf (ProgType t) = t"

subsubsection {* Tests *}

primrec IsBaseVal :: "HO1_VALUE \<Rightarrow> bool" where
"IsBaseVal (BaseVal _) = True" |
"IsBaseVal (ProgVal _) = False"

primrec IsProgVal :: "HO1_VALUE \<Rightarrow> bool" where
"IsProgVal (BaseVal _) = False" |
"IsProgVal (ProgVal _) = True"

primrec IsBaseType :: "HO1_TYPE \<Rightarrow> bool" where
"IsBaseType (BaseType _) = True" |
"IsBaseType (ProgType _) = False"

primrec IsProgType :: "HO1_TYPE \<Rightarrow> bool" where
"IsProgType (BaseType _) = False" |
"IsProgType (ProgType _) = True"

subsection {* Typing and Refinement *}

definition std_prog_type_rel :: "PROG_VALUE \<Rightarrow> PROG_TYPE \<Rightarrow> bool" where
"std_prog_type_rel p t \<longleftrightarrow>
 \<alpha> (Dest_STD_PREDICATE p) = (Dest_STD_ALPHABET t)"

definition std_prog_value_ref :: "PROG_VALUE \<Rightarrow> PROG_VALUE \<Rightarrow> bool" where
"std_prog_value_ref p1 p2 \<longleftrightarrow>
 (Dest_STD_PREDICATE p1) \<sqsubseteq> (Dest_STD_PREDICATE p2)"

defs global_std_prog_type_rel [simp] :
"GLOBAL.type_rel \<equiv> std_prog_type_rel"

fun ho1_type_rel :: "HO1_VALUE \<Rightarrow> HO1_TYPE \<Rightarrow> bool" where
"ho1_type_rel (BaseVal v) (BaseType t) = (v : t)" |
"ho1_type_rel (BaseVal v) (ProgType t) = False" |
"ho1_type_rel (ProgVal v) (ProgType t) = (std_prog_type_rel v t)" |
"ho1_type_rel (ProgVal v) (BaseType t) = False"

fun ho1_value_ref :: "HO1_VALUE \<Rightarrow> HO1_VALUE \<Rightarrow> bool" where
"ho1_value_ref (BaseVal v1) (BaseVal v2) = (v1 \<sqsubseteq>v v2)" |
"ho1_value_ref (BaseVal v1) (ProgVal v2) = False" |
"ho1_value_ref (ProgVal v1) (ProgVal v2) = (std_prog_value_ref v1 v2)" |
"ho1_value_ref (ProgVal v1) (BaseVal v2) = False"

declare std_prog_type_rel_def [simp]
declare std_prog_value_ref_def [simp]

subsection {* Sort Membership *}

text {*
  Instantiation to @{text "COMPOSITE_SORT"} succeeds because we removed the
  inverse assumptions from the various value sorts; in particular, previous
  attempts failed to establish the inverse assumptions for pairs and sets.
*}

instantiation HO1_VALUE :: COMPOSITE_SORT
begin
definition ValueRef_HO1_VALUE [simp] :
"ValueRef_HO1_VALUE = ho1_value_ref"
definition MkInt_HO1_VALUE [simp] :
"MkInt_HO1_VALUE i = BaseVal (MkInt i)"
definition DestInt_HO1_VALUE [simp] :
"DestInt_HO1_VALUE v = DestInt (BaseOf v)"
definition IsInt_HO1_VALUE [simp] :
"IsInt_HO1_VALUE v = ((IsBaseVal v) \<and> (IsInt (BaseOf v)))"
definition MkBool_HO1_VALUE [simp] :
"MkBool_HO1_VALUE i = BaseVal (MkBool i)"
definition DestBool_HO1_VALUE [simp] :
"DestBool_HO1_VALUE v = DestBool (BaseOf v)"
definition IsBool_HO1_VALUE [simp] :
"IsBool_HO1_VALUE v = ((IsBaseVal v) \<and> IsBool (BaseOf v))"
definition MkStr_HO1_VALUE [simp] :
"MkStr_HO1_VALUE i = BaseVal (MkStr i)"
definition DestStr_HO1_VALUE [simp] :
"DestStr_HO1_VALUE v = DestStr (BaseOf v)"
definition IsStr_HO1_VALUE [simp] :
"IsStr_HO1_VALUE v = ((IsBaseVal v) \<and> IsStr (BaseOf v))"
definition MkPair_HO1_VALUE [simp] :
"MkPair_HO1_VALUE v1_v2 =
   BaseVal (MkPair (BaseOf (fst v1_v2), BaseOf (snd v1_v2)))"
definition DestPair_HO1_VALUE [simp] :
"DestPair_HO1_VALUE v = (
   BaseVal (fst (DestPair (BaseOf v))),
   BaseVal (snd (DestPair (BaseOf v))))"
definition IsPair_HO1_VALUE [simp] :
"IsPair_HO1_VALUE v = ((IsBaseVal v) \<and> IsPair (BaseOf v))"
definition MkSet_HO1_VALUE [simp] :
"MkSet_HO1_VALUE vs = BaseVal (MkSet (BaseOf ` vs))"
definition DestSet_HO1_VALUE [simp] :
"DestSet_HO1_VALUE v = BaseVal ` (DestSet (BaseOf v))"
definition IsSet_HO1_VALUE [simp] :
"IsSet_HO1_VALUE v = ((IsBaseVal v) \<and> IsSet (BaseOf v))"
instance
apply (intro_classes)
done
end

instantiation STD_PREDICATE_T :: VALUE_SORT
begin
definition ValueRef_STD_PREDICATE [simp] :
"ValueRef_STD_PREDICATE = std_prog_value_ref"
instance
apply (intro_classes)
done
end

subsection {* Locale @{text "HO1_VALUE"} *}

locale HO1_VALUE_LOCALE = VALUE "ho1_type_rel"
begin

subsubsection {* Constructors *}

definition MkInt :: "int \<Rightarrow> HO1_VALUE" where
"MkInt = INT_SORT_class.MkInt"

definition MkBool :: "bool \<Rightarrow> HO1_VALUE" where
"MkBool = BOOL_SORT_class.MkBool"

definition MkStr :: "string \<Rightarrow> HO1_VALUE" where
"MkStr = STRING_SORT_class.MkStr"

definition MkPair ::
  "(HO1_VALUE \<times> HO1_VALUE) \<Rightarrow> HO1_VALUE" where
"MkPair = PAIR_SORT_class.MkPair"

definition MkSet :: "HO1_VALUE set \<Rightarrow> HO1_VALUE" where
"MkSet = SET_SORT_class.MkSet"

definition MkProg :
"MkProg p = ProgVal (Mk_STD_PREDICATE p)"

subsubsection {* Destructors *}

definition DestInt :: "HO1_VALUE \<Rightarrow> int" where
"DestInt = INT_SORT_class.DestInt"

definition DestBool :: "HO1_VALUE \<Rightarrow> bool" where
"DestBool = BOOL_SORT_class.DestBool"

definition DestStr :: "HO1_VALUE \<Rightarrow> string" where
"DestStr = STRING_SORT_class.DestStr"

definition DestPair ::
  "HO1_VALUE \<Rightarrow> (HO1_VALUE \<times> HO1_VALUE)" where
"DestPair = PAIR_SORT_class.DestPair"

definition DestSet :: "HO1_VALUE \<Rightarrow> HO1_VALUE set" where
"DestSet = SET_SORT_class.DestSet"

definition DestProg :
"DestProg v = Dest_STD_PREDICATE (ProgOf v)"

subsubsection {* Tests *}

definition IsInt :: "HO1_VALUE \<Rightarrow> bool" where
"IsInt = INT_SORT_class.IsInt"

definition IsBool :: "HO1_VALUE \<Rightarrow> bool" where
"IsBool = BOOL_SORT_class.IsBool"

definition IsStr :: "HO1_VALUE \<Rightarrow> bool" where
"IsStr = STRING_SORT_class.IsStr"

definition IsPair :: "HO1_VALUE \<Rightarrow> bool" where
"IsPair = PAIR_SORT_class.IsPair"

definition IsSet :: "HO1_VALUE \<Rightarrow> bool" where
"IsSet = SET_SORT_class.IsSet"

definition IsProg :: "HO1_VALUE \<Rightarrow> bool" where
"IsProg = IsProgVal"

subsubsection {* Default Simplifications *}

declare MkInt_def [simp]
declare MkBool_def [simp]
declare MkStr_def [simp]
declare MkPair_def [simp]
declare MkSet_def [simp]
declare MkProg [simp]

declare DestInt_def [simp]
declare DestBool_def [simp]
declare DestStr_def [simp]
declare DestPair_def [simp]
declare DestSet_def [simp]
declare DestProg [simp]

declare IsInt_def [simp]
declare IsBool_def [simp]
declare IsStr_def [simp]
declare IsPair_def [simp]
declare IsSet_def [simp]
declare IsProg_def [simp]
end

subsection {* Theorems *}

theorem VALUE_ho1_type_rel [simp] :
"VALUE ho1_type_rel"
apply (unfold_locales)
apply (induct_tac t)
apply (subgoal_tac "COMPOSITE_VALUE default_type_rel")
apply (simp add: COMPOSITE_VALUE_def VALUE_def)
apply (drule_tac x = "COMPOSITE_TYPE" in spec)
apply (safe)
apply (rule_tac x = "BaseVal x" in exI)
apply (simp)
apply (auto)
apply (rule_tac x =
  "ProgVal (Mk_STD_PREDICATE
     (STD.FalseP (Dest_STD_ALPHABET STD_ALPHABET_T)))" in exI)
apply (simp)
done
end
