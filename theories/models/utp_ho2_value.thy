(******************************************************************************)
(* Title: utp/models/utp_ho2_value.thy                                        *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory utp_ho2_value
imports "../GLOBAL" "../utp_sorts" "../generic/utp_composite_value"
  utp_ho1_value
  utp_ho1_pred
begin

section {* HO2 Values *}

subsection {* Program Encoding *}

typedef (open) HO1_PREDICATE_T = "HO1.WF_ALPHA_PREDICATE"
  morphisms "Dest_HO1_PREDICATE" "Mk_HO1_PREDICATE"
apply (rule_tac x = "FALSE" in exI)
apply (auto)
done

typedef (open) HO1_ALPHABET_T = "HO1.WF_ALPHABET"
  morphisms "Dest_HO1_ALPHABET" "Mk_HO1_ALPHABET"
apply (rule_tac x = "{}" in exI)
apply (auto)
done

subsubsection {* Default Simplifications *}

declare Mk_HO1_PREDICATE_inverse [simp]
declare Dest_HO1_PREDICATE_inverse [simp]
declare Mk_HO1_PREDICATE_inject [simp, intro!]
declare Dest_HO1_PREDICATE_inject [simp, intro!]
declare Dest_HO1_PREDICATE [simp]

declare Mk_HO1_ALPHABET_inverse [simp]
declare Dest_HO1_ALPHABET_inverse [simp]
declare Mk_HO1_ALPHABET_inject [simp, intro!]
declare Dest_HO1_ALPHABET_inject [simp, intro!]
declare Dest_HO1_ALPHABET [simp]

subsection {* Value Encoding *}

types BASE_VALUE = "STD_VALUE"
types PROG1_VALUE = "STD_PREDICATE_T"
types PROG2_VALUE = "HO1_PREDICATE_T"

datatype HO2_VALUE =
  BaseVal "BASE_VALUE" |
  Prog1Val "PROG1_VALUE" |
  Prog2Val "PROG2_VALUE"

types BASE_TYPE = "STD_TYPE"
types PROG1_TYPE = "STD_ALPHABET_T"
types PROG2_TYPE = "HO1_ALPHABET_T"

datatype HO2_TYPE =
  BaseType "BASE_TYPE" |
  Prog1Type "PROG1_TYPE" |
  Prog2Type "PROG2_TYPE"

subsubsection {* Destructors *}

primrec BaseOf :: "HO2_VALUE \<Rightarrow> BASE_VALUE" where
"BaseOf (BaseVal v) = v"

primrec Prog1Of :: "HO2_VALUE \<Rightarrow> PROG1_VALUE" where
"Prog1Of (Prog1Val p) = p"

primrec Prog2Of :: "HO2_VALUE \<Rightarrow> PROG2_VALUE" where
"Prog2Of (Prog2Val p) = p"

primrec BaseTypeOf :: "HO2_TYPE \<Rightarrow> BASE_TYPE" where
"BaseTypeOf (BaseType t) = t"

primrec Prog1TypeOf :: "HO2_TYPE \<Rightarrow> PROG1_TYPE" where
"Prog1TypeOf (Prog1Type t) = t"

primrec Prog2TypeOf :: "HO2_TYPE \<Rightarrow> PROG2_TYPE" where
"Prog2TypeOf (Prog2Type t) = t"

subsubsection {* Tests *}

primrec IsBaseVal :: "HO2_VALUE \<Rightarrow> bool" where
"IsBaseVal (BaseVal _) = True" |
"IsBaseVal (Prog1Val _) = False" |
"IsBaseVal (Prog2Val _) = False"

primrec IsProg1Val :: "HO2_VALUE \<Rightarrow> bool" where
"IsProg1Val (BaseVal _) = False" |
"IsProg1Val (Prog1Val _) = True" |
"IsProg1Val (Prog2Val _) = False"

primrec IsProg2Val :: "HO2_VALUE \<Rightarrow> bool" where
"IsProg2Val (BaseVal _) = False" |
"IsProg2Val (Prog1Val _) = False" |
"IsProg2Val (Prog2Val _) = True"

primrec IsBaseType :: "HO2_TYPE \<Rightarrow> bool" where
"IsBaseType (BaseType _) = True" |
"IsBaseType (Prog1Type _) = False" |
"IsBaseType (Prog2Type _) = False"

primrec IsProg1Type :: "HO2_TYPE \<Rightarrow> bool" where
"IsProg1Type (BaseType _) = False" |
"IsProg1Type (Prog1Type _) = True" |
"IsProg1Type (Prog2Type _) = False"

primrec IsProg2Type :: "HO2_TYPE \<Rightarrow> bool" where
"IsProg2Type (BaseType _) = False" |
"IsProg2Type (Prog1Type _) = False" |
"IsProg2Type (Prog2Type _) = True"

subsection {* Typing and Refinement *}

definition ho1_prog_type_rel :: "PROG2_VALUE \<Rightarrow> PROG2_TYPE \<Rightarrow> bool" where
"ho1_prog_type_rel p a \<longleftrightarrow>
 \<alpha> (Dest_HO1_PREDICATE p) = (Dest_HO1_ALPHABET a)"

definition ho1_prog_value_ref :: "PROG2_VALUE \<Rightarrow> PROG2_VALUE \<Rightarrow> bool" where
"ho1_prog_value_ref p1 p2 \<longleftrightarrow>
 (Dest_HO1_PREDICATE p1) \<sqsubseteq> (Dest_HO1_PREDICATE p2)"

defs global_ho1_prog_type_rel [simp] :
"GLOBAL.type_rel \<equiv> ho1_prog_type_rel"

fun ho2_type_rel :: "HO2_VALUE \<Rightarrow> HO2_TYPE \<Rightarrow> bool" where
"ho2_type_rel (BaseVal v) (BaseType t) = (v : t)" |
"ho2_type_rel (BaseVal v) (Prog1Type t) = False" |
"ho2_type_rel (BaseVal v) (Prog2Type t) = False" |
"ho2_type_rel (Prog1Val v) (BaseType t) = False" |
"ho2_type_rel (Prog1Val v) (Prog1Type t) = (std_prog_type_rel v t)" |
"ho2_type_rel (Prog1Val v) (Prog2Type t) = False" |
"ho2_type_rel (Prog2Val v) (BaseType t) = False" |
"ho2_type_rel (Prog2Val v) (Prog1Type t) = False" |
"ho2_type_rel (Prog2Val v) (Prog2Type t) = (ho1_prog_type_rel v t)"

fun ho2_value_ref :: "HO2_VALUE \<Rightarrow> HO2_VALUE \<Rightarrow> bool" where
"ho2_value_ref (BaseVal v1) (BaseVal v2) = (v1 \<sqsubseteq>v v2)" |
"ho2_value_ref (BaseVal v1) (Prog1Val v2) = False" |
"ho2_value_ref (BaseVal v1) (Prog2Val v2) = False" |
"ho2_value_ref (Prog1Val v1) (BaseVal v2) = False" |
"ho2_value_ref (Prog1Val v1) (Prog1Val v2) = (std_prog_value_ref v1 v2)" |
"ho2_value_ref (Prog1Val v1) (Prog2Val v2) = False" |
"ho2_value_ref (Prog2Val v1) (BaseVal v2) = False" |
"ho2_value_ref (Prog2Val v1) (Prog1Val v2) = False" |
"ho2_value_ref (Prog2Val v1) (Prog2Val v2) = (ho1_prog_value_ref v1 v2)"

declare ho1_prog_type_rel_def [simp]
declare ho1_prog_value_ref_def [simp]

subsection {* Sort Membership *}

text {*
  Instantiation to @{text "COMPOSITE_SORT"} succeeds because we removed the
  inverse assumptions from the various value sorts; in particular, previous
  attempts failed to establish the inverse assumptions for pairs and sets.
*}

instantiation HO2_VALUE :: COMPOSITE_SORT
begin
definition ValueRef_HO2_VALUE [simp] :
"ValueRef_HO2_VALUE = ho2_value_ref"
definition MkInt_HO2_VALUE [simp] :
"MkInt_HO2_VALUE i = BaseVal (MkInt i)"
definition DestInt_HO2_VALUE [simp] :
"DestInt_HO2_VALUE v = DestInt (BaseOf v)"
definition IsInt_HO2_VALUE [simp] :
"IsInt_HO2_VALUE v = ((IsBaseVal v) \<and> (IsInt (BaseOf v)))"
definition MkBool_HO2_VALUE [simp] :
"MkBool_HO2_VALUE i = BaseVal (MkBool i)"
definition DestBool_HO2_VALUE [simp] :
"DestBool_HO2_VALUE v = DestBool (BaseOf v)"
definition IsBool_HO2_VALUE [simp] :
"IsBool_HO2_VALUE v = ((IsBaseVal v) \<and> IsBool (BaseOf v))"
definition MkStr_HO2_VALUE [simp] :
"MkStr_HO2_VALUE i = BaseVal (MkStr i)"
definition DestStr_HO2_VALUE [simp] :
"DestStr_HO2_VALUE v = DestStr (BaseOf v)"
definition IsStr_HO2_VALUE [simp] :
"IsStr_HO2_VALUE v = ((IsBaseVal v) \<and> IsStr (BaseOf v))"
definition MkPair_HO2_VALUE [simp] :
"MkPair_HO2_VALUE v1_v2 =
   BaseVal (MkPair (BaseOf (fst v1_v2), BaseOf (snd v1_v2)))"
definition DestPair_HO2_VALUE [simp] :
"DestPair_HO2_VALUE v = (
   BaseVal (fst (DestPair (BaseOf v))),
   BaseVal (snd (DestPair (BaseOf v))))"
definition IsPair_HO2_VALUE [simp] :
"IsPair_HO2_VALUE v = ((IsBaseVal v) \<and> IsPair (BaseOf v))"
definition MkSet_HO2_VALUE [simp] :
"MkSet_HO2_VALUE vs = BaseVal (MkSet (BaseOf ` vs))"
definition DestSet_HO2_VALUE [simp] :
"DestSet_HO2_VALUE v = BaseVal ` (DestSet (BaseOf v))"
definition IsSet_HO2_VALUE [simp] :
"IsSet_HO2_VALUE v = ((IsBaseVal v) \<and> IsSet (BaseOf v))"
instance
apply (intro_classes)
done
end

instantiation HO1_PREDICATE_T :: VALUE_SORT
begin
definition ValueRef_HO1_PREDICATE_T [simp] :
"ValueRef_HO1_PREDICATE_T = ho1_prog_value_ref"
instance
apply (intro_classes)
done
end

subsection {* Locale @{text "HO2_VALUE"} *}

locale HO2_VALUE_LOCALE = VALUE "ho2_type_rel"
begin

subsubsection {* Constructors *}

definition MkInt :: "int \<Rightarrow> HO2_VALUE" where
"MkInt = INT_SORT_class.MkInt"

definition MkBool :: "bool \<Rightarrow> HO2_VALUE" where
"MkBool = BOOL_SORT_class.MkBool"

definition MkStr :: "string \<Rightarrow> HO2_VALUE" where
"MkStr = STRING_SORT_class.MkStr"

definition MkPair ::
  "(HO2_VALUE \<times> HO2_VALUE) \<Rightarrow> HO2_VALUE" where
"MkPair = PAIR_SORT_class.MkPair"

definition MkSet :: "HO2_VALUE set \<Rightarrow> HO2_VALUE" where
"MkSet = SET_SORT_class.MkSet"

definition MkProg1 :
"MkProg1 p = Prog1Val (Mk_STD_PREDICATE p)"

definition MkProg2 :
"MkProg2 p = Prog2Val (Mk_HO1_PREDICATE p)"

subsubsection {* Destructors *}

definition DestInt :: "HO2_VALUE \<Rightarrow> int" where
"DestInt = INT_SORT_class.DestInt"

definition DestBool :: "HO2_VALUE \<Rightarrow> bool" where
"DestBool = BOOL_SORT_class.DestBool"

definition DestStr :: "HO2_VALUE \<Rightarrow> string" where
"DestStr = STRING_SORT_class.DestStr"

definition DestPair ::
  "HO2_VALUE \<Rightarrow> (HO2_VALUE \<times> HO2_VALUE)" where
"DestPair = PAIR_SORT_class.DestPair"

definition DestSet :: "HO2_VALUE \<Rightarrow> HO2_VALUE set" where
"DestSet = SET_SORT_class.DestSet"

definition DestProg1 :
"DestProg1 v = Dest_STD_PREDICATE (Prog1Of v)"

definition DestProg2 :
"DestProg2 v = Dest_HO1_PREDICATE (Prog2Of v)"

subsubsection {* Tests *}

definition IsInt :: "HO2_VALUE \<Rightarrow> bool" where
"IsInt = INT_SORT_class.IsInt"

definition IsBool :: "HO2_VALUE \<Rightarrow> bool" where
"IsBool = BOOL_SORT_class.IsBool"

definition IsStr :: "HO2_VALUE \<Rightarrow> bool" where
"IsStr = STRING_SORT_class.IsStr"

definition IsPair :: "HO2_VALUE \<Rightarrow> bool" where
"IsPair = PAIR_SORT_class.IsPair"

definition IsSet :: "HO2_VALUE \<Rightarrow> bool" where
"IsSet = SET_SORT_class.IsSet"

definition IsProg1 :: "HO2_VALUE \<Rightarrow> bool" where
"IsProg1 = IsProg1Val"

definition IsProg2 :: "HO2_VALUE \<Rightarrow> bool" where
"IsProg2 = IsProg2Val"

subsubsection {* Default Simplifications *}

declare MkInt_def [simp]
declare MkBool_def [simp]
declare MkStr_def [simp]
declare MkPair_def [simp]
declare MkSet_def [simp]
declare MkProg1 [simp]
declare MkProg2 [simp]

declare DestInt_def [simp]
declare DestBool_def [simp]
declare DestStr_def [simp]
declare DestPair_def [simp]
declare DestSet_def [simp]
declare DestProg1 [simp]
declare DestProg2 [simp]

declare IsInt_def [simp]
declare IsBool_def [simp]
declare IsStr_def [simp]
declare IsPair_def [simp]
declare IsSet_def [simp]
declare IsProg1_def [simp]
declare IsProg2_def [simp]
end

subsection {* Theorems *}

theorem VALUE_ho2_type_rel [simp] :
"VALUE ho2_type_rel"
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
  "Prog1Val (Mk_STD_PREDICATE
     (STD.FalseP (Dest_STD_ALPHABET STD_ALPHABET_T)))" in exI)
apply (simp)
apply (rule_tac x =
  "Prog2Val (Mk_HO1_PREDICATE
     (HO1.FalseP (Dest_HO1_ALPHABET HO1_ALPHABET_T)))" in exI)
apply (simp)
done
end