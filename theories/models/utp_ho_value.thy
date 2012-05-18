(******************************************************************************)
(* Title: utp/models/utp_ho_value.thy                                         *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Higher Order Values *}

theory utp_ho_value
imports "../GLOBAL"
  "../utp_sorts"
  "../generic/utp_var"
  "../generic/utp_composite_value"
  utp_default_value
begin

subsection {* Type Definitions *}

subsubsection {* Program Type *}

text {* We introduce the program type abstractly. Morphisms are defined later on. *}

typedecl PROGRAM

subsubsection {* Value Type *}

types BASE_VALUE = "DEFAULT_VALUE COMPOSITE_VALUE"
types BASE_TYPE = "DEFAULT_TYPE COMPOSITE_TYPE"

datatype HO_VALUE =
  BaseVal "BASE_VALUE" |
  ProgVal "PROGRAM"

datatype HO_TYPE =
  BaseType "BASE_TYPE" |
  ProgType "(HO_TYPE VAR) list"

text {* Type Synonyms *}

types PROG_TYPE = "(HO_TYPE VAR) list"

text {* Destructors *}

primrec BaseOf :: "HO_VALUE \<Rightarrow> BASE_VALUE" where
"BaseOf (BaseVal v) = v"

primrec ProgOf :: "HO_VALUE \<Rightarrow> PROGRAM" where
"ProgOf (ProgVal p) = p"

primrec BaseTypeOf :: "HO_TYPE \<Rightarrow> BASE_TYPE" where
"BaseTypeOf (BaseType t) = t"

primrec ProgTypeOf :: "HO_TYPE \<Rightarrow> PROG_TYPE" where
"ProgTypeOf (ProgType t) = t"

text {* Tests *}

primrec IsBaseVal :: "HO_VALUE \<Rightarrow> bool" where
"IsBaseVal (BaseVal _) = True" |
"IsBaseVal (ProgVal _) = False"

primrec IsProgVal :: "HO_VALUE \<Rightarrow> bool" where
"IsProgVal (BaseVal _) = False" |
"IsProgVal (ProgVal _) = True"

primrec IsBaseType :: "HO_TYPE \<Rightarrow> bool" where
"IsBaseType (BaseType _) = True" |
"IsBaseType (ProgType _) = False"

primrec IsProgType :: "HO_TYPE \<Rightarrow> bool" where
"IsProgType (BaseType _) = False" |
"IsProgType (ProgType _) = True"

definition IsBaseVar :: "HO_TYPE VAR \<Rightarrow> bool" where
"IsBaseVar x = IsBaseType (type x)"

definition IsProgVar :: "HO_TYPE VAR \<Rightarrow> bool" where
"IsProgVar x = IsProgType (type x)"

subsection {* Typing and Refinement *}

consts ProgAlpha :: "PROGRAM \<Rightarrow> (HO_TYPE VAR) set" ("\<alpha>P")

definition prog_type_rel ::
  "PROGRAM \<Rightarrow> PROG_TYPE \<Rightarrow> bool" (infix ":P" 50) where
"prog_type_rel p t = ((\<alpha>P p) = set t)"

declare prog_type_rel_def [simp]

fun ho_type_rel :: "HO_VALUE \<Rightarrow> HO_TYPE \<Rightarrow> bool" where
"ho_type_rel (BaseVal v) (BaseType t) = (v : t)" |
"ho_type_rel (BaseVal v) (ProgType t) = False" |
"ho_type_rel (ProgVal p) (BaseType t) = False" |
"ho_type_rel (ProgVal p) (ProgType t) = (p :P t)"

consts ProgRefine :: "PROGRAM \<Rightarrow> PROGRAM \<Rightarrow> bool" (infix "\<sqsubseteq>P" 50)

fun ho_value_ref :: "HO_VALUE \<Rightarrow> HO_VALUE \<Rightarrow> bool" where
"ho_value_ref (BaseVal v1) (BaseVal v2) = (v1 \<sqsubseteq>v v2)" |
"ho_value_ref (BaseVal v1) (ProgVal v2) = False" |
"ho_value_ref (ProgVal v1) (BaseVal v2) = False" |
"ho_value_ref (ProgVal v1) (ProgVal v2) = (v1 \<sqsubseteq>P v2)"

subsection {* Global Syntax *}

defs global_base_type_rel [simp] :
"GLOBAL.type_rel \<equiv>
 lift_type_rel_composite default_type_rel"

defs global_prog_type_rel [simp] :
"GLOBAL.type_rel p t \<equiv> (\<alpha>P p) = set t"

defs global_ho_type_rel [simp] :
"GLOBAL.type_rel \<equiv> ho_type_rel"

subsection {* Sort Membership *}

text {*
  Instantiation to @{text "COMPOSITE_SORT"} succeeds because we removed the
  inverse assumptions from the various value sorts; in particular, previous
  attempts failed to establish the inverse assumptions for pairs and sets.
*}

instantiation HO_VALUE :: COMPOSITE_SORT
begin
definition ValueRef_HO_VALUE [simp] :
"ValueRef_HO_VALUE = ho_value_ref"
definition MkInt_HO_VALUE [simp] :
"MkInt_HO_VALUE i = BaseVal (MkInt i)"
definition DestInt_HO_VALUE [simp] :
"DestInt_HO_VALUE v = DestInt (BaseOf v)"
definition IsInt_HO_VALUE [simp] :
"IsInt_HO_VALUE v = ((IsBaseVal v) \<and> (IsInt (BaseOf v)))"
definition MkBool_HO_VALUE [simp] :
"MkBool_HO_VALUE i = BaseVal (MkBool i)"
definition DestBool_HO_VALUE [simp] :
"DestBool_HO_VALUE v = DestBool (BaseOf v)"
definition IsBool_HO_VALUE [simp] :
"IsBool_HO_VALUE v = ((IsBaseVal v) \<and> IsBool (BaseOf v))"
definition MkStr_HO_VALUE [simp] :
"MkStr_HO_VALUE i = BaseVal (MkStr i)"
definition DestStr_HO_VALUE [simp] :
"DestStr_HO_VALUE v = DestStr (BaseOf v)"
definition IsStr_HO_VALUE [simp] :
"IsStr_HO_VALUE v = ((IsBaseVal v) \<and> IsStr (BaseOf v))"
definition MkPair_HO_VALUE [simp] :
"MkPair_HO_VALUE v1_v2 =
   BaseVal (MkPair (BaseOf (fst v1_v2), BaseOf (snd v1_v2)))"
definition DestPair_HO_VALUE [simp] :
"DestPair_HO_VALUE v = (
   BaseVal (fst (DestPair (BaseOf v))),
   BaseVal (snd (DestPair (BaseOf v))))"
definition IsPair_HO_VALUE [simp] :
"IsPair_HO_VALUE v = ((IsBaseVal v) \<and> IsPair (BaseOf v))"
definition MkSet_HO_VALUE [simp] :
"MkSet_HO_VALUE vs = BaseVal (MkSet (BaseOf ` vs))"
definition DestSet_HO_VALUE [simp] :
"DestSet_HO_VALUE v = BaseVal ` (DestSet (BaseOf v))"
definition IsSet_HO_VALUE [simp] :
"IsSet_HO_VALUE v = ((IsBaseVal v) \<and> IsSet (BaseOf v))"
instance
apply (intro_classes)
done
end

subsection {* Locale @{text "HO_VALUE"} *}

locale HO_VALUE = VALUE "ho_type_rel"
begin

text {* Constructors *}

definition MkInt :: "int \<Rightarrow> HO_VALUE" where
"MkInt = INT_SORT_class.MkInt"

definition MkBool :: "bool \<Rightarrow> HO_VALUE" where
"MkBool = BOOL_SORT_class.MkBool"

definition MkStr :: "string \<Rightarrow> HO_VALUE" where
"MkStr = STRING_SORT_class.MkStr"

definition MkPair ::
  "(HO_VALUE \<times> HO_VALUE) \<Rightarrow> HO_VALUE" where
"MkPair = PAIR_SORT_class.MkPair"

definition MkSet :: "HO_VALUE set \<Rightarrow> HO_VALUE" where
"MkSet = SET_SORT_class.MkSet"

definition MkProg :: "PROGRAM \<Rightarrow> HO_VALUE" where
"MkProg = ProgVal"

text {* Destructors *}

definition DestInt :: "HO_VALUE \<Rightarrow> int" where
"DestInt = INT_SORT_class.DestInt"

definition DestBool :: "HO_VALUE \<Rightarrow> bool" where
"DestBool = BOOL_SORT_class.DestBool"

definition DestStr :: "HO_VALUE \<Rightarrow> string" where
"DestStr = STRING_SORT_class.DestStr"

definition DestPair ::
  "HO_VALUE \<Rightarrow> (HO_VALUE \<times> HO_VALUE)" where
"DestPair = PAIR_SORT_class.DestPair"

definition DestSet :: "HO_VALUE \<Rightarrow> HO_VALUE set" where
"DestSet = SET_SORT_class.DestSet"

definition DestProg :: "HO_VALUE \<Rightarrow> PROGRAM" where
"DestProg = ProgOf"

text {* Tests *}

definition IsInt :: "HO_VALUE \<Rightarrow> bool" where
"IsInt = INT_SORT_class.IsInt"

definition IsBool :: "HO_VALUE \<Rightarrow> bool" where
"IsBool = BOOL_SORT_class.IsBool"

definition IsStr :: "HO_VALUE \<Rightarrow> bool" where
"IsStr = STRING_SORT_class.IsStr"

definition IsPair :: "HO_VALUE \<Rightarrow> bool" where
"IsPair = PAIR_SORT_class.IsPair"

definition IsSet :: "HO_VALUE \<Rightarrow> bool" where
"IsSet = SET_SORT_class.IsSet"

definition IsProg :: "HO_VALUE \<Rightarrow> bool" where
"IsProg = IsProgVal"

text {* Default Simplifications *}

declare MkInt_def [simp]
declare MkBool_def [simp]
declare MkStr_def [simp]
declare MkPair_def [simp]
declare MkSet_def [simp]
declare MkProg_def [simp]

declare DestInt_def [simp]
declare DestBool_def [simp]
declare DestStr_def [simp]
declare DestPair_def [simp]
declare DestSet_def [simp]
declare DestProg_def [simp]

declare IsInt_def [simp]
declare IsBool_def [simp]
declare IsStr_def [simp]
declare IsPair_def [simp]
declare IsSet_def [simp]
declare IsProg_def [simp]
end

subsection {* Theorems *}

theorem VALUE_ho_type_rel [simp] :
"VALUE prog_type_rel \<Longrightarrow> VALUE ho_type_rel"
apply (unfold_locales)
apply (induct_tac t)
apply (subgoal_tac "COMPOSITE_VALUE default_type_rel")
apply (simp add: COMPOSITE_VALUE_def VALUE_def)
apply (drule_tac x = "COMPOSITE_TYPE" in spec)
apply (safe)
apply (rule_tac x = "BaseVal x" in exI)
apply (simp)
apply (auto)
apply (simp add: VALUE_def)
apply (drule_tac x = "list" in spec)
apply (clarsimp)
apply (rule_tac x = "ProgVal x" in exI)
apply (simp)
done
end
