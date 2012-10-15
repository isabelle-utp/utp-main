(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_composite_value.thy                                              *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Composite Values *}

theory utp_composite_value
imports
  "../utp_common"
  "../utp_global"
  "../core/utp_sorts"
  "../core/utp_value"
  "../utils/utp_sets"
begin

subsection {* Type Definitions *}

text {* Does @{term "SetVal"} need to know about the type of the set? *}

datatype 'BASE_VALUE COMPLEX_VALUE =
  BaseVal "'BASE_VALUE" |
  PairVal "'BASE_VALUE COMPLEX_VALUE" "'BASE_VALUE COMPLEX_VALUE" |
  SetVal "'BASE_VALUE COMPLEX_VALUE SET" |
  VoidVal

datatype 'BASE_TYPE COMPLEX_TYPE =
  BaseType "'BASE_TYPE" |
  PairType "'BASE_TYPE COMPLEX_TYPE" "'BASE_TYPE COMPLEX_TYPE" |
  SetType "'BASE_TYPE COMPLEX_TYPE" |
  VoidType

text {* Destructors *}

primrec BaseOf ::
  "'BASE_VALUE COMPLEX_VALUE \<Rightarrow> 'BASE_VALUE" where
"BaseOf (BaseVal v) = v"

primrec PairOf ::
  "'BASE_VALUE COMPLEX_VALUE \<Rightarrow>
   'BASE_VALUE COMPLEX_VALUE \<times>
   'BASE_VALUE COMPLEX_VALUE" where
"PairOf (PairVal v1 v2) = (v1, v2)"

primrec SetOf ::
  "'BASE_VALUE COMPLEX_VALUE \<Rightarrow>
   'BASE_VALUE COMPLEX_VALUE SET" where
"SetOf (SetVal s) = s"

text {* Testing Functions *}

primrec IsBaseVal ::
  "'BASE_VALUE COMPLEX_VALUE \<Rightarrow> bool" where
"IsBaseVal (BaseVal v) = True" |
"IsBaseVal (PairVal v1 v2) = False" |
"IsBaseVal (SetVal vs) = False" |
"IsBaseVal VoidVal = False"

primrec IsPairVal ::
  "'BASE_VALUE COMPLEX_VALUE \<Rightarrow> bool" where
"IsPairVal (BaseVal v) = False" |
"IsPairVal (PairVal v1 v2) = True" |
"IsPairVal (SetVal vs) = False" |
"IsPairVal VoidVal = False"

primrec IsSetVal ::
  "'BASE_VALUE COMPLEX_VALUE \<Rightarrow> bool" where
"IsSetVal (BaseVal v) = False" |
"IsSetVal (PairVal v1 v2) = False" |
"IsSetVal (SetVal vs) = True" |
"IsSetVal VoidVal = False"

text {* Abbreviations *}

abbreviation EncSetVal ::
  "'BASE_VALUE COMPLEX_VALUE set \<Rightarrow>
   'BASE_VALUE COMPLEX_VALUE" where
"EncSetVal vs \<equiv>
 if (IdxSet vs) then SetVal (EncSet vs) else VoidVal"

abbreviation DecSetOf ::
  "'BASE_VALUE COMPLEX_VALUE \<Rightarrow>
   'BASE_VALUE COMPLEX_VALUE set" where
"DecSetOf v \<equiv> DecSet (SetOf v)"

subsection {* Typing Relation *}

fun complex_type_rel ::
  "'BASE_VALUE COMPLEX_VALUE \<Rightarrow>
   'BASE_TYPE COMPLEX_TYPE \<Rightarrow> bool" where
"complex_type_rel (BaseVal v) (BaseType t) =
   (global_type_rel v t)" |
"complex_type_rel (PairVal v1 v2) (PairType t1 t2) \<longleftrightarrow>
   (complex_type_rel v1 t1) \<and>
   (complex_type_rel v2 t2)" |
"complex_type_rel (SetVal vs) (SetType t) =
   (\<forall> v \<in> DecSet(vs) . complex_type_rel v t)" |
"complex_type_rel VoidVal VoidType = True" |
"complex_type_rel _ _ = False"

defs default_type_rel [simp] :
"global_type_rel \<equiv> complex_type_rel"

subsection {* Sort Membership *}

instantiation COMPLEX_VALUE :: (BASIC_VALUE) COMPOSITE_VALUE
begin
primrec WellFormed_COMPLEX_VALUE ::
  "('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE \<Rightarrow> bool" where
"WellFormed_COMPLEX_VALUE (BaseVal v) = (WellFormed v)" |
"WellFormed_COMPLEX_VALUE (PairVal v1 v2) = True" |
"WellFormed_COMPLEX_VALUE (SetVal vs) = True" |
"WellFormed_COMPLEX_VALUE VoidVal = False"
definition MkInt_COMPLEX_VALUE ::
  "int \<Rightarrow> ('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE" where
"MkInt_COMPLEX_VALUE i = BaseVal (MkInt i)"
definition DestInt_COMPLEX_VALUE ::
  "('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE \<Rightarrow> int" where
"DestInt_COMPLEX_VALUE v = DestInt (BaseOf v)"
definition IsInt_COMPLEX_VALUE ::
  "('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE \<Rightarrow> bool" where
"IsInt_COMPLEX_VALUE v = ((IsBaseVal v) \<and> IsInt (BaseOf v))"
definition MkBool_COMPLEX_VALUE ::
  "bool \<Rightarrow> ('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE" where
"MkBool_COMPLEX_VALUE b = BaseVal (MkBool b)"
definition DestBool_COMPLEX_VALUE ::
  "('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE \<Rightarrow> bool" where
"DestBool_COMPLEX_VALUE v = DestBool (BaseOf v)"
definition IsBool_COMPLEX_VALUE ::
  "('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE \<Rightarrow> bool" where
"IsBool_COMPLEX_VALUE v = ((IsBaseVal v) \<and> IsBool (BaseOf v))"
definition MkStr_COMPLEX_VALUE ::
  "string \<Rightarrow> ('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE" where
"MkStr_COMPLEX_VALUE s = BaseVal (MkStr s)"
definition DestStr_COMPLEX_VALUE ::
  "('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE \<Rightarrow> string" where
"DestStr_COMPLEX_VALUE v = DestStr (BaseOf v)"
definition IsStr_COMPLEX_VALUE ::
  "('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE \<Rightarrow> bool" where
"IsStr_COMPLEX_VALUE v = ((IsBaseVal v) \<and> IsStr (BaseOf v))"
definition MkPair_COMPLEX_VALUE ::
  "('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE \<times>
   ('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE \<Rightarrow>
   ('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE" where
"MkPair_COMPLEX_VALUE v1_v2 = (uncurry PairVal) v1_v2"
definition DestPair_COMPLEX_VALUE ::
  "('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE \<Rightarrow>
   ('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE \<times>
   ('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE" where
"DestPair_COMPLEX_VALUE v = PairOf v"
definition IsPair_COMPLEX_VALUE ::
  "('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE \<Rightarrow> bool" where
"IsPair_COMPLEX_VALUE v = (IsPairVal v)"
definition MkSet_COMPLEX_VALUE ::
  "('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE set \<Rightarrow>
   ('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE" where
"MkSet_COMPLEX_VALUE vs = EncSetVal vs"
definition DestSet_COMPLEX_VALUE ::
  "('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE \<Rightarrow>
   ('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE set" where
"DestSet_COMPLEX_VALUE v = DecSetOf v"
definition IsSet_COMPLEX_VALUE ::
  "('BASE_VALUE :: BASIC_VALUE) COMPLEX_VALUE \<Rightarrow> bool" where
"IsSet_COMPLEX_VALUE v = (IsSetVal v)"
instance
apply (intro_classes)
apply (simp add: MkBool_COMPLEX_VALUE_def)
apply (simp add: MkBool_COMPLEX_VALUE_def DestBool_COMPLEX_VALUE_def)
apply (simp add: MkInt_COMPLEX_VALUE_def)
apply (simp add: MkInt_COMPLEX_VALUE_def DestInt_COMPLEX_VALUE_def)
apply (simp add: MkStr_COMPLEX_VALUE_def)
apply (simp add: MkStr_COMPLEX_VALUE_def DestStr_COMPLEX_VALUE_def)
apply (simp add: MkPair_COMPLEX_VALUE_def DestPair_COMPLEX_VALUE_def)
apply (simp add: uncurry_def)
apply (simp add: MkSet_COMPLEX_VALUE_def DestSet_COMPLEX_VALUE_def)
done
end

subsection {* Default Simplifications *}

declare WellFormed_COMPLEX_VALUE_def [simp]
declare MkInt_COMPLEX_VALUE_def [simp]
declare DestInt_COMPLEX_VALUE_def [simp]
declare IsInt_COMPLEX_VALUE_def [simp]
declare MkBool_COMPLEX_VALUE_def [simp]
declare DestBool_COMPLEX_VALUE_def [simp]
declare IsBool_COMPLEX_VALUE_def [simp]
declare MkStr_COMPLEX_VALUE_def [simp]
declare DestStr_COMPLEX_VALUE_def [simp]
declare IsStr_COMPLEX_VALUE_def [simp]
declare MkPair_COMPLEX_VALUE_def [simp]
declare DestPair_COMPLEX_VALUE_def [simp]
declare IsPair_COMPLEX_VALUE_def [simp]
declare MkSet_COMPLEX_VALUE_def [simp]
declare DestSet_COMPLEX_VALUE_def [simp]
declare IsSet_COMPLEX_VALUE_def [simp]

subsection {* Theorems *}

theorem complex_type_rel_VALUE [intro!] :
"VALUE (global_type_rel :: 'BASE_VALUE \<Rightarrow> 'BASE_TYPE \<Rightarrow> bool) \<Longrightarrow>
 VALUE (complex_type_rel ::
   'BASE_VALUE COMPLEX_VALUE \<Rightarrow> 'BASE_TYPE COMPLEX_TYPE \<Rightarrow> bool)"
apply (simp add: VALUE_def)
apply (clarify)
apply (induct_tac t)
apply (drule_tac x = "BASE_TYPE" in spec)
apply (safe)
apply (rule_tac x = "BaseVal x" in exI)
apply (simp)
apply (rule_tac x = "PairVal x xa" in exI)
apply (simp)
apply (rule_tac x = "EncSetVal {}" in exI)
apply (simp)
apply (rule_tac x = "VoidVal" in exI)
apply (simp)
done
end