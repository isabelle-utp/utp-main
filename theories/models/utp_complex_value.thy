(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_complex_value.thy                                                *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Complex Values *}

theory utp_complex_value
imports
  "../utp_common"
  "../utp_global"
  "../core/utp_sorts"
  "../core/utp_value"
  "../utils/utp_sets"
begin

subsection {* Value Model *}

text {* Does @{term "SetVal"} need to know about the type of the set? *}

datatype 'VALUE COMPLEX_VALUE =
  BaseVal "'VALUE" |
  PairVal "'VALUE COMPLEX_VALUE" "'VALUE COMPLEX_VALUE" |
  SetVal "'VALUE COMPLEX_VALUE SET" |
  VoidVal -- {* Use to encode undefined results. *}

datatype 'TYPE COMPLEX_TYPE =
  BaseType "'TYPE" |
  PairType "'TYPE COMPLEX_TYPE" "'TYPE COMPLEX_TYPE" |
  SetType "'TYPE COMPLEX_TYPE" |
  VoidType

type_synonym ('VALUE, 'TYPE) COMPLEX_TYPE_REL =
  "'VALUE COMPLEX_VALUE \<Rightarrow> 'TYPE COMPLEX_TYPE \<Rightarrow> bool"

text {* Destructors *}

primrec BaseOf ::
  "'VALUE COMPLEX_VALUE \<Rightarrow> 'VALUE" where
"BaseOf (BaseVal v) = v"

primrec PairOf ::
  "'VALUE COMPLEX_VALUE \<Rightarrow>
   'VALUE COMPLEX_VALUE \<times>
   'VALUE COMPLEX_VALUE" where
"PairOf (PairVal v1 v2) = (v1, v2)"

primrec SetOf ::
  "'VALUE COMPLEX_VALUE \<Rightarrow>
   'VALUE COMPLEX_VALUE SET" where
"SetOf (SetVal s) = s"

text {* Testing Functions *}

primrec IsBaseVal ::
  "'VALUE COMPLEX_VALUE \<Rightarrow> bool" where
"IsBaseVal (BaseVal v) = True" |
"IsBaseVal (PairVal v1 v2) = False" |
"IsBaseVal (SetVal vs) = False" |
"IsBaseVal VoidVal = False"

primrec IsPairVal ::
  "'VALUE COMPLEX_VALUE \<Rightarrow> bool" where
"IsPairVal (BaseVal v) = False" |
"IsPairVal (PairVal v1 v2) = True" |
"IsPairVal (SetVal vs) = False" |
"IsPairVal VoidVal = False"

primrec IsSetVal ::
  "'VALUE COMPLEX_VALUE \<Rightarrow> bool" where
"IsSetVal (BaseVal v) = False" |
"IsSetVal (PairVal v1 v2) = False" |
"IsSetVal (SetVal vs) = True" |
"IsSetVal VoidVal = False"

primrec IsVoidVal ::
  "'VALUE COMPLEX_VALUE \<Rightarrow> bool" where
"IsVoidVal (BaseVal v) = False" |
"IsVoidVal (PairVal v1 v2) = False" |
"IsVoidVal (SetVal vs) = False" |
"IsVoidVal VoidVal = True"

text {* Abbreviations *}

abbreviation EncSetVal ::
  "'VALUE COMPLEX_VALUE set \<Rightarrow>
   'VALUE COMPLEX_VALUE" where
"EncSetVal vs \<equiv>
 if (IdxSet vs) then SetVal (EncSet vs) else VoidVal"

abbreviation DecSetOf ::
  "'VALUE COMPLEX_VALUE \<Rightarrow>
   'VALUE COMPLEX_VALUE set" where
"DecSetOf v \<equiv> DecSet (SetOf v)"

subsection {* Well-formed Values *}

text {* A recursive definition here fails due to the termination proof. *}

inductive WellFormed ::
  "('VALUE :: VALUE_SORT) COMPLEX_VALUE \<Rightarrow> bool" where
"(Defined v) \<Longrightarrow> WellFormed (BaseVal v)" |
"(WellFormed v1) \<and>
 (WellFormed v2) \<Longrightarrow>
 WellFormed (PairVal v1 v2)" |
"(\<forall> v \<in> vs . WellFormed v) \<and> IdxSet vs \<Longrightarrow>
 WellFormed (EncSetVal vs)"

theorem WellFormed_VoidVal [simp] :
"\<not> WellFormed VoidVal"
apply (subst WellFormed.simps)
apply (auto)
done

subsection {* Typing Relation *}

fun complex_type_rel ::
  "('VALUE, 'TYPE) COMPLEX_TYPE_REL" where
"complex_type_rel (BaseVal v) (BaseType t) =
   (global_type_rel v t)" |
"complex_type_rel (PairVal v1 v2) (PairType t1 t2) \<longleftrightarrow>
   (complex_type_rel v1 t1) \<and>
   (complex_type_rel v2 t2)" |
"complex_type_rel (SetVal vs) (SetType t) =
   (\<forall> v \<in> DecSet(vs) . complex_type_rel v t)" |
"complex_type_rel VoidVal VoidType = True" |
"complex_type_rel _ _ = False"

defs global_complex_type_rel [simp] :
"global_type_rel \<equiv> complex_type_rel"

subsection {* Sort Membership *}

text {*
  The definedness notion we use in the instantiation below is weaker than
  the one of well-formedness via the inductive predicate @{const WellFormed}.
  It is nevertheless sufficient to discharge the axioms of the type class.
  The main reason for using it is that it simplifies proofs about values.
*}

instantiation COMPLEX_VALUE :: (BASIC_SORT) COMPOSITE_SORT
begin
fun Defined_COMPLEX_VALUE :: "'a COMPLEX_VALUE \<Rightarrow> bool" where
(* "Defined_COMPLEX_VALUE = WellFormed" *)
"Defined_COMPLEX_VALUE VoidVal = False" |
"Defined_COMPLEX_VALUE _ = True"
definition MkInt_COMPLEX_VALUE :: "int \<Rightarrow> 'a COMPLEX_VALUE" where
"MkInt_COMPLEX_VALUE i = BaseVal (MkInt i)"
definition DestInt_COMPLEX_VALUE :: "'a COMPLEX_VALUE \<Rightarrow> int" where
"DestInt_COMPLEX_VALUE v = DestInt (BaseOf v)"
definition IsInt_COMPLEX_VALUE :: "'a COMPLEX_VALUE \<Rightarrow> bool" where
"IsInt_COMPLEX_VALUE v = ((IsBaseVal v) \<and> IsInt (BaseOf v))"
definition MkBool_COMPLEX_VALUE :: "bool \<Rightarrow> 'a COMPLEX_VALUE" where
"MkBool_COMPLEX_VALUE b = BaseVal (MkBool b)"
definition DestBool_COMPLEX_VALUE :: "'a COMPLEX_VALUE \<Rightarrow> bool" where
"DestBool_COMPLEX_VALUE v = DestBool (BaseOf v)"
definition IsBool_COMPLEX_VALUE :: "'a COMPLEX_VALUE \<Rightarrow> bool" where
"IsBool_COMPLEX_VALUE v = ((IsBaseVal v) \<and> IsBool (BaseOf v))"
definition MkStr_COMPLEX_VALUE :: "string \<Rightarrow> 'a COMPLEX_VALUE" where
"MkStr_COMPLEX_VALUE s = BaseVal (MkStr s)"
definition DestStr_COMPLEX_VALUE :: "'a COMPLEX_VALUE \<Rightarrow> string" where
"DestStr_COMPLEX_VALUE v = DestStr (BaseOf v)"
definition IsStr_COMPLEX_VALUE :: "'a COMPLEX_VALUE \<Rightarrow> bool" where
"IsStr_COMPLEX_VALUE v = ((IsBaseVal v) \<and> IsStr (BaseOf v))"
definition MkReal_COMPLEX_VALUE :: "real \<Rightarrow> 'a COMPLEX_VALUE" where
"MkReal_COMPLEX_VALUE r = BaseVal (MkReal r)"
definition DestReal_COMPLEX_VALUE :: "'a COMPLEX_VALUE \<Rightarrow> real" where
"DestReal_COMPLEX_VALUE v = DestReal (BaseOf v)"
definition IsReal_COMPLEX_VALUE :: "'a COMPLEX_VALUE \<Rightarrow> bool" where
"IsReal_COMPLEX_VALUE v = ((IsBaseVal v) \<and> IsReal (BaseOf v))"
definition MkPair_COMPLEX_VALUE ::
  "'a COMPLEX_VALUE \<times> 'a COMPLEX_VALUE \<Rightarrow> 'a COMPLEX_VALUE" where
"MkPair_COMPLEX_VALUE v1_v2 = (uncurry PairVal) v1_v2"
definition DestPair_COMPLEX_VALUE ::
  "'a COMPLEX_VALUE \<Rightarrow> 'a COMPLEX_VALUE \<times> 'a COMPLEX_VALUE" where
"DestPair_COMPLEX_VALUE v = PairOf v"
definition IsPair_COMPLEX_VALUE :: "'a COMPLEX_VALUE \<Rightarrow> bool" where
"IsPair_COMPLEX_VALUE v = (IsPairVal v)"
definition MkSet_COMPLEX_VALUE ::
  "'a COMPLEX_VALUE set \<Rightarrow> 'a COMPLEX_VALUE" where
"MkSet_COMPLEX_VALUE vs = EncSetVal vs"
definition DestSet_COMPLEX_VALUE ::
  "'a COMPLEX_VALUE \<Rightarrow> 'a COMPLEX_VALUE set" where
"DestSet_COMPLEX_VALUE v = DecSetOf v"
definition IsSet_COMPLEX_VALUE :: "'a COMPLEX_VALUE \<Rightarrow> bool" where
"IsSet_COMPLEX_VALUE v = (IsSetVal v)"
instance
apply (intro_classes)
apply (simp add: MkBool_COMPLEX_VALUE_def)
apply (simp add: MkBool_COMPLEX_VALUE_def DestBool_COMPLEX_VALUE_def)
apply (simp add: MkInt_COMPLEX_VALUE_def)
apply (simp add: MkInt_COMPLEX_VALUE_def DestInt_COMPLEX_VALUE_def)
apply (simp add: MkReal_COMPLEX_VALUE_def)
apply (simp add: MkReal_COMPLEX_VALUE_def DestReal_COMPLEX_VALUE_def)
apply (simp add: MkStr_COMPLEX_VALUE_def)
apply (simp add: MkStr_COMPLEX_VALUE_def DestStr_COMPLEX_VALUE_def)
apply (simp add: MkPair_COMPLEX_VALUE_def DestPair_COMPLEX_VALUE_def)
apply (simp add: uncurry_def)
apply (simp add: MkSet_COMPLEX_VALUE_def DestSet_COMPLEX_VALUE_def)
done
end

subsection {* Default Simplifications *}

declare MkInt_COMPLEX_VALUE_def [simp]
declare DestInt_COMPLEX_VALUE_def [simp]
declare IsInt_COMPLEX_VALUE_def [simp]
declare MkBool_COMPLEX_VALUE_def [simp]
declare DestBool_COMPLEX_VALUE_def [simp]
declare IsBool_COMPLEX_VALUE_def [simp]
declare MkStr_COMPLEX_VALUE_def [simp]
declare DestStr_COMPLEX_VALUE_def [simp]
declare IsStr_COMPLEX_VALUE_def [simp]
declare MkReal_COMPLEX_VALUE_def [simp]
declare DestReal_COMPLEX_VALUE_def [simp]
declare IsReal_COMPLEX_VALUE_def [simp]
declare MkPair_COMPLEX_VALUE_def [simp]
declare DestPair_COMPLEX_VALUE_def [simp]
declare IsPair_COMPLEX_VALUE_def [simp]
declare MkSet_COMPLEX_VALUE_def [simp]
declare DestSet_COMPLEX_VALUE_def [simp]
declare IsSet_COMPLEX_VALUE_def [simp]

subsection {* Locale @{text "COMPLEX_VALUE"} *}

locale COMPLEX_VALUE =
  fixes basic_type_rel :: "'VALUE :: BASIC_SORT \<Rightarrow> 'TYPE \<Rightarrow> bool"
begin

text {* Constructors *}

definition MkInt ::
  "int \<Rightarrow> 'VALUE COMPLEX_VALUE" where
"MkInt = INT_SORT_class.MkInt"

definition MkBool ::
  "bool \<Rightarrow> 'VALUE COMPLEX_VALUE" where
"MkBool = BOOL_SORT_class.MkBool"

definition MkStr ::
  "string \<Rightarrow> 'VALUE COMPLEX_VALUE" where
"MkStr = STRING_SORT_class.MkStr"

definition MkReal ::
  "real \<Rightarrow> 'VALUE COMPLEX_VALUE" where
"MkReal = REAL_SORT_class.MkReal"

definition MkPair ::
  "'VALUE COMPLEX_VALUE \<times>
   'VALUE COMPLEX_VALUE \<Rightarrow>
   'VALUE COMPLEX_VALUE" where
"MkPair = PAIR_SORT_class.MkPair"

definition MkSet ::
  "'VALUE COMPLEX_VALUE set \<Rightarrow>
   'VALUE COMPLEX_VALUE" where
"MkSet = SET_SORT_class.MkSet"

text {* Destructors *}

definition DestInt ::
  "'VALUE COMPLEX_VALUE \<Rightarrow> int" where
"DestInt = INT_SORT_class.DestInt"

definition DestBool ::
  "'VALUE COMPLEX_VALUE \<Rightarrow> bool" where
"DestBool = BOOL_SORT_class.DestBool"

definition DestStr ::
  "'VALUE COMPLEX_VALUE \<Rightarrow> string" where
"DestStr = STRING_SORT_class.DestStr"

definition DestReal ::
  "'VALUE COMPLEX_VALUE \<Rightarrow> real" where
"DestReal = REAL_SORT_class.DestReal"

definition DestPair ::
  "'VALUE COMPLEX_VALUE \<Rightarrow>
   'VALUE COMPLEX_VALUE \<times>
   'VALUE COMPLEX_VALUE" where
"DestPair = PAIR_SORT_class.DestPair"

definition DestSet ::
  "'VALUE COMPLEX_VALUE \<Rightarrow>
   'VALUE COMPLEX_VALUE set" where
"DestSet = SET_SORT_class.DestSet"

text {* Testing Functions *}

definition IsInt ::
  "'VALUE COMPLEX_VALUE \<Rightarrow> bool" where
"IsInt = INT_SORT_class.IsInt"

definition IsBool ::
  "'VALUE COMPLEX_VALUE \<Rightarrow> bool" where
"IsBool = BOOL_SORT_class.IsBool"

definition IsStr ::
  "'VALUE COMPLEX_VALUE \<Rightarrow> bool" where
"IsStr = STRING_SORT_class.IsStr"

definition IsReal ::
  "'VALUE COMPLEX_VALUE \<Rightarrow> bool" where
"IsReal = REAL_SORT_class.IsReal"

definition IsPair ::
  "'VALUE COMPLEX_VALUE \<Rightarrow> bool" where
"IsPair = PAIR_SORT_class.IsPair"

definition IsSet ::
  "'VALUE COMPLEX_VALUE \<Rightarrow> bool" where
"IsSet = SET_SORT_class.IsSet"

text {* Default Simplifications *}

declare MkInt_def [simp]
declare MkBool_def [simp]
declare MkStr_def [simp]
declare MkReal_def [simp]
declare MkPair_def [simp]
declare MkSet_def [simp]

declare DestInt_def [simp]
declare DestBool_def [simp]
declare DestStr_def [simp]
declare DestReal_def [simp]
declare DestPair_def [simp]
declare DestSet_def [simp]

declare IsInt_def [simp]
declare IsBool_def [simp]
declare IsStr_def [simp]
declare IsReal_def [simp]
declare IsPair_def [simp]
declare IsSet_def [simp]
end

subsection {* Theorems *}

theorem complex_type_rel_VALUE [intro!] :
"VALUE (global_type_rel :: 'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool) \<Longrightarrow>
 VALUE (complex_type_rel :: ('VALUE, 'TYPE) COMPLEX_TYPE_REL)"
apply (simp add: VALUE_def)
apply (clarify)
apply (induct_tac t)
apply (rename_tac "t" "BASE_TYPE")
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
