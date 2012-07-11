(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/generic/utp_composite_value.thy                                  *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Composite Values *}

theory utp_composite_value
imports "../utp_sorts" utp_value
begin

subsection {* Type Definitions *}

text {* Does @{term "SetVal"} need to know about the type of the set? *}

datatype 'BASIC_VALUE COMPOSITE_VALUE =
  BasicVal "'BASIC_VALUE" |
  PairVal "'BASIC_VALUE COMPOSITE_VALUE" "'BASIC_VALUE COMPOSITE_VALUE" |
  SetVal "'BASIC_VALUE COMPOSITE_VALUE SET" |
  FunVal "('BASIC_VALUE COMPOSITE_VALUE \<times> 'BASIC_VALUE COMPOSITE_VALUE) SET"

datatype 'BASIC_TYPE COMPOSITE_TYPE =
  BasicType "'BASIC_TYPE" |
  PairType "'BASIC_TYPE COMPOSITE_TYPE" "'BASIC_TYPE COMPOSITE_TYPE" |
  SetType "'BASIC_TYPE COMPOSITE_TYPE" |
  FunType "'BASIC_TYPE COMPOSITE_TYPE" "'BASIC_TYPE COMPOSITE_TYPE"

text {* Destructors *}

primrec BasicOf ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow> 'BASIC_VALUE" where
"BasicOf (BasicVal v) = v"

primrec PairOf ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow>
  ('BASIC_VALUE COMPOSITE_VALUE \<times>
   'BASIC_VALUE COMPOSITE_VALUE)" where
"PairOf (PairVal v1 v2) = (v1, v2)"

primrec SetOf ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow>
   'BASIC_VALUE COMPOSITE_VALUE SET" where
"SetOf (SetVal s) = s"

primrec FunOf ::   
   "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow>
   ('BASIC_VALUE COMPOSITE_VALUE \<times>
    'BASIC_VALUE COMPOSITE_VALUE) SET" where
"FunOf (FunVal s) = s"

text {* Testing Functions *}

primrec IsBasicVal ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow> bool" where
"IsBasicVal (BasicVal v) = True" |
"IsBasicVal (PairVal v1 v2) = False" |
"IsBasicVal (SetVal s) = False" |
"IsBasicVal (FunVal f) = False"

primrec IsPairVal ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow> bool" where
"IsPairVal (BasicVal v) = False" |
"IsPairVal (PairVal v1 v2) = True" |
"IsPairVal (SetVal s) = False" |
"IsPairVal (FunVal f) = False"

primrec IsSetVal ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow> bool" where
"IsSetVal (BasicVal v) = False" |
"IsSetVal (PairVal v1 v2) = False" |
"IsSetVal (SetVal s) = True" |
"IsSetVal (FunVal s) = False"

primrec IsFunVal ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow> bool" where
"IsFunVal (BasicVal v) = False" |
"IsFunVal (PairVal v1 v2) = False" |
"IsFunVal (SetVal s) = False" |
"IsFunVal (FunVal f) = True"

text {* Abbreviations *}

abbreviation EncSetVal ::
  "'BASIC_VALUE COMPOSITE_VALUE set \<Rightarrow>
   'BASIC_VALUE COMPOSITE_VALUE" where
"EncSetVal vs \<equiv> SetVal (EncSet vs)"

abbreviation DecSetOf ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow>
   'BASIC_VALUE COMPOSITE_VALUE set" where
"DecSetOf v \<equiv> DecSet (SetOf v)"

abbreviation EncFunVal ::
  "('BASIC_VALUE COMPOSITE_VALUE \<Rightarrow> 'BASIC_VALUE COMPOSITE_VALUE) \<Rightarrow>
   'BASIC_VALUE COMPOSITE_VALUE" where
"EncFunVal f \<equiv> FunVal (EncSet {(x, f x) | x. x \<in> UNIV})"

abbreviation DecFunOf ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow>
   ('BASIC_VALUE COMPOSITE_VALUE \<Rightarrow> 'BASIC_VALUE COMPOSITE_VALUE)" where
"DecFunOf f \<equiv> \<lambda> x. THE y. (x, y) \<in> DecSet (FunOf f)"

subsection {* Typing and Refinement *}

fun lift_type_rel_composite ::
  "('BASIC_VALUE \<Rightarrow> 'BASIC_TYPE \<Rightarrow> bool) \<Rightarrow>
   ('BASIC_VALUE COMPOSITE_VALUE \<Rightarrow>
    'BASIC_TYPE COMPOSITE_TYPE \<Rightarrow> bool)"
  ("\<up>trel") where
"\<up>trel type_rel (BasicVal v) (BasicType t) =
   (type_rel v t)" |
"\<up>trel type_rel (PairVal v1 v2) (PairType t1 t2) = (
   (\<up>trel type_rel v1 t1) \<and>
   (\<up>trel type_rel v2 t2))" |
"\<up>trel type_rel (SetVal vs) (SetType t) =
   (\<forall> v \<in> DecSet(vs) . \<up>trel type_rel v t)" |
"\<up>trel type_rel (FunVal f) (FunType a b) =
   (\<forall> v \<in> DecSet(f) . \<up>trel type_rel (fst v) a 
                    \<and> \<up>trel type_rel (snd v) b)" |
"\<up>trel type_rel _ _ = False"

fun lift_value_ref_composite ::
  "('BASIC_VALUE \<Rightarrow> 'BASIC_VALUE \<Rightarrow> bool) \<Rightarrow>
   ('BASIC_VALUE COMPOSITE_VALUE \<Rightarrow>
    'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow> bool)"
  ("\<up>vref") where
"\<up>vref value_ref (BasicVal v) (BasicVal v') =
   (value_ref v v')" |
"\<up>vref value_ref (PairVal v1 v2) (PairVal v1' v2') =
   (v1 = v1' \<and> v2 = v2')" |
"\<up>vref value_ref (SetVal vs) (SetVal vs') = (vs = vs')" |
"\<up>vref value_ref (FunVal f) (FunVal f') = (f = f')" |
"\<up>vref value_ref _ _ = False"

subsection {* Sort Membership *}

instantiation COMPOSITE_VALUE :: (BASIC_SORT) COMPOSITE_SORT2
begin
definition ValueRef_COMPOSITE_VALUE :
"ValueRef_COMPOSITE_VALUE = \<up>vref VALUE_SORT_class.ValueRef"
definition MkInt_COMPOSITE_VALUE :
"MkInt_COMPOSITE_VALUE i = BasicVal (MkInt i)"
definition DestInt_COMPOSITE_VALUE :
"DestInt_COMPOSITE_VALUE v = DestInt (BasicOf v)"
definition IsInt_COMPOSITE_VALUE :
"IsInt_COMPOSITE_VALUE v = ((IsBasicVal v) \<and> IsInt (BasicOf v))"
definition MkBool_COMPOSITE_VALUE :
"MkBool_COMPOSITE_VALUE b = BasicVal (MkBool b)"
definition DestBool_COMPOSITE_VALUE :
"DestBool_COMPOSITE_VALUE v = DestBool (BasicOf v)"
definition IsBool_COMPOSITE_VALUE :
"IsBool_COMPOSITE_VALUE v = ((IsBasicVal v) \<and> IsBool (BasicOf v))"
definition MkStr_COMPOSITE_VALUE :
"MkStr_COMPOSITE_VALUE s = BasicVal (MkStr s)"
definition DestStr_COMPOSITE_VALUE :
"DestStr_COMPOSITE_VALUE v = DestStr (BasicOf v)"
definition IsStr_COMPOSITE_VALUE :
"IsStr_COMPOSITE_VALUE v = ((IsBasicVal v) \<and> IsStr (BasicOf v))"
definition MkPair_COMPOSITE_VALUE :
"MkPair_COMPOSITE_VALUE v1_v2 = (uncurry PairVal) v1_v2"
definition DestPair_COMPOSITE_VALUE :
"DestPair_COMPOSITE_VALUE v = PairOf v"
definition IsPair_COMPOSITE_VALUE :
"IsPair_COMPOSITE_VALUE v = (IsPairVal v)"
definition MkSet_COMPOSITE_VALUE :
"MkSet_COMPOSITE_VALUE vs = EncSetVal vs"
definition DestSet_COMPOSITE_VALUE :
"DestSet_COMPOSITE_VALUE v = DecSetOf v"
definition IsSet_COMPOSITE_VALUE :
"IsSet_COMPOSITE_VALUE v = (IsSetVal v)"
definition MkFunc_COMPOSITE_VALUE :
"MkFunc_COMPOSITE_VALUE f = EncFunVal f"
definition DestFunc_COMPOSITE_VALUE :
"DestFunc_COMPOSITE_VALUE f = DecFunOf f"
definition IsFunc_COMPOSITE_VALUE :
"IsFunc_COMPOSITE_VALUE f = (IsFunVal f)"
instance
apply (intro_classes)
done
end

subsection {* Default Simplifications *}

declare ValueRef_COMPOSITE_VALUE [simp]
declare MkInt_COMPOSITE_VALUE [simp]
declare DestInt_COMPOSITE_VALUE [simp]
declare IsInt_COMPOSITE_VALUE [simp]
declare MkBool_COMPOSITE_VALUE [simp]
declare DestBool_COMPOSITE_VALUE [simp]
declare IsBool_COMPOSITE_VALUE [simp]
declare MkStr_COMPOSITE_VALUE [simp]
declare DestStr_COMPOSITE_VALUE [simp]
declare IsStr_COMPOSITE_VALUE [simp]
declare MkPair_COMPOSITE_VALUE [simp]
declare DestPair_COMPOSITE_VALUE [simp]
declare IsPair_COMPOSITE_VALUE [simp]
declare MkSet_COMPOSITE_VALUE [simp]
declare DestSet_COMPOSITE_VALUE [simp]
declare IsSet_COMPOSITE_VALUE [simp]
declare MkFunc_COMPOSITE_VALUE [simp]
declare DestFunc_COMPOSITE_VALUE [simp]
declare IsFunc_COMPOSITE_VALUE [simp]

subsection {* Locale @{text "COMPOSITE_VALUE"} *}

locale COMPOSITE_VALUE =
  VALUE "\<up>trel basic_type_rel"
for basic_type_rel :: "'BASIC_VALUE :: BASIC_SORT \<Rightarrow> 'BASIC_TYPE \<Rightarrow> bool"
begin

text {* Constructors *}

definition MkInt ::
  "int \<Rightarrow> 'BASIC_VALUE COMPOSITE_VALUE" where
"MkInt = INT_SORT_class.MkInt"

definition MkBool ::
  "bool \<Rightarrow> 'BASIC_VALUE COMPOSITE_VALUE" where
"MkBool = BOOL_SORT_class.MkBool"

definition MkStr ::
  "string \<Rightarrow> 'BASIC_VALUE COMPOSITE_VALUE" where
"MkStr = STRING_SORT_class.MkStr"

definition MkPair ::
  "'BASIC_VALUE COMPOSITE_VALUE \<times>
   'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow>
   'BASIC_VALUE COMPOSITE_VALUE" where
"MkPair = PAIR_SORT_class.MkPair"

definition MkSet ::
  "'BASIC_VALUE COMPOSITE_VALUE set \<Rightarrow>
   'BASIC_VALUE COMPOSITE_VALUE" where
"MkSet = SET_SORT_class.MkSet"

definition MkFun ::
  "('BASIC_VALUE COMPOSITE_VALUE \<Rightarrow> 'BASIC_VALUE COMPOSITE_VALUE) \<Rightarrow>
   'BASIC_VALUE COMPOSITE_VALUE" where
"MkFun = FUNCTION_SORT_class.MkFunc"

text {* Destructors *}

definition DestInt ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow> int" where
"DestInt = INT_SORT_class.DestInt"

definition DestBool ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow> bool" where
"DestBool = BOOL_SORT_class.DestBool"

definition DestStr ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow> string" where
"DestStr = STRING_SORT_class.DestStr"

definition DestPair ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow>
  ('BASIC_VALUE COMPOSITE_VALUE \<times>
   'BASIC_VALUE COMPOSITE_VALUE)" where
"DestPair = PAIR_SORT_class.DestPair"

definition DestSet ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow>
   'BASIC_VALUE COMPOSITE_VALUE set" where
"DestSet = SET_SORT_class.DestSet"

definition DestFun ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow>
   ('BASIC_VALUE COMPOSITE_VALUE \<Rightarrow> 'BASIC_VALUE COMPOSITE_VALUE)" where
"DestFun = FUNCTION_SORT_class.DestFunc"

text {* Testing Functions *}

definition IsInt ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow> bool" where
"IsInt = INT_SORT_class.IsInt"

definition IsBool ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow> bool" where
"IsBool = BOOL_SORT_class.IsBool"

definition IsStr ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow> bool" where
"IsStr = STRING_SORT_class.IsStr"

definition IsPair ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow> bool" where
"IsPair = PAIR_SORT_class.IsPair"

definition IsSet ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow> bool" where
"IsSet = SET_SORT_class.IsSet"

definition IsFun ::
  "'BASIC_VALUE COMPOSITE_VALUE \<Rightarrow> bool" where
"IsFun = FUNCTION_SORT_class.IsFunc"

text {* Default Simplifications *}

declare MkInt_def [simp]
declare MkBool_def [simp]
declare MkStr_def [simp]
declare MkPair_def [simp]
declare MkSet_def [simp]
declare MkFun_def [simp]

declare DestInt_def [simp]
declare DestBool_def [simp]
declare DestStr_def [simp]
declare DestPair_def [simp]
declare DestSet_def [simp]
declare DestFun_def [simp]

declare IsInt_def [simp]
declare IsBool_def [simp]
declare IsStr_def [simp]
declare IsPair_def [simp]
declare IsSet_def [simp]
declare IsFun_def [simp]
end

subsection {* Theorems *}

theorem lift_type_rel_composite_VALUE [intro!] :
"VALUE type_rel \<Longrightarrow> VALUE (\<up>trel type_rel)"
apply (simp add: VALUE_def)
apply (clarify)
apply (induct_tac t)
apply (drule_tac x = "BASIC_TYPE" in spec)
apply (safe)
apply (rule_tac x = "BasicVal x" in exI)
apply (simp)
apply (rule_tac x = "PairVal x xa" in exI)
apply (force)
apply (rule_tac x = "EncSetVal {}" in exI)
apply (force)
apply (rule_tac x = "EncFunVal id" in exI)
apply (auto)
(* The proof about functions doesn't go through yet *)
sorry

text {* The following theorem facilitates locale instantiation. *}

theorem VALUE_COMPOSITE_VALUE_inst [intro!] :
"VALUE type_rel \<Longrightarrow> COMPOSITE_VALUE type_rel"
apply (simp add: COMPOSITE_VALUE_def)
apply (auto)
done
end
