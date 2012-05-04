(******************************************************************************)
(* Title: utp/models/utp_default_value.thy                                    *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory utp_default_value
imports "../GLOBAL" "../utp_common" "../utp_sorts" "../generic/utp_abstract_value"
begin

section {* Default Values *}

subsection {* Value Encoding *}

datatype DEFAULT_VALUE =
  IntVal "int" |
  BoolVal "bool" |
  StringVal "string"

datatype DEFAULT_TYPE =
  IntType |
  BoolType |
  StringType

subsubsection {* Tests *}

primrec IsIntVal :: "DEFAULT_VALUE \<Rightarrow> bool" where
"IsIntVal (IntVal _) = True" |
"IsIntVal (BoolVal _) = False" |
"IsIntVal (StringVal _) = False"

primrec IsBoolVal :: "DEFAULT_VALUE \<Rightarrow> bool" where
"IsBoolVal (IntVal _) = False" |
"IsBoolVal (BoolVal _) = True" |
"IsBoolVal (StringVal _) = False"

primrec IsStringVal :: "DEFAULT_VALUE \<Rightarrow> bool" where
"IsStringVal (IntVal _) = False" |
"IsStringVal (BoolVal _) = False" |
"IsStringVal (StringVal _) = True"

subsection {* Typing and Refinement *}

fun default_type_rel :: "DEFAULT_VALUE \<Rightarrow> DEFAULT_TYPE \<Rightarrow> bool"  where
"default_type_rel (IntVal _) IntType = True" |
"default_type_rel (IntVal _) BoolType = False" |
"default_type_rel (IntVal _) StringType = False" |
"default_type_rel (BoolVal _) IntType = False" |
"default_type_rel (BoolVal _) BoolType = True" |
"default_type_rel (BoolVal _) StringType = False" |
"default_type_rel (StringVal _) IntType = False" |
"default_type_rel (StringVal _) BoolType = False" |
"default_type_rel (StringVal _) StringType = True"

defs default_type_rel [simp] :
"GLOBAL.type_rel \<equiv> default_type_rel"

text {* The refinement ordering for basic values is flat. *}

definition default_value_ref ::
  "DEFAULT_VALUE \<Rightarrow> DEFAULT_VALUE \<Rightarrow> bool"  where
"default_value_ref v1 v2 = (v1 = v2)"

declare  default_value_ref_def [simp]

subsection {* Sort Membership *}

instantiation DEFAULT_VALUE :: BASIC_SORT
begin
definition ValueRef_DEFAULT_VALUE ::
  "DEFAULT_VALUE \<Rightarrow> DEFAULT_VALUE \<Rightarrow> bool" where
"ValueRef_DEFAULT_VALUE = default_value_ref"
definition MkInt_DEFAULT_VALUE :: "int \<Rightarrow> DEFAULT_VALUE" where
"MkInt_DEFAULT_VALUE i = IntVal i"
primrec DestInt_DEFAULT_VALUE :: "DEFAULT_VALUE \<Rightarrow> int" where
"DestInt_DEFAULT_VALUE (IntVal i) = i"
definition IsInt_DEFAULT_VALUE :: "DEFAULT_VALUE \<Rightarrow> bool" where
"IsInt_DEFAULT_VALUE = IsIntVal"
definition MkBool_DEFAULT_VALUE :: "bool \<Rightarrow> DEFAULT_VALUE" where
"MkBool_DEFAULT_VALUE b = BoolVal b"
primrec DestBool_DEFAULT_VALUE :: "DEFAULT_VALUE \<Rightarrow> bool" where
"DestBool_DEFAULT_VALUE (BoolVal b) = b"
definition IsBool_DEFAULT_VALUE :: "DEFAULT_VALUE \<Rightarrow> bool" where
"IsBool_DEFAULT_VALUE = IsBoolVal"
definition MkStr_DEFAULT_VALUE :: "string \<Rightarrow> DEFAULT_VALUE" where
"MkStr_DEFAULT_VALUE s = StringVal s"
primrec DestStr_DEFAULT_VALUE:: "DEFAULT_VALUE \<Rightarrow> string" where
"DestStr_DEFAULT_VALUE (StringVal s) = s"
definition IsStr_DEFAULT_VALUE :: "DEFAULT_VALUE \<Rightarrow> bool" where
"IsStr_DEFAULT_VALUE = IsStringVal"
instance
apply (intro_classes)
done
end

subsubsection {* Default Simplifications *}

declare ValueRef_DEFAULT_VALUE_def [simp]
declare MkInt_DEFAULT_VALUE_def [simp]
declare DestInt_DEFAULT_VALUE_def [simp]
declare IsInt_DEFAULT_VALUE_def [simp]
declare MkBool_DEFAULT_VALUE_def [simp]
declare DestBool_DEFAULT_VALUE_def [simp]
declare IsBool_DEFAULT_VALUE_def [simp]
declare MkStr_DEFAULT_VALUE_def [simp]
declare DestStr_DEFAULT_VALUE_def [simp]
declare IsStr_DEFAULT_VALUE_def [simp]

subsection {* Theorems *}

theorem VALUE_default_type_rel [simp] :
"VALUE default_type_rel"
apply (unfold_locales)
apply (induct_tac t)
apply (rule_tac x = "IntVal i" in exI)
apply (auto)
apply (rule_tac x = "BoolVal b" in exI)
apply (auto)
apply (rule_tac x = "StringVal s" in exI)
apply (auto)
done

subsection {* Proof Experiments *}

theorem "(IntVal 1) : IntType"
apply (auto)
done

theorem "(IntVal 1) \<sqsubseteq>v (IntVal 1)"
apply (auto)
done

theorem "((MkInt 1) :: DEFAULT_VALUE) : IntType"
apply (auto)
done
end
