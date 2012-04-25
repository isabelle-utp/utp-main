(******************************************************************************)
(* Title: utp/models/utp_default_value.thy                                    *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory utp_default_value
imports "../utp_common" "../utp_sorts" "../generic/utp_abstract_value"
begin

section {* Default Values *}

subsection {* Data Types *}

datatype DEFAULT_VALUE =
  IntVal "int" |
  BoolVal "bool" |
  StringVal "string"

datatype DEFAULT_TYPE =
  IntType |
  BoolType |
  StringType

subsection {* Tests *}

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

subsection {* Sort Membership *}

instantiation DEFAULT_VALUE :: BASIC_SORT
begin
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
definition IsString_DEFAULT_VALUE :: "DEFAULT_VALUE \<Rightarrow> bool" where
"IsString_DEFAULT_VALUE = IsStringVal"
instance
apply (intro_classes)
apply (simp add: MkBool_DEFAULT_VALUE_def DestBool_DEFAULT_VALUE_def)
apply (simp add: MkInt_DEFAULT_VALUE_def DestInt_DEFAULT_VALUE_def)
apply (simp add: MkStr_DEFAULT_VALUE_def DestStr_DEFAULT_VALUE_def)
done
end

subsection {* Typing and Refinement *}

fun default_type_rel ::
  "DEFAULT_VALUE \<Rightarrow> DEFAULT_TYPE \<Rightarrow> bool" (infix ":" 50) where
"(IntVal _) : IntType = True" |
"(IntVal _) : BoolType = False" |
"(IntVal _) : StringType = False" |
"(BoolVal _) : IntType = False" |
"(BoolVal _) : BoolType = True" |
"(BoolVal _) : StringType = False" |
"(StringVal _) : IntType = False" |
"(StringVal _) : BoolType = False" |
"(StringVal _) : StringType = True"

no_notation default_type_rel (infix ":" 50)

text {* The refinement order of default values is flat. *}

definition default_value_ref ::
  "DEFAULT_VALUE \<Rightarrow> DEFAULT_VALUE \<Rightarrow> bool"  (infix "\<sqsubseteq>v" 50) where
"v1 \<sqsubseteq>v v2 \<longleftrightarrow> (v1 = v2)"

no_notation default_type_rel (infix "\<sqsubseteq>v" 50)

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
end