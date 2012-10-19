(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_default_value.thy                                                *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Default Values *}

theory utp_default_value
imports
  "../utp_common"
  "../utp_global"
  "../core/utp_sorts"
  "../core/utp_value"
begin

subsection {* Value Model *}

datatype DEFAULT_VALUE =
  IntVal "int" |
  BoolVal "bool" |
  StrVal "string" |
  RealVal "real"

datatype DEFAULT_TYPE =
  IntType |
  BoolType |
  StringType |
  RealType

text {* Testing Functions *}

primrec IsIntVal :: "DEFAULT_VALUE \<Rightarrow> bool" where
"IsIntVal (IntVal _) = True" |
"IsIntVal (BoolVal _) = False" |
"IsIntVal (StrVal _) = False" |
"IsIntVal (RealVal _) = False"

primrec IsBoolVal :: "DEFAULT_VALUE \<Rightarrow> bool" where
"IsBoolVal (IntVal _) = False" |
"IsBoolVal (BoolVal _) = True" |
"IsBoolVal (StrVal _) = False" |
"IsBoolVal (RealVal _) = False"

primrec IsStrVal :: "DEFAULT_VALUE \<Rightarrow> bool" where
"IsStrVal (IntVal _) = False" |
"IsStrVal (BoolVal _) = False" |
"IsStrVal (StrVal _) = True" |
"IsStrVal (RealVal _) = False"

primrec IsRealVal :: "DEFAULT_VALUE \<Rightarrow> bool" where
"IsRealVal (IntVal _) = False" |
"IsRealVal (BoolVal _) = False" |
"IsRealVal (StrVal _) = False" |
"IsRealVal (RealVal _) = True"

subsection {* Typing Relation *}

fun default_type_rel ::
  "DEFAULT_VALUE \<Rightarrow> DEFAULT_TYPE \<Rightarrow> bool" where
"default_type_rel (IntVal _) IntType = True" |
"default_type_rel (IntVal _) BoolType = False" |
"default_type_rel (IntVal _) StringType = False" |
"default_type_rel (IntVal _) RealType = False" |
"default_type_rel (BoolVal _) IntType = False" |
"default_type_rel (BoolVal _) BoolType = True" |
"default_type_rel (BoolVal _) StringType = False" |
"default_type_rel (BoolVal _) RealType = False" |
"default_type_rel (StrVal _) IntType = False" |
"default_type_rel (StrVal _) BoolType = False" |
"default_type_rel (StrVal _) StringType = True" |
"default_type_rel (StrVal _) RealType = False" |
"default_type_rel (RealVal _) IntType = False" |
"default_type_rel (RealVal _) BoolType = False" |
"default_type_rel (RealVal _) StringType = False" |
"default_type_rel (RealVal _) RealType = True"

defs global_default_type_rel [simp] :
"global_type_rel \<equiv> default_type_rel"

subsection {* Sort Membership *}

instantiation DEFAULT_VALUE :: BASIC_SORT
begin
definition Defined_DEFAULT_VALUE :: "DEFAULT_VALUE \<Rightarrow> bool" where
"Defined_DEFAULT_VALUE v = True"
definition MkInt_DEFAULT_VALUE :: "int \<Rightarrow> DEFAULT_VALUE" where
"MkInt_DEFAULT_VALUE = IntVal"
primrec DestInt_DEFAULT_VALUE :: "DEFAULT_VALUE \<Rightarrow> int" where
"DestInt_DEFAULT_VALUE (IntVal i) = i"
definition IsInt_DEFAULT_VALUE :: "DEFAULT_VALUE \<Rightarrow> bool" where
"IsInt_DEFAULT_VALUE = IsIntVal"
definition MkBool_DEFAULT_VALUE :: "bool \<Rightarrow> DEFAULT_VALUE" where
"MkBool_DEFAULT_VALUE = BoolVal"
primrec DestBool_DEFAULT_VALUE :: "DEFAULT_VALUE \<Rightarrow> bool" where
"DestBool_DEFAULT_VALUE (BoolVal b) = b"
definition IsBool_DEFAULT_VALUE :: "DEFAULT_VALUE \<Rightarrow> bool" where
"IsBool_DEFAULT_VALUE = IsBoolVal"
definition MkStr_DEFAULT_VALUE :: "string \<Rightarrow> DEFAULT_VALUE" where
"MkStr_DEFAULT_VALUE = StrVal"
primrec DestStr_DEFAULT_VALUE:: "DEFAULT_VALUE \<Rightarrow> string" where
"DestStr_DEFAULT_VALUE (StrVal s) = s"
definition IsStr_DEFAULT_VALUE :: "DEFAULT_VALUE \<Rightarrow> bool" where
"IsStr_DEFAULT_VALUE = IsStrVal"
definition MkReal_DEFAULT_VALUE :: "real \<Rightarrow> DEFAULT_VALUE" where
"MkReal_DEFAULT_VALUE = RealVal"
primrec DestReal_DEFAULT_VALUE:: "DEFAULT_VALUE \<Rightarrow> real" where
"DestReal_DEFAULT_VALUE (RealVal s) = s"
definition IsReal_DEFAULT_VALUE :: "DEFAULT_VALUE \<Rightarrow> bool" where
"IsReal_DEFAULT_VALUE = IsRealVal"
instance
apply (intro_classes)
apply (simp_all add: Defined_DEFAULT_VALUE_def)
apply (simp add: MkBool_DEFAULT_VALUE_def DestBool_DEFAULT_VALUE_def)
apply (simp add: MkInt_DEFAULT_VALUE_def DestInt_DEFAULT_VALUE_def)
apply (simp add: MkReal_DEFAULT_VALUE_def DestReal_DEFAULT_VALUE_def)
apply (simp add: MkStr_DEFAULT_VALUE_def DestStr_DEFAULT_VALUE_def)
done
end

text {* Default Simplifications *}

declare Defined_DEFAULT_VALUE_def [simp]
declare MkInt_DEFAULT_VALUE_def [simp]
declare DestInt_DEFAULT_VALUE_def [simp]
declare IsInt_DEFAULT_VALUE_def [simp]
declare MkBool_DEFAULT_VALUE_def [simp]
declare DestBool_DEFAULT_VALUE_def [simp]
declare IsBool_DEFAULT_VALUE_def [simp]
declare MkStr_DEFAULT_VALUE_def [simp]
declare DestStr_DEFAULT_VALUE_def [simp]
declare IsStr_DEFAULT_VALUE_def [simp]
declare MkReal_DEFAULT_VALUE_def [simp]
declare DestReal_DEFAULT_VALUE_def [simp]
declare IsReal_DEFAULT_VALUE_def [simp]

subsection {* Theorems *}

theorem VALUE_default_type_rel [simp] :
"VALUE default_type_rel"
apply (unfold_locales)
apply (induct_tac t)
apply (rule_tac x = "IntVal i" in exI)
apply (auto)
apply (rule_tac x = "BoolVal b" in exI)
apply (auto)
apply (rule_tac x = "StrVal s" in exI)
apply (auto)
apply (rule_tac x = "RealVal r" in exI)
apply (auto)
done

subsection {* Proof Experiments *}

theorem "(IntVal 1) : IntType"
apply (auto)
done

theorem "((MkInt 1) :: DEFAULT_VALUE) : IntType"
apply (auto)
done
end
