(******************************************************************************)
(* Title: utp/models/utp_ho1_value.thy                                        *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory utp_ho1_value
imports "../GLOBAL" "../utp_sorts" utp_std_pred
begin

section {* HO1 Values *}

subsection {* Program Values *}

typedef STD_PREDICATE = STD_PREDICATE
apply (rule_tac x = "FALSE" in exI)
apply (auto)
done

typedef STD_ALPHABET = STD_ALPHABET
apply (rule_tac x = "{}" in exI)
apply (auto)
done

subsection {* Data Types *}

types PROG_VALUE = STD_PREDICATE

datatype HO1_VALUE =
  IntVal "int" |
  BoolVal "bool" |
  StringVal "string" |
  ProgVal "PROG_VALUE"

types PROG_TYPE = STD_ALPHABET

datatype HO1_TYPE =
  IntType |
  BoolType |
  StringType |
  ProgType "PROG_TYPE"

subsection {* Constructors *}

definition MkProg :: "PROG_VALUE \<Rightarrow> HO1_VALUE" where
"MkProg = ProgVal"

subsection {* Destructors *}

primrec DestProg :: "HO1_VALUE \<Rightarrow> PROG_VALUE" where
"DestProg (ProgVal p) = p"

subsection {* Tests *}

primrec IsIntVal :: "HO1_VALUE \<Rightarrow> bool" where
"IsIntVal (IntVal _) = True" |
"IsIntVal (BoolVal _) = False" |
"IsIntVal (StringVal _) = False" |
"IsIntVal (ProgVal _) = False"

primrec IsBoolVal :: "HO1_VALUE \<Rightarrow> bool" where
"IsBoolVal (IntVal _) = False" |
"IsBoolVal (BoolVal _) = True" |
"IsBoolVal (StringVal _) = False" |
"IsBoolVal (ProgVal _) = False"

primrec IsStringVal :: "HO1_VALUE \<Rightarrow> bool" where
"IsStringVal (IntVal _) = False" |
"IsStringVal (BoolVal _) = False" |
"IsStringVal (StringVal _) = True" |
"IsStringVal (ProgVal _) = False"

primrec IsProgVal :: "HO1_VALUE \<Rightarrow> bool" where
"IsProgVal (IntVal _) = False" |
"IsProgVal (BoolVal _) = False" |
"IsProgVal (StringVal _) = False" |
"IsProgVal (ProgVal _) = True"

subsection {* Sort Membership *}

instantiation HO1_VALUE :: BASIC_SORT
begin
definition MkInt_HO1_VALUE :: "int \<Rightarrow> HO1_VALUE" where
"MkInt_HO1_VALUE i = IntVal i"
primrec DestInt_HO1_VALUE :: "HO1_VALUE \<Rightarrow> int" where
"DestInt_HO1_VALUE (IntVal i) = i"
definition IsInt_HO1_VALUE :: "HO1_VALUE \<Rightarrow> bool" where
"IsInt_HO1_VALUE = IsIntVal"
definition MkBool_HO1_VALUE :: "bool \<Rightarrow> HO1_VALUE" where
"MkBool_HO1_VALUE b = BoolVal b"
primrec DestBool_HO1_VALUE :: "HO1_VALUE \<Rightarrow> bool" where
"DestBool_HO1_VALUE (BoolVal b) = b"
definition IsBool_HO1_VALUE :: "HO1_VALUE \<Rightarrow> bool" where
"IsBool_HO1_VALUE = IsBoolVal"
definition MkStr_HO1_VALUE :: "string \<Rightarrow> HO1_VALUE" where
"MkStr_HO1_VALUE s = StringVal s"
primrec DestStr_HO1_VALUE :: "HO1_VALUE \<Rightarrow> string" where
"DestStr_HO1_VALUE (StringVal s) = s"
definition IsStr_HO1_VALUE :: "HO1_VALUE \<Rightarrow> bool" where
"IsStr_HO1_VALUE = IsStringVal"
instance
apply (intro_classes)
apply (simp add: MkBool_HO1_VALUE_def DestBool_HO1_VALUE_def)
apply (simp add: MkInt_HO1_VALUE_def DestInt_HO1_VALUE_def)
apply (simp add: MkStr_HO1_VALUE_def DestStr_HO1_VALUE_def)
done
end

subsection {* Typing and Refinement *}

fun ho1_type_rel :: "HO1_VALUE \<Rightarrow> HO1_TYPE \<Rightarrow> bool" where
"ho1_type_rel (IntVal _) IntType = True" |
"ho1_type_rel (BoolVal _) BoolType = True" |
"ho1_type_rel (StringVal _) StringType = True" |
"ho1_type_rel (ProgVal p) (ProgType a) =
 (\<alpha> (Rep_STD_PREDICATE p) = (Rep_STD_ALPHABET a))" |
"ho1_type_rel _ _ = False"

fun ho1_value_ref :: "HO1_VALUE \<Rightarrow> HO1_VALUE \<Rightarrow> bool" where
"ho1_value_ref (ProgVal p1) (ProgVal p2) =
 ((Rep_STD_PREDICATE p1) \<sqsubseteq>v (Rep_STD_PREDICATE p2))" |
"ho1_value_ref v1 v2 = (v1 = v2)"

subsection {* Default Simplifications *}

declare Abs_STD_PREDICATE_inverse [simp]
declare Rep_STD_PREDICATE_inverse [simp]
declare Abs_STD_PREDICATE_inject [simp, intro!]
declare Rep_STD_PREDICATE_inject [simp, intro!]
declare Rep_STD_PREDICATE [simp]

declare Abs_STD_ALPHABET_inverse [simp]
declare Rep_STD_ALPHABET_inverse [simp]
declare Abs_STD_ALPHABET_inject [simp, intro!]
declare Rep_STD_ALPHABET_inject [simp, intro!]
declare Rep_STD_ALPHABET [simp]

subsection {* Theorems *}

theorem VALUE_ho1_type_rel [simp] :
"VALUE ho1_type_rel"
apply (unfold_locales)
apply (induct_tac t)
apply (rule_tac x = "IntVal i" in exI)
apply (auto)
apply (rule_tac x = "BoolVal b" in exI)
apply (auto)
apply (rule_tac x = "StringVal s" in exI)
apply (auto)
apply (rule_tac x =
  "ProgVal (Abs_STD_PREDICATE
     (STD.FalseP (Rep_STD_ALPHABET STD_ALPHABET)))" in exI)
apply (simp)
apply (subgoal_tac "Rep_STD_ALPHABET STD_ALPHABET \<in> STD.WF_ALPHABET")
apply (subst Abs_STD_PREDICATE_inverse)
apply (simp_all add: STD_PREDICATE_def)
apply (fold utp_std_pred.STD_ALPHABET)
apply (fold STD_ALPHABET_def, simp)
done
end
