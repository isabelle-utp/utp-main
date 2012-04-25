(******************************************************************************)
(* Title: utp/models/utp_ho2_value.thy                                        *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory utp_ho2_value
imports "../GLOBAL" "../utp_sorts" utp_ho1_pred
begin

section {* HO2 Values *}

subsection {* Program Values *}

typedef HO1_PREDICATE = HO1_PREDICATE
apply (rule_tac x = "FALSE" in exI)
apply (auto)
done

typedef HO1_ALPHABET = HO1_ALPHABET
apply (rule_tac x = "{}" in exI)
apply (auto)
done

subsection {* Data Types *}

types PROG1_VALUE = STD_PREDICATE
types PROG2_VALUE = HO1_PREDICATE

datatype HO2_VALUE =
  IntVal "int" |
  BoolVal "bool" |
  StringVal "string" |
  Prog1Val "PROG1_VALUE" |
  Prog2Val "PROG2_VALUE"

types PROG1_TYPE = STD_ALPHABET
types PROG2_TYPE = HO1_ALPHABET

datatype HO2_TYPE =
  IntType |
  BoolType |
  StringType |
  Prog1Type "PROG1_TYPE" |
  Prog2Type "PROG2_TYPE"

subsection {* Constructors *}

definition MkProg1 :: "PROG1_VALUE \<Rightarrow> HO2_VALUE" where
"MkProg1 = Prog1Val"

definition MkProg2 :: "PROG2_VALUE \<Rightarrow> HO2_VALUE" where
"MkProg2 = Prog2Val"

subsection {* Destructors *}

primrec DestProg1 :: "HO2_VALUE \<Rightarrow> PROG1_VALUE" where
"DestProg1 (Prog1Val p) = p"

primrec DestProg2 :: "HO2_VALUE \<Rightarrow> PROG2_VALUE" where
"DestProg2 (Prog2Val p) = p"

subsection {* Tests *}

primrec IsIntVal :: "HO2_VALUE \<Rightarrow> bool" where
"IsIntVal (IntVal _) = True" |
"IsIntVal (BoolVal _) = False" |
"IsIntVal (StringVal _) = False" |
"IsIntVal (Prog1Val _) = False" |
"IsIntVal (Prog2Val _) = False"

primrec IsBoolVal :: "HO2_VALUE \<Rightarrow> bool" where
"IsBoolVal (IntVal _) = False" |
"IsBoolVal (BoolVal _) = True" |
"IsBoolVal (StringVal _) = False" |
"IsBoolVal (Prog1Val _) = False" |
"IsBoolVal (Prog2Val _) = False"

primrec IsStringVal :: "HO2_VALUE \<Rightarrow> bool" where
"IsStringVal (IntVal _) = False" |
"IsStringVal (BoolVal _) = False" |
"IsStringVal (StringVal _) = True" |
"IsStringVal (Prog1Val _) = False" |
"IsStringVal (Prog2Val _) = False"

primrec IsProg1Val :: "HO2_VALUE \<Rightarrow> bool" where
"IsProg1Val (IntVal _) = False" |
"IsProg1Val (BoolVal _) = False" |
"IsProg1Val (StringVal _) = False" |
"IsProg1Val (Prog1Val _) = True" |
"IsProg1Val (Prog2Val _) = False"

primrec IsProg2Val :: "HO2_VALUE \<Rightarrow> bool" where
"IsProg2Val (IntVal _) = False" |
"IsProg2Val (BoolVal _) = False" |
"IsProg2Val (StringVal _) = False" |
"IsProg2Val (Prog1Val _) = False" |
"IsProg2Val (Prog2Val _) = True"

subsection {* Sort Membership *}

instantiation HO2_VALUE :: BASIC_SORT
begin
definition MkInt_HO2_VALUE :: "int \<Rightarrow> HO2_VALUE" where
"MkInt_HO2_VALUE i = IntVal i"
primrec DestInt_HO2_VALUE :: "HO2_VALUE \<Rightarrow> int" where
"DestInt_HO2_VALUE (IntVal i) = i"
definition IsInt_HO2_VALUE :: "HO2_VALUE \<Rightarrow> bool" where
"IsInt_HO2_VALUE = IsIntVal"
definition MkBool_HO2_VALUE :: "bool \<Rightarrow> HO2_VALUE" where
"MkBool_HO2_VALUE b = BoolVal b"
primrec DestBool_HO2_VALUE :: "HO2_VALUE \<Rightarrow> bool" where
"DestBool_HO2_VALUE (BoolVal b) = b"
definition IsBool_HO2_VALUE :: "HO2_VALUE \<Rightarrow> bool" where
"IsBool_HO2_VALUE = IsBoolVal"
definition MkStr_HO2_VALUE :: "string \<Rightarrow> HO2_VALUE" where
"MkStr_HO2_VALUE s = StringVal s"
primrec DestStr_HO2_VALUE :: "HO2_VALUE \<Rightarrow> string" where
"DestStr_HO2_VALUE (StringVal s) = s"
definition IsStr_HO2_VALUE :: "HO2_VALUE \<Rightarrow> bool" where
"IsStr_HO2_VALUE = IsStringVal"
instance
apply (intro_classes)
apply (simp add: MkBool_HO2_VALUE_def DestBool_HO2_VALUE_def)
apply (simp add: MkInt_HO2_VALUE_def DestInt_HO2_VALUE_def)
apply (simp add: MkStr_HO2_VALUE_def DestStr_HO2_VALUE_def)
done
end

subsection {* Typing and Refinement *}

fun ho2_type_rel :: "HO2_VALUE \<Rightarrow> HO2_TYPE \<Rightarrow> bool" where
"ho2_type_rel (IntVal _) IntType = True" |
"ho2_type_rel (BoolVal _) BoolType = True" |
"ho2_type_rel (StringVal _) StringType = True" |
"ho2_type_rel (Prog1Val p) (Prog1Type a) =
 (\<alpha> (Rep_STD_PREDICATE p) = (Rep_STD_ALPHABET a))" |
"ho2_type_rel (Prog2Val p) (Prog2Type a) =
 (\<alpha> (Rep_HO1_PREDICATE p) = (Rep_HO1_ALPHABET a))" |
"ho2_type_rel _ _ = False"

fun ho2_value_ref :: "HO2_VALUE \<Rightarrow> HO2_VALUE \<Rightarrow> bool" where
"ho2_value_ref (Prog1Val p1) (Prog1Val p2) =
 ((Rep_STD_PREDICATE p1) \<sqsubseteq>v (Rep_STD_PREDICATE p2))" |
"ho2_value_ref (Prog2Val p1) (Prog2Val p2) =
 ((Rep_HO1_PREDICATE p1) \<sqsubseteq>v (Rep_HO1_PREDICATE p2))" |
"ho2_value_ref v1 v2 = (v1 = v2)"
subsection {* Default Simplifications *}
subsection {* Default Simplifications *}

declare Abs_HO1_PREDICATE_inverse [simp]
declare Rep_HO1_PREDICATE_inverse [simp]
declare Abs_HO1_PREDICATE_inject [simp, intro!]
declare Rep_HO1_PREDICATE_inject [simp, intro!]
declare Rep_HO1_PREDICATE [simp]

declare Abs_HO1_ALPHABET_inverse [simp]
declare Rep_HO1_ALPHABET_inverse [simp]
declare Abs_HO1_ALPHABET_inject [simp, intro!]
declare Rep_HO1_ALPHABET_inject [simp, intro!]
declare Rep_HO1_ALPHABET [simp]

subsection {* Theorems *}

theorem VALUE_ho2_type_rel [simp] :
"VALUE ho2_type_rel"
apply (unfold_locales)
apply (induct_tac t)
apply (rule_tac x = "IntVal i" in exI)
apply (auto)
apply (rule_tac x = "BoolVal b" in exI)
apply (auto)
apply (rule_tac x = "StringVal s" in exI)
apply (auto)
apply (rule_tac x =
  "Prog1Val (Abs_STD_PREDICATE
    (STD.FalseP (Rep_STD_ALPHABET STD_ALPHABET)))" in exI)
apply (simp)
apply (subgoal_tac "Rep_STD_ALPHABET STD_ALPHABET \<in> STD.WF_ALPHABET")
apply (subst Abs_STD_PREDICATE_inverse)
apply (simp_all add: STD_PREDICATE_def)
apply (fold utp_std_pred.STD_ALPHABET)
apply (fold STD_ALPHABET_def, simp)
apply (rule_tac x =
  "Prog2Val (Abs_HO1_PREDICATE
     (HO1.FalseP (Rep_HO1_ALPHABET HO1_ALPHABET)))" in exI)
apply (simp)
apply (subgoal_tac "Rep_HO1_ALPHABET HO1_ALPHABET \<in> HO1.WF_ALPHABET")
apply (subst Abs_HO1_PREDICATE_inverse)
apply (simp_all add: HO1_PREDICATE_def)
apply (fold utp_ho1_pred.HO1_ALPHABET)
apply (fold HO1_ALPHABET_def, simp)
done
end
