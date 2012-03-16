theory utp_default_values
imports "../utp_base" "../utp_sorts" "../generic/utp_gen_value"
begin

section {* Default Values *}

text {*
  Note that we do not interpret any value locale here. This is done as part of
  interpreting the predicate model. One reason is that the same locale can only
  be interpreted once with the same set of constants.
*}

subsection {* Data Types *}

datatype DEFAULT_VALUE =
  IntVal "int" |
  BoolVal "bool" |
  StringVal "string"

datatype DEFAULT_TYPE =
  IntType |
  BoolType |
  StringType

subsection {* Sort Membership *}

instantiation DEFAULT_VALUE :: BASIC_SORT
begin
definition MkInt_DEFAULT_VALUE :: "int \<Rightarrow> DEFAULT_VALUE" where
"MkInt_DEFAULT_VALUE i = IntVal i"
primrec DestInt_DEFAULT_VALUE :: "DEFAULT_VALUE \<Rightarrow> int" where
"DestInt_DEFAULT_VALUE (IntVal i) = i"
definition MkBool_DEFAULT_VALUE :: "bool \<Rightarrow> DEFAULT_VALUE" where
"MkBool_DEFAULT_VALUE b = BoolVal b"
primrec DestBool_DEFAULT_VALUE :: "DEFAULT_VALUE \<Rightarrow> bool" where
"DestBool_DEFAULT_VALUE (BoolVal b) = b"
definition MkStr_DEFAULT_VALUE :: "string \<Rightarrow> DEFAULT_VALUE" where
"MkStr_DEFAULT_VALUE s = StringVal s"
primrec DestStr_DEFAULT_VALUE:: "DEFAULT_VALUE \<Rightarrow> string" where
"DestStr_DEFAULT_VALUE (StringVal s) = s"
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
"(IntVal i) : IntType = True" |
"(IntVal i) : BoolType = False" |
"(IntVal i) : StringType = False" |
"(BoolVal i) : IntType = False" |
"(BoolVal i) : BoolType = True" |
"(BoolVal i) : StringType = False" |
"(StringVal i) : IntType = False" |
"(StringVal i) : BoolType = False" |
"(StringVal i) : StringType = True"

no_notation default_type_rel (infix ":" 50)

text {* The refinement ordering for default values is flat. *}

definition default_value_ref ::
  "DEFAULT_VALUE \<Rightarrow> DEFAULT_VALUE \<Rightarrow> bool" where
"default_value_ref v1 v2 \<longleftrightarrow> (v1 = v2)"

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