theory utp_complex_value
imports "../utp_sorts" utp_abstract_value
begin

section {* Complex Values *}

subsection {* Data Types *}

text {*
  The @{text "SetVal"} constructor might need to know about the type of the set.
*}

datatype 'BASE_VALUE COMPLEX_VALUE =
  BaseVal "'BASE_VALUE" |
  PairVal "'BASE_VALUE COMPLEX_VALUE" "'BASE_VALUE COMPLEX_VALUE" |
  SetVal "'BASE_VALUE COMPLEX_VALUE SET"

datatype 'BASE_TYPE COMPLEX_TYPE =
  BaseType "'BASE_TYPE" |
  PairType "'BASE_TYPE COMPLEX_TYPE" "'BASE_TYPE COMPLEX_TYPE" |
  SetType "'BASE_TYPE COMPLEX_TYPE"

subsubsection {* Destructors *}

primrec BaseOf ::
  "'BASE_VALUE COMPLEX_VALUE \<Rightarrow> 'BASE_VALUE" where
"BaseOf (BaseVal v) = v"

primrec PairOf ::
  "'BASE_VALUE COMPLEX_VALUE \<Rightarrow>
  ('BASE_VALUE COMPLEX_VALUE \<times>
   'BASE_VALUE COMPLEX_VALUE)" where
"PairOf (PairVal v1 v2) = (v1, v2)"

primrec SetOf ::
  "'BASE_VALUE COMPLEX_VALUE \<Rightarrow>
   'BASE_VALUE COMPLEX_VALUE SET" where
"SetOf (SetVal s) = s"

primrec BaseTypeOf ::
  "'BASE_TYPE COMPLEX_TYPE \<Rightarrow> 'BASE_TYPE" where
"BaseTypeOf (BaseType t) = t"

primrec PairTypeOf ::
  "'BASE_TYPE COMPLEX_TYPE \<Rightarrow>
  ('BASE_TYPE COMPLEX_TYPE \<times>
   'BASE_TYPE COMPLEX_TYPE)" where
"PairTypeOf (PairType t1 t2) = (t1, t2)"

primrec SetTypeOf ::
  "'BASE_VALUE COMPLEX_TYPE \<Rightarrow>
   'BASE_VALUE COMPLEX_TYPE" where
"SetTypeOf (SetType t) = t"

subsubsection {* Abbreviations *}

abbreviation EncSetVal ::
  "'BASE_VALUE COMPLEX_VALUE set \<Rightarrow>
   'BASE_VALUE COMPLEX_VALUE" where
"EncSetVal vs \<equiv> SetVal(EncSet vs)"

abbreviation DecSetOf ::
  "'BASE_VALUE COMPLEX_VALUE \<Rightarrow>
   'BASE_VALUE COMPLEX_VALUE set" where
"DecSetOf v \<equiv> DecSet(SetOf v)"

subsection {* Sort Membership *}

instantiation COMPLEX_VALUE :: (BASIC_SORT) COMPLEX_SORT
begin
definition MkInt_COMPLEX_VALUE [simp] :
"MkInt_COMPLEX_VALUE i = BaseVal (MkInt i)"
definition DestInt_COMPLEX_VALUE [simp] :
"DestInt_COMPLEX_VALUE v = DestInt (BaseOf v)"
definition MkBool_COMPLEX_VALUE [simp] :
"MkBool_COMPLEX_VALUE b = BaseVal (MkBool b)"
definition DestBool_COMPLEX_VALUE [simp] :
"DestBool_COMPLEX_VALUE v = DestBool (BaseOf v)"
definition MkStr_COMPLEX_VALUE [simp] :
"MkStr_COMPLEX_VALUE s = BaseVal (MkStr s)"
definition DestStr_COMPLEX_VALUE [simp] :
"DestStr_COMPLEX_VALUE v = DestStr (BaseOf v)"
definition MkPair_COMPLEX_VALUE [simp] :
"MkPair_COMPLEX_VALUE v1_v2 = (uncurry PairVal) v1_v2"
definition DestPair_COMPLEX_VALUE [simp] :
"DestPair_COMPLEX_VALUE v = PairOf v"
definition PairInvC_COMPLEX_VALUE [simp] :
"PairInvC_COMPLEX_VALUE
   (v1_v2 :: 'a COMPLEX_VALUE \<times> 'a COMPLEX_VALUE) = True"
definition MkSet_COMPLEX_VALUE [simp] :
"MkSet_COMPLEX_VALUE vs = EncSetVal vs"
definition DestSet_COMPLEX_VALUE [simp] :
"DestSet_COMPLEX_VALUE v = DecSetOf v"
instance
apply (intro_classes)
apply (simp_all add: uncurry_def)
done
end

subsection {* Lifting Functors *}

fun lift_type_rel_complex ::
  "('BASE_VALUE \<Rightarrow> 'BASE_TYPE \<Rightarrow> bool) \<Rightarrow>
   ('BASE_VALUE COMPLEX_VALUE \<Rightarrow>
    'BASE_TYPE COMPLEX_TYPE \<Rightarrow> bool)"
  ("(_ \<bowtie> _ :/ _)" [50, 51] 50) where
"base \<bowtie> (BaseVal v) : (BaseType t) = (base v t)" |
"base \<bowtie> (BaseVal v) : (PairType t1 t2) = False" |
"base \<bowtie> (BaseVal v) : (SetType t) = False" |
"base \<bowtie> (PairVal v1 v2) : (BaseType t) = False" |
"base \<bowtie> (PairVal v1 v2) : (PairType t1 t2) = (
   (base \<bowtie> v1 : t1) \<and>
   (base \<bowtie> v2 : t2))" |
"base \<bowtie> (PairVal v1 v2) : (SetType t) = False" |
"base \<bowtie> (SetVal vs) : (BaseType t) = False" |
"base \<bowtie> (SetVal vs) : (PairType t1 t2) = False" |
"base \<bowtie> (SetVal vs) : (SetType t) =
   (\<forall> v \<in> DecSet(vs) . (base) \<bowtie> v : t)"

fun lift_value_ref_complex ::
  "('BASE_VALUE \<Rightarrow> 'BASE_VALUE \<Rightarrow> bool) \<Rightarrow>
   ('BASE_VALUE COMPLEX_VALUE \<Rightarrow>
    'BASE_VALUE COMPLEX_VALUE \<Rightarrow> bool)"
  ("(_ \<bowtie> _ \<sqsubseteq>/ _)" [50, 51] 50) where
"base \<bowtie> (BaseVal v) \<sqsubseteq> (BaseVal v') = (base v v')" |
"base \<bowtie> (BaseVal v) \<sqsubseteq> (PairVal v1' v2') = False" |
"base \<bowtie> (BaseVal v) \<sqsubseteq> (SetVal vs') = False" |
"base \<bowtie> (PairVal v1 v2) \<sqsubseteq> (BaseVal v') = False" |
"base \<bowtie> (PairVal v1 v2) \<sqsubseteq> (PairVal v1' v2') = (v1 = v1' \<and> v2 = v2')" |
"base \<bowtie> (PairVal v1 v2) \<sqsubseteq> (SetVal vs') = False" |
"base \<bowtie> (SetVal vs) \<sqsubseteq> (BaseVal v') = False" |
"base \<bowtie> (SetVal vs) \<sqsubseteq> (PairVal v1' v2') = False" |
"base \<bowtie> (SetVal vs) \<sqsubseteq> (SetVal vs') = (vs = vs')"

subsection {* Locale @{text "COMPLEX"} *}

locale COMPLEX_VALUE =
  VALUE "lift_type_rel_complex base_type_rel"
    "lift_value_ref_complex base_value_ref"
for base_type_rel :: "'BASE_VALUE :: BASIC_SORT \<Rightarrow> 'BASE_TYPE \<Rightarrow> bool" and
  base_value_ref :: "'BASE_VALUE :: BASIC_SORT \<Rightarrow> 'BASE_VALUE \<Rightarrow> bool"
begin

subsubsection {* Constructors *}

definition MkInt ::
  "int \<Rightarrow> 'BASE_VALUE COMPLEX_VALUE" where
"MkInt = INT_SORT_class.MkInt"

definition MkBool ::
  "bool \<Rightarrow> 'BASE_VALUE COMPLEX_VALUE" where
"MkBool = BOOL_SORT_class.MkBool"

definition MkStr ::
  "string \<Rightarrow> 'BASE_VALUE COMPLEX_VALUE" where
"MkStr = STRING_SORT_class.MkStr"

definition MkVal ::
  "'BASE_VALUE \<Rightarrow>
   'BASE_VALUE COMPLEX_VALUE" where
"MkVal = BaseVal"

definition MkPair ::
  "'BASE_VALUE COMPLEX_VALUE \<times>
   'BASE_VALUE COMPLEX_VALUE \<Rightarrow>
   'BASE_VALUE COMPLEX_VALUE" where
"MkPair = PAIR_SORT_class.MkPair"

definition MkSet ::
  "'BASE_VALUE COMPLEX_VALUE set \<Rightarrow>
   'BASE_VALUE COMPLEX_VALUE" where
"MkSet = SET_SORT_class.MkSet"

text {* Destructors *}

definition DestInt ::
  "'BASE_VALUE COMPLEX_VALUE \<Rightarrow> int" where
"DestInt = INT_SORT_class.DestInt"

definition DestBool ::
  "'BASE_VALUE COMPLEX_VALUE \<Rightarrow> bool" where
"DestBool = BOOL_SORT_class.DestBool"

definition DestStr ::
  "'BASE_VALUE COMPLEX_VALUE \<Rightarrow> string" where
"DestStr = STRING_SORT_class.DestStr"

definition DestVal ::
  "'BASE_VALUE COMPLEX_VALUE \<Rightarrow>
   'BASE_VALUE" where
"DestVal = BaseOf"

definition DestPair ::
  "'BASE_VALUE COMPLEX_VALUE \<Rightarrow>
  ('BASE_VALUE COMPLEX_VALUE \<times>
   'BASE_VALUE COMPLEX_VALUE)" where
"DestPair = PAIR_SORT_class.DestPair"

definition DestSet ::
  "'BASE_VALUE COMPLEX_VALUE \<Rightarrow>
   'BASE_VALUE COMPLEX_VALUE set" where
"DestSet = SET_SORT_class.DestSet"

subsubsection {* Default Simplificiations *}

declare MkInt_def [simp]
declare MkBool_def [simp]
declare MkStr_def [simp]
declare MkVal_def [simp]
declare MkPair_def [simp]
declare MkSet_def [simp]

declare DestInt_def [simp]
declare DestBool_def [simp]
declare DestStr_def [simp]
declare DestVal_def [simp]
declare DestPair_def [simp]
declare DestSet_def [simp]
end

subsection {* Theorems *}

theorem lift_type_rel_complex_VALUE [intro!] :
"\<lbrakk>VALUE base_type_rel\<rbrakk> \<Longrightarrow>
 VALUE (lift_type_rel_complex base_type_rel)"
apply (simp add: VALUE_def)
apply (clarify)
apply (induct_tac t)
apply (drule_tac x = "BASE_TYPE" in spec)
apply (safe)
apply (rule_tac x = "BaseVal x" in exI)
apply (simp)
apply (rule_tac x = "PairVal x xa" in exI)
apply (auto)
apply (rule_tac x = "EncSetVal {}" in exI)
apply (auto)
done

theorem COMPLEX_VALUE_inst [intro!] :
"VALUE base_type_rel \<Longrightarrow> COMPLEX_VALUE base_type_rel"
apply (simp add: COMPLEX_VALUE_def)
apply (auto)
done

subsection {* Proof Experiments *}

print_locale "COMPLEX_VALUE"
end
