theory utp_sorts
imports utp_base
begin

section {* Value Sorts *}

subsection {* Integer Values *}

class INT_SORT =
  fixes MkInt :: "int \<Rightarrow> 'a"
  fixes DestInt :: "'a \<Rightarrow> int"
  fixes IsInt :: "'a \<Rightarrow> bool"
  assumes inverse [simp] : "DestInt (MkInt i) = i"
begin

subsubsection {* Integer Operators *}

definition uminus :: "'a \<Rightarrow> 'a" where
"uminus i = MkInt (-DestInt(i))"
notation uminus ("-v _" [81] 80)

definition plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"plus i1 i2 = MkInt (DestInt(i1) + DestInt(i2))"
notation plus (infixl "+v" 65)

definition minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"minus i1 i2 = MkInt (DestInt(i1) - DestInt(i2))"
notation minus (infixl "-v" 65)

definition times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"times i1 i2 = MkInt (DestInt(i1) * DestInt(i2))"
notation times (infixl "*v" 70)

definition divide :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"divide i1 i2 = MkInt (DestInt(i1) div DestInt(i2))"
notation divide (infixl "DIV" 70)

definition modulus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"modulus i1 i2 = MkInt (DestInt(i1) mod DestInt(i2))"
notation modulus (infixl "MOD" 70)

subsubsection {* Default Simplifications *}

declare uminus_def [simp]
declare plus_def [simp]
declare minus_def [simp]
declare times_def [simp]
declare divide_def [simp]
declare modulus_def [simp]
end

subsection {* Boolean Values *}

class BOOL_SORT =
  fixes MkBool :: "bool \<Rightarrow> 'a"
  fixes DestBool :: "'a \<Rightarrow> bool"
  fixes IsBool :: "'a \<Rightarrow> bool"
  assumes inverse [simp] : "DestBool (MkBool b) = b"

subsection {* String Values *}

class STRING_SORT =
  fixes MkStr :: "string \<Rightarrow> 'a"
  fixes DestStr :: "'a \<Rightarrow> string"
  fixes IsStr :: "'a \<Rightarrow> bool"
  assumes inverse [simp] : "DestStr (MkStr s) = s"

subsection {* Pair Values *}

class PAIR_SORT =
  fixes MkPair :: "('a \<times> 'a) \<Rightarrow> 'a"
  fixes DestPair :: "'a \<Rightarrow> ('a \<times> 'a)"
  fixes IsPair :: "'a \<Rightarrow> bool"
  assumes inverse [simp] :
  "DestPair (MkPair v1_v2) = v1_v2"

subsection {* Set Values *}

class SET_SORT =
  fixes MkSet :: "'a set \<Rightarrow> 'a"
  fixes DestSet :: "'a \<Rightarrow> 'a set"
  fixes IsSet :: "'a \<Rightarrow> bool"
  assumes inverse [simp] :
  "IdxSet vs \<Longrightarrow> DestSet (MkSet vs) = vs"
begin

subsubsection {* Set Operators *}

definition union :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"union v1 v2 = MkSet ((DestSet v1) \<union> (DestSet v2))"
notation union (infixl "\<union>v" 65)

definition inter :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"inter v1 v2 = MkSet ((DestSet v1) \<inter> (DestSet v2))"
notation inter (infixl "\<inter>v" 70)

definition diff :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"diff v1 v2 = MkSet ((DestSet v1) - (DestSet v2))"
notation diff (infixl "\\v" 75)

definition member :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
"member v1 v2 = (v1 \<in> (DestSet v2))"
notation member ("(_/ \<in>v _)" [50, 51] 50)

definition not_member :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
"not_member v1 v2 = (v1 \<notin> (DestSet v2))"
notation not_member ("(_/ \<notin>v _)" [50, 51] 50)

definition subset :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
"subset v1 v2 = ((DestSet v1) \<subset> (DestSet v2))"
notation subset ("(_/ \<subset>v _)" [50, 51] 50)

definition subset_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
"subset_eq v1 v2 = ((DestSet v1) \<subseteq> (DestSet v2))"
notation subset_eq ("(_/ \<subseteq>v _)" [50, 51] 50)

subsection {* Default Simplifications *}

declare union_def [simp]
declare inter_def [simp]
declare member_def [simp]
declare not_member_def [simp]
declare subset_def [simp]
declare subset_eq_def [simp]
end

subsection {* Basic and Complex Values *}

class BASIC_SORT =
  INT_SORT + BOOL_SORT + STRING_SORT

class COMPLEX_SORT =
  BASIC_SORT + PAIR_SORT + SET_SORT

subsection {* Proof Experiments *}

text {* The inconvenience is that we need the typing information below. *}

theorem "MkInt(1) +v MkInt(2) = MkInt(3)"
apply (auto)
done

theorem "MkInt(1) \<in>v MkSet({MkInt(1), MkInt(2)})"
apply (simp)
done

theorem "MkInt(3) \<in>v MkSet({MkInt(1)}) \<union>v MkSet({MkInt(1) +v MkInt(2)})"
apply (simp)
done

theorem "IdxSet s1 \<and> IdxSet s2 \<longrightarrow> MkSet(s1) \<inter>v MkSet(s2) \<subseteq>v MkSet(s1)"
apply (simp)
done
end