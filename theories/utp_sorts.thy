(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/utp_sorts.thy                                                    *)
(* Authors: Frank Zeyda and Simon Foster, University of York                  *)
(******************************************************************************)

header {* Value Sorts *}

theory utp_sorts
imports utp_common
begin

text {* Some of the sorts still need to be developed in terms of their operators. *}

text {*
  I decided for the time being to give up on the @{text "inverse"} theorems.
  Their motivation was initially to support proofs about operators within the
  type classes but it turns out that in particular in mechanising HO values,
  they become a liability to discharge upon instantiation. For instance, our
  current higher-order value model does not retain enough information in order
  to reverse the construction of arbitrarily nested values.
*}

subsection {* Value Sort *}

text {*
  It would be neat to introduce typing in @{text "VALUE_SORT"}, too, but this
  is not possible because it would require a second HOL type parameter in the
  respective fixed constant, namely for the underlying value type. Our design
  thus opted for introducing typing by virtue of a locale @{text "VALUE"}.
*}

class VALUE_SORT =
  fixes ValueRef :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>v" 50)
-- {* We may need additional assumptions here (open issue). *}

subsection {* Integer Sort *}

class INT_SORT = VALUE_SORT +
  fixes MkInt :: "int \<Rightarrow> 'a"
  fixes DestInt :: "'a \<Rightarrow> int"
  fixes IsInt :: "'a \<Rightarrow> bool"
(* assumes inverse [simp] : "DestInt (MkInt i) = i" *)
begin

text {* Integer Operators *}

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
notation divide (infixl "divv" 70)

definition modulus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"modulus i1 i2 = MkInt (DestInt(i1) mod DestInt(i2))"
notation modulus (infixl "modv" 70)

text {* Default Simplifications *}

declare uminus_def [simp]
declare plus_def [simp]
declare minus_def [simp]
declare times_def [simp]
declare divide_def [simp]
declare modulus_def [simp]
end

subsection {* Boolean Sort *}

class BOOL_SORT = VALUE_SORT +
  fixes MkBool :: "bool \<Rightarrow> 'a"
  fixes DestBool :: "'a \<Rightarrow> bool"
  fixes IsBool :: "'a \<Rightarrow> bool"
(* assumes inverse [simp] : "DestBool (MkBool b) = b" *)

subsection {* String Sort *}

class STRING_SORT = VALUE_SORT +
  fixes MkStr :: "string \<Rightarrow> 'a"
  fixes DestStr :: "'a \<Rightarrow> string"
  fixes IsStr :: "'a \<Rightarrow> bool"
(* assumes inverse [simp] : "DestStr (MkStr s) = s" *)

subsection {* Pair Sort *}

class PAIR_SORT = VALUE_SORT +
  fixes MkPair :: "('a \<times> 'a) \<Rightarrow> 'a"
  fixes DestPair :: "'a \<Rightarrow> ('a \<times> 'a)"
  fixes IsPair :: "'a \<Rightarrow> bool"
(* assumes inverse [simp] : "DestPair (MkPair v1_v2) = v1_v2" *)

subsection {* Set Sort *}

class SET_SORT = VALUE_SORT +
  fixes MkSet :: "'a set \<Rightarrow> 'a"
  fixes DestSet :: "'a \<Rightarrow> 'a set"
  fixes IsSet :: "'a \<Rightarrow> bool"
(* assumes inverse [simp] : "IdxSet vs \<longrightarrow> DestSet (MkSet vs) = vs" *)
begin

text {* Set Operators *}

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

definition subseteq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
"subseteq v1 v2 = ((DestSet v1) \<subseteq> (DestSet v2))"
notation subseteq ("(_/ \<subseteq>v _)" [50, 51] 50)

definition subset :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
"subset v1 v2 = ((DestSet v1) \<subset> (DestSet v2))"
notation subset ("(_/ \<subset>v _)" [50, 51] 50)

text {* Default Simplifications *}

declare union_def [simp]
declare inter_def [simp]
declare member_def [simp]
declare not_member_def [simp]
declare subseteq_def [simp]
declare subset_def [simp]
end

subsection {* Function Sorts *}

class FUNCTION_SORT =
  fixes MkFunc :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a"
  fixes DestFunc :: "'a \<Rightarrow> ('a \<Rightarrow> 'a)"
  fixes IsFunc :: "'a \<Rightarrow> bool"
(* assumes inverse [simp] : "MkFun (DestFun f) = f" *)
begin

text {* Function Operators *}

definition idv :: 'a where
"idv = MkFunc id"

definition app :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"app = DestFunc"
end

subsection {* Aggregated Sorts *}

class BASIC_SORT =
  INT_SORT + BOOL_SORT + STRING_SORT

class COMPOSITE_SORT =
  BASIC_SORT + PAIR_SORT + SET_SORT

class COMPOSITE_SORT2 =
  BASIC_SORT + PAIR_SORT + SET_SORT + FUNCTION_SORT
end
