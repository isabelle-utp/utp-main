(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_sorts.thy                                                        *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Value Sorts *}

theory utp_sorts
imports "../utp_common"
begin

hide_const (open) Lattice.top
hide_const (open) Lattice.inf
hide_const (open) Lattice.sup

text {* Some sorts still need to be developed in terms of their operators. *}

subsection {* Root Value Sort *}

text {*
  It is still an open issue whether to include a notion of well-formedness
  of a value. From our experience with concrete value models, we noticed that
  this can be useful. Examples are the HO model and Simon's injectable values.
  Despite this, for reasons of simplicity, we require refinement to be defined
  on the entire carrier set of the value type. Possible this design needs to
  be evaluated too.
*}

text {*
  It would be nice to introduce typing in @{text "UTP_VALUE"} but this seems
  not to be feasible as it would require a second HOL type parameter in the
  respective fixed constant, namely for the underlying value type. Our design
  thus opted for introducing the connection to types by virtue of locales.
*}

class UTP_VALUE =
  fixes WellFormed :: "'a \<Rightarrow> bool"

subsection {* Refinable Values *}

class REF_VALUE = UTP_VALUE + complete_lattice

subsubsection {* Notations *}

text {* Infimum and Supremum *}

notation Inf ("\<Sqinter>v")
notation Sup ("\<Squnion>v")

text {* Meet and Join *}

text {* The precedence of the following two operators is still an open issue. *}

notation inf (infixr "\<sqinter>v" 200)
notation sup (infixr "\<squnion>v" 200)

text {* Refinement *}

notation less_eq (infixr "\<sqsubseteq>v" 50)
notation less (infixr "\<sqsubset>v" 50)

text {* Bottom and Top *}

notation top ("\<top>v")
notation bot ("\<bottom>v")

subsection {* Integer Values *}

class INT_VALUE = UTP_VALUE +
  fixes MkInt :: "int \<Rightarrow> 'a"
  fixes DestInt :: "'a \<Rightarrow> int"
  fixes IsInt :: "'a \<Rightarrow> bool"
  assumes well_formed [simp] : "WellFormed (MkInt i)"
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
notation divide (infixl "divv" 70)

definition modulus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"modulus i1 i2 = MkInt (DestInt(i1) mod DestInt(i2))"
notation modulus (infixl "modv" 70)

subsubsection {* Default Simplifications *}

declare uminus_def [simp]
declare plus_def [simp]
declare minus_def [simp]
declare times_def [simp]
declare divide_def [simp]
declare modulus_def [simp]
end

subsection {* Boolean Values *}

class BOOL_VALUE = UTP_VALUE +
  fixes MkBool :: "bool \<Rightarrow> 'a"
  fixes DestBool :: "'a \<Rightarrow> bool"
  fixes IsBool :: "'a \<Rightarrow> bool"
  assumes well_formed [simp] : "WellFormed (MkBool b)"
  assumes inverse [simp] : "DestBool (MkBool b) = b"

subsection {* String Sort *}

class STRING_VALUE = UTP_VALUE +
  fixes MkStr :: "string \<Rightarrow> 'a"
  fixes DestStr :: "'a \<Rightarrow> string"
  fixes IsStr :: "'a \<Rightarrow> bool"
  assumes well_formed [simp] : "WellFormed (MkStr s)"
  assumes inverse [simp] : "DestStr (MkStr s) = s"

subsection {* Pair Values *}

class PAIR_VALUE = UTP_VALUE +
  fixes MkPair :: "('a \<times> 'a) \<Rightarrow> 'a"
  fixes DestPair :: "'a \<Rightarrow> ('a \<times> 'a)"
  fixes IsPair :: "'a \<Rightarrow> bool"
  assumes inverse [simp] :
    "WellFormed (MkPair v1_v2) \<longrightarrow> DestPair (MkPair v1_v2) = v1_v2"

subsection {* Set Values *}

class SET_VALUE = UTP_VALUE +
  fixes MkSet :: "'a set \<Rightarrow> 'a"
  fixes DestSet :: "'a \<Rightarrow> 'a set"
  fixes IsSet :: "'a \<Rightarrow> bool"
  assumes inverse [simp] :
    "WellFormed (MkSet vs) \<longrightarrow> DestSet (MkSet vs) = vs"
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

definition subseteq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
"subseteq v1 v2 = ((DestSet v1) \<subseteq> (DestSet v2))"
notation subseteq ("(_/ \<subseteq>v _)" [50, 51] 50)

definition subset :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
"subset v1 v2 = ((DestSet v1) \<subset> (DestSet v2))"
notation subset ("(_/ \<subset>v _)" [50, 51] 50)

subsection {* Default Simplifications *}

declare union_def [simp]
declare inter_def [simp]
declare member_def [simp]
declare not_member_def [simp]
declare subseteq_def [simp]
declare subset_def [simp]
end

subsection {* Aggregated Sorts *}

class BASIC_VALUE =
  INT_VALUE + BOOL_VALUE + STRING_VALUE

class COMPOSITE_VALUE =
  BASIC_VALUE + PAIR_VALUE + SET_VALUE
end