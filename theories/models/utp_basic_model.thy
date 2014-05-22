(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_basic_model.thy                                                  *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Basic model for UTP predicates *}

theory utp_basic_model
imports 
  Derive
  "../utp_base"
begin

default_sort type

text {* We first create types to represent basic types and values in our model. *}

datatype btyp = Int\<^sub>t | Bool\<^sub>t | List\<^sub>t btyp
datatype bval = Bot\<^sub>v btyp | Int\<^sub>v int | Bool\<^sub>v bool | List\<^sub>v btyp "(bval list)"

text {* Our type space must be countable which we derive here. Moreover, our type and value
        spaces are also linearly ordered. *}

derive countable btyp
derive linorder btyp
derive linorder bval

text {* Next we create a type relation using an inductive predicate definition. *}

inductive bval_type_rel :: "bval \<Rightarrow> btyp \<Rightarrow> bool" (infix ":\<^sub>b" 50) where
Bot\<^sub>v_type [intro]: "Bot\<^sub>v(t) :\<^sub>b t" |
Bool\<^sub>v_type [intro]: "Bool\<^sub>v(x) :\<^sub>b Bool\<^sub>t"  |  
Int\<^sub>v_type [intro]: "Int\<^sub>v(n) :\<^sub>b Int\<^sub>t"  | 
List\<^sub>v_type [intro]: "\<forall> x\<in>set(xs). x :\<^sub>b t \<Longrightarrow> List\<^sub>v(t)(xs) :\<^sub>b List\<^sub>t(t)"

inductive_cases
  Bot\<^sub>v_cases [elim]: "Bot\<^sub>v a :\<^sub>b t" and
  Bot\<^sub>t_cases [elim!]: "x :\<^sub>b Bot\<^sub>t" and
  Bool\<^sub>v_cases [elim]: "Bool\<^sub>v x :\<^sub>b t" and
  Bool\<^sub>t_cases [elim!]: "x :\<^sub>b Boot\<^sub>t" and
  Int\<^sub>v_cases [elim]: "Int\<^sub>v x :\<^sub>b t" and
  Int\<^sub>t_cases [elim!]: "x :\<^sub>b Int\<^sub>t" and
  List\<^sub>v_cases [elim]: "List\<^sub>v a xs :\<^sub>b t" and
  List\<^sub>t_cases [elim!]: "x :\<^sub>b List\<^sub>t a"

text {* We create some useful type synonyms for expressions, predicates, and variables in
        our basic value model. *}

type_synonym 'a bexp   = "('a, bval) pexpr"
type_synonym bpred     = "bval upred" 
type_synonym 'a bvar   = "('a, bval) pvar"

translations
  (type) "'a bexp" <= (type) "('a, bval) pexpr"
  (type) "bpred" <= (type) "bval upred"
  (type) "'a bvar" <= (type) "('a, bval) pvar"

text {* We next create a definedness predicate for our value space that 
        determines whether a value contains a bottom element. *}

instantiation bval :: DEFINED
begin

fun Defined_bval :: "bval \<Rightarrow> bool" where
"\<D>(Bot\<^sub>v a) = False" |  "\<D>(Bool\<^sub>v x) = True" | "\<D>(Int\<^sub>v x) = True" |
"\<D>(List\<^sub>v a xs) = (\<forall> x \<in> set(xs). \<D>(x))"

instance ..
end

text {* Then we show that our value space is a valid UTP value space by instantiating
        the VALUE class. This involves a proof that the type space is countable. *}

instantiation bval :: VALUE
begin

definition utype_rel_bval :: "bval \<Rightarrow> nat \<Rightarrow> bool" where
"utype_rel_bval x t \<longleftrightarrow> (\<exists> a. t = to_nat a \<and> x :\<^sub>b a)"

instance
  apply (intro_classes)
  apply (simp add:utype_rel_bval_def)
  apply (rule_tac x="to_nat(Int\<^sub>t)" in exI)
  apply (rule_tac x="Int\<^sub>v 0" in exI)
  apply (auto)
done
end

text {* Next we show some useful inverse properties for embedding types. *}

lemma prjTYPE_inv_bty [simp]
  : "embTYPE ((prjTYPE t) :: btyp) = (t :: bval utype)"
  by (metis Rep_utype_elim Rep_utype_inverse embTYPE_def from_nat_to_nat prjTYPE_def utype_rel_bval_def)

lemma embTYPE_inv_bty [simp]:
  "prjTYPE (embTYPE (t :: btyp) :: bval utype) = t"
  apply (induct t)
  apply (rule embTYPE_inv[of "Int\<^sub>v 0"])
  apply (auto simp add: utype_rel_bval_def)
  apply (rule embTYPE_inv[of "Bool\<^sub>v False"])
  apply (auto simp add: utype_rel_bval_def)
  apply (rule_tac v="List\<^sub>v t []" in embTYPE_inv)
  apply (auto simp add: utype_rel_bval_def)
done

text {* We also show that UTP typing corresponds to our basic type relation. *}

lemma type_rel_btyp [simp]: 
  "x : t \<longleftrightarrow> x :\<^sub>b prjTYPE t"
  by (metis (full_types) Rep_utype_elim empty_Collect_eq from_nat_to_nat prjTYPE_def type_rel_def utype_rel_bval_def)

text {* We also instantiate the Boolean and Integer sorts so that we can 
        make use of theories which require them (e.g. Designs). *}

instantiation bval :: BOOL_SORT
begin

definition MkBool_bval :: "bool \<Rightarrow> bval" where
"MkBool_bval x = Bool\<^sub>v x"

primrec DestBool_bval :: "bval \<Rightarrow> bool" where
"DestBool_bval (Bool\<^sub>v x) = x" 

definition BoolType_bval :: "bval utype" where
"BoolType_bval = embTYPE Bool\<^sub>t"

instance
  apply (intro_classes)
  apply (simp add:MkBool_bval_def DestBool_bval_def BoolType_bval_def dcarrier_def monotype_def type_rel_def)
  apply (auto simp add:MkBool_bval_def DestBool_bval_def BoolType_bval_def dcarrier_def monotype_def)
  apply (metis prjTYPE_inv_bty)
done
end

instantiation bval :: INT_SORT
begin

definition MkInt_bval :: "int \<Rightarrow> bval" where
"MkInt_bval x = Int\<^sub>v x"

primrec DestInt_bval :: "bval \<Rightarrow> int" where
"DestInt_bval (Int\<^sub>v x) = x" 

definition IntType_bval :: "bval utype" where
"IntType_bval = embTYPE Int\<^sub>t"

instance
  apply (intro_classes)
  apply (simp add:MkInt_bval_def DestInt_bval_def IntType_bval_def dcarrier_def monotype_def type_rel_def)
  apply (auto simp add:MkInt_bval_def DestInt_bval_def IntType_bval_def dcarrier_def monotype_def)
done
end

end