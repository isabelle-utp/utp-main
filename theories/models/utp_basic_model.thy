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

primrec BoolOf :: "bval \<Rightarrow> bool" where
"BoolOf (Bool\<^sub>v x) = x"

primrec IntOf :: "bval \<Rightarrow> int" where
"IntOf (Int\<^sub>v x) = x"

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

fun default_bval :: "btyp \<Rightarrow> bval" where
"default_bval(Int\<^sub>t)    = Int\<^sub>v 0" |
"default_bval(Bool\<^sub>t)   = Bool\<^sub>v True" |
"default_bval(List\<^sub>t t) = List\<^sub>v t []"

lemma default_bval_type: "default_bval(t) :\<^sub>b t"
  by (induct t, auto)

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
fun defined_bval :: "bval \<Rightarrow> bool" where
"\<D> (Bot\<^sub>v a) = False" |
"\<D> (Bool\<^sub>v x) = True" |
"\<D> (Int\<^sub>v x) = True" |
"\<D> (List\<^sub>v a xs) = (\<forall> x \<in> set(xs). \<D>(x) \<and> x :\<^sub>b a)"
instance ..
end

lemma default_bval_defined: "\<D>(default_bval(t))"
  by (induct t, simp_all)

lemma defined_bval_typed: "\<D>(x) \<Longrightarrow> \<exists> t. x :\<^sub>b t"
  by (induct x, auto)
  
text {* Then we show that our value space is a valid UTP value space by instantiating
        the VALUE class. This involves a proof that the type space is countable. *}

datatype bmdl =
  bval "bval" |
  btyp "btyp"

primrec bvalOf :: "bmdl \<Rightarrow> bval" where
"bvalOf (bval x) = x"

primrec btypOf :: "bmdl \<Rightarrow> btyp" where
"btypOf (btyp x) = x"

instantiation bmdl :: BASE_MODEL
begin
definition VALUE_bmdl :: "bmdl set" where
"VALUE_bmdl = range bval"

definition UTYPE_bmdl :: "bmdl set" where
"UTYPE_bmdl = range btyp"
instance by (intro_classes, auto simp add: VALUE_bmdl_def UTYPE_bmdl_def)
end

setup_lifting type_definition_utype
setup_lifting type_definition_uval

instantiation bmdl :: DEFINED_MODEL
begin
lift_definition value_defined_bmdl :: "bmdl uval \<Rightarrow> bool" is
"\<lambda> v. \<D> (bvalOf v)" .

instance
  apply (intro_classes)
  apply (transfer)
  apply (metis Collect_mem_eq VALUE_bmdl_def bvalOf.simps defined_bval.simps(2) rangeI)
done
end

instantiation bmdl :: PRE_TYPED_MODEL
begin

lift_definition type_rel_bmdl :: "bmdl uval \<Rightarrow> bmdl utype \<Rightarrow> bool" is
"\<lambda> x t. bvalOf x :\<^sub>b btypOf t" .

instance ..

end

instance bmdl :: TYPED_MODEL
  apply (intro_classes)
  apply (transfer)
  apply (auto simp add:UTYPE_bmdl_def VALUE_bmdl_def)
  apply (metis default_bval_defined default_bval_type)
  apply (transfer)
  apply (auto simp add:VALUE_bmdl_def UTYPE_bmdl_def)
  apply (metis defined_bval_typed)
done

text {* We also instantiate the Boolean and Integer sorts so that we can 
        make use of theories which require them (e.g. Designs). *}

instantiation bmdl :: BOOL_SORT
begin

lift_definition MkBool_bmdl :: "bool \<Rightarrow> bmdl uval" is
"\<lambda> x. bval (Bool\<^sub>v x)" by (simp add:VALUE_bmdl_def)

lift_definition DestBool_bmdl :: "bmdl uval \<Rightarrow> bool" is
"\<lambda> v. BoolOf (bvalOf v)" . 

lift_definition BoolType_bmdl :: "bmdl utype" is
"btyp Bool\<^sub>t" by (simp add:UTYPE_bmdl_def)

instance
  apply (intro_classes)
  apply (unfold_locales)
  apply (auto)
  apply (transfer, auto simp add:VALUE_bmdl_def)+
done
end

instantiation bmdl :: INT_SORT
begin

lift_definition MkInt_bmdl :: "int \<Rightarrow> bmdl uval" is
"\<lambda> x. bval (Int\<^sub>v x)" by (simp add:VALUE_bmdl_def)

lift_definition DestInt_bmdl :: "bmdl uval \<Rightarrow> int" is
"\<lambda> v. IntOf (bvalOf v)" . 

lift_definition IntType_bmdl :: "bmdl utype" is
"btyp Int\<^sub>t" by (simp add:UTYPE_bmdl_def)

instance
  apply (intro_classes)
  apply (unfold_locales)
  apply (auto)
  apply (transfer, auto simp add:VALUE_bmdl_def)+
done
end

end