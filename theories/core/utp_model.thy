(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utp_model.thy                                                        *)
(* Authors: Frank Zeyda & Simon Foster, University of York (UK)               *)
(******************************************************************************)
(* LAST REVIEWED: 2 July 2014 *)

header {* Generic Model *}

theory utp_model
imports "../utp_common"
begin

text {* We develop a generic hierarchical model for values and types here. *}

default_sort type

subsection {* Theorem Attributes *}

ML {*
  structure defined = Named_Thms
    (val name = @{binding defined} val description = "definedness theorems")
*}

setup defined.setup

ML {*
  structure typing = Named_Thms
    (val name = @{binding typing} val description = "typing theorems")
*}

setup typing.setup

subsection {* Base Model *}

text {*
  A type class is used to relate the value and type notions of a UTP model.
  This means that the user has to encode both these notions into a single HOL
  type and as part of the instantiation identify subsets of that HOL type's
  universe that correspond to UTP value and type models. This approach works
  around the limitation of HOL not supporting multi-parameter type classes.
*}

class BASE_MODEL =
-- {* Universe of the value model. *}
  fixes VALUE :: "'a set"
-- {* Universe of the type model. *}
  fixes UTYPE :: "'a set"
-- {* The disjointness property below may not be needed. *}
-- {* @{text "assumes models_disjoint : VALUE \<inter> UTYPE = {}"} *}
-- {* There must be at least one model value. *}
  assumes values_non_empty : "\<exists> v . v \<in> VALUE"
-- {* There must be at least one model type. *}
  assumes utypes_non_empty : "\<exists> t . t \<in> UTYPE"

text {*
  The non-emptiness assumptions of the @{class BASE_MODEL} class are needed
  to encapsulate UTP model values and types into HOL types as we do next.
*}

subsection {* Type Definitions *}

typedef 'MODEL::BASE_MODEL VALUE = "VALUE :: 'MODEL set"
apply (rule values_non_empty)
done

typedef 'MODEL::BASE_MODEL UTYPE = "UTYPE :: 'MODEL set"
apply (rule utypes_non_empty)
done

text {* Note that the we cannot directly use the lifting facility here. *}


-- {* @{text "setup_lifting type_definition_VALUE"}. *}
-- {* @{text "setup_lifting type_definition_UTYPE"}. *}

subsubsection {* Proof Support *}

declare Abs_VALUE_inverse [simp, intro!]
declare Rep_VALUE_inverse [simp]
declare Rep_VALUE [simp]

declare Abs_UTYPE_inverse [simp, intro!]
declare Rep_UTYPE_inverse [simp]
declare Rep_UTYPE [simp]

paragraph {* Transfer Support for @{typ "'MODEL VALUE"} *}

text {*
  We note that @{text setup_lifting} fails due to the type parameter
  in @{typ "'a VALUE"}. However, it we can set up transfer manually.
*}

definition cr_VALUE :: "'MODEL::BASE_MODEL \<Rightarrow> 'MODEL VALUE \<Rightarrow> bool" where
"cr_VALUE \<equiv> (\<lambda> x y . x = Rep_VALUE y)"

definition pcr_VALUE :: "'MODEL::BASE_MODEL \<Rightarrow> 'MODEL VALUE \<Rightarrow> bool" where
"pcr_VALUE \<equiv> (op =) OO cr_VALUE"

theorem pcr_cr_eq_VALUE :
"pcr_VALUE = cr_VALUE"
apply (unfold pcr_VALUE_def)
apply (simp add: eq_OO)
done

theorem right_total_VALUE [transfer_rule] :
"right_total pcr_VALUE"
apply (unfold pcr_VALUE_def)
apply (unfold cr_VALUE_def)
apply (unfold right_total_def)
apply (simp add: eq_OO)
done

theorem "right_unique_VALUE" [transfer_rule] :
"right_unique pcr_VALUE"
apply (unfold pcr_VALUE_def)
apply (unfold cr_VALUE_def)
apply (unfold right_unique_def)
apply (simp add: eq_OO)
apply (metis Rep_VALUE_inverse)
done

theorem bi_unique_VALUE [transfer_rule] :
"bi_unique pcr_VALUE"
apply (unfold pcr_VALUE_def)
apply (unfold cr_VALUE_def)
apply (unfold bi_unique_def)
apply (simp add: eq_OO)
apply (metis Rep_VALUE_inverse)
done

theorem rep_transfer_VALUE [transfer_rule] :
"fun_rel pcr_VALUE (op =) (\<lambda> x . x) Rep_VALUE"
apply (unfold pcr_VALUE_def)
apply (unfold cr_VALUE_def)
apply (unfold fun_rel_def)
apply (simp add: eq_OO)
done

theorem domain_VALUE :
"Domainp pcr_VALUE = (\<lambda> x . \<exists> y . x = y \<and> y \<in> VALUE)"
apply (unfold pcr_VALUE_def)
apply (unfold cr_VALUE_def)
apply (simp add: eq_OO)
apply (rule ext)
apply (simp add: Domainp_iff)
apply (safe)
apply (metis Rep_VALUE)
apply (metis Rep_VALUE_cases)
done

theorem domain_eq_VALUE [transfer_domain_rule] :
"Domainp pcr_VALUE = (\<lambda> x . x \<in> VALUE)"
apply (unfold domain_VALUE)
apply (simp)
done

theorem domain_par_VALUE [transfer_domain_rule] :
"Domainp (op =) = P1 \<Longrightarrow>
 fun_rel (op =) (op =) P2' (\<lambda> x . x \<in> VALUE) \<Longrightarrow>
 Domainp pcr_VALUE = inf P1 P2'"
apply (simp add: domain_VALUE)
apply (unfold fun_rel_def)
apply (simp add: fun_eq_iff)
apply (simp add: Domainp_iff)
done

theorem domain_par_left_total_VALUE [transfer_domain_rule] :
"fun_rel op = op = P' (\<lambda>x. x \<in> VALUE) \<Longrightarrow> Domainp pcr_VALUE = P'"
apply (simp add: domain_VALUE)
apply (unfold fun_rel_def)
apply (simp add: fun_eq_iff)
done

theorem Quotient_VALUE :
"Quotient (Lifting.invariant (\<lambda> x . x \<in> VALUE)) Abs_VALUE Rep_VALUE cr_VALUE"
apply (unfold Quotient_def)
apply (unfold Lifting.invariant_def)
apply (unfold cr_VALUE_def)
apply (safe)
apply (simp_all)
apply (metis Abs_VALUE_inverse)
apply (metis Abs_VALUE_cases Abs_VALUE_inverse)
done

text {* Not sure the instantiation below is needed. *}

instantiation VALUE :: (type) term_of
begin
definition term_of_VALUE :: "'a VALUE \<Rightarrow> term" where
"term_of_VALUE x = undefined"
instance
apply (intro_classes)
done
end

theorem term_of_VALUE_triv :
"term_of_class.term_of (t :: 'a VALUE) = undefined"
apply (unfold term_of_VALUE_def)
apply (simp)
done

paragraph {* Transfer Support for @{typ "'MODEL UTYPE"} *}

text {*
  We note that @{text setup_lifting} fails due to the type parameter
  in @{typ "'a VALUE"}. However, it we can set up transfer manually.
*}

definition cr_UTYPE :: "'MODEL::BASE_MODEL \<Rightarrow> 'MODEL UTYPE \<Rightarrow> bool" where
"cr_UTYPE \<equiv> (\<lambda> x y . x = Rep_UTYPE y)"

definition pcr_UTYPE :: "'MODEL::BASE_MODEL \<Rightarrow> 'MODEL UTYPE \<Rightarrow> bool" where
"pcr_UTYPE \<equiv> (op =) OO cr_UTYPE"

theorem pcr_cr_eq_UTYPE :
"pcr_UTYPE = cr_UTYPE"
apply (unfold pcr_UTYPE_def)
apply (simp add: eq_OO)
done

theorem right_total_UTYPE [transfer_rule] :
"right_total pcr_UTYPE"
apply (unfold pcr_UTYPE_def)
apply (unfold cr_UTYPE_def)
apply (unfold right_total_def)
apply (simp add: eq_OO)
done

theorem "right_unique_UTYPE" [transfer_rule] :
"right_unique pcr_UTYPE"
apply (unfold pcr_UTYPE_def)
apply (unfold cr_UTYPE_def)
apply (unfold right_unique_def)
apply (simp add: eq_OO)
apply (metis Rep_UTYPE_inverse)
done

theorem bi_unique_UTYPE [transfer_rule] :
"bi_unique pcr_UTYPE"
apply (unfold pcr_UTYPE_def)
apply (unfold cr_UTYPE_def)
apply (unfold bi_unique_def)
apply (simp add: eq_OO)
apply (metis Rep_UTYPE_inverse)
done

theorem rep_transfer_UTYPE [transfer_rule] :
"fun_rel pcr_UTYPE (op =) (\<lambda> x . x) Rep_UTYPE"
apply (unfold pcr_UTYPE_def)
apply (unfold cr_UTYPE_def)
apply (unfold fun_rel_def)
apply (simp add: eq_OO)
done

theorem domain_UTYPE :
"Domainp pcr_UTYPE = (\<lambda> x . \<exists> y . x = y \<and> y \<in> UTYPE)"
apply (unfold pcr_UTYPE_def)
apply (unfold cr_UTYPE_def)
apply (simp add: eq_OO)
apply (rule ext)
apply (simp add: Domainp_iff)
apply (safe)
apply (metis Rep_UTYPE)
apply (metis Rep_UTYPE_cases)
done

theorem domain_eq_UTYPE [transfer_domain_rule] :
"Domainp pcr_UTYPE = (\<lambda> x . x \<in> UTYPE)"
apply (unfold domain_UTYPE)
apply (simp)
done

theorem domain_par_UTYPE [transfer_domain_rule] :
"Domainp (op =) = P1 \<Longrightarrow>
 fun_rel (op =) (op =) P2' (\<lambda> x . x \<in> UTYPE) \<Longrightarrow>
 Domainp pcr_UTYPE = inf P1 P2'"
apply (simp add: domain_UTYPE)
apply (unfold fun_rel_def)
apply (simp add: fun_eq_iff)
apply (simp add: Domainp_iff)
done

theorem domain_par_left_total_UTYPE [transfer_domain_rule] :
"fun_rel op = op = P' (\<lambda> x . x \<in> UTYPE) \<Longrightarrow> Domainp pcr_UTYPE = P'"
apply (simp add: domain_UTYPE)
apply (unfold fun_rel_def)
apply (simp add: fun_eq_iff)
done

theorem Quotient_UTYPE :
"Quotient (Lifting.invariant (\<lambda> x . x \<in> UTYPE)) Abs_UTYPE Rep_UTYPE cr_UTYPE"
apply (unfold Quotient_def)
apply (unfold Lifting.invariant_def)
apply (unfold cr_UTYPE_def)
apply (safe)
apply (simp_all)
apply (metis Abs_UTYPE_inverse)
apply (metis Abs_UTYPE_cases Abs_UTYPE_inverse)
done

text {* Not sure the instantiation below is needed. *}

instantiation UTYPE :: (type) term_of
begin
definition term_of_UTYPE :: "'a UTYPE \<Rightarrow> term" where
"term_of_UTYPE x = undefined"
instance
apply (intro_classes)
done
end

theorem term_of_UTYPE_triv :
"term_of_class.term_of (t :: 'a UTYPE) = undefined"
apply (unfold term_of_UTYPE_def)
apply (simp)
done

subsection {* Countable Model *}

text {*
  The class @{text COUNTABLE_MODEL} introduces the caveat that model types
  have to be countable. For such models, we automatically obtain that
  @{typ "'MODEL UTYPE"} is an instance of the class @{class countable}.
*}

class COUNTABLE_MODEL = BASE_MODEL +
  assumes countable_UTYPE [simp] : "countable UTYPE"

instantiation UTYPE :: (COUNTABLE_MODEL) countable
begin
instance
apply (intro_classes)
apply (subgoal_tac "countable (UTYPE :: 'a set)")
-- {* Subgoal 1 *}
apply (unfold countable_def) [1]
apply (clarify)
apply (rule_tac x = "f o Rep_UTYPE" in exI)
apply (rule comp_inj_on)
-- {* Subgoal 1.1 *}
apply (rule injI)
apply (metis Rep_UTYPE_inject)
-- {* Subgoal 1.2 *}
apply (subgoal_tac "range Rep_UTYPE = UTYPE")
apply (erule ssubst)
apply (assumption)
apply (rule type_definition.Rep_range)
apply (rule type_definition_UTYPE)
-- {* Subgoal 2 *}
apply (rule countable_UTYPE)
done
end

text {* Countablility also induces a linear order on types. *}

instantiation UTYPE :: (COUNTABLE_MODEL) linorder
begin
definition less_eq_UTYPE :: "'a UTYPE \<Rightarrow> 'a UTYPE \<Rightarrow> bool" where
"less_eq_UTYPE t1 t2 = ((to_nat t1) \<le> (to_nat t2))"
definition less_UTYPE :: "'a UTYPE \<Rightarrow> 'a UTYPE \<Rightarrow> bool" where
"less_UTYPE t1 t2 = ((to_nat t1) < (to_nat t2))"
instance
apply (intro_classes)
apply (unfold less_eq_UTYPE_def less_UTYPE_def)
apply (auto)
done
end

subsection {* Infinite Model *}

text {*
  The class @{text INFINITE_MODEL} introduces the caveat that model types 
  have infinite carriers. For such models, we automatically obtain that
  @{typ "'MODEL UTYPE"} is an instance of the class @{class infinite}.
  Importantly, for models that are both countable and infinite, we can embed
  (meaning inject) their types into arbitrary HOL types that are likewise
  countable and infinite as the cardinality in both cases is @{text "\<aleph>\<^sub>0"}.
*}

class INFINITE_MODEL = BASE_MODEL +
  assumes infinite_UTYPE [simp] : "infinite UTYPE"

instantiation UTYPE :: (INFINITE_MODEL) infinite
begin
instance
apply (intro_classes)
apply (subgoal_tac "infinite (UTYPE :: 'a set)")
apply (metis (full_types) Rep_UTYPE_cases finite_surj rangeI subsetI)
apply (simp)
done
end

subsection {* Defined Model *}

text {* The next layer introduces the notion of definedness. *}

class DEFINED_MODEL = BASE_MODEL +
-- {* Definedness notion for values. *}
  fixes defined :: "'a VALUE \<Rightarrow> bool" ("\<D>")
-- {* We assume the existence of at least one defined value. *}
  assumes defined_value_exists : "\<exists> v . \<D> v"
begin

text {*
  Perhaps the existence of a defined value is not relevant in practice, unless
  we additionally like to introduce a type definition for defined values. For
  now, I am not considering this though as it appears to complicate matters.
*}

theorem defined_vacuous [simp] :
"is_total \<D> \<Longrightarrow> \<D> x"
apply (erule is_totalD)
done

subsubsection {* Defined Values *}

definition DVALUE :: "'a VALUE set" where
"DVALUE = {v . \<D> v}"

theorem DVALUE_member [iff] :
"v \<in> DVALUE \<longleftrightarrow> \<D> v"
apply (simp add: DVALUE_def)
done

theorem DVALUE_exists :
"\<exists> v . v \<in> DVALUE"
apply (simp)
apply (rule defined_value_exists)
done

theorem DVALUE_non_empty [simp] :
"DVALUE \<noteq> {}"
apply (simp add: set_eq_iff)
apply (rule defined_value_exists)
done

theorem DVALUE_vacuous [simp] :
"is_total \<D> \<Longrightarrow> DVALUE = UNIV"
apply (simp add: DVALUE_def)
done
end

subsection {* Pretyped Model *}

text {*
  The class @{text PRE_TYPED_MODEL} is useful in cases where we do not have a
  typing relation with the right properties yet but nevertheless like to make
  use of core definitions related to typed values. In the predicate model, it
  allows us to prove laws that hold irrespective of the non-emptiness property
  of types, for instance. Perhaps review the need for this class once the HO
  model is fully in place; it would actually be nice to eradicate it.
*}

class PRE_TYPED_MODEL = DEFINED_MODEL +
-- {* Typing relation of the model. *}
  fixes type_rel :: "'a VALUE \<Rightarrow> 'a UTYPE \<Rightarrow> bool" (infix ":" 50)
begin

subsubsection {* Strict Typing *}

definition strict_type_rel ::
  "'a VALUE \<Rightarrow> 'a UTYPE \<Rightarrow> bool" (infix ":!" 50) where
"v :! t \<longleftrightarrow> (v : t \<and> \<D> v)"

declare strict_type_rel_def [iff]

theorem strict_type_rel_vacuous [simp] :
"is_total \<D> \<Longrightarrow> op :! = op :"
apply (rule ext)+
apply (simp)
done

subsubsection {* Value of a Type *}

definition some_value :: "'a UTYPE \<Rightarrow> 'a VALUE" where
"some_value t = (SOME v . v : t)"

definition some_defined_value :: "'a UTYPE \<Rightarrow> 'a VALUE" where
"some_defined_value t = (SOME v . v : t \<and> \<D> v)"

subsubsection {* Type of a Value *}

definition utype_of :: "'a VALUE \<Rightarrow> 'a UTYPE" where
"utype_of v = (SOME t . v : t)"

subsubsection {* Carrier Sets *}

definition carrier :: "'a UTYPE \<Rightarrow> 'a VALUE set" where
"carrier t = {v . v : t}"

definition dcarrier :: "'a UTYPE \<Rightarrow> 'a VALUE set" where
"dcarrier t = {v . v :! t}"

subsubsection {* Values Restricted to Types *}

definition VALUES :: "'a UTYPE set \<Rightarrow> 'a VALUE set" where
"VALUES ts = \<Union> (carrier ` ts)"

theorem VALUES_member [iff] :
"v \<in> VALUES ts \<longleftrightarrow> (\<exists> t \<in> ts . v : t)"
apply (unfold VALUES_def)
apply (simp)
apply (unfold carrier_def)
apply (simp)
done
end

subsection {* Typed Model *}

text {*
  The two fundamental properties of typing are that types are non-empty and
  that each defined value belongs to some type. We do not, however, preclude
  type systems in which values may belong to more than one type. Stronger
  constraints are imposed, for instance, in a @{text MONO_TYPED_MODEL} model
  where values indeed must inhabit a single type only.
*}

class TYPED_MODEL = PRE_TYPED_MODEL +
-- {* Every type includes at least one defined value. *}
  assumes types_non_empty : "\<exists> v . v : t \<and> \<D> v"
-- {* Every defined value inhabits at least one type. *}
  assumes all_values_typed : "\<D> v \<Longrightarrow> \<exists> t . v : t"
begin

subsubsection {* Well-typed Values *}

definition WT_VALUE :: "'a VALUE set" where
"WT_VALUE = \<Union> {dcarrier t | t . True}"

theorem  WT_VALUE_member [iff] :
"v \<in> WT_VALUE \<longleftrightarrow> (\<exists> t . v :! t)"
apply (unfold WT_VALUE_def)
apply (unfold dcarrier_def)
apply (unfold strict_type_rel_def)
apply (auto)
done

subsubsection {* Theorems *}

paragraph {* Value of a Type *}

theorem some_value_typed [simp] :
"(some_value t) : t"
apply (unfold some_value_def)
apply (rule someI_ex)
apply (insert types_non_empty [of "t"])
apply (clarify)
apply (rule_tac x = "v" in exI)
apply (assumption)
done

theorem some_defined_value_typed [simp] :
"(some_defined_value t) : t"
apply (unfold some_defined_value_def)
apply (insert types_non_empty [of "t"])
apply (clarify)
apply (rule_tac a = "v" in someI2)
apply (simp_all)
done

theorem some_defined_value_defined [simp] :
"\<D> (some_defined_value t)"
apply (unfold some_defined_value_def)
apply (insert types_non_empty [of "t"])
apply (clarify)
apply (rule_tac a = "v" in someI2)
apply (simp_all)
done

theorem some_defined_value_strictly_typed [simp] :
"(some_defined_value t) :! t"
apply (unfold strict_type_rel_def)
apply (rule conjI)
apply (rule some_defined_value_typed)
apply (rule some_defined_value_defined)
done

paragraph {* Type of a Value *}

theorem utype_of_typed [simp] :
"\<D> v \<Longrightarrow> v : (utype_of v)"
apply (unfold utype_of_def)
apply (rule someI_ex)
apply (erule all_values_typed)
done

paragraph {* Carrier Sets *}

theorem carrier_member [iff] :
"v \<in> carrier t \<longleftrightarrow> v : t"
apply (simp add: carrier_def)
done

theorem carrier_non_empty :
"\<exists> v . v \<in> carrier t"
apply (unfold carrier_member)
apply (metis types_non_empty)
done

theorem dcarrier_member [iff] :
"v \<in> dcarrier t \<longleftrightarrow> v :! t"
apply (simp add: dcarrier_def)
done

theorem dcarrier_non_empty :
"\<exists> v . v \<in> dcarrier t"
apply (unfold dcarrier_member)
apply (unfold strict_type_rel_def)
apply (metis types_non_empty)
done

theorem dcarrier_subset :
"(dcarrier t) \<subseteq> (carrier t)"
apply (simp add: subset_iff)
done

theorem dcarrier_vacuous [simp] :
"is_total \<D> \<Longrightarrow> dcarrier = carrier"
apply (rule ext)
apply (rename_tac t)
apply (rule Set.set_eqI)
apply (simp)
done
end

subsection {* Monotyped Model *}

text {* In monotyped models, values must inhabit a single type. *}

class MONO_TYPED_MODEL = TYPED_MODEL +
  assumes inhabits_single_type : "\<lbrakk>v : t1; v : t2\<rbrakk> \<Longrightarrow> t1 = t2"
begin

declare inhabits_single_type [intro]

theorem carriers_disjoint :
"t1 \<noteq> t2 \<Longrightarrow> carrier t1 \<inter> carrier t2 = {}"
apply (safe)
apply (erule_tac Q = "t1 = t2" in contrapos_np)
apply (simp)
apply (erule inhabits_single_type)
apply (assumption)
done

theorem dcarriers_disjoint :
"t1 \<noteq> t2 \<Longrightarrow> dcarrier t1 \<inter> dcarrier t2 = {}"
apply (safe)
apply (erule_tac Q = "t1 = t2" in contrapos_np)
apply (simp)
apply (erule inhabits_single_type)
apply (assumption)
done

subsubsection {* Unique Type of a Value *}

definition the_utype_of :: "'a VALUE \<Rightarrow> 'a UTYPE" where
"the_utype_of v = (THE t . v : t)"

theorem utype_of_value_unique :
"\<D> v \<Longrightarrow> utype_of v = the_utype_of v"
apply (simp add: utype_of_def the_utype_of_def)
apply (rule some_equality)
apply (rule theI')
apply (safe)
-- {* Subgoal 1 *}
apply (erule all_values_typed)
-- {* Subgoal 2 *}
apply (metis inhabits_single_type)
-- {* Subgoal 3 *}
apply (rule sym [OF the_equality])
apply (assumption)
apply (metis inhabits_single_type)
done
end
end
