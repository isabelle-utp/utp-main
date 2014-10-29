(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utp_model.thy                                                        *)
(* Authors: Simon Foster & Frank Zeyda, University of York (UK)               *)
(******************************************************************************)
(* LAST REVIEWED: 4 September 2014 *)

header {* UTP Model *}

theory utp_model
imports utp_defined
begin

text {* In this theory, we develop a unified model of UTP values and types. *}

default_sort type

subsection {* Base Model *}

text {*
  A type class is used to relate the value and type notions of a UTP model.
  This means that the user has to encode both these notions into a single HOL
  type and, as part of the instantiation, identify subsets of that HOL type's
  universe that correspond to UTP value and type models. This approach works
  around the limitation of HOL not supporting multi-parameter type classes,
  which is really what we need here to solve this design issue.
*}


class BASE_MODEL =
-- {* Universe of the value model. *}
  fixes VALUE :: "'a set"
-- {* Universe of the type model. *}
  fixes UTYPE :: "'a set"
-- {* The disjointness property below may not be essential. *}
-- {* @{text "assumes models_disjoint : VALUE \<inter> UTYPE = {}"} *}
-- {* There must be at least one model value. This is essential! *}
  assumes values_non_empty : "\<exists> v . v \<in> VALUE"
-- {* There must be at least one model type. This is essential! *}
  assumes utypes_non_empty : "\<exists> t . t \<in> UTYPE"

text {*
  We note that the non-emptiness assumptions above are needed to encapsulate
  UTP model values and types into HOL types as we do next.
*}

subsubsection {* Type Definitions *}

typedef 'm::BASE_MODEL uval = "VALUE :: 'm set"
apply (rule values_non_empty)
done

typedef 'm::BASE_MODEL utype = "UTYPE :: 'm set"
apply (rule utypes_non_empty)
done

subsubsection {* Some Model Value *}

abbreviation some_uval :: "'m uval" where
"some_uval \<equiv> undefined"

subsubsection {* Some Model Type *}

abbreviation some_utype :: "'m utype" where
"some_utype \<equiv> undefined"

subsubsection {* Proof Support *}

declare Abs_uval_inverse [simp, intro!]
declare Rep_uval_inverse [simp]
declare Rep_uval [simp]

declare Abs_utype_inverse [simp, intro!]
declare Rep_utype_inverse [simp]
declare Rep_utype [simp]

subsubsection {* Transfer Setup *}

text {*
  Note that the we cannot use @{text "setup_lifting"} due to parametricity of
  the types. Instead, we here prove the relevant transfer theorems by hand.
*}

-- {* @{text "setup_lifting type_definition_uval"}. *}
-- {* @{text "setup_lifting type_definition_utype"}. *}

paragraph {* Transfer Support for @{type uval} *}

definition cr_uval :: "'m::BASE_MODEL \<Rightarrow> 'm uval \<Rightarrow> bool" where
"cr_uval \<equiv> (\<lambda> x y . x = Rep_uval y)"

definition pcr_uval :: "'m::BASE_MODEL \<Rightarrow> 'm uval \<Rightarrow> bool" where
"pcr_uval \<equiv> (op =) OO cr_uval"

theorem pcr_cr_eq_uval :
"pcr_uval = cr_uval"
apply (unfold pcr_uval_def)
apply (simp add: eq_OO)
done

theorem right_total_uval [transfer_rule] :
"right_total pcr_uval"
apply (unfold pcr_uval_def)
apply (unfold cr_uval_def)
apply (unfold right_total_def)
apply (simp add: eq_OO)
done

theorem right_unique_uval [transfer_rule] :
"right_unique pcr_uval"
apply (unfold pcr_uval_def)
apply (unfold cr_uval_def)
apply (unfold right_unique_def)
apply (simp add: eq_OO)
apply (metis Rep_uval_inverse)
done

theorem bi_unique_uval [transfer_rule] :
"bi_unique pcr_uval"
apply (unfold pcr_uval_def)
apply (unfold cr_uval_def)
apply (unfold bi_unique_def)
apply (simp add: eq_OO)
apply (metis Rep_uval_inverse)
done

theorem rep_transfer_uval [transfer_rule] :
"fun_rel pcr_uval (op =) (\<lambda> x . x) Rep_uval"
apply (unfold pcr_uval_def)
apply (unfold cr_uval_def)
apply (unfold fun_rel_def)
apply (simp add: eq_OO)
done

theorem domain_uval :
"Domainp pcr_uval = (\<lambda> x . \<exists> y . x = y \<and> y \<in> VALUE)"
apply (unfold pcr_uval_def)
apply (unfold cr_uval_def)
apply (simp add: eq_OO)
apply (rule ext)
apply (simp add: Domainp_iff)
apply (safe)
apply (metis Rep_uval)
apply (metis Rep_uval_cases)
done

theorem domain_eq_uval [transfer_domain_rule] :
"Domainp pcr_uval = (\<lambda> x . x \<in> VALUE)"
apply (unfold domain_uval)
apply (simp)
done

theorem domain_par_uval [transfer_domain_rule] :
"Domainp (op =) = P1 \<Longrightarrow>
 fun_rel (op =) (op =) P2' (\<lambda> x . x \<in> VALUE) \<Longrightarrow>
 Domainp pcr_uval = P1 \<sqinter> P2'"
apply (simp add: domain_uval)
apply (unfold fun_rel_def)
apply (simp add: fun_eq_iff)
apply (simp add: Domainp_iff)
done

theorem domain_par_left_total_uval [transfer_domain_rule] :
"fun_rel op = op = P' (\<lambda> x . x \<in> VALUE) \<Longrightarrow> Domainp pcr_uval = P'"
apply (simp add: domain_uval)
apply (unfold fun_rel_def)
apply (simp add: fun_eq_iff)
done

theorem Quotient_uval :
"Quotient (Lifting.invariant (\<lambda> x . x \<in> VALUE)) Abs_uval Rep_uval cr_uval"
apply (unfold Quotient_def)
apply (unfold Lifting.invariant_def)
apply (unfold cr_uval_def)
apply (safe)
apply (simp_all)
apply (metis Abs_uval_inverse)
apply (metis Abs_uval_cases Abs_uval_inverse)
done

text {* \fixme{Not sure the instantiation below is needed.} *}

instantiation uval :: (type) term_of
begin
definition term_of_uval :: "'a uval \<Rightarrow> term" where
"term_of_uval x = undefined"
instance
apply (intro_classes)
done
end

theorem term_of_uval_triv :
"term_of_class.term_of (t :: 'a uval) = undefined"
apply (unfold term_of_uval_def)
apply (simp)
done

paragraph {* Transfer Support for @{type utype} *}

definition cr_utype :: "'m::BASE_MODEL \<Rightarrow> 'm utype \<Rightarrow> bool" where
"cr_utype \<equiv> (\<lambda> x y . x = Rep_utype y)"

definition pcr_utype :: "'m::BASE_MODEL \<Rightarrow> 'm utype \<Rightarrow> bool" where
"pcr_utype \<equiv> (op =) OO cr_utype"

theorem pcr_cr_eq_utype :
"pcr_utype = cr_utype"
apply (unfold pcr_utype_def)
apply (simp add: eq_OO)
done

theorem right_total_utype [transfer_rule] :
"right_total pcr_utype"
apply (unfold pcr_utype_def)
apply (unfold cr_utype_def)
apply (unfold right_total_def)
apply (simp add: eq_OO)
done

theorem right_unique_utype [transfer_rule] :
"right_unique pcr_utype"
apply (unfold pcr_utype_def)
apply (unfold cr_utype_def)
apply (unfold right_unique_def)
apply (simp add: eq_OO)
apply (metis Rep_utype_inverse)
done

theorem bi_unique_utype [transfer_rule] :
"bi_unique pcr_utype"
apply (unfold pcr_utype_def)
apply (unfold cr_utype_def)
apply (unfold bi_unique_def)
apply (simp add: eq_OO)
apply (metis Rep_utype_inverse)
done

theorem rep_transfer_utype [transfer_rule] :
"fun_rel pcr_utype (op =) (\<lambda> x . x) Rep_utype"
apply (unfold pcr_utype_def)
apply (unfold cr_utype_def)
apply (unfold fun_rel_def)
apply (simp add: eq_OO)
done

theorem domain_utype :
"Domainp pcr_utype = (\<lambda> x . \<exists> y . x = y \<and> y \<in> UTYPE)"
apply (unfold pcr_utype_def)
apply (unfold cr_utype_def)
apply (simp add: eq_OO)
apply (rule ext)
apply (simp add: Domainp_iff)
apply (safe)
apply (metis Rep_utype)
apply (metis Rep_utype_cases)
done

theorem domain_eq_utype [transfer_domain_rule] :
"Domainp pcr_utype = (\<lambda> x . x \<in> UTYPE)"
apply (unfold domain_utype)
apply (simp)
done

theorem domain_par_utype [transfer_domain_rule] :
"Domainp (op =) = P1 \<Longrightarrow>
 fun_rel (op =) (op =) P2' (\<lambda> x . x \<in> UTYPE) \<Longrightarrow>
 Domainp pcr_utype = P1 \<sqinter> P2'"
apply (simp add: domain_utype)
apply (unfold fun_rel_def)
apply (simp add: fun_eq_iff)
apply (simp add: Domainp_iff)
done

theorem domain_par_left_total_utype [transfer_domain_rule] :
"fun_rel op = op = P' (\<lambda> x . x \<in> UTYPE) \<Longrightarrow> Domainp pcr_utype = P'"
apply (simp add: domain_utype)
apply (unfold fun_rel_def)
apply (simp add: fun_eq_iff)
done

theorem Quotient_utype :
"Quotient (Lifting.invariant (\<lambda> x . x \<in> UTYPE)) Abs_utype Rep_utype cr_utype"
apply (unfold Quotient_def)
apply (unfold Lifting.invariant_def)
apply (unfold cr_utype_def)
apply (safe)
apply (simp_all)
apply (metis Abs_utype_inverse)
apply (metis Abs_utype_cases Abs_utype_inverse)
done

text {* \fixme{Not sure the instantiation below is needed.} *}

instantiation utype :: (type) term_of
begin
definition term_of_utype :: "'a utype \<Rightarrow> term" where
"term_of_utype x = undefined"
instance
apply (intro_classes)
done
end

theorem term_of_utype_triv :
"term_of_class.term_of (t :: 'a utype) = undefined"
apply (unfold term_of_utype_def)
apply (simp)
done

subsection {* Countable Model *}

text {*
  The class @{text COUNTABLE_MODEL} adds the caveat that model types have to be
  countable. For such models, we automatically obtain that @{typ "'m utype"} is
  an instance of the class @{class countable}.
*}

class COUNTABLE_MODEL = BASE_MODEL +
  assumes countable_UTYPE [simp] : "countable UTYPE"

instantiation utype :: (COUNTABLE_MODEL) countable
begin
instance
apply (intro_classes)
apply (subgoal_tac "countable (UTYPE :: 'a set)")
-- {* Subgoal 1 *}
apply (unfold countable_def) [1]
apply (clarify)
apply (rule_tac x = "f o Rep_utype" in exI)
apply (rule comp_inj_on)
-- {* Subgoal 1.1 *}
apply (rule injI)
apply (metis Rep_utype_inject)
-- {* Subgoal 1.2 *}
apply (subgoal_tac "range Rep_utype = UTYPE")
apply (erule ssubst)
apply (assumption)
apply (rule type_definition.Rep_range)
apply (rule type_definition_utype)
-- {* Subgoal 2 *}
apply (rule countable_UTYPE)
done
end

text {* Countability also induces a linear order on types. *}

text {*
  \fixme{Perhaps we ought to give the user the choice of the order since the
  implicit order that derives from countability is not entirely useful as it
  cannot be practically evaluated.}
*}

instantiation utype :: (COUNTABLE_MODEL) linorder
begin
definition less_eq_utype :: "'a utype \<Rightarrow> 'a utype \<Rightarrow> bool" where
"less_eq_utype t1 t2 = ((to_nat t1) \<le> (to_nat t2))"
definition less_utype :: "'a utype \<Rightarrow> 'a utype \<Rightarrow> bool" where
"less_utype t1 t2 = ((to_nat t1) < (to_nat t2))"
instance
apply (intro_classes)
apply (unfold less_eq_utype_def less_utype_def)
apply (auto)
done
end

subsection {* Infinite Model *}

text {*
  The class @{text INFINITE_MODEL} adds the caveat that model types have
  infinite carriers. For such models, we automatically obtain that
  @{typ "'m utype"} is an instance of class @{class infinite}. Importantly,
  for models that are both countable and infinite, we can embed their types
  into arbitrary HOL types that are likewise countable and infinite as the
  cardinality in both cases is @{text "\<aleph>\<^sub>0"}.
*}

class INFINITE_MODEL = BASE_MODEL +
  assumes infinite_UTYPE [simp] : "infinite UTYPE"

instantiation utype :: (INFINITE_MODEL) infinite
begin
instance
apply (intro_classes)
apply (subgoal_tac "infinite (UTYPE :: 'a set)")
apply (metis (full_types) Rep_utype_cases finite_surj rangeI subsetI)
apply (simp)
done
end

subsection {* Defined Model *}

text {* The next layer introduces the notion of definedness. *}

class DEFINED_MODEL = BASE_MODEL +
-- {* Definedness notion for UTP values. *}
  fixes value_defined :: "'a uval \<Rightarrow> bool" ("\<D>\<^sub>v")
-- {* We assume the existence of at least one defined value. *}
  assumes defined_value_exists : "\<exists> v . \<D>\<^sub>v v"
begin

theorem value_defined_vacuous [simp] :
"is_total \<D>\<^sub>v \<Longrightarrow> \<D>\<^sub>v x"
apply (erule is_totalD)
done

subsubsection {* Defined Values *}

definition DVALUE :: "'a uval set" where
"DVALUE = {v . \<D>\<^sub>v v}"

theorem DVALUE_member [iff] :
"v \<in> DVALUE \<longleftrightarrow> \<D>\<^sub>v v"
apply (simp add: DVALUE_def)
done

theorem DVALUE_exists :
"\<exists> v . v \<in> DVALUE"
apply (simp)
apply (rule defined_value_exists)
done

theorem DVALUE_neq_empty :
"DVALUE \<noteq> {}"
apply (simp add: set_eq_iff)
apply (rule defined_value_exists)
done

theorem DVALUE_vacuous [simp] :
"is_total \<D>\<^sub>v \<Longrightarrow> DVALUE = UNIV"
apply (simp add: DVALUE_def)
done
end

subsubsection {* Instantiation as @{class DEFINED}. *}

instantiation uval :: (DEFINED_MODEL) DEFINED_NE
begin
definition defined_uval :: "'a uval \<Rightarrow> bool" where
"\<D> (x :: 'a uval) = \<D>\<^sub>v x"
instance
apply (intro_classes)
apply (unfold defined_uval_def)
apply (rule defined_value_exists)
done
end

declare defined_uval_def [simp]

subsection {* Pretyped Model *}

text {*
  The class @{text PRE_TYPED_MODEL} is useful in cases where we do not have a
  typing relation with the right properties yet but nevertheless like to make
  use of core definitions related to typed values. In the predicate model, it
  allows us to prove laws that hold irrespective of the non-emptiness property
  of types, for instance.
*}

text {*
  \todo{Perhaps review the need for this class once the HO model is fully in
  place; it would actually be nice to eradicate it.}
*}

class PRE_TYPED_MODEL = DEFINED_MODEL +
-- {* Typing relation of the model. *}
  fixes type_rel :: "'a uval \<Rightarrow> 'a utype \<Rightarrow> bool" (infix ":" 50)
begin

subsubsection {* Strict Typing *}

definition strict_type_rel ::
  "'a uval \<Rightarrow> 'a utype \<Rightarrow> bool" (infix ":!" 50) where
"v :! t \<longleftrightarrow> (v : t \<and> \<D>\<^sub>v v)"

declare strict_type_rel_def [iff]

theorem strict_type_rel_vacuous [simp] :
"is_total \<D>\<^sub>v \<Longrightarrow> op :! = op :"
apply (rule ext)+
apply (simp)
done

subsubsection {* Value of a Type *}

definition some_value :: "'a utype \<Rightarrow> 'a uval" where
"some_value t = (SOME v . v : t)"

definition some_defined_value :: "'a utype \<Rightarrow> 'a uval" where
"some_defined_value t = (SOME v . v : t \<and> \<D>\<^sub>v v)"

subsubsection {* Type of a Value *}

definition utype_of :: "'a uval \<Rightarrow> 'a utype" where
"utype_of v = (SOME t . v : t)"

subsubsection {* Carrier Sets *}

definition carrier :: "'a utype \<Rightarrow> 'a uval set" where
"carrier t = {v . v : t}"

definition dcarrier :: "'a utype \<Rightarrow> 'a uval set" where
"dcarrier t = {v . v :! t}"

subsubsection {* Values Restricted to Types *}

definition VALUES :: "'a utype set \<Rightarrow> 'a uval set" where
"VALUES ts = \<Union> (carrier ` ts)"

theorem VALUES_member [iff] :
"v \<in> VALUES ts \<longleftrightarrow> (\<exists> t \<in> ts . v : t)"
apply (unfold VALUES_def)
apply (simp)
apply (unfold carrier_def)
apply (simp)
done
end

subsubsection {* Type Binders *}

default_sort PRE_TYPED_MODEL

definition Tall :: "'m utype \<Rightarrow> ('m uval \<Rightarrow> bool) \<Rightarrow> bool" where
"Tall t P \<equiv> (\<forall> x . x : t \<longrightarrow> P x)"

definition Tex :: "'m utype \<Rightarrow> ('m uval \<Rightarrow> bool) \<Rightarrow> bool" where
"Tex t P \<equiv> (\<exists> x . x : t \<and> P x)"

definition DTall :: "'m utype \<Rightarrow> ('m uval \<Rightarrow> bool) \<Rightarrow> bool" where
"DTall t P \<equiv> (\<forall> x . x :! t \<longrightarrow> P x)"

definition DTex :: "'m utype \<Rightarrow> ('m uval \<Rightarrow> bool) \<Rightarrow> bool" where
"DTex t P \<equiv> (\<exists> x . x :! t \<and> P x)"

syntax
  "_Tall" :: "pttrn \<Rightarrow> 'm utype \<Rightarrow> bool \<Rightarrow> bool" ("(3\<forall>_ : _./ _)" [0, 0, 10] 10)
  "_Tex" :: "pttrn \<Rightarrow> 'm utype \<Rightarrow> bool => bool" ("(3\<exists>_ : _./ _)" [0, 0, 10] 10)
  "_DTall" :: "pttrn \<Rightarrow> 'm utype => bool => bool" ("(3\<forall>_ :! _./ _)" [0, 0, 10] 10)
  "_DTex" :: "pttrn => 'm utype => bool => bool" ("(3\<exists>_ :! _./ _)" [0, 0, 10] 10)

default_sort type

translations
  "\<forall> x : t . P" \<rightleftharpoons> "(CONST Tall) t (\<lambda> x . P)"
  "\<exists> x : t . P" \<rightleftharpoons> "(CONST Tex) t (\<lambda> x . P)"
  "\<forall> x :! t . P" \<rightleftharpoons> "(CONST DTall) t (\<lambda> x . P)"
  "\<exists> x :! t . P" \<rightleftharpoons> "(CONST DTex) t (\<lambda> x . P)"

-- {* Avoid eta-contraction for a more robust  pretty-printing. *}

print_translation {*
 [Syntax_Trans.preserve_binder_abs2_tr'
   @{const_syntax Tall} @{syntax_const "_Tall"}]
*}

print_translation {*
 [Syntax_Trans.preserve_binder_abs2_tr'
   @{const_syntax Tex} @{syntax_const "_Tex"}]
*}

print_translation {*
 [Syntax_Trans.preserve_binder_abs2_tr'
   @{const_syntax DTall} @{syntax_const "_DTall"}]
*}

print_translation {*
 [Syntax_Trans.preserve_binder_abs2_tr'
   @{const_syntax DTex} @{syntax_const "_DTex"}]
*}

declare Tall_def [simp]
declare Tex_def [simp]
declare DTall_def [simp]
declare DTex_def [simp]

subsection {* Typed Model *}

text {*
  The two fundamental properties of typing are that types are non-empty and
  that every defined value belongs to some type. We do not, however, preclude
  type systems in which values may belong to more than one type. Stronger
  constraints are imposed, for instance, in @{text MONO_TYPED_MODEL}s where
  values indeed must inhabit a single type.
*}

class TYPED_MODEL = PRE_TYPED_MODEL +
-- {* Every type includes at least one defined value. *}
  assumes types_non_empty : "\<exists> v . v : t \<and> \<D>\<^sub>v v"
-- {* Every defined value inhabits at least one type. *}
  assumes all_values_typed : "\<D>\<^sub>v v \<Longrightarrow> \<exists> t . v : t"
begin

subsubsection {* Well-typed Values *}

definition WT_VALUE :: "'a uval set" where
"WT_VALUE = \<Union> (dcarrier ` UNIV)"

theorem WT_VALUE_member [iff] :
"v \<in> WT_VALUE \<longleftrightarrow> (\<exists> t . v :! t)"
apply (unfold WT_VALUE_def)
apply (unfold image_def)
apply (unfold dcarrier_def)
apply (unfold strict_type_rel_def)
apply (auto)
done

subsubsection {* Theorems *}

paragraph {* Value of a Type *}

theorem some_value_typed [typing] :
"(some_value t) : t"
apply (unfold some_value_def)
apply (rule someI_ex)
apply (insert types_non_empty [of "t"])
apply (clarify)
apply (rule_tac x = "v" in exI)
apply (assumption)
done

theorem some_defined_value_defined [defined] :
"\<D>\<^sub>v (some_defined_value t)"
apply (unfold some_defined_value_def)
apply (insert types_non_empty [of "t"])
apply (clarify)
apply (rule_tac a = "v" in someI2)
apply (simp_all)
done

theorem some_defined_value_typed [typing] :
"(some_defined_value t) : t"
apply (unfold some_defined_value_def)
apply (insert types_non_empty [of "t"])
apply (clarify)
apply (rule_tac a = "v" in someI2)
apply (simp_all)
done

theorem some_defined_value_strictly_typed [typing] :
"(some_defined_value t) :! t"
apply (unfold strict_type_rel_def)
apply (rule conjI)
apply (rule some_defined_value_typed)
apply (rule some_defined_value_defined)
done

paragraph {* Type of a Value *}

theorem utype_of_typed [typing] :
"\<D>\<^sub>v v \<Longrightarrow> v : (utype_of v)"
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
"is_total \<D>\<^sub>v \<Longrightarrow> dcarrier = carrier"
apply (rule ext)
apply (rename_tac t)
apply (rule Set.set_eqI)
apply (simp)
done
end

subsection {* Monotyped Model *}

definition monotype :: "'a::PRE_TYPED_MODEL utype \<Rightarrow> bool" where
"monotype t \<longleftrightarrow> (\<forall> v t' . v : t \<and> v : t' \<longrightarrow> t = t')"

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

definition the_utype_of :: "'a uval \<Rightarrow> 'a utype" where
"the_utype_of v = (THE t . v : t)"

theorem utype_of_value_unique :
"\<D>\<^sub>v v \<Longrightarrow> utype_of v = the_utype_of v"
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

theorems the_utype_of_value_simp [simp] =
  sym [OF utype_of_value_unique]
end

subsection {* Miscellaneous *}

subsubsection {* Compatibility *}

text {* \todo{Discuss with Simon whether to keep @{text default}.} *}

syntax "_default" :: "'a utype \<Rightarrow> 'a uval" ("default")

translations "default t" \<rightharpoonup> "(CONST some_defined_value) t"

(***********************)
(* REVIEWED UNTIL HERE *)
(***********************)

subsubsection {* Sigma Types *}

text {* \todo{This section needs a review and some more work.} *}

text {* \fixme{Why did Simon not use a set of values? Clarify!} *}

typedef 'm::TYPED_MODEL sigtype =
  "{(t :: 'm utype, v :: 'm uval). v : t}"
apply (clarsimp)
apply (metis split_conv types_non_empty)
done

declare Abs_sigtype_inverse [simp]
declare Rep_sigtype_inverse [simp]
declare Rep_sigtype [simp]

setup_lifting type_definition_sigtype

default_sort TYPED_MODEL

abbreviation Abs_sigtype_syntax ::
  "'m uval \<Rightarrow> 'm utype \<Rightarrow> 'm sigtype" ("(\<Sigma> _ : _)" [50] 50) where
"\<Sigma> x : t \<equiv> Abs_sigtype (t, x)"

lemma Rep_sigtype_intro [intro!] :
"Rep_sigtype x = Rep_sigtype y \<Longrightarrow> x = y"
  by (simp add: Rep_sigtype_inject)

lift_definition sigtype :: "'m sigtype \<Rightarrow> 'm utype"
is "fst" by (simp)

lift_definition sigvalue :: "'m sigtype \<Rightarrow> 'm uval"
is "snd" by (simp)

lemma sigtype [simp] :
"x : t \<Longrightarrow> sigtype (\<Sigma> x : t) = t"
apply (simp add: sigtype.rep_eq)
done

lemma sigvalue [simp] :
"x : t \<Longrightarrow> sigvalue (\<Sigma> x : t) = x"
apply (simp add: sigvalue.rep_eq)
done

lemma sigvalue_typed [typing] :
"sigvalue x : sigtype x"
apply (insert Rep_sigtype [of x])
apply (auto simp add: sigvalue.rep_eq sigtype.rep_eq)
done

default_sort type
end
