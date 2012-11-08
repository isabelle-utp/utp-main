(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_ho_prog.thy                                                      *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* HO Programs *}

theory utp_ho_prog
imports utp_ho_value utp_ho_model
begin

text {*
  Up to this point we have treated the @{text PROG_VALUE} type as given.
  Here, we provide the morphisms that endow this type with a model, namely in
  terms of @{const HO_ALPHA_PREDICATE}. This requires a custom axiomatisation
  of the type morphisms and questions of consistency may be raised because of
  that. I believe though that the axioms are in fact consistent due to the
  restrictions imposed by the notion of types in HO predicates. However, the
  construction of a formal argument and proof is still on-going work.
*}

subsection {* Type Morphisms *}

text {*
  The definition of morphisms requires a leap of faith. That is, we have to
  trust their axiomatisation is sound. I have minor doubts this can be shown
  within HOL but we ought to be able to construct a meta-logical argument.
  Such an argument, I think, would aim to establish the existence of a fixed
  cardinality bound on @{text "HO_ALPHA_PREDICATE"} that is independent of
  the cardinality of @{text "HO_VALUE"} (presumably some limit cardinal).
*}

axiomatization
  Abs_PROG_VALUE :: "(HO_VALUE, HO_TYPE) ALPHA_PREDICATE \<Rightarrow> PROG_VALUE" and
  Rep_PROG_VALUE :: "PROG_VALUE \<Rightarrow> (HO_VALUE, HO_TYPE) ALPHA_PREDICATE" where
PROG_VALUE_type_definition :
  "type_definition Rep_PROG_VALUE Abs_PROG_VALUE HO_ALPHA_PREDICATE" and
-- {* Typing of HO predicates gets its full meaning with the axiom below. *}
ProgAlpha [simp] : "ProgAlpha p \<equiv> \<alpha> (Rep_PROG_VALUE p)"

text {* The interpretation below gives us all the standard typedef laws. *}

interpretation PROG_VALUE :
  type_definition
    "Rep_PROG_VALUE"
    "Abs_PROG_VALUE"
    "HO_ALPHA_PREDICATE"
apply (simp add: PROG_VALUE_type_definition)
done

text {* Default Simplifications *}

declare PROG_VALUE.Abs_inverse [simp]
declare PROG_VALUE.Abs_inject [simp, intro!]
declare PROG_VALUE.Rep_inverse [simp]
declare PROG_VALUE.Rep_inject_sym [simp]
declare PROG_VALUE.Rep [simp]

subsection {* Theorems *}

text {*
  We are finally in a position to prove that HO values meet the assumptions of
  the @{text VALUE} locale. This paves the way for instantiating the core model
  for alphabetised predicates with the higher-order value and type domains.
*}

theorem VALUE_prog_type [simp] :
"VALUE prog_type_rel"
apply (unfold_locales)
apply (rule_tac x = "Abs_PROG_VALUE (set t, {})" in exI)
apply (simp)
apply (subgoal_tac "(set t, {}) \<in> HO_ALPHA_PREDICATE")
apply (simp)
apply (simp add: HO_ALPHA_PREDICATE_def)
apply (rule conjI)
-- {* Subgoal 1 *}
apply (simp add: HO_ALPHABET_def VAR.WF_ALPHABET_def)
-- {* Subgoal 2 *}
apply (simp add: HO_PREDICATE_OVER_def)
apply (simp add: HO_PREDICATE_def HO_UNREST_def)
done
end