(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utype.thy                                                            *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 16 Jan 2016 *)

section {* Universal Types *}

theory utype
imports "../ucommon"
begin

text {* We are going to use the colon for model typing. *}

no_notation
  Set.member ("op :") and
  Set.member ("(_/ : _)" [51, 51] 50)

default_sort typerep

subsection {* Unified Types *}

text {*
  We use Isabelle's @{typ typerep} mechanism to encode UTP model types. This
  avoids having to fix the UTP type model upfront and thereby renders it open
  for extension by the user. A downside of this approach is that there exist
  @{type typerep} objects that do not correspond to permissible types in any
  UTP model, as they may not be injectable into our unified value model.
*}

type_synonym utype = "typerep"

translations (type) "utype" \<leftharpoondown> (type) "typerep"

subsection {* Type Syntax *}

text {* @{text "UTYPE('a)"} is synonymous to @{text "TYPEREP('a)"}. *}

syntax "_UTYPE" :: "type \<Rightarrow> typerep" ("UTYPE'(_')")

translations "UTYPE('a)" \<rightleftharpoons> (* \<rightharpoonup> *) "TYPEREP('a)"

subsection {* Polymorphic Typing *}

definition p_type_rel :: "'a \<Rightarrow> utype \<Rightarrow> bool" (infix ":" 50) where
[typing]: "x : t \<longleftrightarrow> UTYPE('a) = t"

subsection {* Proof Support *}

text {*
  The subsequent interpretation for type definitions automatically collects
  @{class typerep} theorems in the theorem attribute @{text typing}. Hence,
  the user does not have to worry about collecting them manually for any of
  the existing or newly-defined HOL types. The @{text typing} attribute is
  generally useful to facilitate proofs about model typing.
*}

ML_file "../utils/Typerep_Collect.ML"

setup {*
  (Typedef.interpretation
    (Local_Theory.background_theory o Typerep_Collect.collect_typerep_thm))
*}

thm typing

text {*
  The following are not collected by the interpretation above as they are
  ground types; we hence add them manually.
*}

declare typerep_bool_def [typing]
declare typerep_ind_def [typing]
declare typerep_fun_def [typing]
declare typerep_set_def [typing]

subsection {* Experiments *}

text {* The next shows that all typing theorems have been collected. *}

thm typing

text {* The examples in the sequel illustrates reasoning about types. *}

theorem "(1::nat) : UTYPE(nat)"
apply (simp add: typing)
done

theorem "1 : UTYPE(nat)"
apply (simp add: typing)
oops

theorem "\<not> (1::nat) : UTYPE(int)"
apply (simp add: typing)
done

theorem "(x::'a) : UTYPE('a)"
apply (simp add: typing)
done

theorem "{1::nat} : UTYPE('a set)"
apply (simp add: typing)
oops

theorem "{1::nat} : UTYPE(nat set)"
apply (simp add: typing)
done

theorem "{1} : UTYPE('a set)"
apply (simp add: typing)
oops

theorem "{1::('a::{numeral,typerep})} : UTYPE('a set)"
apply (simp add: typing)
done
end