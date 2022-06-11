(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utype.thy                                                            *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Universal Types\<close>

theory utype
imports "../ucommon"
begin

text \<open>We are going to use the colon for model typing.\<close>

no_notation (ASCII)
  Set.member  ("'(:')") and
  Set.member  ("(_/ : _)" [51, 51] 50)

default_sort typerep

subsection \<open>Unified Types\<close>

text \<open>
  We use Isabelle's @{typ typerep} mechanism to encode UTP model types. This
  avoids having to fix the UTP type model upfront and thereby renders it open
  for extension by the user. A downside of this approach is that there exist
  @{type typerep} objects that do not correspond to permissible types in any
  UTP model, as they may not be injectable into our unified value model.
\<close>

type_synonym utype = "typerep"

translations (type) "utype" \<leftharpoondown> (type) "typerep"

subsection \<open>Type Syntax\<close>

text \<open>@{text "UTYPE('a)"} is synonymous to @{text "TYPEREP('a)"}.\<close>

syntax "_UTYPE" :: "type \<Rightarrow> typerep" ("UTYPE'(_')")

translations "UTYPE('a)" \<rightleftharpoons> (* \<rightharpoonup> *) "TYPEREP('a)"

subsection \<open>Polymorphic Typing\<close>

definition p_type_rel :: "'a \<Rightarrow> utype \<Rightarrow> bool" (infix ":" 50) where
[typing]: "x : t \<longleftrightarrow> UTYPE('a) = t"

subsection \<open>Proof Support\<close>

text \<open>
  The subsequent interpretation for type definitions automatically collects
  @{class typerep} theorems in the theorem attribute @{text typing}. Hence,
  the user does not have to worry about collecting them manually for any of
  the existing or newly-defined HOL types. The @{text typing} attribute is
  generally useful to facilitate proofs about model typing.
\<close>

ML_file "../utils/Typerep_Collect.ML"

text \<open>\todo{The below fails to collect the typerep theorem for @{type String.literal}?}\<close>

setup \<open>
  (Typedef.interpretation
    (Local_Theory.background_theory o Typerep_Collect.collect_typerep_thm))
\<close>

text \<open>
  The following are not collected by the interpretation above as they are
  ground types; we hence add them manually.
\<close>

declare typerep_bool_def [typing]
declare typerep_ind_def [typing]
declare typerep_fun_def [typing]
declare typerep_set_def [typing]

subsection \<open>Experiments\<close>

text \<open>The next shows that all typing theorems have been collected.\<close>

thm typing

text \<open>The examples in the sequel illustrates reasoning about types.\<close>

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