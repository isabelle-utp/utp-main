(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: uconst.thy                                                           *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 16 Jan 2016 *)

section {* Polymorphic Constants *}

theory uconsts
imports "../ucommon"
begin

text {* We are going to use the converse symbol for undashing. *}

no_notation
  converse  ("(_\<inverse>)" [1000] 999)

subsection {* Constants for Ad-hoc Overloading *}

text {* The following constants are used for \textit{ad hoc} overloading. *}

consts
  UNDASHED :: "'a set"
  DASHED :: "'a set"
  dash :: "'a \<Rightarrow> 'a" ("_\<acute>" [1000] 1000)
  undash :: "'a \<Rightarrow> 'a" ("_\<inverse>" [1000] 1000)
  subscr :: "'a \<Rightarrow> string \<Rightarrow> 'a" ("_\<^bsub>_\<^esub>" [1000, 0] 1000)

subsection {* Derived Definitions *}

abbreviation NON_REL_VAR :: "'a set" where
"NON_REL_VAR \<equiv> -(UNDASHED \<union> DASHED)"
end