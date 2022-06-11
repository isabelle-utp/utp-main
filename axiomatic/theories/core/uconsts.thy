(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: uconst.thy                                                           *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Polymorphic Constants\<close>

theory uconsts
imports "../ucommon"
begin

text \<open>We are going to use the converse symbol for undashing.\<close>

no_notation
  converse  ("(_\<inverse>)" [1000] 999)

subsection \<open>Constants for Ad-hoc Overloading\<close>

text \<open>The following constants are used for \textit{ad hoc} overloading.\<close>

consts
  UNDASHED :: "'a set"
  DASHED :: "'a set"
  dash :: "'a \<Rightarrow> 'a" ("_\<acute>" [1000] 1000)
  undash :: "'a \<Rightarrow> 'a" ("_\<inverse>" [1000] 1000)
  subscr :: "'a \<Rightarrow> string \<Rightarrow> 'a" ("_\<^bsub>_\<^esub>" [1000, 0] 1000)

subsection \<open>Derived Definitions\<close>

abbreviation NON_REL_VAR :: "'a set" where
"NON_REL_VAR \<equiv> -(UNDASHED \<union> DASHED)"
end