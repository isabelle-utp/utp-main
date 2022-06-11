(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: thiago_prel.thy                                                      *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Relational Extras\<close>

theory thiago_prel
imports "../ucommon"
begin

hide_type Relation.rel

subsection \<open>Notation\<close>

notation Domain ("dom")
notation Range ("ran")

subsection \<open>Type Synonym\<close>

type_synonym ('a, 'b) rel = "('a \<times> 'b) set"

translations (type) "('a, 'b) rel" \<leftharpoondown> (type) "('a \<times> 'b) set"

subsection \<open>Relational Application\<close>

definition rel_app :: "('a, 'b) rel \<Rightarrow> 'a \<Rightarrow> 'b" where
"rel_app r x = (THE y. (x, y) \<in> r)"

notation rel_app ("(_\<cdot>/_)" [101, 101] 100)
end