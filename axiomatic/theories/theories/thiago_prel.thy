(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: thiago_prel.thy                                                      *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 26 Jan 2016 *)

section {* Relational Extras *}

theory thiago_prel
imports "../ucommon"
begin

hide_type Relation.rel

subsection {* Notation *}

notation Domain ("dom")
notation Range ("ran")

subsection {* Type Synonym *}

type_synonym ('a, 'b) rel = "('a \<times> 'b) set"

translations (type) "('a, 'b) rel" \<leftharpoondown> (type) "('a \<times> 'b) set"

subsection {* Relational Application *}

definition rel_app :: "('a, 'b) rel \<Rightarrow> 'a \<Rightarrow> 'b" where
"rel_app r x = (THE y. (x, y) \<in> r)"

notation rel_app ("(_\<cdot>/_)" [101, 101] 100)
end