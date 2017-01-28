(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utheory.thy                                                          *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 26 Jan 2016 *)

section {* UTP Theories *}

theory utheory
imports "../meta/ucore"
begin

subsection {* Healthiness Functions *}

subsubsection {* Type Synonym *}

type_synonym hcond = "upred \<Rightarrow> upred"

subsubsection {* Healthiness Property *}

definition is_healthy :: "upred \<Rightarrow> hcond \<Rightarrow> bool" (infix "is" 50) where
"p is H \<longleftrightarrow> H p = p"

declare is_healthy_def [evalp]
end