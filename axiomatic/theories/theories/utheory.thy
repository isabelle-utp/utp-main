(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utheory.thy                                                          *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>UTP Theories\<close>

theory utheory
imports "../meta/ucore"
begin

subsection \<open>Healthiness Functions\<close>

subsubsection \<open>Type Synonym\<close>

type_synonym hcond = "upred \<Rightarrow> upred"

subsubsection \<open>Healthiness Property\<close>

definition is_healthy :: "upred \<Rightarrow> hcond \<Rightarrow> bool" (infix "is" 50) where
"p is H \<longleftrightarrow> H p = p"

declare is_healthy_def [evalp]

end