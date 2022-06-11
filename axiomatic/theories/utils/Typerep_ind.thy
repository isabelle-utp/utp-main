(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: Typerep_ind.thy                                                      *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Typerep of @{text Nat.ind}\<close>

theory Typerep_ind
imports Main
begin

text \<open>
  By default, Isabelle/HOL does not instantiate class @{class typerep} for the
  @{type ind} type. We do so in this theory.
\<close>

instantiation ind :: typerep
begin
definition typerep_ind :: "ind itself \<Rightarrow> typerep" where
"typerep_ind t = Typerep.Typerep (STR ''Nat.ind'') []"
instance by (intro_classes)
end
end