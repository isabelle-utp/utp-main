(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: udefault.thy                                                         *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 18 Jan 2016 *)

section {* Default Injections *}

theory udefaults
imports uval
begin
inject_type unit
inject_type bool
inject_type nat
inject_type int
inject_type char
inject_type real
inject_type "fun"
inject_type set
inject_type list
inject_type prod
inject_type sum
inject_type option
end