(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utp_constants.thy                                                    *)
(* Authors: Simon Foster & Frank Zeyda, University of York (UK)               *)
(******************************************************************************)
(* LAST REVIEWED: 2 September 2014 *)

header {* Overloaded Constants *}

theory utp_constants
imports Main Adhoc_Overloading
begin

default_sort type

text {* The following constants are used for ad hoc overloading. *}

text {* \todo{Is this list complete? Add some explanation!} *}

text {* \todo{Can the types be further refined? Review their names.} *}

consts
  alphabet :: "'r \<Rightarrow> 'a" ("\<alpha>")
  alpha_coerce :: "'p \<Rightarrow> 'a \<Rightarrow> 'q" ("_\<^bsub>!_\<^esub>" [1000, 0] 1000)
  prime :: "'a \<Rightarrow> 'a" ("_\<acute>" [1000] 1000)
  unprime :: "'a \<Rightarrow> 'a" ("_~" [1000] 1000)
  subscr :: "'a \<Rightarrow> string \<Rightarrow> 'a" ("_\<^bsub>_\<^esub>" [1000, 0] 1000)
  REL :: "'a set"
  COND :: "'a set"
  POST :: "'a set"
end
