(******************************************************************************)
(* Project: Unifying Theories of Programming in Isabelle/HOL                  *)
(* File: utp_constants.thy                                                    *)
(* Author: Simon Foster & Frank Zeyda, University of York (UK)                *)
(******************************************************************************)

header {* Overloaded Constants *}

theory utp_constants
imports Main
begin

default_sort type

text {* Ad-hoc overloading allows the binding of symbols to multiple constructs. *}

consts
  alphabet     :: "'r \<Rightarrow> 'a" ("\<alpha>")
  alpha_coerce :: "'p \<Rightarrow> 'a \<Rightarrow> 'q" ("_\<^bsub>!_\<^esub>" [1000, 0] 1000)
  prime        :: "'a \<Rightarrow> 'a" ("_\<acute>" [1000] 1000)
  unprime      :: "'a \<Rightarrow> 'a" ("_~" [1000] 1000)
  subscr       :: "'a \<Rightarrow> string \<Rightarrow> 'a" ("_\<^bsub>_\<^esub>")
  REL          :: "'a set"
  COND         :: "'a set"
  POST         :: "'a set"
end
