(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utp_synonyms.thy                                                     *)
(* Authors: Simon Foster & Frank Zeyda, University of York (UK)               *)
(******************************************************************************)
(* LAST REVIEWED: 15 July 2014 *)

header {* Type Synonyms *}

theory utp_synonyms
imports utp_name utp_var
begin

default_sort type

text {* This theory defines type synonyms for various semantic domains. *}

type_synonym 'a alpha = "('a uvar) fset"

(*
type_synonym 'm BINDING =
  "('m uvar) \<Rightarrow> 'VALUE"

type_synonym 'm BINDING_SET =
  "'m BINDING set"

type_synonym 'm BINDING_PRED =
  "'m BINDING \<Rightarrow> bool"

type_synonym 'm BINDING_FUN =
  "'m BINDING \<Rightarrow> 'm uval"

type_synonym 'm PREDICATE =
  "'m BINDING_SET"

type_synonym 'm FUNCTION =
  "'m PREDICATE \<Rightarrow>
   'm PREDICATE"

type_synonym 'm ALPHA_PREDICATE =
  "('m alpha) \<times> 'm PREDICATE"
*)
end
