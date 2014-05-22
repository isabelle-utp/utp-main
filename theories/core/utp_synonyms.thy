(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_synonyms.thy                                                        *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Type Synonyms *}

theory utp_synonyms
imports utp_names utp_var
begin

text {* This theory defines type synonyms for the various semantic domains. *}

type_synonym 'a alpha =
  "('a uvar) fset"

type_synonym 'VALUE BINDING =
  "('VALUE uvar) \<Rightarrow> 'VALUE"

type_synonym 'VALUE BINDING_SET =
  "'VALUE  BINDING set"

type_synonym 'VALUE BINDING_PRED =
  "'VALUE BINDING \<Rightarrow> bool"

type_synonym 'VALUE BINDING_FUN =
  "'VALUE BINDING \<Rightarrow> 'VALUE"

type_synonym 'VALUE PREDICATE =
  "'VALUE BINDING_SET"

type_synonym 'VALUE FUNCTION =
  "'VALUE PREDICATE \<Rightarrow>
   'VALUE PREDICATE"

type_synonym 'VALUE ALPHA_PREDICATE =
  "('VALUE alpha) \<times> 'VALUE PREDICATE"

end
