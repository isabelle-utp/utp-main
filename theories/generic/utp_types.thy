(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_types.thy                                                        *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Type Synonyms *}

theory utp_types
imports utp_names
begin

text {* This theory defines type synonyms for the various semantic domains. *}

type_synonym 'TYPE VAR =
  "NAME \<times> 'TYPE"

type_synonym 'TYPE ALPHABET =
  "('TYPE VAR) set"

type_synonym ('VALUE, 'TYPE) BINDING =
  "('TYPE VAR) \<Rightarrow> 'VALUE"

type_synonym ('VALUE, 'TYPE) BINDING_SET =
  "('VALUE, 'TYPE) BINDING set"

type_synonym ('VALUE, 'TYPE) BINDING_BFUN =
  "('VALUE, 'TYPE) BINDING \<Rightarrow> bool"

type_synonym ('VALUE, 'TYPE) BINDING_FUN =
  "('VALUE, 'TYPE) BINDING \<Rightarrow> 'VALUE"

type_synonym ('VALUE, 'TYPE) PREDICATE =
  "('VALUE, 'TYPE) BINDING_SET"

type_synonym ('VALUE, 'TYPE) FUNCTION =
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE"

type_synonym ('VALUE, 'TYPE) ALPHA_PREDICATE =
  "('TYPE ALPHABET) \<times> ('VALUE, 'TYPE) PREDICATE"

type_synonym ('VALUE, 'TYPE) ALPHA_FUNCTION =
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE"
end