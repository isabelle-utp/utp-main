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

types 'TYPE VAR =
  "NAME \<times> 'TYPE"

types 'TYPE ALPHABET =
  "('TYPE VAR) set"

types ('VALUE, 'TYPE) BINDING =
  "('TYPE VAR) \<Rightarrow> 'VALUE"

types ('VALUE, 'TYPE) BINDING_SET =
  "('VALUE, 'TYPE) BINDING set"

types ('VALUE, 'TYPE) BINDING_BFUN =
  "('VALUE, 'TYPE) BINDING \<Rightarrow> bool"

types ('VALUE, 'TYPE) BINDING_FUN =
  "('VALUE, 'TYPE) BINDING \<Rightarrow> 'VALUE"

types ('VALUE, 'TYPE) PREDICATE =
  "('VALUE, 'TYPE) BINDING_SET"

types ('VALUE, 'TYPE) FUNCTION =
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE"

types ('VALUE, 'TYPE) ALPHA_PREDICATE =
  "('TYPE ALPHABET) \<times> ('VALUE, 'TYPE) PREDICATE"

types ('VALUE, 'TYPE) ALPHA_FUNCTION =
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE"
end