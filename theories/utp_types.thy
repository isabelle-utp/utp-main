(******************************************************************************)
(* Title: utp/utp_types.thy                                                   *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory utp_types
imports utp_common "generic/utp_name"
begin

section {* Type Synonyms *}

types 'TYPE VAR = "NAME \<times> 'TYPE"

types 'TYPE ALPHABET =
  "('TYPE VAR) set"

types ('VALUE, 'TYPE) BINDING =
  "('TYPE VAR) \<Rightarrow> 'VALUE"

types ('VALUE, 'TYPE) BINDING_SET =
  "('VALUE, 'TYPE) BINDING set"

types ('VALUE, 'TYPE) BINDING_FUN =
  "('VALUE, 'TYPE) BINDING \<Rightarrow> bool"

types ('VALUE, 'TYPE) ALPHA_PREDICATE =
  "('TYPE ALPHABET) \<times> ('VALUE, 'TYPE) BINDING set"

types ('VALUE, 'TYPE) ALPHA_FUNCTION =
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE"
end