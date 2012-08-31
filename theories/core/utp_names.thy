(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_names.thy                                                        *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Variable Names *}

theory utp_names
imports "../utp_common"
begin

subsection {* Subscripts *}

text {* Subscripts are encoded by virtue of a datatype. *}

datatype SUBSCRIPT = Sub "nat" | NoSub

subsection {* Names *}

text {* A record type is used to encode names. *}

record NAME =
  name_str::"string"
  dashes::"nat"
  subscript::"SUBSCRIPT"

subsection {* Restrictions *}

text {* We only consider substitutions that are permutations. *}

definition NAME_SUBST :: "(NAME \<Rightarrow> NAME) \<Rightarrow> bool" where
"NAME_SUBST = bij"
end