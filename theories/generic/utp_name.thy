(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/generic/utp_name.thy                                             *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Variable Names *}

theory utp_name
imports "../utp_common"
begin

subsection {* Subscripts *}

text {* Subscripts are encoded by virtue of a data type. *}

datatype SUBSCRIPT =
  Sub "nat" | NoSub

subsection {* Name Type *}

text {* A record type is used to encode names. *}

record SIMPLE_NAME =
  name_str::"string"
  subscript::"SUBSCRIPT"

record NAME = SIMPLE_NAME +
  dashes::"nat"

subsection {* Restrictions *}

text {* We only consider substitutions that are permutations. *}

definition NAME_SUBST :: "(NAME \<Rightarrow> NAME) \<Rightarrow> bool" where
"NAME_SUBST = bij"
end
