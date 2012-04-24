(******************************************************************************)
(* Title: utp/generic/utp_name.thy                                            *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory utp_name
imports "../utp_common"
begin

section {* Variable Names *}

subsection {* Encoding of Subscripts *}

datatype SUBSCRIPT =
  Sub "nat" | NoSub

subsection {* Encoding of Names *}

record NAME =
  name_str::"string"
  dashes::"nat"
  subscript::"SUBSCRIPT"

subsection {* Restrictions *}

definition NAME_SUBST :: "(NAME \<Rightarrow> NAME) set" where
"NAME_SUBST = bij"
end
