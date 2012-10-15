(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_global.thy                                                       *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Global Syntax *}

theory utp_global
imports utp_common "./core/utp_synonyms"
begin

text {* This theory introduces generic constants for global syntax. *}

subsection {* Value Syntax *}

consts global_type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool"
notation global_type_rel (infix ":" 50)

consts global_set_type_rel :: "'VALUE set \<Rightarrow> 'TYPE \<Rightarrow> bool"
notation global_set_type_rel (infix ":\<subseteq>" 50)

subsection {* Predicate Syntax *}

end
