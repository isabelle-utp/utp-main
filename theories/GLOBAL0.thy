(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/GLOBAL0.thy                                                      *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Global Value Syntax *}

theory GLOBAL0
imports utp_common utp_types
begin

text {* This theory introduces generic constants for global syntax. *}

consts type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50)

consts set_type_rel :: "'VALUE set \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":\<subseteq>" 50)
end
