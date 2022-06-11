(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: flat_orders.thy                                                      *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Flat Orders\<close>

theory flat_orders
imports Main
keywords "flat_order" :: thy_decl
begin

text \<open>This theory adds a command to instantiate a flat order on a type.\<close>

subsection \<open>Command @{command flat_order}\<close>

ML_file "flat_orders.ML"

text \<open>The following configures the @{command flat_order} command.\<close>

ML \<open>
  Outer_Syntax.command @{command_keyword flat_order} "instantiate flat order"
    (Parse.type_const >> (Toplevel.theory o Flat_Order.flat_order));
\<close>

end