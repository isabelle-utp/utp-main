(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: flat_orders.thy                                                      *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 16 Jan 2016 *)

section {* Flat Orders *}

theory flat_orders
imports Main
keywords "flat_order" :: thy_decl
begin

text {* This theory adds a command to instantiate a flat order on a type. *}

subsection {* Command @{command flat_order} *}

ML_file "flat_orders.ML"

text {* The following configures the @{command flat_order} command. *}

ML {*
  Outer_Syntax.command @{command_keyword flat_order} "instantiate flat order"
    (Parse.type_const >> (Toplevel.theory o Flat_Order.flat_order));
*}
end