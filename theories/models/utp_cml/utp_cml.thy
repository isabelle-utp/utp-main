(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: utp_cml.thy                                                          *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

theory utp_cml
imports
  utp_cml_values
  utp_cml_inject
  utp_cml_sorts
  utp_cml_expr
  utp_cml_laws
  utp_cml_monad
  utp_cml_tac
  utp_cml_types
  utp_cml_functions
  utp_cml_records
  utp_cml_process
begin 

text {* Remove syntax which will likely clash *}

hide_const "SUB"
hide_const "floor"

no_notation
  J_pred ("J") and
  relcomp (infixr "O" 75)

(* Remove standard HOL arithmetic operators *)

no_notation
  plus (infixl "+" 65) and
  minus (infixl "-" 65) and
  times (infixl "*" 70) and
  uminus ("- _" [81] 80) and
  divide (infixl "'/" 70) and
  Groups.zero ("0") and
  greater_eq  (infix ">=" 50) and
  greater  (infix ">" 50) and
  less_eq  ("op <=") and
  less_eq  ("(_/ <= _)" [51, 51] 50) and
  less  ("op <") and
  less  ("(_/ < _)"  [51, 51] 50)

no_syntax
  "_n_upred_prefixed"  :: "n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_ -> _")
  "_n_upred_index"         :: "('b \<Rightarrow> 'a upred) \<Rightarrow> 'b \<Rightarrow> n_upred" ("_<_>" 50)

end
