(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_base.thy                                                         *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Base UTP without any theories *}

theory utp_base
imports
  utp_common
  "core/utp_core"
  "alpha/utp_alpha"
  "tactics/utp_pred_tac"
  "tactics/utp_expr_tac"
  "tactics/utp_rel_tac"
  "tactics/utp_xrel_tac"
  "tactics/utp_subst_tac"
  "tactics/utp_closure_tac"
  "tactics/utp_alpha_tac"
  "laws/utp_pred_laws"
  "laws/utp_rel_laws"
  "laws/utp_subst_laws"
  "laws/utp_rename_laws"
  "laws/utp_refine_laws"
  "laws/utp_poly_laws"
  "laws/utp_alpha_laws"
  "poly/utp_poly"
  "parser/utp_pred_parser"
  "parser/utp_alpha_pred_parser"
  "parser/utp_op_parser"
  "types/utp_list"
  "types/utp_fset"
  "types/utp_uset"
  "types/utp_memory"
  "theories/utp_theory"
  "theories/utp_context"
begin end
