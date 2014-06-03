(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_hoare_tac.thy                                                    *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Proof Tactic(s) for Hoare Logic *}

theory utp_hoare_tac
imports 
  "../core/utp_hoare"
  utp_unrest_tac
  utp_closure_tac
begin

ML {*
fun hoare_cond_tac thms ctxt i = rtac @{thm HoareP_CondR} i

fun hoare_seq_tac thms ctxt i = rtac @{thm HoareP_SemiR} i

fun hoare_assign_tac thms ctxt i =
    (rtac @{thm HoareP_PAssignR} i THEN (TRY (utp_unrest_tac thms ctxt i
                                             THEN utp_unrest_tac thms ctxt i
                                             THEN utp_closure_tac thms ctxt i
                                             THEN utp_unrest_tac thms ctxt i
                                             THEN (SELECT_GOAL (utp_poly_auto_tac thms ctxt i) i)
)))

fun hoare_iter_tac thms ctxt i =
    (rtac @{thm HoareP_IterInvP} i THEN (TRY (utp_poly_auto_tac thms ctxt (i+1) 
                                             THEN utp_poly_auto_tac thms ctxt (i+1)
                                             THEN utp_closure_tac thms ctxt (i+1)
                                             THEN utp_closure_tac thms ctxt (i+1)
                                             THEN utp_closure_tac thms ctxt (i+1) 
)))
 *}

method_setup hoare_cond = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (hoare_cond_tac thms ctxt))
*} "hoare tactic for conditionals"

method_setup hoare_seq = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (hoare_seq_tac thms ctxt))
*} "hoare tactic for sequences"

method_setup hoare_assign = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (hoare_assign_tac thms ctxt))
*} "proof tactic for closure conditions"

method_setup hoare_iter = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (hoare_iter_tac thms ctxt))
*} "proof tactic for closure conditions"


end
