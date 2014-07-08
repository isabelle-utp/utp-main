(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_closure_tac.thy                                                  *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Proof Tactic for Closure Conditions *}

theory utp_closure_tac
imports "../core/utp_pred"
begin

ML {*
  fun utp_closure_simpset ctxt =
    ctxt
      addsimps (closure.get ctxt)
      addsimps (typing.get ctxt)
      addsimps (defined.get ctxt);
*}

ML {*
  fun utp_closure_tac thms ctxt i =
    CHANGED (
      TRY (asm_full_simp_tac (utp_closure_simpset ctxt) i))
*}


method_setup utp_closure_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_closure_tac thms ctxt))
*} "proof tactic for closure conditions"

end
