(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_unrest_tac.thy                                                   *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Proof Tactic for Unrestriction *}

theory utp_unrest_tac
imports "../core/utp_unrest"
begin

ML {*
  fun utp_unrest_simpset ctxt =
    ctxt
      addsimps (closure.get ctxt)
      addsimps (unrest.get ctxt)
      addsimps (typing.get ctxt)
      addsimps (defined.get ctxt);
*}

ML {*
  fun utp_unrest_tac thms ctxt i =
    CHANGED (
      TRY (asm_full_simp_tac (utp_unrest_simpset ctxt) i))
*}


method_setup utp_unrest_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_unrest_tac thms ctxt))
*} "proof tactic for unrestitution"

end
