(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_subst_tac.thy                                                    *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Proof Tactic for Substitution *}

theory utp_subst_tac
imports "../laws/utp_subst_laws"
begin

ML {*
  fun utp_subst_simpset ctxt =
    (simpset_of ctxt)
      addsimps (usubst.get ctxt)
      addsimps (closure.get ctxt)
      addsimps (typing.get ctxt)
      addsimps (defined.get ctxt);
*}

ML {*
  fun utp_subst_tac thms ctxt i =
    CHANGED (
      TRY (asm_full_simp_tac (utp_subst_simpset ctxt) i))
*}


method_setup utp_subst_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_subst_tac thms ctxt))
*} "proof tactic for substitution"

end
