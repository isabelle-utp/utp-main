(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_cml_tac.thy                                                      *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Proof Tactic for CML *}

theory utp_cml_tac
imports 
  utp_cml_expr
  utp_cml_types
  utp_cml_functions
begin


ML {*
  fun utp_cml_simpset ctxt =
    (simpset_of ctxt)
      addsimps (evalp.get ctxt)
      addsimps (closure.get ctxt)
      addsimps (typing.get ctxt)
      addsimps (defined.get ctxt);
*}

ML {*
  fun utp_cml_tac thms ctxt i =
    CHANGED (
      TRY (asm_full_simp_tac (utp_cml_simpset ctxt) i))
*}

ML {*
  fun utp_cml_auto_tac thms ctxt i =
    CHANGED ((
      (asm_full_simp_tac (utp_cml_simpset ctxt)) THEN_ALL_NEW
      (asm_full_simp_tac (simpset_of ctxt)) THEN_ALL_NEW
      (SELECT_GOAL (auto_tac ctxt))) i)
*}

method_setup cml_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_cml_tac thms ctxt))
*} "proof tactic for CML"

method_setup cml_auto_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_cml_auto_tac thms ctxt))
*} "proof tactic for predicates with auto"

text {* Set up some simplifications to deal with finite sets and strings *}

declare nibble_less_eq_def [simp]
declare nibble_less_def [simp]
declare fset_transfer_eq [eval,evalp]
declare fset_transfer_neq [eval,evalp]

text {* Some examples *}

lemma cml_goal1:
  "|forall x : @bool @ &x => &x| = |true|"
  by (cml_tac)

lemma cml_goal2:
  "|forall x : @nat1 @ &x > 0| = |true|"
  by (cml_tac)

lemma cml_goal3:
  "|forall x : @nat @ (&x < 5) => &x in @set {0,1,2,3,4}| = |true|"
  oops

lemma cml_goal4: "|iota x : @nat @ &x = 5| = |5|"
  by (cml_auto_tac)

end