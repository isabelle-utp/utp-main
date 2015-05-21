(******************************************************************************)
(* Project: VDM model for Isabelle/UTP                                        *)
(* File: utp_vdm_tac.thy                                                      *)
(* Author: Simon Foster, University of York (UK)                              *)
(* Authors: Original CML model by Simon Foster, University of York (UK)       *)
(*          Adapted to VDM by Luis Diogo Couto, Aarhus University (DK)        *)
(******************************************************************************)

header {* Proof Tactic for VDM *}

theory utp_vdm_tac
imports 
  utp_vdm_expr
begin

text {* Theorem Attributes *}

ML {*
  structure vdmty_defs =
    Named_Thms (val name = @{binding vdmty_defs} val description = "VDM type defs")
*}

ML {*
  structure vdmval_defs =
    Named_Thms (val name = @{binding vdmval_defs} val description = "VDM value defs")
*}

ML {*
  structure vdmfun_defs =
    Named_Thms (val name = @{binding vdmfun_defs} val description = "VDM function defs")
*}

ML {*
  structure vdmop_defs =
    Named_Thms (val name = @{binding vdmop_defs} val description = "VDM operation defs")
*}

setup vdmty_defs.setup
setup vdmval_defs.setup
setup vdmfun_defs.setup
setup vdmop_defs.setup


ML {*
  fun utp_vdm_defs ctxt =
    ctxt
      addsimps (vdmty_defs.get ctxt)
      addsimps (vdmval_defs.get ctxt)
      addsimps (vdmfun_defs.get ctxt)
      addsimps (vdmop_defs.get ctxt)
*}

ML {*
  fun utp_vdm_simpset ctxt =
    (utp_vdm_defs ctxt)
      addsimps (evalp.get ctxt)
      addsimps (evalpp.get ctxt)
      addsimps (closure.get ctxt)
      addsimps (typing.get ctxt)
      addsimps (defined.get ctxt);
*}

ML {*
  fun utp_vdm_unfold_tac thms ctxt i =
    CHANGED (
      TRY (asm_full_simp_tac (utp_vdm_defs ctxt) i))
*}

ML {*
  fun utp_vdm_tac thms ctxt i =
    CHANGED (
      TRY (asm_full_simp_tac (utp_vdm_simpset ctxt) i))
*}

ML {*
  fun utp_vdm_auto_tac thms ctxt i =
    CHANGED ((
      (asm_full_simp_tac (utp_vdm_simpset ctxt)) THEN_ALL_NEW
      (asm_full_simp_tac ctxt) THEN_ALL_NEW
      (SELECT_GOAL (auto_tac ctxt))) i)
*}

method_setup unfold_vdm = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_vdm_unfold_tac thms ctxt))
*} "proof tactic for VDM"

method_setup vdm_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_vdm_tac thms ctxt))
*} "proof tactic for VDM"

method_setup vdm_auto_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_vdm_auto_tac thms ctxt))
*} "proof tactic for predicates with auto"

text {* Set up some simplifications to deal with finite sets and strings *}

declare nibble_less_eq_def [simp]
declare nibble_less_def [simp]

text {* Some examples *}

lemma mimplies_Some_Some [simp]:
  "mimplies (Some x) (Some y) = Some (x \<longrightarrow> y)"
  by (case_tac x, auto)

(*
lemma vdm_goal1:
  "|forall x : @bool @ &x => &x| = |true|"
  by (vdm_auto_tac)

lemma vdm_goal2:
  "|forall x : @nat1 @ &x > 0| = |true|"
  by (vdm_tac)

lemma vdm_goal3:
  "|forall x : @nat @ (&x < 5) => &x in @set {0,1,2,3,4}| = |true|"
  oops

lemma vdm_goal4: "|iota x : @nat @ &x = 5| = |5|"
  by (vdm_auto_tac)
*)

declare fcard_def [evalp]
declare blist.rep_eq [evalp]

end