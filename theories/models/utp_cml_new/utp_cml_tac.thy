(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_cml_tac.thy                                                      *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Proof Tactic for CML *}

theory utp_cml_tac
imports 
  utp_cml_expr
begin

text {* Theorem Attributes *}

ML {*
  structure cmlty_defs =
    Named_Thms (val name = @{binding cmlty_defs} val description = "CML type defs")
*}

ML {*
  structure cmlval_defs =
    Named_Thms (val name = @{binding cmlval_defs} val description = "CML value defs")
*}

ML {*
  structure cmlfun_defs =
    Named_Thms (val name = @{binding cmlfun_defs} val description = "CML function defs")
*}

ML {*
  structure cmlchan_defs =
    Named_Thms (val name = @{binding cmlchan_defs} val description = "CML channel defs")
*}

ML {*
  structure cmlproc_defs =
    Named_Thms (val name = @{binding cmlproc_defs} val description = "CML process defs")
*}

ML {*
  structure cmlop_defs =
    Named_Thms (val name = @{binding cmlop_defs} val description = "CML operation defs")
*}

ML {*
  structure cmlact_defs =
    Named_Thms (val name = @{binding cmlact_defs} val description = "CML action defs")
*}

setup cmlty_defs.setup
setup cmlval_defs.setup
setup cmlfun_defs.setup
setup cmlchan_defs.setup
setup cmlproc_defs.setup
setup cmlop_defs.setup
setup cmlact_defs.setup

ML {*
  fun utp_cml_defs ctxt =
    ctxt
      addsimps (cmlty_defs.get ctxt)
      addsimps (cmlval_defs.get ctxt)
      addsimps (cmlfun_defs.get ctxt)
      addsimps (cmlchan_defs.get ctxt)
      addsimps (cmlproc_defs.get ctxt)
      addsimps (cmlop_defs.get ctxt)
      addsimps (cmlact_defs.get ctxt);
*}

ML {*
  fun utp_cml_simpset ctxt =
    (utp_cml_defs ctxt)
      addsimps (evalp.get ctxt)
      addsimps (evalpp.get ctxt)
      addsimps (closure.get ctxt)
      addsimps (typing.get ctxt)
      addsimps (defined.get ctxt);
*}

ML {*
  fun utp_cml_unfold_tac thms ctxt i =
    CHANGED (
      TRY (asm_full_simp_tac (utp_cml_defs ctxt) i))
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
      (asm_full_simp_tac ctxt) THEN_ALL_NEW
      (SELECT_GOAL (auto_tac ctxt))) i)
*}

method_setup unfold_cml = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_cml_unfold_tac thms ctxt))
*} "proof tactic for CML"

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

text {* Some examples *}

lemma mimplies_Some_Some [simp]:
  "mimplies (Some x) (Some y) = Some (x \<longrightarrow> y)"
  by (case_tac x, auto)

(*
lemma cml_goal1:
  "|forall x : @bool @ &x => &x| = |true|"
  by (cml_auto_tac)

lemma cml_goal2:
  "|forall x : @nat1 @ &x > 0| = |true|"
  by (cml_tac)

lemma cml_goal3:
  "|forall x : @nat @ (&x < 5) => &x in @set {0,1,2,3,4}| = |true|"
  oops

lemma cml_goal4: "|iota x : @nat @ &x = 5| = |5|"
  by (cml_auto_tac)
*)

declare fcard_def [evalp]

end