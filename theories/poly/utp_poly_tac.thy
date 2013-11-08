(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_poly_tac.thy                                                     *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Proof Tactic for Polymorphic Predicates and Expressions *}

theory utp_poly_tac
imports 
  "../core/utp_pred"
  "../tactics/utp_pred_tac"
  "../core/utp_expr"
  "../tactics/utp_expr_tac"
  "../core/utp_rel"
  "../tactics/utp_rel_tac"
  "../tactics/utp_xrel_tac"
  "../laws/utp_pred_laws"
  utp_poly_value
  utp_poly_var
begin

text {* Theorem Attributes *}

ML {*
  structure evalp =
    Named_Thms (val name = @{binding evalp} val description = "evalp theorems")
*}

setup evalp.setup

ML {*
  structure evalpp =
    Named_Thms (val name = @{binding evalpp} val description = "evalpp theorems")
*}

setup evalpp.setup

ML {*
  structure evalpr =
    Named_Thms (val name = @{binding evalpr} val description = "evalpr theorems")
*}

setup evalpr.setup

declare EvalP_simp [evalpp]
declare EvalP_TrueP [evalpp]
declare EvalP_FalseP [evalpp]
declare EvalP_NotP [evalpp]
declare EvalP_AndP [evalpp]
declare EvalP_OrP [evalpp]
declare EvalP_IffP [evalpp]
declare EvalP_ImpliesP [evalpp]
declare EvalP_ClosureP [evalpp]
declare EvalP_RefP[evalpp]
declare EvalP_RenameP[evalpp]

declare Tautology_def [evalpp]
declare less_eq_WF_PREDICATE_def [evalpp]
declare CondR_def [evalpp, evalpr]

declare EvalR_simp [evalpr]
declare EvalR_refinement [evalpr]
declare EvalR_TrueP_explicit [evalpr]
declare EvalR_FalseP [evalpr]
declare EvalR_NotP [evalpr]
declare EvalR_OrP [evalpr]
declare EvalR_AndP [evalpr]
declare EvalR_SemiR [evalpr]
declare EvalR_SkipR [evalpr]

declare EmptyUS.rep_eq [evalp]
declare InsertUS_rep_eq [evalp]
declare UnionUS.rep_eq [evalp]
declare InterUS.rep_eq [evalp]
declare MinusUS.rep_eq [evalp]
declare MemberUS.rep_eq [evalp]
declare NMemberUS.rep_eq [evalp]
declare SubsetUS.rep_eq [evalp]
declare SubseteqUS.rep_eq [evalp]
declare SetUS.rep_eq [evalp]
declare IntersyncUS_def [evalp]
declare RestrictUS.rep_eq [evalp]
declare USET_transfer [evalp]

declare NilUL.rep_eq [evalp]
declare ConsUL_rep_eq [evalp]
declare AppendUL.rep_eq [evalp]
declare MinusUL.rep_eq [evalp]
declare PrefixUL.rep_eq [evalp]
declare PrefixeqUL.rep_eq [evalp]
declare ULIST_transfer [evalp]

ML {*
  fun utp_poly_simpset ctxt =
    (simpset_of ctxt)
      addsimps (evalp.get ctxt)
      addsimps (evalpp.get ctxt)
      addsimps (closure.get ctxt)
      addsimps (typing.get ctxt)
      addsimps (defined.get ctxt)
      addsimps (unrest.get ctxt);
*}

ML {*
  fun utp_prel_simpset ctxt =
    (simpset_of ctxt)
      addsimps (evalp.get ctxt)
      addsimps (evalpr.get ctxt)
      addsimps (closure.get ctxt)
      addsimps (typing.get ctxt)
      addsimps (defined.get ctxt)
      addsimps (urename.get ctxt)
      addsimps (unrest.get ctxt);
*}

declare binding_equiv_trans [intro]

ML {*
  fun utp_poly_tac thms ctxt i =
    CHANGED (
      TRY (asm_full_simp_tac (utp_poly_simpset ctxt) i))
*}

ML {*
  fun utp_poly_auto_tac thms ctxt i =
    CHANGED (
      (SELECT_GOAL (auto_tac (map_simpset (fn _ => (utp_poly_simpset ctxt)) ctxt)) i))
*}

ML {*
  fun utp_prel_tac thms ctxt i =
    CHANGED (
      TRY (asm_full_simp_tac (utp_prel_simpset ctxt) i))
*}

ML {*
  fun utp_prel_auto_tac thms ctxt i =
    CHANGED (
      (SELECT_GOAL (auto_tac (map_simpset (fn _ => (utp_prel_simpset ctxt) addsimps (@{thms "relcomp_unfold"})) ctxt)) i))
*}

method_setup utp_poly_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_poly_tac thms ctxt))
*} "proof tactic for polymorphic predicates"

method_setup utp_poly_auto_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_poly_auto_tac thms ctxt))
*} "proof tactic for polymorphic predicates with auto"

method_setup utp_prel_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_prel_tac thms ctxt))
*} "proof tactic for polymorphic relations"

method_setup utp_prel_auto_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_prel_auto_tac thms ctxt))
*} "proof tactic for polymorphic relations with auto"

end

