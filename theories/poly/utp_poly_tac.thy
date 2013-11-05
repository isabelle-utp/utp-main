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

text {* Theorem Attribute *}

ML {*
  structure evalp =
    Named_Thms (val name = @{binding evalp} val description = "evalp theorems")
*}

setup evalp.setup

declare EvalP_simp [evalp]
declare EvalP_TrueP [evalp]
declare EvalP_FalseP [evalp]
declare EvalP_NotP [evalp]
declare EvalP_AndP [evalp]
declare EvalP_OrP [evalp]
declare EvalP_ImpliesP [evalp]
declare EvalP_ClosureP [evalp]
declare EvalP_RefP[evalp]
declare EvalP_RenameP[evalp]

declare Tautology_def [evalp]

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
      addsimps (closure.get ctxt)
      addsimps (typing.get ctxt)
      addsimps (defined.get ctxt)
      addsimps (unrest.get ctxt);
*}

ML {*
  fun utp_poly_tac thms ctxt i =
    CHANGED (
      TRY (asm_full_simp_tac (utp_poly_simpset ctxt) i))
*}

ML {*
  fun utp_poly_auto_tac thms ctxt i =
    CHANGED ((
      (asm_full_simp_tac (utp_poly_simpset ctxt)) THEN_ALL_NEW
      (SELECT_GOAL (auto_tac ctxt))) i)
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

end

