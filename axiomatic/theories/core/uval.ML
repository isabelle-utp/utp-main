(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: uval.ML                                                              *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 2 December 2014 *)

signature INJECT_TYPE =
sig
  val is_injectable : Proof.context -> typ -> bool
  val injectable_tac1 : Proof.context -> tactic
  val injectable_tac2 : Proof.context -> tactic
  val injectable_tac : Proof.context -> tactic
  val inject_type : xstring -> theory -> theory
end;

structure Inject_Type : INJECT_TYPE =
struct
  open Tactic_Utils;

  fun is_injectable ctx typ =
    Sign.of_sort (Proof_Context.theory_of ctx) (typ, @{sort injectable});

  fun injectable_tac1 ctx =
    (unfold_tac ctx (typing.get ctx)) THEN
    (auto_tac ctx);

  fun injectable_tac2 ctx =
    (unfold_tac ctx (Named_Theorems.get ctx @{named_theorems typedep})) THEN
    TRY (Simplifier.asm_full_simp_tac ctx 1) THEN
    (unfold_tac ctx (typing.get ctx)) THEN
    TRY (Simplifier.asm_full_simp_tac ctx 1) THEN
    (auto_tac ctx);

  fun injectable_tac ctx =
    (Class.intro_classes_tac ctx []) THEN (
      (SELECT_GOAL (injectable_tac1 ctx) 1) THEN_IF_FEWER
      (SELECT_GOAL (injectable_tac2 ctx) 1))
    THEN (check_solvable_tac);

  fun inject_type typ thy =
    let val tyco = (Sign.intern_type thy typ);
    val sorts = replicate (Sign.arity_number thy tyco) @{sort injectable};
    val vs = Name.invent_names Name.context "'a" sorts;
    (* val instantiates_order =
      (Sign.of_sort thy (Type (tyco, map TFree vs), @{sort order})); *)
    val already_injectable =
      (Sign.of_sort thy (Type (tyco, map TFree vs), @{sort injectable}));
    in
      (* if (instantiates_order) then *)
        if (already_injectable) then
          (warning ("Type \"" ^ typ ^ "\" has already been injected."); thy)
        else (thy
          |> (Class.instantiation ([tyco], vs, @{sort injectable})))
          |> (fn lthy => (Class.prove_instantiation_exit injectable_tac lthy)
          handle UNSOLVABLE =>
            error ( (* Here we know for sure that the proof is infeasible. *)
              "Type \"" ^ tyco ^ "\" not permissible for injection into uval.")
          | ERROR _ =>
            error ( (* Here we do not precisely know why the proof failed. *)
              "Failed to instantiate type \"" ^ typ ^ "\" as injectable."))
          |> (fn thy => (Output.writeln
            ("Successfully injected type \"" ^ typ ^ "\" into uval."); thy))
      (* else
        error ("Type \"" ^ typ ^ "\" does not instantiate class order.") *)
    end;
end;