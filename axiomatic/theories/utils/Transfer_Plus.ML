(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: Transfer_Plus.ML                                                     *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 19 Jan 2016 *)

(* Unfolding Transfer *)

signature TRANSFER_PLUS =
sig
  val transfer_unfold_tac : Proof.context -> tactic
  val unfolding_transfer_method :
    bool -> (Proof.context -> Proof.method) context_parser
end;

structure Transfer_Plus : TRANSFER_PLUS =
struct
  open Transfer;

  fun transfer_unfold_tac ctx =
    Local_Defs.unfold_tac ctx
      (Named_Theorems.get ctx @{named_theorems transfer_unfold});

  local
    val free = Args.context -- Args.term >> (fn (_, Free v) => v | (ctxt, t) =>
      error ("Bad free variable: " ^ Syntax.string_of_term ctxt t))

    val fixing = Scan.optional (Scan.lift (Args.$$$ "fixing" -- Args.colon)
      |-- Scan.repeat free) []
  in
    fun unfolding_transfer_method equiv :
        (Proof.context -> Proof.method) context_parser =
      fixing >> (fn vs => fn ctxt =>
        SIMPLE_METHOD' (K (TRY (transfer_unfold_tac ctxt)) THEN'
          (gen_frees_tac vs ctxt) THEN' (transfer_tac equiv ctxt)))
  end;
end;