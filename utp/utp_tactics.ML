(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_tactics.ML                                                       *)
(* Authors: Simon Foster & Frank Zeyda (University of York, UK)               *)
(* Emails: simon.foster@york.ac.uk frank.zeyda@york.ac.uk                     *)
(******************************************************************************)
(* LAST REVIEWED: 12 Jan 2017 *)

(* UTP_TACTICS Signature *)

signature UTP_TACTICS =
sig
  val update_uexpr_rep_eq_thms : Proof.context -> unit
  val get_uexpr_rep_eq_thms : Proof.context -> thm list
end;

(* UTP_Tactics Structure *)

structure UTP_Tactics : UTP_TACTICS =
struct
  val uexpr_rep_eq_thms = Unsynchronized.ref ([] : thm list);

  val uexpr_rep_eq_query =
    Find_Theorems.read_query Position.none
      "name:\"rep_eq\" \"Rep_uexpr ?e = ?f\"";

  fun update_uexpr_rep_eq_thms ctx =
    let val facts = Find_Theorems.find_theorems_cmd
      ctx NONE (SOME 1000) true uexpr_rep_eq_query;
    val hardcoded = [@{thm numeral_uexpr_rep_eq}];
    in
       uexpr_rep_eq_thms := (hardcoded @ (map snd (snd facts)))
    end;

  (* Querying each time the attribute is read is feasible but a bit slower... *)

  fun get_uexpr_rep_eq_thms ctx =
    (if length (!uexpr_rep_eq_thms) = 0 then
      update_uexpr_rep_eq_thms ctx else (); !uexpr_rep_eq_thms);
end;