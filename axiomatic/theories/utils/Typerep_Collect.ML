(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: Typerep_Collect.ML                                                   *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 16 Jan 2016 *)

(* Utility to automatically collect typerep theorems in an attribute. *)

signature TYPEREP_COLLECT =
sig
  val get_typerep_def : theory -> string -> thm
  val collect_typerep_thm : string -> theory -> theory
end;

structure Typerep_Collect : TYPEREP_COLLECT =
struct
  val typing_add = Named_Theorems.add @{named_theorems "typing"};

  fun get_typerep_def thy ty_name =
    Global_Theory.get_thm thy (
      (* FIXME: The condition below is a hack. Fix this properly! *)
      if ty_name = "literal" then
        "String.typerep_literal_def"
      else "typerep_" ^ ty_name ^ "_def");

  fun collect_typerep_thm tyco thy =
    let val ty_name = Binding.name_of (Binding.qualified_name tyco);
    val typerep_def = get_typerep_def thy ty_name;
    in
      snd (Global_Theory.note_thmss ""
        [((Binding.empty, [typing_add]), [([typerep_def], [])])] thy)
    end
    handle ERROR _ => (Output.warning
      ("Failed to collect typerep theorem for type " ^ tyco); thy);
end;
