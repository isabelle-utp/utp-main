(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: profiling.ML                                                         *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 7/12/2016 *)

signature PROFILING =
sig
  val probe_tac : (thm -> unit) -> Method.method
  val start_profiling : Method.method
  val finish_profiling : Method.method
  val wrap_method : Method.text_range -> Method.text_range
  val setup_command : unit -> unit
end

structure Profiling : PROFILING =
struct
  val start_time = Unsynchronized.ref (Timing.start());

  fun probe_tac f = METHOD (K (fn thm => (f thm; all_tac thm)));

  fun profiling_msg (duration : Timing.timing) =
    let val {cpu = cpu_time, elapsed = real_time, gc = gc_time} = duration in
      "Profiling: "
        ^ (Time.toString real_time) ^ "s elapsed time, "
        ^ (Time.toString cpu_time) ^ "s CPU time and "
        ^ (Time.toString gc_time) ^ "s GC time."
    end;

  val start_profiling =
    probe_tac (fn _ => start_time := Timing.start());

  val finish_profiling =
    probe_tac (fn _ =>
      (Output.information (profiling_msg (Timing.result(!start_time)))));

  fun wrap_method (m : Method.text_range) =
    (Method.Combinator ((Method.no_combinator_info, Method.Then, [
      Method.Basic (K start_profiling), (fst m),
      Method.Basic (K finish_profiling)])),
    (snd m));

  fun setup_command () =
    Outer_Syntax.command @{command_keyword profile}
      "initial goal refinement step (unstructured) with profiling"
      (Method.parse >> (fn m => (Method.report m;
        Toplevel.proofs (Proof.apply (wrap_method m)))));
end