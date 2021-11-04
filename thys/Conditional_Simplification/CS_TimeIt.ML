(* Copyright 2021 (C) Mihails Milehins *)

(*
The infrastructure of CS_TimeIt builds upon and extends the functionality of
the method timeit of Eisbach. It provides only a very thin layer of additional 
or alternative functionality.
*)
signature CS_TIMEIT =
sig
val timing_stats : Timing.timing list -> Timing.timing list
val timing_report : Timing.timing list -> unit
val TIMEIT : int -> (thm -> thm Seq.seq) -> tactic
val mtimeit : int -> Method.text -> Proof.context -> Method.method
end;

structure CS_TimeIt: CS_TIMEIT =
struct

fun timing_stats (ts : Timing.timing list) =
  let
    val mean_time =
      map (Time.toReal) #> CS_Stats.basic_stats #> map Time.fromReal
    val es = map #elapsed ts |> mean_time
    val cpus = map #cpu ts |> mean_time
    val gcs = map #gc ts |> mean_time
    val timing_mean = {elapsed = nth es 0, cpu = nth cpus 0, gc = nth gcs 0}
    val timing_variance = {elapsed = nth es 1, cpu = nth cpus 1, gc = nth gcs 1}
    val timing_min = {elapsed = nth es 2, cpu = nth cpus 2, gc = nth gcs 2}
    val timing_max = {elapsed = nth es 3, cpu = nth cpus 3, gc = nth gcs 3}
  in [timing_mean, timing_variance, timing_min, timing_max] end;

fun timing_report ts =
  let

    fun is_trivial ts =
      let
        val is_trivial_impl = 
          map (Timing.is_relevant_time #> not) #> List.all I
        val is_trivial_es = ts |> map #elapsed |> is_trivial_impl
        val is_trivial_cpu = ts |> map #cpu |> is_trivial_impl
        val is_trivial_gc = ts |> map #gc |> is_trivial_impl
      in is_trivial_es andalso is_trivial_cpu andalso is_trivial_gc end;

    fun mk_report_string timings ts = 
      "\nNumber of runs : " ^ Int.toString (length ts) ^ "\n" ^
      "Mean timing : " ^ (nth timings 0 |> Timing.message) ^ "\n" ^
      "Timing variance : " ^ (nth timings 1 |> Timing.message) ^ "\n" ^
      "Minimum time : " ^ (nth timings 2 |> Timing.message) ^ "\n" ^
      "Maximum time : " ^ (nth timings 3 |> Timing.message) ^ "\n" ^
      "Individual timings : \n" ^
      String.concatWith "\n" (map Timing.message ts) ^ "\n"

    val _ =
      if is_trivial ts 
      then writeln "Trivial timing data: nothing to report"
      else 
        let val timings = timing_stats ts
        in mk_report_string timings ts |> writeln end

  in () end;

fun TIMEIT n tac st = 
  if n <= 0
  then tac st
  else
    let
      fun eval tac st =
        let
          val ts = Timing.start ()
          val result = SINGLE tac st
          val te = Timing.result ts
        in (result, te) end 
      val results = map (eval tac) (replicate n st)
      val _ = timing_report (map #2 results)
      val result = results |> hd |> #1
    in
      (
        case result of
          NONE => Seq.empty
        | SOME st' => Seq.single st'
      )
    end;

fun mtimeit n m ctxt =
  let
    val tac = (Method.evaluate m ctxt) []
      |> Context_Tactic.NO_CONTEXT_TACTIC ctxt
      |> TIMEIT n
  in SIMPLE_METHOD tac end;

val timeit_parser = 
  Method.text_closure -- Scan.option (Scan.lift (Parse.int));

fun process_timeit args ctxt =
  let val n = case snd args of SOME n => n | NONE => 1
  in mtimeit n (fst args) ctxt end;

val _ = Theory.setup
  (
    Method.setup
      \<^binding>\<open>timeit'\<close>
      (timeit_parser >> process_timeit)
      "higher order timing method"
  );

end;