(*  Title:      SpecCheck/speccheck_base.ML
    Author:     Kevin Kappelmann

Types returned by single tests and complete test runs as well as simple utility methods on them.
*)

signature SPECCHECK_BASE =
sig

  datatype result_single = Result of bool | Discard | Exception of exn

  type stats = {
    num_success_tests : int,
    num_failed_tests : int,
    num_discarded_tests : int,
    num_recently_discarded_tests : int,
    num_success_shrinks : int,
    num_failed_shrinks : int,
    timing : Timing.timing
  }

  val add_timing : Timing.timing -> Timing.timing -> Timing.timing

  val empty_stats : stats
  val num_tests : stats -> int
  val num_shrinks : stats -> int

  type 'a failure_data = {
    counterexamples : 'a list,
    the_exception : exn option
  }

  val failure_data : 'a list -> 'a failure_data
  val failure_data_exn : 'a list -> exn -> 'a failure_data

  datatype 'a result =
    Success of stats |
    Gave_Up of stats |
    Failure of stats * 'a failure_data

  val stats_of_result : 'a result -> stats

end

structure SpecCheck_Base : SPECCHECK_BASE =
struct

datatype result_single = Result of bool | Discard | Exception of exn

type stats = {
  num_success_tests : int,
  num_failed_tests : int,
  num_discarded_tests : int,
  num_recently_discarded_tests : int,
  num_success_shrinks : int,
  num_failed_shrinks : int,
  timing : Timing.timing
}

val empty_stats = {
  num_success_tests = 0,
  num_failed_tests = 0,
  num_discarded_tests = 0,
  num_recently_discarded_tests = 0,
  num_success_shrinks = 0,
  num_failed_shrinks = 0,
  timing = {
    cpu = Time.zeroTime,
    elapsed = Time.zeroTime,
    gc = Time.zeroTime
  }
}

fun add_timing {elapsed = elapsed1, cpu = cpu1, gc = gc1}
  {elapsed = elapsed2, cpu = cpu2, gc = gc2} = {
  elapsed = elapsed1 + elapsed2,
  cpu = cpu1 + cpu2,
  gc = gc1 + gc2
}

fun num_tests {num_success_tests, num_failed_tests, ...} =
  num_success_tests + num_failed_tests

fun num_shrinks {num_success_shrinks, num_failed_shrinks, ...} =
  num_success_shrinks + num_failed_shrinks

type 'a failure_data = {
  counterexamples : 'a list,
  the_exception : exn option
}

fun failure_data counterexamples = {
  counterexamples = counterexamples,
  the_exception = NONE
}

fun failure_data_exn counterexamples exn = {
  counterexamples = counterexamples,
  the_exception = SOME exn
}

datatype 'a result =
  Success of stats |
  Gave_Up of stats |
  Failure of stats * 'a failure_data

fun stats_of_result (Success stats) = stats
  | stats_of_result (Gave_Up stats) = stats
  | stats_of_result (Failure (stats, _)) = stats

end
