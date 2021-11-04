(*  Title:      SpecCheck/output_styles/output_style_perl.ML
    Author:     Lukas Bulwahn and Nicolai Schaffroth, TU Muenchen
    Author:     Christopher League

Perl output styles for SpecCheck.
*)

structure SpecCheck_Output_Style_Perl : SPECCHECK_OUTPUT_STYLE =
struct

open SpecCheck_Configuration
open SpecCheck_Base

fun style show_opt ctxt name timing result =
  let
    val sort_counterexamples =  Config.get ctxt sort_counterexamples
    val maybe_sort = if sort_counterexamples then sort (int_ord o apply2 size) else I

    val stats = stats_of_result result
    val num_failed_tests = #num_failed_tests stats

    fun code (Success _) = "ok"
      | code (Gave_Up _) = "Gave up!"
      | code (Failure _) = "FAILED"

    fun ratio stats =
      let
        val num_success_tests = #num_success_tests stats
      in
        if num_failed_tests = 0
        then implode ["(", string_of_int num_success_tests, " passed)"]
        else implode ["(", string_of_int num_success_tests, "/",
          string_of_int (num_success_tests + num_failed_tests),  " passed)"]
      end

    val result_string = name ^ ".\n" ^ code result ^ " " ^ ratio stats

    fun show_counterexamples counterexamples =
      case show_opt of
        SOME show =>
          (case maybe_sort (map (Pretty.string_of o show) counterexamples) of
            [] => ()
          | es => (warning "Counterexamples:"; fold (fn x => fn _ => warning x) es ()))
      | NONE => ()

  in
    case result of
      Success _ => writeln result_string
    | Gave_Up _ => warning result_string
    | Failure (_, failure_data) =>
        (warning result_string; show_counterexamples (#counterexamples failure_data))
  end

end
