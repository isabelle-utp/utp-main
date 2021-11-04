(*  Title:      SpecCheck/dynamic/speccheck_dynamic.ML
    Author:     Lukas Bulwahn and Nicolai Schaffroth, TU Muenchen

This file allows to run SpecCheck tests specified as a string representing ML code.

TODO: this module is not very well tested.
*)

signature SPECCHECK_DYNAMIC =
sig
  val check_dynamic : Proof.context -> string -> unit
end

structure SpecCheck_Dynamic : SPECCHECK_DYNAMIC =
struct

(*call the compiler and pass resulting type string to the parser*)
fun determine_type ctxt s =
  let
    val return = Unsynchronized.ref "return"
    val context : ML_Compiler0.context =
     {name_space = #name_space ML_Env.context,
      print_depth = SOME 1000000,
      here = #here ML_Env.context,
      print = fn r => return := r,
      error = #error ML_Env.context}
    val _ =
      Context.setmp_generic_context (SOME (Context.Proof ctxt))
        (fn () =>
          ML_Compiler0.ML context
            {line = 0, file = "generated code", verbose = true, debug = false} s) ()
  in SpecCheck_Dynamic_Construct.parse_pred (! return) end;

(*call the compiler and run the test*)
fun run_test ctxt s =
  Context.setmp_generic_context (SOME (Context.Proof ctxt))
    (fn () =>
      ML_Compiler0.ML ML_Env.context
        {line = 0, file = "generated code", verbose = false, debug = false} s) ();

(*split input into tokens*)
fun input_split s =
  let
    fun dot c = c = #"."
    fun space c = c = #" "
    val (head, code) = Substring.splitl (not o dot) (Substring.full s)
  in
   (String.tokens space (Substring.string head),
    Substring.string (Substring.dropl dot code))
  end;

(*create the function from the input*)
fun make_fun s =
  let
    val scan_param = Scan.one (fn s => s <> ";")
    fun parameters s = Scan.repeat1 scan_param s
    val p = $$ "ALL" |-- parameters
    val (split, code) = input_split s
    val stop = Scan.stopper (fn _ => ";") (fn s => s = ";");
    val (params, _) = Scan.finite stop p split
  in "fn (" ^ commas params ^ ") => " ^ code end;

(*read input and perform the test*)
fun gen_check_property check ctxt s =
  let
    val func = make_fun s
    val (_, ty) = determine_type ctxt func
  in run_test ctxt (check ctxt "Dynamic Test" (ty, func)) end;

val check_dynamic = gen_check_property SpecCheck_Dynamic_Construct.build_check
(*val check_property_safe = gen_check_property Construct_Gen.safe_check*)

(*perform test for specification function*)
(*fun gen_check_property_f check ctxt s =
  let
    val (name, ty) = determine_type ctxt s
  in run_test ctxt (check ctxt name (ty, s)) end;

val check_property_f = gen_check_property_f Gen_Dynamic.build_check*)
(*val check_property_safe_f_ = gen_check_property_f Construct_Gen.safe_check*)
end;
