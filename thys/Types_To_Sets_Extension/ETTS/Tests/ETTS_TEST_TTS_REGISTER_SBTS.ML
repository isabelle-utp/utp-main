(* Title: ETTS/Tests/ETTS_TEST_TTS_REGISTER_SBTS.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)

signature ETTS_TEST_TTS_REGISTER_SBTS =
sig

type tts_register_sbts_in_type
val execute_test_suite_tts_register_sbts : 
  Proof.context ->
  (tts_register_sbts_in_type, Proof.state) 
    UT_Test_Suite.test_results_suite

end;

structure etts_test_tts_register_sbts : ETTS_TEST_TTS_REGISTER_SBTS =
struct




(**** Auxiliary ****)

fun mk_msg_tts_register_sbts_error msg = "tts_register_sbts: " ^ msg



(*** Data ***)

type tts_register_sbts_in_type = 
  (string * string list) * Proof.context



(*** Exceptions ***)

fun test_exc_fvs ctxt = 
  let
    
    val sbt = "g::'q"
    val UA_c = "UA::'a set"
    val UB_c = "UB::'b set"
    val rissest = [UA_c, UB_c]

    val tts_register_sbts_in : tts_register_sbts_in_type = 
      ((sbt, rissest), ctxt)

    val err_msg = mk_msg_tts_register_sbts_error
      "all fixed variables that occur in the sbterm " ^
      "must be fixed in the context"

  in
    UT_Test_Suite.assert_exception
      "variables not fixed in the context"
      tts_register_sbts_in
      (ERROR err_msg)
  end;

fun test_exc_repeated_risset ctxt = 
  let
    
    val sbt = "f"
    val UA_c = "UA::'a set"
    val UB_c = "UA::'a set"
    val rissest = [UA_c, UB_c]

    val tts_register_sbts_in : tts_register_sbts_in_type = 
      ((sbt, rissest), ctxt)

    val err_msg = mk_msg_tts_register_sbts_error
      "the type variables associated with the risset must be distinct"

  in
    UT_Test_Suite.assert_exception
      "repeated risset"
      tts_register_sbts_in
      (ERROR err_msg)
  end;




(**** Test suite ****)

local

fun tts_register_sbts_string_of_input 
  (tts_register_sbts_in : tts_register_sbts_in_type) = 
  let
    val ((sbt, risset), _) = tts_register_sbts_in
    val ctxt_c = "ctxt: unknown context" 
    val sbt_c = "sbt: " ^ sbt
    val risset_c = "risset: " ^ ML_Syntax.print_list I risset
    val out_c = [ctxt_c, sbt_c, risset_c]
      |> String.concatWith "\n"
  in out_c end;

fun tts_register_sbts_string_of_output (_ : Proof.state) = 
  let val st_c = "st: unknown state" 
  in st_c end;

fun tts_register_sbts ((args, ctxt) : tts_register_sbts_in_type) = 
  ETTS_Substitution.process_tts_register_sbts args ctxt;

in

fun mk_test_suite_tts_register_sbts ctxt =
  let
    val test_suite_tts_register_sbts = UT_Test_Suite.init
      "tts_register_sbts"
      tts_register_sbts
      tts_register_sbts_string_of_input
      tts_register_sbts_string_of_output
  in
    test_suite_tts_register_sbts
    |> test_exc_fvs ctxt
    |> test_exc_repeated_risset ctxt
  end;

end;

fun execute_test_suite_tts_register_sbts ctxt = 
  UT_Test_Suite.execute (mk_test_suite_tts_register_sbts ctxt);

end;