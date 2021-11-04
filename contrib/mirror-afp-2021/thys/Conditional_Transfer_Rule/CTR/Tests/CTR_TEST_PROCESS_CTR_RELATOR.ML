(* Title: CTR/Tests/CTR_TEST_PROCESS_CTR_RELATOR.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)

signature CTR_TEST_PROCESS_CTR_RELATOR =
sig
type process_ctr_relator_in_type
val execute_test_suite_process_ctr_relator : 
  Proof.context -> (process_ctr_relator_in_type, local_theory)
    UT_Test_Suite.test_results_suite
end;

structure ctr_test_process_ctr_relator : CTR_TEST_PROCESS_CTR_RELATOR =
struct



(**** Auxiliary ****)

fun mk_msg_ctr_relator msg = "ctr_relator: " ^ msg;



(*** Data ***)

type process_ctr_relator_in_type = string * Proof.context;




(**** Tests ****)



(*** Exceptions ***)

fun test_exc_not_const ctxt = 
  let
    val c = "a + b"
    val args = (c, ctxt)
    val err_msg = mk_msg_ctr_relator "the input must be a constant term"
  in UT_Test_Suite.assert_exception "not a constant" args (ERROR err_msg) end;

fun test_exc_not_body_bool ctxt = 
  let
    val c = "Cons"
    val args = (c, ctxt)
    val err_msg = mk_msg_ctr_relator 
      "the body of the type of the input must be bool"
  in UT_Test_Suite.assert_exception "not bool body" args (ERROR err_msg) end;

fun test_exc_not_binders_2 ctxt = 
  let
    val c = "Ex"
    val args = (c, ctxt)
    val err_msg = mk_msg_ctr_relator 
      "the type of the input must have more than two binders"
  in UT_Test_Suite.assert_exception "not two binders" args (ERROR err_msg) end;

fun test_exc_not_binders_binrelT ctxt =
  let
    val c = "not_binders_binrelT"
    val args = (c, ctxt)
    val err_msg = mk_msg_ctr_relator
      "all of the binders associated with the type of the input" ^
      "except the last two must be the binary relation types"
  in 
    UT_Test_Suite.assert_exception 
      "not binary relation types" args (ERROR err_msg) 
  end;

fun test_exc_no_dup_binrelT ctxt =
  let
    val c = "no_dup_binrelT"
    val args = (c, ctxt)
    val err_msg = mk_msg_ctr_relator
      "the types of the binders of the binary relations associated " ^
      "with the type of the input must have no duplicates"
  in 
    UT_Test_Suite.assert_exception 
      "no duplicates in the binary relation types" args (ERROR err_msg) 
  end;

fun test_exc_not_binders_binrelT_ftv_stv ctxt =
  let
    val c = "not_binders_binrelT_ftv_stv"
    val args = (c, ctxt)
    val err_msg = mk_msg_ctr_relator
      "the types of the binders of the binary relation types associated " ^
      "with the input type must be either free type variables or " ^
      "schematic type variables"
  in 
    UT_Test_Suite.assert_exception 
      "not binrel type ftv or stv" args (ERROR err_msg) 
  end;

fun test_exc_not_type_constructor_lhs ctxt =
  let
    val c = "not_type_constructor_lhs"
    val args = (c, ctxt)
    val err_msg = mk_msg_ctr_relator
      "the last two binders of the input type must be " ^
      "the results of an application of a type constructor"
  in 
    UT_Test_Suite.assert_exception 
      "not type constructor lhs" args (ERROR err_msg)
  end;

fun test_exc_not_type_constructor_rhs ctxt =
  let
    val c = "not_type_constructor_rhs"
    val args = (c, ctxt)
    val err_msg = mk_msg_ctr_relator
      "the last two binders of the input type must be " ^
      "the results of an application of a type constructor"
  in 
    UT_Test_Suite.assert_exception 
      "not type constructor rhs" args (ERROR err_msg)
  end;

fun test_exc_not_identical_type_constructors_lhs ctxt =
  let
    val c = "not_identical_type_constructors_lhs"
    val args = (c, ctxt)
    val err_msg = mk_msg_ctr_relator
      "the sequences of the input types to the type constructors that are " ^
      "associated with the last two binders of the input type must be " ^
      "identical to the sequences of the types formed by concatenating the " ^
      "type variables associated with the left hand side and the right " ^
      "hand side of the binary relation types, respectively"
  in 
    UT_Test_Suite.assert_exception 
      "not identical type constructors lhs" args (ERROR err_msg)
  end;

fun test_exc_not_identical_type_constructors_rhs ctxt =
  let
    val c = "not_identical_type_constructors_rhs"
    val args = (c, ctxt)
    val err_msg = mk_msg_ctr_relator
      "the sequences of the input types to the type constructors that are " ^
      "associated with the last two binders of the input type must be " ^
      "identical to the sequences of the types formed by concatenating the " ^
      "type variables associated with the left hand side and the right " ^
      "hand side of the binary relation types, respectively"
  in 
    UT_Test_Suite.assert_exception 
      "not identical type constructors rhs" args (ERROR err_msg)
  end;




(**** Test suite ****)

local

fun process_ctr_relator_string_of_input 
   (process_ctr_relator_in : process_ctr_relator_in_type) = 
  let
    val (c, _) = process_ctr_relator_in
    val name_c = "constant name: " ^ c
    val ctxt_c = "lthy: unknown context" 
    val out_c = [name_c, ctxt_c] |> String.concatWith "\n"
  in out_c end;

fun process_ctr_relator ((c, ctxt) : process_ctr_relator_in_type) = 
  CTR_Relators.process_ctr_relator c ctxt;

in

fun mk_test_suite_process_ctr_relator ctxt =
  let
    val test_suite_process_ctr_relator = UT_Test_Suite.init
      "process_ctr_relator"
      process_ctr_relator
      process_ctr_relator_string_of_input
      (fn _ => "lthy: unknown local theory")
  in
    test_suite_process_ctr_relator
    |> test_exc_not_const ctxt
    |> test_exc_not_body_bool ctxt
    |> test_exc_not_binders_2 ctxt
    |> test_exc_not_binders_binrelT ctxt
    |> test_exc_no_dup_binrelT ctxt
    |> test_exc_not_binders_binrelT_ftv_stv ctxt
    |> test_exc_not_type_constructor_lhs ctxt
    |> test_exc_not_type_constructor_rhs ctxt
    |> test_exc_not_identical_type_constructors_lhs ctxt
    |> test_exc_not_identical_type_constructors_rhs ctxt
  end;

end;

fun execute_test_suite_process_ctr_relator ctxt = 
  UT_Test_Suite.execute (mk_test_suite_process_ctr_relator ctxt)

end;