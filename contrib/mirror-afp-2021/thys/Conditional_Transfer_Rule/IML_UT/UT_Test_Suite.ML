(* Title: IML_UT/UT_Test_Suite.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

The implementation of a lightweight unit test framework IML_UT 
for Isabelle/ML code.

Notes:
 - The framework IML_UT was developed before the official release of SpecCheck
that serves a similar purpose (https://www.isa-afp.org/entries/SpecCheck.html).
Nonetheless, it is not unlikely that the author would be willing to make
the framework IML_UT obsolete, using SpecCheck in its place, in the future. 
 - To a certain extent, this work was inspired by xUnit (https://xunit.net/). 
*)


signature UT_TEST_SUITE =
sig
type ('x, 'y) test_suite
type ('x, 'y) test_results_suite
val init : 
  string -> 
  ('x -> 'y) -> 
  ('x -> string) -> 
  ('y -> string) -> 
  ('x, 'y) test_suite
val assert_brel : 
  string -> 
  ('y * 'y -> bool) -> 
  'y -> 'x -> 
  ('x, 'y) test_suite -> 
  ('x, 'y) test_suite
val assert_exception : 
  string -> 'x -> exn -> ('x, 'y) test_suite -> ('x, 'y) test_suite
val execute : ('x, 'y) test_suite -> ('x, 'y) test_results_suite
val output_test_results : bool -> ('a, 'b) test_results_suite -> unit
end;


structure UT_Test_Suite: UT_TEST_SUITE =
struct

exception BLANK;



(**** Types ****)

datatype 'y test_output = Exception of exn | Result of 'y;

type 'y assertion_output =
  {
    expected_output : string,
    output : 'y test_output,
    status : bool
  };

type ('x, 'y) test_result =
  {
    test_id : int, 
    name : string, 
    input : 'x, 
    assertion_output : 'y assertion_output
  };

type ('x, 'y) unit_test =
  {
    test_id : int,
    name : string,
    input : 'x,
    assertion : 'x -> 'y assertion_output
  };

type ('x, 'y) test_results_suite = 
  {
    id : string,
    function : 'x -> 'y,
    string_of_input : 'x -> string,
    string_of_output : 'y -> string,
    test_results : ('x, 'y) test_result Queue.T
  };

type ('x, 'y) test_suite = 
  {
    id : string,
    function : 'x -> 'y,
    string_of_input : 'x -> string,
    string_of_output : 'y -> string,
    tests : ('x, 'y) unit_test Queue.T
  };



(**** Initialization ****)

fun init id f string_of_input string_of_output : ('x, 'y) test_suite = 
  {
    id = id,
    function = f,
    string_of_input = string_of_input,
    string_of_output = string_of_output,
    tests = Queue.empty
  };



(**** Miscellaneous utilities ****)

fun get_num_tests tests = length (Queue.content tests);

fun is_empty_test_suite test_suite = Queue.is_empty (#tests test_suite);



(**** Evaluation ****)

(* The following function evolved from the function try from 
Pure/General/basics.ML of Isabelle2021 *)
fun eval f x =
  let
    val y_opt = try f x
    val out = case y_opt of
        SOME y => Result y
      | NONE => Exception
          (
            let val _ = f x in BLANK end
              handle exn => 
                if Exn.is_interrupt exn then Exn.reraise exn else exn
          )
  in out end;



(**** Assertion of a binary relation ****)

local

fun assert_brel_impl 
  string_of_output brel test_id name y f x : ('x, 'y) unit_test =
  let
    fun assertion x : 'y assertion_output = 
      let 
        val output = eval f x
        val status = case output of
            Exception _ => false
          | Result y' => brel (y', y)
      in
       {
         expected_output = string_of_output y,
         output = output, 
         status = status
       } 
      end
  in {test_id = test_id, name = name, input = x, assertion = assertion} end;

in

fun assert_brel name brel y x (test_suite : ('x, 'y) test_suite) =
  let
    val f = #function test_suite
    val string_of_input = #string_of_input test_suite
    val string_of_output = #string_of_output test_suite
    val tests = #tests test_suite
    val test_id = get_num_tests tests
    val test = assert_brel_impl string_of_output brel test_id name y f x
  in
    {
      id = #id test_suite,
      function = f,
      string_of_input = string_of_input,
      string_of_output = string_of_output,
      tests = Queue.enqueue test tests
    } : ('x, 'y) test_suite
  end;

end;



(**** Assertion of an exception ****)

local

fun assert_exception_impl test_id name (exn : exn) f x : ('x, 'y) unit_test =
  let
    fun assertion x : 'y assertion_output = 
      let
        val output = eval f x
        val status = case output of 
            Exception exn' =>
              exnName exn' = exnName exn 
              andalso exnMessage exn' = exnMessage exn
          | Result _ => false
     in 
       {
         expected_output = "exception '" ^ exnMessage exn ^ "'",
         output = output,
         status = status
       } 
     end
  in {test_id = test_id, name = name, input = x, assertion = assertion} end;

in

fun assert_exception name x (exn : exn) (test_suite : ('x, 'y) test_suite) =
  let
    val f = #function test_suite
    val string_of_input = #string_of_input test_suite
    val string_of_output = #string_of_output test_suite
    val tests = #tests test_suite
    val test_id = get_num_tests tests
    val test = assert_exception_impl test_id name exn f x
  in 
    {
      id = #id test_suite,
      function = f,
      string_of_input = string_of_input,
      string_of_output = string_of_output,
      tests = Queue.enqueue test tests
    } : ('x, 'y) test_suite
  end;

end;



(**** Test execution ****)

local 

fun execute_test (test_suite : ('x, 'y) test_suite) : 
  (('x, 'y) test_result * ('x, 'y) test_suite) =
  let
    val {id, function, string_of_input, string_of_output, tests} = test_suite
    val ({test_id, name, input, assertion}, tests') = Queue.dequeue tests
    val assertion_output = assertion input
    val test_result = 
      {
        test_id = test_id, 
        name = name, 
        input = input,
        assertion_output = assertion_output
      }
    val test_suite' = 
      {
        id = id, 
        function = function, 
        string_of_input = string_of_input, 
        string_of_output = string_of_output, 
        tests = tests'
      }
  in (test_result, test_suite') end;

in

fun execute (test_suite : ('x, 'y) test_suite) = 
  let
    fun execute_impl test_results test_suite =
      let
        val (test_result, test_suite') = execute_test test_suite
        val test_results' = Queue.enqueue test_result test_results
      in
        if is_empty_test_suite test_suite'
        then test_results'
        else execute_impl test_results' test_suite'
      end;
    val test_results = 
      {
        id = #id test_suite,
        function = #function test_suite,
        string_of_input = #string_of_input test_suite,
        string_of_output = #string_of_output test_suite,
        test_results = 
          if is_empty_test_suite test_suite 
          then Queue.empty 
          else execute_impl Queue.empty test_suite
      }
  in test_results : ('x, 'y) test_results_suite end;

end;



(**** Output ****)

local

fun mk_message 
  string_of_input string_of_output (test_result : ('x, 'y) test_result) =
  let
    fun string_of_output' (Exception exn) =
        "execution failed with the exception '" ^ exnMessage exn ^ "'"
      | string_of_output' (Result y) = string_of_output y
    val test = "Test " ^ Int.toString (#test_id test_result) ^ "\n"
    val function = "Name: " ^ #name test_result ^ "\n"
    val input = 
      "Input data:\n" ^ 
      tabulate (string_of_input (#input test_result)) ^ 
      "\n"
    val output = 
      "Outcome:\n" ^ 
      tabulate (string_of_output' (#output (#assertion_output test_result))) ^
      "\n"
    val expected_output = 
      "Expected outcome:\n" ^ 
      tabulate (#expected_output (#assertion_output test_result)) ^ 
      "\n"
    val test_pass_flag = #status (#assertion_output test_result)
    val status = "Test result: " ^ (if test_pass_flag then "pass" else "fail") 
    val c = String.concatWith 
      " " [test, function, input, output, expected_output, status] 
  in (test_pass_flag, c) end;

in

fun output_test_results 
  error_flag (test_results_suite : ('x, 'y) test_results_suite) = 
  let

    val
      {
        id = id,
        string_of_input = string_of_input,
        string_of_output = string_of_output,
        test_results = test_results,
        ...
      } = test_results_suite

    fun mk_messages cs test_results =
      if Queue.is_empty test_results
      then rev cs
      else
        let
          val (test_result, test_results') = Queue.dequeue test_results
          val (test_pass_flag, c) = 
            mk_message string_of_input string_of_output test_result        
        in mk_messages ((test_pass_flag, c)::cs) test_results' end

    val test_results = mk_messages [] test_results

    val heading_c = "Test results for the test suite: " ^ id ^ "\n"

    val test_cs = map snd test_results 
    val num_tests = length test_cs
    val test_cs = test_cs
      |> String.concatWith "\n\n"
      |> single

    val tests_failed = test_results 
      |> map fst
      |> map not
      |> find_indices I
    val num_tests_failed = length tests_failed
    val num_tests_passed = num_tests - num_tests_failed
    val success_flag = num_tests_failed = 0

    val num_tests_c = "Number of tests: " ^ Int.toString num_tests 
    val num_tests_passed_c = 
      "Number of tests passed: " ^ Int.toString num_tests_passed 
    val num_tests_failed_c = 
      "Number of tests failed: " ^ Int.toString num_tests_failed 
    val summary_c = 
      "Test outcome: " ^ 
      (if success_flag then "success" else "failure")
    val failed_tests_c = 
      if success_flag 
      then "\n"
      else 
        (
          "Failed tests: " ^
          ML_Syntax.print_list Int.toString tests_failed ^ 
          "\n"
        ) 

    val _ =
      (
        heading_c :: 
        num_tests_c :: 
        num_tests_passed_c :: 
        num_tests_failed_c ::
        summary_c :: 
        failed_tests_c ::
        test_cs
      )         
      |> map Pretty.str
      |> Pretty.chunks
      |> Pretty.writeln

    val _ = (not error_flag orelse success_flag) 
      orelse error ("at least one of the " ^ id ^ " tests failed")

  in () end;

end;

end;