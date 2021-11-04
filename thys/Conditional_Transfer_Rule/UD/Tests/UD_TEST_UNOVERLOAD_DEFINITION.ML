(* Title: UD/Tests/UD_TEST_UNOVERLOAD_DEFINITION.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)

signature UD_TEST_UNOVERLOAD_DEFINITION =
sig
type unoverload_definition_in_type
val execute_test_suite_unoverload_definition : 
  theory ->
  (unoverload_definition_in_type, UD.ud_thm_out_type * theory)
    UT_Test_Suite.test_results_suite
end;

structure ud_test_unoverload_definition : UD_TEST_UNOVERLOAD_DEFINITION =
struct




(**** Auxiliary ****)

fun mk_msg_unoverload_definition_error msg = "ud: " ^ msg



(*** Data ***)

type unoverload_definition_in_type = 
  (binding * mixfix) * (string * typ) * theory;



(*** Relation ***)

fun ud_test_eq_thm thy (act_c, exp_c) (act_ud_out, exp_ud_out) =
  let

    fun rel (act_thm, exp_thm) =
      let
        fun replace_const (Const (c, T)) =
            if c = exp_c then Const (act_c, T) else Const (c, T)
          | replace_const (t $ u) = replace_const t $ replace_const u
          | replace_const (Abs (c, T, t)) = Abs (c, T, replace_const t)
          | replace_const x = x
        val act_t = Thm.full_prop_of act_thm
        val exp_t = exp_thm |> Thm.full_prop_of |> replace_const
      in Pattern.equiv thy (act_t, exp_t) end;

    fun ud_test_eq_thm_impl ((UD.trivial act_thm), (UD.trivial exp_thm)) =
          rel (act_thm, exp_thm)
      | ud_test_eq_thm_impl ((UD.nontrivial act_thms), (UD.nontrivial exp_thms)) = 
          let
            val (act_with_def_thm, act_with_thm) = act_thms 
            val (exp_with_def_thm, exp_with_thm) = exp_thms
          in 
            rel (act_with_def_thm, exp_with_def_thm)
            andalso rel (act_with_thm, exp_with_thm) 
          end
     | ud_test_eq_thm_impl (_, _) = false

  in ud_test_eq_thm_impl (fst act_ud_out, fst exp_ud_out) end;




(**** Tests ****)



(*** Valid inputs ***)

fun test_eq_trivial thy  = 
  let
    
    (*input*)
    val act_c = "UD_Tests.closed'.with"
    val exp_c = ""
    val b = Binding.name "closed'"
    val aT = TVar (("'a", 0), \<^sort>\<open>topological_space\<close>)
    val T = HOLogic.mk_setT aT --> HOLogic.boolT
    val closed_c = "Topological_Spaces.topological_space_class.closed"
    val ud_in = ((b, NoSyn), (closed_c, T), thy)
    
    (*output*)
    val ud_out = (UD.trivial (@{thm closed_with}), thy)
    
  in
    UT_Test_Suite.assert_brel 
      "nontrivial output equivalence"
      (ud_test_eq_thm thy (act_c, exp_c)) 
      ud_out
      ud_in
  end;

fun test_eq_nontrivial thy  = 
  let
    
    (*input*)
    val act_c = "UD_Tests.closure.with"
    val exp_c = "UD_Tests.closure_with"
    val b = Binding.name "closure"
    val aT = TVar (("'a", 0), \<^sort>\<open>topological_space\<close>)
    val T = (HOLogic.mk_setT aT --> HOLogic.mk_setT aT)
    val closure_c = "UD_Tests.closure"
    val ud_in = ((b, NoSyn), (closure_c, T), thy)
    
    (*output*)
    val ud_out = 
      (UD.nontrivial (@{thm closure_with_def}, @{thm closure_with}), thy)
    
  in
    UT_Test_Suite.assert_brel 
      "nontrivial output equivalence"
      (ud_test_eq_thm thy (act_c, exp_c)) 
      ud_out
      ud_in
  end;



(*** Exceptions ***)

fun test_exc_extra_type_variables thy = 
  let
    val aT = TVar (("'a", 0), \<^sort>\<open>type\<close>)
    val Sup_class_c = "Complete_Lattices.Sup_class"
    val args : unoverload_definition_in_type =
      (
        (Binding.empty, NoSyn), 
        (Sup_class_c, Term.itselfT aT --> \<^typ>\<open>prop\<close>), 
        thy
      )
    val err_msg = mk_msg_unoverload_definition_error 
      "specification depends on extra type variables"
  in 
    UT_Test_Suite.assert_exception 
      "extra type variables" args (ERROR err_msg)
  end;

fun test_exc_ud_ex thy = 
  let
    val aT = TVar (("'a", 0), \<^sort>\<open>type\<close>)
    val T = 
      (HOLogic.mk_setT aT --> HOLogic.boolT) --> 
      HOLogic.mk_setT aT --> 
      HOLogic.boolT
    val ts_c = "Topological_Spaces.topological_space.closed"
    val args : unoverload_definition_in_type =
      ((Binding.empty, NoSyn), (ts_c, T), thy)
    val err_msg = mk_msg_unoverload_definition_error 
      "unoverloaded constant already exists"
  in 
    UT_Test_Suite.assert_exception 
      "constant already exists" args (ERROR err_msg)
  end;

fun test_exc_no_cids thy = 
  let
    val aT = TVar (("'a", 0), \<^sort>\<open>type\<close>)
    val T = 
      (HOLogic.mk_setT aT --> HOLogic.boolT) --> 
      HOLogic.mk_setT aT --> 
      HOLogic.boolT
    val implies_c = "HOL.implies"
    val args : unoverload_definition_in_type =
      ((Binding.empty, NoSyn), (implies_c, T), thy)
    val err_msg = mk_msg_unoverload_definition_error
      "no suitable constant-instance definitions"
  in 
    UT_Test_Suite.assert_exception 
      "no suitable CIs" args (ERROR err_msg)
  end;




(**** Test suite ****)

local

fun unoverload_definition_string_of_input 
  (unoverload_definition_in : unoverload_definition_in_type) = 
  let
    val ((b, _), (c, T), thy) = unoverload_definition_in
    val b_c = "binding: " ^ Binding.name_of b
    val const_c = 
      "constant: " ^ 
      c ^ 
      " :: " ^ 
      Syntax.string_of_typ (Proof_Context.init_global thy) T
    val thy_c = "thy: unknown theory" 
    val out_c = [b_c, const_c, thy_c] |> String.concatWith "\n"
  in out_c end;

fun unoverload_definition_string_of_output (ud_thm_out, thy) = 
  let
    val ctxt = Proof_Context.init_global thy
    val ud_thm_c = 
      let
        val with_thm_c = "with_thm: "
        val with_def_thm_c = "with_def_thm: "
      in
        case ud_thm_out of 
          UD.trivial with_thm => 
            with_thm_c ^ Thm.string_of_thm ctxt with_thm
        | UD.nontrivial (with_def_thm, with_thm) =>
            with_def_thm_c ^ 
            Thm.string_of_thm ctxt with_def_thm ^ 
            "\n" ^
            with_thm_c ^ 
            Thm.string_of_thm ctxt with_thm
      end
    val thy_c = "thy: unknown theory"
    val out_c = [ud_thm_c, thy_c] |> String.concatWith "\n"
  in out_c end;

fun unoverload_definition 
  (((b, mixfix), (c, T), thy) : unoverload_definition_in_type) = 
  UD.unoverload_definition (b, mixfix) (c, T) thy;

in

fun mk_test_suite_unoverload_definition thy =
  let
    val test_suite_unoverload_definition = UT_Test_Suite.init
      "unoverload_definition"
      unoverload_definition
      unoverload_definition_string_of_input
      unoverload_definition_string_of_output
  in
    test_suite_unoverload_definition
    |> test_eq_trivial thy
    |> test_eq_nontrivial thy
    |> test_exc_extra_type_variables thy
    |> test_exc_ud_ex thy
    |> test_exc_no_cids thy
  end;

end;

fun execute_test_suite_unoverload_definition thy = 
  UT_Test_Suite.execute (mk_test_suite_unoverload_definition thy)

end;