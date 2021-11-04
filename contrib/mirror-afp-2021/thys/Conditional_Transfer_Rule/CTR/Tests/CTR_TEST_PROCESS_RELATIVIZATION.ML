(* Title: CTR/Tests/CTR_TEST_PROCESS_RELATIVIZATION.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)

signature CTR_TEST_PROCESS_RELATIVIZATION =
sig
type process_relativization_in_type
val execute_test_suite_process_relativization : 
  Proof.context -> (process_relativization_in_type, ctr_pp_out)
    UT_Test_Suite.test_results_suite
end;

structure ctr_test_process_relativization : CTR_TEST_PROCESS_RELATIVIZATION =
struct




(**** Auxiliary ****)

fun mk_msg_ctr_error msg = "ctr: " ^ msg



(*** Data ***)

type process_relativization_in_type = 
  (
    (string * thm list option) option *
    Element.context list *
    (string * string) list *
    ((binding option * thm) * mixfix) 
  ) * Proof.context;



(*** Relation ***)

local

fun map_const_name (oldc, newc) (Const (c, T)) = 
    if oldc = c then Const (newc, T) else Const (c, T)
  | map_const_name eqc (Abs (c, T, t)) = Abs (c, T, map_const_name eqc t)
  | map_const_name eqc (t $ u) = map_const_name eqc t $ map_const_name eqc u
  | map_const_name _ t = t

in 
 
fun process_relativization_test_eq 
    (PPRelativization args1, PPRelativization args2) = 
      let
        val act_lthy = #2 args1
        val exp_lthy = #2 args2
        val (act_ow_def_t, act_tr_t) = args1
          |> #1
          |>> Local_Defs.meta_rewrite_rule act_lthy 
          |> apply2 Thm.full_prop_of
        val (exp_ow_def_t, exp_tr_t) = args2
          |> #1
          |>> Local_Defs.meta_rewrite_rule act_lthy 
          |> apply2 Thm.full_prop_of
        val act_ow_def_lhst = act_ow_def_t |> Logic.dest_equals |> #1
        val exp_ow_def_lhst = exp_ow_def_t |> Logic.dest_equals |> #1
        val thy = Proof_Context.theory_of exp_lthy
        val mapc = 
          (
            act_ow_def_lhst |> head_of |> dest_Const |> #1, 
            exp_ow_def_lhst |> head_of |> dest_Const |> #1
          )
        val act_ow_def_t' = map_const_name mapc act_ow_def_t
        val act_tr_t' = map_const_name mapc act_tr_t
        val act_ow_def_eq = Pattern.equiv thy (act_ow_def_t', exp_ow_def_t)
        val tr_eq = Pattern.equiv thy (act_tr_t', exp_tr_t)
        val _ = act_ow_def_eq |> Bool.toString |> writeln
      in act_ow_def_eq andalso tr_eq end
  | process_relativization_test_eq 
      (PPParametricity args1, PPParametricity args2) = 
      (*careful: not needed; hence, a usable implementation is not provided*)
      Thm.eq_thm (fst args1, fst args2) 
  | process_relativization_test_eq (_, _) = false;

end;




(**** Tests ****)



(*** Valid inputs ***)

fun test_eq_trivial ctxt = 
  let
    (*input*)
    val {synthesis, elems, type_specs, thm_specs, ...} = 
      ctr_test_data_of_proof ctxt "mono_with" |> the
    val process_relativization_in = 
      ((synthesis, elems, type_specs, the_single thm_specs), ctxt)
    (*output*)
    val process_relativization_out = 
      PPRelativization ((@{thm mono_ow_def}, @{thm mono_ow_transfer'}), ctxt)
  in
    UT_Test_Suite.assert_brel 
      "output equivalence"
      process_relativization_test_eq 
      process_relativization_out
      process_relativization_in
  end;



(*** Exceptions ***)

fun test_exc_def ctxt = 
  let
    val {synthesis, elems, type_specs, thm_specs, ...} = 
      ctr_test_data_of_proof ctxt "exI" |> the
    val args = 
      ((synthesis, elems, type_specs, the_single thm_specs), ctxt)
    val err_msg = mk_msg_ctr_error 
      (
        Syntax.string_of_term ctxt (Thm.full_prop_of @{thm exI}) ^ 
        " is not a definition"
      )
  in UT_Test_Suite.assert_exception "not a definition" args (ERROR err_msg) end;

fun test_exc_binrel ctxt = 
  let
    val {synthesis, elems, type_specs, thm_specs, ...} = 
      ctr_test_data_of_proof ctxt "binrel" |> the
    val args = ((synthesis, elems, type_specs, the_single thm_specs), ctxt)
    val err_msg = mk_msg_ctr_error 
      "trp: trp must consist of (stv, binary relation) pairs"
  in UT_Test_Suite.assert_exception "binary relation" args (ERROR err_msg) end;

fun test_exc_binrel_ftv ctxt = 
  let
    val {synthesis, elems, type_specs, thm_specs, ...} = 
      ctr_test_data_of_proof ctxt "binrel_ftv" |> the
    val args = ((synthesis, elems, type_specs, the_single thm_specs), ctxt)
    val err_msg = mk_msg_ctr_error 
      "trp: the user-specified binary relations must " ^
      "be defined over type variables"
  in 
    UT_Test_Suite.assert_exception "binary relation ftv" args (ERROR err_msg) 
  end;

fun test_exc_dup_stvs ctxt = 
  let
    val {synthesis, elems, type_specs, thm_specs, ...} = 
      ctr_test_data_of_proof ctxt "dup_stvs" |> the
    val args = ((synthesis, elems, type_specs, the_single thm_specs), ctxt)
    val err_msg = mk_msg_ctr_error "trp: duplicate stvs"
  in UT_Test_Suite.assert_exception "duplicate stv" args (ERROR err_msg) end;

fun test_exc_dup_binrel_ftvs ctxt = 
  let
    val {synthesis, elems, type_specs, thm_specs, ...} = 
      ctr_test_data_of_proof ctxt "dup_binrel_ftvs" |> the
    val args = ((synthesis, elems, type_specs, the_single thm_specs), ctxt)
    val err_msg = mk_msg_ctr_error
      "trp: duplicate ftvs in the specification of the binary relations"
  in
    UT_Test_Suite.assert_exception "duplicate binrel ftvs" args (ERROR err_msg) 
  end;

fun test_exc_no_relator ctxt = 
  let
    val {synthesis, elems, type_specs, thm_specs, ...} = 
      ctr_test_data_of_proof ctxt "no_relator" |> the
    val args = ((synthesis, elems, type_specs, the_single thm_specs), ctxt)
    val err_msg = mk_msg_ctr_error
      "no relator found for the type constructor CTR_Tests.K"
  in
    UT_Test_Suite.assert_exception "no relator" args (ERROR err_msg) 
  end;

fun test_exc_invalid_relator ctxt = 
  let
    val {synthesis, elems, type_specs, thm_specs, ...} = 
      ctr_test_data_of_proof ctxt "invalid_relator" |> the
    val args = ((synthesis, elems, type_specs, the_single thm_specs), ctxt)
    val err_msg = mk_msg_ctr_error
      (
        "the relator found for the type constructor CTR_Tests.L " ^
        "is not suitable (is there is a mismatch of type variables?)" 
      )
  in
    UT_Test_Suite.assert_exception "no relator" args (ERROR err_msg) 
  end;




(**** Test suite ****)

local

fun string_of_elem_ctxt_fixes args = "fixes: " ^
  (
    args
    |> map (fn (x, y, _) => (x, y)) 
    |> ML_Syntax.print_list 
      (ML_Syntax.print_pair Binding.print (ML_Syntax.print_option I))
  );
fun string_of_elem_ctxt_assumes ctxt args =
  let
    val string_of_fst = ML_Syntax.print_pair 
      Binding.print 
      (ML_Syntax.print_list (Token.pretty_src ctxt #> Pretty.string_of))
    val string_of_snd = 
      ML_Syntax.print_list (ML_Syntax.print_pair I (ML_Syntax.print_list I))
  in 
    "assumes: " ^ 
    ML_Syntax.print_list (ML_Syntax.print_pair string_of_fst string_of_snd) args
  end;
fun string_of_elem_ctxt_constrains _ = "constrains: unknown constrains";
fun string_of_elem_ctxt_defines _ = "defines: unknown defines";
fun string_of_elem_ctxt_notes _ = "notes: unknown notes";
fun string_of_elem_ctxt_lazy_notes _ = "lazy notes: unknown lazy notes";

fun string_of_elem_ctxt _ (Element.Fixes args : Element.context) = 
      string_of_elem_ctxt_fixes args
  | string_of_elem_ctxt _ (Element.Constrains args) = 
      string_of_elem_ctxt_constrains args
  | string_of_elem_ctxt ctxt (Element.Assumes args) = 
      string_of_elem_ctxt_assumes ctxt args
  | string_of_elem_ctxt _ (Element.Defines args) = 
      string_of_elem_ctxt_defines args
  | string_of_elem_ctxt _ (Element.Notes args) = 
      string_of_elem_ctxt_notes args
  | string_of_elem_ctxt _ (Element.Lazy_Notes args) = 
      string_of_elem_ctxt_lazy_notes args

fun process_relativization_string_of_input ctxt 
  (process_relativization_in : process_relativization_in_type) = 
  let
    val ((synthesis_opt, elems, type_specs, thm_spec), lthy) =
      process_relativization_in
    val synthesis_opt_c =
      let val synthesis_c = "synthesis: "
      in
        case synthesis_opt of 
          SOME synthesis => 
            (
              case #2 synthesis of 
                  SOME _ => synthesis_c ^ "user-defined simpset"
                | NONE => synthesis_c ^ "default simpset"
            )
        | NONE => synthesis_c ^ "none"
      end
    val elems_c = "elements:" ^ 
      (
        if null elems 
        then " none" 
        else "\n" ^
          (
            elems
            |> map (string_of_elem_ctxt ctxt)
            |> map (fn c => "\t" ^ c)
            |> String.concatWith "\n"
          )
      )
    val type_specs_c = "type_specs: " ^
      ML_Syntax.print_list (ML_Syntax.print_pair I I) type_specs
    val thm_spec_c =
      "definition: " ^ (thm_spec |> #1 |> #2 |> Thm.string_of_thm lthy) 
    val lthy_c = "lthy: unknown local theory" 
    val out_c = [synthesis_opt_c, elems_c, type_specs_c, thm_spec_c, lthy_c] 
      |> String.concatWith "\n"
  in out_c end;

fun process_relativization 
  (
    ((synthesis, assms, type_specs, thm_spec), lthy) : 
      process_relativization_in_type
  ) = CTR.process_relativization synthesis assms type_specs thm_spec lthy;

in

fun mk_test_suite_process_relativization ctxt =
  let
    val test_suite_process_relativization = UT_Test_Suite.init
      "process_relativization"
      process_relativization
      (process_relativization_string_of_input ctxt)
      string_of_pp_out
  in
    test_suite_process_relativization
    |> test_eq_trivial ctxt
    |> test_exc_def ctxt
    |> test_exc_binrel ctxt
    |> test_exc_binrel_ftv ctxt
    |> test_exc_dup_stvs ctxt
    |> test_exc_dup_binrel_ftvs ctxt
    |> test_exc_no_relator ctxt
    |> test_exc_invalid_relator ctxt
  end;

end;

fun execute_test_suite_process_relativization ctxt = 
  UT_Test_Suite.execute (mk_test_suite_process_relativization ctxt)

end;