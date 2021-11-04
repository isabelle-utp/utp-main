(* Title: CTR/CTR_Relativization.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Implementation of the algorithm CTR II: Relativization.
*)


structure CTR_Relativization : CTR_ALGORITHM =
struct

open More_Simplifier;

fun pp_tac ctxt unfld_thms def_thm i = 
  SELECT_GOAL (Local_Defs.unfold_tac ctxt (def_thm :: unfld_thms)) i
  THEN CONVERSION (Thm.beta_conversion true) i
  THEN CONVERSION Thm.eta_conversion i
  THEN Transfer.transfer_prover_start_tac ctxt i
  THEN (TRYALL (Transfer.transfer_step_tac ctxt))
  THEN (Transfer.transfer_prover_end_tac ctxt i);

fun try_prove ctxt xs asms prop tac = SOME (Goal.prove ctxt xs asms prop tac)
  handle ERROR _  => NONE;

fun try_relativization ctxt simp_spec_opt trt unfld_thms def_thm =
  let
    val tr_thm_opt = pp_tac ctxt unfld_thms def_thm 1
      |> K
      |> try_prove ctxt [] [] (HOLogic.mk_Trueprop trt) 
    val tr_thm_opt = Option.map (rewrite_simp_opt ctxt simp_spec_opt) tr_thm_opt 
  in tr_thm_opt end;

fun apply ctxt (synthesis, simp_spec_opt) assms type_specs def_thm = 
  let
    val is_equality_assms = 
      let val is_is_equality_thm = 
        Thm.full_prop_of 
        #> HOLogic.dest_Trueprop 
        #> Transfer.is_is_equality
      in
        assms
        |> filter is_is_equality_thm
        |> map (@{thm is_equality_def} |> single |> Local_Defs.unfold ctxt)
      end
    val trt = def_thm 
      |> CTR_Conversions.const_of_def ctxt
      |> CTR_Conversions.trt_of_const ctxt type_specs
    val pp_thm_opt =
      let val ppt = CTR_Conversions.prt_of_trt trt
      in
        pp_tac ctxt is_equality_assms def_thm 1
        |> K
        |> try_prove ctxt [] [] (HOLogic.mk_Trueprop ppt) 
      end
    val tr_thm_opt = 
      if pp_thm_opt |> Option.isSome |> not andalso synthesis
      then try_relativization ctxt simp_spec_opt trt is_equality_assms def_thm
      else NONE
    val output = 
      if Option.isSome tr_thm_opt 
      then ALGRelativization (the tr_thm_opt)
      else 
        if Option.isSome pp_thm_opt
        then ALGParametricity (the pp_thm_opt)
        else ALGFailure
  in output end;

end;