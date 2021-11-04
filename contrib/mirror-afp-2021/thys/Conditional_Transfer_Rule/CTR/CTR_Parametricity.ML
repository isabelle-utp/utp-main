(* Title: CTR/CTR_Parametricity.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Implementation of the invocation of the algorithm CTR I: Parametricity.
*)

structure CTR_Parametricity : CTR_ALGORITHM =
struct

fun theorem_format_error ctxt thm =
  let
    val msg_main = "Unexpected format for the definition." 
    val msg = [(Pretty.para msg_main), Thm.pretty_thm ctxt thm]
      |> Pretty.chunks 
      |> Pretty.string_of;
  in error msg end;

fun gen_parametric_constant settings lthy def_thm =
  let
    val eq = Ctr_Sugar_Util.mk_abs_def def_thm 
      handle TERM _ => theorem_format_error lthy def_thm
    val goalt = Conditional_Parametricity.mk_param_goal_from_eq_def lthy eq
    val thm = Conditional_Parametricity.prove_goal settings lthy (SOME eq) goalt
  in thm end;

fun apply ctxt (_, _) _ _ def_thm = 
  let
    val thm = def_thm
      |> gen_parametric_constant Conditional_Parametricity.quiet_settings ctxt
  in ALGParametricity thm end;

end;