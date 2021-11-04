(* Title: CTR/CTR_Foundations.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Basic data types for CTR.
*)

signature CTR_FOUNDATIONS =
sig
datatype ctr_algorithm = relativization | parametricity
datatype ctr_alg_out = 
  ALGRelativization of thm | ALGParametricity of thm | ALGFailure
datatype ctr_pp_out = 
    PPRelativization of (thm * thm) * local_theory 
  | PPParametricity of thm * local_theory
  | PPFailure of local_theory;
val apply_alg_out : (thm -> thm) -> ctr_alg_out -> ctr_alg_out
val lthy_of_pp_out : ctr_pp_out -> local_theory 
val string_of_pp_out :  ctr_pp_out -> string
end;

structure CTR_Foundations : CTR_FOUNDATIONS =
struct

datatype ctr_algorithm = relativization | parametricity;
datatype ctr_alg_out = 
  ALGRelativization of thm | ALGParametricity of thm | ALGFailure;
datatype ctr_pp_out = 
    PPRelativization of (thm * thm) * local_theory 
  | PPParametricity of thm * local_theory
  | PPFailure of local_theory;

fun apply_alg_out f (ALGRelativization thm) = ALGRelativization (f thm)
  | apply_alg_out f (ALGParametricity thm) = ALGParametricity (f thm)
  | apply_alg_out _ ALGFailure = ALGFailure;

fun lthy_of_pp_out (PPRelativization (_, lthy)) = lthy
  | lthy_of_pp_out (PPParametricity (_, lthy)) = lthy
  | lthy_of_pp_out (PPFailure lthy) = lthy;

fun string_of_pp_out (PPRelativization ((ow_def_thm, tr_thm), lthy)) = 
      let
        val preamble_c = 
          "PPRelativization ((ow_def_thm, tr_thm), lthy), where"
        val ow_def_thm_c = "ow_def_thm: " ^ Thm.string_of_thm lthy ow_def_thm
        val tr_thm_c = "tr_thm: " ^ Thm.string_of_thm lthy tr_thm
        val lthy_c = "lthy: unknown local theory" 
        val out_c = [preamble_c, ow_def_thm_c, tr_thm_c, lthy_c] 
          |> String.concatWith "\n"
      in out_c end
  | string_of_pp_out (PPParametricity (tr_thm, lthy)) =
      let
        val preamble_c = "PPParametricity (tr_thm, lthy), where"
        val tr_thm_c = "tr_thm" ^ Thm.string_of_thm lthy tr_thm
        val lthy_c = "lthy: unknown local theory" 
        val out_c = [preamble_c, tr_thm_c, lthy_c] 
          |> String.concatWith "\n"    
      in out_c end
  | string_of_pp_out (PPFailure _) = "Failure";

end;

open CTR_Foundations;