(* Title: CTR/CTR_Postprocessing.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Postprocessing of the output of the algorithms associated with the CTR.
*)


signature CTR_POSTPROCESSING =
sig

val postprocess_parametricity : 
  binding -> thm -> local_theory -> ctr_pp_out
val postprocess_relativization : 
  binding -> mixfix -> thm -> Proof.context -> ctr_pp_out
val postprocess_failure : Proof.context -> ctr_pp_out

end;

structure CTR_Postprocessing : CTR_POSTPROCESSING =
struct

open CTR_Utilities;

(*post-processing of an arbitrary transfer rule*)
fun postprocess_transfer_rule b thm ctxt = 
  let
    val b = ((b |> Binding.path_of |> map fst) @ [Binding.name_of b, "transfer"])
      |> Long_Name.implode
      |> Binding.qualified_name_mandatory
    val lthy = ctxt
      |> Local_Theory.note 
        (
          (b, Transfer.transfer_add |> K |> Attrib.internal |> single), 
          single thm
        )
      |>> #2
      |>> the_single
      |> #2
    val _ =
      let
        val lthy_print = 
          ("Transfer.lifting_syntax" |> single |> Bundle.includes) lthy
      in
        thm 
        |> single
        |> (Local_Theory.full_name lthy_print b |> thm_printer lthy_print true)
      end
  in lthy end;

(*post-processing of a parametricity property*)
fun postprocess_parametricity b thm ctxt = 
  PPParametricity (thm, postprocess_transfer_rule b thm ctxt);

(*post-processing of a relativization*)
fun postprocess_relativization b mf thm ctxt = 
  let
    
    val (_, rhst, _) = thm 
      |> Thm.concl_of
      |> HOLogic.dest_Trueprop 
      |> CTR_Conversions.dest_trt
    val (rhst, ctxt') = Logic.unvarify_local_term ctxt rhst 
    val (absts, rhst) = rhst
      |> Term.strip_abs_eta (rhst |> strip_abs_vars |> length) 
    val argts = rhst
      |> (fn t => Term.add_frees t [])
      |> rev
      |> subtract op= absts
      |> curry (swap #> op@) absts  
      |> map Free
    val (lhst, lthy) = 
      let 
        fun declare_const_with thy = 
          let val T = map type_of argts ---> type_of rhst 
          in Sign.declare_const_global ((b, T), mf) thy end
      in Local_Theory.raw_theory_result declare_const_with ctxt' end
    val lhst = Term.list_comb (lhst, argts)
    fun make_with_def thy = 
      let
        val b =
          ((b |> Binding.path_of |> map fst) @ [Binding.name_of b ^ "_def"])
          |> Long_Name.implode
          |> Binding.qualified_name_mandatory
      in
        Global_Theory.add_defs 
          false (single ((b, Logic.mk_equals (lhst, rhst)), [])) thy
        |>> the_single
      end
    val (ow_def_thm, lthy') = Local_Theory.raw_theory_result make_with_def lthy
    val _ = ow_def_thm 
      |> single
      |> (ow_def_thm |> Thm.derivation_name |> thm_printer lthy' true)
    val thm = Thm.pure_unfold lthy' (ow_def_thm |> Thm.symmetric |> single) thm
  in 
    PPRelativization ((ow_def_thm, thm), postprocess_transfer_rule b thm lthy') 
  end;

(*post-processing of a failed attempt to perform relativization*)
fun postprocess_failure lthy = PPFailure lthy;

end;