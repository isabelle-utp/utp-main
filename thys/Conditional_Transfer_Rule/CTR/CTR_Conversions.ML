(* Title: CTR/CTR_Conversions.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Conversion of a transfer rule goal to a parametricity property goal.
*)

signature CTR_CONVERSIONS =
sig

val const_of_def : Proof.context -> thm -> string * typ
val trt_of_const : 
  Proof.context -> ((indexname * sort) * term) list -> string * typ -> term
val dest_trt : term -> term * term * term
val prt_of_trt : term -> term

end;

structure CTR_Conversions : CTR_CONVERSIONS =
struct

(*conversion of stvs to ftvs based on type_specs: rhs*)
fun type_specs_rhs_ftv_of_stv type_specs = type_specs 
  |> map (apsnd (type_of #> HOLogic.dest_binrelT #> #2))  
  |> AList.lookup op= #> the;

(*conversion of stvs to ftvs based on type_specs: lhs*)
fun type_specs_lhs_ftv_of_stv type_specs = type_specs
  |> map (apsnd (type_of #> HOLogic.dest_binrelT #> #1))  
  |> AList.lookup op= #> the;

(*extraction of a constant from a definition*)
fun const_of_def ctxt thm = thm 
  |> Local_Defs.meta_rewrite_rule ctxt
  |> Thm.full_prop_of
  |> Logic.dest_equals
  |> #1
  |> strip_comb
  |> #1
  |> dest_Const;

(*transfer rule goal from a constant*)
fun trt_of_const ctxt type_specs const_spec = 
  let

    fun mk_lhs_stv T = (("a", 0), T)

    val rhs_ftv_of_stv = type_specs_rhs_ftv_of_stv type_specs
    val lhs_ftv_of_stv = type_specs_lhs_ftv_of_stv type_specs

    val rhs_const_spec = apsnd (map_type_tvar rhs_ftv_of_stv) const_spec
    val lhs_var_spec = const_spec 
      |> #2 
      |> mk_lhs_stv 
      ||> map_type_tvar lhs_ftv_of_stv

    val prt =                               
      let val type_specs = map (apfst (rhs_ftv_of_stv #> dest_TFree)) type_specs
      in rhs_const_spec |> #2 |> CTR_Relators.pr_of_typ ctxt type_specs end
    
  in prt $ (Var lhs_var_spec) $ (Const rhs_const_spec) end;

(*transfer rule destruction*)
fun dest_trt (pr $ lhst $ rhst) = (pr, lhst, rhst)
  | dest_trt t = raise TERM ("dest_trt", single t);

(*conversion of a transfer rule goal to a parametricity property goal*)
fun prt_of_trt trt =
  let val (pr, lhst, rhst) = dest_trt trt
  in pr $ Const (rhst |> dest_Const |> #1, type_of lhst) $ rhst end;

end;