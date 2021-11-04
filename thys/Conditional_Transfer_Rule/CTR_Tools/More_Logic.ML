(* Title: CTR_Tools/More_Logic.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the structure Logic from the standard library of Isabelle/Pure.
*)

signature LOGIC =
sig
  include LOGIC
  val unvarify_types_local_term : 
    Proof.context -> term -> term * Proof.context
  val unvarify_local_term : Proof.context -> term -> term * Proof.context
  val varifyT_mixed_global : typ -> typ
  val varify_mixed_global : term -> term
  val unoverload_types_term : theory -> term -> term
  val is_equals : term -> bool
end

structure Logic : LOGIC  =
struct

open Logic;

(*unvarify types in a local context*)
fun unvarify_types_local_factt ctxt ts = 
  let
    val stv_specs = ts
      |> map (fn thmt => Term.add_tvars thmt [] |> rev)
      |> flat
      |> distinct op=
    val ctxt' = fold Proof_Context.augment ts ctxt
    val (ftv_specs, _) = Variable.invent_types (map #2 stv_specs) ctxt'
    val ctxt'' = fold Variable.declare_typ (map TFree ftv_specs) ctxt
    val stv_to_ftv = stv_specs ~~ ftv_specs
      |> AList.lookup op= 
      #> the
      #> TFree
    val ts = map (map_types (map_type_tvar stv_to_ftv)) ts
  in (ts, ctxt'') end;

(*unvarify types in a single term in a local context*)
fun unvarify_types_local_term ctxt t = t
  |> single
  |> unvarify_types_local_factt ctxt
  |>> the_single;

(*unvarify terms in a local context*)
fun unvarify_local_factt ctxt ts =
  let
    val (ts, ctxt') = unvarify_types_local_factt ctxt ts
    val sv_specs = map (fn thmt => Term.add_vars thmt [] |> rev) ts
      |> flat 
      |> distinct op=
    val stvcs = sv_specs |> (#1 #> #1 |> map)
      |> Variable.variant_name_const ctxt'
      |> rev
    val ftvcs = Variable.variant_fixes stvcs ctxt' |> #1
    val ctxt'' = ctxt' |> Variable.add_fixes ftvcs |> #2
    val stvc_to_ftvc = (sv_specs ~~ (ftvcs ~~ map #2 sv_specs))
      |> AList.lookup op=  
      #> the
      #> Free
    val ts = map (Term.map_sv stvc_to_ftvc) ts
  in (ts, ctxt'') end;

(*unvarify a single term in a local context*)
fun unvarify_local_term ctxt thm = thm
  |> single
  |> unvarify_local_factt ctxt
  |>> the_single;

local

fun ftvs_stvs_map svtcs stvs = stvs
  |> map (apdupr #1)
  |> map_slice_r (fn cs => Name.variant_list svtcs cs) 
  |> map (K 0 |> apdupr |> apsnd)
  |> map (fn ((c, S), v) => ((c, S), (v, S))) 
  |> map (apsnd TVar)
  |> AList.lookup op= #> the
 
in
 
(*varify a type that may have occurrences of both schematic and fixed 
type variables*)
fun varifyT_mixed_global T = 
  let
    val svtcs = map (#1 #> #1) (Term.add_tvarsT T [])
    val ftvs_stvs_map = ftvs_stvs_map svtcs (Term.add_tfreesT T [])
  in Term.map_type_tfree ftvs_stvs_map T end;

(* varify a term that may have occurrences of both schematic and fixed 
variables and, also, both schematic and fixed type variables *)
fun varify_mixed_global t =
  let
    val svtcs = map (#1 #> #1) (Term.add_tvars t [])
    val ftvs_stvs_map = ftvs_stvs_map svtcs (Term.add_tfrees t [])
    val t = Term.map_tfree ftvs_stvs_map t 
    val svcs = map (#1 #> #1) (Term.add_vars t [])
    val fvs_svs_map = Term.add_frees t []
      |> map (apdupr #1)
      |> map_slice_r (fn cs => Name.variant_list svcs cs) 
      |> map (K 0 |> apdupr |> apsnd)
      |> map (fn ((c, T), v) => ((c, T), (v, T)))
      |> map (apsnd Var)
      |> AList.lookup op= #> the
    val t = Term.map_fv fvs_svs_map t
  in t end;

end;

(*unoverload all types in a term*)
fun unoverload_types_term thy t =
  let
    val sort_consts = Term.add_tvars t []
      |> map #2
      |> map (Sorts.params_of_sort thy)
      |> flat
      |> distinct op=
    val const_map = Term.add_consts t []
      |> distinct op=
      |> filter (member Term.could_match_const sort_consts)
      |> dup
      ||> map (#1 #> Long_Name.base_name)
      ||> Name.variant_list (Term.add_vars t [] |> map #1 |> map #1)
      |> op~~
      |> map (fn ((c, T), d) => ((c, T), Var ((d, 0), T)))
    fun const_map_opt const_spec = case AList.lookup op= const_map const_spec of 
      SOME t => t | 
      NONE => Const const_spec
    val t' = Term.map_const const_map_opt t
    val t'' =
      let                     
        val uctxt = Logic.unconstrainT [] t' |> #1
        (*Ported from Pure/Logic.ML with amendments*)
        val map_atyps = 
          Term.map_atyps (Type.default_sorts thy o (#atyp_map uctxt))
        (*Ported from Pure/Logic.ML with amendments*)
        val t'' = t'
          |> Term.map_types map_atyps
          |> curry Logic.list_implies (map #2 (#constraints uctxt));
        val prems = Logic.strip_imp_prems t'
        val prems = drop (length prems - Logic.count_prems t') prems
      in Logic.list_implies (prems, Logic.strip_imp_concl t'') end
  in t'' end;


(*equality*)
fun is_equals (Const (\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ _) = true
  | is_equals _ = false;

end;