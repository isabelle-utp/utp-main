(* Title: ETTS/ETTS_RI.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Implementation of the functionality associated with the relativization
isomorphisms.
*)

signature ETTS_RI =
sig
val is_risset : term -> bool
val dest_rissetT : typ -> string * sort
val dest_rissetFree : term -> string * (string * sort)
val ftv_spec_of_rissetT_spec : string -> string * string list
val type_of_rissetT_spec : string -> typ
val fv_spec_of_rissetFree : string * string -> string * typ
val mk_Domainp_sc : term -> term -> term
val risset_input : Proof.context -> string -> term list -> unit
end;


structure ETTS_RI : ETTS_RI =
struct

(*representation/abstraction of the specification of the rissets*)
fun is_risset t = case type_of t of 
    (Type (\<^type_name>\<open>Set.set\<close>, [T])) => is_TFree T
  | _ => false
  andalso Term.add_tvars t [] |> null
  andalso Term.add_vars t [] |> null;
val dest_rissetT = HOLogic.dest_SetTFree;
fun dest_rissetFree (Free (c, T)) = (c, dest_rissetT T)
  | dest_rissetFree t = raise TERM("dest_rissetFree", single t);
fun ftv_spec_of_rissetT_spec (c : string) = (c, \<^sort>\<open>HOL.type\<close>)
fun type_of_rissetT_spec c = 
  Type (\<^type_name>\<open>Set.set\<close>, TFree (ftv_spec_of_rissetT_spec c) |> single);
fun fv_spec_of_rissetFree (tc : string, Tc : string) = 
  (tc, type_of_rissetT_spec Tc);

(*domain transfer rule associated with a relativization isomorphism*)
fun mk_Domainp_sc brelt rissett =
  let
    val T = rissett |> type_of |> dest_rissetT |> TFree
    val lhst = 
      Const 
        (
          \<^const_name>\<open>Relation.Domainp\<close>, 
          (type_of brelt) --> T --> HOLogic.boolT
        ) $ 
        brelt
    val rhst =
      let val U = T --> HOLogic.mk_setT T --> HOLogic.boolT 
      in Abs ("x", T, Const (\<^const_name>\<open>Set.member\<close>, U) $ Bound 0 $ rissett) end
  in HOLogic.mk_eq (lhst, rhst) end;

(*elements of the input error verification for the RIs*)
local

fun get_tvs t = t
  |> (fn t => (Term.add_tvars t [], Term.add_tfrees t []))
  |>> map TVar
  ||> map TFree
  |> op@;

fun ntv_eq ((TVar (xi, _)), (TVar (xi', _))) = Term.eq_ix (xi, xi')
  | ntv_eq (TFree (c, _), TFree (c', _)) = c = c'
  | ntv_eq (_, _) = false;

fun ex_eq_sorts_neq_ntvs thy = 
  partition_eq ntv_eq 
  #> map (distinct (Term.sort_eqT thy)) 
  #> exists (fn xs => 1 < length xs);

fun get_vs t = t
  |> (fn t => (Term.add_vars t [], Term.add_frees t []))
  |>> map Var
  ||> map Free
  |> op@;

fun tv_eq ((Var (xi, _)), (Var (xi', _))) = Term.eq_ix (xi, xi')
  | tv_eq (Free (c, _), Free (c', _)) = c = c'
  | tv_eq (_, _) = false;

fun type_eqT (t, u) =
  let
    val get_varT = type_of #> HOLogic.dest_SetT
    val T = get_varT t 
    val U = get_varT u
  in ntv_eq (T, U) end;

val ex_eq_types_neq_nvs = partition_eq tv_eq
  #> map (distinct type_eqT)
  #> exists (fn xs => 1 < length xs);

in

fun risset_input ctxt c risset = 
  let

    fun mk_msg_prefix msg = c ^ ": " ^ msg 

    val msg_riss_not_set = mk_msg_prefix
      "risset must be terms of the type of the form ?'a set or 'a set"
    val msg_riss_not_ds_dtv = mk_msg_prefix 
      "risset: type variables with distinct sorts must be distinct"
    val msg_riss_not_dt_dv = mk_msg_prefix 
      "risset: variables with distinct types must be distinct"

    val _ = risset |> map (type_of #> HOLogic.is_var_setT) |> List.all I
      orelse error msg_riss_not_set
    val _ = risset 
      |> map get_tvs
      |> flat
      |> ex_eq_sorts_neq_ntvs (Proof_Context.theory_of ctxt)
      |> not
      orelse error msg_riss_not_ds_dtv
    val _ = risset
      |> map get_vs
      |> flat
      |> ex_eq_types_neq_nvs 
      |> not
      orelse error msg_riss_not_dt_dv

  in () end;

end;

end;