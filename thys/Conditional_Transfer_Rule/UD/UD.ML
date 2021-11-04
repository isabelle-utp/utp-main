(* Title: UD/UD.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

The following file provides an implementation of the command ud.

The algorithm associated with the command ud draws inspiration and builds
upon the ideas associated with/expressed in 
  - The function Unoverload_Def.unoverload_def that was written by 
Fabian Immler and is available in the file HOL-Types_To_Sets/unoverload_def.ML 
in Isabelle2020. 
  - The conference proceedings article titled "A Mechanized Translation from 
Higher-Order Logic to Set Theory" written by Alexander Krauss and 
Andreas Schropp [1].

[1] Krauss A, Schropp A. A Mechanized Translation from Higher-Order Logic
to Set Theory. In: Kaufmann M, Paulson LC, editors. Interactive Theorem
Proving. Berlin: Springer; 2010. p. 323–38. 
(Lecture Notes in Computer Science; vol. 6172).
*)

signature UD =
sig
datatype ud_thm_out_type = trivial of thm | nontrivial of thm * thm
val axioms_of_ci : 
  theory -> Defs.T -> string * typ -> (string option * string) list
val das_of_ci : theory -> Defs.T -> string * typ -> thm list
val unoverload_definition : 
  binding * mixfix -> string * typ -> theory -> ud_thm_out_type * theory
end;


structure UD : UD =
struct



(**** Auxiliary ****)

fun mk_msg_unoverload_definition msg = "ud: " ^ msg;



(**** Data ****)

datatype ud_thm_out_type = trivial of thm | nontrivial of thm * thm



(**** Definitional Axioms ****)

(*the implementation of axioms_of_ci and da_of_ci are based on elements of 
the code HOL/Types_To_Sets/unoverloading.ML*)
local

fun match_args (Ts, Us) =
  if Type.could_matches (Ts, Us) 
  then 
    Option.map Envir.subst_type 
      (
        SOME (Type.raw_matches (Ts, Us) Vartab.empty) 
          handle Type.TYPE_MATCH => NONE
      )
  else NONE;

in

fun axioms_of_ci thy defs (c, T) = 
  let
    val const_entry = Theory.const_dep thy (c, T);
    val Uss = Defs.specifications_of defs (fst const_entry);
  in
    Uss
    |> filter (fn spec => is_some (match_args (#lhs spec, snd const_entry)))
    |> map (fn Us => (#def Us, #description Us))
  end;

fun das_of_ci thy defs = axioms_of_ci thy defs
  #> map #1
  #> filter is_some
  #> map (the #> try (Thm.axiom thy))
  #> filter is_some
  #> map (the #> Drule.abs_def);

end;



(**** Main ****)

local

val msg_no_cids = 
  mk_msg_unoverload_definition "no suitable constant-instance definitions";
val msg_ud_ex = 
  mk_msg_unoverload_definition "unoverloaded constant already exists";
val msg_multiple_cids = 
  mk_msg_unoverload_definition "multiple constant-instance definitions";
val msg_extra_type_variables = 
  mk_msg_unoverload_definition "specification depends on extra type variables";

fun map_sorts ctxt map_sortsT thm =
  let
    val Ts = thm
      |> Thm.full_prop_of
      |> (fn t => Term.add_tvars t [])
    val instTs = Ts
      |> map TVar
      |> map (Term.map_atyps (map_sortsT (Proof_Context.theory_of ctxt)))
      |> map (Thm.ctyp_of ctxt)
      |> curry op~~ Ts
  in Drule.instantiate_normalize (instTs, []) thm end;

fun trivial_ud thy b cid' =
  let
    val (with_thm, thy') =
      let 
        val b' = Binding.qualify_name true b "with"
        val attr = single UD_With.UDWithData.add
      in Global_Theory.add_thm ((b', cid'), attr) thy end
    val _ = 
      let val c = Thm.derivation_name with_thm
      in
        with_thm
        |> single
        |> CTR_Utilities.thm_printer (Proof_Context.init_global thy') true c
      end
  in (trivial with_thm, thy') end;

fun nontrivial_ud thy defs (b, mixfix) cid T =
  let

    fun mk_with_thm thm_rhs_ct with_def_thm cid =
      let
        val with_def_thm_rhs_ct = with_def_thm
          |> Thm.cprop_of
          |> Thm.dest_equals_rhs
        val inst = Thm.match (with_def_thm_rhs_ct, thm_rhs_ct)
        val const_with_def = with_def_thm
          |> Drule.instantiate_normalize inst
          |> Thm.symmetric
        val with_thm = Thm.transitive cid const_with_def
      in with_thm end;

    val ctxt = Proof_Context.init_global thy

    val cid' = Thm.unvarify_global thy cid 

    val cid_rhs_ct = cid' |> Thm.cprop_of |> Thm.dest_equals_rhs

    val (cid_rhs_t, ctxt') = cid_rhs_ct
      |> Thm.term_of 
      |> Logic.unoverload_types_term thy
      |> Logic.unvarify_types_local_term ctxt

    val rhs_consts = 
      let
        val sort_const_cs = Term.add_tvarsT T []
          |> map #2
          |> map (Sorts.params_of_sort thy)
          |> flat
          |> distinct op=
          |> map #1
        val consts = Term.add_consts cid_rhs_t []
        val consts_no_cids = consts
          |> map (fn const => (const, axioms_of_ci thy defs const))
          |> filter (fn (_, cid_opt) => null cid_opt)
          |> map fst
        val consts_in_sort = consts
          |> filter (fn (_, T) => Term.has_tfreesT T)
          |> filter (fn (c, _) => member op= sort_const_cs c)
        val elim_consts = thy
          |> UD_Consts.get_keys
          |> map (UD_Consts.const_of_key thy #> the #> dest_Const)
        val consts_out = consts_no_cids @ consts_in_sort 
          |> distinct op=
          |> filter_out (member (swap #> Term.could_match_const) elim_consts)
      in consts_out end

    val (cs, ctxt'') = ctxt'
      |> Variable.variant_fixes (map (#1 #> Long_Name.base_name) rhs_consts) 

    val fv_of_const = 
      (map Const rhs_consts ~~ map Free (cs ~~ map #2 rhs_consts))
      |> AList.lookup op=
      |> mk_opt_id I

    val rhs_const_ts = map Const rhs_consts
    val arg_ts = map fv_of_const rhs_const_ts

    val cid_rhs_t' = map_aterms fv_of_const cid_rhs_t

    fun declare_const_with thy =
      let
        val T = map type_of arg_ts ---> type_of cid_rhs_t'
        val b' = Binding.qualify_name true b "with"
      in Sign.declare_const_global ((b', T), mixfix) thy end

    val (lhst, thy') = declare_const_with thy

    val lhst' = Term.list_comb (lhst, arg_ts)

    val (with_def_thm, thy'') =
      let
        val b' = Binding.qualify_name true b "with_def"
        val def_t = Logic.mk_equals (lhst', cid_rhs_t')
      in 
        Global_Theory.add_defs false [((b', def_t), [])] thy' |>> the_single
          handle ERROR c =>
            let val msg_match = "Specification depends on extra type variables"
            in 
              if String.isSubstring msg_match c
              then error msg_extra_type_variables 
              else error c 
            end
      end

    val _ = 
      let val c = Thm.derivation_name with_def_thm
      in
        with_def_thm
        |> single
        |> CTR_Utilities.thm_printer (Proof_Context.init_global thy'') true c
      end

    val (with_thm, thy''') =
      let
        val b' = Binding.qualify_name true b "with"
        val with_thm = cid' 
          |> mk_with_thm cid_rhs_ct with_def_thm
          |> singleton (Proof_Context.export ctxt'' ctxt)
        val attr = single UD_With.UDWithData.add
      in Global_Theory.add_thm ((b', with_thm), attr) thy'' end

    val _ = 
      let val c = Thm.derivation_name with_thm
      in 
        with_thm
        |> single
        |> CTR_Utilities.thm_printer (Proof_Context.init_global thy''') true c
      end

  in (nontrivial (with_def_thm, with_thm), thy''') end;

in

fun unoverload_definition (b, mixfix) (c, T) thy =
  let


    (*auxiliary*)

    fun get_ud_const lr ud_thms = 
      let 
        val get_ud_const_impl = Thm.cprop_of
          #> lr
          #> Thm.term_of
          #> strip_abs_body
          #> head_of
          #> dest_Const
      in map get_ud_const_impl ud_thms end


    (*main*)

    val ctxt = Proof_Context.init_global thy
    
    val defs = Theory.defs_of thy

    val ud_thms = ctxt
      |> UD_With.UDWithData.get
      |> map (Local_Defs.meta_rewrite_rule ctxt)

    val T' = T
      |> Type.default_sorts_of_empty_sorts thy
      |> Logic.varifyT_mixed_global

    val _ =
      let 
        val ud_lhs_consts = get_ud_const Thm.dest_equals_lhs ud_thms
        val ex = member (swap #> Term.could_match_const) ud_lhs_consts (c, T')
      in not ex orelse error msg_ud_ex end

    val cids = das_of_ci thy defs (c, T')
    
    val cid = 
      if null cids 
      then error msg_no_cids
      else 
        if length cids = 1 
        then the_single cids 
        else error msg_multiple_cids

    val cid' = 
      let
        val lhs_const = cid
          |> Thm.cprop_of
          |> Thm.dest_equals_lhs
          |> Thm.term_of
          |> head_of
        val insts = (lhs_const, Const (c, T'))
          |> apply2 (Thm.cterm_of ctxt)
          |> Thm.first_order_match
      in 
        cid
        |> Drule.instantiate_normalize insts
        |> map_sorts ctxt Type.default_sorts_of_empty_sorts
        |> Local_Defs.unfold ctxt ud_thms
      end

    val cid_rhs_t = cid' 
      |> Thm.cprop_of 
      |> Thm.dest_equals_rhs
      |> Thm.term_of 

    val trivial_flag = 
      let val ud_rhs_consts = get_ud_const Thm.dest_equals_rhs ud_thms
      in
        Term.is_comb cid_rhs_t
        andalso cid_rhs_t |> head_of |> is_Const
        andalso cid_rhs_t
          |> head_of
          |> dest_Const
          |> member (swap #> Term.could_match_const) ud_rhs_consts
      end

    val (ud_thm_out, thy') =
      if trivial_flag
      then trivial_ud thy b cid'
      else nontrivial_ud thy defs (b, mixfix) cid' T'

  in (ud_thm_out, thy') end;

end;



(**** Interface ****)

val msg_not_constant = 
  mk_msg_unoverload_definition "the input term is not a constant";

fun process_ud ((b_opt, t), mixfix) thy = 
  let 
    val t' = Proof_Context.read_term_pattern (Proof_Context.init_global thy) t
    val (c, T) = dest_Const t'
      handle TERM _ => error msg_not_constant 
    val b = case b_opt of
        SOME b => b
      | NONE => Binding.name (Long_Name.base_name c)
  in unoverload_definition (b, mixfix) (c, T) thy |> #2 end;

val parse_ud = Scan.option Parse.binding -- Parse.const -- Parse.opt_mixfix';

val _ = Outer_Syntax.command
  \<^command_keyword>\<open>ud\<close> 
  "unoverloading of constant-instance definitions"
  (parse_ud >> (process_ud #> Toplevel.theory));

end;