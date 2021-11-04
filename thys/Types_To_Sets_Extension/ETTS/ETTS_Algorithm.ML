(* Title: ETTS/ETTS_Algorithm.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Implementation of the ERA.
*)

signature ETTS_ALGORITHM =
sig

(*misc*)
val mk_local_typedef_ex : (string * sort) * term -> term
val dest_local_typedef_ex : term -> typ * term

(*output type*)
datatype etts_output_type = default | verbose | active
val etts_output_type_of_string : string -> etts_output_type
val string_of_etts_output_type : etts_output_type -> string 
val is_verbose : etts_output_type -> bool
val is_active : etts_output_type -> bool
val is_default : etts_output_type -> bool

(*relativization*)
val etts_algorithm :
  Proof.context ->
  etts_output_type ->
  int list ->
  (indexname * term) list ->
  (term * term) list ->
  (Facts.ref * Token.src list) option ->
  (Facts.ref * Token.src list) list ->
  (term list * (Proof.context -> tactic)) option -> 
  Token.src list ->
  thm ->
  (thm * int list) * Proof.context
val etts_fact : 
  Proof.context ->
  etts_output_type ->
  int list ->
  (indexname * term) list ->
  (term * term) list ->
  (Facts.ref * Token.src list) option ->
  (Facts.ref * Token.src list) list ->
  (term list * (Proof.context -> tactic)) option ->
  Token.src list ->
  thm list ->
  (thm list * int list) * Proof.context

end;


structure ETTS_Algorithm : ETTS_ALGORITHM =
struct



(**** Prerequisites ****)

open UD_With;
open ETTS_Utilities;
open ETTS_RI;
open ETTS_Substitution;




(**** Misc ****)

fun mk_local_typedef_ex (rcd_spec, rissett) =
  let
    val T = TFree rcd_spec
    val risset_ftv = rissett 
      |> type_of 
      |> (fn T => Term.add_tfreesT T []) 
      |> the_single
      |> TFree
  in 
    HOLogic.mk_exists 
      (
        "rep", 
        T --> risset_ftv,
        HOLogic.mk_exists  
          (
            "abs", 
            risset_ftv --> T,
            HOLogic.mk_type_definition_pred T risset_ftv $ Bound 1 $ Bound 0 $ rissett
          )
      )
  end;

fun dest_local_typedef_ex t = 
  let
    val (_, T', t') = HOLogic.dest_exists t
      handle TERM ("dest_exists", _) => 
        raise TERM ("dest_local_typedef_ex", single t)
    val (_, _, t'') = HOLogic.dest_exists t'
      handle TERM ("dest_exists", _) => 
        raise TERM ("dest_local_typedef_ex", single t)
    val (T''', _) = dest_funT T'
    val t''' = t'' |> HOLogic.dest_type_definition |> #3
  in (T''', t''') end;




(**** Output type ****)

datatype etts_output_type = default | verbose | active;

fun etts_output_type_of_string "" = default
  | etts_output_type_of_string "!" = verbose
  | etts_output_type_of_string "?" = active
  | etts_output_type_of_string _ = 
      error "etts_output_type_of_string: invalid input";

fun string_of_etts_output_type default = "default"
  | string_of_etts_output_type verbose = "verbose"
  | string_of_etts_output_type active = "active";
 
fun is_verbose verbose = true
  | is_verbose _ = false;

fun is_active active = true
  | is_active _ = false;

fun is_default default = true
  | is_default _ = false;




(**** Auxiliary functions ****)



(*** Standard output ***)

fun verbose_writer_prem etts_output_type writer c = 
  if is_verbose etts_output_type 
  then ETTS_Writer.write_action c writer 
  else writer

fun verbose_writer_concl_thms etts_output_type ctxt thms = 
  if is_verbose etts_output_type
  then map (Thm.string_of_thm ctxt #> writeln) thms
  else single ();

fun verbose_writer_concl_types etts_output_type ctxt Ts = 
  if is_verbose etts_output_type
  then map (Syntax.string_of_typ ctxt #> writeln) Ts
  else single ();



(*** Types-To-Sets ***)

(*multiple applications of the function cancel_type_definition*)
fun cancel_type_definition_repeat n thm =
  let
    fun apply_cancel_type_definition 0 thm = thm
      | apply_cancel_type_definition n thm = thm 
          |> Local_Typedef.cancel_type_definition
          |> rotate_prems 1
          |> apply_cancel_type_definition (n - 1)
  in
    thm 
    |> apply_cancel_type_definition n 
    |> rotate_prems (~n) 
  end;



(**** Initialization of the relativization context ****)

local



(*** Auxiliary ***)

(*theorems used for the relativization in conjunction with transfer*)
val risset_tthms = 
  [@{thm type_definition_Domainp}, @{thm type_definition_Domainp'}];
val sc_tthms = 
  [ 
    @{thm typedef_bi_unique},
    @{thm typedef_right_total},
    @{thm typedef_left_unique},
    @{thm typedef_right_unique}
  ];                                       

(*obtain the types associated with a relativization isomorphism*)
fun get_riT rit = rit 
  |> type_of 
  |> (fn T => (T |> binder_types |> the_single, body_type T));

(*create the rhs of the specification of cr*)
fun mk_cr_rhst rept =
  let
    val (isoT, domT) = get_riT rept
    val rhst = 
      Abs 
        (
          "r", 
          domT, 
          Abs 
            (
              "a", 
              isoT, 
              Const (\<^const_name>\<open>HOL.eq\<close>, domT --> domT --> HOLogic.boolT) $ 
                Bound 1 $ 
                (rept $ Bound 0)
           )
        )
  in rhst end;

(*initialization*)
fun etts_rlt_ctxt_intialize rispec = length rispec;

(*declare fresh ris*)
fun etts_rlt_ctxt_mk_fresh_ris ctxt rispec = rispec
  |> map #2
  |> map (fn t => Term.add_frees t [])
  |> flat
  |> dup
  ||> map #1
  ||> Variable.fix_new_vars ctxt
  |>> map Free  
  |-> fold_rev Variable.declare_term;

(*create fresh risstv isomorphic to risset*)
fun etts_rlt_ctxt_mk_fresh_risstv ctxt etts_output_type writer nds rispec = 
  let
    val writer' = verbose_writer_prem 
      etts_output_type writer "types associated with the RIs..."
    val (rispec', ctxt') = ctxt
      |> (\<^sort>\<open>HOL.type\<close> |> replicate nds |> Variable.invent_types)
      |>> curry (swap #> op~~) rispec
    val _ = verbose_writer_concl_types 
      etts_output_type ctxt' (map (#1 #> TFree) rispec')
  in ((writer', rispec'), ctxt') end;

(*assumptions for the local typedef*)
fun etts_rlt_ctxt_mk_ltd_assms ctxt etts_output_type writer rispec = 
  let
    val writer' = verbose_writer_prem 
      etts_output_type writer "assumptions for the local typedef..."
    val (ltd_assms, ctxt') = rispec
      |> 
        (
          apsnd #2 
          #> mk_local_typedef_ex 
          #> HOLogic.mk_Trueprop 
          #> Thm.cterm_of ctxt
          |> map
        )
      |> (fn ltdts => Assumption.add_assumes ltdts ctxt)
    val _  = verbose_writer_concl_thms etts_output_type ctxt' ltd_assms
  in ((writer', ltd_assms), ctxt') end;



(*** Transfer relations associated with relativization isomorphisms ***)

local

fun mk_ex_crt rept =
  let
    val (isoT, domainT) = get_riT rept
    val crT = domainT --> isoT --> HOLogic.boolT
    val rhst = mk_cr_rhst rept
    val t = HOLogic.mk_exists 
      (
        "cr", 
        crT, 
        Const (\<^const_name>\<open>HOL.eq\<close>, crT --> crT --> HOLogic.boolT) $ 
          Bound 0 $ 
          rhst
      )
  in t end;

in

fun etts_rlt_ctxt_mk_crs ctxt etts_output_type writer nds ltd_assms = 
  let
    val writer' = verbose_writer_prem etts_output_type writer "crs..."
    val ((ra_var_specs, ra_thms), ctxt') = ctxt
      |> Obtain.result 
        (K (REPEAT (eresolve_tac ctxt (single @{thm exE}) 1))) ltd_assms
    val repts = ra_var_specs 
      |> map (#2 #> Thm.term_of) 
      |> chop nds
      |> #1
    val ex_cr_thms =
      let 
        val hol_ex_cr_tac = resolve_tac ctxt' (single @{thm ex_eq}) 1
        fun hol_cr_prover thm = 
          Goal.prove ctxt' [] [] thm (K (hol_ex_cr_tac))
      in map (mk_ex_crt #> HOLogic.mk_Trueprop #> hol_cr_prover) repts end
    val ((crts, hol_cr_thms), ctxt'') = ctxt'
      |> Obtain.result 
        (K (REPEAT (eresolve_tac ctxt' (single @{thm exE}) 1))) ex_cr_thms
      |>> (fn x => x |>> map #2 |>> map Thm.term_of)
    val pure_cr_thms = 
      let
        val pure_crts = map Logic.mk_equals (crts ~~ (map mk_cr_rhst repts))
        fun pure_cr_tac thm _ = 
          Object_Logic.full_atomize_tac ctxt'' 1
          THEN resolve_tac ctxt'' (single thm) 1
        fun pure_cr_prover (goal, tac_thm) = 
          Goal.prove ctxt'' [] [] goal (pure_cr_tac tac_thm)
      in map pure_cr_prover (pure_crts ~~ hol_cr_thms) end
    val _  = verbose_writer_concl_thms etts_output_type ctxt'' pure_cr_thms
  in ((writer', ra_thms, crts, pure_cr_thms), ctxt'') end;

end;



(*** Transfer rules for the relativization isomorphisms ***)

fun etts_rlt_ctxt_mk_ri_tr ctxt etts_output_type writer ra_thms pure_cr_thms =  
  let
    val writer' = 
      verbose_writer_prem etts_output_type writer "main transfer rules..."
    val (risset_transfer_thms, sc_transfer_thms) =
      let 
        val OFthms = map list_of_pair (ra_thms ~~ pure_cr_thms)
        val apply_OFthms = 
          map (fn thm => map ((curry op OF) thm) OFthms) #> flat
      in (risset_tthms, sc_tthms) |>> apply_OFthms ||> apply_OFthms end
    val _  = verbose_writer_concl_thms 
      etts_output_type ctxt (risset_transfer_thms @ sc_transfer_thms)
  in (writer', risset_transfer_thms, sc_transfer_thms) end;



(*** Transfer rules for the set-based terms ***)

local

fun get_sc_ex_rissets risset_transfer_thms sc_transfer_thms = 
  let val nds = (length risset_transfer_thms) div (length risset_tthms)
  in
    (risset_transfer_thms, sc_transfer_thms)
    |>> take nds
    ||> chop nds
    ||> (nds |> chop #> #1 |> apsnd)
    ||> op ~~
    |> op ~~
  end;

in

fun etts_rlt_ctxt_mk_sbt_tr 
  ctxt
  etts_output_type 
  writer 
  risset_transfer_thms 
  sc_transfer_thms 
  rispec 
  sbtspec = 
  let
    val writer' = verbose_writer_prem 
      etts_output_type writer "transfer rules for the sbts..."
    val ((sbtspec_specs, pp_thms), ctxt') = 
      let
        val sc_ex_rissets = get_sc_ex_rissets risset_transfer_thms sc_transfer_thms
        val scthms_of_ftv =
          let
            val scthms_ftv = 
              (
                map (#1 #> #2 #> #2 #> type_of #> dest_rissetT) rispec ~~ 
                map reroute_sp_triple sc_ex_rissets
              )
          in AList.lookup op= scthms_ftv end
        fun thm_prem_ftvs thm = thm
          |> Thm.prems_of
          |> map (fn t => Term.add_tfrees t [])
          |> flat
          |> distinct op=
        fun get_sc_ftv_specs (thm_ftv_specs, rvt_ftv_specs) = rvt_ftv_specs
          |> subtract op= (rvt_ftv_specs |> subtract op= thm_ftv_specs)
        fun obtain_prs ctxt ex_pr_thms = case ex_pr_thms of 
            [] => (([], []), ctxt)
          | _ => Obtain.result 
              (K (REPEAT (eresolve_tac ctxt (single @{thm exE}) 1))) 
              ex_pr_thms
              ctxt
      in
        sbtspec
        |>
          (
            (Thm.cterm_of ctxt #> (sbt_data_of ctxt #> the) |> apdupl)
            #> swap
            |> apsnd
            #> reroute_sp_ps
            |> map
          )
        |> map (reroute_ps_sp #> apsnd swap)
        |> 
          (
            (fn (thm, t) => (thm, (thm, t)))
            #> 
              (
                (apfst thm_prem_ftvs) 
                #> (type_of #> (fn t => Term.add_tfreesT t []) |> apsnd)
                #> get_sc_ftv_specs
                #> 
                  (
                    Option.compose (list_of_triple, scthms_of_ftv)
                    #> 
                      (
                        fn xs_opt => case xs_opt of 
                            SOME xs_opt => xs_opt 
                          | NONE => []
                      )
                    |> map 
                    #> flat 
                  )
                |> apsnd
              )
            #> op OF
            |> apsnd 
            |> map
          )
        |> split_list
        ||> obtain_prs ctxt
        |> reroute_sp_ps
        |>> reroute_sp_ps
        |>> apfst op~~
        |>> (#2 |> apsnd |> map |> apfst)
        |>> apsnd Transfer.mk_transfer_rels
      end
    val _  = verbose_writer_concl_thms etts_output_type ctxt' pp_thms
  in ((writer', pp_thms, sbtspec_specs), ctxt') end;

end;



(*** Post-processing ***)


(** Post-processing 1: transfer theorems **)

fun etts_rlt_ctxt_mk_transfer risset_transfer_thms sc_transfer_thms pp_thms = 
  risset_transfer_thms @ sc_transfer_thms @ pp_thms;


(** Post-processing 2: rispec lookup **)

fun etts_rlt_ctxt_mk_rispec rispec = 
  map (#1 #> swap #> apfst #1) rispec;


(** Post-processing 3: sbtspec lookup **)

fun etts_rlt_ctxt_mk_sbtspec sbtspec_specs = 
  let
    val sbtspec_var_specs = sbtspec_specs
      |> filter (apfst is_Var #> #1)
      |> map (apfst dest_Var)
    val sbtspec_const_specs = sbtspec_specs
      |> filter (apfst is_Const #> #1)
      |> map (apfst dest_Const)
  in (sbtspec_var_specs, sbtspec_const_specs) end;


in


(*** Main ***)

fun init_rlt_ctxt ctxt etts_output_type writer rispec sbtspec = 
  let
    val nds = etts_rlt_ctxt_intialize rispec
    val ctxt' = etts_rlt_ctxt_mk_fresh_ris ctxt rispec
    val ((writer', rispec'), ctxt'') = etts_rlt_ctxt_mk_fresh_risstv 
      ctxt' etts_output_type writer nds rispec
    val ((writer'', ltd_assms), ctxt''') = etts_rlt_ctxt_mk_ltd_assms 
      ctxt'' etts_output_type writer' rispec'
    val ((writer''', ra_thms, crts, pure_cr_thms), ctxt'''') = 
      etts_rlt_ctxt_mk_crs ctxt''' etts_output_type writer'' nds ltd_assms
    val rispec'' = rispec' ~~ crts
    val (writer'''', risset_transfer_thms, sc_transfer_thms) = etts_rlt_ctxt_mk_ri_tr 
      ctxt'''' etts_output_type writer''' ra_thms pure_cr_thms
    val ((writer''''', pp_thms, sbtspec_specs), ctxt''''') = 
      etts_rlt_ctxt_mk_sbt_tr 
        ctxt''''
        etts_output_type 
        writer'''' 
        risset_transfer_thms 
        sc_transfer_thms 
        rispec''
        sbtspec
    val transfer_thms = etts_rlt_ctxt_mk_transfer 
      risset_transfer_thms sc_transfer_thms pp_thms
    val rispec''' = etts_rlt_ctxt_mk_rispec rispec''
    val (sbtspec_var_specs, sbtspec_const_specs) = 
      etts_rlt_ctxt_mk_sbtspec sbtspec_specs
  in 
    (
      ctxt,
      ctxt''''',
      writer''''',
      rispec''',
      sbtspec_var_specs,
      sbtspec_const_specs,
      transfer_thms
    )
  end;

end;




(**** Kernel of the relativization algorithm ****)

local



(*** Naming conventions for schematic type variables ***)

fun etts_algorithm_fresh_stv 
  ctxt
  writer
  rispec 
  sbtspec_var_specs 
  sbtspec_const_specs 
  thm =
  let

    val stvs = thm |> Thm.full_prop_of |> (fn t => Term.add_tvars t [])
    val rispec' = rispec
      |> filter (fn (v, _) => member op= (map fst stvs) v)
      |> map (apfst (apdupr ((AList.lookup op= stvs #> the))))
    val thm_stvs =
      let val cs = rispec' |> map fst |> map fst |> map fst
      in stvs |> filter (fn (v, _) => fst v |> member op= cs |> not) end
    val cs =
      let
        fun folder c (cs, nctxt) = 
          let val out = Name.variant c nctxt 
          in (fst out::cs, snd out) end
        val cs = rispec' |> map snd |> map fst
        val nctxt = fold Name.declare cs (Variable.names_of ctxt)
      in fold folder (thm_stvs |> map fst |> map fst) ([], nctxt) |> fst end
    val rhsTs = cs ~~ map (reroute_ps_sp #> snd) thm_stvs
      |> map reroute_sp_ps
      |> map TVar

    val thm' = 
      let val rhs_cT = map (Thm.ctyp_of ctxt) rhsTs
      in Drule.instantiate_normalize (thm_stvs ~~ rhs_cT, []) thm end
    fun thm_stvs_map (v, T) = 
      case AList.lookup op= (thm_stvs ~~ rhsTs) (v, T) of 
          SOME T => T
        | NONE => TVar (v, T)
    val sbtspec_var_specs = sbtspec_var_specs 
      |> map (fn ((v, T), x) => ((v, map_type_tvar thm_stvs_map T), x))
    val sbtspec_const_specs = sbtspec_const_specs 
      |> map (fn ((c, T), x) => ((c, map_type_tvar thm_stvs_map T), x))

    val thm_stvs = thm' |> Thm.full_prop_of |> (fn t => Term.add_tvars t [])
    val thm_stvs_map = map_type_tvar 
      (fn (v, _) => TVar (v, (AList.lookup op= thm_stvs #> the) v))
    val sbtspec_const_specs = sbtspec_const_specs 
      |> map (fn ((c, T), x) => ((c, thm_stvs_map T), x))

  in ((writer, rispec', sbtspec_var_specs, sbtspec_const_specs), thm') end;



(*** Unfold ud_with ***)

fun etts_algorithm_unfold_ud_with 
  ctxt'' 
  etts_output_type 
  writer 
  sbtspec_var_specs
  sbtspec_const_specs
  thm = 
  let

    val writer' = verbose_writer_prem etts_output_type writer "unfold ud_with..."
    val ud_with_thms = ctxt''
      |> UDWithData.get 
      |> map (Local_Defs.meta_rewrite_rule ctxt'')

    val thm' = Local_Defs.unfold ctxt'' ud_with_thms thm

    val stvs = thm' |> Thm.full_prop_of |> (fn t => Term.add_vars t [])
    val consts = thm' |> Thm.full_prop_of |> (fn t => Term.add_consts t [])
    val sbtspec_var_specs = sbtspec_var_specs
      |> filter (fn ((v, T), _) => member op= stvs (v, T))
    val sbtspec_const_specs = sbtspec_const_specs
      |> filter (fn (const, _) => member op= consts const)
    val sbtspec_specs =
      (
        (map (apfst Var) sbtspec_var_specs) @
        (map (apfst Const) sbtspec_const_specs)
      )
    val _ = verbose_writer_concl_thms etts_output_type ctxt'' (single thm')

  in ((writer', sbtspec_specs), thm') end;



(*** Unoverload types ***)

fun etts_algorithm_unoverload_types 
  ctxt' etts_output_type writer rispec sbtspec_specs thm =
  let

    val writer' = 
      verbose_writer_prem etts_output_type writer "unoverload types..."

    val thm' = Unoverload_Type.unoverload_type 
      (Context.Proof ctxt') (rispec |> map (#1 #> #1) |> rev) thm

    val t = Thm.full_prop_of thm
    val n = Logic.count_prems t
   
    val out_t = Thm.full_prop_of thm'
    val out_n = Logic.count_prems out_t

    val out_prem_ts = out_t |> Logic.strip_imp_prems |> drop (out_n - n)

    val out_t' = Logic.list_implies (out_prem_ts, Logic.strip_imp_concl out_t)
    
    val (mapT, mapt) = (Thm.cterm_of ctxt' out_t', Thm.cprop_of thm)
      |> Thm.match 
      |>> map (apfst TVar)
      ||> map (apfst Var)
      |>> map (apsnd Thm.typ_of)
      ||> map (apsnd Thm.term_of)
      |>> map swap
      ||> map swap

    val rispec' = rispec
      |> map (apfst TVar)
      |> map (apfst (map_atyps (AList.lookup op= mapT #> the))) 
      |> map (apfst dest_TVar)

    val sbtspec_specs' = sbtspec_specs
      |> map (apfst (map_aterms (AList.lookup op= mapt #> the))) 
      |> map (apfst dest_Var)
      |> map (apfst (apsnd (map_atyps (AList.lookup op= mapT #> the))))

    val _ = verbose_writer_concl_thms etts_output_type ctxt' (single thm')

  in ((writer', rispec', sbtspec_specs'), thm') end;



(*** Substitution of type variables ***)
                                                                
fun etts_algorithm_subst_type ctxt' etts_output_type writer rispec thm =
  let
    val writer' = verbose_writer_prem 
      etts_output_type writer "substitution of type variables..."
    val thm' = 
      Drule.instantiate_normalize 
        (
          rispec 
          |> map (apsnd TFree) 
          |> map (apsnd (Thm.ctyp_of ctxt')), 
          []
        )
        thm
    val _ = verbose_writer_concl_thms etts_output_type ctxt' (single thm')
  in (writer', thm') end;



(*** Substitution of variables ***)

fun etts_algorithm_subst_var ctxt' etts_output_type writer sbtspec_specs thm =
  let
    val writer' = verbose_writer_prem 
      etts_output_type writer "substitution of variables..."
    val thm' = sbtspec_specs
      |> (Var #> (ctxt' |> Thm.cterm_of) |> apfst |> map)
      |> map Thm.first_order_match
      |> fold Drule.instantiate_normalize
      |> curry op|> thm
    val _ = verbose_writer_concl_thms etts_output_type  ctxt' (single thm')
  in (writer', thm') end;



(*** Untransfer ***)

fun etts_algorithm_untransfer ctxt' etts_output_type writer transfer_thms thm =
  let
    val writer' = verbose_writer_prem etts_output_type writer "untransfer..."
    val (thm', context) = Thm.apply_attribute
      (Transfer.untransferred_attribute transfer_thms) 
      thm 
      (Context.Proof ctxt')  
    val _ = verbose_writer_concl_thms etts_output_type ctxt' (single thm')
  in (context, writer', thm') end;



(*** Export ***)

fun etts_algorithm_export context ctxt etts_output_type writer thm =
  let
    val writer' = verbose_writer_prem etts_output_type writer "export..."
    val thy' = Context.theory_of context
    val ctxt' = Context.proof_of context
    val ctxt'' = Proof_Context.transfer thy' ctxt    
    val thm' = singleton (Proof_Context.export ctxt' ctxt'') thm
    val _ = verbose_writer_concl_thms etts_output_type ctxt'' (single thm')
  in ((writer', thm'), ctxt'') end;



(*** Cancel type definition ***)

fun etts_algorithm_ctd ctxt etts_output_type writer rispec thm =
  let
    val writer' = 
      verbose_writer_prem etts_output_type writer "cancel type definition..."
    val thm' = (rispec |> length |> cancel_type_definition_repeat) thm
    val _ = verbose_writer_concl_thms etts_output_type ctxt (single thm')
  in ((writer', thm'), ctxt) end;

in

fun etts_kera 
  ctxt 
  ctxt' 
  etts_output_type
  writer
  rispec 
  sbtspec_var_specs 
  sbtspec_const_specs 
  transfer_thms 
  thm =
  let
    val ((writer', rispec, sbtspec_var_specs, sbtspec_const_specs), thm') = 
      etts_algorithm_fresh_stv
        ctxt' 
        writer
        rispec 
        sbtspec_var_specs 
        sbtspec_const_specs 
        thm
    val ((writer'', sbtspec_specs), thm'') = 
      etts_algorithm_unfold_ud_with 
        ctxt' 
        etts_output_type 
        writer' 
        sbtspec_var_specs
        sbtspec_const_specs 
        thm'
    val ((writer''', rispec, sbtspec_specs'), thm''') = 
      etts_algorithm_unoverload_types 
        ctxt' etts_output_type writer'' rispec sbtspec_specs thm''
    val (writer'''', thm'''') = etts_algorithm_subst_type 
      ctxt' etts_output_type writer''' rispec thm'''
    val (writer''''', thm''''') = etts_algorithm_subst_var 
      ctxt' etts_output_type writer'''' sbtspec_specs' thm''''
    val (context, writer'''''', thm'''''') = etts_algorithm_untransfer 
      ctxt' etts_output_type writer''''' transfer_thms thm'''''
    val ((writer''''''', thm'''''''), ctxt'') = etts_algorithm_export 
      context ctxt etts_output_type writer'''''' thm''''''
    val ((writer'''''''', thm''''''''), ctxt''') = etts_algorithm_ctd 
      ctxt'' etts_output_type writer''''''' rispec thm'''''''
  in ((thm'''''''', writer''''''''), ctxt''') end;

end;




(**** Post-processing ****)

local



(*** Post-processing 1: simplification ***)

fun etts_algorithm_simplification ctxt etts_output_type writer sbrr_opt thm =
  let
    val writer = verbose_writer_prem etts_output_type writer "simplification..."
    val out_thm = More_Simplifier.rewrite_simp_opt' ctxt sbrr_opt thm
    val _ = verbose_writer_concl_thms etts_output_type ctxt (single out_thm)
  in (writer, out_thm) end;



(*** Post-processing 2: substitution of known premises ***)

local

(*ad-hoc application specific term equivalence*)
fun term_equiv_st (t, u) =
  let
    fun term_equiv_st ((Const (a, T)), (Const (b, U))) = 
          a = b andalso Type.could_match (T, U)
      | term_equiv_st ((Free (_, T)), (Free (_, U))) = Type.could_match (T, U)
      | term_equiv_st ((Var (_, T)), (Var (_, U))) = Type.could_match (T, U)
      | term_equiv_st ((Free (_, T)), (Var (_, U))) = Type.could_match (T, U)
      | term_equiv_st ((Var (_, T)), (Free (_, U))) = Type.could_match (T, U)
      | term_equiv_st ((Const (_, T)), (Free (_, U))) = Type.could_match (T, U)
      | term_equiv_st ((Free (_, T)), (Const (_, U))) = Type.could_match (T, U)
      | term_equiv_st ((Const (_, T)), (Var (_, U))) = Type.could_match (T, U)
      | term_equiv_st ((Var (_, T)), (Const (_, U))) = Type.could_match (T, U)
      | term_equiv_st ((Bound n), (Bound m)) = (n = m)
      | term_equiv_st ((Abs (_, T, t)), (Abs (_, U, u))) = 
          Type.could_match (T, U) andalso term_equiv_st (t, u)
      | term_equiv_st ((tl $ tr), (ul $ ur)) = 
          term_equiv_st (tl, ul) andalso term_equiv_st (tr, ur)
      | term_equiv_st ((Var (_, T)), (ul $ ur)) = 
          Type.could_match (T, type_of (ul $ ur))
      | term_equiv_st ((Var (_, T)), (Abs (c, U, u))) = 
          Type.could_match (T, type_of (Abs (c, U, u)))
      | term_equiv_st (_, _) = false;
  in 
    if 
      (Term.add_frees t [] |> null |> not) 
      andalso (Term.add_frees u [] |> null |> not) 
    then term_equiv_st (t, u)  
    else false
  end;

in

fun etts_algorithm_subst_prems ctxt etts_output_type writer subst_thms thm =
  let
    val writer' = verbose_writer_prem 
      etts_output_type writer "substitute known premises..."
    val thm' = 
      let 
        val subst_thms = Attrib.eval_thms ctxt subst_thms
        val subst_thmst = map Thm.full_prop_of subst_thms 
        fun option_thm thm_opt = case thm_opt of 
            SOME thm => thm 
          | _ => @{thm _}
        fun mk_OFthms ts = ts
          |> 
            (
              (subst_thmst ~~ subst_thms) 
              |> AList.lookup term_equiv_st 
              |> map
            )
          |> map option_thm
        fun subst_premises_repeat thm = 
          let
            val premsts = thm |> Thm.full_prop_of |> Logic.strip_imp_prems
            val out_thm = thm OF (mk_OFthms premsts)
          in 
            if Thm.nprems_of thm = Thm.nprems_of out_thm 
            then out_thm
            else subst_premises_repeat out_thm
          end
      in subst_premises_repeat thm end
    val _ = verbose_writer_concl_thms etts_output_type ctxt (single thm')
  in (writer', thm') end;

end;



(*** Post-processing 3: elimination of premises ***)

fun etts_algorithm_premred ctxt etts_output_type writer mpespc_opt thm =
  let
    val writer' = 
      verbose_writer_prem etts_output_type writer "elimination of premises..."
    val thm' = case mpespc_opt of 
        SOME m_spec => 
          let 
            val (out_thm, ctxt') = Thm.unvarify_local_thm ctxt thm
            val out_thm = out_thm 
              |> ETTS_Tactics.prem_red ctxt' m_spec 
              |> singleton (Proof_Context.export ctxt' ctxt) 
          in out_thm end
      | NONE => thm
    val _ = verbose_writer_concl_thms etts_output_type ctxt (single thm')
  in (writer', thm') end;



(*** Post-processing 4: application of the attributes ***)

fun etts_algorithm_app_attrb ctxt etts_output_type writer attrbs thm =
  let
    val writer' = verbose_writer_prem etts_output_type writer 
      "application of the attributes for the set-based theorem..."
    val (thm', ctxt') =
      let 
        val attrbs = 
          map (Attrib.check_src ctxt #> Attrib.attribute ctxt) attrbs
      in Thm.proof_attributes attrbs thm ctxt end
    val _ = verbose_writer_concl_thms etts_output_type ctxt' (single thm')
  in (writer', thm') end;

in

fun etts_algorithm_pp
  ctxt etts_output_type writer sbrr_opt subst_thms mpespc_opt attrbs thm =
  let
    val (writer', thm') = etts_algorithm_simplification 
      ctxt etts_output_type writer sbrr_opt thm
    val (writer'', thm'') = etts_algorithm_subst_prems 
      ctxt etts_output_type writer' subst_thms thm'
    val (writer''', thm''') = etts_algorithm_premred 
      ctxt etts_output_type writer'' mpespc_opt thm''
    val (writer'''', thm'''') = etts_algorithm_app_attrb 
      ctxt etts_output_type writer''' attrbs thm''' 
  in ((thm'''', writer''''), ctxt) end;

end;




(**** Extended relativization algorithm ****)

local

fun mk_msg_etts_algorithm msg = "tts_algorithm: " ^ msg;

fun etts_algorithm_input rispec thm =
  let

    val msg_etts_context = mk_msg_etts_algorithm
      "ERA can only be invoked from an appropriately parameterized tts context"
    val msg_ftvs = mk_msg_etts_algorithm
      "fixed type variables must not occur in the type-based theorems"
    val msg_fvs = mk_msg_etts_algorithm
      "fixed variables must not occur in the type-based theorems"
    val msg_not_risstv_subset = mk_msg_etts_algorithm
      "risstv must be a subset of the schematic type " ^
      "variables that occur in the type-based theorems"

    val _ = not (null rispec) orelse error msg_etts_context

    val t = Thm.full_prop_of thm
    val _ = t
      |> (fn t => Term.add_tfrees t [])
      |> null
      orelse error msg_ftvs 
    val _ = t
      |> (fn t => Term.add_frees t [])
      |> null
      orelse error msg_fvs 
    val stvs = t
      |> (fn t => Term.add_tvars t [])
      |> map #1
      |> distinct op=
    val risstv = map #1 rispec
    val _ = subset op= (risstv, stvs) orelse error msg_not_risstv_subset

  in () end;

in

fun etts_algorithm 
  ctxt 
  etts_output_type 
  writer
  rispec 
  sbtspec 
  sbrr_opt 
  subst_thms 
  mpespc_opt 
  attrbs 
  thm =
  let

    (*0. User input validation*)
    val _ = etts_algorithm_input rispec thm

    (*1. Initialization of the relativization context*)
    val 
      (
        ctxt,
        ctxt',
        writer,
        rispec,
        sbtspec_var_specs,
        sbtspec_const_specs,
        transfer_thms
      ) = init_rlt_ctxt ctxt etts_output_type writer rispec sbtspec

    (*2. Initialization of the relativization context*)
    val writer' = ETTS_Writer.increment_index 2 writer
    val ((thm', writer'), ctxt'') = etts_kera
      ctxt 
      ctxt' 
      etts_output_type
      writer'
      rispec 
      sbtspec_var_specs 
      sbtspec_const_specs 
      transfer_thms 
      thm

    (*3. Initialization of the relativization context*)
    val writer'' = ETTS_Writer.increment_index 2 writer'
    val ((thm'', writer'''), ctxt''') = etts_algorithm_pp
      ctxt'' etts_output_type writer'' sbrr_opt subst_thms mpespc_opt attrbs thm'

  in ((thm'', writer'''), ctxt''') end;

end;

fun etts_fact
  ctxt 
  etts_output_type 
  writer
  rispec 
  sbtspec 
  sbrr_opt 
  subst_thms 
  mpespc_opt 
  attrbs 
  thms =
  let
    fun folder thm ((thms, writer), ctxt) = 
      etts_algorithm
        ctxt
        etts_output_type
        writer
        rispec
        sbtspec 
        sbrr_opt 
        subst_thms 
        mpespc_opt 
        attrbs 
        thm
      |>> apsnd (ETTS_Writer.increment_index 1) 
      |>> apfst (curry (swap #> op::) thms)
  in fold_rev folder thms (([], writer), ctxt) end;

end;