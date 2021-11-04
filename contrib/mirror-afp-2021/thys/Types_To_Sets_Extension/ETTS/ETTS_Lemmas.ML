(* Title: ETTS/ETTS_Lemmas.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Implementation of the command tts_lemmas.
*)

signature TTS_LEMMAS =
sig
val tts_lemmas : 
  Proof.context ->
  ETTS_Algorithm.etts_output_type ->
  ((binding * Token.src list) * (thm list * (string * Token.src list))) list ->
  Proof.context * int list
end;


structure TTS_Lemmas : TTS_LEMMAS =
struct




(**** Prerequisites ****)

open ETTS_Algorithm;
open ETTS_Context;
open ETTS_Active;




(**** Implicit statement of theorems ****)

fun register_output ctxt ab out_thms = 
  let

    val ((thmc, out_thms), lthy) = 
      let 
        val facts' = (ab ||> map (Attrib.check_src ctxt), single (out_thms, []))
          |> single
          |> Attrib.partial_evaluation ctxt
      in ctxt |> Local_Theory.notes facts' |>> the_single end

    val _ = CTR_Utilities.thm_printer lthy true thmc out_thms

  in (lthy, "") end




(**** Output to an active area ****)

local

(*number of repeated premises*)
fun num_rep_prem eq ts = 
  let
    val premss = map Logic.strip_imp_prems ts    
    val min_length = min_list (map length premss)
    val premss = map (take min_length) premss
    val template_prems = hd premss
    val num_eq_prems = premss
      |> tl
      |> 
        map 
          (
            compare_each eq template_prems
            #> take_prefix (curry op= true)
            #> length
          )
    
    val num_rep_prems = 
      if length premss = 1 
      then length template_prems
      else min_list num_eq_prems
  in (num_rep_prems, premss) end;

(*elimination of premises*)
fun elim_assms assm_thms thm = fold (flip Thm.implies_elim) assm_thms thm;

(*create a single theorem from a fact via Pure conjunction*)
fun thm_of_fact ctxt thms =
  let
    
    val ts = map Thm.full_prop_of thms    

    val (num_rep_prems, _) = num_rep_prem (op aconv) ts

    val rep_prems = thms 
      |> hd 
      |> Thm.full_prop_of 
      |> Logic.strip_imp_prems 
      |> take num_rep_prems
      |> map (Thm.cterm_of ctxt);

    val all_ftv_rels = 
      let val subtract = swap #> uncurry (subtract op=)
      in 
        rep_prems
        |> map 
          (
            Thm.term_of 
            #> Logic.forall_elim_all 
            #> apfst (fn t => Term.add_frees t [])
            #> apsnd dup
            #> reroute_sp_ps  
            #> apfst (apfst dup)
            #> apfst reroute_ps_sp  
            #> apfst (apsnd subtract)
            #> apfst subtract
          )
        end

    val index_of_ftvs = all_ftv_rels 
      |> map 
        (
          #1
          #> map_index I
          #> map swap
          #> AList.lookup op=
          #> curry (swap #> op#>) the
        )

    val all_indicess = (map #2 all_ftv_rels) ~~ index_of_ftvs
      |> map (fn (x, f) => map f x)
    
    val (assms, ctxt') = Assumption.add_assumes rep_prems ctxt

    val stvss = 
      map 
        (
          Thm.full_prop_of 
          #> (fn t => Term.add_vars t [])
          #> map Var
          #> map (Thm.cterm_of ctxt)
        )
        assms
    
    val stvss = stvss ~~ all_indicess
      |> map (fn (stvs, indices) => map (nth stvs) indices)

    val assms = map2 forall_intr_list stvss assms
    
    val thm = thms 
      |> map (elim_assms assms)
      |> Conjunction.intr_balanced
      |> singleton (Proof_Context.goal_export ctxt' ctxt)

  in thm end;

in

(*output to an active area*)
fun active_output ctxt thm_out_name attrs_out thm_in_name attrs_in thms = 
  let
    val (thms, ctxt') = Thm.unvarify_local_fact ctxt thms
    val thmc = thms
      |> thm_of_fact ctxt' 
      |> Thm.full_prop_of
      |> theorem_string_of_term 
        ctxt tts_lemma thm_out_name attrs_out thm_in_name attrs_in
  in (ctxt, thmc) end;

end;




(**** Implementation ****)

fun tts_lemmas ctxt tts_output_type thm_specs =
  let

    val 
      {
        mpespc_opt = mpespc_opt, 
        rispec = rispec, 
        sbtspec = sbtspec, 
        sbrr_opt = sbrr_opt,
        subst_thms = subst_thms, 
        attrbs = attrbs
      } = get_tts_ctxt_data ctxt

    val writer = ETTS_Writer.initialize 4

    fun folder
      ((b, attrs_out), (thms, (thm_in_name, attrs_in))) (ctxt, thmcs, writer) =
      let
      
        val ((out_thms, writer), ctxt) = 
          ETTS_Algorithm.etts_fact 
            ctxt 
            tts_output_type 
            writer
            rispec 
            sbtspec 
            sbrr_opt 
            subst_thms 
            mpespc_opt 
            attrbs 
            thms
        
        val writer = ETTS_Writer.increment_index 0 writer
  
        val (lthy, thmc) = 
          if is_default tts_output_type orelse is_verbose tts_output_type
          then register_output ctxt (b, attrs_out) out_thms
          else 
            active_output 
              ctxt 
              (Name_Space.base_name b) 
              attrs_out 
              thm_in_name 
              attrs_in 
              out_thms

        val thmcs = thmcs ^ thmc
        
      in (lthy, thmcs, writer) end

    val (ctxt'', thmcs, writer) = fold folder thm_specs (ctxt, "", writer)

    val _ = 
      if is_active tts_output_type 
      then thmcs |> Active.sendback_markup_command |> writeln
      else () 

  in (ctxt'', writer) end;




(**** Parser ****)

local

val parse_output_mode = Scan.optional (\<^keyword>\<open>!\<close> || \<^keyword>\<open>?\<close>) "";
val parse_facts = \<^keyword>\<open>in\<close> |-- Parse_Spec.name_facts;

in

val parse_tts_lemmas = parse_output_mode -- parse_facts;

end;




(**** User input analysis ****)

fun mk_msg_tts_lemmas msg = "tts_lemmas: " ^ msg;

fun thm_specs_raw_input thm_specs_raw = 
  let
    val msg_multiple_facts = 
      mk_msg_tts_lemmas "only one fact per entry is allowed" 
    val _ = thm_specs_raw |> map (#2 #> length) |> List.all (fn n => n = 1)
      orelse error msg_multiple_facts
  in () end;




(**** Evaluation ****)

local

fun mk_thm_specs ctxt thm_specs_raw =
  let

    (*auxiliary functions*)

    fun binding_last c =
      let val binding_last_h = Long_Name.base_name #> Binding.qualified_name
      in if size c = 0 then Binding.empty else binding_last_h c end

    fun binding_of_binding_spec (b, (factb, thmbs)) =
      if Binding.is_empty b 
      then
        if length thmbs = 1 
        then
          if Binding.is_empty (the_single thmbs) 
          then factb
          else the_single thmbs
        else factb 
      else b

    (*main*)

    val thm_specs = thm_specs_raw
      |> map (apsnd the_single)
      |> 
        (
          Facts.ref_name 
          #> binding_last 
          |> apdupl 
          |> apfst
          #> reroute_ps_sp
          |> apsnd 
          |> map
        )
      |> map reroute_sp_ps
      |> map (reroute_ps_sp #> (swap |> apsnd) #> reroute_sp_ps |> apfst)  
      |> map (apsnd dup)
      |> 
        (
          single 
          #> (ctxt |> Attrib.eval_thms)
          #> (Thm.derivation_name #> binding_last |> map |> apdupl) 
          |> apfst
          |> apsnd 
          |> map
        )
      |> map (reroute_sp_ps #> apfst reroute_sp_ps #> reroute_ps_sp)
      |> 
        (
          reroute_ps_sp 
          #> (swap |> apsnd) 
          #> reroute_sp_ps 
          #> (reroute_ps_sp #> binding_of_binding_spec |> apfst) 
          |> apfst
          |> map
        )
      |> map (Facts.ref_name |> apfst |> apsnd |> apsnd)

  in thm_specs end;

in

fun process_tts_lemmas args ctxt =
  let
    (*unpacking*)
    val tts_output_type = args |> #1 |> etts_output_type_of_string
    val thm_specs_raw = #2 args 
    (*user input analysis*)
    val _ = thm_specs_raw_input thm_specs_raw
    (*pre-processing*)
    val thm_specs = mk_thm_specs ctxt thm_specs_raw
  in thm_specs |> tts_lemmas ctxt tts_output_type |> #1 end;

end;




(**** Interface ****)

val _ = Outer_Syntax.local_theory
  \<^command_keyword>\<open>tts_lemmas\<close> 
  "automated relativization of facts"
  (parse_tts_lemmas >> process_tts_lemmas);

end;