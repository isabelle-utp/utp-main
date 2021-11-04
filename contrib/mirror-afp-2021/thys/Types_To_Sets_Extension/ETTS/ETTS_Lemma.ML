(* Title: ETTS/ETTS_Lemma.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Implementation of the command tts_lemma.
*)

signature ETTS_LEMMA =
sig
val tts_lemma : Outer_Syntax.command_keyword -> string -> unit
end


structure ETTS_Lemma : ETTS_LEMMA =
struct




(**** Prerequisites ****)

open ETTS_Context;
open ETTS_Algorithm;




(**** Data for tts addendum ****)

datatype tts_addendum = tts_given | tts_is;

fun string_to_tts_addendum "given" = tts_given
  | string_to_tts_addendum "is" = tts_is
  | string_to_tts_addendum _ = error "string_to_tts_addendum: invalid input.";




(**** Tactics ****)

fun eq_thm_tac ctxt thm i = 
  let
    fun eq_thm_impl ctxt thm goal_thm =
      let
        val error_msg = "eq_thm_tac failed on " ^ (Thm.string_of_thm ctxt thm)
        val goal_prem_ct = goal_thm
          |> Thm.cprems_of 
          |> the_single
        val thm_ct = Thm.cprop_of thm
        val thm = thm
          |> Drule.instantiate_normalize (Thm.match (thm_ct, goal_prem_ct)) 
          |> Drule.eta_contraction_rule
          handle Pattern.MATCH => error error_msg
        val _ = ((Thm.full_prop_of thm) aconv (Thm.term_of goal_prem_ct))
          orelse error error_msg
      in Thm.implies_elim goal_thm thm end
  in SELECT_GOAL (PRIMITIVE (eq_thm_impl ctxt thm)) i end;

fun tts_lemma_tac ctxt (tts_given, thm) = Method.insert_tac ctxt (single thm)
  | tts_lemma_tac ctxt (tts_is, thm) = eq_thm_tac ctxt thm;

fun tts_lemma_map_tac ctxt tts_thm_spec = 
  let
    val tts_addendum_map = 
      AList.lookup op= (1 upto (length tts_thm_spec) ~~ tts_thm_spec) #> the                                  
    fun tac_map n = tts_lemma_tac ctxt (tts_addendum_map n) n
  in ALLGOALS tac_map end;

fun tts_lemma_map_method tts_thm_spec =
  let
    val method = CONTEXT_METHOD 
      (
        fn _ => fn (ctxt, st) => st 
          |> tts_lemma_map_tac ctxt tts_thm_spec 
          |> Context_Tactic.TACTIC_CONTEXT ctxt
      )
  in method end;

fun refine_tts_lemma_map thmss =
  Proof.refine_singleton (Method.Basic (K (tts_lemma_map_method thmss)));




(**** TTS algorithm interface ****)

fun relativization ctxt thms =
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
    val ((thms, _), _) = ETTS_Algorithm.etts_fact
      ctxt 
      default 
      writer
      rispec 
      sbtspec 
      sbrr_opt 
      subst_thms 
      mpespc_opt 
      attrbs 
      thms
  in thms end;

fun insert_rotate j thms =
  CONTEXT_METHOD 
    (
      fn _ => fn (ctxt, st) => st 
      |> ALLGOALS (fn i => Method.insert_tac ctxt thms i THEN rotate_tac j i) 
      |> Context_Tactic.TACTIC_CONTEXT ctxt
    );

fun refine_insert_rotate j ths =
  Proof.refine_singleton (Method.Basic (K (insert_rotate j ths)));

fun mk_tts_goal tts_thms_specs outer_ctxt st = 
  let

    (*pre-processing*)
    val tts_thms_specs = tts_thms_specs
      |> map
        (
          relativization outer_ctxt 
          |> apsnd 
          #> 
            (
              fn (tts_addendum, thms) => 
                (replicate (length thms) tts_addendum, thms)
            )
          #> op~~
        )
      |> flat
      |> map (apfst string_to_tts_addendum)
      
    (*create assumptions*)
    val ctxt = Proof.context_of st
    val assms = Assumption.local_prems_of ctxt outer_ctxt
    val all_ftv_permutes = assms
      |> map 
        (
          Thm.hyps_of 
          #> the_single 
          #> Logic.get_forall_ftv_permute 
          #> #2
          #> #2
        ) 
    val assms = map2 (Thm.forall_intr_var_order ctxt) all_ftv_permutes assms

    val st = refine_insert_rotate (~(length assms)) assms st

  in refine_tts_lemma_map tts_thms_specs st end;




(**** Parser ****)

(* 
The content of this section was adopted (with amendments) from the
theory Pure.thy.
*)
local

val long_keyword =
   Parse_Spec.includes >> K "" || Parse_Spec.long_statement_keyword;

val parse_tts_addendum = 
  \<^keyword>\<open>given\<close> -- Parse.thm || \<^keyword>\<open>is\<close> -- Parse.thm;

val parse_obtains = 
  Parse.$$$ "obtains" |-- Parse.!!! (Parse_Spec.obtains -- parse_tts_addendum);

fun process_obtains args = 
  (args |> #1 |> Element.Obtains, args |> #2 |> single);

val parse_shows = 
  let
    val statement = Parse.and_list1 
      (
        Parse_Spec.opt_thm_name ":" -- 
        Scan.repeat1 Parse.propp -- 
        parse_tts_addendum
      );
  in Parse.$$$ "shows" |-- Parse.!!! statement end;

fun process_shows args = (args |> map #1 |> Element.Shows, map #2 args);

val parse_long_statement = 
  Scan.optional 
    (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword) 
    Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- 
    (
      Scan.repeat Parse_Spec.context_element -- 
      (parse_obtains >> process_obtains || parse_shows >> process_shows)
    );

fun process_long_statement 
  (((binding, includes), (elems, (concl, tts_thms_specs)))) = 
  (true, binding, includes, elems, concl, tts_thms_specs);

val long_statement = parse_long_statement >> process_long_statement;

val parse_short_statement = 
  Parse_Spec.statement -- 
  Parse_Spec.if_statement -- 
  Parse.for_fixes --
  parse_tts_addendum;

fun process_short_statement (((shows, assumes), fixes), tts_thms_specs) =
  (
    false, 
    Binding.empty_atts, 
    [], 
    [Element.Fixes fixes, Element.Assumes assumes],
    Element.Shows shows,
    single tts_thms_specs
  );

val short_statement = parse_short_statement >> process_short_statement;

in

val parse_tts_lemma = long_statement || short_statement;

end;




(**** Evaluation ****)

fun process_tts_lemma
  (long, binding, includes, elems, concl, tts_thms_specs) b lthy = 
  let
    val tts_thms_specs = 
      map (single #> Attrib.eval_thms lthy |> apsnd) tts_thms_specs
  in
    lthy
    |> Specification.theorem_cmd
      long Thm.theoremK NONE (K I) binding includes elems concl b
    |> mk_tts_goal tts_thms_specs lthy
  end;




(**** Interface ****)

fun tts_lemma spec descr = Outer_Syntax.local_theory_to_proof' 
  spec ("state " ^ descr) (parse_tts_lemma >> process_tts_lemma);

end;