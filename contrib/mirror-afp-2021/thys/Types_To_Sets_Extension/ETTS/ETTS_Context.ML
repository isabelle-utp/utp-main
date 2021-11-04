(* Title: ETTS/ETTS_Context.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Implementation of the command tts_context.
*)

signature ETTS_CONTEXT =
sig
type ctxt_def_type
type amend_ctxt_data_input_type
val rule_attrb : string list
val update_tts_ctxt_data : ctxt_def_type -> Proof.context -> Proof.context
val get_tts_ctxt_data : Proof.context -> ctxt_def_type
val string_of_sbrr_opt : (Facts.ref * Token.src list) option -> string
val string_of_subst_thms : (Facts.ref * Token.src list) list -> string
val string_of_mpespc_opt : 
  Proof.context -> 
  (term list * (Proof.context -> tactic)) option -> 
  string
val string_of_amend_context_data_args : 
  Proof.context -> amend_ctxt_data_input_type -> string
val string_of_tts_ctxt_data : Proof.context -> ctxt_def_type -> string
val amend_context_data : 
  amend_ctxt_data_input_type -> Proof.context -> ctxt_def_type * Proof.context
val process_tts_context : 
  amend_ctxt_data_input_type -> Toplevel.transition -> Toplevel.transition
end;


structure ETTS_Context : ETTS_CONTEXT =
struct




(**** Data ****)


(*names of selected rule attributes suitable for tts_context*)
val rule_attrb =
  ["OF", "of", "THEN", "where", "simplified", "folded", "unfolded"];

val is_rule_attrb = member op= rule_attrb;

(*
Conventions
 - risstv: type variable associated with an RI specification element
 - risset: set associated with an RI specification element
 - rispec: RI specification
 - tbt: tbterm associated with the sbterm specification element
 - sbt: sbterm associated with the sbterm specification element
 - sbtspec: sbterm specification
 - sbrr_opt: rewrite rules for the set-based theorem
 - subst_thms: known premises for the set-based theorem 
 - mpespc_opt: specification of the elimination of premises in 
    the set-based theorem
 - attrbs: attributes for the set-based theorem
*)
type ctxt_def_type = 
  {
    rispec : (indexname * term) list,
    sbtspec : (term * term) list,
    sbrr_opt : (Facts.ref * Token.src list) option,
    subst_thms : (Facts.ref * Token.src list) list,
    mpespc_opt : (term list * (Proof.context -> tactic)) option,
    attrbs : Token.src list
  };
type amend_ctxt_data_input_type = 
  (
    (
      (
        ((string * string) list * (string * string) list) * 
        (Facts.ref * Token.src list) option
      ) * (Facts.ref * Token.src list) list
    ) * (string list * (Method.text * (Position.T * Position.T))) option
  ) * Token.src list;

(*default values for the data associated with a tts_context*)
val init_ctxt_def_type = 
  {
    rispec = [], 
    sbtspec = [], 
    sbrr_opt = NONE,
    subst_thms = [],
    mpespc_opt = NONE,
    attrbs = []
  };

(*data for tts_context*)
structure TTSContextData = Proof_Data
  (
    type T = ctxt_def_type; 
    fun init _ = init_ctxt_def_type;
  );

fun update_tts_ctxt_data value = TTSContextData.map (K value);
fun get_tts_ctxt_data ctxt = TTSContextData.get ctxt;

fun is_empty_tts_ctxt_data (ctxt_data : ctxt_def_type) = 
  ctxt_data |> #attrbs |> null 
  andalso ctxt_data |> #mpespc_opt |> is_none
  andalso ctxt_data |> #rispec |> null
  andalso ctxt_data |> #sbrr_opt |> is_none
  andalso ctxt_data |> #subst_thms |> null
  andalso ctxt_data |> #sbtspec |> null;




(**** Input processing ****)

fun mk_mpespc_opt ctxt mpespc_opt_raw = 
  let
    fun mk_mpespc_opt_impl ctxt mpespc_raw = 
      let
        fun prem_red_tac ctxt = 
          (Method.evaluate ((#2 #> #1) mpespc_raw) ctxt) []
          |> Context_Tactic.NO_CONTEXT_TACTIC ctxt
        val prems = mpespc_raw 
          |> #1 
          |> map (Proof_Context.read_term_pattern ctxt)
      in (prems, prem_red_tac) end;
  in Option.map (mk_mpespc_opt_impl ctxt) mpespc_opt_raw end;

fun unpack_amend_context_data_args args = 
  let
    val rispec_raw = args |> #1 |> #1 |> #1 |> #1 |> #1
    val sbtspec_raw = args |> #1 |> #1 |> #1 |> #1 |> #2
    val sbrr_opt_raw = args |> #1 |> #1 |> #1 |> #2
    val subst_thms_raw = args |> #1 |> #1 |> #2
    val mpespc_opt_raw = args |> #1 |> #2
    val attrbs_raw = args |> #2
  in 
    (
      rispec_raw, 
      sbtspec_raw, 
      sbrr_opt_raw, 
      subst_thms_raw, 
      mpespc_opt_raw,
      attrbs_raw
    ) 
  end;




(**** String I/O ****)

fun string_of_rispec ctxt = ML_Syntax.print_pair 
  Term.string_of_vname (Syntax.string_of_term ctxt);

fun string_of_term_pair ctxt =
  let val string_of_term = Syntax.string_of_term ctxt
  in ML_Syntax.print_pair string_of_term string_of_term end;

val string_of_sbrr_opt =
  (ML_Syntax.print_pair Facts.string_of_ref string_of_token_src_list)
  |> ML_Syntax.print_option;

val string_of_subst_thms = 
  ML_Syntax.print_pair Facts.string_of_ref string_of_token_src_list
  |> ML_Syntax.print_list;

fun string_of_mpespc_opt ctxt =
  let 
    val tac_c = K "unknown tactic"
    val term_cs = (ML_Syntax.print_list (Syntax.string_of_term ctxt))
  in ML_Syntax.print_pair term_cs tac_c |> ML_Syntax.print_option end;

fun string_of_amend_context_data_args ctxt args =
  let
    val 
      (
        rispec_raw, 
        sbtspec_raw, 
        sbrr_opt_raw, 
        subst_thms_raw, 
        mpespc_opt_raw,
        attrbs_raw
      ) = unpack_amend_context_data_args args
    val rispec_c = rispec_raw
      |> map (ML_Syntax.print_pair I I)
      |> String.concatWith ", "
      |> curry op^ "rispec: "
    val sbtspec_c = sbtspec_raw
      |> map (ML_Syntax.print_pair I I)
      |> String.concatWith ", "
      |> curry op^ "sbtspec: "
    val sbrr_opt_c = sbrr_opt_raw
      |> string_of_sbrr_opt
      |> curry op^ "sbrr_opt: "
    val subst_thms_c = subst_thms_raw
      |> string_of_subst_thms
      |> curry op^ "subst_thms: "
    val mpespc_opt_c = mpespc_opt_raw
      |> mk_mpespc_opt ctxt
      |> string_of_mpespc_opt ctxt
      |> curry op^ "mpespc_opt: "
    val attrbs_c = attrbs_raw
      |> string_of_token_src_list
      |> curry op^ "attrbs: "
    val out_c =
      [
        rispec_c,
        sbtspec_c,
        sbrr_opt_c,
        subst_thms_c,
        mpespc_opt_c,
        attrbs_c
      ]
      |> String.concatWith "\n"
  in out_c end;

fun string_of_tts_ctxt_data ctxt ctxt_data =
  let
    val rispec_c = ctxt_data
      |> #rispec
      |> map (string_of_rispec ctxt)
      |> String.concatWith ", "
      |> curry op^ "rispec: "
    val sbtspec_c = ctxt_data
      |> #sbtspec
      |> map (string_of_term_pair ctxt)
      |> String.concatWith ", "
      |> curry op^ "sbtspec: "
    val sbrr_opt_c = ctxt_data
      |> #sbrr_opt
      |> string_of_sbrr_opt
      |> curry op^ "sbrr_opt: "
    val subst_thms_c = ctxt_data
      |> #subst_thms
      |> string_of_subst_thms
      |> curry op^ "subst_thms: "
    val mpespc_opt_c = ctxt_data
      |> #mpespc_opt
      |> string_of_mpespc_opt ctxt
      |> curry op^ "mpespc_opt: "
    val attrbs_c = ctxt_data
      |> #attrbs
      |> string_of_token_src_list
      |> curry op^ "attrbs: " 
    val out_c =
      [
        rispec_c,
        sbtspec_c,
        sbrr_opt_c,
        subst_thms_c,
        mpespc_opt_c,
        attrbs_c
      ]
      |> String.concatWith "\n"
  in out_c end;




(**** User input analysis ****)

fun mk_msg_tts_ctxt_error msg = "tts_context: " ^ msg;

fun rispec_input ctxt rispec = 
  let

    val msg_rispec_empty = 
      mk_msg_tts_ctxt_error "rispec must not be empty"
    val msg_risstv_not_distinct = 
      mk_msg_tts_ctxt_error "risstvs must be distinct"

    val risstv = map #1 rispec
    val risset = map #2 rispec

    val _ = rispec |> List.null |> not 
      orelse error msg_rispec_empty
    val _ = risstv |> has_duplicates op= |> not 
      orelse error msg_risstv_not_distinct
    
    val _ = ETTS_RI.risset_input ctxt "tts_context" risset

  in () end;

local

fun tv_of_ix (T, U) = 
  let
    fun tv_of_ix ((TVar v), (TFree x)) = [(v, x)]
      | tv_of_ix ((Type (c, Ts)), (Type (d, Us))) = 
          if length Ts = length Us andalso c = d 
          then (Ts ~~ Us) |> map tv_of_ix |> flat
          else raise TYPE ("tv_of_ix", [Type (c, Ts), Type (d, Us)], [])
      | tv_of_ix (T, U) = raise TYPE ("tv_of_ix", [T, U], [])
  in tv_of_ix (T, U) |> distinct op= end

fun is_fun xs = xs |> map fst |> has_duplicates op= |> not
fun is_bij xs = is_fun xs andalso xs |> map snd |> has_duplicates op= |> not

in

fun sbtspec_input ctxt rispec sbtspec =
  let

    val msg_tbts_not_stvs = mk_msg_tts_ctxt_error 
      "the type variables that occur in the tbts must be schematic"
    val msg_tbts_distinct_sorts = mk_msg_tts_ctxt_error 
      "tbts: a single stv should not have two distinct sorts associated with it"
    val msg_not_type_instance = mk_msg_tts_ctxt_error 
      "\n\t-the types of the sbts must be equivalent " ^ 
      "to the types of the tbts up to renaming of the type variables\n" ^
      "\t-to each type variable that occurs among the tbts must correspond " ^ 
      "exactly one type variable among all type " ^
      "variables that occur among all of the sbts"
    val msg_tbts_not_cv = mk_msg_tts_ctxt_error 
      "tbts must consist of constants and schematic variables"
    val msg_tbts_not_distinct = mk_msg_tts_ctxt_error "tbts must be distinct"
    val msg_tbts_not_sbt_data_key = mk_msg_tts_ctxt_error
      "sbts must be registered using the command tts_register_sbts"
    val msg_sbterms_subset_rispec = mk_msg_tts_ctxt_error
      "the collection of the (stv, ftv) pairs associated with the sbterms " ^
      "must form a subset of the collection of the (stv, ftv) pairs " ^
      "associated with the RI specification, provided that only the pairs " ^
      "(stv, ftv) associated with the sbterms such that ftv occurs in a " ^
      "premise of a theorem associated with an sbterm are taken into account"

    val tbts = map #1 sbtspec
    val sbts = map #2 sbtspec

    val _ = (tbts |> map (fn t => Term.add_tfrees t []) |> flat |> null)
      orelse error msg_tbts_not_stvs

    val _ = tbts
      |> map (fn t => Term.add_tvars t []) 
      |> flat
      |> distinct op=
      |> is_fun
      orelse error msg_tbts_distinct_sorts

    val tbts_sbts_Ts = map type_of tbts ~~ map type_of sbts
      |> map tv_of_ix
      |> flat
      |> distinct op=

    val _ = tbts_sbts_Ts
      |> is_bij
      orelse error msg_not_type_instance
      handle TYPE ("tv_of_ix", _, _) => error msg_not_type_instance

    val _ = tbts |> map Term.is_cv |> List.all I 
      orelse error msg_tbts_not_cv
    val _ = tbts |> has_duplicates (op aconv) |> not
      orelse error msg_tbts_not_distinct

    val _ = sbts
      |> map (Thm.cterm_of ctxt #> apdupl (K ctxt)) 
      |> map (uncurry ETTS_Substitution.is_sbt_data_key)
      |> List.all I 
      orelse error msg_tbts_not_sbt_data_key

    val sbt_ftvs = sbts
      |> map (Thm.cterm_of ctxt)
      |> map (ETTS_Substitution.sbt_data_of ctxt)
      |> filter is_some
      |> map the
      |> map Thm.prems_of
      |> flat
      |> map (fn t => Term.add_tfrees t [])
      |> flat

    val tbts_sbts_Ts' = tbts_sbts_Ts
      |> filter (fn (_, ftv) => ftv |> member op= sbt_ftvs)
      |> map (apfst fst)

    val rispec_ftvs_Ts = 
      map (apsnd (fn t => t |> type_of |> HOLogic.dest_SetTFree)) rispec

    val _ = subset op= (tbts_sbts_Ts', rispec_ftvs_Ts)
      orelse error msg_sbterms_subset_rispec

  in () end;

end;

fun sbrr_opt_raw_input ctxt (SOME sbrr_raw) = 
    let val _ = Attrib.eval_thms ctxt (single sbrr_raw) in () end
  | sbrr_opt_raw_input _ NONE = ();

fun subst_thms_input ctxt subst_thms_raw =
  let val _ = Attrib.eval_thms ctxt subst_thms_raw
  in () end;

fun attrbs_input attrbs = 
  let
    val msg_rule_attrbs = mk_msg_tts_ctxt_error
      "attrbs: only " ^ String.concatWith ", " rule_attrb ^ " are allowed"
    val _ = attrbs 
      |> map (map Token.unparse #> hd) 
      |> map is_rule_attrb 
      |> List.all I
      orelse error msg_rule_attrbs
  in () end;

fun tts_context_input (ctxt_data : ctxt_def_type) =
  let val msg_nested_tts_context = mk_msg_tts_ctxt_error "nested tts contexts"
  in is_empty_tts_ctxt_data ctxt_data orelse error msg_nested_tts_context end;




(**** Parser ****)

local

(*Parser for the field 'tts'*)
val parse_tts = 
  let
    val parse_tts_title = (\<^keyword>\<open>tts\<close> -- kw_col); 
    val parse_tts_entry = 
      (kw_bo |-- Parse.type_var -- (\<^keyword>\<open>to\<close> |-- Parse.term --| kw_bc));
  in parse_tts_title |-- Parse.and_list parse_tts_entry end;

(*Parser for the field 'sbterms'*)
val parse_sbterms = 
  let
    val parse_sbterms_title = (\<^keyword>\<open>sbterms\<close> -- kw_col);
    val parse_sbterms_entry = 
      (kw_bo |-- Parse.term -- (\<^keyword>\<open>to\<close> |-- Parse.term --| kw_bc));
  in parse_sbterms_title |-- Parse.and_list parse_sbterms_entry end;

(*Parser for the field 'rewriting'*)
val parse_rewriting = (\<^keyword>\<open>rewriting\<close> |-- Parse.thm);

(*Parser for the field 'substituting'*)
val parse_substituting = (\<^keyword>\<open>substituting\<close> |-- Parse.and_list Parse.thm);

(*Parser for the field 'eliminating'*)
val parse_eliminating = 
  let
    val parse_eliminating_pattern = Parse.and_list Parse.term; 
    val parse_eliminating_method = (\<^keyword>\<open>through\<close> |-- Method.parse);
  in
    (
      \<^keyword>\<open>eliminating\<close> |--  
      (
        Scan.optional (parse_eliminating_pattern) [] --
        parse_eliminating_method
      )
    ) 
  end;

(*Parser for the field 'applying'*)
val parse_applying = (\<^keyword>\<open>applying\<close> |-- Parse.attribs);

in

(*Parser for the entire command*)
val parse_tts_context = 
  parse_tts -- 
  Scan.optional parse_sbterms [] --
  Scan.option parse_rewriting --
  Scan.optional parse_substituting [] --
  Scan.option parse_eliminating --
  Scan.optional parse_applying [];

end;




(**** Evaluation ****)

local

fun mk_rispec ctxt rispec_raw = 
  let val ctxt' = Proof_Context.init_global (Proof_Context.theory_of ctxt)
  in 
    rispec_raw
    |> map (ctxt' |> Syntax.parse_typ #> dest_TVar #> #1 |> apfst)
    |> map (ctxt |> Syntax.read_term |> apsnd) 
  end;

fun mk_sbtspec ctxt sbtspec_raw = 
  let val ctxt' = Proof_Context.init_global (Proof_Context.theory_of ctxt)
  in 
    sbtspec_raw
    |> map (ctxt' |> Proof_Context.read_term_pattern |> apfst)
    |> map (ctxt |> Syntax.read_term |> apsnd)
  end;

in 

fun amend_context_data args ctxt =
  let

    (*tts contexts should not be nested*)
    val _ = ctxt |> get_tts_ctxt_data |> tts_context_input

    (*unpacking*)
    val
      (
        rispec_raw,
        sbtspec_raw,
        sbrr_opt_raw,
        subst_thms_raw,
        mpespc_opt_raw,
        attrbs_raw
      ) = unpack_amend_context_data_args args

    (*pre-processing*)
    val rispec = mk_rispec ctxt rispec_raw
    val sbtspec = mk_sbtspec ctxt sbtspec_raw    
    val mpespc_opt = mk_mpespc_opt ctxt mpespc_opt_raw

    (*user input analysis*)
    val _ = rispec_input ctxt rispec
    val _ = sbtspec_input ctxt rispec sbtspec
    val _ = sbrr_opt_raw_input ctxt sbrr_opt_raw
    val _ = subst_thms_input ctxt subst_thms_raw
    val _ = attrbs_input attrbs_raw
   
    (*structure*)
    val ctxt_def : ctxt_def_type = 
      {
        rispec = rispec, 
        sbtspec = sbtspec, 
        subst_thms = subst_thms_raw, 
        sbrr_opt = sbrr_opt_raw,
        mpespc_opt = mpespc_opt,
        attrbs = attrbs_raw
      }

  in (ctxt_def, update_tts_ctxt_data ctxt_def ctxt) end;

end;

(*generate a new context for tts_context*)
(*ported with amendments from target_context.ML*)
fun tts_gen_context args gthy = gthy
  |> Context.cases Named_Target.theory_init Local_Theory.assert
  |> amend_context_data args
  |> snd
  |> Local_Theory.begin_nested
  |> snd;

fun process_tts_context (args: amend_ctxt_data_input_type) =
  Toplevel.begin_nested_target (tts_gen_context args);




(**** Interface ****)

val _ = Outer_Syntax.command 
  \<^command_keyword>\<open>tts_context\<close> 
  "context for the relativization of facts"
  ((parse_tts_context >> process_tts_context) --| Parse.begin);

end;