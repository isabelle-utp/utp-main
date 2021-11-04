(* Title: ETTS/ETTS_Active.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Active area output for Types-To-Sets.

Notes:
  - The structure ETTS_Active contains elements of code from the theory
  Sketch_and_Explore in the main library of Isabelle/HOL.
*)

signature ETTS_ACTIVE =
sig
val etts_indent : int Config.T
datatype etts_thm_type = 
  tts_lemma | tts_theorem | tts_corollary | tts_proposition
val theorem_string_of_term : 
  Proof.context ->
  etts_thm_type ->
  string ->
  Token.src list ->
  string -> 
  Token.src list -> 
  term -> 
  string
end;

structure ETTS_Active : ETTS_ACTIVE =
struct




(**** Indentation ****)

val etts_indent = Attrib.setup_config_int \<^binding>\<open>tts_indent\<close> (K 2)

fun etts_indent_val ctxt = Config.get ctxt etts_indent

fun mk_etts_indent ctxt n = replicate (n*(etts_indent_val ctxt)) " " 
  |> String.concat




(**** Synonyms ****)

datatype etts_thm_type = 
  tts_lemma | tts_theorem | tts_corollary | tts_proposition;

fun string_of_etts_thm_type tts_lemma = "tts_lemma"
  | string_of_etts_thm_type tts_theorem = "tts_theorem"
  | string_of_etts_thm_type tts_corollary = "tts_corollary"
  | string_of_etts_thm_type tts_proposition = "tts_proposition";




(**** Auxiliary functions ported from Sketch_and_Explore ****)

(*ported from Sketch_and_Explore*)
fun maybe_quote ctxt =
  ATP_Util.maybe_quote (Thy_Header.get_keywords' ctxt);

(*ported from Sketch_and_Explore*)
fun print_term ctxt t = t
  |> Print_Mode.setmp [] (Syntax.unparse_term ctxt #> Pretty.string_of)
  |> Sledgehammer_Util.simplify_spaces
  |> maybe_quote ctxt;

(*ported from Sketch_and_Explore*)
fun mk_print_ctxt ctxt = fold
  (fn opt => Config.put opt false)
  [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts]
  ctxt;




(**** Further auxiliary functions ****)

(*create an assumption from a term represented by a string*)
fun mk_assumptions ctxt assmcs =
  let fun mk_eoln c = c ^ "\n"
  in 
    case assmcs of 
      [] => ""
    | assmcs => 
        mk_etts_indent ctxt 1 ^
        "assumes " ^ 
        String.concatWith ((mk_etts_indent ctxt 2) ^ "and ") (map mk_eoln assmcs)
  end;

(*unparsing attributes*)
fun mk_attr_string attrs = 
  if length attrs = 0 
  then ""
  else
    let
      val attrsc = attrs
        |> map (map Token.unparse) 
        |> map (String.concatWith " ")
        |> String.concatWith ", "
    in "[" ^ attrsc ^ "]" end

(*create a conclusion from a term represented by a string*)
fun mk_is ctxt thm_in_name attrs_in = 
  mk_etts_indent ctxt 2 ^ "is " ^ thm_in_name ^ mk_attr_string attrs_in

(*create conclusions*)
fun mk_shows ctxt thm_in_name attrs_in conclcs = case conclcs of
    [] => ""
  | conclcs => 
      mk_etts_indent ctxt 1 ^
      "shows " ^ 
      String.concatWith "\n" conclcs ^ "\n" ^
      mk_is ctxt thm_in_name attrs_in;

(*create a preamble*)
fun mk_preamble etts_thm_type thm_out_name attrs_out =
  (string_of_etts_thm_type etts_thm_type) ^ " " ^ 
  thm_out_name ^ 
  mk_attr_string attrs_out ^ ":\n"




(**** Conversion of theorems to strings for theory output ****)

fun theorem_string_of_term 
  ctxt etts_thm_type thm_out_name attrs_out thm_in_name attrs_in t =
  let
    val ctxt = mk_print_ctxt ctxt
    val t = t
      |> singleton (Syntax.uncheck_terms ctxt)
      |> Sledgehammer_Isar_Annotate.annotate_types_in_term ctxt
    val assmsc = t
      |> Logic.strip_imp_prems 
      |> map (print_term ctxt) 
      |> mk_assumptions ctxt
    val conclc = t
      |> Logic.strip_imp_concl
      |> Logic.dest_conjunctions
      |> map (print_term ctxt) 
      |> mk_shows ctxt thm_in_name attrs_in
    val preamblec = mk_preamble etts_thm_type thm_out_name attrs_out
    val done = ".\n\n"
    val thmc = String.concatWith "" [preamblec, assmsc, conclc, done]
  in thmc end;

end;