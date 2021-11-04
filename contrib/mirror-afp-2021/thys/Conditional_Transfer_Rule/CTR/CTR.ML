(* Title: CTR/CTR.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

The implementation of the command ctr.
*)

signature CTR =
sig

datatype alg_input = 
    ALG_PP of ((binding option * (Facts.ref * Token.src list)) * mixfix) list 
  | ALG_RP of
     (
       (
         (
           (string * (Facts.ref * Token.src list) option) option *
           (string, string, Facts.ref) Element.ctxt list
         ) *
         (string * string) list
       ) * ((binding option * (Facts.ref * Token.src list)) * mixfix) list
     )
val ctr_parser : alg_input parser
val process_parametricity :
  (binding option * thm) * mixfix ->
  Proof.context -> 
  ctr_pp_out
val process_relativization : 
  (string * thm list option) option ->
  Element.context list ->
  (string * string) list ->
  (binding option * thm) * mixfix ->
  Proof.context -> 
  ctr_pp_out
val process_ctrs : alg_input -> Proof.context -> Proof.context

end;


structure CTR : CTR =
struct



(**** Data ****)

datatype alg_input = 
    ALG_PP of ((binding option * (Facts.ref * Token.src list)) * mixfix) list 
  | ALG_RP of
     (
       (
         (
           (string * (Facts.ref * Token.src list) option) option *
           (string, string, Facts.ref) Element.ctxt list
         ) * (string * string) list
       ) * ((binding option * (Facts.ref * Token.src list)) * mixfix) list
     );



(**** Parser ****)

local

val algorithm_parser = \<^keyword>\<open>relativization\<close> || \<^keyword>\<open>parametricity\<close>;

val synthesis_parser = 
  Scan.option (\<^keyword>\<open>synthesis\<close> -- Scan.option Parse.thm);

val type_specs_parser = 
  Scan.optional
    (
      \<^keyword>\<open>trp\<close> |-- 
      Parse.and_list (kw_bo |-- Parse.type_var -- Parse.term --| kw_bc)
    ) 
    [];

val thm_specs_parser =
  \<^keyword>\<open>in\<close> |-- 
  Parse.and_list 
    (
      (Scan.option (Parse.binding --| \<^keyword>\<open>:\<close>)) -- 
      Parse.thm -- 
      Parse.opt_mixfix'
    );

fun rel_opt_thm_name s =
  Scan.optional
    (
      (
        Parse.binding -- Parse.opt_attribs || Parse.attribs >> 
          pair Binding.empty
      ) --| Parse.$$$ s
    )
    Binding.empty_atts;

(* 
The function was ported with amendments from the file Parse_Spec.ML in the main 
distribution of Isabelle 2021.
*)
val rel_loc_element =
  \<^keyword>\<open>fixes\<close> |-- Parse.!!! Parse_Spec.locale_fixes >> Element.Fixes ||
  \<^keyword>\<open>assumes\<close> |-- 
    Parse.!!! (Parse.and_list1 (rel_opt_thm_name ":" -- Scan.repeat1 Parse.propp))
    >> Element.Assumes;

(* 
The function was ported with amendments from the file Parse_Spec.ML in the main 
distribution of Isabelle 2021.
*)
val rel_context_element = 
  Parse.group (fn () => "context element") rel_loc_element;

fun parametricity_parser tokens = thm_specs_parser tokens |>> ALG_PP;

fun relativization_parser tokens = tokens
  |> 
    (
      synthesis_parser -- 
      Scan.repeat rel_context_element -- 
      type_specs_parser --
      thm_specs_parser
    ) 
  |>> ALG_RP;

in

val ctr_parser = 
  algorithm_parser :|-- 
  (           
    fn c => case c of
        "relativization" => relativization_parser
      | "parametricity" => parametricity_parser
      | _ => error "relativization or parametricity expected"
  );

end;




(**** User input analysis ****)

fun mk_msg_ctr msg = "ctr: " ^ msg;
fun mk_msg_binrel c = c ^ ": trp must consist of (stv, binary relation) pairs" ;
fun mk_msg_binrel_ftv c = c ^ 
  ": the user-specified binary relations must be defined over type variables";
fun mk_msg_no_dup_stvs c = c ^ ": duplicate stvs";
fun mk_msg_no_dup_binrel_ftvs c = c ^ 
  ": duplicate ftvs in the specification of the binary relations";
fun mk_msg_def ctxt t = Syntax.string_of_term ctxt t ^ " is not a definition";

fun check_def ctxt thm = 
  let
    val t = Thm.full_prop_of thm
    val _ = (ctxt, t) |> #2 |> Logic.is_equals
      orelse error (mk_msg_def ctxt t |> mk_msg_ctr)
  in () end;

fun mk_msg_no_relator c = "no relator found for the type constructor " ^ c
fun mk_msg_invalid_relator c = 
  "the relator found for the type constructor " ^ c ^
  " is not suitable (is there is a mismatch of type variables?)"



(**** Preprocessing ****)



(*** Preprocessing of the type-relation pairs ***)

fun preprocess_type_specs ctxt type_specs =
  let

    fun preprocess_entry ctxt ctxt' (T, relt) = 
      let
        val v = T |> Syntax.parse_typ ctxt' |> dest_TVar |> #1
        val relt = Syntax.read_term ctxt relt
        val T = type_of relt
        val _ = T |> HOLogic.is_binrelT 
          orelse error ("trp" |> mk_msg_binrel |> mk_msg_ctr)
        val (U, V) = HOLogic.dest_binrelT T
        val _ = is_TFree U andalso is_TFree V 
          orelse error ("trp" |> mk_msg_binrel_ftv |> mk_msg_ctr)
        val S = V |> dest_TFree |> #2
      in ((v, S), relt) end

    val type_specs = 
      let val ctxt' = Proof_Context.init_global (Proof_Context.theory_of ctxt)
      in map (preprocess_entry ctxt ctxt') type_specs end

    val _ = type_specs |> map #1 |> has_duplicates op= |> not
      orelse error ("trp" |> mk_msg_no_dup_stvs |> mk_msg_ctr)

    val _ = type_specs 
      |> map #2 
      |> map (fn T => Term.add_tfrees T [])
      |> flat
      |> has_duplicates op=
      |> not
      orelse error ("trp" |> mk_msg_no_dup_binrel_ftvs |> mk_msg_ctr)

    val ctxt' = type_specs
      |> map (#2 #> (fn t => Term.add_frees t []))
      |> flat 
      |> map #1
      |> Variable.fix_new_vars ctxt
      |> fold (Variable.declare_term) (map #2 type_specs)

  in (type_specs, ctxt') end;



(*** Preprocessing of the context elements ***)

fun preprocess_declaration elems lthy = 
  let
    val lthy' = Expression.read_statement elems (Element.Shows []) lthy |> #2
    val assms = Assumption.local_prems_of lthy' lthy
    val (assms', lthy'') = Thm.unvarify_local_fact lthy' assms
  in (assms', lthy'') end;

fun preprocess_definition ctxt thm_spec = 
  let
    val thm_spec' = apfst (apsnd (Local_Defs.meta_rewrite_rule ctxt)) thm_spec
    val thm = thm_spec' |> #1 |> #2
    val _ = check_def ctxt thm
    val b = case thm_spec' |> #1 |> #1 of
        SOME b => b
      | NONE => 
          let
            val c = thm 
              |> Thm.cprop_of 
              |> Thm.dest_equals_lhs 
              |> Thm.term_of
              |> head_of
              |> dest_Const
              |> fst
          in 
            Binding.qualified_name_mandatory 
              (CTR_Utilities.qualified_name_of_const_name c ^ ".transferred") 
          end
  in ((b, thm_spec' |> #1 |> #2), thm_spec' |> #2)  end;



(*** Preprocessing of the theorem specification ***)

fun preprocess_thm_spec ctxt type_specs thm_spec = 
  let

    (*auxiliary*)

    fun gen_indexed_rel_names n c = ((replicate n c), (1 upto n))
      ||> map Int.toString
      |> op~~
      |> map (op^)

    (*theorems*)
    val thm_spec = preprocess_definition ctxt thm_spec

    (*invent a new brel for each ftv not previously associated with a brel*)
    val ftvs = thm_spec
      |> (#1 #> #2 #> Thm.full_prop_of #> (fn t => Term.add_tvars t []))
      |> distinct op=
      |> subtract op= (map #1 type_specs)    
    val (cs, ctxt') =
      Variable.variant_fixes (gen_indexed_rel_names (length ftvs) "A") ctxt
    val Ss = map #2 ftvs
    val (lhsTs, ctxt'') = Variable.invent_types Ss ctxt' |>> map TFree
    val (rhsTs, ctxt''') = Variable.invent_types Ss ctxt'' |>> map TFree
    val ts = map Free (cs ~~ map HOLogic.mk_binrelT (lhsTs ~~ rhsTs))
    val ctxt'''' = fold Variable.declare_term ts ctxt'''
    val type_specs = type_specs @ (ftvs ~~ ts)

  in ((thm_spec, type_specs), ctxt'''') end;


(*** Preprocessing of the keyword synthesis ***)

fun preprocess_synthesis (synthesis : (string * thm list option) option) = 
  case synthesis of
      SOME (_, thm_opt) => 
        (
          case thm_opt of 
              SOME simp_spec => (true, SOME simp_spec)
            | NONE => (true, NONE)
        )
    | NONE => (false, NONE);



(**** Evaluation ****)

fun apply_algorithm ctxt' alg synthesis assms type_specs thm_spec = 
  let
    fun mk_msg_relator f T = T
      |> dest_Type
      |> #1
      |> f 
      |> mk_msg_ctr
    fun mk_error_no_relator T = mk_msg_relator mk_msg_no_relator T
    fun mk_error_invalid_relator T = mk_msg_relator mk_msg_invalid_relator T
    val alg_out = case alg of 
        relativization => 
          (
            CTR_Relativization.apply ctxt' synthesis assms type_specs thm_spec
            handle 
                TYPE ("pr_of_typ: no relator", [T], []) => 
                  error (mk_error_no_relator T) 
              | TYPE ("pr_of_typ: invalid relator", [T], []) => 
                  error (mk_error_invalid_relator T) 
          )
      | parametricity => CTR_Parametricity.apply 
          ctxt' synthesis assms type_specs thm_spec
  in alg_out end;

fun postprocess_alg_out b mf alg_out ctxt = case alg_out of
    ALGRelativization thm => 
      CTR_Postprocessing.postprocess_relativization b mf thm ctxt
  | ALGParametricity thm => 
      CTR_Postprocessing.postprocess_parametricity b thm ctxt
  | ALGFailure => error "ctr: a transfer rule could not be established.";

fun process_definition ctxt' alg synthesis assms type_specs thm_spec ctxt = 
  let
    val alg_out = thm_spec 
      |> #1 
      |> #2 
      |> apply_algorithm ctxt' alg synthesis assms type_specs
      |> apply_alg_out (singleton (Proof_Context.export ctxt' ctxt))
  in postprocess_alg_out (thm_spec |> #1 |> #1) (#2 thm_spec) alg_out ctxt end;



(*** Parametricity ***)

fun process_parametricity thm_spec lthy = 
  let val thm_spec' = preprocess_definition lthy thm_spec 
  in 
    process_definition lthy parametricity (false, NONE) [] [] thm_spec' lthy 
  end;



(*** Relativization ***)

fun preprocess_relativization lthy synthesis elems type_specs thm_spec = 
  let
    val synthesis' = preprocess_synthesis synthesis
    val (assms, lthy') = preprocess_declaration elems lthy
    val (type_specs', lthy'') = preprocess_type_specs lthy' type_specs
    val ((thm_spec', type_specs''), lthy''') = 
      preprocess_thm_spec lthy'' type_specs' thm_spec
  in ((synthesis', assms, type_specs'', thm_spec'), lthy''') end;

fun process_relativization synthesis elems type_specs thm_spec lthy = 
  let
    val ((synthesis, assms, type_specs, thm_spec), lthy') = 
      preprocess_relativization lthy synthesis elems type_specs thm_spec 
    val lthy'' = process_definition
      lthy' relativization synthesis assms type_specs thm_spec lthy
  in lthy'' end;




(**** Interface ****)

fun process_parametricities thm_specs lthy = fold
  (
    fn thm_spec => fn ctxt => 
      process_parametricity thm_spec ctxt |> lthy_of_pp_out
  ) 
  thm_specs
  lthy;

fun process_relativizations synthesis elems type_specs thm_specs lthy =  
  let 
    fun process_relativization' thm_spec ctxt =  
      process_relativization synthesis elems type_specs thm_spec ctxt 
      |> lthy_of_pp_out
  in fold process_relativization' thm_specs lthy end;

fun process_ctrs args lthy = 
  let
    fun preprocess_thm_specs lthy = 
      map (apfst (apsnd (singleton (Attrib.eval_thms lthy))))
    fun process_ctrs_impl (ALG_PP thm_specs) lthy = 
          process_parametricities (preprocess_thm_specs lthy thm_specs) lthy
      | process_ctrs_impl 
          (ALG_RP (((synthesis, elems), type_specs), thm_specs)) lthy =
          let
            val thm_specs' = preprocess_thm_specs lthy thm_specs
            val synthesis' = Option.map 
              (apsnd (Option.map ((single #> Attrib.eval_thms lthy)))) 
              synthesis
          in
            process_relativizations synthesis' elems type_specs thm_specs' lthy 
          end
  in process_ctrs_impl args lthy end;

val _ =
  Outer_Syntax.local_theory 
    \<^command_keyword>\<open>ctr\<close> 
    "automated synthesis of transfer rules and relativization of definitions"
    (ctr_parser >> process_ctrs);

end;