signature CS_COND_SIMP =
sig
datatype match = mdefault | mfull;
datatype ist = ist_simple | ist_compound;
datatype is_thm = cs_simp of thm list | cs_intro of thm list;
val concl_simp_of_simp : thm -> thm
val prems_simp_of_simp : thm -> thm
val remdups_tac : Proof.context -> int -> tactic
val cs_concl_step_tac :
  Proof.context -> bool -> match -> thm list -> int -> tactic
val cs_concl_step : Proof.context -> bool -> match -> thm list -> Method.method
val cs_intro_step_tac : Proof.context -> bool -> thm list -> int -> tactic
val cs_intro_search_tac : Proof.context -> bool -> thm list -> int -> tactic
val cs_concl_tac :
  Proof.context -> bool -> match -> ist -> is_thm list -> int -> tactic
val cs_concl :
  Proof.context -> int -> bool -> match -> ist -> is_thm list -> Method.method
val cs_prems_atom_step_tac : 
  Proof.context -> match -> thm list -> int -> tactic
val cs_prems_atom_step : Proof.context -> match -> thm list -> Method.method
val cs_prems_step_tac :
  Proof.context ->
  bool ->
  match ->
  ist ->
  thm list ->
  is_thm list ->
  int ->
  thm ->
  thm Seq.seq
val cs_prems_step: 
  Proof.context -> bool -> match -> ist -> is_thm list -> Method.method
val cs_prems_tac :
  Proof.context -> bool -> match -> ist -> thm list -> is_thm list -> tactic
val cs_prems: 
  Proof.context -> int -> bool -> match -> ist -> is_thm list -> Method.method
end;


structure CS_Cond_Simp: CS_COND_SIMP =
struct



(*** General purpose utilities ***)


(** General purpose messages **)

val msg_simp_rules = "cs: invalid simplification rules"


(** Synthesis of introduction rules from conditional rewrite rules **)

fun concl_simp_of_simp thm = thm RS @{thm forw_subst};

fun map_concl_simp_of_simp thms = map concl_simp_of_simp thms
  handle THM ("RSN: no unifiers", _, _) => (warning msg_simp_rules; []);

fun prems_simp_of_simp thm = (thm RS @{thm subst})
  |> rotate_prems ~1
  |> Tactic.make_elim;

fun map_prems_simp_of_simp thms = map prems_simp_of_simp thms
  handle THM ("RSN: no unifiers", _, _) => (warning msg_simp_rules; []);


(** Removal of duplicate premises **)

(*Copied (with amendments) from the file ~/Tools/intuitionistic.ML in the 
main distribution of Isabelle2020.*)
fun remdups_tac ctxt = SUBGOAL 
  (
    fn (g, i) =>
    let val prems = Logic.strip_assums_hyp g 
    in
      REPEAT_DETERM_N (length prems - length (distinct op aconv prems))
      (ematch_tac ctxt [Drule.remdups_rl] i THEN Tactic.eq_assume_tac i)
    end
  );

val _ = Theory.setup
  (
    Method.setup \<^binding>\<open>remdups\<close> 
      (Scan.succeed (SIMPLE_METHOD' o remdups_tac))
      "removal of duplicate premises"
  );



(*** Flags ***)


(** Match function selector **)

datatype match = mdefault | mfull;

fun fun_of_match mdefault = CS_UM.match_inst_rec
  | fun_of_match mfull = CS_UM.match_inst_list;

fun match_of_cs_match "cs_default" = mdefault
  | match_of_cs_match "cs_full" = mfull
  | match_of_cs_match _ = error "match_of_cs_match: invalid keyword";

val cs_match_parser = Scan.lift (Scan.optional (\<^keyword>\<open>cs_full\<close>) "cs_default");


(** Introduction step selector **)

datatype ist = ist_simple | ist_compound;

fun ist_of_cs_ist "cs_ist_simple" = ist_simple
  | ist_of_cs_ist "cs_ist_compound" = ist_compound
  | ist_of_cs_ist _ = error "ist_of_cs_ist: invalid keyword";

val cs_ist_parser =
  Scan.lift (Scan.optional (\<^keyword>\<open>cs_ist_simple\<close>) "cs_ist_compound");


(** Printed output **)

fun print_state ctxt c st =
  let
    val c_st = st
      |> Thm.prems_of
      |> hd
      |> Logic.strip_imp_concl
      |> Syntax.string_of_term ctxt
  in writeln (c ^ c_st) end;



(*** Auxiliary tactics and tacticals ***)

fun ONLY_IF_NULL p f = if null p then f else no_tac;
fun only_if_not_null x = if null x then raise Empty else x;

fun trivial_solved_tac ctxt i =
  let val assm_tac = Method.assm_tac ctxt
  in
    assm_tac i
    APPEND SOLVED' (resolve_tac ctxt @{thms HOL.sym} THEN' assm_tac) i
    APPEND SOLVED' (resolve_tac ctxt @{thms HOL.not_sym} THEN' assm_tac) i
    APPEND SOLVED' (resolve_tac ctxt @{thms HOL.refl}) i
  end;



(*** Conditional simplification of a conclusion ***)

fun is_trivial_intro thm = thm
  |> Thm.prems_of
  |> find_index (fn t => t aconv (Thm.concl_of thm))
  |> (curry op<= 0);

fun concl_match_inst m =
  CS_UM.match_inst (fun_of_match m) Thm.concl_of is_trivial_intro;

fun match_concl_tac ctxt m rwr =
  Subgoal.FOCUS
    (
      fn {context = ctxt', concl = concl_ct, params = params, ...} =>
        ONLY_IF_NULL params
          (
            HEADGOAL
              (
                Classical.rule_tac
                  ctxt'
                  (
                    concl_ct
                    |> Thm.term_of
                    |> Logic.strip_imp_concl
                    |> concl_match_inst m ctxt' rwr
                    |> only_if_not_null
                  )
                  []
              )
              handle
                  Empty => no_tac
                | Pattern.MATCH => no_tac
          )
    )
    ctxt;

fun cs_concl_step_tac ctxt verbose m rwr_thms i st =
  let
    val _ = if verbose then print_state ctxt "simp: " st else ()
    val tacs = map (match_concl_tac ctxt m) rwr_thms
  in 
    Subgoal.FOCUS_PARAMS
      (
        fn {context = ctxt', ...} =>
          (
            trivial_solved_tac ctxt' 1
            APPEND
              (
                CONVERSION Thm.eta_conversion 1
                THEN FIRST_APPEND' tacs 1
                THEN TRY (remdups_tac ctxt' 1)
              )
          )
      )
      ctxt
      i
      st
  end;

fun cs_concl_step ctxt verbose m rwr_thms =
  let val rwr_thms' = map_concl_simp_of_simp rwr_thms
  in SIMPLE_METHOD' (cs_concl_step_tac ctxt verbose m rwr_thms') end;

val _ = Theory.setup
  (
    Method.setup
      \<^binding>\<open>cs_concl_step\<close>
      (
        cs_match_parser -- Attrib.thms >>
          (
            fn (csm, thms) => fn ctxt =>
              cs_concl_step ctxt false (match_of_cs_match csm) (rev thms)
          )
      )
      "conditional simplification of a conclusion"
  );



(*** Introduction for conditional simplification ***)

val default_intro_thms = [@{thm TrueI}];

fun is_sc_match ctxt (sc_rule, t) =
  let 
    fun seq_null seq = is_none (Seq.pull seq);
    val sc_match = Thm.concl_of sc_rule
  in
    (sc_match, t)
    |> single
    |> Unify.matchers (Context.Proof ctxt) 
    |> seq_null
    |> not
  end;

fun cs_intro_step_tac ctxt verbose all_rwrs i =
  let
    val all_rwrs' = all_rwrs @ default_intro_thms
    fun get_hd_goal_concl_t st = st
      |> Thm.prems_of
      |> hd
      |> Logic.strip_imp_concl
      handle
          Empty => Thm.full_prop_of st
        | Pattern.MATCH => Thm.full_prop_of st
    fun side_cond_impl_tac ctxt verbose all_rwrs i st =
      let
        val _ = if verbose then print_state ctxt "intro: " st else ()
        val sts = Method.assm_tac ctxt i st
        val sts = case Seq.pull sts of
            SOME _ => sts
          | NONE =>
              let
                val rwrs = filter
                  (fn rwr => is_sc_match ctxt (rwr, get_hd_goal_concl_t st)) 
                  all_rwrs
                val scrs = rwrs
                  |> map
                    (
                      fn rwr => 
                        (fn thm => thm |> single |> match_tac ctxt) rwr i st
                    )
              in fold Seq.append scrs Seq.empty end
      in sts end
  in
    Subgoal.FOCUS_PARAMS
      (
        fn {context = ctxt', ...} =>
          CONVERSION Thm.eta_conversion 1
          THEN side_cond_impl_tac ctxt' verbose all_rwrs' 1 
          THEN TRY (remdups_tac ctxt' 1)
      )
      ctxt
      i
  end;

fun cs_intro_step ctxt verbose thms = 
  SIMPLE_METHOD' (cs_intro_step_tac ctxt verbose thms);

val _ = Theory.setup
  (
    Method.setup
      \<^binding>\<open>cs_intro_step\<close>
      (Attrib.thms >> (fn thms => fn ctxt => cs_intro_step ctxt false thms))
      "apply side condition introduction rules once"
  );

fun cs_intro_search_tac ctxt verbose all_rwrs i =
  DEPTH_SOLVE_1 (cs_intro_step_tac ctxt verbose all_rwrs i);

fun cs_intro_search ctxt verbose thms = 
  SIMPLE_METHOD' (cs_intro_search_tac ctxt verbose thms);

val _ = Theory.setup
  (
    Method.setup
      \<^binding>\<open>cs_intro_search\<close>
      (Attrib.thms >> (fn thms => fn ctxt => cs_intro_search ctxt false thms))
      "repeated application of the side condition introduction rules"
  );



(*** is_thm : disjoint set of rewrite rules and introduction rules ***)

datatype is_thm = cs_simp of thm list | cs_intro of thm list;

fun is_simp_thms (cs_simp _) = true
  | is_simp_thms (cs_intro _) = false;

fun apply_is_thm f (cs_simp thms) = cs_simp (f thms)
  | apply_is_thm f (cs_intro thms) = cs_intro (f thms);

fun get_thms_of_is_thms (cs_simp thms) = thms
  | get_thms_of_is_thms (cs_intro thms) = thms;

fun process_cs_simps _ [] = []
  | process_cs_simps f (cs_simp thms::is_thms) =
      cs_simp (f thms) :: process_cs_simps f is_thms
  | process_cs_simps f (cs_intro thms::is_thms) =
      cs_intro thms :: process_cs_simps f is_thms;



(*** Combined simplification and introduction solver ***)

fun cs_concl_tac ctxt verbose m ist is_thms i =
  let
    fun concl_step_impl_compound_tac ctxt verbose m (cs_simp thms) =
        cs_concl_step_tac ctxt verbose m (rev thms)
      | concl_step_impl_compound_tac ctxt verbose _ (cs_intro thms) =
        (
          cs_intro_search_tac ctxt verbose thms 
          APPEND' cs_intro_step_tac ctxt verbose thms
        )
    fun concl_step_impl_simple_tac ctxt verbose m (cs_simp thms) =
        cs_concl_step_tac ctxt verbose m (rev thms)
      | concl_step_impl_simple_tac ctxt verbose _ (cs_intro thms) =
        cs_intro_step_tac ctxt verbose thms
    val conc_step_impl_tac = case ist of
        ist_simple => concl_step_impl_simple_tac
      | ist_compound => concl_step_impl_compound_tac
  in 
    (FIRST_APPEND' (map (conc_step_impl_tac ctxt verbose m) is_thms) i)
    |> DEPTH_SOLVE_1
  end;

fun cs_concl ctxt timing verbose m ist is_thms =
  let 
    val is_thms' = 
      process_cs_simps map_concl_simp_of_simp is_thms @ [cs_simp []]
    fun tac i st = 
      CS_TimeIt.TIMEIT timing (cs_concl_tac ctxt verbose m ist is_thms' i) st
  in SIMPLE_METHOD' tac end;

fun cs_simp_intro_thms_parser kw =
  Scan.lift (kw -- Args.colon) |-- Attrib.thms;

val cs_simp_intro_parser =
  cs_simp_intro_thms_parser \<^keyword>\<open>cs_simp\<close> >> cs_simp ||
  cs_simp_intro_thms_parser \<^keyword>\<open>cs_intro\<close> >> cs_intro;

val _ = Theory.setup
  (
    Method.setup
      \<^binding>\<open>cs_concl\<close>
      (
        Scan.option (Scan.lift (Parse.int)) --
        Scan.option (Scan.lift Args.bang) --
        cs_match_parser --
        cs_ist_parser --
        Scan.repeat cs_simp_intro_parser >>
        (
          fn ((((timing, verbose), csm), ist), is_thms) => fn ctxt =>
            cs_concl
              ctxt
              (case timing of SOME n => n | NONE => 0)
              (case verbose of SOME _ => true | NONE => false)
              (match_of_cs_match csm)
              (ist_of_cs_ist ist)
              is_thms
        )
      )
      "combined simplification and introduction solver"
  );



(*** Conditional simplification of premises ***)

fun is_trivial_elim thm =
  let
    val prems = Thm.prems_of thm
    val lhs_t = hd prems
    val rhs_t = prems |> tl |> rev |> hd |> Logic.dest_implies |> #1
  in lhs_t aconv rhs_t end;

val elim_pat_fun = Thm.prems_of #> hd;

fun elim_matcher_inst m =
  CS_UM.match_inst (fun_of_match m) elim_pat_fun is_trivial_elim;

fun match_prems_tac ctxt m rwr =
  Subgoal.FOCUS_PARAMS_FIXED
    (
      fn {context = ctxt', concl = concl, params = params, ...} =>
        ONLY_IF_NULL params
          (
            let
              fun initialize ctxt' concl =
                let
                  val prems = concl |> Thm.term_of |> Logic.strip_imp_prems
                  val thms = prems 
                    |> hd 
                    |> elim_matcher_inst m ctxt' rwr 
                    |> only_if_not_null
                  val insts = Thm.match 
                    (
                      (("V", 0), \<^typ>\<open>prop\<close>) |> Var |> Thm.cterm_of ctxt',
                      Thm.cterm_of ctxt' (nth prems 0)
                    )
                  val remdups = Drule.instantiate_normalize insts thin_rl
                in (remdups, thms) end
              val params = SOME (initialize ctxt' concl)
                handle 
                    Empty => NONE
                  | Pattern.MATCH => NONE
            in
              case params of
                  NONE => no_tac
                | SOME (remdups, thms) =>
                    HEADGOAL
                      (
                        Subgoal.FOCUS
                          (
                            fn {context = ctxt'', ...} =>
                              HEADGOAL (Classical.rule_tac ctxt'' thms [])
                              handle Empty => no_tac
                          )
                        ctxt'
                      )
                THEN (PRIMITIVE (Thm.permute_prems 0 ~1))
                THEN HEADGOAL (eresolve_tac ctxt' (single remdups))
                THEN HEADGOAL (rotate_tac ~1)
                THEN HEADGOAL defer_tac
            end
          )
    )
    ctxt;

fun cs_prems_atom_step_tac ctxt m rwr_thms i =
  let val tacs = map (match_prems_tac ctxt m) rwr_thms
  in
    Subgoal.FOCUS_PARAMS
      (
        fn {context = ctxt', ...} =>
          trivial_solved_tac ctxt' 1
          APPEND
            (
              CONVERSION Thm.eta_conversion 1
              THEN FIRST_APPEND' tacs 1
              THEN TRY (remdups_tac ctxt' 1)
            )
      )
      ctxt
      i
  end;

fun cs_prems_atom_step ctxt m rwr_thms =
  let val rwr_thms' = map_prems_simp_of_simp rwr_thms
  in SIMPLE_METHOD' (cs_prems_atom_step_tac ctxt m rwr_thms') end;

val _ = Theory.setup
  (
    Method.setup
      \<^binding>\<open>cs_prems_atom_step\<close>
      (
        cs_match_parser -- Attrib.thms >>
          (
            fn (csm, thms) => fn ctxt =>
              cs_prems_atom_step ctxt (match_of_cs_match csm) (rev thms)
          )
      )
      "conditional simplification of premises: single atomic step"
  );

fun cs_prems_step_tac ctxt verbose m ist prem_rwr_thms concl_is_thms i st =
  let
    fun cs_prems_intro_step i st =
      let val sgn = Thm.nprems_of st
      in
        if i = sgn
        then all_tac st
        else
          if i > sgn
          then no_tac st
          else
            st
            |> cs_concl_tac ctxt verbose m ist concl_is_thms i
            |> Seq.map (cs_prems_intro_step i)
            |> Seq.flat
      end
    val sts = st
      |> cs_prems_atom_step_tac ctxt m prem_rwr_thms i
      |> Seq.map (cs_prems_intro_step i)
      |> Seq.flat
  in sts end;

fun mk_prem_thms is_thms =
  let
    val prem_rwr_thms = is_thms
      |> filter is_simp_thms
      |> map (apply_is_thm (map_prems_simp_of_simp))
      |> map get_thms_of_is_thms
      |> flat
    val concl_is_thms = process_cs_simps (map_concl_simp_of_simp) is_thms
  in (prem_rwr_thms, concl_is_thms) end;

fun cs_prems_step ctxt verbose m ist is_thms = 
  let val (prem_rwr_thms, concl_is_thms) = mk_prem_thms is_thms
  in 
    SIMPLE_METHOD' (
      cs_prems_step_tac ctxt verbose m ist prem_rwr_thms concl_is_thms
      )
  end;

val _ = Theory.setup
  (
    Method.setup
      \<^binding>\<open>cs_prems_step\<close>
      (
        Scan.option (Scan.lift Args.bang) --
        cs_match_parser --
        cs_ist_parser --
        Scan.repeat cs_simp_intro_parser >>
        (
          fn (((verbose, csm), ist), is_thms) => fn ctxt =>
            cs_prems_step 
              ctxt 
              (case verbose of SOME _ => true | NONE => false)
              (match_of_cs_match csm)
              (ist_of_cs_ist ist) 
              is_thms
        )
      )
      "conditional simplification of premises: single step"
  );

fun cs_prems_tac ctxt verbose m ist prem_rwr_thms concl_is_thms =
  REPEAT_SOME (cs_prems_step_tac ctxt verbose m ist prem_rwr_thms concl_is_thms);

fun cs_prems ctxt timing verbose m ist is_thms =
  let 
    val (prem_rwr_thms, concl_is_thms) = mk_prem_thms is_thms |>> rev
    val tac = cs_prems_tac ctxt verbose m ist prem_rwr_thms concl_is_thms
      |> CS_TimeIt.TIMEIT timing 
  in SIMPLE_METHOD tac end;

val _ = Theory.setup
  (
    Method.setup
      \<^binding>\<open>cs_prems\<close>
      (
        Scan.option (Scan.lift (Parse.int)) --
        Scan.option (Scan.lift Args.bang) --
        cs_match_parser --
        cs_ist_parser --
        Scan.repeat cs_simp_intro_parser >>
        (
          fn ((((timing, verbose), csm), ist), is_thms) => fn ctxt => 
            cs_prems 
              ctxt
              (case timing of SOME n => n | NONE => 0)
              (case verbose of SOME _ => true | NONE => false)
              (match_of_cs_match csm) 
              (ist_of_cs_ist ist) 
              is_thms
        )
      )
      "conditional simplification of premises"
  );

end;