subsection \<open> RoboChart State Machine Compiler \<close>

theory StateMachine
  imports MetaModel
  keywords "statemachine" :: "thy_decl_block" and "states" "initial" "transitions" "vars" "events"
begin

subsection \<open> Interface to Algebraic Datatypes \<close>

lemma meta_refl: "(x = x) \<equiv> True"
  by (simp)

lemmas sc_rewrites = aext_true[THEN eq_reflection] aext_false[THEN eq_reflection] if_True[THEN eq_reflection] if_False[THEN eq_reflection] meta_refl option.simps(1,4-9)[THEN eq_reflection]

ML \<open>
structure Datatype_Utils =
struct
fun basic_datatype (name, ctrs) =
  BNF_FP_Def_Sugar.co_datatype_cmd BNF_FP_Rec_Sugar_Util.Least_FP BNF_LFP.construct_lfp 
       (Ctr_Sugar.default_ctr_options_cmd, [((((([],name),Mixfix.NoSyn),ctrs), (Binding.empty, Binding.empty, Binding.empty)),[])]);
end;
\<close>

subsection \<open> ML Code to compile statemachines \<close>

ML \<open>
signature STATEMACHINE_COMPILER =
sig
  val statemachineParser:
         (binding *
          (((((binding * string * mixfix) list option * (binding * string option) list option) * (binding * string) list) * binding) *
           (binding * string) list option)) parser
  val compileStatemachine:
       binding *
       (((((binding * string * mixfix) list option * (binding * string option) list option) * (binding * string) list) * binding) *
        (binding * string) list option)
         -> theory -> theory
end;

structure StateMachine_Compiler : STATEMACHINE_COMPILER =
struct

fun prove_eq_simplify ctx t1 t2 thms = 
  Goal.prove ctx [] []
      (hd (Type_Infer_Context.infer_types ctx [ HOLogic.Trueprop $ (Const ("HOL.eq", dummyT) $ t1 $ t2)]))
      (fn {context = context, prems = _} =>
          EVERY [ PARALLEL_ALLGOALS (asm_simp_tac (fold Simplifier.add_simp thms context)) ]);

open HOLogic;
open Datatype_Utils;
open Parse;
open Scan;

val event_binding = binding -- option ($$$ "::" |-- !!! typ);

val varDeclParser = @{keyword "vars"} |-- repeat1 const_binding;

val eventsParser = @{keyword "events"} |-- repeat1 event_binding;

val defaultState = "entry skip during skip exit skip";

val stateDeclParser = @{keyword "states"} |-- repeat1 (binding -- optional ($$$ ":" |-- term) defaultState);

val initStateParser = @{keyword "initial"} |-- binding;

val transDeclParser = @{keyword "transitions"} |-- repeat1 ((binding --| $$$ ":") -- term);

val statemachineParser = 
  Parse.binding -- 
    (Parse.$$$ "[" |-- 
      Scan.option varDeclParser -- 
      Scan.option eventsParser -- 
      stateDeclParser --
      initStateParser --
      Scan.option transDeclParser
    --| Parse.$$$ "]");

fun compileVarDecls (sm_binding : binding, SOME defs) = 
  Lens_Utils.add_alphabet_cmd 
    {overloaded = false} 
    ([], Binding.suffix_name "_alphabet" sm_binding) 
    NONE 
    defs |
compileVarDecls (sm_binding : binding, NONE) = 
  Named_Target.theory_map (
  snd o Typedecl.abbrev_cmd (Binding.suffix_name "_alphabet" sm_binding, [], Mixfix.NoSyn) "robochart_ctrl");;

fun compileEventDecls (SOME defs) =
  basic_datatype (Binding.name "events", 
                  (((Binding.empty, Binding.name "null_event"), []), Mixfix.NoSyn) ::
                  map (fn (b, SOME t) => (((Binding.empty, b), [(Binding.empty, t)]), Mixfix.NoSyn) |
                          (b, NONE) => (((Binding.empty, b), []), Mixfix.NoSyn)) defs) |

compileEventDecls NONE =
  snd o Typedecl.abbrev_cmd (Binding.name "events", [], Mixfix.NoSyn) "unit";

fun mk_def ty = Const ("Pure.eq", ty --> ty --> Term.propT);

fun nodeBodyT state event = Type (@{type_name NodeBody_ext}, [state, event, unitT]);
fun nodeT state event = mk_prodT (HOLogic.stringT, nodeBodyT state event);
fun transitionT state event = Type (@{type_name "Transition_ext"}, [state, event, unitT]);
fun statemachineT state event = Type (@{type_name "StateMachine_ext"}, [state, event, unitT]);
fun actionT state event = Type ("Actions.Action", [state, event]); 

val mk_StateMachine = Const (fst (dest_Const @{term StateMachine.make}), dummyT);
val sm_semantics = Const (fst (dest_Const @{term sm_semantics}), dummyT);


fun compileStateDecls defs typ ctx =
  fold (fn (b, t) => fn (ts, ctx) =>        
           let 
             val tm = pair_const @{typ string} dummyT $ mk_string (Binding.name_of b) $ Syntax.parse_term ctx t;
             val (t', ctx') = Specification.definition NONE [] [] ((Binding.empty, []), mk_def typ $ Free (Binding.name_of b, typ) $ tm) ctx
           in
             (t' :: ts, ctx')
           end
        ) defs ([], ctx);

fun compileTransDecls (SOME defs) typ ctx =
  fold (fn (b, t) => fn (ts, ctx) =>        
           let 
             val tm = Syntax.parse_term ctx t;
             val (t', ctx') = Specification.definition NONE [] [] ((Binding.empty, []), mk_def typ $ Free (Binding.name_of b, typ) $ tm) ctx
           in
             (t' :: ts, ctx')
           end
        ) defs ([], ctx)
  |
  compileTransDecls NONE _ ctx = ([], ctx);

fun compileTransSem null_event def_thms tds ctx =
  let
    val sem_thms = 
      map (fn (term, (n, thm)) =>
        (* Use simplifier with definitional theorems and Circus laws to calculate semantics *)
        let val thms = (def_thms @ @{thms Transition.defs} @ [@{thm tr_semantics_def}]);
            val thms_raw = @{thms sc_rewrites} @ @{thms Transition.select_convs[THEN eq_reflection]} @ thms
            val ft = Syntax.check_term ctx (Const ("MetaModel.tr_semantics", dummyT) $ term $ null_event) (* (Const ("MetaModel.tr_semantics", dummyT) $ term $ null_event) *);
            val semt = Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctx) thms_raw [] ft;
        in prove_eq_simplify ctx ft semt thms end) tds;
  in Local_Theory.note ((Binding.name "semantics", []), sem_thms) ctx end;


fun compileStatemachine (n, ((((vs, es), ss), ins), ts)) thy0 =
  let val thy1 = compileVarDecls (n, vs) thy0;
      val (loc, ctx0) = Expression.add_locale_cmd n Binding.empty ([],[]) [] thy1;
      val ctx1 = compileEventDecls es ctx0;
      val alphaT = Syntax.read_typ ctx1 (Binding.name_of n ^ "_alphabet");
      val evT = Syntax.read_typ ctx1 ("events");
      val stateT = nodeT alphaT evT;
      val tranT = transitionT alphaT evT;
      val machineT = statemachineT alphaT evT;
      val actT = actionT (Type (@{type_name "robochart_ctrl_ext"}, [alphaT])) evT;
      val (tds, ctx2) = compileTransDecls ts tranT ctx1;
      val transDef = mk_def (listT tranT) $ Free ("transitions", (listT tranT)) $ mk_list tranT (map fst tds);
      val ((tr_term, (_, tr_thm)), ctx3) = Specification.definition NONE [] [] ((Binding.empty, []), transDef) ctx2;
      val (sds, ctx4) = compileStateDecls ss stateT ctx3;
      val statesDef = mk_def (listT stateT) $ Free ("states", (listT stateT)) $ mk_list stateT (map fst sds)
      val ((st_term, (_, st_thm)), ctx5) = Specification.definition NONE [] [] ((Binding.empty, []), statesDef) ctx4;
      val machineDef = mk_def machineT $ Free ("machine", machineT) $ (mk_StateMachine $ mk_string (Binding.name_of ins) $ st_term $ tr_term)
      val ((mch_term, (_, mch_thm)), ctx6) = Specification.definition NONE [] [] ((Binding.empty, []), machineDef) ctx5;
      val null_event = Syntax.read_term ctx6 "null_event";
      val semDef = mk_def actT $ Free ("action", actT) $ (sm_semantics $ mch_term $ null_event);
      val ((act_term, (_, act_thm)), ctx7) = Specification.definition NONE [] [] ((Binding.empty, []), semDef) ctx6;
      val def_thms = map (snd o snd) tds @ map (snd o snd) sds @ [st_thm, tr_thm, mch_thm, act_thm];
      val (_, ctx8) = Local_Theory.note ((Binding.name "defs", []), def_thms) ctx7;
      val (_, ctx9) = compileTransSem null_event def_thms tds ctx8;
  in Local_Theory.exit_global ctx9
  end;

val _ =
  Outer_Syntax.command @{command_keyword statemachine} "define RoboChart state machines" 
  (statemachineParser >> (Toplevel.theory o compileStatemachine));

end;
\<close>

end