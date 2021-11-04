(* 
    This is a file that containts a grammar and a parser for
    Fast-Downward's Multi-valued problem representation.
*)

structure LexSASProb =
(* An implementation that uses token parser. *)
struct

  open ParserCombinators
  open CharParser

  infixr 4 << >>
  infixr 3 &&
  infix  2 -- ##
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??

  structure SASProbDef :> LANGUAGE_DEF =
  struct

    type scanner = SubstringMonoStreamable.elem CharParser.charParser

    val commentStart   = NONE
    val commentEnd     = NONE
    val commentLine    = NONE
    val nestedComments = false

    val alphaNumUnderDashSpace  = try (satisfy (fn c =>
                                (if (Char.isAlphaNum c)
                                 then true
                                 else if (c = #"_")
                                 then true
                                 else if (c = #"-")
                                 then true
                                 else if (c = #" ")
                                 then true
                                 else if (c = #"(")
                                 then true
                                 else if (c = #")")
                                 then true
                                 else if (c = #",")
                                 then true
                                 else if (c = #"<")
                                 then true
                                 else if (c = #">")
                                 then true
                                 else false)) ) ?? "alphanumeric character"

    val identLetter    = alphaNumUnderDashSpace (*Idents can only be separated with \n and can contain [Aa-Zz], [0-9], " ", "-", "_"*)
    val identStart     = identLetter
    val opStart        = fail "Operators not supported" : scanner
    val opLetter       = opStart
    val reservedNames  = ["begin_version", "end_version",
                          "begin_metric", "end_metric",
                          "begin_variable", "end_variable",
                          "begin_mutex_group", "end_mutex_group",
                          "begin_state", "end_state",
                          "begin_goal", "end_goal",
                          "begin_operator", "end_operator"]
    val reservedOpNames= []
    val caseSensitive  = true

  end

  structure RTP = TokenParser (SASProbDef)
  open RTP

  val SMLCharImplode = String.implode;
  val SMLCharExplode = String.explode;


  val num = (lexeme ((char #"-" || digit) && (repeat digit)) when
	      (fn (x,xs) => Int.fromString (SMLCharImplode (x::xs)))) ?? "num expression"

  val sas_ident = identifier

  fun sas_reserved wrd = (reserved wrd)

  val version  = (sas_reserved "begin_version" ?? "begin_version")>>
                  (num ?? "version number") <<
                  (sas_reserved "end_version" ?? "begversion")

  val metric  = (sas_reserved "begin_metric" ?? "begin_metric")>>
                (num ?? "Metric number") <<
                (sas_reserved "end_metric" ?? "end_metric")

  val variable  = (sas_reserved "begin_variable" ?? "begin_variable")>>
                  (sas_ident ?? "Variable name") &&
                  (num ?? "Axiom layer") &&
                  ((num ?? "Number of asses") --
                   (fn n_asses => (repeatn n_asses sas_ident) ?? "Atom names")) <<
                  (sas_reserved "end_variable" ?? "end_variable")
                  ?? "SAS+ Variable"

  val sas_ass = (num ?? "SAS+ Variable ID") &&
                (num ?? "SAS+ ass")
                ?? "sas+ ass"

  val mutex_group = (sas_reserved "begin_mutex_group" ?? "begin_mutex_group")>>
              ((num ?? "number of mutexes") --
               (fn n_mutexes => (repeatn n_mutexes sas_ass) ?? "SAS+ asses")) <<
              (sas_reserved "end_mutex_group" ?? "end_mutex_group")
              ?? "mutex"

  val init_state = (sas_reserved "begin_state" ?? "begin_state")>>
              (repeat1 num ?? "Initial state assignments") <<
              (sas_reserved "end_state" ?? "end_state")
              ?? "Initial state"

  val goal = (sas_reserved "begin_goal" ?? "begin_goal")>>
              ((num ?? "Number of goal asses") --
               (fn n_goals => (repeatn n_goals sas_ass) ?? "Goal asses"))  <<
              (sas_reserved "end_goal" ?? "end_goal")
              ?? "Initial state"

  val numPreconds = 0

  val effect = ((num ?? "Number of effect preconds") --
                (fn n_eff_pres => ((repeatn n_eff_pres sas_ass ) ?? "Effect preconds"))) &&
                (num ?? "Variable ID") &&
                (num ?? "Old ass") &&
                (num ?? "New ass") ?? "Effect"

  val operator = (sas_reserved "begin_operator" ?? "begin_operator")>>
              (sas_ident ?? "Operator name") &&
              ((num ?? "Number of preconds") --
               (fn n_preconds => (repeatn n_preconds sas_ass) ?? "Prevail preconditions")) &&
              ((num ?? "Number of effects") --
                (fn n_eff => (repeatn n_eff effect) ?? "Action effects")) &&
              (num ?? "Cost") <<
              (sas_reserved "end_operator" ?? "end_operator")
              ?? "Operator"

  val problem   = version && metric &&
                 ((num ?? "Number of SAS+ variables") --
                  (fn n_sas_vars => (repeatn n_sas_vars variable) ?? "SAS+ variables section")) &&
                 ((num ?? "Number of mutex groups") --
                  (fn n_mutx => repeatn n_mutx mutex_group ?? "Mutex groups section")) &&
                 (init_state) &&
                 (goal) &&
                 ((num ?? "Number of operators") --
                  (fn n_opr => (repeatn n_opr operator)?? "Operators")) &&
                 (num ?? "Number of axioms") <<
                 (eos ?? "end of stream") ?? "problem"

  val plan   = (repeat sas_ident) ?? "Plan"

  val model_line = (sas_reserved "v" ?? "v, parsing model_line")>>
                   (repeat num ?? "literal, parsing model_line")

  val model = (repeat model_line ?? "model_line, parsing model")
      
end

fun readFile file =
let
    fun next_String input = (TextIO.inputAll input)
    val stream = TextIO.openIn file
in
    next_String stream
end

fun parse_plan plan_file =
  (CharParser.parseString LexSASProb.plan (readFile plan_file))


type SAS_VAR = (string * (int * string list))

fun varToString (variable_name: string,
                 (axiom_layer:int,
                   atom_names :string list)) =
         " Variable name = " ^ variable_name ^
         "\n  Axiom layer = " ^ Int.toString(axiom_layer) ^
         "\n  Atoms:\n   " ^ ((String.concatWith "\n   ") atom_names);

fun sasAssToString (varID: int, ass: int) =
         "  VariableID = " ^ Int.toString(varID) ^
         " Ass = " ^ Int.toString(ass);

fun mutexGroupToString (mutex_group: (int * int) list) =
         "\n  Mutex group asses:\n" ^ ((String.concatWith "\n") (map sasAssToString mutex_group));

type SAS_ASS = int * int

fun effectToString (effect_preconds: SAS_ASS list,
                     (var_ID: int,
                      (old_ass: int,
                       (new_ass)))) =
         "\n  Effect:" ^ ((String.concatWith "\n   ") (map sasAssToString effect_preconds)) ^
         "\n  Var ID = " ^ Int.toString(var_ID) ^
         " Old ass = " ^ Int.toString(new_ass) ^
         " New ass = " ^ Int.toString(old_ass);

type EFFECT = ((SAS_ASS list) * (int * (int * int)))

fun operatorToString
                (operator_name: string,
                   (preconds: SAS_ASS list,
                     (effects: EFFECT list,
                      (cost: int)))) =
         " Operator name = " ^ operator_name ^
         "\n  Preconds:\n" ^ ((String.concatWith "\n   ") (map sasAssToString preconds)) ^
         "\n  Effects:\n   " ^ ((String.concatWith "\n   ") (map effectToString effects)) ^
         "\n  Cost = "  ^ Int.toString(cost);

type MUTEX_GRP = ((SAS_ASS list))

type OPRTR = string *
              ((SAS_ASS list)*
               ((EFFECT list) * int))

type SAS_PROB =  int*
             (int*
              ((SAS_VAR list) *
                ((MUTEX_GRP list) *
                 ((int list)*
                   ((SAS_ASS list)*
                     ((OPRTR list) * int))))))

fun probToString
           (version_res:int,
             (metric_res:int,
               (variables: SAS_VAR list,
                 (mutex_groups: MUTEX_GRP list,
                  (init_state: int list,
                    (goal: SAS_ASS list,
                      (operators: OPRTR list,
                       num_axioms: int))))))) =
         ("Version = " ^ (Int.toString version_res) ^ "\n") ^
         ("Metric = " ^ (Int.toString metric_res) ^ "\n") ^
         ("SAS+ vars:\n" ^ ((String.concatWith "\n") (map varToString variables)) ^ "\n") ^
         ("Mutex Groups:\n" ^ ((String.concatWith "\n") (map mutexGroupToString mutex_groups)) ^ "\n") ^
         ("Initial state:\n " ^ ((String.concatWith "\n ") (map Int.toString init_state)) ^ "\n") ^
         ("Goals:\n " ^ ((String.concatWith "\n ") (map sasAssToString goal)) ^ "\n") ^
         ("Operators:\n " ^ ((String.concatWith "\n ") (map operatorToString operators)) ^ "\n")

fun planToString (plan: string list) =
      ("Plan:\n " ^ ((String.concatWith "\n ") plan) ^ "\n")

type PLAN = string list


val IsabelleStringImplode = exported.implode;
val IsabelleStringExplode = exported.explode;

fun planToIsabellePlan plan = map IsabelleStringExplode plan

fun variableToIsabelleVariable
              (variable_name: string,
                 (axiom_layer: int,
                   atom_names: string list)) =
       (IsabelleStringExplode variable_name,
        (exported.nat_opt_of_integer(IntInf.fromInt axiom_layer),
         map IsabelleStringExplode atom_names))

fun sasAssToIsabelleSasAss (varID, ass) =
        (exported.nat_of_integer (IntInf.fromInt varID),
         exported.nat_of_integer (IntInf.fromInt ass))

fun effectToIsabelleEffect
      (effect_preconds: SAS_ASS list,
       (var_ID: int,
        (old_ass: int,
         (new_ass)))) =
     (map sasAssToIsabelleSasAss effect_preconds,
      (exported.nat_of_integer (IntInf.fromInt var_ID),
       (exported.nat_opt_of_integer (IntInf.fromInt old_ass),
        exported.nat_of_integer (IntInf.fromInt new_ass))))

fun operatorToIsabelleOperator
                (operator_name: string,
                   (preconds: SAS_ASS list,
                     (effects: EFFECT list,
                      (cost: int)))) =
  (IsabelleStringExplode operator_name,
   (map sasAssToIsabelleSasAss preconds,
    (map effectToIsabelleEffect effects,
     exported.nat_of_integer (IntInf.fromInt cost))))

fun problemToIsabelleProblem
          (version_res:int,
             (metric_res:int,
               (variables: SAS_VAR list,
                 (mutex_groups: MUTEX_GRP list,
                  (init_state: int list,
                    (goal: SAS_ASS list,
                      (operators: OPRTR list,
                       num_axioms: int))))))) =
(map variableToIsabelleVariable variables,
 (map (exported.nat_of_integer o IntInf.fromInt) init_state,
  (map sasAssToIsabelleSasAss goal,
   (map operatorToIsabelleOperator operators))))
