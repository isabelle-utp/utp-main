(* This is a demo example of a simple grammar for receipts.

   Consider the following EBNF:
     sas_prob ::= version 0
*)
structure LexCNFModel =
(* An implementation that uses token parser. *)
struct

  open ParserCombinators
  open CharParser

  infixr 4 << >>
  infixr 3 &&
  infix  2 -- ##
  infix  2 wth suchthat return guard when
  infixr 1 || <|> ??

  structure CNFModelDef :> LANGUAGE_DEF =
  struct

    type scanner = SubstringMonoStreamable.elem CharParser.charParser

    val commentStart   = NONE
    val commentEnd     = NONE
    val commentLine    = NONE
    val nestedComments = false

    val alphaNumUnderDashSpace  = try (satisfy (fn c =>
                                (if (Char.isAlpha c)
                                 then true
                                 else false)) ) ?? "alphanumeric character"

    val identLetter    = alphaNumUnderDashSpace (*Idents can only be separated with \n and can contain [Aa-Zz], [0-9], " ", "-", "_"*)
    val identStart     = identLetter
    val opStart        = fail "Operators not supported" : scanner
    val opLetter       = opStart
    val reservedNames  = []
    val reservedOpNames= []
    val caseSensitive  = true

  end

  structure RTP = TokenParser (CNFModelDef)
  open RTP

  val SMLCharImplode = String.implode;
  val SMLCharExplode = String.explode;


  val num = (lexeme ((char #"-" || digit) && (repeat digit)) when
	      (fn (x,xs) => Int.fromString (SMLCharImplode (x::xs)))) ?? "num expression"

  fun model_reserved wrd = (reserved wrd)

  val model_line = (*(model_reserved "v" ?? "v, parsing model_line") <<*)
                   (repeat num ?? "literal, parsing model_line")

  val model = (repeat num ?? "literal, parsing model_line") 
      
end
      

val args = CommandLine.arguments()

fun parse_problem sas_file =
  (CharParser.parseString LexSASProb.problem (readFile sas_file))

val parsed_problem = parse_problem (List.nth (args,0))

val _ = case parsed_problem of Sum.INR _ =>
     (case (Sum.outR parsed_problem) of (prob: SAS_PROB)
                 => print "Problem parsed\n")
     | Sum.INL err => print ("ERR: " ^ err)

fun parse_model model_file =
    (CharParser.parseString LexCNFModel.model (readFile model_file))

val parsed_model = parse_model (List.nth (args,1))

val _ = case parsed_model of Sum.INR _ =>
     (case (Sum.outR parsed_model) of (model)
                 => print "Model Parsed\n")
     | Sum.INL err => print ("ERR: " ^ err)

fun modelToString model = (String.concatWith " " (map IntInf.toString (map IntInf.fromInt model)))

fun modelToIsabelleModel model = (map (exported.int_of_integer o IntInf.fromInt) model)

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

open LexSASProb

val isabelle_plan =
  (case parsed_problem of
     Sum.INR _ =>
       (case (Sum.outR parsed_problem) of (prob: SAS_PROB)
          =>
            (case parsed_model of
               Sum.INR _ =>
                 (case (Sum.outR parsed_model) of (model: int list)
                    => (
                        exported.decode
                          (modelToIsabelleModel model)
                          ((case (IntInf.fromString (List.nth (args,2))) of Option.SOME n => exported.nat_of_integer n))
                          (problemToIsabelleProblem prob)
                       )))))

val _ = case isabelle_plan
          of exported.Inl plan 
            => print ("Plan:\n" ^ (String.concatWith "\n" (map exported.implode plan)) ^ "\n")
          | exported.Inr err
            => print (err ^ "\n")

val _ = OS.Process.exit(OS.Process.success)
