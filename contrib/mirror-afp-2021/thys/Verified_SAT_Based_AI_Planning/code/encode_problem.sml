(* This is a demo example of a simple grammar for receipts.

   Consider the following EBNF:
     sas_prob ::= version 0
*)

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

type PLAN = string list

val args = CommandLine.arguments()

(**********************************)

(* open SASP_to_DIMACS *)
(* open SASP_Checker_Exported *)

val IsabelleStringImplode = exported.implode;
val IsabelleStringExplode = exported.explode;

(* val _ = (IntInf.fromInt (IntSplayDict (0))) *)

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

val readstdIn =
let
    fun next_String input = (TextIO.inputAll input)
    val stream = TextIO.stdIn
in
    next_String stream
end

val parse_problem = (CharParser.parseString LexSASProb.problem readstdIn)

val CNF_formula =
        (case parse_problem of
             Sum.INR _ =>
              (case (Sum.outR parse_problem) of (prob: SAS_PROB)
                 => (exported.encode
                         (case (IntInf.fromString (List.nth (args,0))) of Option.SOME n => exported.nat_of_integer n)
                         (problemToIsabelleProblem prob))))

fun clause_to_string ls = (concat (map ((fn x => x ^ " ") o
                             IntInf.toString o
                               exported.integer_of_int) ls)) ^
                             " 0\n"

fun max xs = foldl (fn (x : int, y : int) => if (abs x) >= (abs y) then abs x else abs y) 0 xs

fun cnfToString cnf =
  (case cnf of exported.Inl formula 
     =>(let val n_vars = exported.integer_of_int ((exported.max_var (map exported.max_var formula)))
            val n_clauses = length formula
        in
          ("p cnf " ^
           (IntInf.toString n_vars) ^ " " ^
           (Int.toString n_clauses) ^ "\n" ^
           (concat (map clause_to_string formula)))
        end)
    | exported.Inr err => err)

val _ = print (cnfToString CNF_formula)

val _ = OS.Process.exit(OS.Process.success)
