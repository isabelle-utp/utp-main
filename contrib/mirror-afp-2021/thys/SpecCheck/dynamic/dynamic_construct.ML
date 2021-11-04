(*  Title:      SpecCheck/dynamic/dynamic_construct.ML
    Author:     Lukas Bulwahn and Nicolai Schaffroth, TU Muenchen

Dynamic construction of generators and show functions (returned as strings that need to be compiled)
from a given string representing ML code to be tested as a SpecCheck test.
*)

signature SPECCHECK_DYNAMIC_CONSTRUCT =
sig
  val register : string * (string * string) -> theory -> theory
  type mltype
  val parse_pred : string -> string * mltype
  val build_check : Proof.context -> string -> mltype * string -> string
  (*val safe_check : string -> mltype * string -> string*)
  val string_of_bool : bool -> string
  val string_of_ref : ('a -> string) -> 'a Unsynchronized.ref -> string
end;

structure SpecCheck_Dynamic_Construct : SPECCHECK_DYNAMIC_CONSTRUCT =
struct

(* Parsing ML types *)

datatype mltype = Var | Con of string * mltype list | Tuple of mltype list;

(*Split string into tokens for parsing*)
fun split s =
  let
    fun split_symbol #"(" = "( "
      | split_symbol #")" = " )"
      | split_symbol #"," = " ,"
      | split_symbol #":" = " :"
      | split_symbol c = Char.toString c
    fun is_space c = c = #" "
  in String.tokens is_space (String.translate split_symbol s) end;

(*Accept anything that is not a recognized symbol*)
val scan_name = Scan.one (fn s => not (String.isSubstring s "(),*->;"));

(*Turn a type list into a nested Con*)
fun make_con [] = raise Empty
  | make_con [c] = c
  | make_con (Con (s, _) :: cl) = Con (s, [make_con cl]);

(*Parse a type*)
fun parse_type s = (parse_fun || parse_tuple || parse_type_single) s

and parse_type_arg s = (parse_tuple || parse_type_single) s

and parse_type_single s = (parse_con || parse_type_basic) s

and parse_type_basic s = (parse_var || $$ "(" |-- parse_type --| $$ ")") s

and parse_list s =
  ($$ "(" |-- parse_type -- Scan.repeat1 ($$ "," |-- parse_type) --| $$ ")" >> op::) s

and parse_var s = (Scan.one (String.isPrefix "'") >> (fn _ => Var)) s

and parse_con s = ((parse_con_nest
  || parse_type_basic -- parse_con_nest >> (fn (b, Con (t, _) :: tl) => Con (t, [b]) :: tl)
  || parse_list -- parse_con_nest >> (fn (l, Con (t, _) :: tl) => Con (t, l) :: tl))
  >> (make_con o rev)) s

and parse_con_nest s = Scan.unless parse_var (Scan.repeat1 (scan_name >> (fn t => Con (t, [])))) s

and parse_fun s = (parse_type_arg -- $$ "->" -- parse_type >> (fn ((a, f), r) => Con (f, [a, r]))) s

and parse_tuple s = (parse_type_single -- Scan.repeat1 ($$ "*" |-- parse_type_single)
  >> (fn (t, tl) => Tuple (t :: tl))) s;

(*Parse entire type + name*)
fun parse_function s =
  let
    val p = $$ "val" |-- scan_name --| ($$ "=" -- $$ "fn" -- $$ ":")
    val (name, ty) = p (split s)
    val stop = Scan.stopper (fn _ => ";") (fn s => s = ";");
    val (typ, _) = Scan.finite stop parse_type ty
  in (name, typ) end;

(*Create desired output*)
fun parse_pred s =
  let
    val (name, Con ("->", t :: _)) = parse_function s
  in (name, t) end;

(* Construct Generators and Pretty Printers *)

(*copied from smt_config.ML *)
fun string_of_bool b = if b then "true" else "false"

fun string_of_ref f r = f (!r) ^ " ref";

val initial_content = Symtab.make [
  ("bool", ("SpecCheck_Generator.bernoulli 0.5", "Gen_Construction.string_of_bool")),
  ("option", ("SpecCheck_Generator.option (SpecCheck_Generator.bernoulli (2.0 / 3.0))",
              "ML_Syntax.print_option")),
  ("list", ("SpecCheck_Generator.unfold_while (K (SpecCheck_Generator.bernoulli (2.0 / 3.0)))",
            " ML_Syntax.print_list")),
  ("unit", ("gen_unit", "fn () => \"()\"")),
  ("int", ("SpecCheck_Generator.range_int (~2147483647,2147483647)", "string_of_int")),
  ("real", ("SpecCheck_Generator.real", "string_of_real")),
  ("char", ("SpecCheck_Generator.char", "fn c => \"#'\" ^ (Char.toString c) ^ \"'\"")),
  ("string", ("SpecCheck_Generator.string (SpecCheck_Generator.nonneg 100) SpecCheck_Generator.char",
              "ML_Syntax.print_string")),
  ("->", ("SpecCheck_Generator.function' o snd", "fn (_, _) => fn _ => \"fn\"")),
  ("typ", ("SpecCheck_Generator.typ'' (SpecCheck_Generator.return 8) (SpecCheck_Generator.nonneg 4) (SpecCheck_Generator.nonneg 4) (1,1,1)",
           "Pretty.string_of o Syntax.pretty_typ (Context.the_local_context ())")),
  ("term", ("SpecCheck_Generator.term_tree (fn h => fn _ => "
            ^ "let val ngen = SpecCheck_Generator.nonneg (Int.max (0, 4-h))\n"
            ^ "    val aterm_gen = SpecCheck_Generator.aterm' (SpecCheck_Generator.return 8) ngen (1,1,1,0)\n"
            ^ "in SpecCheck_Generator.zip aterm_gen ngen end)",
            "Pretty.string_of o Syntax.pretty_term (Context.the_local_context ())"))]

structure Data = Theory_Data
(
  type T = (string * string) Symtab.table
  val empty = initial_content
  val extend = I
  fun merge data : T = Symtab.merge (K true) data
)

fun data_of ctxt tycon =
  (case Symtab.lookup (Data.get (Proof_Context.theory_of ctxt)) tycon of
    SOME data => data
  | NONE => error ("No generator and printer defined for ML type constructor " ^ quote tycon))

val generator_of = fst oo data_of
val printer_of = snd oo data_of

fun register (ty, data) = Data.map (Symtab.update (ty, data))

(*
fun remove_gen ty = gen_table := AList.delete (op =) ty (!gen_table);
*)

fun combine dict [] = dict
  | combine dict dicts = enclose "(" ")" dict ^ " " ^ enclose "(" ")" (commas dicts)

fun compose_generator _ Var = "SpecCheck_Generator.range_int (~2147483647, 2147483647)"
  | compose_generator ctxt (Con (s, types)) =
      combine (generator_of ctxt s) (map (compose_generator ctxt) types)
  | compose_generator ctxt (Tuple t) =
      let
        fun tuple_body t = space_implode ""
          (map
            (fn (ty, n) => implode ["val (x", string_of_int n, ", r", string_of_int n, ") = ",
              compose_generator ctxt ty, " r", string_of_int (n - 1), " "])
            (t ~~ (1 upto (length t))))
        fun tuple_ret a = commas (map (fn n => "x" ^ string_of_int n) (1 upto a))
      in
        "fn r0 => let " ^ tuple_body t ^
        "in ((" ^ tuple_ret (length t) ^ "), r" ^ string_of_int (length t) ^ ") end"
      end

fun compose_printer _ Var = "Int.toString"
  | compose_printer ctxt (Con (s, types)) =
      combine (printer_of ctxt s) (map (compose_printer ctxt) types)
  | compose_printer ctxt (Tuple t) =
      let
        fun tuple_head a = commas (map (fn n => "x" ^ string_of_int n) (1 upto a))
        fun tuple_body t = space_implode " ^ \", \" ^ "
          (map (fn (ty, n) => "(" ^ compose_printer ctxt ty ^ ") x" ^ string_of_int n)
          (t ~~ (1 upto (length t))))
      in implode ["fn (", tuple_head (length t), ") => \"(\" ^ ", tuple_body t, " ^ \")\""] end

(*produce compilable string*)
fun build_check ctxt name (ty, spec) = implode ["SpecCheck.check (Pretty.str o (",
  compose_printer ctxt ty, ")) (", compose_generator ctxt ty, ")  \"", name,
  "\" (SpecCheck_Property.prop (", spec,
  ")) (Context.the_local_context ()) (SpecCheck_Random.new ());"]

(*produce compilable string - non-eqtype functions*)
(*
fun safe_check name (ty, spec) =
  let
    val default =
      (case AList.lookup (op =) (!gen_table) "->" of
        NONE => ("gen_function_rand", "fn (_, _) => fn _ => \"fn\"")
      | SOME entry => entry)
  in
   (gen_table :=
     AList.update (op =) ("->", ("gen_function_safe", "fn (_, _) => fn _ => \"fn\"")) (!gen_table);
    build_check name (ty, spec) before
    gen_table := AList.update (op =) ("->", default) (!gen_table))
  end;
*)

end;
