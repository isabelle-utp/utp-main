(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_parser_utils.thy                                                 *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Parser Utilities *}

theory utp_parser_utils
imports "../utp_common"
begin

text {* We create two useful translation functions. _id_string converts between an Isabelle id
        and a string carrying the id name. _utp_alpha returns a global identifier which we
        use to carry the contextual alphabet. Both are implemented using ML-based syntax
        translations. *}

syntax
  "_id_string"  :: "id \<Rightarrow> string" ("IDSTR'(_')")
  "_utp_alpha"  :: "logic" ("ALPHA")

ML {* 
signature UTP_PARSER_UTILS =
sig
  val mk_nib : int -> Ast.ast
  val mk_char : string -> Ast.ast
  val mk_string : string list -> Ast.ast
  val string_ast_tr : Ast.ast list -> Ast.ast
  val GLOBAL_ALPHA_VAR : string
end;

structure Utp_Parser_Utils : UTP_PARSER_UTILS =
struct

val mk_nib =
  Ast.Constant o Lexicon.mark_const o
    fst o Term.dest_Const o HOLogic.mk_nibble;

fun mk_char s =
  if Symbol.is_ascii s then
    Ast.Appl [Ast.Constant @{const_syntax Char}, mk_nib (ord s div 16), mk_nib (ord s mod 16)]
  else error ("Non-ASCII symbol: " ^ quote s);

fun mk_string [] = Ast.Constant @{const_syntax Nil}
  | mk_string (c :: cs) =
      Ast.Appl [Ast.Constant @{const_syntax List.Cons}, mk_char c, mk_string cs];

fun string_ast_tr [Ast.Variable str] =
      (case Lexicon.explode_str str of
        [] =>
          Ast.Appl
            [Ast.Constant @{syntax_const "_constrain"},
              Ast.Constant @{const_syntax List.Nil}, Ast.Constant @{type_syntax string}]
      | cs => mk_string cs)
  | string_ast_tr [Ast.Appl [Ast.Constant @{syntax_const "_constrain"}, ast1, ast2]] =
      Ast.Appl [Ast.Constant @{syntax_const "_constrain"}, string_ast_tr [ast1], ast2]
  | string_ast_tr asts = raise Ast.AST ("string_tr", asts);

val GLOBAL_ALPHA_VAR = "GLOB\<alpha>";

end
*} 

parse_translation {*
let 
  fun id_string_tr [Free (full_name, _)] = HOLogic.mk_string full_name
    | id_string_tr [Const (full_name, _)] = HOLogic.mk_string full_name
    | id_string_tr _ = raise Match;
  fun utp_alpha_tr [] = Syntax.free Utp_Parser_Utils.GLOBAL_ALPHA_VAR
    | utp_alpha_tr _ = raise Match;
in
  [(@{syntax_const "_id_string"}, K id_string_tr),
   (@{syntax_const "_utp_alpha"}, K utp_alpha_tr)]
end
*}

term "IDSTR(x)"
term "ALPHA"

end
