signature CML_PARSER =
sig
  val mk_nibble : int -> Ast.ast
  val mk_char : string -> Ast.ast
  val mk_string : string -> Ast.ast
  val cml_var_ast_tr : Ast.ast list -> Ast.ast
  val cml_dcl_ast_tr : Ast.ast list -> Ast.ast
  val cml_op_dcl_ast_tr : Ast.ast list -> Ast.ast
end;

structure Cml_Parser : CML_PARSER =
struct

  val mk_nibble =
    Ast.Constant o Lexicon.mark_const o
      fst o Term.dest_Const o HOLogic.mk_nibble;

  fun mk_char s =
    if Symbol.is_ascii s then
      Ast.Appl [Ast.Constant @{const_syntax Char},
        mk_nibble (ord s div 16),
        mk_nibble (ord s mod 16)]
    else error ("Non-ASCII symbol: " ^ quote s);

  local
    fun mk_string_aux [] =
      Ast.Appl [Ast.Constant @{syntax_const "_constrain"},
      Ast.Constant @{const_syntax List.Nil},
        Ast.Constant @{type_syntax string}]
    | mk_string_aux (c :: cs) =
      Ast.Appl [Ast.Constant @{const_syntax List.Cons}, mk_char c, mk_string_aux cs];
    in
  fun mk_string s =
    mk_string_aux (map String.str (String.explode s));
  end;

  fun cml_var_ast_tr [Ast.Variable full_name, cml_type] =
        Ast.Appl [Ast.Constant @{const_syntax MkVarD},
          mk_string full_name,
          cml_type]
  | cml_var_ast_tr _ = raise Match;


  fun cml_dcl_ast_tr [cml_var, cml_type, cml_pred] =
    Ast.Appl [Ast.Constant @{const_syntax DclD},
              cml_var_ast_tr [cml_var, cml_type],
              Ast.Appl [Ast.Constant @{syntax_const "_abs"},
                        cml_var,
                        cml_pred]
             ]
  | cml_dcl_ast_tr _ = raise Match;

  fun cml_op_dcl_ast_tr [cml_var, cml_type, cml_op] =
    Ast.Appl [Ast.Constant @{const_syntax DclO},
              cml_var_ast_tr [cml_var, cml_type],
              Ast.Appl [Ast.Constant @{syntax_const "_abs"},
                        cml_var,
                        cml_op]
             ]
  | cml_op_dcl_ast_tr _ = raise Match;


end;
