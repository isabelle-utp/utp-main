(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: uexpr_ust.ML                                                         *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 14 Feb 2017 *)

(* Expression Utilities *)

signature EXPR_UTILS =
sig
  val mk_varT : typ -> typ
  val mk_exprT : typ -> typ
  val mk_lit_expr : typ -> term
  val mk_var_expr : typ -> term
  val mk_avar_expr : typ -> term
  val mk_uop_expr : typ -> typ -> term
  val mk_bop_expr : typ -> typ -> typ -> term
  val mk_trop_expr : typ -> typ -> typ -> typ -> term
  val mk_binder_expr : typ -> typ -> typ -> term
end;

structure Expr_Utils : EXPR_UTILS =
struct
  open List_Utils;

  fun mk_varT  typ = Type (@{type_name var}, [typ]);
  fun mk_exprT typ = Type (@{type_name expr}, [typ, dummyT]);

  fun mk_lift_functorT src_typs = let
    val dst_typs = (map mk_exprT src_typs) in
      (Library.foldr (op -->) (front src_typs, List.last src_typs)) -->
      (Library.foldr (op -->) (front dst_typs, List.last dst_typs))
    end;

  fun mk_lit_expr typ =
    (Const (@{const_name "lit_expr"}, typ --> (mk_exprT typ)));

  fun mk_var_expr typ =
    (Const (@{const_name "var_expr"}, (mk_varT typ) --> (mk_exprT typ)));

  fun mk_avar_expr typ =
    (Const (@{const_name "avar_expr"}, (mk_varT typ) --> (mk_exprT typ)));

  fun mk_uop_expr t1 t2 =
    (Const (@{const_name "uop_expr"}, mk_lift_functorT [t1, t2]));

  fun mk_bop_expr t1 t2 t3 =
    (Const (@{const_name "bop_expr"}, mk_lift_functorT [t1, t2, t3]));

  fun mk_trop_expr t1 t2 t3 t4 =
    (Const (@{const_name "trop_expr"}, mk_lift_functorT [t1, t2, t3, t4]));

  fun mk_binder_expr t1 t2 t3  =
    (Const (@{const_name "binder_expr"},
      ((t1 --> t2) --> t3) -->
      ((mk_exprT t1 --> mk_exprT t2) --> mk_exprT t3)));
end;

(* Expression Parser *)

signature EXPR_PARSER =
sig
  val already_parsed : term -> bool
  val uparse_tr : Proof.context -> term list -> term list
end;

structure Expr_Parser : EXPR_PARSER =
struct
  fun is_uparse_app (Const (@{const_name uparse}, _) $ _) = true
    | is_uparse_app _ = false;

  fun already_parsed term =
    (if (is_uparse_app term) then false
     else
      (case term of t1 $ t2 =>
        (already_parsed t1) andalso
        (already_parsed t2)
      | Abs (_, _, body) =>
        (already_parsed body)
      | _ => true));

  fun rewrite_into_expr ctx bvs term debruijn =
    (case term of Free (name, typ) =>
      (* Free variables are lifted into axiomatic variable lenses. *)
      (if (Inject_Type.is_injectable ctx typ) then
        (* (Expr_Utils.mk_var_expr typ) $ ... (previous version) *)
        (Expr_Utils.mk_avar_expr typ) $ (Var_Utils.mk_MkPVar ctx name typ)
      else error("Type " ^ (Syntax.string_of_typ ctx typ) ^ " of variable " ^
        (Syntax.string_of_term ctx term) ^ " is not injectable."))
    (* Lifting protected terms simply removes the uprotect tag. *)
    | Const (@{const_name uprotect}, _) $ term => term
    (* Binder lifting must come first as they matches unary operators! *)
    | Const (_, Type ("fun", [Type ("fun", [t1, t2]), t3])) =>
        (Expr_Utils.mk_binder_expr t1 t2 t3) $ term
    (* Operator lifting only supports operators up to a fixed arity. *)
    | Const (_, typ as Type ("fun", _)) =>
      (* TODO: Check that there  are no nested function types. *)
      (case (Type_Utils.unravel_funT typ) of
            [t1, t2]         => (Expr_Utils.mk_uop_expr t1 t2)        $ term
          | [t1, t2, t3]     => (Expr_Utils.mk_bop_expr t1 t2 t3)     $ term
          | [t1, t2, t3, t4] => (Expr_Utils.mk_trop_expr t1 t2 t3 t4) $ term
          (* Further cases can be added here to support higher arities. *)
          | _ => error("Cannot lift operators with more than three arguments."))
    (* Literal-value lifting. *)
    | Const (_, typ) => (Expr_Utils.mk_lit_expr typ) $ term
    | Bound i =>
    (* Inner bound variables are left untouched while outer bound ones are
       wrapped into literals. We note that the types of inner bound variables
       are already automatically changed by the rule for abstractions below. *)
      (if i < debruijn then term else
        (Expr_Utils.mk_lit_expr (snd (nth bvs i)) $ term))
    (* Lifting proceeds recursively through function applications. *)
    | term1 $ term2 =>
      (rewrite_into_expr ctx bvs term1 debruijn) $
      (rewrite_into_expr ctx bvs term2 debruijn)
    | Abs (v, typ, term) =>
    (* We change (lift) the type of the bound variable of the abstraction;
       this is necessary to support lambda-expressions in lifted HOL terms. *)
      Abs (v, Expr_Utils.mk_exprT typ,
        (rewrite_into_expr ctx ((v, typ) :: bvs) term (debruijn + 1)))
    (* TODO: Are there any more cases that need to be considered? *)
    | term => error("Error parsing " ^ (Syntax.string_of_term ctx term)));

  fun uparse_app_tr ctx bvs (Const (@{const_name uparse}, _) $ e) =
      (rewrite_into_expr ctx bvs e 0)
    | uparse_app_tr _ _ _ = raise Match;

  fun uparse_tr ctx terms =
    (* We need the test below in order to avoid an infinite loop. *)
    if exists (not o already_parsed) terms then
      (* Rechecking is necessary to fully determine sigma types. *)
      (Syntax.check_terms ctx
        (map (Term_Utils.map_top_down_bvs (uparse_app_tr ctx) []) terms))
    else terms;
end;

(* Expression Cartouche *)

signature EXPR_CARTOUCHE =
sig
  val uexpr_cartouche : Proof.context -> string -> term
  val uexpr_cartouche_tr : Proof.context -> term list -> term
end;

structure Expr_Cartouche : EXPR_CARTOUCHE =
struct
  fun uexpr_cartouche ctx content =
    (Syntax.read_term ctx ("(" ^ content ^ ")\<^sub>u"));

  val extract_content =
    (Symbol_Pos.content o Symbol_Pos.cartouche_content o Symbol_Pos.explode);

  fun uexpr_cartouche_tr ctx args =
    (case args of
      [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
        (case (Term_Position.decode_position p) of
          SOME (pos, _) =>
            (c $ (uexpr_cartouche ctx (extract_content (s, pos))) $ p)
        | NONE => raise TERM ("uexpr_cartouche_tr", args))
    | _ => raise TERM ("uexpr_cartouche_tr", args));
end;

(***********************)
(* REVIEWED UNTIL HERE *)
(***********************)

(* Automatic Typing *)

(* TODO: Wrap lenses and expressions into special tags to suppress lifting. *)

signature UVAR_TYPING =
sig
  val is_uprotect : term -> bool
  val mk_uvar_type_synonym : string -> string -> local_theory -> local_theory
  val read_type_synonym : theory -> xstring -> typ
  val add_constraints_free_var : Proof.context -> term -> term
  val uvar_implicit_typing_tr : Proof.context -> term list -> term
end;

structure UVAR_Typing : UVAR_TYPING =
struct
  fun is_uprotect (Const (@{const_syntax uprotect}, _) $ _) = true
    | is_uprotect _ = false;

  fun mk_uvar_type_synonym uvar_name typ_name lthy =
    let val typ = Syntax.parse_typ (Local_Theory.target_of lthy) typ_name
    val tfrees = (Type_Utils.get_tfree_namesT typ) in
      (snd o (Typedecl.abbrev_cmd
        (Binding.name (uvar_name ^ "_t"), tfrees, NoSyn) typ_name)) lthy
    end;

  fun read_type_synonym thy typ_name =
    let val full_name = Sign.intern_type thy typ_name;
    val decl = Type.the_decl (Sign.tsig_of thy) (full_name, Position.none) in
      (case decl of Type.Abbreviation (_, typ, false) => typ
      | _ =>  error ("Not a type abbreviation: \"" ^ full_name ^ "\""))
    end;

  fun refine_free_var_type ctx name =
    let val thy = Proof_Context.theory_of ctx;
    val (base_name, _, _) = Name_Parser.dest_name name
    (* We first try and obtain a declared type for the variable name... *)
    val typ = (read_type_synonym thy (base_name ^ "_t")) in
      (* FIXME: How may the user specify additional sort constraints? *)
      (Type_Utils.change_sort_of_free_types @{sort injectable} typ)
    end handle ERROR _ => (* If that fails make it injectable at least! *)
      @{typ "_::injectable"};

  fun gen_dest_free_ast (whole as Const ("_constrain", _) $ term $ typ) =
    (* Are we dealing with a variable with no type constraint? (Same AST). *)
    (if (Syntax_Utils.is_free_ast whole) then (whole, NONE) else
    (* Otherwise assume the whole constitutes an explicit type constraint. *)
    (if (Syntax_Utils.is_free_ast term) then (term, SOME typ) else
    (raise Match)))
  | gen_dest_free_ast _ = raise Match;

  fun add_constraints_free_var ctx term =
    let val (var, typ_opt) = gen_dest_free_ast term in
      (case typ_opt of NONE =>
        (* Free variable with no type constraint. *)
        (Const ("_constrain", dummyT) $ var $
          (Syntax_Phases.term_of_typ ctx
            (refine_free_var_type ctx (Syntax_Utils.dest_free_ast var))))
      | SOME typ =>
        (* Free variable with a type constraint. *)
        (if (Syntax_Utils.is_tfree_ast typ) then
          (* The constraining type is free too. *)
          (Const ("_constrain", dummyT) $ var $
            (Const ("_ofsort", dummyT) $ typ $
              Const (@{class_syntax injectable}, dummyT)))
         else
          (* Otherwise leave the variable term untouched. *)
          term))
    end;

  fun uvar_implicit_typing_tr ctx [term] =
    (Const (@{const_syntax uparse}, dummyT) $
      (Term_Utils.map_top_down_grd
        (add_constraints_free_var ctx) (not o is_uprotect) term))
    | uvar_implicit_typing_tr _ _ = raise Match;
end;