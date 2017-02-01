(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: uexpr.ML                                                             *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 27 Jan 2017 *)

(* Expression Utilities *)

signature EXPR_UTILS =
sig
  val mk_varT : typ -> typ
  val mk_uexprT : typ -> typ
  val mk_lit_uexpr : typ -> term
  val mk_var_uexpr : typ -> term
  val mk_uop_uexpr : typ -> typ -> term
  val mk_bop_uexpr : typ -> typ -> typ -> term
  val mk_trop_uexpr : typ -> typ -> typ -> typ -> term
  val mk_binder_uexpr : typ -> typ -> typ -> term
end;

structure Expr_Utils : EXPR_UTILS =
struct
  open List_Utils;

  fun mk_varT   typ = Type (@{type_name var}, [typ]);
  fun mk_uexprT typ = Type (@{type_name uexpr}, [typ]);

  fun mk_lift_functorT src_typs = let
    val dst_typs = (map mk_uexprT src_typs) in
      (Library.foldr (op -->) (front src_typs, List.last src_typs)) -->
      (Library.foldr (op -->) (front dst_typs, List.last dst_typs))
    end;

  fun mk_lit_uexpr typ =
    (Const (@{const_name "lit_uexpr"}, typ --> (mk_uexprT typ)));

  fun mk_var_uexpr typ =
    (Const (@{const_name "var_uexpr"}, (mk_varT typ) --> (mk_uexprT typ)));

  fun mk_uop_uexpr t1 t2 =
    (Const (@{const_name "uop_uexpr"}, mk_lift_functorT [t1, t2]));

  fun mk_bop_uexpr t1 t2 t3 =
    (Const (@{const_name "bop_uexpr"}, mk_lift_functorT [t1, t2, t3]));

  fun mk_trop_uexpr t1 t2 t3 t4 =
    (Const (@{const_name "trop_uexpr"}, mk_lift_functorT [t1, t2, t3, t4]));

  fun mk_binder_uexpr t1 t2 t3  =
    (Const (@{const_name "binder_uexpr"},
      ((t1 --> t2) --> t3) -->
      ((mk_uexprT t1 --> mk_uexprT t2) --> mk_uexprT t3)));
end;

(* Expression Parser *)

signature EXPR_PARSER =
sig
  val is_injectable : Proof.context -> typ -> bool
  val uparse_tr : Proof.context -> term list -> term list
end;

structure Expr_Parser : EXPR_PARSER =
struct
  fun is_injectable ctx typ =
    Sign.of_sort (Proof_Context.theory_of ctx) (typ, @{sort injectable});

  fun uparse_error msg = error("Error parsing (_)\<^sub>u: " ^ msg);

  (* The next function is the heart of the parser and tricky to get right! *)

  fun rewrite_into_uexpr ctx bvs term debruijn =
    (case term of Free (name, typ) => (* Rewriting of free variables. *)
      (if (is_injectable ctx typ) then
        (Expr_Utils.mk_var_uexpr typ) $ (Var_Utils.mk_MkPVar ctx name typ)
      else uparse_error("type " ^
        (Syntax.string_of_typ ctx typ) ^ " of variable " ^
        (Syntax.string_of_term ctx term) ^ " is not injectable."))
    (* Rewriting of protected terms. We simply remove the uprotect tag here. *)
    | Const (@{const_name uprotect}, _) $ term => term
    (* Binder lifting must come first as they matches unary operator types. *)
    | Const (_, Type ("fun", [Type ("fun", [t1, t2]), t3])) =>
        (Expr_Utils.mk_binder_uexpr t1 t2 t3) $ term
    (* Opertor lifting. Check there are no nested function types. [TODO] *)
    | Const (_, typ as Type ("fun", _)) =>
      (case (Term_Utils.unravel_funT typ) of
            [t1, t2]         => (Expr_Utils.mk_uop_uexpr t1 t2)        $ term
          | [t1, t2, t3]     => (Expr_Utils.mk_bop_uexpr t1 t2 t3)     $ term
          | [t1, t2, t3, t4] => (Expr_Utils.mk_trop_uexpr t1 t2 t3 t4) $ term
          | _ => uparse_error(
            "cannot lift operators with more than three arguments."))
    (* Note that HO function lifting is not supported in all its generality.
       Hence, the following might well raise a type error after rewriting. *)
    | Const (_, typ) =>
        (Expr_Utils.mk_lit_uexpr typ) $ term
    | Bound i =>
    (* Inner bound variables are left untouched; and outer ones are wrapped
       into literals. We note that the type of inner variables is already
       changed i.e. from 'a to 'a uexpr by the rewrite rule for Abs below. *)
      (if i < debruijn then term else
        (Expr_Utils.mk_lit_uexpr (snd (nth bvs i)) $ term))
    | term1 $ term2 =>
      (rewrite_into_uexpr ctx bvs term1 debruijn) $
      (rewrite_into_uexpr ctx bvs term2 debruijn)
    | Abs (v, typ, term) =>
    (* We change (lift) the type of the bound variable of the abstraction;
       this necessary to support lambda-expressions in lifted HOL terms. *)
      Abs (v, Expr_Utils.mk_uexprT typ,
        (rewrite_into_uexpr ctx ((v, typ) :: bvs) term (debruijn + 1)))
    (* Are there any more cases that need to be consider? What about Var? *)
    | term => uparse_error("term" ^ (Syntax.string_of_term ctx term)));

  fun uparse_app_tr ctx bvs (Const (@{const_name uparse}, _) $ e) =
      (rewrite_into_uexpr ctx bvs e 0)
    | uparse_app_tr _ _ _ = raise Match;

  fun uparse_tr ctx terms =
    (map (Term_Utils.map_top_down_bvs (uparse_app_tr ctx) []) terms);
end;