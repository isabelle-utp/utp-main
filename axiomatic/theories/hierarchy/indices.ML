(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: indices.ML                                                           *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 17 Jan 2016 *)

(* Type Index Utilities *)

signature IDX_UTILS =
sig
  val mk_r0 : unit -> typ
  val mk_rS : typ -> typ
  val mk_rT : typ option -> int -> typ
  val dest_rT : typ -> int -> int * typ
end;

structure Idx_Utils : IDX_UTILS =
struct
  fun mk_r0 ()  = @{typ r0};
  fun mk_rS typ = Type (@{type_name rS}, [typ]);

  fun mk_rT (SOME typ) 0 = typ
  | mk_rT   (NONE)     0 = mk_r0()
  | mk_rT typ n = mk_rS (mk_rT typ (n - 1));

  fun dest_rT @{typ r0} n = (n, mk_r0())
  | dest_rT (typ as (TFree _)) n = (n, typ)
  | dest_rT (Type (@{type_name rS}, [typ])) n =
    dest_rT typ (n + 1)
  | dest_rT _ _ = raise Match;
end;

(* Type Index Parser *)

signature IDX_PARSER =
sig
  val dest_num_const : term -> int
  val strip_constraint : term -> term
  val open_idx_tr : Proof.context -> term list -> term
  val close_idx_tr : Proof.context -> term list -> term
end;

structure Idx_Parser : IDX_PARSER =
struct
  open Idx_Utils;

  fun dest_num_const (Const (num, _)) =
    (* Is there any way in which the following conversion may fail? *)
    Option.valOf (Int.fromString num)
  | dest_num_const _ = raise Match;

  fun strip_constraint
    (Const (@{syntax_const "_constrain"}, _) $ t $ _) = t
  | strip_constraint t = t;

  fun change_sorts sorts (TFree (x, _)) = TFree (x, sorts)
  | change_sorts sorts (TVar (xi, _)) = TVar (xi, sorts)
  | change_sorts sorts (Type (t, ts)) =
    Type (t, (map (change_sorts sorts) ts));

  fun open_idx_tr ctx [num, typ_tm] =
    let val n = dest_num_const (strip_constraint num);
    val typ = (Syntax_Phases.decode_typ typ_tm);
    val typ' = (change_sorts [@{class index}] typ) in
      Syntax_Phases.term_of_typ ctx (mk_rT (SOME typ') n)
    end
  | open_idx_tr _ _ = raise Match;

  fun close_idx_tr ctx [num] =
    let val n = dest_num_const (strip_constraint num) in
      Syntax_Phases.term_of_typ ctx (mk_rT NONE n)
    end
  | close_idx_tr _ _ = raise Match;
end;

(* Type Index Printer *)

signature IDX_PRINTER =
sig
  val r0_tr' : Proof.context -> term list -> term
  val rS_tr' : Proof.context -> term list -> term
end;

structure Idx_Printer : IDX_PRINTER =
struct
  open Idx_Utils;

  fun r0_tr' _ [] =
    Const (@{syntax_const "_closed_idxn"}, Term.dummyT) $
    Const ("0", Term.dummyT)
  | r0_tr' _ _ = raise Match;

  fun rS_tr' ctx [typ_tm] =
    let val typ = Syntax_Phases.decode_typ typ_tm;
    val (n, ext_typ) = (dest_rT typ 1) in
      case ext_typ of
        @{typ r0} =>
          Const (@{syntax_const "_closed_idxn"}, Term.dummyT) $
          Const (Int.toString n, Term.dummyT) |
        @{typ unit} =>
          Const (@{syntax_const "_closed_idxn"}, Term.dummyT) $
          Const (Int.toString n, Term.dummyT) |
        _ =>
          Const (@{syntax_const "_open_idxn"}, Term.dummyT) $
          Const (Int.toString n, Term.dummyT) $
          (Syntax_Phases.term_of_typ ctx ext_typ)
    end
  | rS_tr' _ _ = raise Match;
end;