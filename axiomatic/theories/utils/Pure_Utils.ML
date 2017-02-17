(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: Pure_Utils.ML                                                        *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 16 Jan 2016 *)

(* List Utilities *)

signature LIST_UTILS =
sig
  val front : 'a list -> 'a list
end;

structure List_Utils : LIST_UTILS =
struct
  fun front (h::(t as (_::_))) = h::(front t)
    | front ([_]) = []
    | front _ = raise Empty;
end;

(* Syntax Utilities *)

signature SYNTAX_UTILS =
sig
  val is_free_ast : term -> bool
  val dest_free_ast : term -> string
  val is_tfree_ast : term -> bool
  val dest_tfree_ast : term -> string
end;

structure Syntax_Utils : SYNTAX_UTILS =
struct
  fun is_free_ast (Const ("_constrain", Type ("dummy", [])) $
    Free (name, Type ("dummy", [])) $ (markup as Free (_ , _))) =
    not (String.isPrefix "'" name) andalso (Term_Position.is_position markup)
  | is_free_ast _ = false;

  fun dest_free_ast (term as Const ("_constrain", Type ("dummy", [])) $
    Free (name, Type ("dummy", [])) $ Free (_ , Type ("dummy", []))) =
    (if (is_free_ast term) then name else raise Match)
  | dest_free_ast _ = raise Match;

  fun is_tfree_ast (Const ("_ofsort", Type ("dummy", [])) $
    Free (name, Type ("dummy", [])) $ (markup as Free (_ , _))) =
    (String.isPrefix "'" name) andalso (Term_Position.is_position markup)
  | is_tfree_ast _ = false;

  fun dest_tfree_ast (term as Const ("_ofsort", Type ("dummy", [])) $
    Free (name, Type ("dummy", [])) $ Free (_ , Type ("dummy", []))) =
    (if (is_tfree_ast term) then name else raise Match)
  | dest_tfree_ast _ = raise Match;
end;

(* Term Utilities *)

signature TERM_UTILS =
sig
  type bvs = (string * typ) list
  val map_top_down : (term -> term) -> term -> term
  val map_top_down_bvs : (bvs -> term -> term) -> bvs -> term -> term
  val map_top_down_grd : (term -> term) -> (term -> bool) -> term -> term
  val inst_const : Proof.context -> string * typ list -> term
  val mk_bool : bool -> term
  val dest_bool : term -> bool
end;

structure Term_Utils : TERM_UTILS =
struct
  type bvs = (string * typ) list

  fun map_top_down f t =
    (f t) handle Match =>
      (case t of (t1 $ t2) =>
        (map_top_down f t1) $
        (map_top_down f t2)
      | Abs (v, typ, t) =>
        Abs (v, typ, map_top_down f t)
      | _ => t);

  fun map_top_down_bvs f bvs term =
    (f bvs term) handle Match =>
      (case term of (term1 $ term2) =>
        (map_top_down_bvs f bvs term1) $
        (map_top_down_bvs f bvs term2)
      | Abs (v, typ, body) =>
        Abs (v, typ, map_top_down_bvs f ((v, typ) :: bvs) body)
      | _ => term);

  fun map_top_down_grd f test t =
    (if (test t) then
      (f t) handle Match =>
        (case t of (t1 $ t2) =>
          (map_top_down_grd f test t1) $
          (map_top_down_grd f test t2)
        | Abs (v, typ, t) =>
          Abs (v, typ, map_top_down_grd f test t)
        | _ => t)
    else t);

  fun inst_const ctx (name, typs) =
  let val (cname, _) = dest_Const
      (Proof_Context.read_const
        {proper = true, strict = true} ctx name);
    val consts = Proof_Context.consts_of ctx;
    val typ = Consts.instance consts (cname, typs);
  in
    Const (cname, typ)
  end;

  fun mk_bool b =
    (if b then @{term True} else @{term False});

  fun dest_bool @{const True} = true
    | dest_bool @{const False} = false
    | dest_bool _ = raise Match;
end;

(* Type Utilities *)

signature TYPE_UTILS =
sig
  val dest_itselfT : typ -> typ
  val unravel_funT : typ -> typ list
  val get_tfree_namesT : typ -> string list
  val change_sort_of_free_types: sort -> typ -> typ
end;

structure Type_Utils : TYPE_UTILS =
struct
  fun dest_itselfT (Type ("itself", [typ])) = typ
    | dest_itselfT typ =
      raise TYPE ("dest_itselfT", [typ], []);

  fun unravel_funT_aux (Type ("fun", [T, U])) = T :: (unravel_funT_aux U)
    | unravel_funT_aux T = [T];

  fun unravel_funT (typ as Type ("fun", _)) = (unravel_funT_aux typ)
    | unravel_funT T = raise TYPE ("unravel_funT", [T], []);

  fun get_tfree_namesT typ =
    rev (Term.add_tfree_namesT typ []);

  fun change_sort_of_free_types sort =
    Term.map_type_tfree (fn (name, _) => TFree (name, sort));
end;

(* Tactic Utilities *)

infix 1 THEN_IF_FEWER

signature TACTIC_UTILS =
sig
  exception UNSOLVABLE
  val THEN_IF_FEWER : tactic * tactic -> tactic
  val check_solvable_tac : tactic
end;

structure Tactic_Utils : TACTIC_UTILS =
struct
  exception UNSOLVABLE;

  fun (tac1 THEN_IF_FEWER tac2) st =
    (tac1 THEN COND (has_fewer_prems (Thm.nprems_of st)) tac2 all_tac) st;

  fun check_solvable_tac st =
    let fun is_False_prop term =
      (term = @{term "Trueprop False"});
    val prems = Thm.prems_of st in
      if (exists is_False_prop prems) then
        raise UNSOLVABLE
      else Seq.single st
    end;
end;

(* Isar Utils *)

signature ISAR_UTILS =
sig
  val full_type_name : theory -> string -> string
end;

structure Isar_Utils : ISAR_UTILS =
struct
  fun full_type_name thy typ =
    let val ctx = Proof_Context.init_global thy in
      (#1 o dest_Type)
        (Proof_Context.read_type_name {proper = true, strict = false} ctx typ)
    end;
end;