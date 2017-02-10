(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: ulift.ML                                                             *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 26 Jan 2017 *)

(* Lifting Parser *)

signature ULIFT_PARSER =
sig
  val is_injectable : Proof.context -> typ -> bool
  val mk_MkPVar : Proof.context -> string -> typ -> term
  val ustate_app_intro : Proof.context -> term -> int -> term
  val ulift_term_tr : Proof.context -> term -> term
  val ulift_tr : Proof.context -> term list -> term list
end;

structure Ulift_Parser : ULIFT_PARSER =
struct
  open Term_Utils;

  fun is_injectable ctx typ =
    Sign.of_sort (Proof_Context.theory_of ctx) (typ, @{sort injectable});

  fun mk_type_of_term ctx term =
    let val typ = type_of term in
      (inst_const ctx (@{const_name type_of_term}, [typ]) $ term)
    end;

  fun mk_MkPVar ctx name typ =
    (inst_const ctx (@{const_name MkPVar}, [typ]))
      $ (Name_Parser.uname_tr [Free (name, typ)])
      $ (mk_type_of_term ctx (Free (name, typ)));

  fun ustate_app_intro ctx term debruijn =
    (case term of Free (name, typ) =>
      if (is_injectable ctx typ) then
        (inst_const ctx (@{const_name ustate_app_poly}, [typ]))
          $ (Bound debruijn) $ (mk_MkPVar ctx name typ)
      else
        error ("Error parsing (_)\<^sub>p: type " ^
          (Syntax.string_of_typ ctx typ) ^ " of variable " ^
          (Syntax.string_of_term ctx term) ^ " is not injectable.")
    (* Do not further process protected terms, just remove the tag. *)
    | Const (@{const_name uprotect}, _) $ term => term
    | Abs (v, typ, t) =>
      Abs (v, typ, ustate_app_intro ctx t (debruijn + 1))
    | t1 $ t2 =>
      (ustate_app_intro ctx t1 debruijn) $
      (ustate_app_intro ctx t2 debruijn)
    (* TODO: Are there more cases to be (usefully) considered? *)
    | _ => term);

  fun ulift_term_tr ctx term =
    (case term of @{const ulift} $ e =>
      (Syntax.check_term ctx (inst_const ctx (@{const_name LiftP}, [])) $
          (* Note that we do not have to worry about capture of b in e. *)
          (Abs ("b", @{typ ustate}, ustate_app_intro ctx e 0)))
    | _ => raise Match);

  fun ulift_tr ctx terms =
    map (map_top_down (ulift_term_tr ctx)) terms;
end;

(* Lifting Printer *)

signature ULIFT_PRINTER =
sig
  val dest_MkName : term -> string
  val MkPVar_to_Free : term -> term
  val ustate_app_elim : Proof.context -> term -> int -> term
  val ulift_term_tr' : Proof.context -> term -> term
  val ulift_tr' : Proof.context -> term list -> term list
end;

structure Ulift_Printer : ULIFT_PRINTER =
struct
  open Term_Utils;
  open Type_Utils;

  fun dest_MkName
    (Const (@{const_abbrev MkName}, _) $ name $ dashes $ subscr) =
      Name_Printer.name_from_terms (name, dashes, subscr)
  | dest_MkName _ = raise Match;

  (* TODO: Isabelle highlights the printed free variables in red. Fix? *)

  fun MkPVar_to_Free
    (Const (@{const_name MkPVar}, _) $ n $ type_of_term) =
      Free (dest_MkName n, dest_itselfT (type_of type_of_term))
  | MkPVar_to_Free _ = raise Match;

  fun ustate_app_elim ctx term debruijn =
    (case term of
      Const (@{const_name ustate_app_poly}, _) $ (Bound n) $ v =>
        (if n = debruijn then (MkPVar_to_Free v) else term)
    | Abs (v, typ, t) =>
      Abs (v, typ, ustate_app_elim ctx t (debruijn + 1))
    | t1 $ t2 =>
      (ustate_app_elim ctx t1 debruijn) $
      (ustate_app_elim ctx t2 debruijn)
    | Bound n =>
      (if n = debruijn then (raise Match) else term)
    | _ => term);

  fun ulift_term_tr' ctx term =
    (case term of @{const LiftP} $
      (Abs (_, @{typ ustate}, e)) =>
        @{const ulift} $ (ustate_app_elim ctx e 0)
    | _ => raise Match);

  fun ulift_tr' ctx terms =
    if not (Config.get ctx disable_ulift_pp) then
      (map (map_top_down (ulift_term_tr' ctx)) terms)
    else terms;
end;

(* Implicit Typing *)

signature ULIFT_TYPING =
sig
  val mk_uvar_type_synonym : string -> string -> local_theory -> local_theory
  val refine_type : Proof.context -> string -> typ
  val refine_free : Proof.context -> term -> term
  val implicit_typing : Proof.context -> term list -> term
end;

(* The following does not seem to work in Isabelle 2015?! *)

structure Ulift_Typing : ULIFT_TYPING =
struct
  (* TODO: Check that type typ is injectable. *)

  fun mk_uvar_type_synonym uvar typ = snd o
    (Typedecl.abbrev_cmd (Binding.name (uvar ^ "_t"), [], NoSyn) typ)

  fun refine_type ctx name =
    let val (base_name, _, _) = Name_Parser.dest_name name in
      Syntax.read_typ ctx (base_name ^ "_t")
    end (* handle ERROR _ => @{typ "_::injectable"} *);

  fun refine_free ctx term =
    if not (Term_Position.is_position term) then
      (case term of Free (name, _) =>
        (* Since Isabelle 2015, the below throws Par_Exn rather than ERROR. *)
        (Free (name, refine_type ctx name) handle (* ERROR *) _ => term)
      | anything => anything)
    else term;

  fun implicit_typing ctx [term] =
    if (Config.get ctx ulift_typing) then
      @{const ulift} $ (map_aterms (refine_free ctx) term)
    else raise Match
  | implicit_typing _ _ = raise Match;
end;