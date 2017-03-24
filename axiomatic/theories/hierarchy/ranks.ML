(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: ranks.ML                                                             *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 6 January 2017 *)

(* Typedef Interpretation *)

signature RANKS =
sig
  val mk_rankT : typ -> typ
  val mk_rank : typ -> term
  val simplify_rank_def : Proof.context -> thm -> thm
  val inst_rank : string -> theory -> theory
  val ensure_rank : string -> theory -> theory
end;

structure Ranks : RANKS =
struct
  fun get_abs_type ctx tyco =
    let val info = Typedef.get_info ctx tyco in
      if (length info) = 0 then
        raise TYPE ("No type info found for \"" ^ tyco ^ "\"", [], [])
      else (* Can (length info) be greater than 1? *)
        (#abs_type (#1 (nth info 0)))
    end;

  fun get_rep_type ctx tyco =
    let val info = Typedef.get_info ctx tyco in
      if (length info) = 0 then
        raise TYPE ("No type info found for \"" ^ tyco ^ "\"", [], [])
      else (* Can (length info) be greater than 1? *)
        (#rep_type (#1 (nth info 0)))
    end;

  fun replace_sorts sorts (TFree (x, _)) = TFree (x, sorts)
  | replace_sorts sorts (TVar (xi, _)) = TVar (xi, sorts)
  | replace_sorts sorts (Type (t, ts)) =
      Type (t, (map (replace_sorts sorts) ts));

  fun mk_rankT typ = (Term.itselfT typ) --> @{typ "nat"};

  fun mk_rank typ =
    Const (@{const_name "rank"}, mk_rankT typ) $ (Logic.mk_type typ);

  fun simplify_rank_def ctx = Simplifier.simplify
    (Simplifier.addsimps (ctx, (ranks.get ctx) @ @{thms max_cancel_simps}))

  val ranks_attr = (Binding.empty, @{attributes [ranks]});

  fun inst_rank tyco thy =
    let val ctx = Proof_Context.init_global thy;
    val abs_typ = get_abs_type ctx tyco;
    val abs_typ' = replace_sorts @{sort rank} abs_typ;
    val vs = (map dest_TFree (snd (dest_Type abs_typ')));
    val lhs = Const (@{const_name rank}, mk_rankT abs_typ') $
      Free ("t", Term.itselfT abs_typ');
    val rep_typ = get_rep_type (Proof_Context.init_global thy) tyco;
    val rhs = mk_rank (replace_sorts @{sort rank} rep_typ);
    val def_eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
    in (thy (* Perform instantiation of class rank. *)
      |> Class.instantiation ([tyco], vs, @{sort rank})
      |> `(fn lthy => Syntax.check_term lthy def_eq)
      |-> (fn def_eq =>
        Specification.definition NONE [] [] (Binding.empty_atts, def_eq))
      |> (fn ((_, (_, thm)), lthy) => (* Add defn axiom to rank attribute. *)
        snd (Local_Theory.note (ranks_attr,
          [simplify_rank_def (Local_Theory.target_of lthy) thm]) lthy))
      (* Discharge instantiation proof; note there are no assumptions. *)
      |> Class.prove_instantiation_exit
        (fn ctx => Class.intro_classes_tac ctx []))
    end;

  fun ensure_rank tyco thy =
    if not (Sorts.has_instance (Sign.classes_of thy) tyco @{sort rank})
      andalso Sorts.has_instance (Sign.classes_of thy) tyco @{sort type}
    then inst_rank tyco thy else thy;
end;