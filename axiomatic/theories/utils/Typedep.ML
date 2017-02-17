(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: Typedep.ML                                                           *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 16 Jan 2016 *)

(* Typedef Interpretation *)

signature TYPEDEP =
sig
  val mk_typedepT : typ -> typ
  val mk_typedep : typ -> term
  val simplify_typedep_def : Proof.context -> thm -> thm
  val inst_typedep : string -> theory -> theory
  val ensure_typedep : string -> theory -> theory
end;

structure Typedep : TYPEDEP =
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

  fun change_sort sort (TFree (x, _)) = TFree (x, [sort] (* :: sorts *))
  | change_sort sort (TVar (xi, _)) = TVar (xi, [sort] (* :: sorts *))
  | change_sort sort (Type (t, ts)) = Type (t, (map (change_sort sort) ts));

  fun mk_typedepT typ = (Term.itselfT typ) --> @{typ "typerep set"};

  fun mk_typedep typ =
    Const (@{const_name "typedep"}, mk_typedepT typ) $ (Logic.mk_type typ);

  fun simplify_typedep_def ctx =
    let val ctx' = Simplifier.addsimps (ctx,
      (typedep.get ctx) @ @{thms insert_dup_simps union_dup_simps});
    in
      (* (remove_duplicates_rule ctx) o *) (Simplifier.simplify ctx')
    end;

  local
    val typedep_attr = (Binding.empty, @{attributes [typedep]});
  in
    fun inst_typedep tyco thy =
      let val ctx = Proof_Context.init_global thy;
      val abs_typ = get_abs_type ctx tyco;
      val abs_typ' = change_sort @{class typedep} abs_typ;
      val vs = (map dest_TFree (snd (dest_Type abs_typ')));
      val lhs = Const (@{const_name typedep}, mk_typedepT abs_typ') $
        Free ("t", Term.itselfT abs_typ');
      val rep_typ = get_rep_type (Proof_Context.init_global thy) tyco;
      val rhs = mk_typedep (change_sort @{class typedep} rep_typ);
      val def_eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
      in (thy (* Perform instantiation of class typedep. *)
        |> Class.instantiation ([tyco], vs, @{sort typedep})
        |> `(fn lthy => Syntax.check_term lthy def_eq)
        |-> (fn def_eq =>
          Specification.definition NONE [] [] (Binding.empty_atts, def_eq))
        |> (fn ((_, (_, thm)), lthy) => (* Tag defn with typedep attribute. *)
          snd (Local_Theory.note (typedep_attr,
            [simplify_typedep_def (Local_Theory.target_of lthy) thm]) lthy))
        (* Discharge instantiation proof; note there are no assumptions. *)
        |> Class.prove_instantiation_exit
          (fn ctx => Class.intro_classes_tac ctx []))
      end;
  end;

  fun ensure_typedep tyco thy =
    if not (Sorts.has_instance (Sign.classes_of thy) tyco @{sort typedep})
      andalso Sorts.has_instance (Sign.classes_of thy) tyco @{sort type}
    then inst_typedep tyco thy else thy;
end;