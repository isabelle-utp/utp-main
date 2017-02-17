(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: flat_orders.ML                                                       *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 16 Jan 2016 *)

(* Signature: FLAT_ORDER *)

signature FALT_ORDER =
sig
  val flat_order_tac : Proof.context -> tactic
  val flat_order : xstring -> theory -> theory
end;

(* Structure: Flat_Order *)

structure Flat_Order : FALT_ORDER =
struct
  val simp_attr = @{attributes [simp]};

  fun full_type_name ctx typ = (#1 o dest_Type)
    (Proof_Context.read_type_name {proper = true, strict = false} ctx typ);

  fun mk_less_eq_def typ =
      HOLogic.mk_Trueprop (HOLogic.mk_eq (
        Const (@{const_name "less_eq"}, typ --> typ --> HOLogic.boolT),
        Const (@{const_name "HOL.eq"}, typ --> typ --> HOLogic.boolT)));

  fun mk_less_def typ =
      HOLogic.mk_Trueprop (HOLogic.mk_eq (
        Const (@{const_name "less"}, typ --> typ --> HOLogic.boolT),
        Abs ("uu_", typ, Abs ("uu_", typ, @{term False}))));

  fun flat_order_tac ctx =
    (Class.intro_classes_tac ctx []) THEN ALLGOALS (asm_full_simp_tac ctx);

  fun flat_order typ thy =
    let val tyco = full_type_name (Proof_Context.init_global thy) typ;
      val sorts = replicate (Sign.arity_number thy tyco) @{sort type};
      val vs = Name.invent_names Name.context "'a" sorts;
      val typ_inst = Type (tyco, map TFree vs);
      val less_eq_def = mk_less_eq_def typ_inst;
      val less_def = mk_less_def typ_inst;
    in
      if (Sign.of_sort thy (typ_inst, @{sort ord})) then
        error ("Type \"" ^ typ ^ "\" already instantiates class ord.")
      else (thy
        |> Class.instantiation ([tyco], vs, @{sort "ord"})
        |> Specification.definition NONE [] [] (Binding.empty_atts, less_eq_def)
        |> (fn ((_, (_, thm)), lthy) =>
          snd (Local_Theory.note ((Binding.empty, simp_attr), [thm]) lthy))
        |> Specification.definition  NONE [] [] (Binding.empty_atts, less_def)
        |> (fn ((_, (_, thm)), lthy) =>
          snd (Local_Theory.note ((Binding.empty, simp_attr), [thm]) lthy))
        |> Class.prove_instantiation_exit
          (fn ctx => Class.intro_classes_tac ctx [])
        |> Class.instantiation ([tyco], vs, @{sort "order"})
        |> Class.prove_instantiation_exit (flat_order_tac))
    end;
end;