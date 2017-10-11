(******************************************************************************)
(* External Algorithm for Calculating the Transitive Closure in Isabelle/HOL  *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(* Email: frank.zeyda@york.ac.uk                                              *)
(******************************************************************************)

(* PRESIMPLIFIER Signature *)

signature PRESIMPLIFIER  =
sig
  val inst_TRUE : Proof.context -> term -> thm;
  val dest_TRUE : term -> term;
  val dest_TRUE_thm : thm -> term;
  val get_spec_thms : Proof.context -> (term -> bool) -> term -> thm list;
  val presimplify : Proof.context -> (term -> bool) -> term -> term;
end;

(* PreSimplifier Structure *)

structure PreSimplifier : PRESIMPLIFIER =
struct
  (* A robust method to obtain the free variable and type of @{thm TRUE_t}. *)
  val TRUE_var = let
    val vterm = Thm.term_of (hd (Thm.add_vars @{thm TRUE_t} []));
    val (vname, vtyp) = dest_Var vterm;
    val (tname, sort) = dest_TVar vtyp;
  in (vname, tname, sort) end;

  (* Instantiation and destruction of @{term "TRUE t"} terms and theorems. *)
  fun inst_TRUE ctx term = let
    val typ = Term.type_of term;
    val cterm = Thm.cterm_of ctx term;
    val ctyp = Thm.ctyp_of ctx typ;
    val (vname, tname, sort) = TRUE_var;
  in
    Thm.instantiate
      ([((tname, sort), ctyp)], [((vname, typ), cterm)]) @{thm TRUE_t}
  end;

  fun dest_TRUE (Const (@{const_name TRUE}, _) $ arg) = arg
    | dest_TRUE _ = raise Match;

  val dest_TRUE_thm = (dest_TRUE o HOLogic.dest_Trueprop o Thm.prop_of);

  local
    fun extract_spec_thms name (h :: t) =
      (case h of (Spec_Rules.Equational, ([Const (spec, (*typ*)_)], thms)) =>
        (* What about typ? Do we have to check or process it in some way? *)
        (if name = spec then thms else []) | _ => []) @
        (extract_spec_thms name t)
      | extract_spec_thms _ [] = [];
  in
    fun get_spec_thms ctx filter term =
      let
        fun get_spec_thms_aux ctx (term as Const (name, _)) =
          if (filter term) then
            (extract_spec_thms name (Spec_Rules.retrieve ctx term)) else []
        | get_spec_thms_aux ctx (t1 $ t2) =
          let val thm_ord = Term_Ord.fast_term_ord o (apply2 Thm.prop_of) in
            (Ord_List.union thm_ord)
              (get_spec_thms_aux ctx t1)
              (get_spec_thms_aux ctx t2)
          end
        | get_spec_thms_aux ctx (Abs (_, _, t)) = (get_spec_thms_aux ctx t)
        | get_spec_thms_aux _ _ = [];
      in
        (get_spec_thms_aux ctx term)
      end;
  end;

  local
    (* The function below could become a bottle-neck RE efficiency. *)
    fun presimplify_aux ctx filter term =
      let
        val dummy_thm = (inst_TRUE ctx term);
        val spec_thms = (get_spec_thms ctx filter term);
        val simp_rule = (Simplifier.full_simplify ctx) o
          (Local_Defs.unfold ctx spec_thms);
        val new_term = dest_TRUE_thm (simp_rule dummy_thm)
      in
        if new_term = term then term else
          (* While the term is changing, keep simplifying iteratively... *)
          (presimplify_aux ctx filter new_term)
      end;
  in
    fun presimplify ctx filter term =
      (* Perhaps the simpset ought to be tuned further for performance! *)
      let val ctx' = ctx delsimps [@{thm One_nat_def}] in
        (presimplify_aux ctx' filter term)
      end;
  end;
end;