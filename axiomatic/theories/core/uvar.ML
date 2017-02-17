(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: uvar.ML                                                              *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 2 December 2014 *)

(* Var Utilities *)

signature VAR_UTILS =
sig
  val mk_MkPVar : Proof.context -> string -> typ -> term
end;

structure Var_Utils : VAR_UTILS =
struct
  fun mk_type_of_term ctx term =
    let val typ = type_of term in
      (Term_Utils.inst_const ctx
        (@{const_name type_of_term}, [typ]) $ term)
    end;

  fun mk_MkPVar ctx name typ =
    (Term_Utils.inst_const ctx (@{const_name MkPVar}, [typ]))
      $ (Name_Parser.uname_tr [Free (name, typ)])
      $ (mk_type_of_term ctx (Free (name, typ)));
end;

(* Var Rewriter *)

signature VAR_REWRITER =
sig
  val MkPVar_type_of_term_elim : term -> term
  val remove_hidden_vars_tr : Proof.context -> term list -> term list
end;

structure Var_Rewriter : VAR_REWRITER =
struct
  fun MkPVar_type_of_term_elim term =
    (case term of
      (Const (@{const_name MkPVar}, t) $ name $ type_of_term) =>
        (Const (@{const_name MkPVar}, t) $ name $
          Logic.mk_type (Type_Utils.dest_itselfT (type_of type_of_term)))
    | _ => raise Match);

  fun remove_hidden_vars_tr ctx terms =
    if (Config.get ctx remove_hidden_vars) then
      (map (Term_Utils.map_top_down MkPVar_type_of_term_elim) terms)
    else terms;
end;