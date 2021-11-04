(* Title: ETTS/ETTS_Tools/More_Term.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the structure Term from the standard library of 
Isabelle/Pure.
*)

signature TERM =
sig
  include TERM
  val is_cv : term -> bool
  val sort_of_tvar : typ -> sort
  val sort_eqT : theory -> typ * typ -> bool
end;

structure Term: TERM  =
struct

open Term;

fun is_cv t = is_Const t orelse is_Var t

fun sort_of_tvar (TVar (_, S)) = S
  | sort_of_tvar (TFree (_, S)) = S
  | sort_of_tvar T = 
      raise TYPE ("the type is not a type variable", single T, [])

fun sort_eqT thy (T, U) =
  let val algebra = Sign.classes_of thy
  in Sorts.sort_eq algebra (sort_of_tvar T, sort_of_tvar U) end;

end;