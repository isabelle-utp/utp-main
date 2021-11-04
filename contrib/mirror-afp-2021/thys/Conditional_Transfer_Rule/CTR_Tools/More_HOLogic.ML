(* Title: CTR_Tools/More_HOLogic.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the structure HOLogic from the standard library of Isabelle/HOL.
*)

signature HOLOGIC =
sig
  include HOLOGIC
  val mk_binrelT : typ * typ -> typ 
  val is_binrelT : typ -> bool
  val dest_binrelT : typ -> typ * typ
  val mk_rel : string * (typ * typ) -> term
  val is_conj : term -> bool
end;

structure HOLogic: HOLOGIC =
struct

open HOLogic;

fun mk_binrelT (T, U) = T --> U --> HOLogic.boolT;

fun is_binrelT (
  Type (\<^type_name>\<open>fun\<close>, [_, Type (\<^type_name>\<open>fun\<close>, [_, \<^typ>\<open>bool\<close>])])
  ) = true
  | is_binrelT _ = false
 
fun dest_binrelT (Type (\<^type_name>\<open>fun\<close>, [T, Type (\<^type_name>\<open>fun\<close>, [U, _])])) = 
      (T, U)
  | dest_binrelT T = raise TYPE("dest_binrelT", single T, []); 

fun mk_rel (c, (T, U)) = Free (c, mk_binrelT (T, U))

fun is_conj (Const (\<^const_name>\<open>conj\<close>, _) $ _ $ _) = true
  | is_conj _ = false;

end;