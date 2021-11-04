(* Title: ETTS/ETTS_Tools/More_HOLogic.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the structure HOLogic from the standard library of 
Isabelle/Pure.
*)

signature HOLOGIC =
sig
  include HOLOGIC
  val dest_exists :  term -> string * typ * term
  val mk_type_definition_pred : typ -> typ -> term
  val dest_type_definition : term -> term * term * term
  val is_binrelvarT : typ -> bool
  val dest_SetT : typ -> typ
  val dest_SetTFree: typ -> string * sort 
  val is_setT : typ -> bool
  val is_var_setT : typ -> bool
end;

structure HOLogic: HOLOGIC =
struct

open HOLogic;

fun dest_exists ((Const (\<^const_name>\<open>HOL.Ex\<close>, _) $ Abs (c, U, t))) = (c, U, t)
  | dest_exists t = raise TERM ("dest_exists", single t);

fun mk_type_definition_pred T U = Const 
  (
    \<^const_name>\<open>type_definition\<close>,
    (T --> U) --> (U --> T) --> HOLogic.mk_setT U --> HOLogic.boolT
  );

fun dest_type_definition
  (Const (\<^const_name>\<open>type_definition\<close>, _) $ rept $ abst $ sett) = 
    (rept, abst, sett)
  | dest_type_definition t = raise TERM ("dest_type_definition", single t);

fun is_binrelvarT 
    (
      Type 
        (
          \<^type_name>\<open>fun\<close>, 
            [
              TVar sT,
              Type (\<^type_name>\<open>fun\<close>, [TVar sU, Type (\<^type_name>\<open>HOL.bool\<close>, [])])
            ]
        )
    ) = not (sT = sU)
  | is_binrelvarT _ = false;

fun is_setT (Type (\<^type_name>\<open>Set.set\<close>, _)) = true
  | is_setT _ = false

fun is_var_setT (Type (\<^type_name>\<open>Set.set\<close>, [TVar _])) = true
  | is_var_setT (Type (\<^type_name>\<open>Set.set\<close>, [TFree _])) = true
  | is_var_setT _ = false

fun dest_SetT (Type (\<^type_name>\<open>Set.set\<close>, [T])) = T
  | dest_SetT T = raise TYPE("dest_SetT", single T, []);

fun dest_SetTFree (Type (\<^type_name>\<open>Set.set\<close>, [T])) = dest_TFree T
  | dest_SetTFree T = raise TYPE("dest_SetTFree", single T, []);

end;