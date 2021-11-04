(* Title: ETTS/ETTS_Tools/More_Tactical.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the structure Tactical from the standard library of 
Isabelle/Pure.
*)

signature TACTICAL =
sig
  include TACTICAL
  val FIRST_APPEND' : ('a -> tactic) list -> 'a -> tactic
end;

structure Tactical: TACTICAL =
struct

open Tactical;

(*based on the tactical FIRST in the main distribution*)
fun FIRST_APPEND' tacs = fold_rev (curry op APPEND') tacs (K no_tac);

end;

open Tactical;