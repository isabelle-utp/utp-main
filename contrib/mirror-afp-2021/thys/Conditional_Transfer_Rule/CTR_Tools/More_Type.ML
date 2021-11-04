(* Title: CTR_Tools/More_Type.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the structure Type from the standard library of 
Isabelle/Pure.
*)

signature TYPE =
sig
  include TYPE
  val typ_matches : tsig -> typ list * typ list -> tyenv -> tyenv
  val default_sorts_of_empty_sorts : theory -> typ -> typ
  val default_sorts : theory -> typ -> typ
end 

structure Type: TYPE  =
struct

open Type;

fun typ_matches tsig (T :: Ts, U :: Us) subs = 
      typ_matches tsig (Ts, Us) (Type.typ_match tsig (T, U) subs)
  | typ_matches _ ([], []) subs = subs
  | typ_matches _ _ _ = raise Type.TYPE_MATCH;

fun default_sorts_of_empty_sorts thy = 
  let val dS = Sign.defaultS thy
  in
    map_atyps
      (
        fn TFree (x, []) => TFree (x, dS)
         | TVar (xi, []) => TVar (xi, dS)
         | TFree (x, S) => TFree (x, S)
         | TVar (xi, S) => TVar (xi, S)
      )
  end;

fun default_sorts thy = 
  let val dS = Sign.defaultS thy
  in
    map_atyps
      (
        fn TFree (x, _) => TFree (x, dS)
         | TVar (xi, _) => TVar (xi, dS)
      )
  end;

end;