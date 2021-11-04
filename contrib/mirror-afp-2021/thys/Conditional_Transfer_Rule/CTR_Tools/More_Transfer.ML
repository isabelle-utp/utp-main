(* Title: CTR_Tools/More_Transfer.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the structure Transfer from the standard library of 
Isabelle/Pure.
*)

signature TRANSFER =
sig
  include TRANSFER
  val is_is_equality : term -> bool
end;

structure Transfer: TRANSFER =
struct

open Transfer;

fun is_is_equality (Const (\<^const_name>\<open>is_equality\<close>, _) $ _) = true
  | is_is_equality _ = false;

end;