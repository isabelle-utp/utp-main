(* Title: CTR_Tools/More_Binding.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the structure Binding from the standard library of 
Isabelle/Pure.
*)

signature BINDING =
sig
  include BINDING
  val qualified_name_mandatory : string -> binding
end;

structure Binding: BINDING =
struct

open Binding;

fun qualified_name_mandatory c = fold
  (fn c => fn b => Binding.qualify_name true b c)
  (Long_Name.explode c)
  Binding.empty;

end;