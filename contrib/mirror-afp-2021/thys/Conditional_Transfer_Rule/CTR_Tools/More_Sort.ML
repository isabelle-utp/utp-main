(* Title: CTR_Tools/More_Sort.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the structure Sorts from the standard library of 
Isabelle/Pure.
*)

signature SORTS =
sig
  include SORTS
  val params_of_super_classes : theory -> class -> (string * typ) list
  val params_of_sort : theory -> class list -> (string * typ) list
end;

structure Sorts: SORTS  =
struct

open Sorts;

fun params_of_class thy class = 
  try (Axclass.get_info thy #> #params) class |> these;

fun params_of_super_classes thy class =
  class :: Sorts.super_classes (Sign.classes_of thy) class 
  |> maps (params_of_class thy);

fun params_of_sort thy sort = maps (params_of_super_classes thy) sort;

end;