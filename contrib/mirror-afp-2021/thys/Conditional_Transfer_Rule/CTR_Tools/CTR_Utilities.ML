(* Title: CTR_Tools/CTR_Utilities.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

A collection of Isabelle/ML utilities for the CTR.
*)

signature CTR_UTILITIES =
sig
val thm_printer : Proof.context -> bool -> string -> thm list -> unit
val qualified_name_of_const_name : string -> string
end;

structure CTR_Utilities : CTR_UTILITIES =
struct

fun thm_printer ctxt print name thms =
  Proof_Display.print_results
    print
    (Position.thread_data ())
    ctxt
    ((Thm.theoremK, ""), single (name, thms));

fun qualified_name_of_const_name c = 
  if Long_Name.qualification c = 0
  then error "qualified_name_of_const_name: invalid constant name"
  else 
    if Long_Name.qualification c = 1 
    then c 
    else c |> Long_Name.explode |> tl |> Long_Name.implode

end;