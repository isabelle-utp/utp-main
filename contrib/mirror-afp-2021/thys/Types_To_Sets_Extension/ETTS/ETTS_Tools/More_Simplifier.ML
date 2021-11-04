(* Title: ETTS/ETTS_Tools/More_Simplifier.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the structure Simplifier from the standard library of 
Isabelle/Pure.

Notes: 
  - The structure More_Simplifier was copied from the file 
  HOL/Types_To_Sets/Examples/Prerequisites.thy (with amendments)
*)

structure More_Simplifier =
struct

open More_Simplifier;

fun rewrite_simp_opt' ctxt simp_spec_opt = case simp_spec_opt of 
    SOME simp_spec => 
      var_simplify_only 
        ctxt 
        (Attrib.eval_thms ctxt (single simp_spec)) 
  | NONE => Simplifier.full_simplify ctxt;

end;