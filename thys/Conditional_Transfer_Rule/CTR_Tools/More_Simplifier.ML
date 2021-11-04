(* Title: CTR_Tools/More_Simplifier.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the functionality of the simplifier provided as part of
the standard library of Isabelle/Pure.

Notes:
  - The structure More_Simplifier was copied from the file 
  HOL/Types_To_Sets/Examples/Prerequisites.thy (with amendments)
*)

structure More_Simplifier =
struct

fun asm_full_var_simplify ctxt thm =
  let
    val ((_, [thm']), ctxt') = Variable.import false [thm] ctxt
  in
    Simplifier.full_simplify ctxt' thm'
    |> singleton (Variable.export ctxt' ctxt)
    |> Drule.zero_var_indexes
  end;

fun var_simplify_only ctxt ths thm =
  asm_full_var_simplify (Raw_Simplifier.clear_simpset ctxt addsimps ths) thm;

val var_simplified = Attrib.thms >>
  (fn ths => Thm.rule_attribute ths
    (fn context => var_simplify_only (Context.proof_of context) ths));

fun rewrite_simp_opt ctxt simp_spec_opt = case simp_spec_opt of 
    SOME simp_spec => var_simplify_only ctxt simp_spec 
  | NONE => Simplifier.full_simplify ctxt;

end;