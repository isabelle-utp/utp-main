(* Title: CTR_Tools/More_Variable.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the structure Variable from the standard library of 
Isabelle/Pure.
*)

signature VARIABLE =
sig
  include VARIABLE
  val fix_new_vars : Proof.context -> string list -> Proof.context
  val variant_name_const : Proof.context -> string list -> string list
end

structure Variable: VARIABLE  =
struct

open Variable;

(*fix new variables*)
fun fix_new_vars ctxt cs = 
  let
    fun fix_new_vars_select c ctxt = 
      if Variable.is_fixed ctxt c 
      then ctxt
      else ctxt |> Variable.add_fixes (single c) |> #2
  in fold_rev fix_new_vars_select cs ctxt end;

(*invent new name variants with respect to the base names of constants*)
fun variant_name_const ctxt names = 
  let
    val {constants=constants, ...} = Consts.dest (Proof_Context.consts_of ctxt)
    val const_names = map (#1 #> Long_Name.base_name) constants
    val name_ctxt = ctxt
      |> Variable.names_of
      |> fold Name.declare const_names
    val names =
      let
        fun folder name (names, name_ctxt) = 
          Name.variant name name_ctxt |>> curry (swap #> op::) names
      in ([], name_ctxt) |> fold folder names |> #1 end
  in names end;

end