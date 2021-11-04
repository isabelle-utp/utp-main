(* Title: ETTS/ETTS_Tools/More_Logic.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the structure Logic from the standard library of 
Isabelle/Pure.
*)

signature LOGIC =
sig
  include LOGIC
  val forall_elim_all : term -> term * (string * typ) list
  val get_forall_ftv_permute : term -> term * ((string * typ) list * int list)
end

structure Logic: LOGIC  =
struct

open Logic;

(*forall elimination*)
fun forall_elim_all t =
  let
    fun forall_elim_all_impl t ftv_specs = 
      let val (ftv_spec, t) = Logic.dest_all t 
      in forall_elim_all_impl t (ftv_spec::ftv_specs) end
      handle TERM ("dest_all", _) => (t, ftv_specs)
  in forall_elim_all_impl t [] ||> rev end;

(*indices of the universally quantified variables with respect to the 
order of their appearance in the term in the sense of Term.add_frees*)
fun get_forall_ftv_permute t =
  let
    val (t', forall_ftv_specs) = forall_elim_all t
    val ftv_specs = Term.add_frees t' [] |> rev
    val call_ftv_specs = ftv_specs 
      |> subtract op= (ftv_specs |> subtract op= forall_ftv_specs)
    val index_of_ftv = 
      (call_ftv_specs ~~ (0 upto (length call_ftv_specs - 1)))
      |> AList.lookup op= #> the
    val forall_ftv_permute = map index_of_ftv forall_ftv_specs
  in (t', (forall_ftv_specs, forall_ftv_permute)) end;

end;