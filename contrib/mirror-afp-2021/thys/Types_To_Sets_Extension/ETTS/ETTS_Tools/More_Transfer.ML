(* Title: ETTS/ETTS_Tools/More_Transfer.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the structure Transfer from the standard library of 
Isabelle/Pure.
*)

signature TRANSFER =
sig
  include TRANSFER
  val mk_rel_sc : string -> term -> term
  val mk_bi_unique : term -> term
  val mk_right_total : term -> term  
  val mk_transfer_rels : thm list -> thm list
end

structure Transfer: TRANSFER  =
struct

open Transfer;

fun mk_rel_sc c t = Const (c, type_of t --> HOLogic.boolT) $ t;
fun mk_bi_unique t = mk_rel_sc \<^const_name>\<open>Transfer.bi_unique\<close> t;
fun mk_right_total t = mk_rel_sc \<^const_name>\<open>Transfer.right_total\<close> t;

(*amend a list of transfer rules with the constant Transfer.Rel*)
fun mk_transfer_rels tr_thms =
  let
    val tr_to_tr_rel_thm = @{thm tr_to_tr_rel};
    val ct = Thm.cprems_of tr_to_tr_rel_thm |> the_single
    val tr_thms = tr_thms
      |> 
        (
          (
            fn tr_thm => 
            Thm.first_order_match (ct, (tr_thm |> Thm.cprop_of))
          )
          |> map
        )
      |> map (fn inst => Drule.instantiate_normalize inst tr_to_tr_rel_thm)
      |> curry (swap #> op~~) (map single tr_thms)
      |> map op OF
  in tr_thms end;

end
