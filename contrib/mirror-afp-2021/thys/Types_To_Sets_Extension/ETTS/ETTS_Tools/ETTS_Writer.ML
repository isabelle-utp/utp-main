(* Title: ETTS/ETTS_Tools/ETTS_Writer.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the structure Writer from the standard library of 
Isabelle/Pure.
*)

signature ETTS_WRITER =
sig
val initialize : int -> int list
val increment_index : int -> int list -> int list
val write_action : string -> int list -> int list
end;

structure ETTS_Writer : ETTS_WRITER =
struct

fun initialize length = replicate length 1

fun index_to_string ns = ns 
  |> rev
  |> map Int.toString
  |> String.concatWith ".";

fun increment_index i ns = 
  let
    val i = length ns - i - 1
    val ns = nth_map i (fn n => n + 1) ns
    val (ns_lhs, ns_rhs) = chop i ns
    val ns_lhs = map (K 1) ns_lhs
  in ns_lhs @ ns_rhs end;

fun write_action c ns =
  let
    val c = index_to_string ns ^ ". " ^ c
    val ns = (hd ns + 1) :: tl ns
    val _ = writeln c
  in ns end;

end;