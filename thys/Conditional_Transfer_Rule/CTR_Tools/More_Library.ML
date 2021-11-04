(* Title: CTR_Tools/More_Library.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the structure Library from the standard library of 
Isabelle/Pure.
*)

signature LIBRARY =
sig
    
  include LIBRARY
  
  (*pairs and triples*)
  val reroute_ps_sp : ('a * 'b) * 'c -> 'a * ('b * 'c)
  val reroute_sp_ps : 'a * ('b * 'c) -> ('a * 'b) * 'c
  val reroute_ps_triple : ('a * 'b) * 'c -> 'a * 'b * 'c  
  val reroute_sp_triple : 'a * ('b * 'c) -> 'a * 'b * 'c
  val reroute_triple_ps : 'a * 'b * 'c -> ('a * 'b) * 'c  
  val reroute_triple_sp : 'a * 'b * 'c -> 'a * ('b * 'c)

  val dup : 'a -> 'a * 'a
  val apdupr : ('a -> 'b) -> 'a -> 'a * 'b
  val apdupl : ('a -> 'b) -> 'a -> 'b * 'a

  (*lists*)
  val map_slice_l : ('a list -> 'b list) -> ('a * 'c) list -> ('b * 'c) list
  val map_slice_r : ('a list -> 'b list) -> ('c * 'a) list -> ('c * 'b) list
  val map_slice_side_l : 
    ('a list -> 'b list * 'c) -> ('a * 'd) list -> ('b * 'd) list * 'c
  val map_slice_side_r : 
    ('a list -> 'b list * 'c) -> ('d * 'a) list -> ('d * 'b) list * 'c  
  val find_indices : ('a -> bool) -> 'a list -> int list

  (*strings*)
  val tabulate : string -> string
  
  (*option*)
  val mk_opt_id : ('a -> 'b) -> ('a -> 'b option) -> 'a -> 'b

  (*keywords*)
  val kw_bo : string parser
  val kw_bc : string parser
  val kw_col : string parser

end

structure Library: LIBRARY =
struct

open Library;


(** pairs and triples **)

fun reroute_ps_sp ((x, y), z) = (x, (y, z));
fun reroute_sp_ps (x, (y, z)) = ((x, y), z);
fun reroute_ps_triple ((x, y), z) = (x, y, z);
fun reroute_sp_triple (x, (y, z)) = (x, y, z);
fun reroute_triple_ps (x, y, z) = ((x, y), z);
fun reroute_triple_sp (x, y, z) = (x, (y, z));

fun dup x = (x, x);
fun apdupr f x = (x, f x);
fun apdupl f x = (f x, x);


(** lists **)

fun map_slice_l f xs = xs 
  |> split_list
  |>> f
  |> op~~;
fun map_slice_r f xs = xs 
  |> split_list
  ||> f
  |> op~~;
fun map_slice_side_l f xs = xs 
  |> split_list
  |>> f
  |> swap
  |> reroute_sp_ps
  |>> swap  
  |>> op~~;
fun map_slice_side_r f xs = xs 
  |> split_list
  ||> f
  |> reroute_sp_ps
  |>> op~~;

fun find_indices p xs =
  let
    fun find_indices_impl _ _ [] = []
      | find_indices_impl p i (x::xs) =
          if p x 
          then i::find_indices_impl p (i + 1) xs
          else find_indices_impl p (i + 1) xs
  in find_indices_impl p 0 xs end;


(** option **)

fun mk_opt_id g f x = case f x of SOME y => y | NONE => g x;


(** strings **)

val tabulate = split_lines #> map (fn c => "\t" ^ c) #> String.concatWith "\n"


(** shortcuts for common keywords **)

val kw_bo = \<^keyword>\<open>(\<close>;
val kw_bc = \<^keyword>\<open>)\<close>;
val kw_col = \<^keyword>\<open>:\<close>;

end

open Library;