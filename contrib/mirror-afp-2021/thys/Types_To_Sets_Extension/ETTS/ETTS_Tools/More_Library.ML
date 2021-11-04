(* Title: ETTS/ETTS_Tools/More_Library.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the structure Library from the standard library of 
Isabelle/Pure.
*)

signature LIBRARY =
sig

  include LIBRARY

  (*functions*)
  val flip : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  
  (*lists*)
  val list_of_pair : 'a * 'a -> 'a list
  val pair_of_list : 'a list -> 'a * 'a
  val list_of_triple : 'a * 'a * 'a -> 'a list
  val triple_of_list : 'a list -> 'a * 'a * 'a
  val compare_each : ('a * 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val numdup : ('a * 'a -> bool) -> 'a list -> int
  val rotate_list : 'a list -> 'a list
  
  (*integers*)
  val min_list : int list -> int

end;

structure Library: LIBRARY =
struct

open Library;

(** functions **)

fun flip f x y = f y x


(** lists **)

fun list_of_pair (x, y) = [x, y];
fun pair_of_list [x, y] = (x, y)
  | pair_of_list _ = raise Fail "pair_of_list";
fun list_of_triple (x, y, z) = [x, y, z];
fun triple_of_list [x, y, z] = (x, y, z)
  | triple_of_list _ = raise Fail "triple_of_list";

fun compare_each _ [] [] = []
  | compare_each eq (x::xs) (y::ys) = (eq (x, y)) :: compare_each eq xs ys
  | compare_each _ [] (_::_) = raise Empty
  | compare_each _ (_::_) [] = raise Empty;

fun numdup eq xs = length xs - length (distinct eq xs);

fun rotate_list xs = tl xs @ [hd xs];


(** integers **)

fun min_list xs = 
  fold (fn x => fn min => if x < min then x else min) (tl xs) (hd xs);

end;

open Library;