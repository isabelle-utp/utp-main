(* Title: CTR_Tools/More_Term.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

An extension of the structure Term from the standard library of 
Isabelle/Pure.
*)

signature TERM =
sig
  include TERM
  val map_sv : (indexname * typ -> term) -> term -> term
  val map_fv : (string * typ -> term) -> term -> term
  val map_const : (string * typ -> term) -> term -> term
  val map_tfree: (string * sort -> typ) -> term -> term
  val has_tfreesT : typ -> bool
  val is_comb : term -> bool
  val could_match_const : (''a * typ) * (''a * typ) -> bool
end;

structure Term: TERM  =
struct

open Term;

fun map_sv f (Var sv_spec) = f sv_spec
  | map_sv f (Abs (c, T, t)) = Abs (c, T, map_sv f t)
  | map_sv f (t $ u) = map_sv f t $ map_sv f u
  | map_sv _ t = t;

fun map_fv f (Free fv_spec) = f fv_spec
  | map_fv f (Abs (c, T, t)) = Abs (c, T, map_fv f t)
  | map_fv f (t $ u) = map_fv f t $ map_fv f u
  | map_fv _ t = t;

fun map_const f (Const const_spec) = f const_spec
  | map_const f (Abs (c, T, t)) = Abs (c, T, map_const f t)
  | map_const f (t $ u) = map_const f t $ map_const f u
  | map_const _ t = t;

fun map_tfree f (Const (c, T)) = Const (c, map_type_tfree f T)
  | map_tfree f (Free (c, T)) = Free (c, map_type_tfree f T)
  | map_tfree f (Var (v, T)) = Var (v, map_type_tfree f T) 
  | map_tfree f (Abs (c, T, t)) = Abs (c, map_type_tfree f T, map_tfree f t)
  | map_tfree f (t $ u) = map_tfree f t $ map_tfree f u
  | map_tfree _ t = t

fun has_tfreesT (TFree _) = true
  | has_tfreesT (TVar _) = false
  | has_tfreesT (Type (_, Ts)) = has_tfreesT_list Ts
and has_tfreesT_list [] = false
  | has_tfreesT_list (T::Ts) = has_tfreesT T orelse has_tfreesT_list Ts;

fun is_comb (_ $ _) = true
  | is_comb _ = false;

fun could_match_const ((c, T), (c', T')) = 
  c = c' andalso Type.could_match (T, T');

end;