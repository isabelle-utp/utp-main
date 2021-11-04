(* Title: CTR/CTR_Algorithm.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Abstract interface for the definition of an algorithm for the synthesis
of transfer rules and relativized definitions.
*)

signature CTR_ALGORITHM =
sig

val apply : 
  Proof.context ->
  bool * thm list option ->
  thm list ->
  ((indexname * sort) * term) list ->
  thm -> 
  ctr_alg_out

end;