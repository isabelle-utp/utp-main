(* Copyright 2021 (C) Mihails Milehins *)

signature CS_STATS =
sig
val basic_stats : real list -> real list
end;

structure CS_Stats: CS_STATS =
struct

(*based on https://en.wikipedia.org/wiki/Variance*)
fun basic_stats xs =
  let
    fun sqr x = x*x
    val n = Real.fromInt (length xs)
    val mean = fold (curry op+) xs 0.0 / n
    val variance = fold (fn x => fn y => y + sqr (x - mean)) xs 0.0 / n
    val max = fold (curry Real.max) xs 0.0
    val min = fold (curry Real.min) xs max
  in [mean, variance, min, max] end;

end;