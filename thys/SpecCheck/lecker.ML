(*  Title:      SpecCheck/lecker.ML
    Author:     Kevin Kappelmann

Testing framework that lets you combine SpecCheck tests into test suites.

TODO: this file can be largely extended to become a pendant of Haskell's tasty:
https://hackage.haskell.org/package/tasty
*)

signature LECKER =
sig
  (*the first parameter to test_group will usually be a context*)
  val test_group : 'a -> 's -> ('a -> 's -> 's) list -> 's
end

structure Lecker : LECKER =
struct

fun test_group _ s [] = s
  | test_group fixed_param s (t::ts) =
      fold (fn t => (Pretty.writeln (Pretty.para ""); t fixed_param)) ts (t fixed_param s)

end
