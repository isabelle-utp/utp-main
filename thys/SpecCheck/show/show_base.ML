(*  Title:      SpecCheck/show/show_base.ML
    Author:     Kevin Kappelmann

Basic utility functions to create and combine show functions.
*)

signature SPECCHECK_SHOW_BASE =
sig
  include SPECCHECK_SHOW_TYPES

  val none : 'a show
  val char : char show
  val string : string show
  val int : int show
  val real : real show
  val bool : bool show
  val list : 'a show -> ('a list) show
  val option : 'a show -> ('a option) show

  val zip : 'a show -> 'b show -> ('a * 'b) show
  val zip3 : 'a show -> 'b show -> 'c show -> ('a * 'b * 'c) show
  val zip4 : 'a show -> 'b show -> 'c show -> 'd show -> ('a * 'b * 'c * 'd) show

end

structure SpecCheck_Show_Base : SPECCHECK_SHOW_BASE =
struct

open SpecCheck_Show_Types

fun none _ = Pretty.str "<NO_SHOW>"
val char = Pretty.enclose "'" "'" o single o Pretty.str o Char.toString
val string = Pretty.quote o Pretty.str
val int = Pretty.str o string_of_int
val real = Pretty.str o string_of_real
fun bool b = Pretty.str (if b then "true" else "false")
fun list show = Pretty.list "[" "]" o map show
fun option _ NONE = Pretty.str "NONE"
  | option show (SOME v) = Pretty.block [Pretty.str "SOME ", show v]

fun pretty_tuple ps = ps |> Pretty.commas |> Pretty.enclose "(" ")"

fun zip showA showB (a, b) = pretty_tuple [showA a, showB b]
fun zip3 showA showB showC (a, b, c) = pretty_tuple [showA a, showB b, showC c]
fun zip4 showA showB showC showD (a, b, c, d) = pretty_tuple [showA a, showB b, showC c, showD d]

end
