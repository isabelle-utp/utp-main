signature PRISM_LIB =
sig
  val wb_prismN: string
  val prism_diffN: string
  val codepsN: string

  (* Prism terms *)

  val prismT: typ -> typ -> typ
  val isPrismT: typ -> bool
  val mk_wb_prism: term -> term           (* Make a well-behaved prism term *)
  val mk_codep: term -> term -> term      (* Make a codependence term *)

end

structure Prism_Lib : PRISM_LIB = 
struct

open Syntax
open HOLogic

val wb_prismN = @{const_name wb_prism}
val prism_diffN = @{const_name prism_diff}

val codepsN = "codeps"

fun prismT a b = Type (@{type_name prism_ext}, [a, b, unitT])

fun isPrismT (Type (n, _)) = (n = @{type_name prism_ext}) |
    isPrismT _ = false

fun mk_wb_prism t = mk_Trueprop (const wb_prismN $ t)

fun mk_codep x y = mk_Trueprop (const prism_diffN $ x $ y)

end
