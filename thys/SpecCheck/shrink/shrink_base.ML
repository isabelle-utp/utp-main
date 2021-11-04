(*  Title:      SpecCheck/shrink/shrink_base.ML
    Author:     Kevin Kappelmann

Basic utility functions to create and combine shrink functions.
*)

signature SPECCHECK_SHRINK_BASE =
sig
  include SPECCHECK_SHRINK_TYPES

  val none : 'a shrink

  val product : 'a shrink -> 'b shrink -> ('a * 'b) shrink
  val product3 : 'a shrink -> 'b shrink -> 'c shrink -> ('a * 'b * 'c) shrink
  val product4 : 'a shrink -> 'b shrink -> 'c shrink -> 'd shrink -> ('a * 'b * 'c * 'd) shrink

  val int : int shrink

  val list : 'a shrink -> ('a list shrink)
  val list' : ('a list) shrink

  val term : term shrink

end

structure SpecCheck_Shrink_Base : SPECCHECK_SHRINK_BASE =
struct
open SpecCheck_Shrink_Types

fun none _ = Seq.empty

fun product_seq xq yq (x, y) =
  let
    val yqy = Seq.append yq (Seq.single y)
    val zq1 = Seq.maps (fn x => Seq.map (pair x) yqy) xq
    val zq2 = Seq.map (pair x) yq
  in Seq.append zq1 zq2 end

fun product shrinkA shrinkB (a, b) = product_seq (shrinkA a) (shrinkB b) (a, b)

fun product3 shrinkA shrinkB shrinkC (a, b, c) =
  product shrinkA shrinkB (a, b)
  |> (fn abq => product_seq abq (shrinkC c) ((a,b),c))
  |> Seq.map (fn ((a,b),c) => (a,b,c))

fun product4 shrinkA shrinkB shrinkC shrinkD (a, b, c, d) =
  product3 shrinkA shrinkB shrinkC (a, b, c)
  |> (fn abcq => product_seq abcq (shrinkD d) ((a,b,c),d))
  |> Seq.map (fn ((a,b,c),d) => (a,b,c,d))

(*bit-shift right until it hits zero (some special care needs to be taken for negative numbers*)
fun int 0 = Seq.empty
  | int i =
    let
      val absi = abs i
      val signi = Int.sign i
      fun seq 0w0 () = NONE
        | seq w () =
          let
            val next_value = signi * IntInf.~>> (absi, w)
            val next_word = Word.- (w, 0w1)
          in SOME (next_value, Seq.make (seq next_word)) end
      val w = Word.fromInt (IntInf.log2 (abs i))
    in Seq.cons 0 (Seq.make (seq w)) end

fun list _ [] = Seq.single []
  | list elem_shrink [x] = Seq.cons [] (Seq.map single (elem_shrink x))
  | list elem_shrink (x::xs) =
    let
      val elems = Seq.append (elem_shrink x) (Seq.single x)
      val seq = Seq.maps (fn xs => Seq.map (fn x => x :: xs) elems) (list elem_shrink xs)
    in Seq.cons [] seq end

fun list' xs = list none xs

fun term (t1 $ t2) =
    let
      val s1 = Seq.append (term t1) (Seq.single t1)
      val s2 = Seq.append (term t2) (Seq.single t2)
      val s3 = Seq.map (op$) (product term term (t1, t2))
    in Seq.append s1 (Seq.append s2 s3) end
  | term (Abs (x, T, t)) =
      let
        val s1 = Seq.append (term t) (Seq.single t)
        val s2 = Seq.map (fn t => Abs (x, T, t)) (term t)
      in Seq.append s1 s2 end
  | term _ = Seq.empty

end
