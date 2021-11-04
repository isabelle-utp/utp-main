(* Bird's Morris-Pratt string matcher, with the `K' optimisation in ocaml
   Chapter 17, "Pearls of Functional Algorithm Design", 2010. *)

(*
Encoding the requisite laziness is fiddly:
 - as Wadler observes this style is `odd`
 - forced to use `Lazy.t` to share `root`
 - intuitively need to manually manage how demand is transferred
   through the computation.
*)

type 'a tree
  = Null
  | Node of 'a list * 'a ltree * 'a tree
and 'a ltree = 'a tree Lazy.t

let kmatches (type a) (eq: a -> a -> bool) (ws: a list) : a list -> int list =
     let ok (t: a ltree) : bool = match Lazy.force t with Node (vs, l, r) -> vs = []
  in let next (x: a) (t: a ltree) : a ltree =
           lazy (let t = Lazy.force t in match t with
             Null -> Null
           | Node ([], _l, _r) -> t
           | Node (v :: vs, l, _r) -> if eq x v then Lazy.force l else t)
  in let rec op (t: a ltree) (x: a) : a ltree =
           lazy (match Lazy.force t with
             Null -> Lazy.force root
           | Node (vvs, l, r) ->
             (match vvs with
                [] -> Lazy.force (op l x)
              | v :: vs -> if eq x v then r else Lazy.force (op l x)))
     and grep (l: a ltree) (vvs: a list) : a tree =
           match vvs with
             [] -> Node ([], l, Null)
           | v :: vs -> Node (vvs, next v l, grep (op l v) vs)
     and root : a ltree = lazy (grep (lazy Null) ws)
  in let step (nt: int * a ltree) (x: a) : int * a ltree =
           fst nt + 1, op (snd nt) x
  in let rec rheight (t: a tree) =
           match t with Null -> 0 | Node (_, _, r) -> 1 + rheight r
  in let rec driver (nt: int * a ltree) (xxs: a list) : int list =
           match xxs with
             [] -> if ok (snd nt) then [fst nt] else []
           | x :: xs -> let nt' : int * a ltree = step nt x
                    in if ok (snd nt) then fst nt :: driver nt' xs else driver nt' xs
  in driver (0, root)

;;

List.iter (Printf.printf "%d ") (kmatches (=) [] []) ;
List.iter (Printf.printf "%d ") (kmatches (=) [] [1;2;3]) ;
List.iter (Printf.printf "%d ") (kmatches (=) [1;2;1] []) ;
List.iter (Printf.printf "%d ") (kmatches (=) [1;2] [1;2;3]) ;
List.iter (Printf.printf "%d ") (kmatches (=) [1;2;3;1;2] [1;2;1;2;3;1;2;3;1;2]) ;
