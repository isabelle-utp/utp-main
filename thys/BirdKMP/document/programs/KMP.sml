(* Bird's Morris-Pratt string matcher
   Chapter 17, "Pearls of Functional Algorithm Design", 2010.
    - with the `K' (next) optimisation
    - using backpatching
 *)

structure KMP :> sig val kmatches : ('a * 'a -> bool) -> 'a list -> 'a list -> int list end =
struct

datatype 'a thunk = Val of 'a | Thunk of unit -> 'a

type 'a lazy = 'a thunk ref

fun lazy (f: unit -> 'a) : 'a lazy =
  ref (Thunk f)

fun force (su : 'a lazy) : 'a =
  case !su of
      Val v => v
    | Thunk f => let val v = f () in su := Val v; v end

datatype 'a tree
  = Null
  | Node of 'a list * 'a tree lazy * 'a tree

type 'a ltree = 'a tree lazy

fun kmatches (eq: 'a * 'a -> bool) (ws: 'a list) : 'a list -> int list =
  let
    fun ok (t: 'a ltree) : bool = case force t of Node ([], l, r) => true | _ => false
    fun next (x: 'a) (t: 'a ltree) : 'a ltree =
           lazy (fn () => let val t = force t in case t of
             Null => Null
           | Node ([], _, _) => t
           | Node (v :: vs, l, _) => if eq (x, v) then force l else t end)
     (* Backpatching! *)
     val root : 'a ltree = lazy (fn () => raise Fail "blackhole")
     fun op' (t: 'a ltree) (x: 'a) : 'a ltree =
           lazy (fn () => case force t of
             Null => force root
           | Node (vvs, l, r) =>
             (case vvs of
                [] => force (op' l x)
              | v :: vs => if eq (x, v) then r else force (op' l x)))
     and grep (l: 'a ltree) (vvs: 'a list): 'a tree =
           ( (* print "grep: produce node\n"; *) case vvs of
             [] => Node ([], l, Null)
           | v :: vs => Node (vvs, next v l, grep (op' l v) vs) )
     val () = root := Thunk (fn () => grep (lazy (fn () => Null)) ws)
     fun step ((n, t): int * 'a ltree) (x: 'a) : int * 'a ltree = (n + 1, op' t x)
     fun rheight (t: 'a tree) =
           case t of Null => 0 | Node (_, _, r) => 1 + rheight r
     fun driver ((n, t): int * 'a ltree) (xxs: 'a list) : int list =
           case xxs of
             [] => if ok t then [n] else []
           | x :: xs => let val nt' = step (n, t) x
                        in if ok t then n :: driver nt' xs else driver nt' xs end
  in
    driver (0, root)
  end

end;

KMP.kmatches (op =) [] [] ;
KMP.kmatches (op =) [] [1,2,3] ;
KMP.kmatches (op =) [1, 2, 1] [] ;
KMP.kmatches (op =) [1, 2] [1, 2, 3] ;
KMP.kmatches (op =) [1, 2, 3, 1, 2] [1, 2, 1, 2, 3, 1, 2, 3, 1, 2] ;

List.app (fn x => print (Int.toString x ^ "\n")) (KMP.kmatches (op =) [1, 2, 3, 1, 2] [1, 2, 1, 2, 3, 1, 2, 3, 1, 2]) ;

val text = List.concat (List.tabulate (1000000, fn _ => [1, 2, 1, 2, 3, 1, 2, 3, 1, 2]));
val _ = (fn x => print (Int.toString (List.length x) ^ "\n")) (KMP.kmatches (op =) [1, 2, 3, 1, 2] text);
