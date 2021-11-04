structure SASP_Checker_Exported : sig
  type nat
  val integer_of_nat : nat -> IntInf.int
  type char
  datatype ('a, 'b) sum = Inl of 'a | Inr of 'b
  val implode : char list -> string
  val explode : string -> char list
  val verify_plan :
    (char list * (nat option * (char list) list)) list *
      (nat list *
        ((nat * nat) list *
          (char list *
            ((nat * nat) list *
              (((nat * nat) list * (nat * (nat option * nat))) list *
                nat))) list)) ->
      (char list) list -> (string, unit) sum
  val nat_of_integer : IntInf.int -> nat
  val nat_opt_of_integer : IntInf.int -> nat option
end = struct

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = equal_nata} : nat equal;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

fun equal_bool p true = p
  | equal_bool p false = not p
  | equal_bool true p = p
  | equal_bool false p = not p;

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

fun equal_chara (Chara (x1, x2, x3, x4, x5, x6, x7, x8))
  (Chara (y1, y2, y3, y4, y5, y6, y7, y8)) =
  equal_bool x1 y1 andalso
    (equal_bool x2 y2 andalso
      (equal_bool x3 y3 andalso
        (equal_bool x4 y4 andalso
          (equal_bool x5 y5 andalso
            (equal_bool x6 y6 andalso
              (equal_bool x7 y7 andalso equal_bool x8 y8))))));

val equal_char = {equal = equal_chara} : char equal;

datatype num = One | Bit0 of num | Bit1 of num;

val one_integera : IntInf.int = (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_integer = {one = one_integera} : IntInf.int one;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_integer = {zero = (0 : IntInf.int)} : IntInf.int zero;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

val zero_neq_one_integer =
  {one_zero_neq_one = one_integer, zero_zero_neq_one = zero_integer} :
  IntInf.int zero_neq_one;

datatype ('a, 'b) sum = Inl of 'a | Inr of 'b;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nat : nat = Nat (1 : IntInf.int);

fun suc n = plus_nat n one_nat;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

val zero_nat : nat = Nat (0 : IntInf.int);

fun nth (x :: xs) n =
  (if equal_nata n zero_nat then x else nth xs (minus_nat n one_nat));

fun find uu [] = NONE
  | find p (x :: xs) = (if p x then SOME x else find p xs);

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun fun_upd A_ f a b = (fn x => (if eq A_ x a then b else f x));

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun member A_ [] y = false
  | member A_ (x :: xs) y = eq A_ x y orelse member A_ xs y;

fun distinct A_ [] = true
  | distinct A_ (x :: xs) = not (member A_ xs x) andalso distinct A_ xs;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun of_bool A_ true = one (one_zero_neq_one A_)
  | of_bool A_ false = zero (zero_zero_neq_one A_);

fun integer_of_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
  IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (of_bool
                        zero_neq_one_integer
                        b7, (2 : IntInf.int)), of_bool zero_neq_one_integer
         b6), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                   b5), (2 : IntInf.int)), of_bool
                     zero_neq_one_integer
                     b4), (2 : IntInf.int)), of_bool zero_neq_one_integer
       b3), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                 b2), (2 : IntInf.int)), of_bool
                   zero_neq_one_integer
                   b1), (2 : IntInf.int)), of_bool zero_neq_one_integer b0);

fun implode cs =
  (String.implode
    o List.map (fn k => if 0 <= k andalso k < 128 then (Char.chr o IntInf.toInt) k else raise Fail "Non-ASCII character in literal"))
    (map integer_of_char cs);

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun all_interval_nat p i j =
  less_eq_nat j i orelse p i andalso all_interval_nat p (suc i) j;

fun fst (x1, x2) = x1;

fun snd (x1, x2) = x2;

fun equal_option A_ NONE (SOME x2) = false
  | equal_option A_ (SOME x2) NONE = false
  | equal_option A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_option A_ NONE NONE = true;

fun match_pre x =
  (fn (xa, v) => fn s => equal_option equal_nat (s xa) (SOME v)) x;

fun bit_cut_integer k =
  (if ((k : IntInf.int) = (0 : IntInf.int)) then ((0 : IntInf.int), false)
    else let
           val (r, s) =
             IntInf.divMod (IntInf.abs k, IntInf.abs (2 : IntInf.int));
         in
           ((if IntInf.< ((0 : IntInf.int), k) then r
              else IntInf.- (IntInf.~ r, s)),
             ((s : IntInf.int) = (1 : IntInf.int)))
         end);

fun char_of_integer k = let
                          val (q0, b0) = bit_cut_integer k;
                          val (q1, b1) = bit_cut_integer q0;
                          val (q2, b2) = bit_cut_integer q1;
                          val (q3, b3) = bit_cut_integer q2;
                          val (q4, b4) = bit_cut_integer q3;
                          val (q5, b5) = bit_cut_integer q4;
                          val (q6, b6) = bit_cut_integer q5;
                          val a = bit_cut_integer q6;
                          val (_, aa) = a;
                        in
                          Chara (b0, b1, b2, b3, b4, b5, b6, aa)
                        end;

fun explode s =
  map char_of_integer
    ((List.map (fn c => let val k = Char.ord c in if k < 128 then IntInf.fromInt k else raise Fail "Non-ASCII character in literal" end) 
       o String.explode)
      s);

fun match_pres pres s = list_all (fn pre => match_pre pre s) pres;

fun astG problem = let
                     val (_, (_, (g, _))) = problem;
                   in
                     g
                   end;

fun lookup_operator x =
  (fn (_, (_, (_, delta))) => fn name =>
    find (fn (n, (_, (_, _))) => equal_lista equal_char n name) delta)
    x;

fun eff_enabled s = (fn (pres, (_, (_, _))) => match_pres pres s);

fun execute_opr x =
  (fn (_, (_, (effs, _))) => fn s =>
    let
      val effsa = filter (eff_enabled s) effs;
    in
      fold (fn (_, (xa, (_, v))) => fn sa => fun_upd equal_nat sa xa (SOME v))
        effsa s
    end)
    x;

fun match_implicit_pres effs s =
  list_all
    (fn a =>
      (case a of (_, (_, (NONE, _))) => true
        | (_, (x, (SOME v, _))) => equal_option equal_nat (s x) (SOME v)))
    effs;

fun enabled_opr x =
  (fn (_, (pres, (effs, _))) => fn s =>
    match_pres pres s andalso match_implicit_pres effs s)
    x;

fun simulate_plan problem (pi :: pi_s) s =
  (case lookup_operator problem pi of NONE => NONE
    | SOME pia =>
      (if enabled_opr pia s then simulate_plan problem pi_s (execute_opr pia s)
        else NONE))
  | simulate_plan problem [] s = SOME s;

fun astI problem = let
                     val (_, (i, (_, _))) = problem;
                   in
                     i
                   end;

fun size_list x = gen_length zero_nat x;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

fun initial_state problem =
  let
    val astIa = astI problem;
  in
    (fn v =>
      (if less_nat v (size_list astIa) then SOME (nth astIa v) else NONE))
  end;

fun check_plan problem pi_s =
  (case simulate_plan problem pi_s (initial_state problem) of NONE => false
    | SOME a => match_pres (astG problem) a);

fun astDom problem = let
                       val (d, (_, (_, _))) = problem;
                     in
                       d
                     end;

fun numVars problem = size_list (astDom problem);

fun numVals problem x = size_list (snd (snd (nth (astDom problem) x)));

fun wf_partial_state problem ps =
  distinct equal_nat (map fst ps) andalso
    list_all
      (fn (x, v) =>
        less_nat x (numVars problem) andalso less_nat v (numVals problem x))
      ps;

fun wf_operator problem =
  (fn (_, (pres, (effs, _))) =>
    wf_partial_state problem pres andalso
      (distinct equal_nat (map (fn (_, (v, (_, _))) => v) effs) andalso
        list_all
          (fn (epres, (x, (vp, v))) =>
            wf_partial_state problem epres andalso
              (less_nat x (numVars problem) andalso
                (less_nat v (numVals problem x) andalso
                  (case vp of NONE => true
                    | SOME va => less_nat va (numVals problem x)))))
          effs));

fun ast_delta problem = let
                          val (_, (_, (_, delta))) = problem;
                        in
                          delta
                        end;

fun well_formed problem =
  equal_nata (size_list (astI problem)) (numVars problem) andalso
    (all_interval_nat
       (fn x => less_nat (nth (astI problem) x) (numVals problem x)) zero_nat
       (numVars problem) andalso
      (wf_partial_state problem (astG problem) andalso
        (distinct (equal_list equal_char) (map fst (ast_delta problem)) andalso
          list_all (wf_operator problem) (ast_delta problem))));

fun verify_plan problem pi_s =
  (if well_formed problem
    then (if check_plan problem pi_s then Inr () else Inl "Invalid plan")
    else Inl "Problem not well formed");

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun nat_opt_of_integer i =
  (if IntInf.<= ((0 : IntInf.int), i) then SOME (nat_of_integer i) else NONE);

end; (*struct SASP_Checker_Exported*)
