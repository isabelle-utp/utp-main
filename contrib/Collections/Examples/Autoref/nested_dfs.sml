
structure STArray = struct

datatype 'a Cell = Invalid | Value of 'a array;

exception AccessedOldVersion;

type 'a array = 'a Cell Unsynchronized.ref;

fun fromList l = Unsynchronized.ref (Value (Array.fromList l));
fun array (size, v) = Unsynchronized.ref (Value (Array.array (size,v)));
fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
fun sub (Unsynchronized.ref Invalid, idx) = raise AccessedOldVersion |
    sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx);
fun update (aref,idx,v) =
  case aref of
    (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
    (Unsynchronized.ref (Value a)) => (
      aref := Invalid;
      Array.update (a,idx,v);
      Unsynchronized.ref (Value a)
    );

fun length (Unsynchronized.ref Invalid) = raise AccessedOldVersion |
    length (Unsynchronized.ref (Value a)) = Array.length a

fun grow (aref, i, x) = case aref of 
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    let val len=Array.length a;
        val na = Array.array (len+i,x) 
    in
      aref := Invalid;
      Array.copy {src=a, dst=na, di=0};
      Unsynchronized.ref (Value na)
    end
    );

fun shrink (aref, sz) = case aref of
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    if sz > Array.length a then 
      raise Size
    else (
      aref:=Invalid;
      Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
    )
  );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:int) = array (n, a);

fun array_length (a:'a ArrayType) = length a;

fun array_get (a:'a ArrayType) (i:int) = sub (a, i);

fun array_set (a:'a ArrayType) (i:int) (e:'a) = update (a, i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:int) (x:'a) = grow (a, i, x);

fun array_shrink (a:'a ArrayType) (sz:int) = shrink (a,sz);

end;

end;

structure FArray = struct
  datatype 'a Cell = Value of 'a Array.array | Upd of (int*'a*'a Cell Unsynchronized.ref);

  type 'a array = 'a Cell Unsynchronized.ref;

  fun array (size,v) = Unsynchronized.ref (Value (Array.array (size,v)));
  fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
  fun fromList l = Unsynchronized.ref (Value (Array.fromList l));

  fun sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx) |
      sub (Unsynchronized.ref (Upd (i,v,cr)),idx) =
        if i=idx then v
        else sub (cr,idx);

  fun length (Unsynchronized.ref (Value a)) = Array.length a |
      length (Unsynchronized.ref (Upd (i,v,cr))) = length cr;

  fun realize_aux (aref, v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let
          val len = Array.length a;
          val a' = Array.array (len,v);
        in
          Array.copy {src=a, dst=a', di=0};
          Unsynchronized.ref (Value a')
        end
      ) |
      (Unsynchronized.ref (Upd (i,v,cr))) => (
        let val res=realize_aux (cr,v) in
          case res of
            (Unsynchronized.ref (Value a)) => (Array.update (a,i,v); res)
        end
      );

  fun realize aref =
    case aref of
      (Unsynchronized.ref (Value _)) => aref |
      (Unsynchronized.ref (Upd (i,v,cr))) => realize_aux(aref,v);

  fun update (aref,idx,v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let val nref=Unsynchronized.ref (Value a) in
          aref := Upd (idx,Array.sub(a,idx),nref);
          Array.update (a,idx,v);
          nref
        end
      ) |
      (Unsynchronized.ref (Upd _)) =>
        let val ra = realize_aux(aref,v) in
          case ra of
            (Unsynchronized.ref (Value a)) => Array.update (a,idx,v);
          ra
        end
      ;

  fun grow (aref, inc, x) = case aref of 
    (Unsynchronized.ref (Value a)) => (
      let val len=Array.length a;
          val na = Array.array (len+inc,x) 
      in
        Array.copy {src=a, dst=na, di=0};
        Unsynchronized.ref (Value na)
      end
      )
  | (Unsynchronized.ref (Upd _)) => (
    grow (realize aref, inc, x)
  );

  fun shrink (aref, sz) = case aref of
    (Unsynchronized.ref (Value a)) => (
      if sz > Array.length a then 
        raise Size
      else (
        Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
      )
    ) |
    (Unsynchronized.ref (Upd _)) => (
      shrink (realize aref,sz)
    );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:int) = array (n, a);

fun array_length (a:'a ArrayType) = length a;

fun array_get (a:'a ArrayType) (i:int) = sub (a, i);

fun array_set (a:'a ArrayType) (i:int) (e:'a) = update (a, i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:int) (x:'a) = grow (a, i, x);

fun array_shrink (a:'a ArrayType) (sz:int) = shrink (a,sz);

fun array_get_oo (d:'a) (a:'a ArrayType) (i:int) = 
  sub (a,i) handle Subscript => d

fun array_set_oo (d:(unit->'a ArrayType)) (a:'a ArrayType) (i:int) (e:'a) = 
  update (a, i, e) handle Subscript => d ()

end;
end;




structure HPY_new : sig
  type 'a equal
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
  datatype nat = Nat of IntInf.int
  datatype num = One | Bit0 of num | Bit1 of num
  val map : ('a -> 'b) -> 'a list -> 'b list
  val fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  type 'a ord
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  val integer_of_nat : nat -> IntInf.int
  val less_eq_nat : nat -> nat -> bool
  val less_nat : nat -> nat -> bool
  val ord_nat : nat ord
  val one_nat : nat
  val foldli : 'a list -> ('b -> bool) -> ('a -> 'b -> 'b) -> 'b -> 'b
  val equal_nata : nat -> nat -> bool
  val equal_nat : nat equal
  val plus_nat : nat -> nat -> nat
  val ord_integer : IntInf.int ord
  val max : 'a ord -> 'a -> 'a -> 'a
  val minus_nat : nat -> nat -> nat
  val times_nat : nat -> nat -> nat
  datatype 'a dres = DSUCCEEDi | DFAILi | DRETURN of 'a
  val equal_list : 'a equal -> 'a list -> 'a list -> bool
  datatype 'a blue_witness = NO_CYC | Reach of 'a * 'a list * 'a * 'a list |
    Circ of 'a * 'a list * 'a list
  val dbind : 'a dres -> ('a -> 'b dres) -> 'b dres
  val array_set :
    'a FArray.IsabelleMapping.ArrayType ->
      nat -> 'a -> 'a FArray.IsabelleMapping.ArrayType
  val iam_empty : unit -> ('a option) FArray.IsabelleMapping.ArrayType
  val the_res : 'a dres -> 'a
  val equal_blue_witness :
    'a equal -> 'a blue_witness -> 'a blue_witness -> bool
  val map2set_insert : ('a -> unit -> 'b -> 'c) -> 'a -> 'b -> 'c
  val nat_of_integer : IntInf.int -> nat
  val iam_increment : nat -> nat -> nat
  val array_set_oo :
    (unit -> 'a FArray.IsabelleMapping.ArrayType) ->
      'a FArray.IsabelleMapping.ArrayType ->
        nat -> 'a -> 'a FArray.IsabelleMapping.ArrayType
  val array_length : 'a FArray.IsabelleMapping.ArrayType -> nat
  val array_grow :
    'a FArray.IsabelleMapping.ArrayType ->
      nat -> 'a -> 'a FArray.IsabelleMapping.ArrayType
  val iam_update :
    nat ->
      'a -> ('a option) FArray.IsabelleMapping.ArrayType ->
              ('a option) FArray.IsabelleMapping.ArrayType
  val array_get_oo : 'a -> 'a FArray.IsabelleMapping.ArrayType -> nat -> 'a
  val iam_alpha :
    ('a option) FArray.IsabelleMapping.ArrayType -> nat -> 'a option
  val iam_lookup :
    nat -> ('a option) FArray.IsabelleMapping.ArrayType -> 'a option
  val iam_delete :
    nat ->
      ('a option) FArray.IsabelleMapping.ArrayType ->
        ('a option) FArray.IsabelleMapping.ArrayType
  val prep_wit_blue : 'a equal -> 'a -> 'a blue_witness -> 'a blue_witness
  val init_wit_blue : 'a equal -> 'a -> ('a list * 'a) option -> 'a blue_witness
  val map2set_memb : ('a -> 'b -> 'c option) -> 'a -> 'b -> bool
  val is_None : 'a option -> bool
  val red_init_witness : 'a -> 'a -> ('a list * 'a) option
  val prep_wit_red : 'a -> ('a list * 'a) option -> ('a list * 'a) option
  val red_dfs_impl_0 :
    (unit option) FArray.IsabelleMapping.ArrayType ->
      (nat -> nat list) ->
        (unit option) FArray.IsabelleMapping.ArrayType * nat ->
          ((unit option) FArray.IsabelleMapping.ArrayType *
            (nat list * nat) option)
            dres
  val red_dfs_impl :
    nat ->
      (unit option) FArray.IsabelleMapping.ArrayType ->
        (unit option) FArray.IsabelleMapping.ArrayType ->
          (nat -> nat list) ->
            (unit option) FArray.IsabelleMapping.ArrayType *
              (nat list * nat) option
  val ndfs_impl_0 :
    (nat -> nat list) ->
      (unit option) FArray.IsabelleMapping.ArrayType ->
        (unit option) FArray.IsabelleMapping.ArrayType *
          ((unit option) FArray.IsabelleMapping.ArrayType *
            ((unit option) FArray.IsabelleMapping.ArrayType * nat)) ->
          ((unit option) FArray.IsabelleMapping.ArrayType *
            ((unit option) FArray.IsabelleMapping.ArrayType *
              ((unit option) FArray.IsabelleMapping.ArrayType *
                nat blue_witness)))
            dres
  val extract_res : 'a blue_witness -> ('a * ('a list * 'a list)) option
  val ndfs_impl :
    (nat -> nat list) ->
      (unit option) FArray.IsabelleMapping.ArrayType ->
        nat -> (nat * (nat list * nat list)) option
  val glist_member : ('a -> 'a -> bool) -> 'a -> 'a list -> bool
  val glist_insert : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list
  val acc_of_list_impl :
    nat list -> (unit option) FArray.IsabelleMapping.ArrayType
  val succ_of_list_impl : (nat * nat) list -> nat -> nat list
  val acc_of_list_impl_int :
    IntInf.int list -> (unit option) FArray.IsabelleMapping.ArrayType
  val succ_of_list_impl_int : (IntInf.int * IntInf.int) list -> nat -> nat list
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

datatype nat = Nat of IntInf.int;

datatype num = One | Bit0 of num | Bit1 of num;

fun map f [] = []
  | map f (x :: xs) = f x :: map f xs;

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun integer_of_nat (Nat x) = x;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

val one_nat : nat = Nat (1 : IntInf.int);

fun foldli [] c f sigma = sigma
  | foldli (x :: xs) c f sigma =
    (if c sigma then foldli xs c f (f x sigma) else sigma);

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

val equal_nat = {equal = equal_nata} : nat equal;

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun minus_nat m n =
  Nat (max ord_integer 0 (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun times_nat m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

datatype 'a dres = DSUCCEEDi | DFAILi | DRETURN of 'a;

fun equal_list A_ (a :: lista) [] = false
  | equal_list A_ [] (a :: lista) = false
  | equal_list A_ (aa :: listaa) (a :: lista) =
    eq A_ aa a andalso equal_list A_ listaa lista
  | equal_list A_ [] [] = true;

datatype 'a blue_witness = NO_CYC | Reach of 'a * 'a list * 'a * 'a list |
  Circ of 'a * 'a list * 'a list;

fun dbind DFAILi f = DFAILi
  | dbind DSUCCEEDi f = DSUCCEEDi
  | dbind (DRETURN x) f = f x;

fun array_set a = FArray.IsabelleMapping.array_set a o integer_of_nat;

fun iam_empty x = (fn _ => FArray.IsabelleMapping.array_of_list []) x;

fun the_res (DRETURN x) = x;

fun equal_blue_witness A_ (Circ (v, list1a, list2a))
  (Reach (v1, list1, v2, list2)) = false
  | equal_blue_witness A_ (Reach (v1, list1a, v2, list2a))
    (Circ (v, list1, list2)) = false
  | equal_blue_witness A_ (Circ (v, list1, list2)) NO_CYC = false
  | equal_blue_witness A_ NO_CYC (Circ (v, list1, list2)) = false
  | equal_blue_witness A_ (Reach (v1, list1, v2, list2)) NO_CYC = false
  | equal_blue_witness A_ NO_CYC (Reach (v1, list1, v2, list2)) = false
  | equal_blue_witness A_ (Circ (va, list1a, list2a)) (Circ (v, list1, list2)) =
    eq A_ va v andalso
      (equal_list A_ list1a list1 andalso equal_list A_ list2a list2)
  | equal_blue_witness A_ (Reach (v1a, list1a, v2a, list2a))
    (Reach (v1, list1, v2, list2)) =
    eq A_ v1a v1 andalso
      (equal_list A_ list1a list1 andalso
        (eq A_ v2a v2 andalso equal_list A_ list2a list2))
  | equal_blue_witness A_ NO_CYC NO_CYC = true;

fun map2set_insert i k s = i k () s;

fun nat_of_integer k = Nat (max ord_integer 0 k);

fun iam_increment l idx =
  max ord_nat (minus_nat (plus_nat idx one_nat) l)
    (plus_nat (times_nat (nat_of_integer (2 : IntInf.int)) l)
      (nat_of_integer (3 : IntInf.int)));

fun array_set_oo f a = FArray.IsabelleMapping.array_set_oo f a o integer_of_nat;

fun array_length x = (nat_of_integer o FArray.IsabelleMapping.array_length) x;

fun array_grow a = FArray.IsabelleMapping.array_grow a o integer_of_nat;

fun iam_update k v a =
  array_set_oo
    (fn _ =>
      let
        val l = array_length a;
      in
        array_set (array_grow a (iam_increment l k) NONE) k (SOME v)
      end)
    a k (SOME v);

fun array_get_oo x a = FArray.IsabelleMapping.array_get_oo x a o integer_of_nat;

fun iam_alpha a i = array_get_oo NONE a i;

fun iam_lookup k a = iam_alpha a k;

fun iam_delete k a = array_set_oo (fn _ => a) a k NONE;

fun prep_wit_blue A_ u0 NO_CYC = NO_CYC
  | prep_wit_blue A_ u0 (Reach (v, pa, u, p)) =
    (if eq A_ u0 u then Circ (v, pa @ u :: p, u0 :: p)
      else Reach (v, pa, u, u0 :: p))
  | prep_wit_blue A_ u0 (Circ (v, pc, pr)) = Circ (v, pc, u0 :: pr);

fun init_wit_blue A_ u0 NONE = NO_CYC
  | init_wit_blue A_ u0 (SOME (p, u)) =
    (if eq A_ u u0 then Circ (u0, p, []) else Reach (u0, p, u, []));

fun map2set_memb l k s = (case l k s of NONE => false | SOME _ => true);

fun is_None a = (case a of NONE => true | SOME _ => false);

fun red_init_witness u v = SOME ([u], v);

fun prep_wit_red v NONE = NONE
  | prep_wit_red v (SOME (p, u)) = SOME (v :: p, u);

fun red_dfs_impl_0 onstack e x =
  let
    val (a, b) = x;
    val xa = map2set_insert iam_update b a;
  in
    dbind (foldli (e b)
            (fn aa =>
              (case aa of DSUCCEEDi => false | DFAILi => false
                | DRETURN ab => is_None ab))
            (fn xb => fn s =>
              dbind s
                (fn _ =>
                  (if map2set_memb iam_lookup xb onstack
                    then DRETURN (red_init_witness b xb) else DRETURN NONE)))
            (DRETURN NONE))
      (fn xb =>
        (case xb
          of NONE =>
            foldli (e b)
              (fn aa =>
                (case aa of DSUCCEEDi => false | DFAILi => false
                  | DRETURN (_, ab) => is_None ab))
              (fn xc => fn s =>
                dbind s
                  (fn (aa, _) =>
                    (if not (map2set_memb iam_lookup xc aa)
                      then dbind (red_dfs_impl_0 onstack e (aa, xc))
                             (fn (ab, bb) => DRETURN (ab, prep_wit_red b bb))
                      else DRETURN (aa, NONE))))
              (DRETURN (xa, NONE))
          | SOME _ => DRETURN (xa, xb)))
  end;

fun red_dfs_impl u v onstack e = the_res (red_dfs_impl_0 onstack e (v, u));

fun ndfs_impl_0 succi ai x =
  let
    val (a, (aa, (ab, bb))) = x;
    val xa = map2set_insert iam_update bb a;
    val xb = map2set_insert iam_update bb ab;
  in
    dbind (foldli (succi bb)
            (fn ac =>
              (case ac of DSUCCEEDi => false | DFAILi => false
                | DRETURN (_, (_, (_, xj))) =>
                  equal_blue_witness equal_nat xj NO_CYC))
            (fn xc => fn s =>
              dbind s
                (fn (ac, (ad, (ae, be))) =>
                  (if not (map2set_memb iam_lookup xc ac)
                    then dbind (ndfs_impl_0 succi ai (ac, (ad, (ae, xc))))
                           (fn (af, (ag, (ah, bh))) =>
                             DRETURN
                               (af, (ag, (ah, prep_wit_blue equal_nat bb bh))))
                    else DRETURN (ac, (ad, (ae, be))))))
            (DRETURN (xa, (aa, (xb, NO_CYC)))))
      (fn (ac, (ad, (ae, be))) =>
        dbind (if equal_blue_witness equal_nat be NO_CYC andalso
                    map2set_memb iam_lookup bb ai
                then dbind (DRETURN (red_dfs_impl bb ad ae succi))
                       (fn (af, bf) =>
                         DRETURN (af, init_wit_blue equal_nat bb bf))
                else DRETURN (ad, be))
          (fn (af, bf) =>
            let
              val xe = iam_delete bb ae;
            in
              DRETURN (ac, (af, (xe, bf)))
            end))
  end;

fun extract_res cyc =
  (case cyc of NO_CYC => NONE | Reach (_, _, _, _) => NONE
    | Circ (v, pc, pr) => SOME (v, (pc, pr)));

fun ndfs_impl succi ai s =
  the_res
    (dbind
      (ndfs_impl_0 succi ai (iam_empty (), (iam_empty (), (iam_empty (), s))))
      (fn (_, (_, (_, bb))) => DRETURN (extract_res bb)));

fun glist_member eq x [] = false
  | glist_member eq x (y :: ys) = eq x y orelse glist_member eq x ys;

fun glist_insert eq x xs = (if glist_member eq x xs then xs else x :: xs);

fun acc_of_list_impl x =
  (fn xa => fold (map2set_insert iam_update) xa (iam_empty ())) x;

fun succ_of_list_impl x =
  (fn xa =>
    let
      val xaa =
        fold (fn (xaa, xb) => fn xc =>
               (case iam_alpha xc xaa of NONE => iam_update xaa [xb] xc
                 | SOME xd =>
                   iam_update xaa (glist_insert equal_nata xb xd) xc))
          xa (iam_empty ());
    in
      (fn xb => (case iam_alpha xaa xb of NONE => [] | SOME xc => xc))
    end)
    x;

fun acc_of_list_impl_int x = (acc_of_list_impl o map nat_of_integer) x;

fun succ_of_list_impl_int x =
  (succ_of_list_impl o map (fn (u, v) => (nat_of_integer u, nat_of_integer v)))
    x;

end; (*struct HPY_new*)
