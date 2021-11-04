(*  Title:      SpecCheck/generators/gen_term.ML
    Author:     Sebastian Willenbrink and Kevin Kappelmann TU Muenchen

Generators for terms and types.
*)
signature SPECCHECK_GEN_TERM = sig
  (* sort generators *)

  (*first parameter determines the number of classes to pick*)
  val sort : (int, 's) SpecCheck_Gen_Types.gen_state -> (class, 's) SpecCheck_Gen_Types.gen_state
    -> (sort, 's) SpecCheck_Gen_Types.gen_state
  val dummyS : (sort, 's) SpecCheck_Gen_Types.gen_state

  (* name generators *)
  (*parameters: a base name and a generator for the number of variants to choose from based on then
    passed base name*)
  val basic_name : string -> int SpecCheck_Gen_Types.gen -> string SpecCheck_Gen_Types.gen

  val indexname : (string, 's) SpecCheck_Gen_Types.gen_state ->
    (int, 's) SpecCheck_Gen_Types.gen_state -> (indexname, 's) SpecCheck_Gen_Types.gen_state

  (*a variant with base name "k"*)
  val type_name : int SpecCheck_Gen_Types.gen -> string SpecCheck_Gen_Types.gen

  (*creates a free type variable name from a passed basic name generator*)
  val tfree_name : (string, 's) SpecCheck_Gen_Types.gen_state ->
    (string, 's) SpecCheck_Gen_Types.gen_state
  (*chooses a variant with base name "'a"*)
  val tfree_name' : int SpecCheck_Gen_Types.gen -> string SpecCheck_Gen_Types.gen

  (*creates a type variable name from a passed basic name (e.g. "a") generator*)
  val tvar_name : (indexname, 's) SpecCheck_Gen_Types.gen_state ->
    (indexname, 's) SpecCheck_Gen_Types.gen_state
  (*chooses a variant with base name "'a"*)
  val tvar_name' : int SpecCheck_Gen_Types.gen -> int SpecCheck_Gen_Types.gen ->
    indexname SpecCheck_Gen_Types.gen

  (*chooses a variant with base name "c"*)
  val const_name : int SpecCheck_Gen_Types.gen -> string SpecCheck_Gen_Types.gen
  (*chooses a variant with base name "f"*)
  val free_name : int SpecCheck_Gen_Types.gen -> string SpecCheck_Gen_Types.gen
  (*chooses a variant with base name "v*)
  val var_name : int SpecCheck_Gen_Types.gen -> int SpecCheck_Gen_Types.gen ->
    indexname SpecCheck_Gen_Types.gen

  (* typ  generators *)

  val tfree : (string, 's) SpecCheck_Gen_Types.gen_state ->
    (sort, 's) SpecCheck_Gen_Types.gen_state -> (typ, 's) SpecCheck_Gen_Types.gen_state
  (*uses tfree_name' and dummyS to create a free type variable*)
  val tfree' : int SpecCheck_Gen_Types.gen -> typ SpecCheck_Gen_Types.gen

  val tvar : (indexname, 's) SpecCheck_Gen_Types.gen_state ->
    (sort, 's) SpecCheck_Gen_Types.gen_state -> (typ, 's) SpecCheck_Gen_Types.gen_state
  (*uses tvar' and dummyS to create a type variable*)
  val tvar' : int SpecCheck_Gen_Types.gen -> int SpecCheck_Gen_Types.gen ->
    typ SpecCheck_Gen_Types.gen

  (*atyp tfree_gen tvar_gen (weight_tfree, weight_tvar)*)
  val atyp : typ SpecCheck_Gen_Types.gen -> typ SpecCheck_Gen_Types.gen -> (int * int) ->
    typ SpecCheck_Gen_Types.gen
  (*uses tfree' and tvar' to create an atomic type*)
  val atyp' : int SpecCheck_Gen_Types.gen -> int SpecCheck_Gen_Types.gen -> (int * int) ->
    typ SpecCheck_Gen_Types.gen

  (*type' type_name_gen arity_gen tfree_gen tvar_gen (weight_type, weight_tfree, weight_tvar)*)
  val type' : string SpecCheck_Gen_Types.gen -> int SpecCheck_Gen_Types.gen ->
    typ SpecCheck_Gen_Types.gen -> typ SpecCheck_Gen_Types.gen ->
    (int * int * int) -> typ SpecCheck_Gen_Types.gen
  (*uses type_name to generate a type*)
  val type'' : int SpecCheck_Gen_Types.gen -> int SpecCheck_Gen_Types.gen ->
    typ SpecCheck_Gen_Types.gen -> typ SpecCheck_Gen_Types.gen -> (int * int * int) ->
    typ SpecCheck_Gen_Types.gen

  (*typ type_gen tfree_gen tvar_gen (wtype, wtfree, wtvar)*)
  val typ : typ SpecCheck_Gen_Types.gen -> typ SpecCheck_Gen_Types.gen ->
    typ SpecCheck_Gen_Types.gen -> (int * int * int) -> typ SpecCheck_Gen_Types.gen
  (*uses type'' for its type generator*)
  val typ' : int SpecCheck_Gen_Types.gen -> int SpecCheck_Gen_Types.gen ->
    typ SpecCheck_Gen_Types.gen -> typ SpecCheck_Gen_Types.gen -> (int * int * int) ->
    typ SpecCheck_Gen_Types.gen
  (*uses typ' with tfree' and tvar' parameters*)
  val typ'' : int SpecCheck_Gen_Types.gen -> int SpecCheck_Gen_Types.gen ->
    int SpecCheck_Gen_Types.gen -> (int * int * int) -> typ SpecCheck_Gen_Types.gen

  val dummyT : (typ, 's) SpecCheck_Gen_Types.gen_state

  (* term generators *)

  val const : (string, 's) SpecCheck_Gen_Types.gen_state ->
    (typ, 's) SpecCheck_Gen_Types.gen_state -> (term, 's) SpecCheck_Gen_Types.gen_state
  (*uses const_name and dummyT to create a constant*)
  val const' : int SpecCheck_Gen_Types.gen -> term SpecCheck_Gen_Types.gen

  val free : (string, 's) SpecCheck_Gen_Types.gen_state ->
    (typ, 's) SpecCheck_Gen_Types.gen_state -> (term, 's) SpecCheck_Gen_Types.gen_state
  (*uses free_name and dummyT to create a free variable*)
  val free' : int SpecCheck_Gen_Types.gen -> term SpecCheck_Gen_Types.gen

  val var : (indexname, 's) SpecCheck_Gen_Types.gen_state ->
    (typ, 's) SpecCheck_Gen_Types.gen_state -> (term, 's) SpecCheck_Gen_Types.gen_state
  (*uses var_name and dummyT to create a variable*)
  val var' : int SpecCheck_Gen_Types.gen -> int SpecCheck_Gen_Types.gen ->
    term SpecCheck_Gen_Types.gen

  val bound : (int, 's) SpecCheck_Gen_Types.gen_state -> (term, 's) SpecCheck_Gen_Types.gen_state

  (*aterm const_gen free_gen var_gen bound_gen
    (weight_const, weight_free, weight_var, weight_bound*)
  val aterm : term SpecCheck_Gen_Types.gen -> term SpecCheck_Gen_Types.gen ->
    term SpecCheck_Gen_Types.gen -> term SpecCheck_Gen_Types.gen -> (int * int * int * int) ->
    term SpecCheck_Gen_Types.gen
  (*uses const', free', and var' to create an atomic term*)
  val aterm' : int SpecCheck_Gen_Types.gen -> int SpecCheck_Gen_Types.gen ->
    (int * int * int * int) -> term SpecCheck_Gen_Types.gen

  (*term_tree f init_state - where "f height index state" returns "((term, num_args), new_state)" -
    generates a term by applying f to every node and expanding that node depending
    on num_args returned by f.
    Traversal order: function \<rightarrow> first argument \<rightarrow> ... \<rightarrow> last argument
    The tree is returned in its applicative term form: (...((root $ child1) $ child2) .. $ childn).

    Arguments of f:
    - height describes the distance from the root (starts at 0)
    - index describes the global index in that tree layer, left to right (0 \<le> index < width)
    - state is passed along according to above traversal order

    Return value of f:
    - term is the term whose arguments will be generated next.
    - num_args specifies how many arguments should be passed to the term.
    - new_state is passed along according to the traversal above.*)
  val term_tree : (int -> int -> (term * int, 's) SpecCheck_Gen_Types.gen_state) ->
    (term, 's) SpecCheck_Gen_Types.gen_state

  (*In contrast to term_tree, f now takes a (term, index_of_argument) list which specifies the path
    from the root to the current node.*)
  val term_tree_path : ((term * int) list -> (term * int, 's) SpecCheck_Gen_Types.gen_state) ->
    (term, 's) SpecCheck_Gen_Types.gen_state

end

structure SpecCheck_Gen_Term : SPECCHECK_GEN_TERM =
struct

structure Gen = SpecCheck_Gen_Base

fun sort size_gen = Gen.list size_gen
fun dummyS s = Gen.return Term.dummyS s

fun basic_name name num_variants_gen =
  num_variants_gen
  #>> (fn i => name ^ "_" ^ string_of_int i)

fun indexname basic_name_gen = Gen.zip basic_name_gen

fun type_name num_variants_gen = basic_name "k" num_variants_gen

fun tfree_name basic_name_gen = Gen.map (curry op^"'") basic_name_gen
fun tfree_name' num_variants_gen = tfree_name (basic_name "a" num_variants_gen)

fun tvar_name indexname_gen = Gen.map (curry op^"'" |> apfst) indexname_gen
fun tvar_name' num_variants_gen =
  tvar_name o indexname (basic_name "a" num_variants_gen)

fun const_name num_variants_gen = basic_name "c" num_variants_gen
fun free_name num_variants_gen = basic_name "v" num_variants_gen
fun var_name num_variants_gen = indexname (free_name num_variants_gen)

(* types *)

fun tfree name_gen = Gen.map TFree o Gen.zip name_gen
fun tfree' num_variants_gen =
  tfree_name' num_variants_gen
  |> (fn name_gen => tfree name_gen dummyS)

fun tvar idx_gen = Gen.map TVar o Gen.zip idx_gen
fun tvar' num_variants_gen =
  tvar_name' num_variants_gen
  #> (fn name_gen => tvar name_gen dummyS)

fun atyp tfree_gen tvar_gen (wtfree, wtvar) =
  Gen.one_ofWL [(wtfree, tfree_gen), (wtvar, tvar_gen)]
fun atyp' num_variants_gen = atyp (tfree' num_variants_gen) o tvar' num_variants_gen

fun type' type_name_gen arity_gen tfree_gen tvar_gen (weights as (wtype, wtfree, wtvar)) =
  (*eta-abstract to avoid strict evaluation, causing an infinite loop*)
  [(wtype, fn r => type' type_name_gen arity_gen tfree_gen tvar_gen weights r),
   (wtfree, fn r => tfree_gen r), (wtvar, fn r => tvar_gen r)]
  |> Gen.one_ofWL
  |> Gen.list arity_gen
  |> Gen.zip type_name_gen
  |> Gen.map Type

fun type'' num_variants_gen = type_name num_variants_gen |> type'

fun typ type_gen tfree_gen tvar_gen (wtype, wtfree, wtvar) =
  Gen.one_ofWL [(wtype, type_gen), (wtfree, tfree_gen), (wtvar, tvar_gen)]
fun typ' num_variants_gen arity_gen tfree_gen tvar_gen weights =
  typ (type'' num_variants_gen arity_gen tfree_gen tvar_gen weights) tfree_gen tvar_gen weights
fun typ'' num_variants_gen arity_gen =
  typ' num_variants_gen arity_gen (tfree' num_variants_gen) o tvar' num_variants_gen

fun dummyT s = Gen.return Term.dummyT s

(* terms *)

fun const name_gen = Gen.map Const o Gen.zip name_gen
fun const' num_variants_gen =
  const_name num_variants_gen
  |> (fn name_gen => const name_gen dummyT)

fun free name_gen = Gen.map Free o Gen.zip name_gen
fun free' num_variants_gen =
  free_name num_variants_gen
  |> (fn name_gen => free name_gen dummyT)

fun var idx_gen = Gen.map Var o Gen.zip idx_gen
fun var' num_variants_gen =
  var_name num_variants_gen
  #> (fn name_gen => var name_gen dummyT)

fun bound int_gen = Gen.map Bound int_gen

fun aterm const_gen free_gen var_gen bound_gen (wconst, wfree, wvar, wbound) =
  Gen.one_ofWL [(wconst, const_gen), (wfree, free_gen), (wvar, var_gen), (wbound, bound_gen)]
fun aterm' num_variants_gen index_gen =
  aterm (const' num_variants_gen) (free' num_variants_gen) (var' num_variants_gen index_gen)
    (bound num_variants_gen)

(*nth_map has no default*)
fun nth_map_default 0 f _ (x::xs) = f x :: xs
  | nth_map_default 0 f d [] = [f d]
  | nth_map_default n f d [] = replicate (n-1) d @ [f d]
  | nth_map_default n f d (x::xs) = x :: nth_map_default (n-1) f d xs

fun term_tree term_gen state =
  let
    fun nth_incr n = nth_map_default n (curry op+ 1) (~1)
    fun build_tree indices height state =
      let
        (*indices stores the number of nodes visited so far at each height*)
        val indices = nth_incr height indices
        val index = nth indices height
        (*generate the term for the current node*)
        val ((term, num_args), state) = term_gen height index state
        fun build_child (children, indices, state) =
          build_tree indices (height + 1) state
          |> (fn (child, indices, state) => (child :: children, indices, state))
        (*generate the subtrees for each argument*)
        val (children, indices, state) = fold (K build_child) (1 upto num_args) ([], indices, state)
      in (Term.list_comb (term, (rev children)), indices, state) end
  in
    build_tree [] 0 state
    |> (fn (term, _, state) => (term, state))
  end

fun term_tree_path f init_state =
  let
    fun build_tree path state =
      let
        val ((term, num_args), state) = f path state
        fun build_children i (args, state) =
          build_tree ((term, i) :: path) state
          |>> (fn x => x :: args)
        val (children, state) = fold build_children (0 upto num_args-1) ([], state)
      in (Term.list_comb (term, (rev children)), state) end
  in build_tree [] init_state end

end
