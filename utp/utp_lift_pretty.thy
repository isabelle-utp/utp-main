theory utp_lift_pretty
  imports "utp_pred" "utp_lift_parser"
  keywords "utp_pretty" :: "thy_decl_block" and "no_utp_pretty" :: "thy_decl_block"
begin

subsection \<open> Pretty Printer\<close>

text \<open> The pretty printer infers when a HOL expression is actually a UTP expression by determing
  whether it contains operators like @{const bop}, @{const lit} etc. If so, it inserts the syntactic
  UTP quote defined above and then pushes these upwards through the expression syntax as far as possible, removing
  expression operators along the way. In this way, lifted HOL expressions are printed exactly as the
  HOL expression with a quote around.

  There are two phases to this implementation. Firstly, a collection of print translation functions
  for each of the combinators for functions, such as @{const uop} and @{const bop} insert a UTP quote
  for each subexpression that is not also headed by such a combinator. This is effectively trying
  to find ``leaf nodes'' in an expression. Secondly, a set of translation rules push the UTP quotes
  upwards, combining where necessary, to the highest possible level, removing the expression operators
  as they go.

  We manifest the pretty printer through two commands that enable and disable it. Disabling allows
  us to inspect the syntactic structure of a term.
 \<close>

(* FIXME: We need a general way of recognising which functions should insert term markings. For example,
  in the case of plus, we may encounter a term like $U(x) + y$, which should be treated as a UTP
  expression and thus turned into $U(x + y)$. We can't do this in general though, because terms 
  with meta-implication should not be dealt with in this way. We really need a mechanism for
  specifying when these ``hints'' should be inserted. *)

ML \<open>
let val utp_tr_rules = map (fn (l, r) => Syntax.Print_Rule (("logic", l), ("logic", r)))
  [("U(t)" , "U(U(t))"),
  ("U(x \<or> y)", "U(x) \<or> U(y)"),
  ("U(x \<and> y)", "U(x) \<and> U(y)"),
  ("U(x \<Rightarrow> y)", "U(x) \<Rightarrow> U(y)"),
  ("U(\<not> e)", "\<not> U(e)"),
  ("U(x + y)", "U(x) + U(y)"),
  ("U(x - y)", "U(x) - U(y)"),
  ("U(- e)", "- U(e)"),
  ("U(x * y)", "U(x) * U(y)"),
  ("U(x / y)", "U(x) / U(y)"),
  ("U(_ulens_ovrd e f A)", "_ulens_ovrd (U(e)) (U(f)) A"),
  ("_UTP (_SubstUpd m (_smaplet x v))", "_SubstUpd (_UTP m) (_smaplet x (_UTP v))"),
  ("_UTP (_Subst (_smaplet x v))", "_Subst (_smaplet x (_UTP v))"),
  ("U(f x)" , "U(f) |> U(x)"),
(*  ("U(f x)" , "f |> U(x)"),
  ("U(f x)" , "U(f) |> x"), *)
  ("U(\<lambda> x. f)", "(\<lambda> x \<bullet> U(f))"),
  ("U(\<lambda> x. f)", "(\<lambda> x . U(f))"),
  ("U(f x)" , "CONST uop f U(x)"),
  ("U(f x y)" , "CONST bop f U(x) U(y)"),
  ("U(f x y z)" , "CONST trop f U(x) U(y) U(z)"),
(*
  ("U(f x y z)" , "f U(x) U(y) U(z)"),
  ("U(f x y)" , "f U(x) U(y)"),
  ("U(f x y z)" , "f x y U(z)"),
  ("U(f x y z)" , "f x U(y) z"),
  ("U(f x y z)" , "f U(x) y z"),

  ("U(f x y)" , "f x U(y)"),
  ("U(f x y)" , "f U(x) y"),
  ("U(f x)" , "f U(x)"),
  ("U(f x)" , "_UTP f x") *)
  ("U(f x)" , "_UTP f (_UTP x)")]

  val utp_terminals = [@{const_syntax zero_class.zero}, @{const_syntax one_class.one}, @{const_syntax numeral}, @{const_syntax utrue}, @{const_syntax ufalse}];
  fun utp_consts ctx = @{syntax_const "_UTP"} :: filter (not o member (op =) utp_terminals) (map Lexicon.mark_const (Symtab.keys (NoLiftUTP.get (Proof_Context.theory_of ctx))));

(*
  fun utp_consts ctx =
  [@{syntax_const "_UTP"}, 
     @{const_syntax lit}, 
     @{const_syntax var},
     @{const_syntax uop}, 
     @{const_syntax bop}, 
     @{const_syntax trop}, 
     @{const_syntax qtop},
(*     @{const_syntax subst_upd}, *)
     @{const_syntax plus},
     @{const_syntax minus},
     @{const_syntax times},
     @{const_syntax divide}];
*)
  
  fun needs_mark ctx t = 
    case t of
      (Const (@{syntax_const "_free"}, _) $ Free (_, Type (\<^type_name>\<open>uexpr\<close>, _))) => true |
(*      (Const (c , _), _) => (not (member (op =) (utp_consts ctx) c)) | *)
      _ => false;

  fun utp_mark_term ctx t = 
    if (needs_mark ctx t) then Const (@{syntax_const "_UTP"}, dummyT) $ t else t;

  fun mark_uexpr_leaf n = (n, fn _ => fn typ => fn ts => 
    case typ of 
    (Type (\<^type_name>\<open>uexpr\<close>, _)) => Const (@{syntax_const "_UTP"}, dummyT) $ Term.list_comb (Const (n, dummyT), ts) |
    (Type (\<^type_name>\<open>fun\<close>, [_, Type (\<^type_name>\<open>uexpr\<close>, _)])) => Const (@{syntax_const "_UTP"}, dummyT) $ Term.list_comb (Const (n, dummyT), ts) |
    _ => raise Match);

  fun insert_U ctx pre ts =
    if (Library.foldl (fn (x, y) => needs_mark ctx y orelse x) (false, ts)) 
    then Library.foldl1 (op $) (pre @ map (utp_mark_term ctx) ts)
    else raise Match;

  fun uop_insert_U ctx (f :: ts) = insert_U ctx [Const (@{const_syntax "uop"}, dummyT), f] ts |
  uop_insert_U _ _ = raise Match;

  fun bop_insert_U ctx (f :: ts) = insert_U ctx [Const (@{const_syntax "bop"}, dummyT), f] ts |
  bop_insert_U _ _ = raise Match;

  fun trop_insert_U ctx (f :: ts) =
    insert_U ctx [Const (@{const_syntax "trop"}, dummyT), f] ts |
  trop_insert_U _ _ = raise Match;

  fun appl_insert_U ctx ts = insert_U ctx [] ts;

  fun disj_insert_U ctx ts = insert_U ctx [Const (@{const_syntax udisj}, dummyT)] ts;

  val print_tr = [ (@{const_syntax "var"}, K (fn ts => Const (@{syntax_const "_UTP"}, dummyT) $ hd(ts)))
                 , (@{const_syntax "lit"}, K (fn ts => Const (@{syntax_const "_UTP"}, dummyT) $ hd(ts)))
                 , (@{const_syntax "trop"}, trop_insert_U)
                 , (@{const_syntax "bop"}, bop_insert_U)
                 , (@{const_syntax "uop"}, uop_insert_U)
                 , (@{const_syntax "udisj"}, disj_insert_U)
                 , (@{const_syntax "uexpr_appl"}, appl_insert_U)];
  val ty_print_tr = [mark_uexpr_leaf @{const_syntax utrue},
                     mark_uexpr_leaf @{const_syntax ufalse},
                     mark_uexpr_leaf @{const_syntax zero_class.zero},
                     mark_uexpr_leaf @{const_syntax one_class.one},
                     mark_uexpr_leaf @{const_syntax numeral}];
  val no_print_tr = [ (@{syntax_const "_UTP"}, K (fn ts => Term.list_comb (hd ts, tl ts))) ];
in Outer_Syntax.command @{command_keyword utp_pretty} "enable pretty printing of UTP expressions" 
    (Scan.succeed (Toplevel.theory (Isar_Cmd.translations utp_tr_rules #> 
                                    Sign.typed_print_translation ty_print_tr #>
                                    Sign.print_translation print_tr
                                     )));
   (* FIXME: It actually isn't currently possible to disable pretty printing without destroying the term rewriting *)
   Outer_Syntax.command @{command_keyword no_utp_pretty} "disable pretty printing of UTP expressions"
    (Scan.succeed (Toplevel.theory (Isar_Cmd.no_translations utp_tr_rules #> Sign.print_translation no_print_tr)))
 end

\<close>

ML \<open>@{syntax_const "_UTP"}\<close>


term "\<^U>(3 + &x)"


utp_pretty


term "\<^U>(3 + &x)"

term "\<^U>(1 + &x)"

term "\<guillemotleft>x\<guillemotright> + $y"

term "\<guillemotleft>x\<guillemotright> + $y"

term "\<^U>(&v < 0)"

term "\<^U>(&v > 0)"

term "U($y = 5)"

term "\<^U>($y\<acute> = 1 + $y)"

term "U($x + $y + $z + $u / $f\<acute>)"

term "\<^U>($f x)"

term "U($f $\<^bold>v\<acute>)"

term "e \<oplus> f on A"

term "U($x = v)"

term "true"

term "U(P \<or> $x = 1 \<Rightarrow> false)"

term "U($tr\<acute> = $tr @ [a] \<and> $ref \<subseteq> $i:ref\<acute> \<union> $j:ref\<acute> \<and> $x\<acute> = $x + 1)"

end