theory utp_lift_pretty
  imports "utp_subst" "utp_lift_parser"
  keywords "utp_pretty" :: "thy_decl_block" and "no_utp_pretty" :: "thy_decl_block" and "utp_const" :: "thy_decl_block" and "utp_lift_notation" :: "thy_decl_block"
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

\<close>

ML \<open>
let val utp_tr_rules = map (fn (l, r) => Syntax.Print_Rule (("logic", l), ("logic", r)))
  [("U(t)" , "U(U(t))"),

(*
  ("_UTP (_uex x P)", "_uex x (_UTP P)"),
  ("_UTP (_uall x P)", "_uall x (_UTP P)"),
*)
  ("U(_ulens_ovrd e f A)", "_ulens_ovrd (U(e)) (U(f)) A"),

  ("_UTP (_SubstUpd m (_smaplet x v))", "_SubstUpd (_UTP m) (_smaplet x (_UTP v))"),
  ("_UTP (_Subst (_smaplet x v))", "_Subst (_smaplet x (_UTP v))"),
  ("_UTP (_subst e v x)", "_subst (_UTP e) (_UTP v) x"),

  ("U(\<sigma> \<dagger> e)", "U(\<sigma>) \<dagger> U(e)"),
  ("U(f x)" , "U(f) |> U(x)"),

  ("U(\<lambda> x. f)", "(\<lambda> x \<bullet> U(f))"),
  ("U(\<lambda> x. f)", "(\<lambda> x . U(f))"),

  ("U(f x)" , "CONST uop f U(x)"),
  ("U(f x y)" , "CONST bop f U(x) U(y)"),
  ("U(f x y z)" , "CONST trop f U(x) U(y) U(z)"),
  ("U(f x)" , "_UTP f (_UTP x)")]

  val utp_terminals = [@{const_syntax zero_class.zero}, @{const_syntax one_class.one}, @{const_syntax numeral}, @{const_syntax utrue}, @{const_syntax ufalse}];
  fun utp_consts ctx = @{syntax_const "_UTP"} :: filter (not o member (op =) utp_terminals) (map Lexicon.mark_const (Symtab.keys (NoLiftUTP.get (Proof_Context.theory_of ctx))));

  fun needs_mark ctx t = 
    case t of
      (Const (@{syntax_const "_free"}, _) $ Free (_, Type (\<^type_name>\<open>uexpr\<close>, ts))) => true |
      (Const (@{syntax_const "_free"}, _) 
       $ Free (_, Type (\<^syntax_const>\<open>_ignore_type\<close>, [Type (\<^type_name>\<open>uexpr\<close>, ts)]))) => true |
      Free (_, _) => true |
      _ => false;

  fun utp_mark_term ctx t = 
    if (needs_mark ctx t) then Const (@{syntax_const "_UTP"}, dummyT) $ t else t;

  fun mark_uexpr_leaf n = (n, fn _ => fn typ => fn ts => 
    case typ of 
    (Type (\<^type_name>\<open>uexpr\<close>, _)) => Const (@{syntax_const "_UTP"}, dummyT) $ Term.list_comb (Const (n, dummyT), ts) |
    (Type (\<^type_name>\<open>fun\<close>, [_, Type (\<^type_name>\<open>uexpr\<close>, _)])) => Const (@{syntax_const "_UTP"}, dummyT) $ Term.list_comb (Const (n, dummyT), ts) |
    _ => raise Match);

  fun insert_U args pre ctx ts =
    if (Library.foldl (fn (x, (i, y)) => (not (member (op =) args i) andalso needs_mark ctx y) orelse x) (false, (Library.map_index (fn x => x) ts))) 
    then Library.foldl1 (op $) (pre @ map_index (fn (i, t) => if (member (op =) args i) then t else utp_mark_term ctx t) ts)
    else raise Match;

  fun insert_const_U args c = insert_U args [Const (c, dummyT)];

  
  (* Function to register a constant c with n arguments as a lifted constant that should be
     aware of U notation. The values in opt are any arguments that should be ignored when
     checking for lifting. *)

  fun mk_remove_U_prtr c n opt =
    let open Ast
        val vars = map (fn i => Variable ("x" ^ string_of_int i)) (0 upto (n-1))
        val mvars = 
          map (fn i => 
                let val v = Variable ("x" ^ string_of_int i) in
                if (member (op =) opt i) then v else Appl (Constant @{syntax_const "_UTP"} :: [v])
                end
              ) (0 upto (n-1))
    in
    (Appl (Constant c :: vars), Appl (Constant c :: mvars))
    end;
    
  fun mk_lift_U_prtr c n opt =
    let 
      open Ast
      val (l, r) = mk_remove_U_prtr c n opt
    in
    if n = 0 then []
    else
    [      
    Syntax.Print_Rule (
    Appl [Constant @{syntax_const "_UTP"}
         , l],
    r)
    ]
    end;

  fun utp_remove_const_U thy (s, opt)  =
    let val Const (ct, ty) = Proof_Context.read_const {proper = true, strict = false} (Proof_Context.init_global thy) s 
        val cs = Lexicon.mark_const ct
        val n = length (fst (Term.strip_type ty)) 
        val args = map Value.parse_int opt in
    (Syntax.Print_Rule (mk_remove_U_prtr cs n args))
    end;

  fun add_utp_print_const (s, opt) thy =
    let val Const (ct, ty) = Proof_Context.read_const {proper = true, strict = false} (Proof_Context.init_global thy) s 
        val cs = Lexicon.mark_const ct
        val n = length (fst (Term.strip_type ty)) 
        val args = map Value.parse_int opt in
    (Sign.add_trrules (mk_lift_U_prtr cs n args) #> 
     Sign.print_translation [(cs, insert_const_U args cs)]
    ) thy
    end;


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
  

  fun uop_insert_U ctx (f :: ts) = insert_U [] [Const (@{const_syntax "uop"}, dummyT), f] ctx ts |
  uop_insert_U _ _ = raise Match;

  fun bop_insert_U ctx (f :: ts) = insert_U [] [Const (@{const_syntax "bop"}, dummyT), f] ctx ts |
  bop_insert_U _ _ = raise Match;

  fun trop_insert_U ctx (f :: ts) =
    insert_U [] [Const (@{const_syntax "trop"}, dummyT), f] ctx ts |
  trop_insert_U _ _ = raise Match;

  fun appl_insert_U ctx ts = insert_U [] [] ctx ts;

  val print_tr = [ (@{const_syntax "var"}, 
                    K (fn ts => if (ts = []) 
                                   then Const ("var", dummyT) 
                                   else Const (@{syntax_const "_UTP"}, dummyT) $ hd(ts)))
                 , (@{const_syntax "lit"}, 
                    K (fn ts => if (ts = []) 
                                   then Const ("lit", dummyT) 
                                   else Const (@{syntax_const "_UTP"}, dummyT) $ hd(ts)))
                 , (@{const_syntax "trop"}, trop_insert_U)
                 , (@{const_syntax "bop"}, bop_insert_U)
                 , (@{const_syntax "uop"}, uop_insert_U)
(*                 , (@{const_syntax "udisj"}, insert_const_U @{const_syntax udisj}) *)
                 , (@{const_syntax "uexpr_appl"}, appl_insert_U)];
  val ty_print_tr = map mark_uexpr_leaf utp_terminals;
  (* FIXME: We should also mark expressions that are free variables *)
  val no_print_tr = [ (@{syntax_const "_UTP"}, K (fn ts => Term.list_comb (@{print} hd ts, tl ts))) ];
  fun nolift_const thy (n, opt) =  
        let val Const (c, _) = Proof_Context.read_const {proper = true, strict = false} (Proof_Context.init_global thy) n 
        in NoLiftUTP.map (Symtab.update (c, (map Value.parse_int opt))) thy end;
  fun utp_lift_notation thy (n, args) =
    let val Const (c, _) = Proof_Context.read_const {proper = true, strict = false} (Proof_Context.init_global thy) n in
    (Lexicon.mark_const c, 
     fn ctx => fn ts => 
      let val ts' = map_index (fn (i, t) => if (not (member (op =) (map Value.parse_int args) i)) then utp_lift ctx (Term_Position.strip_positions t) else t) ts 
       in if (ts = ts') then raise Match else Term.list_comb (Const (c, dummyT), ts') end) 
      end; 
  in 
  Outer_Syntax.command @{command_keyword utp_lift_notation} "insert UTP parser quotes into existing notation"
    (Scan.repeat1 (Parse.term -- Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Scan.repeat1 Parse.number --| Parse.$$$ ")")) [])
     >> (fn ns => 
         Toplevel.theory 
         (fn thy => (Sign.parse_translation (map (utp_lift_notation thy) ns)
                    #> Sign.add_trrules ((map (utp_remove_const_U thy) ns))) thy)));

  Outer_Syntax.command @{command_keyword utp_pretty} "enable pretty printing of UTP expressions"
    (Scan.succeed (Toplevel.theory (Isar_Cmd.translations utp_tr_rules #> 
                                    Sign.typed_print_translation ty_print_tr #>
                                    Sign.print_translation print_tr
                                     )));
   (* FIXME: It actually isn't currently possible to disable pretty printing without destroying the term rewriting *)

   Outer_Syntax.command @{command_keyword no_utp_pretty} "disable pretty printing of UTP expressions"
    (Scan.succeed (Toplevel.theory (Isar_Cmd.no_translations utp_tr_rules #> Sign.print_translation no_print_tr)));

  Outer_Syntax.command @{command_keyword utp_const} "declare that certain UTP constants should not be lifted"
    (Scan.repeat1 (Parse.term -- Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Scan.repeat1 Parse.number --| Parse.$$$ ")")) [])
     >> (fn ns => 
         Toplevel.theory                                                           
         (fn thy => Library.foldl (fn (thy, n) => nolift_const thy n |> add_utp_print_const n) (thy, ns))))  
 end;
\<close>

utp_const
  plus minus uminus times divide inverse inverse_divide power power2
  subst_upd(1) usubst usubst_lookup(1) 
  utrue ufalse cond

term "\<^U>(3 + &x)"

utp_pretty

term "\<^U>(3 + &x)"

term "true"

term "U(P \<or> $x = 1 \<longrightarrow> false)"

term "U(true \<and> q)"

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

term "U($tr\<acute> = $tr @ [a] \<and> $ref \<subseteq> $i:ref\<acute> \<union> $j:ref\<acute> \<and> $x\<acute> = $x + 1)"

term "U(e\<lbrakk>v/x\<rbrakk>)"

term "U((length e)\<lbrakk>1+1/&x\<rbrakk>)"

term "U([x \<mapsto>\<^sub>s 1 + 2])"

end