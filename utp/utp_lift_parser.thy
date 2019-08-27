section \<open> Lifting Parser and Pretty Printer \<close>

theory utp_lift_parser
  imports "utp_rel"
  keywords "no_utp_lift" :: "thy_decl_block" and "utp_pretty" :: "thy_decl_block" and "no_utp_pretty" :: "thy_decl_block"
begin

subsection \<open> Parser \<close>

text \<open> Here, we derive a parser for UTP expressions that mimicks (and indeed reuses) the syntax of
  HOL expressions. It has two main features: (1) it lifts HOL functions into UTP expressions using 
  the @{term "(|>)"} construct; and (2) it recognises when a free variable is a declared lens
  and treats it as a UTP variable, whilst lifting HOL variables. The parser therefore allows
  free mixing of HOL operators and lenses. 

  Sometimes it is necessary that operators are handled
  in a special way however. We, therefore, first create a mutable data structure to store the names 
  of constants that should not be lifted, and arguments of those constants that should not be 
  further processed. \<close>

ML \<open>
structure NoLiftUTP = Theory_Data
  (type T = int list Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true));
   
val _ =
  let fun nolift_const thy (n, opt) =  
          let val Const (c, _) = Proof_Context.read_const {proper = true, strict = false} (Proof_Context.init_global thy) n 
          in NoLiftUTP.map (Symtab.update (c, (map Value.parse_int opt))) thy end
  in

  Outer_Syntax.command @{command_keyword no_utp_lift} "declare that certain constants should not be lifted"
    (Scan.repeat1 (Parse.term -- Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Scan.repeat1 Parse.number --| Parse.$$$ ")")) [])
     >> (fn ns => 
         Toplevel.theory 
         (fn thy => Library.foldl (fn (thy, n) => nolift_const thy n) (thy, ns))))  
  end
\<close>


text \<open> The core UTP operators should not be lifted. Certain operators have arguments that also
  should not be processed further by expression lifting. For example, in a substitution update
  @{term "subst_upd \<sigma> x v"}, the lens x (i.e. the second argument) should not be lifted as its 
  target is not an expression. Consequently, constants names in the command @{command no_utp_lift}  
  can be accompanied by a list of numbers stating the arguments that should be not be further
  processed. \<close>

no_utp_lift
  uexpr_appl uop (0) bop (0) trop (0) qtop (0) lit (0)
  Groups.zero Groups.one plus uminus minus times divide
  shEx shAll unot uconj udisj uimpl utrue ufalse 
  usubst subst UINF USUP
  var (0) in_var (0) out_var (0) lift_pre lift_post
  cond rcond uassigns id seqr useq uskip rcond rassume rassert
  rgcmd while_top while_bot while_inv while_inv_bot while_vrt
  subst_upd (1) numeral (0) refineBy ZedSetCompr

text \<open> The following function takes a parser, but not-yet type-checked term, and wherever it
  encounters an application, it inserts a UTP expression operator. Any operators that have
  been marked in the above structure will not be lifted. In addition, when it encounters a constant
  or free variable it will use the type system to determine whether is has a lens type. If it does,
  then it constructs a UTP variable expression; otherwise it constructs a literal.

  FIXME: Actually, this test is a little too coarse for some situations. For example, when the lens
  is bound by a $\lambda$-abstraction the type data is not available, and so it will not necessarily
  be recognised as a lens. This could either be fixed by adding proper syntactic procedure for
  determining lenses, or else by using type inference wrt. the bound lambda term.
\<close>

ML \<open> 

  val list_appl = Library.foldl (fn (f, x) => Const (@{const_name "uexpr_appl"}, dummyT) $ f $ x);

  fun utp_lift_aux ctx (Const (n', t), args) =
    let val n = (if (Lexicon.is_marked n') then Lexicon.unmark_const n' else n') in
    \<comment> \<open> If the leading constructor is an already lifted UTP variable...\<close>
    if ((n = @{const_name "var"}) andalso (length args > 0))
    \<comment> \<open> ... then we take the first argument as the variable contents, and apply the remaining arguments \<close>
    then list_appl (Const (n, t) $ hd args, map (utp_lift ctx) (tl args))
    \<comment> \<open> Otherwise, if the name of the given constant is in the ``no lifting'' list... \<close>
    else if (member (op =) (Symtab.keys (NoLiftUTP.get (Proof_Context.theory_of ctx))) n)
      \<comment> \<open> ... then do not lift it, and also do not process any arguments in the given list of integers. \<close>
      then let val (SOME aopt) = Symtab.lookup (NoLiftUTP.get (Proof_Context.theory_of ctx)) n in
           Term.list_comb (Const (n, t), map_index (fn (i, t) => if (member (op =) aopt i) then t else utp_lift ctx t) args) end
      \<comment> \<open> If the name is not in the ``no lifting'' list... \<close>
      else
        list_appl
        (case (Type_Infer_Context.const_type ctx n) of
          \<comment> \<open> ... and it's a lens, then lift it as a UTP variable... \<close>
          SOME (Type (\<^type_name>\<open>lens_ext\<close>, _)) => Const (@{const_name var}, dummyT) $ (Const (@{const_name pr_var}, dummyT) $ Const (n', t)) |
          \<comment> \<open> ... or, if it's a UTP expression already, then leave it alone... \<close>
          SOME (Type (\<^type_name>\<open>uexpr\<close>, _)) => Const (n, t) |
          \<comment> \<open> ...otherwise, lift it to a HOL literal. \<close>
          _ => Const (@{const_name lit}, dummyT) $ Const (n, t)
        , map (utp_lift ctx) args)
    end
    |

  \<comment> \<open> Free variables are handled similarly to constants; that they are usually
      lifted. The exception is when the free variable actually refers to a constant,
      which can occur if lifting is applied during syntax translation. In this 
      case, we convert it to a constant first and then apply lifting to it. \<close>
  utp_lift_aux ctx (Free (n, t), args) =
    \<comment> \<open> We first extract the constant table from the context. \<close>
    let val consts = (Proof_Context.consts_of ctx)
        val {const_space, ...} = Consts.dest consts
        \<comment> \<open> The name must be internalised in case it needs qualifying. \<close>
        val c = Consts.intern consts n in
        \<comment> \<open> If the name refers to a declared constant, then we lift it as a constant. \<close>
        if (Name_Space.declared const_space c) then
          utp_lift_aux ctx (Const (c, t), args)
        \<comment> \<open> Otherwise, we simply apply normal lifting.\<close>
        else
          list_appl
          (case (Syntax.check_term ctx (Free (n, t))) of
            Free (_, Type (\<^type_name>\<open>lens_ext\<close>, _)) => Const (@{const_name var}, dummyT) $ (Const (@{const_name pr_var}, dummyT) $ Free (n, t)) |
            Free (_, Type (\<^type_name>\<open>uexpr\<close>, _)) => Free (n, t) |
            _ => Const (@{const_name lit}, dummyT) $ Free (n, t)
          , map (utp_lift ctx) args)
    end
    |

  \<comment> \<open> Bound variables are always lifted as well \<close>
  utp_lift_aux ctx (Bound n, args) = list_appl (Const (@{const_name lit}, dummyT) $ Bound n, map (utp_lift ctx) args) |
  utp_lift_aux _ (t, args) = raise TERM ("_utp_lift_aux", t :: args)
  and
  (* FIXME: Think more about abstractions; at the moment they are essentially passed over. *)
(*  utp_lift ctx (Abs (x, ty, tm)) = Abs (x, ty, utp_lift ctx tm) | *)
  utp_lift ctx (Const (\<^syntax_const>\<open>_constrain\<close>, k) $ t $ ty) = (utp_lift ctx t) |
  utp_lift ctx (Abs (x, ty, tm)) = Const (@{const_name uabs}, dummyT) $ Abs (x, ty, utp_lift ctx tm) |
  utp_lift _ (Bound n) = (Const (@{const_name lit}, dummyT) $ Bound n) |
  utp_lift ctx t = utp_lift_aux ctx (Term.strip_comb t);

  \<comment> \<open> Apply the Isabelle term parser, strip type constraints, perform lifting, and finally type
      check the resulting lifted term. \<close>

  fun utp_tr ctx content args =
    let fun err () = raise TERM ("utp_tr", args) in
      (case args of
        [(Const (\<^syntax_const>\<open>_constrain\<close>, _)) $ Free (s, _) $ p] =>
          (case Term_Position.decode_position p of
            SOME (pos, _) => (utp_lift ctx (Type.strip_constraints (Syntax.parse_term ctx (content (s, pos)))))
          | NONE => err ())
      | _ => err ())
    end;
\<close>

text \<open> Set up Cartouche syntax using the above. \<close>

syntax "_utp" :: \<open>cartouche_position \<Rightarrow> string\<close>  ("UTP_")
syntax "_utp" :: \<open>cartouche_position \<Rightarrow> string\<close>  ("\<^U>_")

parse_translation \<open>
  [(\<^syntax_const>\<open>_utp\<close>,
    (fn ctx => utp_tr ctx (Symbol_Pos.implode o Symbol_Pos.cartouche_content o Symbol_Pos.explode)))]
\<close>

text \<open> Cartouche parser for UTP expressions. We can either surround the whole of a UTP relation
  with a the cartouche, or alternatively just the program text. \<close>
                     
syntax "_uexpr_cartouche" :: \<open>cartouche_position \<Rightarrow> uexp\<close>  ("_")

translations
  "_uexpr_cartouche e" => "_utp e"

text \<open> A more conventional parse translation version of the above \<close>

syntax
  "_UTP" :: "logic \<Rightarrow> logic" ("U'(_')")
  "_UTP" :: "logic \<Rightarrow> logic" ("\<^U>'(_')")

parse_translation \<open>
  [(@{syntax_const "_UTP"}, fn ctx => fn term => utp_lift ctx (Term_Position.strip_positions (hd term)))]
\<close>

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
  [("U(x)" , "CONST lit x"),
  ("U(t)" , "U(U(t))"),
  ("U(f x)" , "U(f) |> U(x)"),
(*  ("U(f x)" , "f |> U(x)"),
  ("U(f x)" , "U(f) |> x"), *)
  ("U(\<lambda> x. f)", "(\<lambda> x \<bullet> U(f))"),
  ("U(\<lambda> x. f)", "(\<lambda> x . U(f))"),
  ("U(f x)" , "CONST uop f U(x)"),
  ("U(f x y)" , "CONST bop f U(x) U(y)"),
(*  ("U(f x y)" , "CONST bop f x U(y)"),
  ("U(f x y)" , "CONST bop f U(x) y"), *)
  ("U(f x y z)" , "CONST trop f x y U(z)"),
  ("U(f x y z)" , "CONST trop f x U(y) z"),
  ("U(f x y z)" , "CONST trop f U(x) y z"),
  ("U(f x y z)" , "f U(x) U(y) U(z)"),

  ("U(f x y)" , "f U(x) U(y)"),
(*
  ("U(f x y z)" , "f x y U(z)"),
  ("U(f x y z)" , "f x U(y) z"),
  ("U(f x y z)" , "f U(x) y z"),

  ("U(f x y)" , "f x U(y)"),
  ("U(f x y)" , "f U(x) y"),
  ("U(f x)" , "f U(x)"),
  ("U(f x)" , "_UTP f x") *)
  ("U(f x)" , "_UTP f (_UTP x)")]
  val utp_consts = [@{syntax_const "_UTP"}, @{const_syntax lit}, @{const_syntax uop}, @{const_syntax bop}, @{const_syntax trop}, @{const_syntax qtop}];

  fun needs_mark t = 
    case Term.strip_comb t of
      (Const (c, _), _) => not (member (op =) utp_consts c) |
      _ => false;

  fun utp_mark_term (f, ts) = 
    if (needs_mark f) then Const (@{syntax_const "_UTP"}, dummyT) $ Term.list_comb (f, ts) else Term.list_comb (f, ts);

  fun uop_insert_U [f, x] = 
    if (needs_mark x) then Const (@{const_syntax "uop"}, dummyT) $ f $ (utp_mark_term (Term.strip_comb x))
    else raise Match |
  uop_insert_U _ = raise Match;

  fun bop_insert_U [f, x, y] =
    if (needs_mark x orelse needs_mark y) then Const (@{const_syntax "bop"}, dummyT) $ f $ (utp_mark_term (Term.strip_comb x)) $ (utp_mark_term (Term.strip_comb y))
    else raise Match |
  bop_insert_U _ = raise Match;

  fun trop_insert_U [f, x, y, z] =
    if (needs_mark x orelse needs_mark y orelse needs_mark z) 
      then Const (@{const_syntax "trop"}, dummyT) $ f $ (utp_mark_term (Term.strip_comb x)) $ (utp_mark_term (Term.strip_comb y))
      else raise Match |
  trop_insert_U _ = raise Match;

  fun appl_insert_U [f, x] =
    if (needs_mark f orelse needs_mark x)
      then utp_mark_term (Term.strip_comb f) $ utp_mark_term (Term.strip_comb x)
      else raise Match |
  appl_insert_U _ = raise Match;

  val print_tr = [ (@{const_syntax "trop"}, K trop_insert_U)
                 , (@{const_syntax "bop"}, K bop_insert_U)
                 , (@{const_syntax "uop"}, K uop_insert_U)
                 , (@{const_syntax "uexpr_appl"}, K appl_insert_U)];
  val no_print_tr = [ (@{syntax_const "_UTP"}, K (fn ts => Term.list_comb (hd ts, tl ts))) ];
in Outer_Syntax.command @{command_keyword utp_pretty} "enable pretty printing of UTP expressions" 
    (Scan.succeed (Toplevel.theory (Isar_Cmd.translations utp_tr_rules #> Sign.print_translation print_tr)));
   (* FIXME: It actually isn't currently possible to disable pretty printing without destroying the term rewriting *)
   Outer_Syntax.command @{command_keyword no_utp_pretty} "disable pretty printing of UTP expressions"
    (Scan.succeed (Toplevel.theory (Isar_Cmd.no_translations utp_tr_rules #> Sign.print_translation no_print_tr)))
 end
\<close>

utp_pretty

subsection \<open> Examples \<close>

text \<open> A couple of examples \<close>

term "UTP\<open>f x\<close>"

term "\<^U>\<open>f x\<close>"

term "UTP\<open>(xs @ ys) ! i\<close>"

term "UTP\<open>mm i\<close>"

term "UTP\<open>\<exists> x. f x\<close>"

term "UTP\<open>xs ! (x + y)\<close>"

term "UTP\<open>xs ! i\<close>"

term "UTP\<open>A \<union> B\<close>"

term "UTP\<open>\<exists> x. x \<le> xs ! i\<close>"

term "UTP\<open>(length xs + 1 + n \<le> 0) \<or> true\<close>"

term "UTP\<open>\<exists> n. (length xs + 1 + n \<le> 0) \<or> true\<close>"

term "UTP\<open>{x + y | x. 1 < x}\<close>"

term "UTP\<open>\<lambda> x. x + y\<close>"

term "UTP\<open>$x + 1 \<le> $y\<acute>\<close>"

term "UTP\<open>$x\<acute> = $x + 1 \<and> $y\<acute> = $y\<close>"

term "UTP\<open>\<Sqinter> x \<in> A. x < y\<close>"

locale test =
  fixes x :: "nat \<Longrightarrow> 's" and xs :: "int list \<Longrightarrow> 's"
begin

  abbreviation (input) "z \<equiv> x"

  text \<open> The lens x and HOL variable y are automatically distinguished \<close>

  term "if \<open>x \<le> y\<close> then P else Q fi"

  term "x := \<open>x + y\<close>"

  term "x := \<open>x + y + z\<close>"

  term "U(x + y)"

  term "UTP\<open>x\<^sup>< = x\<^sup>>\<close>"

  term "UTP\<open>x := to_nat (hd xs)\<close>"

  term "UTP\<open>x := to_nat (xs ! 5)\<close>"

  term "UTP\<open>while (x \<le> 10) do x := x + 1 od\<close>"

  term "UTP\<open>if (x \<le> y) then x := x + 1 ;; x := x + y else II fi\<close>"

  term "UTP\<open>($x < $x\<acute>) \<sqsubseteq> x := x + 1\<close>"

  term "UTP\<open>$f v\<close>"

  term "UTP\<open>{2<..}\<close>"

end

term "\<guillemotleft>x\<guillemotright> + $y"

term "\<guillemotleft>x\<guillemotright> + $y"

term "\<^U>(&v < 0)"

term "U($y = 5)"

term "\<^U>(f 0 $y \<le> 1 \<Rightarrow> $y = 1 + $y)"

term "\<^U>(f 0 $y \<le> 1) \<Rightarrow> bop (=) \<^U>($y) true"

term "\<^U>($f x)"

term "U($f $\<^bold>v\<acute>)"

end

