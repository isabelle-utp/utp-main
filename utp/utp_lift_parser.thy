section \<open> Lifting Parser \<close>

theory utp_lift_parser
  imports "utp_rel"
  keywords "no_utp_lift" :: "thy_decl_block"
begin

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
structure NoLift = Theory_Data
  (type T = int list Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true));

val _ =
  let fun nolift_const thy (n, opt) =  
          let val Const (c, _) = Proof_Context.read_const {proper = true, strict = false} (Proof_Context.init_global thy) n 
          in NoLift.map (Symtab.update (c, (map Value.parse_int opt))) thy end
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
  shEx ushEx shAll ushAll unot uconj udisj uimpl utrue ufalse 
  UINF USUP
  var (0) in_var (0) out_var  (0)
  cond rcond uassigns id seqr useq uskip rcond rassume rassert 
  rgcmd while_top while_bot while_inv while_inv_bot while_vrt
  subst_upd (1) numeral (0) refineBy

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

  fun utp_lift_aux ctx (Const (n, t), args) = 
    \<comment> \<open> If the name of the given constant is in the ``no lifting'' list... \<close>
    if (member (op =) (Symtab.keys (NoLift.get (Proof_Context.theory_of ctx))) n)
      \<comment> \<open> ... then do not lift it, and also do not process any arguments in the given list of integers. \<close>
      then let val (SOME aopt) = Symtab.lookup (NoLift.get (Proof_Context.theory_of ctx)) n in
           Term.list_comb (Const (n, t), map_index (fn (i, t) => if (member (op =) aopt i) then t else utp_lift ctx t) args) end
      \<comment> \<open> If the name is not in the ``no lifting'' list... \<close>
      else
        list_appl
        (case (Syntax.check_term ctx (Const (n, t))) of
          \<comment> \<open> ... and it's a lens, then lift it as a UTP variable... \<close>
          Const (_, Type ("Lens_Laws.lens.lens_ext", _)) => Const (@{const_name var}, dummyT) $ (Const (@{const_name pr_var}, dummyT) $ Const (n, t)) |
          \<comment> \<open> ...otherwise, lift it is a HOL literal \<close>
          _ => Const (@{const_name lit}, dummyT) $ Const (n, t)
        , map (utp_lift ctx) args)
    |

  \<comment> \<open> Free variables are handled as constants, except that they are always lifted \<close>
  utp_lift_aux ctx (Free (n, t), args) =
        list_appl
        (case (Syntax.check_term ctx (Free (n, t))) of
          Free (_, Type ("Lens_Laws.lens.lens_ext", _)) => Const (@{const_name var}, dummyT) $ (Const (@{const_name pr_var}, dummyT) $ Free (n, t)) |
          _ => Const (@{const_name lit}, dummyT) $ Free (n, t)
        , map (utp_lift ctx) args)
    |

  \<comment> \<open> Bound variables are always lifted as well \<close>
  utp_lift_aux ctx (Bound n, args) = list_appl (Const (@{const_name lit}, dummyT) $ Bound n, map (utp_lift ctx) args) |
  utp_lift_aux _ (t, args) = raise TERM ("_utp_lift_aux", t :: args)
  and
  (* FIXME: Think more about abstractions; at the moment they are essentially passed over. *)
  utp_lift ctx (Abs (x, ty, tm)) = Abs (x, ty, utp_lift ctx tm) |
  utp_lift ctx t = utp_lift_aux ctx (Term.strip_comb t);

  \<comment> \<open> Apply the Isabelle term parser, strip type constraints, perform lifting, and finally type
      check the resulting lifted term. \<close>

  fun utp_tr ctx content args =
    let fun err () = raise TERM ("utp_tr", args) in
      (case args of
        [(Const (\<^syntax_const>\<open>_constrain\<close>, _)) $ Free (s, _) $ p] =>
          (case Term_Position.decode_position p of
            SOME (pos, _) => Syntax.check_term ctx (utp_lift ctx (Type.strip_constraints (Syntax.parse_term ctx (content (s, pos)))))
          | NONE => err ())
      | _ => err ())
    end;
\<close>

text \<open> Set up Cartouche syntax using the above. \<close>

syntax "_utp" :: \<open>cartouche_position \<Rightarrow> string\<close>  ("UTP_")

parse_translation \<open>
  [(\<^syntax_const>\<open>_utp\<close>,
    (fn ctx => utp_tr ctx (Symbol_Pos.implode o Symbol_Pos.cartouche_content o Symbol_Pos.explode)))]
\<close>

text \<open> Cartouche parser for UTP expressions. We can either surround the whole of a UTP relation
  with a the cartouche, or alternatively just the program text. \<close>

syntax "_uexpr_cartouche" :: \<open>cartouche_position \<Rightarrow> uexp\<close>  ("_")

translations
  "_uexpr_cartouche e" => "_utp e"

text \<open> A couple of examples \<close>

term "UTP\<open>f x\<close>"

term "UTP\<open>(xs @ ys) ! i\<close>"

term "UTP\<open>mm i\<close>"

term "UTP\<open>xs ! (x + y)\<close>"

term "UTP\<open>xs ! i\<close>"

term "UTP\<open>A \<union> B\<close>"

term "UTP\<open>\<^bold>\<exists> x \<bullet> x \<le> xs ! i\<close>"

term "UTP\<open>(length xs + 1 + n \<le> 0) \<or> true\<close>"

term "UTP\<open>\<^bold>\<exists> n \<bullet> (length xs + 1 + n \<le> 0) \<or> true\<close>"

term "UTP\<open>\<lambda> x. x + y\<close>"

term "UTP\<open>$x + 1 \<le> $y\<acute>\<close>"

term "UTP\<open>\<Sqinter> x \<in> A \<bullet> x < y\<close>"

locale test =
  fixes x :: "nat \<Longrightarrow> 's" and xs :: "int list \<Longrightarrow> 's"
begin

  text \<open> The lens x and HOL variable y are automatically distinguished \<close>

  term "if \<open>x \<le> y\<close> then P else Q fi"

  term "x := \<open>x + y\<close>"

  term "UTP\<open>x := to_nat (hd xs)\<close>"

  term "UTP\<open>x := to_nat (xs ! 5)\<close>"

  term "UTP\<open>while (x \<le> 10) do x := x + 1 od\<close>"

  term "UTP\<open>if (x \<le> y) then x := x + 1 ;; x := x + y else II fi\<close>"

  term "UTP\<open>($x < $x\<acute>) \<sqsubseteq> x := x + 1\<close>"

end

end

