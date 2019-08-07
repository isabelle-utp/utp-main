section \<open> Lifting Parser \<close>

theory utp_lift_parser
  imports "utp_rel"
  keywords "no_utp_lift" :: "thy_decl_block"
begin

text \<open> Create a mutable data structure to store the names of constants that should not be lifted \<close>

ML \<open>
structure NoLift = Theory_Data
  (type T = string Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true));

val _ =
  let fun nolift_const thy n =  
          let val Const (c, _) = Proof_Context.read_const {proper = true, strict = false} (Proof_Context.init_global thy) n 
          in NoLift.map (Symtab.update (c, "")) thy end
  in

  Outer_Syntax.command @{command_keyword no_utp_lift} "declare that certain constants should not be lifted"
    (Scan.repeat1 Parse.term
     >> (fn ns => 
         Toplevel.theory 
         (fn thy => Library.foldl (fn (thy, n) => nolift_const thy n) (thy, ns))))  
  end
\<close>

text \<open> The core UTP operators should not be lifted \<close>

no_utp_lift
  Groups.zero Groups.one plus uminus minus times divide numeral
  shEx ushEx uconj udisj uimpl utrue ufalse var ivar ovar 
  cond rcond uassigns

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

(*
  fun
  utp_lift ctx (f $ x) = Const (@{const_name "uexpr_appl"}, dummyT) $ utp_lift ctx f $ utp_lift ctx x |
  utp_lift ctx (Const (n, t)) =
    if (member (op =) (Symtab.keys (NoLift.get @{theory})) n)
      then Const (n, t) else
    (case (Syntax.check_term ctx (Const (n, t))) of
      Const (_, Type ("Lens_Laws.lens.lens_ext", _)) => Const (@{const_name var}, dummyT) $ (Const (@{const_name pr_var}, dummyT) $ Const (n, t)) |
      _ => Const (@{const_name lit}, dummyT) $ Const (n, t)) |
  utp_lift _ (Free c) = Const (@{const_name lit}, dummyT) $ Free c |
  utp_lift _ (Bound c) = Const (@{const_name lit}, dummyT) $ Bound c |
  utp_lift ctx (Abs (x, ty, tm)) = Abs (x, ty, utp_lift ctx tm) |
  utp_lift _ t = raise TERM ("_utp", [t]); 
*)

  val list_appl = Library.foldl (fn (f, x) => Const (@{const_name "uexpr_appl"}, dummyT) $ f $ x);

  fun utp_lift_aux ctx (Const (n, t), args) = 
    if (member (op =) (Symtab.keys (NoLift.get @{theory})) n)
      then Term.list_comb (Const (n, t), map (utp_lift ctx) args)
      else
        list_appl
        (case (Syntax.check_term ctx (Const (n, t))) of
          Const (_, Type ("Lens_Laws.lens.lens_ext", _)) => Const (@{const_name var}, dummyT) $ (Const (@{const_name pr_var}, dummyT) $ Const (n, t)) |
          _ => Const (@{const_name lit}, dummyT) $ Const (n, t)
        , map (utp_lift ctx) args)
    |
  utp_lift_aux ctx (Free (n, t), args) = 
        list_appl
        (case (Syntax.check_term ctx (Free (n, t))) of
          Free (_, Type ("Lens_Laws.lens.lens_ext", _)) => Const (@{const_name var}, dummyT) $ (Const (@{const_name pr_var}, dummyT) $ Free (n, t)) |
          _ => Const (@{const_name lit}, dummyT) $ Free (n, t)
        , map (utp_lift ctx) args)
    |

(* utp_lift_aux ctx (Free c, args) = list_appl (Const (@{const_name lit}, dummyT) $ Free c, map (utp_lift ctx) args) | *)
  utp_lift_aux ctx (Bound n, args) = list_appl (Const (@{const_name lit}, dummyT) $ Bound n, map (utp_lift ctx) args) |
  utp_lift_aux _ (t, args) = raise TERM ("_utp_lift_aux", t :: args)
  and
  (* FIXME: Think more about abstractions *)
  utp_lift ctx (Abs (x, ty, tm)) = Abs (x, ty, utp_lift ctx tm) |
  utp_lift ctx t = utp_lift_aux ctx (Term.strip_comb t);


 \<close>

text \<open> Apply the Isabelle term parser, strip type constraints, perform lifting, and finally type
  check the resulting lifted term. \<close>

ML \<open>
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

text \<open> Cartouche parser for UTP expressions \<close>

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

locale test =
  fixes x :: "int \<Longrightarrow> 's"
begin

  term "if \<open>x \<le> y\<close> then P else Q fi"

  term "x := \<open>x + y\<close>"

end

end

