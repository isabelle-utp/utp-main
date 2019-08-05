section \<open> Lifting Parser \<close>

theory utp_lift_parser
  imports "UTP.utp"
begin

text \<open> Create a mutable data structure to store the names of constants that should not be lifted \<close>

ML \<open>
structure NoLift = Theory_Data
  (type T = string Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true));
\<close>

text \<open> Add a sample of the UTP operators that shouldn't be lifted \<close>

setup \<open>
NoLift.map (Symtab.update (@{const_name "Groups.zero"}, "")) #>
NoLift.map (Symtab.update (@{const_name "Groups.one"}, "")) #>
NoLift.map (Symtab.update (@{const_name "Groups.plus"}, "")) #>
NoLift.map (Symtab.update (@{const_name "shEx"}, "")) #>
NoLift.map (Symtab.update (@{const_name "ushEx"}, "")) #>
NoLift.map (Symtab.update (@{const_name "uconj"}, "")) #>
NoLift.map (Symtab.update (@{const_name "udisj"}, "")) #>
NoLift.map (Symtab.update (@{const_name "uimpl"}, "")) #>
NoLift.map (Symtab.update (@{const_name "utrue"}, "")) #>
NoLift.map (Symtab.update (@{const_name "ufalse"}, "")) #>
NoLift.map (Symtab.update (@{const_name "var"}, "")) #>
NoLift.map (Symtab.update (@{const_name "ivar"}, "")) #>
NoLift.map (Symtab.update (@{const_name "ovar"}, ""))
\<close>

text \<open> The following function takes a parser, but not-yet type-checked term, and wherever it
  encounters an application, it inserts a UTP expression operator. Any operators that have
  been marked in the above structure will not be lifted. \<close>

ML \<open> 
  fun
  utp_lift ctx (Const (n, t) $ x $ y) = 
    if (member (op =) (Symtab.keys (NoLift.get @{theory})) n)
      then (Const (n, t) $ utp_lift ctx x $ utp_lift ctx y)
      else Const (@{const_name bop}, dummyT) $ Const (n, t) $ utp_lift ctx x $ utp_lift ctx y |
  utp_lift ctx (Const (n, t) $ x) = 
    if (member (op =) (Symtab.keys (NoLift.get @{theory})) n)
      then Const (n, t) $ utp_lift ctx x
      else Const (@{const_name uop}, dummyT) $ Const (n, t) $ utp_lift ctx x |
  \<comment> \<open> In the case of an unapplied constant, the parser tries to determine whether it is a defined
       operation of a lens, and behaves appropriately. \<close>
  utp_lift ctx (Const (n, t)) =
    if (member (op =) (Symtab.keys (NoLift.get @{theory})) n)
      then Const (n, t) else
    (case (Syntax.check_term ctx (Const (n, t))) of
      Const (_, Type ("Lens_Laws.lens.lens_ext", _)) => Const (@{const_name var}, dummyT) $ Const (n, t) |
      _ => Const (@{const_name lit}, dummyT) $ Const (n, t)) |
  utp_lift _ (Free c) = Const (@{const_name lit}, dummyT) $ Free c |
  utp_lift _ (Bound c) = Const (@{const_name lit}, dummyT) $ Bound c |
  utp_lift ctx (Abs (x, ty, tm)) = Abs (x, ty, utp_lift ctx tm) |
  utp_lift _ t = raise TERM ("_utp", [t]); 
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

text \<open> A couple of examples \<close>

alphabet myss = xs :: "int list"

term "UTP\<open>A \<union> B\<close>"

term "x := UTP\<open>A \<union> B\<close>"

term "UTP\<open>\<^bold>\<exists> n \<bullet> (length xs + 1 + n \<le> 0) \<or> true\<close>"


end

