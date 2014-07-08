theory utp_alpha_pred_parser
  imports
  "../alpha/utp_alpha_pred"
  "../alpha/utp_alpha_rel"
  "../alpha/utp_alpha_expr"
  "../alpha/utp_alpha_lattice"
  "../tactics/utp_pred_tac"
  "../tactics/utp_expr_tac"
  "../tactics/utp_rel_tac"
  "../poly/utp_poly_alpha_expr"
  utp_parser_utils
begin

nonterminal 
  n_uapred and n_uaexpr and 
  n_apexpr and n_apexprs and
  uzdecls and uzdecl

syntax
  "_n_apexprs"            :: "[n_apexpr, n_apexprs] => n_apexprs" ("_,/ _")
  ""                    :: "n_apexpr => n_apexprs" ("_")
  "_n_apexpr_brack"       :: "n_apexpr \<Rightarrow> n_apexpr" ("'(_')")
  "_n_apexpr_pred_var"    :: "idt \<Rightarrow> n_apexpr" ("@(_)")
  "_n_apexpr_expr_var"    :: "idt \<Rightarrow> n_apexpr" ("(_)")
  "_n_apexpr_evar"        :: "('a, 'm) pvar \<Rightarrow> n_apexpr" ("$_" [999] 999)
  "_n_apexpr_subst"       :: "n_apexpr \<Rightarrow> n_apexpr \<Rightarrow> ('a, 'm) pvar \<Rightarrow> n_apexpr" ("(_[_'/_])" [999,999] 1000)
  "_n_apexpr_lit"         :: "'a \<Rightarrow> n_apexpr" ("\<guillemotleft>_\<guillemotright>")
  "_n_apexpr_true"        :: "n_apexpr" ("true")
  "_n_apexpr_false"       :: "n_apexpr" ("false")
  "_n_apexpr_op1"         :: "idt \<Rightarrow> n_apexpr \<Rightarrow> n_apexpr" ("_'(_')")
  "_n_apexpr_op2"         :: "idt \<Rightarrow> n_apexpr \<Rightarrow> n_apexpr \<Rightarrow> n_apexpr" ("_'(_,_')")
  "_n_apexpr_op3"         :: "idt \<Rightarrow> n_apexpr \<Rightarrow> n_apexpr \<Rightarrow> n_apexpr \<Rightarrow> n_apexpr" ("_'(_,_,_')")

(* Predicate Parser *)

syntax
  "_n_uapred_top_clos" :: "n_uapred \<Rightarrow> bool" ("(1[_])")
  "_n_uapred_quote"    :: "n_uapred \<Rightarrow> 'a uapred" ("(1``_``)")
  "_n_uapred_brack"    :: "n_uapred \<Rightarrow> n_uapred" ("'(_')" [0] 900)
  "_n_uapred_op1"      :: "idt \<Rightarrow> n_uapred \<Rightarrow> n_uapred" ("_'(_')")
  "_n_uapred_op2"      :: "idt \<Rightarrow> n_uapred \<Rightarrow> n_uapred \<Rightarrow> n_uapred" ("_'(_,_')")
  "_n_uapred_op3"      :: "idt \<Rightarrow> n_uapred \<Rightarrow> n_uapred \<Rightarrow> n_uapred \<Rightarrow> n_uapred" ("_'(_,_,_')")
  "_n_uapred_TRUE"     :: "n_uapred" ("TT")
  "_n_uapred_true"     :: "'a alpha \<Rightarrow> n_uapred" ("true\<^bsub>_\<^esub>")
  "_n_uapred_tt"       :: "'a alpha \<Rightarrow> n_uapred" ("tt\<^bsub>_\<^esub>")
  "_n_uapred_FALSE"    :: "n_uapred" ("FF")
  "_n_uapred_false"    :: "'a alpha \<Rightarrow> n_uapred" ("false\<^bsub>_\<^esub>")
  "_n_uapred_ff"       :: "'a alpha \<Rightarrow> n_uapred" ("ff\<^bsub>_\<^esub>")
  "_n_uapred_var"      :: "pttrn \<Rightarrow> n_uapred" ("(_)")
  "_n_uapred_evar"     :: "(bool, 'm) pvar \<Rightarrow> n_uapred" ("$_" [999] 999)
  "_n_uapred_and"      :: "n_uapred \<Rightarrow> n_uapred \<Rightarrow> n_uapred" (infixr "\<and>" 35)
  "_n_uapred_or"       :: "n_uapred \<Rightarrow> n_uapred \<Rightarrow> n_uapred" (infixr "\<or>" 35)
  "_n_uapred_imp"      :: "n_uapred \<Rightarrow> n_uapred \<Rightarrow> n_uapred" (infixr "\<Rightarrow>" 25)
  "_n_uapred_iff"      :: "n_uapred \<Rightarrow> n_uapred \<Rightarrow> n_uapred" (infixr "\<Leftrightarrow>" 25)
  "_n_uapred_ref"      :: "n_uapred \<Rightarrow> n_uapred \<Rightarrow> n_uapred" (infixr "\<sqsubseteq>" 25)
  "_n_uapred_clos"     :: "n_uapred \<Rightarrow> n_uapred" ("[_]")
  "_n_uapred_not"      :: "n_uapred \<Rightarrow> n_uapred" ("\<not> _" [40] 40) 
  "_n_uapred_ext"      :: "n_uapred \<Rightarrow> 'a alpha \<Rightarrow> n_uapred" (infixr "\<oplus>" 40)
  "_n_uapred_res"      :: "n_uapred \<Rightarrow> 'a alpha \<Rightarrow> n_uapred" (infixr "\<ominus>" 40)
(*
  "_n_uapred_ext"      :: "n_uapred \<Rightarrow> 'a ALPHABET \<Rightarrow> n_uapred" ("_\<^bsub>+_\<^esub>" 40)
  "_n_uapred_res"      :: "n_uapred \<Rightarrow> 'a ALPHABET \<Rightarrow> n_uapred" ("_\<^bsub>-_\<^esub>" 40)
*)
  "_n_uapred_all1"     :: "('a, 'm) pvar \<Rightarrow> n_uapred \<Rightarrow> n_uapred"  ("(3\<forall> _./ _)" [0, 10] 10) 
  "_n_uapred_exists1"  :: "('a, 'm) pvar \<Rightarrow> n_uapred \<Rightarrow> n_uapred"  ("(3\<exists>+ _./ _)" [0, 10] 10) 
  "_n_uapred_existsres1" :: "('a, 'm) pvar \<Rightarrow> n_uapred \<Rightarrow> n_uapred"  ("(3\<exists> _./ _)" [0, 10] 10) 
  "_n_uapred_pexpr"    :: "n_apexpr \<Rightarrow> n_uapred" ("\<lparr>_\<rparr>")
  "_n_uapred_equal"    :: "n_apexpr \<Rightarrow> n_apexpr \<Rightarrow> n_uapred" (infixl "=" 50)
  "_n_uapred_nequal"   :: "n_apexpr \<Rightarrow> n_apexpr \<Rightarrow> n_uapred" (infixl "\<noteq>" 50)
  "_n_uapred_skip"     :: "'a alpha \<Rightarrow> n_uapred" ("II\<^bsub>_\<^esub>")
  "_n_uapred_seq"      :: "n_uapred \<Rightarrow> n_uapred \<Rightarrow> n_uapred" (infixr ";" 45)
  "_n_uapred_cond"     :: "n_uapred \<Rightarrow> n_uapred \<Rightarrow> n_uapred \<Rightarrow> n_uapred" ("_ \<lhd> _ \<rhd> _")
  "_n_uapred_ifthenelse" :: "n_uapred \<Rightarrow> n_uapred \<Rightarrow> n_uapred \<Rightarrow> n_uapred" ("if _ then _ else _")
  "_n_uapred_assign"   :: "('a, 'm) pvar \<Rightarrow> 'a alpha \<Rightarrow> n_apexpr \<Rightarrow> n_uapred" ("_ :=\<^bsub>_ \<^esub>_" [100] 100)
  "_n_uapred_conv"     :: "n_uapred \<Rightarrow> n_uapred" ("(_\<^sup>\<smile>)" [1000] 999)
  "_n_uapred_prime"    :: "n_uapred \<Rightarrow> n_uapred" ("_\<acute>" [1000] 1000)
  "_n_uapred_varext"   :: "n_uapred \<Rightarrow> ('a, 'm) pvar \<Rightarrow> n_uapred" ("_\<^bsub>+_\<^esub>")
(*
  "_n_uapred_zpara"    :: "uzdecls \<Rightarrow> n_uapred \<Rightarrow> n_uapred" ("[_|_]")
  "_uzdecl_basic"    :: "'a VAR \<Rightarrow> 'a VAR \<Rightarrow> uzdecl" (infix ":" 45)
  ""                 :: "uzdecl => uzdecls"             ("_")
  "_uzdecls"         :: "[uzdecl, uzdecls] => uzdecls" ("_,/ _")
*)

translations
  "_n_uapred_brack p"     => "p"
  "_n_uapred_op1 f x"     => "f x"
  "_n_uapred_op2 f x y"   => "f x y"
  "_n_uapred_op3 f x y z" => "f x y z" 
  "_n_uapred_quote p"     => "p"
  "_n_uapred_top_clos p"  == "CONST TautologyA p"
  "_n_uapred_TRUE"        == "CONST TRUE"
  "_n_uapred_true a"      == "CONST TrueA a"
  "_n_uapred_tt a"        => "CONST TrueA a"
  "_n_uapred_FALSE"       == "CONST FALSE"
  "_n_uapred_false a"     == "CONST FalseA a"
  "_n_uapred_ff a"        => "CONST FalseA a"
  "_n_uapred_var x"       => "x"
  "_n_uapred_evar x"      == "CONST VarAP x"
  "_n_uapred_and p q"     == "CONST AndA p q"
  "_n_uapred_or p q"      == "CONST OrA p q"
  "_n_uapred_imp p q"     == "CONST ImpliesA p q"
  "_n_uapred_ref p q"     == "CONST RefA p q"
  "_n_uapred_iff p q"     == "CONST IffA p q"
  "_n_uapred_clos p"      == "CONST ClosureA p"
  "_n_uapred_not p"       == "CONST NotA p"
  "_n_uapred_ext a p"     == "CONST ExtA a p"
  "_n_uapred_res a p"     == "CONST ResA a p"
  "_n_uapred_all1 x p"    == "CONST ForallA \<lbrace>x\<down>\<rbrace> p"
  "_n_uapred_exists1 x p" == "CONST ExistsA \<lbrace>x\<down>\<rbrace> p"
  "_n_uapred_existsres1 x p" == "CONST ExistsResA \<lbrace>x\<down>\<rbrace> p"
  "_n_uapred_pexpr e"     == "CONST APExprA e"
  "_n_uapred_equal e f"   == "CONST APEqualA e f"
  "_n_uapred_nequal e f"  == "CONST NotA (CONST EqualA e f)"
  "_n_uapred_skip a"      == "CONST SkipA a"
  "_n_uapred_seq p q"     => "CONST SemiA p q"
  "_n_uapred_cond p q r"  == "CONST CondA p q r"
  "_n_uapred_ifthenelse b p q"  => "CONST CondA p b q"
  "_n_uapred_assign x a e" == "CONST PAssignA x a e"
  "_n_uapred_conv x"      => "CONST ConvA x"
  "_n_uapred_prime x"     == "CONST ConvA x"
  "_n_uapred_varext p x"  == "CONST VarExtA p x\<down>"

(* Expression Parser *)

syntax
  "_n_uaexpr_brack"    :: "n_uaexpr \<Rightarrow> n_uaexpr" ("'(_')" [0] 700)
  "_n_uaexpr_true"     :: "n_uaexpr" ("true")
  "_n_uaexpr_false"    :: "n_uaexpr" ("false")
  "_n_uaexpr_var"      :: "pttrn \<Rightarrow> n_uaexpr" ("_")
  "_n_uaexpr_evar"     :: "'a uvar \<Rightarrow> n_uaexpr" ("$_" [500] 500)
  "_n_uaexpr_substp"   :: "n_uapred \<Rightarrow> n_apexpr \<Rightarrow> ('a, 'm) pvar \<Rightarrow> n_uapred" ("(_[_'/_])" [999,999] 1000)
  "_n_uaexpr_member"   :: "n_uaexpr \<Rightarrow> n_uaexpr \<Rightarrow> n_uaexpr" (infix ":" 45)
  "_n_uaexpr_coerce"   :: "n_uaexpr \<Rightarrow> pttrn \<Rightarrow> n_uaexpr" ("_\<Colon>_" [60,60] 65)

translations
  "_n_uaexpr_brack e"      => "e"
  "_n_uaexpr_true"         == "CONST TrueAE"
  "_n_uaexpr_false"        == "CONST FalseAE"
  "_n_uaexpr_var x"        => "x" 
  "_n_uaexpr_evar x"       == "CONST VarAE x"
  "_n_uaexpr_substp p e x" == "CONST PSubstA p e x"
  "_n_uaexpr_coerce e t"   == "CONST CoerceAE e t"

translations
  "_n_apexpr_evar x"             == "CONST VarAPE x"
  "_n_apexpr_expr_var e"         => "e"
  "_n_apexpr_brack e"            => "e"
  "_n_apexpr_lit v"              == "CONST LitAPE v"
  "_n_apexpr_true"               == "CONST TrueAPE"
  "_n_apexpr_false"              == "CONST FalseAPE"
  "_n_apexpr_op1 f x"            == "CONST Op1APE f x"
  "_n_apexpr_op2 f x y"          == "CONST Op2APE f x y"
  "_n_apexpr_op3 f x y z"        == "CONST Op3APE f x y z"

syntax
  (* Data Structures *)
  "_n_apexpr_num_0"         :: "n_apexpr" ("0")
  "_n_apexpr_num_1"         :: "n_apexpr" ("1")
  "_n_apexpr_num"           :: "num_const \<Rightarrow> n_apexpr" ("_")
  "_n_apexpr_float"         :: "float_const \<Rightarrow> n_apexpr" ("_")
  "_n_apexpr_string"        :: "str_position \<Rightarrow> n_apexpr" ("_")
  "_n_apexpr_plus"          :: "n_apexpr \<Rightarrow> n_apexpr \<Rightarrow> n_apexpr" (infixl "+" 65)
  "_n_apexpr_mult"          :: "n_apexpr \<Rightarrow> n_apexpr \<Rightarrow> n_apexpr" (infixl "*" 70)
  "_n_apexpr_div"           :: "n_apexpr \<Rightarrow> n_apexpr \<Rightarrow> n_apexpr" (infixl "'/" 70)
  "_n_apexpr_minus"         :: "n_apexpr \<Rightarrow> n_apexpr \<Rightarrow> n_apexpr" (infixl "-" 65)
  "_n_apexpr_max"           :: "n_apexpr \<Rightarrow> n_apexpr \<Rightarrow> n_apexpr" ("max'(_, _')")
  "_n_apexpr_min"           :: "n_apexpr \<Rightarrow> n_apexpr \<Rightarrow> n_apexpr" ("min'(_, _')")
  "_n_apexpr_less"          :: "n_apexpr \<Rightarrow> n_apexpr \<Rightarrow> n_apexpr" (infixr "<" 25)
  "_n_apexpr_less_eq"       :: "n_apexpr \<Rightarrow> n_apexpr \<Rightarrow> n_apexpr" (infixr "\<le>" 25)
  "_n_apexpr_greater"       :: "n_apexpr \<Rightarrow> n_apexpr \<Rightarrow> n_apexpr" (infixr ">" 25)
  "_n_apexpr_greater_eq"    :: "n_apexpr \<Rightarrow> n_apexpr \<Rightarrow> n_apexpr" (infixr "\<ge>" 25)

translations
  "_n_apexpr_num_0"               == "CONST LitAPE 0"
  "_n_apexpr_num_1"               == "CONST LitAPE 1"
  "_n_apexpr_num n"               == "CONST LitAPE (_Numeral n)"
  "_n_apexpr_float n"             == "CONST LitAPE (_Float n)"
  "_n_apexpr_plus x y"            == "CONST PlusAPE x y"
  "_n_apexpr_mult x y"            == "CONST MultAPE x y"
  "_n_apexpr_minus x y"           == "CONST MinusAPE x y"
  "_n_apexpr_div x y"             == "CONST DivAPE x y"
  "_n_apexpr_max x y"             == "CONST MaxAPE x y"
  "_n_apexpr_min x y"             == "CONST MinAPE x y"
  "_n_apexpr_less x y"            == "CONST LessAPE x y"
  "_n_apexpr_less_eq x y"         == "CONST LessEqAPE x y"
  "_n_apexpr_greater x y"         == "CONST LessAPE y x"
  "_n_apexpr_greater_eq x y"      == "CONST LessEqAPE y x"

parse_ast_translation {*
let fun apexpr_string_tr [str] =
  Ast.Appl [Ast.Constant @{const_syntax LitAPE}, Utp_Parser_Utils.string_ast_tr [str]]
  | apexpr_string_tr _ = raise Match;
  in
  [(@{syntax_const "_n_apexpr_string"}, K apexpr_string_tr)]
end
*}
  
(* Big operators *)

default_sort type

syntax
  "_n_uapred_index" :: "('b \<Rightarrow> 'a uapred) \<Rightarrow> 'b \<Rightarrow> n_uapred" ("_<_>" 50)
  "_n_uapred_ANDI1" :: "'a alpha \<Rightarrow> pttrns \<Rightarrow> n_uapred \<Rightarrow> n_uapred" ("(3\<And>\<^bsub>_\<^esub> _./ _)" [0, 0, 10] 10)
  "_n_uapred_ANDI"  :: "'a alpha \<Rightarrow> pttrn \<Rightarrow> 'b set \<Rightarrow> n_uapred \<Rightarrow> n_uapred"  ("(3\<And>\<^bsub>_\<^esub> _:_./ _)" [0, 0, 0, 10] 10)
  "_n_uapred_ORDI1" :: "'a alpha \<Rightarrow> pttrns \<Rightarrow> n_uapred \<Rightarrow> n_uapred" ("(3\<Or>\<^bsub>_\<^esub> _./ _)" [0, 0, 10] 10)
  "_n_uapred_ORDI"  :: "'a alpha \<Rightarrow> pttrn \<Rightarrow> 'b set \<Rightarrow> n_uapred \<Rightarrow> n_uapred"  ("(3\<Or>\<^bsub>_\<^esub> _:_./ _)" [0, 0, 10] 10)
  "_n_uapred_INF1"  :: "'a alpha \<Rightarrow> pttrns \<Rightarrow> n_uapred \<Rightarrow> n_uapred" ("(3\<Sqinter>\<^bsub>_\<^esub> _./ _)" [0, 0, 10] 10)
  "_n_uapred_INF"   :: "'a alpha \<Rightarrow> pttrn \<Rightarrow> 'b set \<Rightarrow> n_uapred \<Rightarrow> n_uapred"  ("(3\<Sqinter>\<^bsub>_\<^esub> _:_./ _)" [0, 0, 0, 10] 10)
  "_n_uapred_SUP1"  :: "'a alpha \<Rightarrow> pttrns \<Rightarrow> n_uapred \<Rightarrow> n_uapred" ("(3\<Squnion>\<^bsub>_\<^esub> _./ _)" [0, 0, 10] 10)
  "_n_uapred_SUP"   :: "'a alpha \<Rightarrow> pttrn \<Rightarrow> 'b set \<Rightarrow> n_uapred \<Rightarrow> n_uapred"  ("(3\<Squnion>\<^bsub>_\<^esub> _:_./ _)" [0, 0, 0, 10] 10)

translations
  "_n_uapred_index f i"     => "f i"
  "_n_uapred_ANDI1 a x y B" => "AND[a] x. AND[a] y. B"
  "_n_uapred_ANDI1 a x B"   == "CONST AANDI a CONST UNIV (%x. B)"
  "_n_uapred_ANDI a x A B"  == "CONST AANDI a A (%x. B)"
  "_n_uapred_ORDI1 a x y B" => "OR[a] x. OR[a] y. B"
  "_n_uapred_ORDI1 a x B"   == "CONST AORDI a CONST UNIV (%x. B)"
  "_n_uapred_ORDI a x A B"  == "CONST AORDI a A (%x. B)"
  "_n_uapred_INF1 a x B"    == "CONST InfiA a CONST UNIV (%x. B)"
  "_n_uapred_INF a x A B"   == "CONST InfiA a A (%x . B)"
  "_n_uapred_SUP1 a x B"    == "CONST SuprA a CONST UNIV (%x. B)"
  "_n_uapred_SUP a x A B"   == "CONST SuprA a A (%x . B)"

default_sort VALUE

(* Parser sanity check *)

term "``\<And>\<^bsub>a\<^esub> i:I. P``"

term "``\<Sqinter>\<^bsub>a\<^esub> i. P<i>``"

term "``p \<and> q``"

term "``$x = false``"

term "``p[v/x]``"

term "``x :=\<^bsub>\<lbrace>x\<down>,x\<down>\<acute>\<rbrace>\<^esub> true``"

term "``p \<oplus> \<lbrace>x\<down>\<rbrace>``"

term "``\<exists> x\<acute>. p``"

term "``$x = 1``"

term "``$x = ''hello''``"

end
