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
begin

nonterminal 
  uapred and uaexpr and 
  apexpr and apexprs and
  uzdecls and uzdecl

syntax
  "_apexprs"            :: "[apexpr, apexprs] => apexprs" ("_,/ _")
  ""                    :: "apexpr => apexprs" ("_")
  "_apexpr_brack"       :: "apexpr \<Rightarrow> apexpr" ("'(_')")
  "_apexpr_pred_var"    :: "idt \<Rightarrow> apexpr" ("@(_)")
  "_apexpr_expr_var"    :: "idt \<Rightarrow> apexpr" ("(_)")
  "_apexpr_evar"        :: "('a, 'm) PVAR \<Rightarrow> apexpr" ("$_" [999] 999)
  "_apexpr_subst"       :: "apexpr \<Rightarrow> apexpr \<Rightarrow> ('a, 'm) PVAR \<Rightarrow> apexpr" ("(_[_'/_])" [999,999] 1000)
  "_apexpr_lit"         :: "'a \<Rightarrow> apexpr" ("\<guillemotleft>_\<guillemotright>")
  "_apexpr_true"        :: "apexpr" ("true")
  "_apexpr_false"       :: "apexpr" ("false")
  "_apexpr_op1"         :: "idt \<Rightarrow> apexpr \<Rightarrow> apexpr" ("_'(_')")
  "_apexpr_op2"         :: "idt \<Rightarrow> apexpr \<Rightarrow> apexpr \<Rightarrow> apexpr" ("_'(_,_')")
  "_apexpr_op3"         :: "idt \<Rightarrow> apexpr \<Rightarrow> apexpr \<Rightarrow> apexpr \<Rightarrow> apexpr" ("_'(_,_,_')")

(* Predicate Parser *)

syntax
  "_uapred_top_clos" :: "uapred \<Rightarrow> bool" ("(1[_])")
  "_uapred_quote"    :: "uapred \<Rightarrow> 'a WF_ALPHA_PREDICATE" ("(1``_``)")
  "_uapred_brack"    :: "uapred \<Rightarrow> uapred" ("'(_')" [0] 900)
  "_uapred_op1"      :: "idt \<Rightarrow> uapred \<Rightarrow> uapred" ("_'(_')")
  "_uapred_op2"      :: "idt \<Rightarrow> uapred \<Rightarrow> uapred \<Rightarrow> uapred" ("_'(_,_')")
  "_uapred_op3"      :: "idt \<Rightarrow> uapred \<Rightarrow> uapred \<Rightarrow> uapred \<Rightarrow> uapred" ("_'(_,_,_')")
  "_uapred_TRUE"     :: "uapred" ("TT")
  "_uapred_true"     :: "'a ALPHABET \<Rightarrow> uapred" ("true\<^bsub>_\<^esub>")
  "_uapred_tt"       :: "'a ALPHABET \<Rightarrow> uapred" ("tt\<^bsub>_\<^esub>")
  "_uapred_FALSE"    :: "uapred" ("FF")
  "_uapred_false"    :: "'a ALPHABET \<Rightarrow> uapred" ("false\<^bsub>_\<^esub>")
  "_uapred_ff"       :: "'a ALPHABET \<Rightarrow> uapred" ("ff\<^bsub>_\<^esub>")
  "_uapred_var"      :: "pttrn \<Rightarrow> uapred" ("(_)")
  "_uapred_evar"     :: "(bool, 'm) PVAR \<Rightarrow> uapred" ("$_" [999] 999)
  "_uapred_and"      :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr "\<and>" 35)
  "_uapred_or"       :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr "\<or>" 35)
  "_uapred_imp"      :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr "\<Rightarrow>" 25)
  "_uapred_iff"      :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr "\<Leftrightarrow>" 25)
  "_uapred_ref"      :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr "\<sqsubseteq>" 25)
  "_uapred_clos"     :: "uapred \<Rightarrow> uapred" ("[_]")
  "_uapred_not"      :: "uapred \<Rightarrow> uapred" ("\<not> _" [40] 40) 
  "_uapred_ext"      :: "uapred \<Rightarrow> 'a ALPHABET \<Rightarrow> uapred" (infixr "\<oplus>" 40)
  "_uapred_res"      :: "uapred \<Rightarrow> 'a ALPHABET \<Rightarrow> uapred" (infixr "\<ominus>" 40)
(*
  "_uapred_ext"      :: "uapred \<Rightarrow> 'a ALPHABET \<Rightarrow> uapred" ("_\<^bsub>+_\<^esub>" 40)
  "_uapred_res"      :: "uapred \<Rightarrow> 'a ALPHABET \<Rightarrow> uapred" ("_\<^bsub>-_\<^esub>" 40)
*)
  "_uapred_all1"     :: "('a, 'm) PVAR \<Rightarrow> uapred \<Rightarrow> uapred"  ("(3\<forall> _./ _)" [0, 10] 10) 
  "_uapred_exists1"  :: "('a, 'm) PVAR \<Rightarrow> uapred \<Rightarrow> uapred"  ("(3\<exists>+ _./ _)" [0, 10] 10) 
  "_uapred_existsres1" :: "('a, 'm) PVAR \<Rightarrow> uapred \<Rightarrow> uapred"  ("(3\<exists> _./ _)" [0, 10] 10) 
  "_uapred_pexpr"    :: "apexpr \<Rightarrow> uapred" ("\<lparr>_\<rparr>")
  "_uapred_equal"    :: "apexpr \<Rightarrow> apexpr \<Rightarrow> uapred" (infixl "=" 50)
  "_uapred_nequal"   :: "apexpr \<Rightarrow> apexpr \<Rightarrow> uapred" (infixl "\<noteq>" 50)
  "_uapred_skip"     :: "'a ALPHABET \<Rightarrow> uapred" ("II\<^bsub>_\<^esub>")
  "_uapred_seq"      :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr ";" 45)
  "_uapred_cond"     :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred \<Rightarrow> uapred" ("_ \<lhd> _ \<rhd> _")
  "_uapred_ifthenelse" :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred \<Rightarrow> uapred" ("if _ then _ else _")
  "_uapred_assign"   :: "'a VAR \<Rightarrow> 'a ALPHABET \<Rightarrow> apexpr \<Rightarrow> uapred" ("_ :=\<^bsub>_ \<^esub>_" [100] 100)
  "_uapred_conv"     :: "uapred \<Rightarrow> uapred" ("(_\<^sup>\<smile>)" [1000] 999)
  "_uapred_prime"    :: "uapred \<Rightarrow> uapred" ("_\<acute>" [1000] 1000)
  "_uapred_varext"   :: "uapred \<Rightarrow> ('a, 'm) PVAR \<Rightarrow> upred" ("_\<^bsub>+_\<^esub>")
(*
  "_uapred_zpara"    :: "uzdecls \<Rightarrow> uapred \<Rightarrow> uapred" ("[_|_]")
  "_uzdecl_basic"    :: "'a VAR \<Rightarrow> 'a VAR \<Rightarrow> uzdecl" (infix ":" 45)
  ""                 :: "uzdecl => uzdecls"             ("_")
  "_uzdecls"         :: "[uzdecl, uzdecls] => uzdecls" ("_,/ _")
*)

translations
  "_uapred_brack p"     => "p"
  "_uapred_op1 f x"     => "f x"
  "_uapred_op2 f x y"   => "f x y"
  "_uapred_op3 f x y z" => "f x y z" 
  "_uapred_quote p"     => "p"
  "_uapred_top_clos p"  == "CONST TautologyA p"
  "_uapred_TRUE"        == "CONST TRUE"
  "_uapred_true a"      == "CONST TrueA a"
  "_uapred_tt a"        => "CONST TrueA a"
  "_uapred_FALSE"       == "CONST FALSE"
  "_uapred_false a"     == "CONST FalseA a"
  "_uapred_ff a"        => "CONST FalseA a"
  "_uapred_var x"       => "x"
  "_uapred_evar x"      == "CONST VarAP x"
  "_uapred_and p q"     == "CONST AndA p q"
  "_uapred_or p q"      == "CONST OrA p q"
  "_uapred_imp p q"     == "CONST ImpliesA p q"
  "_uapred_ref p q"     == "CONST RefA p q"
  "_uapred_iff p q"     == "CONST IffA p q"
  "_uapred_clos p"      == "CONST ClosureA p"
  "_uapred_not p"       == "CONST NotA p"
  "_uapred_ext a p"     == "CONST ExtA a p"
  "_uapred_res a p"     == "CONST ResA a p"
  "_uapred_all1 x p"    == "CONST ForallA \<lbrace>x\<down>\<rbrace> p"
  "_uapred_exists1 x p" == "CONST ExistsA \<lbrace>x\<down>\<rbrace> p"
  "_uapred_existsres1 x p" == "CONST ExistsResA \<lbrace>x\<down>\<rbrace> p"
  "_uapred_pexpr e"     == "CONST APExprA e"
  "_uapred_equal e f"   == "CONST APEqualA e f"
  "_uapred_nequal e f"  == "CONST NotA (CONST EqualA e f)"
  "_uapred_skip a"      == "CONST SkipA a"
  "_uapred_seq p q"     => "CONST SemiA p q"
  "_uapred_cond p q r"  == "CONST CondA p q r"
  "_uapred_ifthenelse b p q"  => "CONST CondA p b q"
  "_uapred_assign x a e" == "CONST PAssignA x a e"
  "_uapred_conv x"      => "CONST ConvA x"
  "_uapred_prime x"     == "CONST ConvA x"
  "_uapred_varext p x"  == "CONST VarExtA p x\<down>"

(* Expression Parser *)

syntax
  "_uaexpr_brack"    :: "uaexpr \<Rightarrow> uaexpr" ("'(_')" [0] 700)
  "_uaexpr_true"     :: "uaexpr" ("true")
  "_uaexpr_false"    :: "uaexpr" ("false")
  "_uaexpr_var"      :: "pttrn \<Rightarrow> uaexpr" ("_")
  "_uaexpr_evar"     :: "'a VAR \<Rightarrow> uaexpr" ("$_" [500] 500)
  "_uaexpr_substp"   :: "uapred \<Rightarrow> apexpr \<Rightarrow> ('a, 'm) PVAR \<Rightarrow> uapred" ("(_[_'/_])" [999,999] 1000)
  "_uaexpr_member"   :: "uaexpr \<Rightarrow> uaexpr \<Rightarrow> uaexpr" (infix ":" 45)
  "_uaexpr_coerce"   :: "uaexpr \<Rightarrow> pttrn \<Rightarrow> uaexpr" ("_\<Colon>_" [60,60] 65)

translations
  "_uaexpr_brack e"      => "e"
  "_uaexpr_true"         == "CONST TrueAE"
  "_uaexpr_false"        == "CONST FalseAE"
  "_uaexpr_var x"        => "x" 
  "_uaexpr_evar x"       == "CONST VarAE x"
  "_uaexpr_substp p e x" == "CONST PSubstA p e x"
  "_uaexpr_coerce e t"   == "CONST CoerceAE e t"

translations
  "_apexpr_evar x"             == "CONST VarAPE x"
  "_apexpr_expr_var e"         => "e"
  "_apexpr_brack e"            => "e"
  "_apexpr_lit v"              == "CONST LitAPE v"
  "_apexpr_true"               == "CONST TrueAPE"
  "_apexpr_false"              == "CONST FalseAPE"
  "_apexpr_op1 f x"            == "CONST Op1APE f x"
  "_apexpr_op2 f x y"          == "CONST Op2APE f x y"
  "_apexpr_op3 f x y z"        == "CONST Op3APE f x y z"

syntax
  (* Data Structures *)
  "_apexpr_plus"          :: "apexpr \<Rightarrow> apexpr \<Rightarrow> apexpr" (infixl "+" 65)
  "_apexpr_mult"          :: "apexpr \<Rightarrow> apexpr \<Rightarrow> apexpr" (infixl "*" 70)
  "_apexpr_div"           :: "apexpr \<Rightarrow> apexpr \<Rightarrow> apexpr" (infixl "'/" 70)
  "_apexpr_minus"         :: "apexpr \<Rightarrow> apexpr \<Rightarrow> apexpr" (infixl "-" 65)
  "_apexpr_max"           :: "apexpr \<Rightarrow> apexpr \<Rightarrow> apexpr" ("max'(_, _')")
  "_apexpr_min"           :: "apexpr \<Rightarrow> apexpr \<Rightarrow> apexpr" ("min'(_, _')")
  "_apexpr_less"          :: "apexpr \<Rightarrow> apexpr \<Rightarrow> apexpr" (infixr "<" 25)
  "_apexpr_less_eq"       :: "apexpr \<Rightarrow> apexpr \<Rightarrow> apexpr" (infixr "\<le>" 25)
  "_apexpr_greater"       :: "apexpr \<Rightarrow> apexpr \<Rightarrow> apexpr" (infixr ">" 25)
  "_apexpr_greater_eq"    :: "apexpr \<Rightarrow> apexpr \<Rightarrow> apexpr" (infixr "\<ge>" 25)

translations
  "_apexpr_plus x y"            == "CONST PlusAPE x y"
  "_apexpr_mult x y"            == "CONST MultAPE x y"
  "_apexpr_div x y"             == "CONST DivAPE x y"
  "_apexpr_max x y"             == "CONST MaxAPE x y"
  "_apexpr_min x y"             == "CONST MinAPE x y"
  "_apexpr_less x y"            == "CONST LessAPE x y"
  "_apexpr_less_eq x y"         == "CONST LessEqAPE x y"
  "_apexpr_greater x y"         == "CONST LessAPE y x"
  "_apexpr_greater_eq x y"      == "CONST LessEqAPE y x"

  
(* Big operators *)

default_sort type

syntax
  "_uapred_index" :: "('b \<Rightarrow> 'a WF_ALPHA_PREDICATE) \<Rightarrow> 'b \<Rightarrow> uapred" ("_<_>" 50)
  "_uapred_ANDI1" :: "'a ALPHABET \<Rightarrow> pttrns \<Rightarrow> uapred \<Rightarrow> uapred" ("(3\<And>\<^bsub>_\<^esub> _./ _)" [0, 0, 10] 10)
  "_uapred_ANDI"  :: "'a ALPHABET \<Rightarrow> pttrn \<Rightarrow> 'b set \<Rightarrow> uapred \<Rightarrow> uapred"  ("(3\<And>\<^bsub>_\<^esub> _:_./ _)" [0, 0, 0, 10] 10)
  "_uapred_ORDI1" :: "'a ALPHABET \<Rightarrow> pttrns \<Rightarrow> uapred \<Rightarrow> uapred" ("(3\<Or>\<^bsub>_\<^esub> _./ _)" [0, 0, 10] 10)
  "_uapred_ORDI"  :: "'a ALPHABET \<Rightarrow> pttrn \<Rightarrow> 'b set \<Rightarrow> uapred \<Rightarrow> uapred"  ("(3\<Or>\<^bsub>_\<^esub> _:_./ _)" [0, 0, 10] 10)
  "_uapred_INF1"  :: "'a ALPHABET \<Rightarrow> pttrns \<Rightarrow> uapred \<Rightarrow> uapred" ("(3\<Sqinter>\<^bsub>_\<^esub> _./ _)" [0, 0, 10] 10)
  "_uapred_INF"   :: "'a ALPHABET \<Rightarrow> pttrn \<Rightarrow> 'b set \<Rightarrow> uapred \<Rightarrow> uapred"  ("(3\<Sqinter>\<^bsub>_\<^esub> _:_./ _)" [0, 0, 0, 10] 10)
  "_uapred_SUP1"  :: "'a ALPHABET \<Rightarrow> pttrns \<Rightarrow> uapred \<Rightarrow> uapred" ("(3\<Squnion>\<^bsub>_\<^esub> _./ _)" [0, 0, 10] 10)
  "_uapred_SUP"   :: "'a ALPHABET \<Rightarrow> pttrn \<Rightarrow> 'b set \<Rightarrow> uapred \<Rightarrow> uapred"  ("(3\<Squnion>\<^bsub>_\<^esub> _:_./ _)" [0, 0, 0, 10] 10)

translations
  "_uapred_index f i"     => "f i"
  "_uapred_ANDI1 a x y B" => "AND[a] x. AND[a] y. B"
  "_uapred_ANDI1 a x B"   == "CONST AANDI a CONST UNIV (%x. B)"
  "_uapred_ANDI a x A B"  == "CONST AANDI a A (%x. B)"
  "_uapred_ORDI1 a x y B" => "OR[a] x. OR[a] y. B"
  "_uapred_ORDI1 a x B"   == "CONST AORDI a CONST UNIV (%x. B)"
  "_uapred_ORDI a x A B"  == "CONST AORDI a A (%x. B)"
  "_uapred_INF1 a x B"    == "CONST InfiA a CONST UNIV (%x. B)"
  "_uapred_INF a x A B"   == "CONST InfiA a A (%x . B)"
  "_uapred_SUP1 a x B"    == "CONST SuprA a CONST UNIV (%x. B)"
  "_uapred_SUP a x A B"   == "CONST SuprA a A (%x . B)"

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

end
