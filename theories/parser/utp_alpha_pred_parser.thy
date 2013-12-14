theory utp_alpha_pred_parser
  imports
  "../alpha/utp_alpha_pred"
  "../alpha/utp_alpha_rel"
  "../alpha/utp_alpha_expr"
  "../tactics/utp_pred_tac"
  "../tactics/utp_expr_tac"
  "../tactics/utp_rel_tac"
  "../poly/utp_poly_alpha_expr"
  "../theories/utp_theory"
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

(* Predicate Parser *)

syntax
  "_uapred_top_clos" :: "uapred \<Rightarrow> bool" ("(1[_])")
  "_uapred_quote"    :: "uapred \<Rightarrow> 'a WF_ALPHA_PREDICATE" ("(1``_``)")
  "_uapred_brack"    :: "uapred \<Rightarrow> uapred" ("'(_')" [0] 900)
  "_uapred_TRUE"     :: "uapred" ("true")
  "_uapred_true"     :: "'a ALPHABET \<Rightarrow> uapred" ("true\<^bsub>_\<^esub>")
  "_uapred_FALSE"    :: "uapred" ("false")
  "_uapred_false"    :: "'a ALPHABET \<Rightarrow> uapred" ("false\<^bsub>_\<^esub>")
  "_uapred_var"      :: "pttrn \<Rightarrow> uapred" ("(_)")
(*  "_uapred_evar"     :: "idt \<Rightarrow> uapred" ("$_") *)
  "_uapred_and"      :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr "\<and>" 35)
  "_uapred_or"       :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr "\<or>" 35)
  "_uapred_imp"      :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr "\<Rightarrow>" 25)
  "_uapred_iff"      :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr "\<Leftrightarrow>" 25)
  "_uapred_ref"      :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr "\<sqsubseteq>" 25)
  "_uapred_clos"     :: "uapred \<Rightarrow> uapred" ("[_]")
  "_uapred_not"      :: "uapred \<Rightarrow> uapred" ("\<not> _" [40] 40) 
(*  "_uapred_ext"      :: "uapred \<Rightarrow> 'a ALPHABET \<Rightarrow> uapred" (infixr "\<oplus>" 40) *)
  "_uapred_ext"      :: "uapred \<Rightarrow> 'a ALPHABET \<Rightarrow> uapred" ("_\<^bsub>+_\<^esub>" 40)
  "_uapred_all1"     :: "pttrn \<Rightarrow> uapred \<Rightarrow> uapred"  ("(3\<forall> _./ _)" [0, 10] 10) 
  "_uapred_exists1"  :: "pttrn \<Rightarrow> uapred \<Rightarrow> uapred"  ("(3\<exists>+ _./ _)" [0, 10] 10) 
  "_uapred_existsres1" :: "pttrn \<Rightarrow> uapred \<Rightarrow> uapred"  ("(3\<exists>- _./ _)" [0, 10] 10) 
  "_uapred_pexpr"    :: "apexpr \<Rightarrow> uapred" ("\<lparr>_\<rparr>")
  "_uapred_equal"    :: "apexpr \<Rightarrow> apexpr \<Rightarrow> uapred" (infixl "=" 50)
  "_uapred_nequal"   :: "apexpr \<Rightarrow> apexpr \<Rightarrow> uapred" (infixl "\<noteq>" 50)
  "_uapred_skip"     :: "'a ALPHABET \<Rightarrow> uapred" ("II\<^bsub>_\<^esub>")
  "_uapred_seq"      :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr ";" 45)
  "_uapred_cond"     :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred \<Rightarrow> uapred" ("_ \<triangleleft> _ \<triangleright> _")
  "_uapred_assign"   :: "'a VAR \<Rightarrow> 'a ALPHABET \<Rightarrow> apexpr \<Rightarrow> uapred" ("_ :=\<^bsub>_ \<^esub>_" [100] 100)
  "_uapred_top"      :: "'a THEORY \<Rightarrow> 'a ALPHABET \<Rightarrow> uapred" ("\<top>\<^bsub>_[_]\<^esub>")
  "_uapred_bot"      :: "'a THEORY \<Rightarrow> 'a ALPHABET \<Rightarrow> uapred" ("\<bottom>\<^bsub>_[_]\<^esub>")
  "_uapred_joint"    :: "uapred \<Rightarrow> 'a THEORY \<Rightarrow> 'a ALPHABET \<Rightarrow> uapred \<Rightarrow> uapred" (infixl "\<squnion>\<^bsub>_[_]\<^esub>" 65)
  "_uapred_meett"    :: "uapred \<Rightarrow> 'a THEORY \<Rightarrow> 'a ALPHABET \<Rightarrow> uapred \<Rightarrow> uapred" (infixl "\<sqinter>\<^bsub>_[_]\<^esub>" 70)
  "_uapred_zpara"    :: "uzdecls \<Rightarrow> uapred \<Rightarrow> uapred" ("[_|_]")
  "_uzdecl_basic"    :: "'a VAR \<Rightarrow> 'a VAR \<Rightarrow> uzdecl" (infix ":" 45)
  ""                 :: "uzdecl => uzdecls"             ("_")
  "_uzdecls"         :: "[uzdecl, uzdecls] => uzdecls" ("_,/ _")

translations
  "_uapred_brack p"     => "p"
  "_uapred_quote p"     => "p"
  "_uapred_top_clos p"  == "CONST TautologyA p"
  "_uapred_TRUE"        == "CONST TRUE"
  "_uapred_true a"      == "CONST TrueA a"
  "_uapred_FALSE"       == "CONST FALSE"
  "_uapred_false a"     == "CONST FalseA a"
  "_uapred_var x"       => "x"
(*  "_uapred_evar x"      == "CONST VarA x" *)
  "_uapred_and p q"     == "CONST AndA p q"
  "_uapred_or p q"      == "CONST OrA p q"
  "_uapred_imp p q"     == "CONST ImpliesA p q"
  "_uapred_ref p q"     == "CONST RefA p q"
  "_uapred_iff p q"     == "CONST IffA p q"
  "_uapred_clos p"      == "CONST ClosureA p"
  "_uapred_not p"       == "CONST NotA p"
  "_uapred_ext a p"     == "CONST ExtA a p"
  "_uapred_all1 x p"    == "CONST ForallA \<lbrace>x\<rbrace> p"
  "_uapred_exists1 x p" == "CONST ExistsA \<lbrace>x\<rbrace> p"
  "_uapred_existsres1 x p" == "CONST ExistsResA \<lbrace>x\<rbrace> p"
  "_uapred_equal e f"   == "CONST APEqualA e f"
  "_uapred_nequal e f"  == "CONST NotA (CONST EqualA e f)"
  "_uapred_skip"        == "CONST SkipA"
  "_uapred_seq p q"     => "CONST SemiA p q"
  "_uapred_cond p q r"  == "CONST CondA p q r"
  "_uapred_assign x a e" == "CONST PAssignA x a e"
  "_uapred_top T a"     == "CONST TopT T a"
  "_uapred_bot T a"     == "CONST BotT T a"
  "_uapred_joint T a"   == "CONST JoinT T a"
  "_uapred_meett T a"   == "CONST MeetT T a"
  "_uapred_zpara ds p"  == "CONST AndA ds p"

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


(* Parser sanity check *)

term "``p \<and> q``"

term "``$x = false``"

term "``p[v/x]``"

term "``x :=\<^bsub>\<lbrace>x\<down>,x\<down>\<acute>\<rbrace>\<^esub> true``"

term "``p\<^bsub>+\<lbrace>x\<down>\<rbrace>\<^esub>``"

end
