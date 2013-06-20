(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_pred_parser.thy                                                  *)
(* Author: Frank Zeyda and Simon Foster, University of York (UK)              *)
(******************************************************************************)

header {* Predicate Parser *}

theory utp_pred_parser
  imports
  "../core/utp_pred"
  "../core/utp_rel"
  "../core/utp_expr"
begin

nonterminal upred and upreds and uexpr and uexprs

syntax
  "_upred_top_clos" :: "upred \<Rightarrow> bool" ("(1[_])")
  "_upred_quote"    :: "upred \<Rightarrow> 'a WF_PREDICATE" ("(1`_`)")
  "_upred_brack"    :: "upred \<Rightarrow> upred" ("'(_')")
  "_upred_true"     :: "upred" ("true")
  "_upred_false"    :: "upred" ("false")
  "_upred_var"      :: "pttrn \<Rightarrow> upred" ("(_)")
  "_upred_evar"     :: "'a VAR \<Rightarrow> upred" ("$_" [999] 999)
  "_upred_and"      :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<and>" 35)
  "_upred_or"       :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<or>" 35)
  "_upred_imp"      :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<Rightarrow>" 25)
  "_upred_iff"      :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<Leftrightarrow>" 25)
  "_upred_ref"      :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<sqsubseteq>" 25)
  "_upred_clos"     :: "upred \<Rightarrow> upred" ("[_]")
  "_upred_not"      :: "upred \<Rightarrow> upred" ("\<not> _" [40] 40)
  "_upred_all1"     :: "'a VAR \<Rightarrow> upred \<Rightarrow> upred"  ("(3\<forall> _./ _)" [0, 10] 10) 
  "_upred_exists1"  :: "'a VAR \<Rightarrow> upred \<Rightarrow> upred"  ("(3\<exists> _./ _)" [0, 10] 10) 
  "_upred_equal"    :: "uexpr \<Rightarrow> uexpr \<Rightarrow> upred" (infixl "=" 50)
  "_upred_uexpr"    :: "uexpr \<Rightarrow> upred" ("\<lparr>_\<rparr>")
  "_upred_skip"     :: "upred" ("II")
  "_upred_skipa"    :: "'VALUE VAR set \<Rightarrow> upred" ("II\<^bsub>_\<^esub>")
  "_upred_seq"      :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr ";" 36)
  "_upred_cond"     :: "upred \<Rightarrow> upred \<Rightarrow> upred \<Rightarrow> upred" ("_ \<lhd> _ \<rhd> _")
  "_upred_assigna"  :: "'a VAR \<Rightarrow> 'a VAR set \<Rightarrow> uexpr \<Rightarrow> upred" ("_ :=\<^bsub>_ \<^esub>_" [100] 100)
  "_upred_assign"   :: "'a VAR \<Rightarrow> uexpr \<Rightarrow> upred" ("_ := _" [100] 100)
  "_upred_assigns"  :: "string \<Rightarrow> uexpr \<Rightarrow> upred" ("_ := _" [100] 100)
  "_upred_conv"     :: "upred \<Rightarrow> upred" ("(_\<^sup>\<smile>)" [1000] 999)
  "_upred_prime"    :: "upred \<Rightarrow> upred" ("_\<acute>" [1000] 1000)
  "_upred_varopen"  :: "'a VAR \<Rightarrow> upred" ("var _")
  "_upred_varclose" :: "'a VAR \<Rightarrow> upred" ("end _")

abbreviation AssignS :: "string \<Rightarrow> 'VALUE WF_EXPRESSION \<Rightarrow> 'VALUE WF_PREDICATE" where
"AssignS x e \<equiv> (MkPlain x (expr_type e) False) :=p e"

translations
  "_upred_brack p"     => "p"
  "_upred_quote p"     => "p"
  "_upred_top_clos p"  == "taut p"
  "_upred_true"        == "CONST TrueP"
  "_upred_false"       == "CONST FalseP"
  "_upred_var x"       => "x"
  "_upred_evar x"      == "CONST VarP x"
  "_upred_and p q"     == "CONST AndP p q"
  "_upred_or p q"      == "CONST OrP p q"
  "_upred_imp p q"     == "CONST ImpliesP p q"
  "_upred_ref p q"     == "CONST RefP p q"
  "_upred_iff p q"     == "CONST IffP p q"
  "_upred_clos p"      == "CONST ClosureP p"
  "_upred_not p"       == "CONST NotP p"
  "_upred_all1 x p"    == "CONST ForallP {x} p"
  "_upred_exists1 x p" == "CONST ExistsP {x} p"
  "_upred_equal e f"   == "CONST EqualP e f"
  "_upred_uexpr e"     == "CONST ExprP e"
  "_upred_skip"        == "CONST SkipR"
  "_upred_skipa vs"    == "CONST SkipRA vs"
  "_upred_seq p q"     => "CONST SemiR p q"
  "_upred_cond p q r"  == "CONST CondR p q r"
  "_upred_assign x e"  == "CONST AssignR x e"
  "_upred_assigns x e" == "CONST AssignS x e"
  "_upred_assigna x xs e" == "CONST AssignRA x xs e"
  "_upred_conv x"      => "CONST ConvR x"
  "_upred_prime x"     == "CONST ConvR x"
  "_upred_varopen x"   == "CONST VarOpenP x"
  "_upred_varclose x"  == "CONST VarCloseP x"

term "`x \<Rightarrow> $y\<acute>`"

(* Expression Parser *)

syntax
  "_uexprs"             :: "[uexpr, uexprs] => uexprs" ("_,/ _")
  ""                    :: "uexpr => uexprs" ("_")
  "_uexpr_brack"        :: "uexpr \<Rightarrow> uexpr" ("'(_')")
  "_uexpr_quote"        :: "uexpr \<Rightarrow> 'a WF_EXPRESSION" ("(1^_^)")
  "_uexpr_true"         :: "uexpr" ("true")
  "_uexpr_false"        :: "uexpr" ("false")
  "_uexpr_var"          :: "pttrn \<Rightarrow> uexpr" ("_")
  "_uexpr_evar"         :: "'a VAR \<Rightarrow> uexpr" ("$_" [999] 999)
  "_uexpr_substp"       :: "upred \<Rightarrow> uexpr \<Rightarrow> 'a VAR \<Rightarrow> upred" ("(_[_'/_])" [999,999] 1000)
  "_uexpr_prime"        :: "uexpr \<Rightarrow> uexpr" ("_\<acute>" [1000] 1000)
  "_uexpr_minus"        :: "uexpr \<Rightarrow> uexpr \<Rightarrow> uexpr" (infixl "-" 65) 
  "_uexpr_lesseq"       :: "uexpr \<Rightarrow> uexpr \<Rightarrow> uexpr" (infixr "\<le>" 25)
  "_upred_lesseq"       :: "uexpr \<Rightarrow> uexpr \<Rightarrow> upred" (infixr "\<le>" 25)
  "_uexpr_list"         :: "uexprs \<Rightarrow> uexpr" ("\<langle>_\<rangle>")
  "_uexpr_list_nil"     :: "uexpr" ("\<langle>\<rangle>")
  "_uexpr_list_append"  :: "uexpr \<Rightarrow> uexpr \<Rightarrow> uexpr" (infixr "^" 65)
  "_uexpr_fset"         :: "uexprs \<Rightarrow> uexpr" ("{_}")
  "_uexpr_fset_empty"   :: "uexpr" ("{}")
  "_uexpr_fset_union"   :: "uexpr \<Rightarrow> uexpr \<Rightarrow> uexpr" (infixl "\<union>" 65)
  "_uexpr_fset_inter"   :: "uexpr \<Rightarrow> uexpr \<Rightarrow> uexpr" (infixl "\<inter>" 70)
  "_uexpr_fset_member"  :: "uexpr \<Rightarrow> uexpr \<Rightarrow> upred" ("(_/ \<in> _)" [51, 51] 50)
  "_uexpr_fset_nmember" :: "uexpr \<Rightarrow> uexpr \<Rightarrow> upred" ("(_/ \<notin> _)" [51, 51] 50)
  "_uexpr_pair"         :: "uexpr \<Rightarrow> uexpr \<Rightarrow> uexpr" ("'(_, _')")
  "_uexpr_pair_fst"     :: "uexpr \<Rightarrow> uexpr" ("\<pi>\<^sub>1 _")
  "_uexpr_pair_snd"     :: "uexpr \<Rightarrow> uexpr" ("\<pi>\<^sub>2 _")
  "_uexpr_name"         :: "NAME \<Rightarrow> uexpr" ("&_" [999] 999)

translations
  "_uexpr_brack e"      => "e"
  "_uexpr_quote e"      => "e"
  "_uexpr_true"         == "CONST TrueE"
  "_uexpr_false"        == "CONST FalseE"
  "_uexpr_var x"        => "x" 
  "_uexpr_evar x"       == "CONST VarE x"
  "_uexpr_substp p e x" == "CONST SubstP p e x"
  "_uexpr_prime e"      == "CONST RenameE e (CONST SS)"
  "_uexpr_minus e f"   == "CONST Op2E CONST utminus e f"
  "_uexpr_lesseq e f"  == "CONST Op2E CONST ulesseq e f"
  "_upred_lesseq e f"  == "CONST ExprP (CONST Op2E CONST ulesseq e f)"
  "_uexpr_list_nil"    == "CONST LitE (CONST MkList CONST Nil)"
  "_uexpr_list_append e f" == "CONST Op2E (CONST ConcatV) e f"
  "_uexpr_list (_uexprs x xs)" == "CONST Op2E (CONST ConsV) x (_uexpr_list xs)"
  "_uexpr_list x" == "CONST Op2E (CONST ConsV) x (CONST LitE (CONST NilV))"
  "_uexpr_fset (_uexprs x xs)" == "CONST Op2E (CONST FInsertV) x (_uexpr_list xs)"
  "_uexpr_fset x" == "CONST Op2E (CONST FInsertV) x (CONST LitE (CONST FEmptyV))"
  "_uexpr_fset_empty" == "CONST LitE (CONST FEmptyV)"
  "_uexpr_fset_union xs ys" == "CONST Op2E (CONST FUnionV) xs ys"
  "_uexpr_fset_inter xs ys" == "CONST Op2E (CONST FInterV) xs ys"
  "_uexpr_fset_member x xs"  == "CONST ExprP (CONST Op2E (CONST FMemberV) x xs)"
  "_uexpr_fset_nmember x xs" == "CONST ExprP (CONST Op2E (CONST FNMemberV) x xs)"
  "_uexpr_pair x y"         == "CONST Op2E (CONST PairV) x y"
  "_uexpr_pair_fst x"       == "CONST Op1E (CONST FstV) x"
  "_uexpr_pair_snd x"       == "CONST Op1E (CONST SndV) x"
  "_uexpr_name x"           == "CONST LitE (CONST MkName) x"

(* Some regression tests *)
term "`x \<in> {true,false} \<union> {false,true}`"
term "`($x)\<acute> = $y\<acute>`"
term "`p[($x)\<acute>/y\<acute>]`"
term "`\<lparr>true\<rparr>`"
term "`a = \<langle>$x, true\<rangle> ^ \<langle>false, $y\<rangle>`"
term "`a = \<pi>\<^sub>1 (true, false)`"

end

