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
  "../poly/utp_poly_expr"
begin

nonterminal 
  upred and upreds and 
  uexpr and uexprs and
  pexpr and pexprs

section {* Core Polymorphic Expression Syntax *}

syntax
  "_pexpr_quote"        :: "pexpr \<Rightarrow> ('a, 'm) WF_PEXPRESSION" ("(1\<parallel>_\<parallel>)")
  "_pexpr_pred_quote"   :: "pexpr \<Rightarrow> 'a WF_PREDICATE" ("(1``_``)")
  "_pexprs"             :: "[pexpr, pexprs] => pexprs" ("_,/ _")
  ""                    :: "pexpr => pexprs" ("_")
  "_pexpr_brack"        :: "pexpr \<Rightarrow> pexpr" ("'(_')")
  "_pexpr_pred_var"     :: "idt \<Rightarrow> pexpr" ("@(_)")
  "_pexpr_expr_var"     :: "idt \<Rightarrow> pexpr" ("(_)")
  "_pexpr_evar"         :: "('a, 'm) PVAR \<Rightarrow> pexpr" ("$_" [999] 999)
  "_pexpr_subst"        :: "pexpr \<Rightarrow> pexpr \<Rightarrow> ('a, 'm) PVAR \<Rightarrow> pexpr" ("(_[_'/_])" [999,999] 1000)
  "_pexpr_prime"        :: "pexpr \<Rightarrow> pexpr" ("_\<acute>" [1000] 1000)
  "_pexpr_erase"        :: "pexpr \<Rightarrow> pexpr" ("_\<down>" [1000] 1000)

translations
  "_pexpr_quote e"             => "e"
  "_pexpr_pred_quote e"        == "CONST PExprP e"
  "_pexpr_pred_var p"          == "CONST PredPE p"
  "_pexpr_expr_var v"          => "v"
  "_pexpr_evar x"              == "CONST PVarPE x"
  "_pexpr_brack e"             => "e"
  "_pexpr_subst e v x"         == "CONST PSubstPE e v x"
  "_pexpr_prime e"             == "CONST PermPE (CONST SS) e"
  "_pexpr_erase e"             == "CONST ErasePE e" 

section {* Predicate Parser *}

syntax
  "_upred_top_clos" :: "upred \<Rightarrow> bool" ("(1[_])")
  "_upred_quote"    :: "upred \<Rightarrow> 'a WF_PREDICATE" ("(1`_`)")
  "_upred_brack"    :: "upred \<Rightarrow> upred" ("'(_')")
  "_upred_true"     :: "upred" ("true")
  "_upred_false"    :: "upred" ("false")
  "_upred_var"      :: "pttrn \<Rightarrow> upred" ("(_)")
  "_upred_evar"     :: "(bool, 'm) PVAR \<Rightarrow> upred" ("$_" [999] 999)
  "_upred_and"      :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<and>" 35)
  "_upred_or"       :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<or>" 35)
  "_upred_imp"      :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<Rightarrow>" 25)
  "_upred_iff"      :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<Leftrightarrow>" 25)
  "_upred_ref"      :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<sqsubseteq>" 25)
  "_upred_clos"     :: "upred \<Rightarrow> upred" ("[_]")
  "_upred_not"      :: "upred \<Rightarrow> upred" ("\<not> _" [40] 40)
  "_upred_all1"     :: "('a, 'm) PVAR \<Rightarrow> upred \<Rightarrow> upred"  ("(3\<forall> _./ _)" [0, 10] 10) 
  "_upred_exists1"  :: "('a, 'm) PVAR \<Rightarrow> upred \<Rightarrow> upred"  ("(3\<exists> _./ _)" [0, 10] 10) 
  "_upred_equal"    :: "pexpr \<Rightarrow> pexpr \<Rightarrow> upred" (infixl "=" 50)
  "_upred_pexpr"    :: "pexpr \<Rightarrow> upred" ("\<lparr>_\<rparr>")
  "_upred_skip"     :: "upred" ("II")
  "_upred_skipa"    :: "'VALUE VAR set \<Rightarrow> upred" ("II\<^bsub>_\<^esub>")
  "_upred_seq"      :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr ";" 36)
  "_upred_cond"     :: "upred \<Rightarrow> upred \<Rightarrow> upred \<Rightarrow> upred" ("_ \<lhd> _ \<rhd> _")
  "_upred_assigna"  :: "'a VAR \<Rightarrow> 'a VAR set \<Rightarrow> uexpr \<Rightarrow> upred" ("_ :=\<^bsub>_ \<^esub>_" [100] 100)
  "_upred_assign"   :: "('a, 'm) PVAR \<Rightarrow> pexpr \<Rightarrow> upred" ("_ := _" [100] 100)
  "_upred_assigns"  :: "string \<Rightarrow> uexpr \<Rightarrow> upred" ("_ := _" [100] 100)
  "_upred_conv"     :: "upred \<Rightarrow> upred" ("(_\<^sup>\<smile>)" [1000] 999)
  "_upred_prime"    :: "upred \<Rightarrow> upred" ("_\<acute>" [1000] 1000)
  "_upred_varopen"  :: "('a, 'm) PVAR \<Rightarrow> upred" ("var _")
  "_upred_varclose" :: "('a, 'm) PVAR \<Rightarrow> upred" ("end _")
  "_upred_substp"   :: "upred \<Rightarrow> pexpr \<Rightarrow> ('a, 'm) PVAR \<Rightarrow> upred" ("(_[_'/_])" [999,999] 1000)

(*
abbreviation AssignS :: "string \<Rightarrow> 'VALUE WF_EXPRESSION \<Rightarrow> 'VALUE WF_PREDICATE" where
"AssignS x e \<equiv> (MkPlain x (expr_type e) False) :=p e"
*)

translations
  "_upred_brack p"     => "p"
  "_upred_quote p"     => "p"
  "_upred_top_clos p"  == "taut p"
  "_upred_true"        == "CONST TrueP"
  "_upred_false"       == "CONST FalseP"
  "_upred_var x"       => "x"
  "_upred_evar x"      == "CONST VarP x\<down>"
  "_upred_and p q"     == "CONST AndP p q"
  "_upred_or p q"      == "CONST OrP p q"
  "_upred_imp p q"     == "CONST ImpliesP p q"
  "_upred_ref p q"     == "CONST RefP p q"
  "_upred_iff p q"     == "CONST IffP p q"
  "_upred_clos p"      == "CONST ClosureP p"
  "_upred_not p"       == "CONST NotP p"
  "_upred_all1 x p"    == "CONST ForallP {x\<down>} p"
  "_upred_exists1 x p" == "CONST ExistsP {x\<down>} p"
  "_upred_equal e f"   == "CONST PEqualP e f"
  "_upred_pexpr e"     == "CONST PExprP e"
  "_upred_skip"        == "CONST SkipR"
  "_upred_skipa vs"    == "CONST SkipRA vs"
  "_upred_seq p q"     => "CONST SemiR p q"
  "_upred_cond p q r"  == "CONST CondR p q r"
  "_upred_assign x e"  == "CONST PAssignR x e"
  "_upred_assigna x xs e" == "CONST AssignRA x xs e"
  "_upred_conv x"      => "CONST ConvR x"
  "_upred_prime x"     == "CONST ConvR x"
  "_upred_varopen x"   == "CONST VarOpenP x"
  "_upred_varclose x"  == "CONST VarCloseP x"
  "_upred_substp p e x" == "CONST PSubstP p e x"

term "`p[x/v]`"
term "`p[$x/y]`"
term "`x \<Rightarrow> $y\<acute>`"

section {* Core Expression Parser *}

syntax
  "_uexprs"             :: "[uexpr, uexprs] => uexprs" ("_,/ _")
  ""                    :: "uexpr => uexprs" ("_")
  "_uexpr_brack"        :: "uexpr \<Rightarrow> uexpr" ("'(_')")
  "_uexpr_quote"        :: "uexpr \<Rightarrow> 'a WF_EXPRESSION" ("(1^_^)")
  "_uexpr_true"         :: "uexpr" ("true")
  "_uexpr_false"        :: "uexpr" ("false")
  "_uexpr_var"          :: "pttrn \<Rightarrow> uexpr" ("_")
  "_uexpr_evar"         :: "'a VAR \<Rightarrow> uexpr" ("$_" [999] 999)
  "_uexpr_prime"        :: "uexpr \<Rightarrow> uexpr" ("_\<acute>" [1000] 1000)

translations
  "_uexpr_brack e"      => "e"
  "_uexpr_quote e"      => "e"
  "_uexpr_true"         == "CONST TrueE"
  "_uexpr_false"        == "CONST FalseE"
  "_uexpr_var x"        => "x" 
  "_uexpr_evar x"       == "CONST VarE x"
  "_uexpr_prime e"      == "CONST RenameE e (CONST SS)"


syntax
  (* Basic logical operators *)
  "_pexpr_equal"        :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "=" 50)
  "_pexpr_wequal"       :: "uexpr \<Rightarrow> uexpr \<Rightarrow> pexpr" (infixl "\<equiv>" 50)
  "_pexpr_true"         :: "pexpr" ("true")
  "_pexpr_false"        :: "pexpr" ("false")
  "_pexpr_and"          :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "\<and>" 35)
  "_pexpr_or"           :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "\<or>" 35)
  "_pexpr_imp"          :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "\<Rightarrow>" 25)
  "_pexpr_iff"          :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "\<Leftrightarrow>" 25)
  "_pexpr_ref"          :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "\<sqsubseteq>" 25)
  "_pexpr_clos"         :: "pexpr \<Rightarrow> pexpr" ("[_]")
  "_pexpr_not"          :: "pexpr \<Rightarrow> pexpr" ("\<not> _" [40] 40)
  "_pexpr_all1"         :: "('a, 'm) PVAR \<Rightarrow> pexpr \<Rightarrow> pexpr"  ("(3\<forall> _./ _)" [0, 10] 10) 
  "_pexpr_exists1"      :: "('a, 'm) PVAR \<Rightarrow> pexpr \<Rightarrow> pexpr"  ("(3\<exists> _./ _)" [0, 10] 10) 

syntax
  (* Relational operators *)

  "_pexpr_skip"         :: "pexpr" ("II")
  "_pexpr_skipa"        :: "'VALUE VAR set \<Rightarrow> pexpr" ("II\<^bsub>_\<^esub>")
  "_pexpr_seq"          :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr ";" 36)
  "_pexpr_cond"         :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" ("_ \<lhd> _ \<rhd> _")
  "_pexpr_assign"       :: "('a, 'm) PVAR \<Rightarrow> pexpr \<Rightarrow> pexpr" ("_ := _" [100] 100)
  "_pexpr_wassign"      :: "'m VAR \<Rightarrow> uexpr \<Rightarrow> pexpr" ("_ :\<equiv> _" [100] 100)
  "_pexpr_conv"         :: "pexpr \<Rightarrow> pexpr" ("(_\<^sup>\<smile>)" [1000] 999)
  "_pexpr_varopen"      :: "('a, 'm) PVAR \<Rightarrow> pexpr" ("var _")
  "_pexpr_varclose"     :: "('a, 'm) PVAR \<Rightarrow> pexpr" ("end _")

syntax
  (* Data Structures *)
  "_pexpr_int"          :: "int \<Rightarrow> pexpr" ("<_>")
  "_pexpr_plus"         :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "+" 65)
  "_pexpr_minus"        :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "-" 65)
  "_pexpr_less"         :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "<" 25)
  "_pexpr_less_eq"      :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "\<le>" 25)
  "_pexpr_list"         :: "pexprs \<Rightarrow> pexpr" ("\<langle>_\<rangle>")
  "_pexpr_list_nil"     :: "pexpr" ("\<langle>\<rangle>")
  "_pexpr_list_append"  :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "^" 65)
  "_pexpr_fset"         :: "pexprs \<Rightarrow> pexpr" ("{_}")
  "_pexpr_fset_empty"   :: "pexpr" ("{}")
  "_pexpr_fset_union"   :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "\<union>" 65)
  "_pexpr_fset_inter"   :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "\<inter>" 70)
  "_pexpr_fset_member"  :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" ("(_/ \<in> _)" [51, 51] 50)
  "_pexpr_fset_nmember" :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" ("(_/ \<notin> _)" [51, 51] 50)
  "_pexpr_intersync"    :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "\<parallel>\<^bsub>_\<^esub>" 75)
  "_pexpr_event"        :: "NAME \<Rightarrow> pexpr \<Rightarrow> pexpr" ("_?_" 50)

translations
  (* Basic logical operators *)
  "_pexpr_equal e f"           == "CONST EqualPE e f"
  "_pexpr_wequal e f"          == "CONST PredPE (CONST EqualP e f)"
  "_pexpr_true"                == "CONST TruePE"
  "_pexpr_false"               == "CONST FalsePE"
  "_pexpr_and p q"             == "CONST AndPE p q"
  "_pexpr_or p q"              == "CONST OrPE p q"
  "_pexpr_imp p q"             == "CONST ImpliesPE p q"
  "_pexpr_iff p q"             == "CONST IffPE p q"
  "_pexpr_ref p q"             == "CONST RefPE p q"
  "_pexpr_clos p"              == "CONST ClosurePE p"
  "_pexpr_not p"               == "CONST NotPE p"
  "_pexpr_all1 x p"            == "CONST ForallPE {x\<down>} p"
  "_pexpr_exists1 x p"         == "CONST ExistsPE {x\<down>} p"

translations
  (* Relational operators *)
  "_pexpr_skip"                == "CONST PredPE (CONST SkipR)"
  "_pexpr_skipa vs"            == "CONST PredPE (CONST SkipRA vs)"
  "_pexpr_seq p q"             == "CONST PredOp2PE (CONST SemiR) p q"
  "_pexpr_cond p q r"          == "CONST PredOp3PE (CONST CondR) p q r"
  "_pexpr_assign x v"          == "CONST AssignRPE x v"
  "_pexpr_wassign x v"         == "CONST WAssignRPE x v"
  "_pexpr_conv p"              == "CONST PredOp1PE (CONST ConvR) p"
  "_pexpr_varopen x"           == "CONST PredPE (CONST VarOpenP x\<down>)"
  "_pexpr_varclose x"          == "CONST PredPE (CONST VarCloseP x\<down>)"

translations
  (* Data Structures *)
  "_pexpr_int x"               == "CONST IntPE x"
  "_pexpr_plus x y"            == "CONST PlusPE x y"
  "_pexpr_minus x y"           == "CONST MinusPE x y"
  "_pexpr_less x y"            == "CONST LessPE x y"
  "_pexpr_less_eq x y"         == "CONST LessEqPE x y"
  "_pexpr_list_nil"            == "CONST NilPE"
  "_pexpr_list_append e f"     == "CONST ConcatPE e f"
  "_pexpr_list (_pexprs x xs)" == "CONST ConsPE x (_pexpr_list xs)"
  "_pexpr_list x"              == "CONST ConsPE x (CONST NilPE)"
  "_pexpr_fset (_pexprs x xs)" == "CONST FInsertPE x (_pexpr_fset xs)"
  "_pexpr_fset x"              == "CONST FInsertPE x CONST FEmptyPE"
  "_pexpr_fset_empty"          == "CONST FEmptyPE"
  "_pexpr_fset_union xs ys"    == "CONST FUnionPE xs ys"
  "_pexpr_fset_inter xs ys"    == "CONST FInterPE xs ys"
  "_pexpr_fset_member x xs"    == "CONST FMemberPE x xs"
  "_pexpr_fset_nmember x xs"   == "CONST FNotMemberPE x xs"
  "_pexpr_intersync p xs q"    == "CONST IntersyncPE xs p q"
  "_pexpr_event n v"           == "CONST EventPE n v"

(* Linking the predicate parser to the poly parser *)

syntax
  "_upred_lesseq"       :: "pexpr \<Rightarrow> pexpr \<Rightarrow> upred" (infixr "\<le>" 25)
  "_upred_fset_member"  :: "pexpr \<Rightarrow> pexpr \<Rightarrow> upred" ("(_/ \<in> _)" [51, 51] 50)
  "_upred_fset_nmember" :: "pexpr \<Rightarrow> pexpr \<Rightarrow> upred" ("(_/ \<notin> _)" [51, 51] 50)

translations
  "_upred_lesseq e f"        == "CONST PExprP (_pexpr_less_eq e f)"
  "_upred_fset_member x xs"  == "CONST PExprP (_pexpr_fset_member x xs)"
  "_upred_fset_nmember x xs" == "CONST PExprP (_pexpr_fset_nmember x xs)"

(* Some regression tests *)

term "`($x)\<acute> = $y\<acute>`"
term "`p[($x)\<acute>/y\<acute>]`"
term "`\<lparr>true\<rparr>`"

lemma "`$x \<in> {<1>,<2>,<3>,<4>,<5>} \<sqsubseteq> $x = <1>`"
  by (utp_pred_tac)

term "`\<lparr>$x \<inter> $y = {}\<rparr>`"

end

