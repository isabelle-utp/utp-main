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
  utp_parser_utils
begin

nonterminal 
  n_upred and n_upreds and 
  n_expr and n_exprs and
  n_pexpr and n_pexprs and
  n_pexprb and n_pexprbs and
  n_pvar and n_pvars

section {* Core Polymorphic Expression Syntax *}

syntax
  "_n_pexpr_quote"        :: "n_pexpr \<Rightarrow> ('a, 'm) pexpr" ("(1|_|)")
  "_n_pexprs"             :: "[n_pexpr, n_pexprs] => n_pexprs" ("_,/ _")
  ""                      :: "n_pexpr => n_pexprs" ("_")
  "_pvar"                 :: "idt \<Rightarrow> n_pvar" ("(_)")
  "_pvars"                :: "[n_pvar, n_pvars] => n_pvars" ("_,/ _")
  ""                      :: "n_pvar => n_pvars" ("_")
  "_passign"              :: "['a AssignF, n_pvars, n_pexprs] \<Rightarrow> 'a AssignF" ("(1[_])")
  "_n_pexpr_brack"        :: "n_pexpr \<Rightarrow> n_pexpr" ("'(_')")
  "_n_pexpr_pred_var"     :: "idt \<Rightarrow> n_pexpr" ("@(_)")
  "_n_pexpr_expr_var"     :: "idt \<Rightarrow> n_pexpr" ("(_)")
  "_n_pexpr_evar"         :: "('a, 'm) pvar \<Rightarrow> n_pexpr" ("$_" [999] 999)
  "_n_pexpr_subst"        :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> ('a, 'm) pvar \<Rightarrow> n_pexpr" ("(_[_'/_])" [999,999] 1000)
  "_n_pexpr_prime"        :: "n_pexpr \<Rightarrow> n_pexpr" ("_\<acute>" [1000] 1000)
  "_n_pexpr_erase"        :: "n_pexpr \<Rightarrow> n_pexpr" ("_\<down>" [1000] 1000)

translations
  "_n_pexpr_quote e"             => "e"
(*  "_n_pexpr_pred_quote e"        == "CONST PExprP e" *)
  "_n_pexpr_pred_var p"          == "CONST PredPE p"
  "_n_pexpr_expr_var v"          => "v"
  "_n_pexpr_evar x"              == "CONST PVarPE x"
  "_n_pexpr_brack e"             => "e"
  "_n_pexpr_subst e v x"         == "CONST PSubstPE e v x"
  "_n_pexpr_prime e"             == "CONST PermPE (CONST SS) e"
  "_n_pexpr_erase e"             == "CONST ErasePE e"
  "_passign m (_pvar x) v"     == "CONST PAssignF_upd m x v"
  "_passign m (_pvars x xs) (_n_pexprs v vs)" == "_passign (_passign m x v) xs vs"

section {* Predicate Parser *}

syntax
  "_n_upred_inf"      :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixl "|~|" 65)

syntax (xsymbols)
  "_n_upreds"         :: "[n_upred, n_upreds] => n_upreds" ("_,/ _")
  "_n_upreds_end"     :: "n_upred => n_upreds" ("_")
  "_n_upred_top_clos" :: "n_upred \<Rightarrow> bool" ("(1[_])")
  "_n_upred_quote"    :: "n_upred \<Rightarrow> 'a upred" ("(1`_`)")
  "_n_upred_brack"    :: "n_upred \<Rightarrow> n_upred" ("'(_')")
  "_n_upred_op1"      :: "idt \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_'(_')")
  "_n_upred_op2"      :: "idt \<Rightarrow> n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_'(_,_')")
  "_n_upred_op3"      :: "idt \<Rightarrow> n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_'(_,_,_')")
  "_n_upred_true"     :: "n_upred" ("true")
  "_n_upred_false"    :: "n_upred" ("false")
  "_n_upred_var"      :: "idt \<Rightarrow> n_upred" ("_")
  "_n_upred_evar"     :: "(bool, 'm) pvar \<Rightarrow> n_upred" ("$_" [999] 999)
  "_n_upred_and"      :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixr "\<and>" 35)
  "_n_upred_or"       :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixr "\<or>" 35)
  "_n_upred_imp"      :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixr "\<Rightarrow>" 25)
  "_n_upred_iff"      :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixr "\<Leftrightarrow>" 25)
  "_n_upred_ref"      :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixr "\<sqsubseteq>" 25)
  "_n_upred_clos"     :: "n_upred \<Rightarrow> n_upred" ("[_]")
  "_n_upred_not"      :: "n_upred \<Rightarrow> n_upred" ("\<not> _" [40] 40)
  "_n_upred_all1"     :: "('a, 'm) pvar \<Rightarrow> n_upred \<Rightarrow> n_upred"  ("(3\<forall> _./ _)" [0, 10] 10) 
  "_n_upred_exists1"  :: "('a, 'm) pvar \<Rightarrow> n_upred \<Rightarrow> n_upred"  ("(3\<exists> _./ _)" [0, 10] 10) 
  "_n_upred_all_sh"   :: "idt \<Rightarrow> n_upred \<Rightarrow> n_upred"  ("(4\<forall>\<^sub>s _./ _)" [0, 10] 10) 
  "_n_upred_exists_sh":: "idt \<Rightarrow> n_upred \<Rightarrow> n_upred"  ("(4\<exists>\<^sub>s _./ _)" [0, 10] 10) 
  "_n_upred_equal"    :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" (infixl "=" 50)
  "_n_upred_nequal"   :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" (infixl "\<noteq>" 50)
  "_n_upred_n_pexpr"    :: "n_pexpr \<Rightarrow> n_upred" ("\<lparr>_\<rparr>")
  "_n_upred_skip"     :: "n_upred" ("II")
  "_n_upred_skipa"    :: "'a uvar set \<Rightarrow> n_upred" ("II\<^bsub>_\<^esub>")
  "_n_upred_seq"      :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixr ";" 36)
  "_n_upred_cond"     :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" ("_ \<lhd> _ \<rhd> _")
  "_n_upred_ifthenelse" :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" ("if _ then _ else _")
  "_n_upred_assigna"  :: "('a, 'm) pvar \<Rightarrow> 'a uvar set \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("_ :=\<^bsub>_ \<^esub>_" [100] 100)
(*  "_n_upred_assign"   :: "('a, 'm) PVAR \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("_ := _" [100] 100) *)
  "_n_upred_assigns"  :: "n_pvars \<Rightarrow> n_pexprs \<Rightarrow> n_upred" ("_ := _" [100] 100)
  "_n_upred_conv"     :: "n_upred \<Rightarrow> n_upred" ("(_\<^sup>\<smile>)" [1000] 999)
  "_n_upred_prime"    :: "n_upred \<Rightarrow> n_upred" ("_\<acute>" [1000] 1000)
  "_n_upred_varopen"  :: "('a, 'm) pvar \<Rightarrow> n_upred" ("var _")
  "_n_upred_varclose" :: "('a, 'm) pvar \<Rightarrow> n_upred" ("end _")
  "_n_upred_varext"   :: "n_upred \<Rightarrow> ('a, 'm) pvar \<Rightarrow> n_upred" ("_\<^bsub>+_\<^esub>")
  "_n_upred_substp"   :: "n_upred \<Rightarrow> n_pexpr \<Rightarrow> ('a, 'm) pvar \<Rightarrow> n_upred" ("(_[_'/_])" [999,999] 1000)
  "_n_upred_perm"     :: "'m VAR_RENAME \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixr "\<bullet>" 80)

translations
  "_n_upred_brack p"     => "p"
  "_n_upred_op1 f x"     => "f x"
  "_n_upred_op2 f x y"   => "f x y"
  "_n_upred_op3 f x y z" => "f x y z" 
  "_n_upred_quote p"     => "p"
  "_n_upred_top_clos p"  == "CONST Tautology p"
  "_n_upred_true"        == "CONST TrueP"
  "_n_upred_false"       == "CONST FalseP"
  "_n_upred_var x"       => "x"
  "_n_upred_evar x"      == "CONST VarP x\<down>"
  "_n_upred_and p q"     == "CONST AndP p q"
  "_n_upred_or p q"      == "CONST OrP p q"
  "_n_upred_imp p q"     == "CONST ImpliesP p q"
  "_n_upred_ref p q"     == "CONST RefP p q"
  "_n_upred_iff p q"     == "CONST IffP p q"
  "_n_upred_clos p"      == "CONST ClosureP p"
  "_n_upred_not p"       == "CONST NotP p"
  "_n_upred_all1 x p"    == "CONST ForallP {x\<down>} p"
  "_n_upred_exists1 x p" == "CONST ExistsP {x\<down>} p"
  "_n_upred_all_sh x p"  == "\<forall>\<^sub>s x. p"
  "_n_upred_exists_sh x p"  == "\<exists>\<^sub>s x. p"
  "_n_upred_equal e f"   == "CONST PEqualP e f"
  "_n_upred_nequal e f"  == "CONST NotP (CONST PEqualP e f)"
  "_n_upred_n_pexpr e"     == "CONST PExprP e"
  "_n_upred_skip"        == "CONST SkipR"
  "_n_upred_skipa vs"    == "CONST SkipRA vs"
  "_n_upred_seq p q"     == "CONST SemiR p q"
  "_n_upred_cond p q r"  == "CONST CondR p q r"
  "_n_upred_ifthenelse b p q"  == "CONST CondR p b q"
(*  "_n_upred_assign x e"  == "CONST PAssignR x e" *)
  "_n_upred_assigns xs vs" == "CONST AssignsR (_passign (CONST IdA) xs vs)"
  "_n_upred_assigna x xs e" == "CONST AssignRA x\<down> xs e\<down>" 
  "_n_upred_conv x"      => "CONST ConvR x"
  "_n_upred_prime x"     == "CONST ConvR x"
  "_n_upred_varopen x"   == "CONST VarOpenP x\<down>"
  "_n_upred_varclose x"  == "CONST VarCloseP x\<down>"
  "_n_upred_varext p x"  == "CONST VarExtP p x\<down>"
  "_n_upred_substp p e x" == "CONST PSubstP p e x"
  "_n_upred_perm ss p"   == "CONST PermP ss p"

term "`p[x/v]`"
term "`p[$x/y]`"
term "`x \<Rightarrow> $y\<acute>`"
term "`SS\<bullet>p`"

term "`p\<^bsub>+x\<^esub>`"

section {* Core Expression Parser *}

syntax
  "_n_exprs"             :: "[n_expr, n_exprs] => n_exprs" ("_,/ _")
  ""                    :: "n_expr => n_exprs" ("_")
  "_n_expr_brack"        :: "n_expr \<Rightarrow> n_expr" ("'(_')")
  "_n_expr_quote"        :: "n_expr \<Rightarrow> 'a uexpr" ("(1^_^)")
  "_n_expr_true"         :: "n_expr" ("true")
  "_n_expr_false"        :: "n_expr" ("false")
  "_n_expr_var"          :: "idt \<Rightarrow> n_expr" ("_")
  "_n_expr_evar"         :: "'a uvar \<Rightarrow> n_expr" ("$_" [999] 999)
  "_n_expr_prime"        :: "n_expr \<Rightarrow> n_expr" ("_\<acute>" [1000] 1000)

translations
  "_n_expr_brack e"      => "e"
  "_n_expr_quote e"      => "e"
  "_n_expr_true"         == "CONST TrueE"
  "_n_expr_false"        == "CONST FalseE"
  "_n_expr_var x"        => "x" 
  "_n_expr_evar x"       == "CONST VarE x"
  "_n_expr_prime e"      == "CONST RenameE e (CONST SS)"


syntax
  (* Basic logical operators *)
  "_n_pexpr_equal"        :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "=" 50)
  "_n_pexpr_wequal"       :: "n_expr \<Rightarrow> n_expr \<Rightarrow> n_pexpr" (infixl "\<equiv>" 50)
  "_n_pexpr_true"         :: "n_pexpr" ("true")
  "_n_pexpr_false"        :: "n_pexpr" ("false")
  "_n_pexpr_and"          :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "\<and>" 35)
  "_n_pexpr_or"           :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "\<or>" 35)
  "_n_pexpr_imp"          :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "\<Rightarrow>" 25)
  "_n_pexpr_iff"          :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "\<Leftrightarrow>" 25)
  "_n_pexpr_ref"          :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "\<sqsubseteq>" 25)
  "_n_pexpr_clos"         :: "n_pexpr \<Rightarrow> n_pexpr" ("[_]")
  "_n_pexpr_not"          :: "n_pexpr \<Rightarrow> n_pexpr" ("\<not> _" [40] 40)
  "_n_pexpr_all1"         :: "('a, 'm) pvar \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr"  ("(3\<forall> _./ _)" [0, 10] 10) 
  "_n_pexpr_exists1"      :: "('a, 'm) pvar \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr"  ("(3\<exists> _./ _)" [0, 10] 10) 
  "_n_pexpr_op1"          :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("_'(_')")
  "_n_pexpr_op2"          :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("_'(_,_')")
  "_n_pexpr_op3"          :: "idt \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("_'(_,_,_')")

syntax
  (* Relational operators *)

(*  "_n_pexpr_skip"         :: "n_pexpr" ("II") *)
(*  "_n_pexpr_skipa"        :: "'VALUE VAR set \<Rightarrow> n_pexpr" ("II\<^bsub>_\<^esub>") *)
(*  "_n_pexpr_seq"          :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr ";" 36) *)
  "_n_pexpr_cond"         :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("_ \<lhd> _ \<rhd> _")
  "_n_pexpr_assign"       :: "('a, 'm) pvar \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("_ := _" [100] 100)
  "_n_pexpr_wassign"      :: "'m uvar \<Rightarrow> n_expr \<Rightarrow> n_pexpr" ("_ :\<equiv> _" [100] 100)
  "_n_pexpr_conv"         :: "n_pexpr \<Rightarrow> n_pexpr" ("(_\<^sup>\<smile>)" [1000] 999)
  "_n_pexpr_varopen"      :: "('a, 'm) pvar \<Rightarrow> n_pexpr" ("var _")
  "_n_pexpr_varclose"     :: "('a, 'm) pvar \<Rightarrow> n_pexpr" ("end _")

syntax
  (* Data Structures *)
  "_n_pexpr_lit"           :: "'a \<Rightarrow> n_pexpr" ("\<guillemotleft>_\<guillemotright>")
  "_n_pexpr_int"           :: "int \<Rightarrow> n_pexpr" ("<_>")
  "_n_pexpr_num_0"         :: "n_pexpr" ("0")
  "_n_pexpr_num_1"         :: "n_pexpr" ("1")
  "_n_pexpr_num"           :: "num_const \<Rightarrow> n_pexpr" ("_")
  "_n_pexpr_float"         :: "float_const \<Rightarrow> n_pexpr" ("_")
  "_n_pexpr_string"        :: "str_position \<Rightarrow> n_pexpr" ("_")
  "_n_pexpr_plus"          :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "+" 65)
  "_n_pexpr_mult"          :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "*" 70)
  "_n_pexpr_div"           :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "'/" 70)
  "_n_pexpr_minus"         :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "-" 65)
  "_n_pexpr_less"          :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "<" 25)
  "_n_pexpr_less_eq"       :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "\<le>" 25)
  "_n_pexpr_greater"       :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr ">" 25)
  "_n_pexpr_greater_eq"    :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "\<ge>" 25)
  "_n_pexpr_max"           :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("max'(_, _')")
  "_n_pexpr_min"           :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("min'(_, _')")
  "_n_pexpr_list"          :: "n_pexprs \<Rightarrow> n_pexpr" ("\<langle>_\<rangle>")
  "_n_pexpr_list_nil"      :: "n_pexpr" ("\<langle>\<rangle>")
  "_n_pexpr_list_append"   :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "^" 65)
  "_n_pexpr_set"           :: "n_pexprs \<Rightarrow> n_pexpr" ("{_}")
  "_n_pexpr_set_empty"     :: "n_pexpr" ("{}")
  "_n_pexpr_set_union"     :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "\<union>" 65)
  "_n_pexpr_set_inter"     :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "\<inter>" 70)
  "_n_pexpr_set_member"    :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("(_/ \<in> _)" [51, 51] 50)
  "_n_pexpr_set_nmember"   :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("(_/ \<notin> _)" [51, 51] 50)
  "_n_pexpr_set_subset"    :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "\<subset>" 50)
  "_n_pexpr_set_subseteq"  :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "\<subseteq>" 50)
  "_n_pexpr_set_list"      :: "n_pexpr \<Rightarrow> n_pexpr" ("elems _")
  "_n_pexpr_intersync"     :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "\<parallel>\<^bsub>_\<^esub>" 75)
  "_n_pexpr_restrict"      :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "\<upharpoonright>" 70)
  "_n_pexpr_event"         :: "uname \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("_.'(_')" 50)
(* Modified by Frank Zeyda to avoid a clash with the channel type. *)
  "_n_pexpr_event_chan"    :: "n_pexpr \<Rightarrow> n_pexpr" ("echan _")

translations
  (* Basic logical operators *)
  "_n_pexpr_equal e f"           == "CONST EqualPE e f"
  "_n_pexpr_wequal e f"          == "CONST PredPE (CONST EqualP e f)"
  "_n_pexpr_true"                == "CONST TruePE"
  "_n_pexpr_false"               == "CONST FalsePE"
  "_n_pexpr_and p q"             == "CONST AndPE p q"
  "_n_pexpr_or p q"              == "CONST OrPE p q"
  "_n_pexpr_imp p q"             == "CONST ImpliesPE p q"
  "_n_pexpr_iff p q"             == "CONST IffPE p q"
  "_n_pexpr_ref p q"             == "CONST RefPE p q"
  "_n_pexpr_clos p"              == "CONST ClosurePE p"
  "_n_pexpr_not p"               == "CONST NotPE p"
  "_n_pexpr_all1 x p"            == "CONST ForallPE {x\<down>} p"
  "_n_pexpr_exists1 x p"         == "CONST ExistsPE {x\<down>} p"
  "_n_pexpr_op1 f x"             == "CONST Op1PE f x"
  "_n_pexpr_op2 f x y"           == "CONST Op2PE f x y"
  "_n_pexpr_op3 f x y z"         == "CONST Op3PE f x y z"

translations
  (* Relational operators *)
(*  "_n_pexpr_skip"                == "CONST PredPE (CONST SkipR)" *)
(*  "_n_pexpr_skipa vs"            == "CONST PredPE (CONST SkipRA vs)" *)
(*  "_n_pexpr_seq p q"             == "CONST PredOp2PE (CONST SemiR) p q" *)
  "_n_pexpr_cond p q r"          == "CONST PredOp3PE (CONST CondR) p q r"
  "_n_pexpr_assign x v"          == "CONST AssignRPE x v"
  "_n_pexpr_wassign x v"         == "CONST WAssignRPE x v"
  "_n_pexpr_conv p"              == "CONST PredOp1PE (CONST ConvR) p"
  "_n_pexpr_varopen x"           == "CONST PredPE (CONST VarOpenP x\<down>)"
  "_n_pexpr_varclose x"          == "CONST PredPE (CONST VarCloseP x\<down>)"

translations
  (* Data Structures *)
  "_n_pexpr_lit x"               == "CONST LitPE x"
  "_n_pexpr_int x"               == "CONST IntPE x"
  "_n_pexpr_num_0"               == "CONST LitPE 0"
  "_n_pexpr_num_1"               == "CONST LitPE 1"
  "_n_pexpr_num n"               == "CONST LitPE (_Numeral n)"
  "_n_pexpr_float n"             == "CONST LitPE (_Float n)"
  "_n_pexpr_plus x y"            == "CONST PlusPE x y"
  "_n_pexpr_mult x y"            == "CONST MultPE x y"
  "_n_pexpr_div x y"             == "CONST DivPE x y"
  "_n_pexpr_minus x y"           == "CONST MinusPE x y"
  "_n_pexpr_less x y"            == "CONST LessPE x y"
  "_n_pexpr_less_eq x y"         == "CONST LessEqPE x y"
  "_n_pexpr_greater x y"         == "CONST LessPE y x"
  "_n_pexpr_greater_eq x y"      == "CONST LessEqPE y x"
  "_n_pexpr_max x y"             == "CONST MaxPE x y"
  "_n_pexpr_min x y"             == "CONST MinPE x y"
  "_n_pexpr_list_nil"            == "CONST NilPE"
  "_n_pexpr_list_append e f"     == "CONST ConcatPE e f"
  "_n_pexpr_list (_n_pexprs x xs)" == "CONST ConsPE x (_n_pexpr_list xs)"
  "_n_pexpr_list x"              == "CONST ConsPE x (CONST NilPE)"
  "_n_pexpr_set (_n_pexprs x xs)"  == "CONST InsertPE x (_n_pexpr_set xs)"
  "_n_pexpr_set x"               == "CONST InsertPE x CONST EmptyPE"
  "_n_pexpr_set_empty"           == "CONST EmptyPE"
  "_n_pexpr_set_union xs ys"     == "CONST UnionPE xs ys"
  "_n_pexpr_set_inter xs ys"     == "CONST InterPE xs ys"
  "_n_pexpr_set_member x xs"     == "CONST MemberPE x xs"
  "_n_pexpr_set_subset xs ys"    == "CONST SubsetPE xs ys"
  "_n_pexpr_set_subseteq xs ys"  == "CONST SubseteqPE xs ys"
  "_n_pexpr_set_nmember x xs"    == "CONST NotMemberPE x xs"
  "_n_pexpr_set_list xs"         == "CONST SetPE xs"
  "_n_pexpr_intersync p xs q"    == "CONST IntersyncPE xs p q"
  "_n_pexpr_restrict xs A"       == "CONST RestrictPE xs A"
  "_n_pexpr_event n v"           == "CONST EventPE n v"
  "_n_pexpr_event_chan e"        == "CONST ChannelPE e"

(* Strings are not available via a translation function, so we spin our own : *)

parse_ast_translation {*
let fun pexpr_string_tr [str] =
  Ast.Appl [Ast.Constant @{const_syntax LitPE}, Utp_Parser_Utils.string_ast_tr [str]]
  | pexpr_string_tr _ = raise Match;
  in
  [(@{syntax_const "_n_pexpr_string"}, K pexpr_string_tr)]
end
*}

(* Linking the predicate parser to the poly parser *)

default_sort type

syntax
  "_n_upred_lesseq"        :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" (infixr "\<le>" 25)
  "_n_upred_less"          :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" (infixr "<" 25)
  "_n_upred_greater_eq"    :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" (infixr "\<ge>" 25)
  "_n_upred_greater"       :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" (infixr ">" 25)
  "_n_upred_set_member"    :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("(_/ \<in> _)" [51, 51] 50)
  "_n_upred_set_nmember"   :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("(_/ \<notin> _)" [51, 51] 50)
  "_n_upred_set_subset"    :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" (infixr "\<subset>" 50)
  "_n_upred_set_subseteq"  :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_upred" (infixr "\<subseteq>" 50)
  "_n_upred_index"         :: "('b \<Rightarrow> 'a upred) \<Rightarrow> 'b \<Rightarrow> n_upred" ("_<_>" 50)

translations
  "_n_upred_lesseq e f"         => "CONST PExprP (_n_pexpr_less_eq e f)"
  "_n_upred_less e f"           => "CONST PExprP (_n_pexpr_less e f)"
  "_n_upred_greater_eq e f"     => "CONST PExprP (_n_pexpr_greater_eq e f)"
  "_n_upred_greater e f"        => "CONST PExprP (_n_pexpr_greater e f)"
  "_n_upred_set_member x xs"    => "CONST PExprP (_n_pexpr_set_member x xs)"
  "_n_upred_set_nmember x xs"   => "CONST PExprP (_n_pexpr_set_nmember x xs)"
  "_n_upred_set_subset xs ys"   => "CONST PExprP (_n_pexpr_set_subset xs ys)"
  "_n_upred_set_subseteq xs ys" => "CONST PExprP (_n_pexpr_set_subseteq xs ys)"
  "_n_upred_index f i"          => "f i"

(* Big operators *)

syntax
  "_n_upred_ANDI1" :: "pttrns \<Rightarrow> n_upred \<Rightarrow> n_upred" ("(3\<And> _./ _)" [0, 10] 10)
  "_n_upred_ANDI"  :: "pttrn \<Rightarrow> 'b set \<Rightarrow> n_upred \<Rightarrow> n_upred"  ("(3\<And> _:_./ _)" [0, 0, 10] 10)
  "_n_upred_ORDI1" :: "pttrns \<Rightarrow> n_upred \<Rightarrow> n_upred" ("(3\<Or> _./ _)" [0, 10] 10)
  "_n_upred_ORDI"  :: "pttrn \<Rightarrow> 'b set \<Rightarrow> n_upred \<Rightarrow> n_upred"  ("(3\<Or> _:_./ _)" [0, 0, 10] 10)

translations
  "_n_upred_ANDI1 x y B" == "AND x. AND y. B"
  "_n_upred_ANDI1 x B"   == "CONST ANDI CONST UNIV (%x. B)"
  "_n_upred_ANDI x A B"  == "CONST ANDI A (%x. B)"
  "_n_upred_ORDI1 x y B" == "OR x. OR y. B"
  "_n_upred_ORDI1 x B"   == "CONST ORDI CONST UNIV (%x. B)"
  "_n_upred_ORDI x A B"  == "CONST ORDI A (%x. B)"

default_sort BASE_MODEL

(* Some regression tests *)

term "`(P \<and> Q) \<Rightarrow> P`"

term "`(P \<lhd> b \<rhd> Q) \<sqsubseteq> (b \<and> P)`"

term "`$x \<in> {\<guillemotleft>1\<guillemotright>,\<guillemotleft>2\<guillemotright>,\<guillemotleft>3\<guillemotright>} \<sqsubseteq> $x = \<guillemotleft>2\<guillemotright>`"

term "`x,y,z := \<guillemotleft>1::int\<guillemotright>,false,{}`"

term "`x := (7 * $z) ; ((y := $x + 1) \<lhd> ($x < 10) \<rhd> P)`"

term "`var x; x := \<guillemotleft>5::int\<guillemotright>; end x`"

term "`$x\<acute> = $y\<acute>`"
term "`p[$x\<acute>/y\<acute>]`"
term "`\<lparr>true\<rparr>`"

lemma "`$x \<in> {<1>,\<guillemotleft>2\<guillemotright>,<3>,<4>,<5>} \<sqsubseteq> $x = <1>`"
  by (utp_poly_tac)

lemma "`{} \<subseteq> {<1>}`"
  by (utp_poly_tac)

lemma "`({<1>,<2>} - {<1>}) \<subseteq> {<2>}`"
  by (utp_poly_tac)
  
lemma "`<1> \<in> elems \<langle><4>,<7>,<1>,<9>\<rangle>`"
  by (utp_poly_tac)

(* term "|$x\<^bsub>0\<^esub>|" *)

lemma "|\<langle><1>,<2>,<3>\<rangle> \<upharpoonright> {\<guillemotleft>2\<guillemotright>}| = |\<langle><1>,<3>\<rangle>|"
  by (auto simp add:evalp typing defined)

term "`\<Or> i:I. P`"

term "`if \<lparr>$x \<ge> $y\<rparr> then z := $x else z := $y`"

term "`x := ''hello''`"

end
