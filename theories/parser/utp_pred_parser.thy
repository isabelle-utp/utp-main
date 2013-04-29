theory utp_pred_parser
  imports
  "../core/utp_pred"
  "../core/utp_rel"
  "../core/utp_expr"
  "../tactics/utp_pred_tac"
  "../tactics/utp_expr_tac"
  "../tactics/utp_rel_tac"
begin

nonterminal upred and uexpr

(* Predicate Parser *)

syntax
  "_upred_top_clos" :: "upred \<Rightarrow> bool" ("(1[_])")
  "_upred_quote"    :: "upred \<Rightarrow> 'a WF_PREDICATE" ("(1`_`)")
  "_upred_brack"    :: "upred \<Rightarrow> upred" ("'(_')")
  "_upred_true"     :: "upred" ("true")
  "_upred_false"    :: "upred" ("false")
  "_upred_var"      :: "pttrn \<Rightarrow> upred" ("(_)")
  "_upred_evar"     :: "'a VAR \<Rightarrow> upred" ("$_")
  "_upred_and"      :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<and>" 35)
  "_upred_or"       :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<or>" 35)
  "_upred_imp"      :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<Rightarrow>" 25)
  "_upred_iff"      :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<Leftrightarrow>" 25)
  "_upred_ref"      :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<sqsubseteq>" 25)
  "_upred_clos"     :: "upred \<Rightarrow> upred" ("[_]")
  "_upred_not"      :: "upred \<Rightarrow> upred" ("\<not> _" [40] 40)
  "_upred_all1"     :: "pttrn \<Rightarrow> upred \<Rightarrow> upred"  ("(3\<forall> _./ _)" [0, 10] 10) 
  "_upred_exists1"  :: "pttrn \<Rightarrow> upred \<Rightarrow> upred"  ("(3\<exists> _./ _)" [0, 10] 10) 
  "_upred_equal"    :: "uexpr \<Rightarrow> uexpr \<Rightarrow> upred" (infixl "=" 50)
  "_upred_skip"     :: "upred" ("II")
  "_upred_seq"      :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr ";" 50)
  "_upred_cond"     :: "upred \<Rightarrow> upred \<Rightarrow> upred \<Rightarrow> upred" ("_ \<triangleleft> _ \<triangleright> _")
  "_upred_assigna"  :: "'a VAR \<Rightarrow> 'a VAR set \<Rightarrow> uexpr \<Rightarrow> upred" ("_ :=\<^bsub>_ \<^esub>_" [100] 100)
  "_upred_assign"   :: "'a VAR \<Rightarrow> uexpr \<Rightarrow> upred" ("_ := _" [100] 100)
  "_upred_assigns"  :: "string \<Rightarrow> uexpr \<Rightarrow> upred" ("_ := _" [100] 100)

abbreviation AssignS :: "string \<Rightarrow> 'VALUE WF_EXPRESSION \<Rightarrow> 'VALUE WF_PREDICATE" where
"AssignS x e \<equiv> AssignR (MkPlain x (expr_type e) False) e"

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
  "_upred_skip"        == "CONST SkipR"
  "_upred_seq p q"     => "CONST SemiR p q"
  "_upred_cond p q r"  == "CONST CondR p q r"
  "_upred_assign x e" == "CONST AssignR x e"
  "_upred_assigns x e" == "CONST AssignS x e"
  "_upred_assigna x xs e" == "CONST AssignRA x xs e"

(* Expression Parser *)

syntax
  "_uexpr_true"     :: "uexpr" ("true")
  "_uexpr_false"    :: "uexpr" ("false")
  "_uexpr_var"      :: "pttrn \<Rightarrow> uexpr" ("_")
  "_uexpr_evar"     :: "'a VAR \<Rightarrow> uexpr" ("$_")
  "_uexpr_substp"   :: "upred \<Rightarrow> uexpr \<Rightarrow> pttrn \<Rightarrow> upred" ("(_[_'/_])")

translations
  "_uexpr_true"         == "CONST TrueE"
  "_uexpr_false"        == "CONST FalseE"
  "_uexpr_var x"        => "x" 
  "_uexpr_evar x"       == "CONST VarE x"
(*  "_uexpr_substp p e x" == "CONST SubstPE p e x" *)


end


