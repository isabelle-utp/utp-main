(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_op_parser.thy                                                    *)
(* Author: Frank Zeyda and Simon Foster, University of York (UK)              *)
(******************************************************************************)

header {* Simple Operation Parser *}

theory utp_op_parser
  imports utp_pred_parser
begin

text {* Theorem Attribute *}

ML {*
  structure uop_defs =
    Named_Thms (val name = @{binding uop_defs} val description = "UTP operation defs")
*}

setup uop_defs.setup

text {* Operations / Procedures are implemented through functional abstraction *}

type_synonym ('a, 'm) WF_OPERATION = "(('a, 'm) pvar * bool) \<Rightarrow> 'm upred"
type_synonym ('a, 'b, 'm) WF_POPERATION = "('a, 'm) pexpr \<Rightarrow> ('b, 'm) WF_OPERATION"

nonterminal n_uproc

definition "TrueO           = (\<lambda> r. TrueP)"
definition "FalseO          = (\<lambda> r. FalseP)"
definition "NotO p          = (\<lambda> r. NotP (p r))"
definition "AndO p q        = (\<lambda> r. AndP (p r) (q r))"
definition "OrO p q         = (\<lambda> r. OrP (p r) (q r))"
definition "ImpliesO p q    = (\<lambda> r. ImpliesP (p r) (q r))"
definition "IffO p q        = (\<lambda> r. IffP (p r) (q r))"
definition "ExprO e         = (\<lambda> r. PExprP e)"
definition "SkipO           = (\<lambda> r. SkipR)"
definition "PAssignO x e    = (\<lambda> r. PAssignR x e)"
definition "SemiO p q       = (\<lambda> r. p r ;\<^sub>R q r)"
definition "CondO p c q     = (\<lambda> r. CondR (p r) c (q r))"
definition "ReturnO e       = (\<lambda> r. if (snd r) then PAssignR (fst r) e else SkipR)"
definition "AssignRO x f v  = f v (x, True)"
definition "CallRO f v      = f v (undefined, False)"

declare TrueO_def [eval, evalpp, evalr, evalpr, uop_defs]
declare FalseO_def [eval, evalpp, evalr, evalpr, uop_defs]
declare NotO_def [eval, evalpp, evalr, evalpr, uop_defs]
declare AndO_def [eval, evalpp, evalr, evalpr, uop_defs]
declare OrO_def [eval, evalpp, evalr, evalpr, uop_defs]
declare ImpliesO_def [eval, evalpp, evalr, evalpr, uop_defs]
declare IffO_def [eval, evalpp, evalr, evalpr, uop_defs]
declare ExprO_def [eval, evalpp, evalr, evalpr, uop_defs]
declare SkipO_def [eval, evalpp, evalr, evalpr, uop_defs]
declare PAssignO_def [eval, evalpp, evalr, evalpr, uop_defs]
declare SemiO_def [eval, evalpp, evalr, evalpr, uop_defs]
declare CondO_def [eval, evalpp, evalr, evalpr, uop_defs]
declare ReturnO_def [eval, evalpp, evalr, evalpr, uop_defs]
declare AssignRO_def [eval, evalpp, evalr, evalpr, uop_defs]
declare CallRO_def [eval, evalpp, evalr, evalpr, uop_defs]

syntax
  "_n_uproc_var"        :: "pttrn \<Rightarrow> n_uproc" ("(_)")
  "_n_uproc_true"       :: "n_uproc" ("true")
  "_n_uproc_false"      :: "n_uproc" ("false")
  "_n_uproc_not"        :: "n_uproc \<Rightarrow> n_uproc" ("\<not> _" [40] 40)
  "_n_uproc_and"        :: "n_uproc \<Rightarrow> n_uproc \<Rightarrow> n_uproc" (infixr "\<and>" 35)
  "_n_uproc_or"         :: "n_uproc \<Rightarrow> n_uproc \<Rightarrow> n_uproc" (infixr "\<or>" 35)
  "_n_uproc_imp"        :: "n_uproc \<Rightarrow> n_uproc \<Rightarrow> n_uproc" (infixr "\<Rightarrow>" 25)
  "_n_uproc_iff"        :: "n_uproc \<Rightarrow> n_uproc \<Rightarrow> n_uproc" (infixr "\<Leftrightarrow>" 25)
  "_n_uproc_pexpr"      :: "n_pexpr \<Rightarrow> n_uproc" ("\<lparr>_\<rparr>")
  "_n_uproc_quote"      :: "n_uproc \<Rightarrow> ('a, 'm) WF_OPERATION" ("{:_:}")
  "_n_uproc_brack"      :: "n_uproc \<Rightarrow> n_uproc" ("'(_')")
  "_n_uproc_skip"       :: "n_uproc" ("II")
  "_n_uproc_assign"     :: "('a, 'm) pvar \<Rightarrow> n_pexpr \<Rightarrow> n_uproc" ("_ := _" [100] 100)
  "_n_uproc_seq"        :: "n_uproc \<Rightarrow> n_uproc \<Rightarrow> n_uproc" (infixr ";" 36)
  "_n_uproc_ifthenelse" :: "n_upred \<Rightarrow> n_uproc \<Rightarrow> n_uproc \<Rightarrow> n_uproc" ("if _ then _ else _")
  "_n_uproc_cond"       :: "n_uproc \<Rightarrow> n_upred \<Rightarrow> n_uproc \<Rightarrow> n_uproc" ("_ \<lhd> _ \<rhd> _")
  "_n_uproc_return"     :: "n_pexpr \<Rightarrow> n_uproc" ("return _")
  "_upred_assignpr"   :: "('a, 'm) pvar \<Rightarrow> ('a, 'b, 'm) WF_POPERATION \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("_ := _'[_']" [100] 100)
  "_upred_callpr"     :: "('a, 'b, 'm) WF_POPERATION \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("call _'[_']")

translations
  "_n_uproc_var p"            => "p"
  "_n_uproc_true"             == "CONST TrueO"
  "_n_uproc_false"            == "CONST FalseO"
  "_n_uproc_not p"            == "CONST NotO p"
  "_n_uproc_and p q"          == "CONST AndO p q"
  "_n_uproc_or p q"           == "CONST OrO p q"
  "_n_uproc_imp p q"          == "CONST ImpliesO p q"
  "_n_uproc_iff p q"          == "CONST IffO p q"
  "_n_uproc_pexpr e"          == "CONST ExprO e"
  "_n_uproc_quote x"          => "x"
  "_n_uproc_brack x"          => "x"
  "_n_uproc_skip"             == "CONST SkipO"
  "_n_uproc_assign x e"       == "CONST PAssignO x e"
  "_n_uproc_seq p q"          == "CONST SemiO p q"
  "_n_uproc_cond p c q"       == "CONST CondO p c q"
  "_n_uproc_ifthenelse c p q" == "CONST CondO p c q"
  "_n_uproc_return e"         == "CONST ReturnO e"
  "_upred_assignpr x f v"   == "CONST AssignRO x f v"
  "_upred_callpr f v"       == "CONST CallRO f v"

term "{: p \<Rightarrow> q ; true :}"

definition utp_test_op1 :: "(int, int, 'm :: INT_SORT) WF_POPERATION" where
"utp_test_op1(x) = {: if (x > \<guillemotleft>1::int\<guillemotright>) then return x else return \<guillemotleft>10\<guillemotright> :}"

declare utp_test_op1_def [evalpp, evalpr]

term "`call utp_test_op1[$x]`"
term "`x := utp_test_op1[\<guillemotleft>5\<guillemotright> + $y]`"
term "`x := \<guillemotleft>5\<guillemotright>`"

text {* Some quick tests *}

lemma "\<lbrakk> x \<in> PUNDASHED \<rbrakk> \<Longrightarrow> `x := utp_test_op1[\<guillemotleft>1\<guillemotright>]` = `x := \<guillemotleft>10\<guillemotright>`"
  by (utp_prel_auto_tac)

end