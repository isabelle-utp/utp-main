(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_op_parser.thy                                                    *)
(* Author: Frank Zeyda and Simon Foster, University of York (UK)              *)
(******************************************************************************)

header {* Simple Operation Parser *}

theory utp_op_parser
  imports utp_pred_parser
begin

type_synonym ('a, 'm) WF_OPERATION = "(('a, 'm) PVAR * bool) \<Rightarrow> 'm WF_PREDICATE"
type_synonym ('a, 'b, 'm) WF_POPERATION = "('a, 'm) WF_PEXPRESSION \<Rightarrow> ('b, 'm) WF_OPERATION"
  
nonterminal uproc

definition "SkipO           = (\<lambda> r. SkipR)"
definition "PAssignO x e    = (\<lambda> r. PAssignR x e)"
definition "SemiO p q       = (\<lambda> r. p r ; q r)"
definition "CondO p c q     = (\<lambda> r. CondR (p r) c (q r))"
definition "ReturnO e       = (\<lambda> r. if (snd r) then PAssignR (fst r) e else SkipR)"
definition "AssignRO x f v  = f v (x, True)"
definition "CallRO f v      = f v (undefined, False)"

syntax
  "_uproc_quote"      :: "uproc \<Rightarrow> ('a, 'm) WF_OPERATION" ("UTPOP'(_')")
  "_uproc_brack"      :: "uproc \<Rightarrow> uproc" ("'(_')")
  "_uproc_skip"       :: "uproc" ("II")
  "_uproc_assign"     :: "('a, 'm) PVAR \<Rightarrow> pexpr \<Rightarrow> uproc" ("_ := _" [100] 100)
  "_uproc_seq"        :: "uproc \<Rightarrow> uproc \<Rightarrow> uproc" (infixr ";" 36)
  "_uproc_ifthenelse" :: "upred \<Rightarrow> uproc \<Rightarrow> uproc \<Rightarrow> uproc" ("if _ then _ else _")
  "_uproc_cond"       :: "uproc \<Rightarrow> upred \<Rightarrow> uproc \<Rightarrow> uproc" ("_ \<lhd> _ \<rhd> _")
  "_uproc_return"     :: "pexpr \<Rightarrow> uproc" ("return _")
  "_upred_assignpr"   :: "('a, 'm) PVAR \<Rightarrow> ('a, 'b, 'm) WF_POPERATION \<Rightarrow> pexpr \<Rightarrow> upred" ("_ := _'[_']" [100] 100)
  "_upred_callpr"     :: "('a, 'b, 'm) WF_POPERATION \<Rightarrow> pexpr \<Rightarrow> upred" ("call _'[_']")

translations
  "_uproc_quote x"          => "x"
  "_uproc_brack x"          => "x"
  "_uproc_skip"             == "CONST SkipO"
  "_uproc_assign x e"       == "CONST PAssignO x e"
  "_uproc_seq p q"          == "CONST SemiO p q"
  "_uproc_cond p c q"       == "CONST CondO p c q"
  "_uproc_ifthenelse c p q" == "CONST CondO p c q"
  "_uproc_return e"         == "CONST ReturnO e"
  "_upred_assignpr x f v"   == "CONST AssignRO x f v"
  "_upred_callpr f v"       == "CONST CallRO f v"

definition "utp_test_op1(x) \<equiv> UTPOP(if (x > \<guillemotleft>1::int\<guillemotright>) then return x else return \<guillemotleft>10\<guillemotright>)"

term "`call utp_test_op1[$x]`"
term "`x := utp_test_op1[\<guillemotleft>5\<guillemotright> + $y]`"
term "`x := \<guillemotleft>5\<guillemotright>`"

end