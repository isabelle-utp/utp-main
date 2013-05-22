(******************************************************************************)
(* Project: VDM model for Isabelle/UTP                                        *)
(* File: utp_vdm_functions.thy                                                *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* VDM Function Library *}

theory utp_vdm_functions
imports utp_vdm_expr
begin

abbreviation "vexpr_defined   \<equiv> UOpD' \<D>"
abbreviation "vexpr_in_set    \<equiv> BOpD' (op \<in>\<^sub>f)"
abbreviation "vexpr_dom       \<equiv> UOpD' fdom"
abbreviation "vexpr_ran       \<equiv> UOpD' fran"
abbreviation "vexpr_card      \<equiv> UOpD' fcard"
abbreviation "vexpr_lookup    \<equiv> BOpD (\<lambda> (x, m). \<langle>m\<rangle>\<^sub>m x)"
abbreviation "vexpr_empty     \<equiv> LitD \<lbrace>\<rbrace>"
abbreviation "vexpr_insert    \<equiv> BOpD' finsert"
abbreviation "vexpr_le        \<equiv> BOpD' (op \<le>)"
abbreviation "vexpr_less      \<equiv> BOpD' (op <)"
abbreviation "vexpr_ge        \<equiv> BOpD' (\<lambda> x y. y \<le> x)"
abbreviation "vexpr_greater   \<equiv> BOpD' (\<lambda> x y. y < x)"
abbreviation "vexpr_true      \<equiv> LitD True"
abbreviation "vexpr_false     \<equiv> LitD False"
abbreviation "vexpr_not       \<equiv> UOpD' Not"
abbreviation "vexpr_and       \<equiv> BOpD' conj"
abbreviation "vexpr_or        \<equiv> BOpD' disj"
abbreviation "vexpr_implies   \<equiv> BOpD' implies"

text {* We remove the generic syntax for true and false in favour of our own *}

no_syntax
  "_uexpr_true"     :: "uexpr" ("true")
  "_uexpr_false"    :: "uexpr" ("false")

syntax
  "_vexpr_num"     :: "int \<Rightarrow> vexpr" ("_")
  "_vexpr_bot"     :: "vexpr" ("undefined")
  "_vexpr_defined" :: "vexpr \<Rightarrow> vexpr" ("defn _")
  "_vexpr_plus"    :: "vexpr \<Rightarrow> vexpr \<Rightarrow> vexpr" (infix "+" 30)
  "_vexpr_le"      :: "vexpr \<Rightarrow> vexpr \<Rightarrow> vexpr" (infix "<=" 50)
  "_vexpr_less"    :: "vexpr \<Rightarrow> vexpr \<Rightarrow> vexpr" (infix "<" 50)
  "_vexpr_ge"      :: "vexpr \<Rightarrow> vexpr \<Rightarrow> vexpr" (infix ">=" 50)
  "_vexpr_greater" :: "vexpr \<Rightarrow> vexpr \<Rightarrow> vexpr" (infix ">" 50)
  "_vexpr_in_set"  :: "vexpr \<Rightarrow> vexpr \<Rightarrow> vexpr" (infix "in set" 50)
  "_vexpr_union"   :: "vexpr \<Rightarrow> vexpr \<Rightarrow> vexpr" (infix "union" 65)
  "_vexpr_inter"   :: "vexpr \<Rightarrow> vexpr \<Rightarrow> vexpr" (infix "inter" 70)
  "_vexpr_card"    :: "vexpr \<Rightarrow> vexpr" ("card _")
  "_vexpr_empty"   :: "vexpr" ("{}")
  "_vexpr_fset"    :: "vexprs => vexpr"    ("{(_)}")
  "_vexpr_true"    :: "vexpr" ("true")
  "_vexpr_false"   :: "vexpr" ("false")
  "_vexpr_not"     :: "vexpr \<Rightarrow> vexpr" ("not _" [40] 40)
  "_vexpr_and"     :: "vexpr \<Rightarrow> vexpr \<Rightarrow> vexpr" (infix "and" 35)
  "_vexpr_or"      :: "vexpr \<Rightarrow> vexpr \<Rightarrow> vexpr" (infix "or" 30)
  "_vexpr_implies" :: "vexpr \<Rightarrow> vexpr \<Rightarrow> vexpr" (infix "=>" 25)

translations
  "_vexpr_in_set x xs" == "CONST vexpr_in_set x xs"
  "_vexpr_num x"       == "CONST LitD x"
  "_vexpr_bot"         == "CONST BotDE"
  "_vexpr_defined x"   == "CONST vexpr_defined x"
  "_vexpr_brack x"     => "x"
  "_vexpr_plus x y"    == "CONST BOpD' CONST plus x y"
  "_vexpr_le x y"      == "CONST vexpr_le x y"
  "_vexpr_less x y"    == "CONST vexpr_less x y"
  "_vexpr_ge x y"      == "CONST vexpr_ge x y"
  "_vexpr_greater x y" == "CONST vexpr_greater x y"
  "_vexpr_union x y"   == "CONST BOpD' CONST funion x y"
  "_vexpr_inter x y"   == "CONST BOpD' CONST finter x y"
  "_vexpr_card x"      == "CONST UOpD' CONST fcard x"
  "_vexpr_empty"       == "CONST vexpr_empty"
  "_vexpr_fset (_vexprs x xs)" == "CONST vexpr_insert x (_vexpr_fset xs)"
  "_vexpr_fset x"      == "CONST vexpr_insert x CONST vexpr_empty"
  "_vexpr_true"        == "CONST vexpr_true"
  "_vexpr_false"       == "CONST vexpr_false"
  "_vexpr_not x"       == "CONST vexpr_not x"
  "_vexpr_and x y"     == "CONST vexpr_and x y"
  "_vexpr_or x y"      == "CONST vexpr_or x y"
  "_vexpr_implies x y" == "CONST vexpr_implies x y"

lemma "^forall x :: int. x in set {<x>}^ = ^true^"
  by (utp_expr_tac)

lemma "^true => false^ = ^false^"
  by (utp_expr_tac)

term "`''x'' := {1,2,3,4,5,6,7} union {8,9}`"

lemma "^{2::int} union {3}^ = ^{2::int,3}^"
  by (utp_expr_tac)

lemma "^card {2}^ = ^1::nat^"
  by (utp_expr_tac)

lemma "^2 in set {2,2}^ = ^true^"
  by (utp_expr_tac)

lemma "^5::int <= 6::int^ = ^true^"
  by (utp_expr_tac)

end
