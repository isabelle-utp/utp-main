(******************************************************************************)
(* Project: VDM model for Isabelle/UTP                                        *)
(* File: utp_vdm_functions.thy                                                *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* VDM Function Library *}

theory utp_vdm_functions
imports 
  utp_vdm_types
  utp_vdm_expr
begin

abbreviation "vexpr_defined   \<equiv> (DefinedD :: 'a vdme \<Rightarrow> bool vdme)"
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
abbreviation "vexpr_prod      \<equiv> BOpD' (\<lambda> x y. (x,y))"

text {* We remove some of the generic syntax in favour of our own *}

no_syntax
  "_uexpr_true"     :: "uexpr" ("true")
  "_uexpr_false"    :: "uexpr" ("false")
  "_uexpr_var"      :: "pttrn \<Rightarrow> uexpr" ("_")
  "_uexpr_brack"    :: "uexpr \<Rightarrow> uexpr" ("'(_')")
  "_uexpr_evar"     :: "'a VAR \<Rightarrow> uexpr" ("$_" [999] 999)

syntax
(*  "_vexpr_num"     :: "num \<Rightarrow> vexpr" ("_") *)
  "_vexpr_quotev"  :: "string \<Rightarrow> vexpr" ("<_>")
  "_vexpr_quote"   :: "vexpr \<Rightarrow> 'a vdme" ("(1*_*)")
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
  "_vexpr_prod"    :: "vexprs \<Rightarrow> vexpr"    ("'(_')")

translations
  "_vexpr_quote x"     => "x"
  "_vexpr_quotev x"    == "CONST LitD (CONST Q x)"
  "_vexpr_in_set x xs" == "CONST vexpr_in_set x xs"
(*  "_vexpr_num x"       == "CONST LitD x" *)
  "_vexpr_bot"         == "CONST BotDE"
  "_vexpr_defined x"   == "CONST vexpr_defined x"
(*  "_vexpr_brack x"     => "x" *)
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
  "_vexpr_prod (_vexprs x xs)" == "CONST vexpr_prod x (_vexpr_prod xs)"
  "_vexpr_prod x" => "x"

lemma "^!2! : @nat inv x == (!x! < !5!)^ = ^!2 :: nat!^"
  apply (simp add:evale defined typing)
  apply (simp add:CoerceD_def defined evale typing InvS_def)
done


lemma "^{!1!} : @set of @nat^ = ^{!1 :: nat!}^"
  by (simp add:evale defined typing)

lemma "\<lbrakk> \<D> <x::int>; \<D> <y> \<rbrakk> \<Longrightarrow> ^!x! + !y!^ = ^!y! + !x!^"
  by (utp_expr_tac)

lemma "^defn defn ($''x'')^ = ^true^"
  by (utp_expr_tac)

lemma "^forall x :: int. !x! in set {!x!}^ = ^true^"
  by (utp_expr_tac)

lemma [evale]:"\<lbrakk>BOpD f BotDE y\<rbrakk>\<^sub>vb = None"
  by (simp add:BOpD_def evale)


lemma "^undefined in set {undefined}^ = ^undefined : @bool^"
  apply (utp_expr_tac)
oops

lemma "^true => false^ = ^false^"
  by (utp_expr_tac)

(* term "`''x'' := ({1,2,3,4,5,6,7} union {8,9})`" *)

(*
lemma "^{2::int} union {3}^ = ^{2::int,3}^"
  by (utp_expr_tac)

lemma "^card {2}^ = ^1::nat^"
  by (utp_expr_tac)

lemma "^2 in set {2,2}^ = ^true^"
  by (utp_expr_tac)

lemma "^5::int <= 6::int^ = ^true^"
  by (utp_expr_tac)
*)

end
