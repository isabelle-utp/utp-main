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
abbreviation "vexpr_in_set    \<equiv> Op2D' (op \<in>\<^sub>f)"
abbreviation "vexpr_dom       \<equiv> Op1D' fdom"
abbreviation "vexpr_rng       \<equiv> Op1D' fran"
abbreviation "vexpr_card      \<equiv> Op1D' fcard"
abbreviation "vexpr_lookup    \<equiv> Op2D (\<lambda> (x, m). \<langle>m\<rangle>\<^sub>m x)"
abbreviation "vexpr_le        \<equiv> Op2D' (op \<le>)"
abbreviation "vexpr_less      \<equiv> Op2D' (op <)"
abbreviation "vexpr_ge        \<equiv> Op2D' (\<lambda> x y. y \<le> x)"
abbreviation "vexpr_greater   \<equiv> Op2D' (\<lambda> x y. y < x)"
abbreviation "vexpr_not       \<equiv> Op1D' Not"
abbreviation "vexpr_and       \<equiv> Op2D' conj"
abbreviation "vexpr_or        \<equiv> Op2D' disj"
abbreviation "vexpr_implies   \<equiv> Op2D' implies"
abbreviation "vexpr_hd        \<equiv> Op1D' hd"
abbreviation "vexpr_tl        \<equiv> Op1D' tl"

definition ForallSetD :: "'a fset vdme \<Rightarrow> ('a \<Rightarrow> bool vdme) \<Rightarrow> bool vdme" where
"ForallSetD xs p = ForallD (\<lambda> x. vexpr_implies (vexpr_in_set (LitD x) xs) (p x))"

syntax
(*  "_vexpr_num"     :: "num \<Rightarrow> pexpr" ("_") *)
  "_vexpr_quotev"  :: "string \<Rightarrow> pexpr" ("<_>")
  "_vexpr_defined" :: "pexpr \<Rightarrow> pexpr" ("defn _")
  "_vexpr_plus"    :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix "+" 30)
  "_vexpr_le"      :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix "<=" 50)
  "_vexpr_less"    :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix "<" 50)
  "_vexpr_ge"      :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix ">=" 50)
  "_vexpr_greater" :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix ">" 50)
  "_vexpr_in_set"  :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix "in @set" 50)
  "_vexpr_union"   :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix "union" 65)
  "_vexpr_inter"   :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix "inter" 70)
  "_vexpr_card"    :: "pexpr \<Rightarrow> pexpr" ("card _")
  "_vexpr_dom"     :: "pexpr \<Rightarrow> pexpr" ("dom _")
  "_vexpr_rng"     :: "pexpr \<Rightarrow> pexpr" ("rng _")
  "_vexpr_not"     :: "pexpr \<Rightarrow> pexpr" ("not _" [40] 40)
  "_vexpr_and"     :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix "and" 35)
  "_vexpr_or"      :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix "or" 30)
  "_vexpr_implies" :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix "=>" 25)
  "_vexpr_hd"      :: "pexpr \<Rightarrow> pexpr" ("hd _")
  "_vexpr_tl"      :: "pexpr \<Rightarrow> pexpr" ("tl _")
  "_vexpr_all_set" :: "pttrn \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" ("(3forall _ in @set _ &/ _)" [0, 0, 10] 10)

translations
  "_vexpr_quotev x"    == "CONST LitD (CONST Q x)"
  "_vexpr_in_set x xs" == "CONST vexpr_in_set x xs"
(*  "_vexpr_num x"       == "CONST LitD x" *)
  "_vexpr_defined x"   == "CONST vexpr_defined x"
(*  "_vexpr_brack x"     => "x" *)
  "_vexpr_plus x y"    == "CONST Op2D' CONST plus x y"
  "_vexpr_le x y"      == "CONST vexpr_le x y"
  "_vexpr_less x y"    == "CONST vexpr_less x y"
  "_vexpr_ge x y"      == "CONST vexpr_ge x y"
  "_vexpr_greater x y" == "CONST vexpr_greater x y"
  "_vexpr_union x y"   == "CONST Op2D' CONST funion x y"
  "_vexpr_inter x y"   == "CONST Op2D' CONST finter x y"
  "_vexpr_card x"      == "CONST Op2D' CONST fcard x"
  "_vexpr_dom x"       == "CONST vexpr_dom x"
  "_vexpr_rng x"       == "CONST vexpr_rng x"
  "_vexpr_not x"       == "CONST vexpr_not x"
  "_vexpr_and x y"     == "CONST vexpr_and x y"
  "_vexpr_or x y"      == "CONST vexpr_or x y"
  "_vexpr_implies x y" == "CONST vexpr_implies x y"
  "_vexpr_hd xs"       == "CONST vexpr_hd xs"
  "_vexpr_tl xs"       == "CONST vexpr_tl xs"
  "_vexpr_all_set x xs p" == "CONST ForallSetD xs (\<lambda>x. p)"

thm ForallSetD_def

term "\<parallel>$x in @set {<1>}\<parallel>"

term "\<parallel>forall x in @set {<1>} & (<x> > <5>)\<parallel>"



(* term "|\<langle>x\<rangle> > \<langle>5 :: int\<rangle>|" *)
term "\<parallel>@int inv x == \<langle>x\<rangle> > \<langle>5\<rangle>\<parallel>\<^sub>t"

lemma "\<parallel>\<langle>2\<rangle> : @int inv x == (\<langle>x\<rangle> < \<langle>5\<rangle>)\<parallel> = \<parallel>\<langle>2\<rangle> : @int\<parallel>"
  by (auto simp add:evalp defined typing)

lemma "\<parallel>(true,true) : {($x,$y) | $x = $y}\<parallel> = \<parallel>(true,true)\<parallel>"
  apply (utp_pred_tac)

instantiation fset :: (DEFINED) DEFINED
begin

definition "Defined_fset xs = (\<forall>x\<in>\<^sub>fxs. \<D> x)"

instance ..

end

lemma "\<parallel>{\<langle>1\<rangle>} : @set of @int\<parallel> = \<parallel>{\<langle>1\<rangle>}\<parallel>"
  by (auto simp add:evalp defined typing)

(*
lemma "\<lbrakk> \<D> <x::int>; \<D> <y> \<rbrakk> \<Longrightarrow> \<parallel>\<langle>x\<rangle> + \<langle>y\<rangle>\<parallel> = \<parallel>\<langle>y\<rangle> + \<langle>x\<rangle>\<parallel>"
  by (utp_expr_tac)

lemma "^defn defn ($''x'')^ = ^true^"
  by (utp_expr_tac)

lemma "^forall x :: int. \<langle>x\<rangle> in set {\<langle>x\<rangle>}^ = ^true^"
  by (utp_expr_tac)

lemma [evale]:"\<lbrakk>BOpD f BotDE y\<rbrakk>\<^sub>vb = None"
  by (simp add:BOpD_def evale)

lemma "^undefined in set {undefined}^ = ^undefined : @bool^"
  apply (utp_expr_tac)
oops

lemma "^true => false^ = ^false^"
  by (utp_expr_tac)
*)

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
