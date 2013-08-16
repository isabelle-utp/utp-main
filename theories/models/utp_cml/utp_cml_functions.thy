(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: utp_cml_functions.thy                                                *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* CML Function Library *}

theory utp_cml_functions
imports 
  utp_cml_types
  utp_cml_expr
begin

text {* Set up the CML expression parser with API functions *}

text {* Numeric Functions *}

abbreviation idiv :: "real \<Rightarrow> real \<Rightarrow> real" where
"idiv x y \<equiv> (floor x) div (floor y)"

abbreviation imod :: "real \<Rightarrow> real \<Rightarrow> real" where
"imod x y \<equiv> (floor x) mod (floor y)"

abbreviation vpower :: "real \<Rightarrow> real \<Rightarrow> real" where
"vpower x n \<equiv> power x (nat (floor n))"

abbreviation "vexpr_uminus    \<equiv> Op1D' (uminus :: real \<Rightarrow> real)"
abbreviation "vexpr_abs       \<equiv> Op1D' (abs :: real \<Rightarrow> real)"
abbreviation "vexpr_floor     \<equiv> Op1D' (floor :: real \<Rightarrow> real)"
abbreviation "vexpr_plus      \<equiv> Op2D' (op + :: real \<Rightarrow> real \<Rightarrow> real)"
abbreviation "vexpr_minus     \<equiv> Op2D' (op - :: real \<Rightarrow> real \<Rightarrow> real)"
abbreviation "vexpr_mult      \<equiv> Op2D' (op * :: real \<Rightarrow> real \<Rightarrow> real)"
abbreviation "vexpr_divide    \<equiv> Op2D' (op / :: real \<Rightarrow> real \<Rightarrow> real)"
abbreviation "vexpr_idiv      \<equiv> Op2D' idiv"
abbreviation "vexpr_imod      \<equiv> Op2D' imod"
abbreviation "vexpr_power     \<equiv> Op2D' (vpower :: real \<Rightarrow> real \<Rightarrow> real)"
abbreviation "vexpr_le        \<equiv> Op2D' (op \<le> :: real \<Rightarrow> real \<Rightarrow> bool)"
abbreviation "vexpr_less      \<equiv> Op2D' (op < :: real \<Rightarrow> real \<Rightarrow> bool)"
abbreviation "vexpr_ge        \<equiv> Op2D' (\<lambda> (x::real) y. y \<le> x)"
abbreviation "vexpr_greater   \<equiv> Op2D' (\<lambda> (x::real) y. y < x)"

syntax
  "_vexpr_uminus"  :: "pexpr \<Rightarrow> pexpr" ("- _" [81] 80)
  "_vexpr_abs"     :: "pexpr \<Rightarrow> pexpr" ("abs _")
  "_vexpr_floor"   :: "pexpr \<Rightarrow> pexpr" ("floor _")
  "_vexpr_plus"    :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix "+" 30)
  "_vexpr_minus"   :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix "-" 65)
  "_vexpr_mult"    :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "*" 70)
  "_vexpr_divide"  :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "'/" 70)
  "_vexpr_idiv"    :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "div" 70)
  "_vexpr_imod"    :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "mod" 70)
  "_vexpr_power"   :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "**" 70)
  "_vexpr_le"      :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix "<=" 50)
  "_vexpr_less"    :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix "<" 50)
  "_vexpr_ge"      :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix ">=" 50)
  "_vexpr_greater" :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix ">" 50)

translations
  "_vexpr_uminus x"    == "CONST vexpr_uminus x"
  "_vexpr_abs x"       == "CONST vexpr_abs x"
  "_vexpr_floor x"     == "CONST vexpr_floor x"
  "_vexpr_plus x y"    == "CONST vexpr_plus x y"
  "_vexpr_minus x y"   == "CONST vexpr_minus x y"
  "_vexpr_mult x y"    == "CONST vexpr_mult x y"
  "_vexpr_divide x y"  == "CONST vexpr_divide x y"
  "_vexpr_idiv x y"    == "CONST vexpr_idiv x y"
  "_vexpr_imod x y"    == "CONST vexpr_imod x y"
  "_vexpr_power x y"   == "CONST vexpr_power x y"
  "_vexpr_le x y"      == "CONST vexpr_le x y"
  "_vexpr_less x y"    == "CONST vexpr_less x y"
  "_vexpr_ge x y"      == "CONST vexpr_le y x"
  "_vexpr_greater x y" == "CONST vexpr_less y x"

abbreviation "vexpr_defined   \<equiv> (DefinedD :: 'a cmle \<Rightarrow> bool cmle)"
abbreviation "vexpr_in_set    \<equiv> Op2D' (op \<in>\<^sub>f)"
abbreviation "vexpr_dunion    \<equiv> Op1D' FUnion"
abbreviation "vexpr_dinter    \<equiv> Op1D' FInter"
abbreviation "vexpr_subset    \<equiv> Op2D' (op \<subseteq>\<^sub>f)"
abbreviation "vexpr_psubset   \<equiv> Op2D' (op \<subset>\<^sub>f)"
abbreviation "vexpr_fpower    \<equiv> Op1D' FinPow"
abbreviation "vexpr_dom       \<equiv> Op1D' fdom"
abbreviation "vexpr_rng       \<equiv> Op1D' fran"
abbreviation "vexpr_card      \<equiv> Op1D' fcard"
abbreviation "vexpr_lookup    \<equiv> Op2D (\<lambda> (x, m). \<langle>m\<rangle>\<^sub>m x)"
abbreviation "vexpr_not       \<equiv> Op1D' Not"
abbreviation "vexpr_and       \<equiv> Op2D' conj"
abbreviation "vexpr_or        \<equiv> Op2D' disj"
abbreviation "vexpr_implies   \<equiv> Op2D' implies"
abbreviation "vexpr_hd        \<equiv> Op1D' hd"
abbreviation "vexpr_tl        \<equiv> Op1D' tl"

definition ForallSetD :: "'a fset cmle \<Rightarrow> ('a option \<Rightarrow> bool cmle) \<Rightarrow> bool cmle" where
"ForallSetD xs f = MkPExpr (\<lambda> b. (Some (\<forall> x \<in> \<langle>the (\<lbrakk>xs\<rbrakk>\<^sub>* b)\<rangle>\<^sub>f. \<lbrakk>f (Some x)\<rbrakk>\<^sub>* b = Some True)))"

syntax
  "_vexpr_quotev"  :: "string \<Rightarrow> pexpr" ("<_>")
  "_vexpr_defined" :: "pexpr \<Rightarrow> pexpr" ("defn _")
  "_vexpr_in_set"  :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix "in @set" 50)
  "_vexpr_union"   :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "union" 65)
  "_vexpr_inter"   :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "inter" 70)
  "_vexpr_dunion"  :: "pexpr \<Rightarrow> pexpr" ("dunion _")
  "_vexpr_dinter"  :: "pexpr \<Rightarrow> pexpr" ("dinter _")
  "_vexpr_sminus"  :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix "setminus" 70)
  "_vexpr_subset"  :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix "subset" 50) 
  "_vexpr_psubset" :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infix "psubset" 50)
  "_vexpr_fpower"  :: "pexpr \<Rightarrow> pexpr" ("power _")
  "_vexpr_card"    :: "pexpr \<Rightarrow> pexpr" ("card _")
  "_vexpr_dom"     :: "pexpr \<Rightarrow> pexpr" ("dom _")
  "_vexpr_rng"     :: "pexpr \<Rightarrow> pexpr" ("rng _")
  "_vexpr_not"     :: "pexpr \<Rightarrow> pexpr" ("not _" [40] 40)
  "_vexpr_and"     :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "and" 35)
  "_vexpr_or"      :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "or" 30)
  "_vexpr_implies" :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "=>" 25)
  "_vexpr_hd"      :: "pexpr \<Rightarrow> pexpr" ("hd _")
  "_vexpr_tl"      :: "pexpr \<Rightarrow> pexpr" ("tl _")
  "_vexpr_all_set" :: "pttrn \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" ("(3forall _ in @set _ @/ _)" [0, 0, 10] 10)

translations
  "_vexpr_quotev x"    == "CONST LitD (CONST QuoteD x)"
  "_vexpr_in_set x xs" == "CONST vexpr_in_set x xs"
  "_vexpr_defined x"   == "CONST vexpr_defined x"
  "_vexpr_union x y"   == "CONST Op2D' CONST funion x y"
  "_vexpr_inter x y"   == "CONST Op2D' CONST finter x y"
  "_vexpr_dunion xs"   == "CONST vexpr_dunion xs"
  "_vexpr_dinter xs"   == "CONST vexpr_dinter xs"
  "_vexpr_sminus x y"  == "CONST Op2D' CONST fminus x y"
  "_vexpr_subset x y"  == "CONST vexpr_subset x y"
  "_vexpr_psubset x y" == "CONST vexpr_psubset x y"
  "_vexpr_fpower xs"   == "CONST vexpr_fpower xs"
  "_vexpr_card x"      == "CONST vexpr_card x"
  "_vexpr_dom x"       == "CONST vexpr_dom x"
  "_vexpr_rng x"       == "CONST vexpr_rng x"
  "_vexpr_not x"       == "CONST vexpr_not x"
  "_vexpr_and x y"     == "CONST vexpr_and x y"
  "_vexpr_or x y"      == "CONST vexpr_or x y"
  "_vexpr_implies x y" == "CONST vexpr_implies x y"
  "_vexpr_hd xs"       == "CONST vexpr_hd xs"
  "_vexpr_tl xs"       == "CONST vexpr_tl xs"
  "_vexpr_all_set x xs p" == "CONST ForallSetD xs (\<lambda>x. p)"

lemma "|dunion({{1,3},{2},{3}})| = |{1,2,3}|"
  by (auto simp add:evalp)

term "|$x <= $y|"

term "|$x in @set {<1>}|"

term "|^x^|"

term "|mk_prod(1, {})|"

term "|forall x:@nat1 @ ^x^ > 1|"
term "|forall x in @set {1} @ ^x^ > 5|"

lemma "|forall x:@nat1 @ ^x^ > 0| = |true|"
  by (simp add:evalp)

term "|x > (5 : @int)|"
term "\<parallel>@int inv x == ^x^ > 5\<parallel>"

lemma "|2 : (@int inv x == (^x^ < 5))| = |2 : @int|"
  by (simp add:evalp typing defined)

lemma "|card {1,2,3}| = |3|"
  by (simp add:evalp)

instantiation fset :: (DEFINED) DEFINED
begin

definition "Defined_fset xs = (\<forall>x\<in>\<^sub>fxs. \<D> x)"

instance ..

end

text {* Some test lemmas ... *}

lemma "|{1} : @set of @int| = |{1}|"
  by (simp add:evalp defined typing)

lemma "|{1,2,3} hasType @set of @nat| = |true|"
  by (simp add:evalp)

lemma "|forall x : @int @ ^x^ in @set {^x^}| = |true|"
  by (simp add:evalp)

lemma "|true => false| = |false|"
  by (simp add:evalp)

term "`x := ({1,2,3,4,5,6,7} union {8,9})`"

lemma "|{2} union {3}| = |{2,3}|"
  by (simp add:evalp)

lemma "|card {2}| = |1|"
  by (simp add:evalp)

lemma "|2 in @set {3,2}| = |true|"
  by (simp add:evalp)

lemma "|5 <= 6| = |true|"
  by (simp add:evalp)

end
