(******************************************************************************)
(* Project: VDM model for Isabelle/UTP                                        *)
(* File: utp_vdm_types.thy                                                    *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* VDM expressions *}

theory utp_vdm_types
imports 
  utp_vdm_expr
begin

datatype quote = Q string

instantiation quote :: vbasic
begin

primrec Inject_quote :: "quote \<Rightarrow> vbasic" where
"Inject (Q x) = QuoteI x"

definition Type_quote :: "quote itself \<Rightarrow> vdmt" where
"Type_quote x = QuoteT"

instance
  apply (intro_classes)
  apply (case_tac x, case_tac y, simp)
  apply (auto)
  apply (case_tac xa, auto simp add:Type_quote_def)
  apply (case_tac xa, auto simp add:Type_quote_def)
  apply (simp add:image_def)
  apply (rule_tac x="Q xa" in exI)
  apply (auto)
done
end

abbreviation "QuoteS x \<equiv> {Q x}"

abbreviation "vty_bool \<equiv> (UNIV :: bool set)"
abbreviation "vty_nat  \<equiv> (UNIV :: nat set)"
abbreviation "vty_nat1 \<equiv> {x::nat. x > 1}"
abbreviation "vty_int  \<equiv> (UNIV :: int set)"
abbreviation "vty_rat  \<equiv> (UNIV :: rat set)"
abbreviation "vty_real \<equiv> (UNIV :: real set)"
abbreviation "vty_char \<equiv> (UNIV :: char set)"
abbreviation "vty_prod \<equiv> op \<times>"
abbreviation "vty_seq_of A  \<equiv> {xs. set xs \<subseteq> A}" 
abbreviation "vty_seq1_of A \<equiv> {xs. set xs \<subseteq> A \<and> length xs > 0}" 

definition Fow :: "'a set \<Rightarrow> 'a fset set" where
"Fow A = {Abs_fset x | x. x \<subseteq> A \<and> finite x}"

lemma Fow_mem [iff]: "x \<in> Fow A \<longleftrightarrow> \<langle>x\<rangle>\<^sub>f \<subseteq> A"
  apply (auto simp add:Fow_def)
  apply (rule_tac x="\<langle>x\<rangle>\<^sub>f" in exI)
  apply (simp)
done

(* FIXME: It may be that VDM types need to be binding dependent
   as they can potentially depend on UTP variables. *)
definition InvS :: "'a set \<Rightarrow> ('a \<Rightarrow> bool vdme) \<Rightarrow> 'a set" where
"InvS A P = {x. x \<in> A \<and> (\<forall> b. \<lbrakk>P x\<rbrakk>\<^sub>v b = Some True)}"

syntax 
  "_vty_quote"   :: "string \<Rightarrow> vty" ("<_>")
  "_vty_brack"   :: "vty \<Rightarrow> vty" ("'(_')")
  "_vty_union"   :: "vty \<Rightarrow> vty \<Rightarrow> vty" (infixr "|" 65)
  "_vty_set"     :: "'a set \<Rightarrow> vty" ("@_")
  "_vty_bool"    :: "vty" ("@bool")
  "_vty_nat"     :: "vty" ("@nat")
  "_vty_nat1"     :: "vty" ("@nat1")
  "_vty_int"     :: "vty" ("@int")
  "_vty_rat"     :: "vty" ("@rat")
  "_vty_char"    :: "vty" ("@char")
  "_vty_real"    :: "vty" ("@real")
  "_vty_set_of"  :: "vty \<Rightarrow> vty" ("@set of _")
  "_vty_seq_of"  :: "vty \<Rightarrow> vty" ("@seq of _")
  "_vty_seq1_of" :: "vty \<Rightarrow> vty" ("@seq1 of _")
  "_vty_prod"    :: "vty \<Rightarrow> vty \<Rightarrow> vty" (infixl "\<times>" 20)
  "_vty_quo"     :: "vty \<Rightarrow> 'a set" ("\<parallel>_\<parallel>")
  "_vty_inv"     :: "vty \<Rightarrow> pttrn \<Rightarrow> vexpr \<Rightarrow> vty" ("_ inv _ == _")

translations
  "_vty_quote x"   == "CONST QuoteS x"
  "_vty_union x y" == "CONST union x y"
  "_vty_set x"     => "x"
  "_vty_brack x"   => "x"
  "_vty_bool"      == "CONST vty_bool"
  "_vty_nat"       == "CONST vty_nat"
  "_vty_nat1"      == "CONST vty_nat1"
  "_vty_int"       == "CONST vty_int"
  "_vty_rat"       == "CONST vty_rat"
  "_vty_real"      == "CONST vty_real"
  "_vty_char"      == "CONST vty_char"
  "_vty_prod x y"  == "CONST vty_prod x y"
  "_vty_set_of A"  == "CONST Fow A"
  "_vty_seq_of A"  == "CONST vty_seq_of A"
  "_vty_seq1_of A" == "CONST vty_seq1_of A"
  "_vty_quo x"     => "x"
  "_vty_inv A x P" == "CONST InvS A (\<lambda>x. P)"

term "\<parallel>@seq1 of @char\<parallel>"

term "|[\<langle>1\<rangle>]|"

term "`''x'' := [\<langle>1\<rangle>] : @seq1 of @nat1`"

end
