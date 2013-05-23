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

abbreviation "QuoteS x \<equiv> {Q x}"

abbreviation "vty_bool \<equiv> (UNIV :: bool set)"
abbreviation "vty_nat  \<equiv> (UNIV :: nat set)"
abbreviation "vty_int  \<equiv> (UNIV :: int set)"
abbreviation "vty_rat  \<equiv> (UNIV :: rat set)"
abbreviation "vty_real \<equiv> (UNIV :: real set)"

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
  "_vty_quote"  :: "string \<Rightarrow> vty" ("<_>")
  "_vty_union"  :: "vty \<Rightarrow> vty \<Rightarrow> vty" (infix "|" 50)
  "_vty_bool"    :: "vty" ("@bool")
  "_vty_nat"    :: "vty" ("@nat")
  "_vty_int"    :: "vty" ("@int")
  "_vty_rat"    :: "vty" ("@rat")
  "_vty_real"   :: "vty" ("@real")
  "_vty_set_of" :: "vty \<Rightarrow> vty" ("@set of _")
  "_vty_quo"  :: "vty \<Rightarrow> 'a set" ("&_&")
  "_vty_inv"  :: "vty \<Rightarrow> pttrn \<Rightarrow> vexpr \<Rightarrow> vty" ("_ inv _ == _")

translations
  "_vty_quote x"   == "CONST QuoteS x"
  "_vty_union x y" == "CONST union x y"
  "_vty_bool"       == "CONST vty_bool"
  "_vty_nat"       == "CONST vty_nat"
  "_vty_int"       == "CONST vty_int"
  "_vty_rat"       == "CONST vty_rat"
  "_vty_real"      == "CONST vty_real"
  "_vty_set_of A"  == "CONST Fow A"
  "_vty_quo x"     => "x"
  "_vty_inv A x P" == "CONST InvS A (\<lambda>x. P)"

end
