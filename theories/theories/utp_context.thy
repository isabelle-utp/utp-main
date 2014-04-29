(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_context.thy                                                      *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* UTP Contexts *}

theory utp_context
imports 
  utp_theory
  "../parser/utp_alpha_pred_parser"
begin

record 'm utp_struct = alpha :: "'m ALPHABET"

record 'm thy_struct = "'m utp_struct" + thy :: "'m THEORY"

notation alpha ("\<Sigma>\<index>")
notation thy ("\<T>\<index>")

abbreviation "TopTS TS \<equiv> TopT (thy TS) (alpha TS)"
abbreviation "BotTS TS \<equiv> BotT (thy TS) (alpha TS)"

no_syntax
  "_uapred_true"     :: "'m ALPHABET \<Rightarrow> uapred" ("true\<^bsub>_\<^esub>")
  "_uapred_false"    :: "'a ALPHABET \<Rightarrow> uapred" ("false\<^bsub>_\<^esub>")
  "_uapred_skip"     :: "'a ALPHABET \<Rightarrow> uapred" ("II\<^bsub>_\<^esub>")
  "_uapred_assign"   :: "'a VAR \<Rightarrow> 'a ALPHABET \<Rightarrow> apexpr \<Rightarrow> uapred" ("_ :=\<^bsub>_ \<^esub>_" [100] 100)

no_translations
  "_uapred_true a"      == "CONST TrueA a"
  "_uapred_skip a"      == "CONST SkipA a"

no_notation TrueA ("true\<^bsub>_\<^esub>")

syntax
  "_uapred_true_st"   :: "'a utp_struct \<Rightarrow> uapred" ("true\<index>")
  "_uapred_false_st"  :: "'a utp_struct \<Rightarrow> uapred" ("false\<index>")
  "_uapred_top_st"    :: "'a utp_struct \<Rightarrow> uapred" ("\<top>\<index>")
  "_uapred_bot_st"    :: "'a utp_struct \<Rightarrow> uapred" ("\<bottom>\<index>")
  "_uapred_skip_st"   :: "'a utp_struct \<Rightarrow> uapred" ("II\<index>")
  "_uapred_assign_st" :: "'a utp_struct \<Rightarrow> 'a VAR \<Rightarrow> apexpr \<Rightarrow> uapred" ("_ :=\<index> _" [100] 100)

translations
  "_uapred_true_st A"       == "CONST TrueA (CONST alpha A)"
  "_uapred_false_st A"      == "CONST FalseA (CONST alpha A)"
  "_uapred_top_st A "       == "CONST TopTS A"
  "_uapred_bot_st A "       == "CONST BotTS A"
  "_uapred_skip_st A"       == "CONST SkipA (CONST alpha A)"
  "_uapred_assign_st A x e" == "CONST PAssignA x (CONST alpha A) e"

locale UTP_CTX =
  fixes US :: "('m::VALUE, 'e::type) utp_struct_scheme" (structure)

locale UTP_THY_CTX = 
  UTP_CTX "US" for US :: "('m::VALUE, 'e::type) thy_struct_scheme" (structure) +
  assumes thy_is_theory: "UTP_THEORY \<T>" and alpha_of_theory: "\<Sigma> \<in> alphas \<T>"

locale UTP_REL_CTX = UTP_THY_CTX  +
  assumes RELT_thy [simp]: "\<T> \<le> RELT"
begin

lemma alpha_rel [closure]: "\<Sigma> \<in> REL_ALPHABET"
  by (metis RELT_thy THEORY.select_convs(1) alpha_of_theory less_eq_THEORY_ext_def set_mp)

end

locale UTP_HOM_CTX =
  UTP_REL_CTX +
  assumes alpha_hom [closure]: "\<Sigma> \<in> HOM_ALPHABET"
begin

lemma SkipA_right_unit: "in\<^sub>\<alpha> \<Sigma> = (out\<^sub>\<alpha> (\<alpha> P))\<acute> \<Longrightarrow> ``P ; II`` = ``P``"
  by (simp add:SemiA_SkipA_right closure)

lemma SkipA_left_unit: "out\<^sub>\<alpha> \<Sigma> = (in\<^sub>\<alpha> (\<alpha> P))\<acute> \<Longrightarrow> ``II ; P`` = ``P``"
  by (simp add:SemiA_SkipA_left closure)

lemma TrueA_right_unit_pre: "\<lbrakk> \<alpha>(p) = \<Sigma>; p \<in> COND \<rbrakk> \<Longrightarrow> ``p ; true`` = ``p``"
  by (utp_alpha_tac, metis SemiR_TrueP_precond WF_ALPHA_COND_EvalA_WF_CONDITION)

end


end
