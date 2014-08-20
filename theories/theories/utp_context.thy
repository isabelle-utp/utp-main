(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_context.thy                                                      *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* UTP Contexts *}

theory utp_context
imports 
  utp_theory
  "../alpha/utp_alpha_lattice"
  "../parser/utp_alpha_pred_parser"
begin

record 'm utp_struct = alpha :: "'m alpha"

record 'm thy_struct = "'m utp_struct" + thy :: "'m THEORY"

notation alpha ("\<Sigma>\<index>")
notation thy ("\<T>\<index>")

abbreviation "TopTS TS \<equiv> TopT (thy TS) (alpha TS)"
abbreviation "BotTS TS \<equiv> BotT (thy TS) (alpha TS)"
abbreviation "MeetTS TS p q \<equiv> MeetT p (thy TS) (alpha TS) q"
abbreviation "JoinTS TS p q \<equiv> JoinT p (thy TS) (alpha TS) q"
abbreviation "SupTS TS \<equiv> SupT (thy TS) (alpha TS)"
abbreviation "InfTS TS \<equiv> InfT (thy TS) (alpha TS)"

abbreviation WfpTS :: 
  "('a::TYPED_MODEL, 'b) thy_struct_scheme \<Rightarrow> ('a uapred \<Rightarrow> 'a uapred) \<Rightarrow> 'a uapred" ("\<mu>\<index>")
where "WfpTS TS \<equiv> GfpT (thy TS) (alpha TS)"

abbreviation SfpTS :: 
  "('a::TYPED_MODEL, 'b) thy_struct_scheme \<Rightarrow> ('a uapred \<Rightarrow> 'a uapred) \<Rightarrow> 'a uapred" ("\<nu>\<index>")
where "SfpTS TS \<equiv> LfpT (thy TS) (alpha TS)"

no_syntax
  "_n_uapred_true"     :: "'m alpha \<Rightarrow> n_uapred" ("true\<^bsub>_\<^esub>")
  "_n_uapred_false"    :: "'a alpha \<Rightarrow> n_uapred" ("false\<^bsub>_\<^esub>")
  "_n_uapred_skip"     :: "'a alpha \<Rightarrow> n_uapred" ("II\<^bsub>_\<^esub>")
  "_n_uapred_assign"   :: "'a uvar \<Rightarrow> 'a alpha \<Rightarrow> n_apexpr \<Rightarrow> n_uapred" ("_ :=\<^bsub>_ \<^esub>_" [100] 100)

no_translations
  "_n_uapred_true a"      == "CONST TrueA a"
  "_n_uapred_skip a"      == "CONST SkipA a"

no_notation TrueA ("true\<^bsub>_\<^esub>")

syntax
  "_n_uapred_true_st"   :: "'a utp_struct \<Rightarrow> n_uapred" ("true\<index>")
  "_n_uapred_false_st"  :: "'a utp_struct \<Rightarrow> n_uapred" ("false\<index>")
  "_n_uapred_top_st"    :: "'a utp_struct \<Rightarrow> n_uapred" ("\<top>\<index>")
  "_n_uapred_bot_st"    :: "'a utp_struct \<Rightarrow> n_uapred" ("\<bottom>\<index>")
  "_n_uapred_skip_st"   :: "'a utp_struct \<Rightarrow> n_uapred" ("II\<index>")
  "_n_uapred_assign_st" :: "'a utp_struct \<Rightarrow> 'a uvar \<Rightarrow> n_apexpr \<Rightarrow> n_uapred" ("_ :=\<index> _" [100] 100)
  "_n_uapred_meet_st"   :: "'a utp_struct \<Rightarrow> n_uapred \<Rightarrow> n_uapred \<Rightarrow> n_uapred" (infixl "\<squnion>\<index>" 65)
  "_n_uapred_join_st"   :: "'a utp_struct \<Rightarrow> n_uapred \<Rightarrow> n_uapred \<Rightarrow> n_uapred" (infixl "\<sqinter>\<index>" 70)
  "_n_uapred_wfp"       :: "logic \<Rightarrow> idt \<Rightarrow> n_uapred \<Rightarrow> n_uapred" ("(3\<mu>\<index>_./ _)" [0, 10] 10)
  "_n_uapred_sfp"       :: "logic \<Rightarrow> idt \<Rightarrow> n_uapred \<Rightarrow> n_uapred" ("(3\<nu>\<index>_./ _)" [0, 10] 10)

translations
  "_n_uapred_true_st A"       == "CONST TrueA (CONST alpha A)"
  "_n_uapred_false_st A"      == "CONST FalseA (CONST alpha A)"
  "_n_uapred_top_st A "       == "CONST TopTS A"
  "_n_uapred_bot_st A "       == "CONST BotTS A"
  "_n_uapred_skip_st A"       == "CONST SkipA (CONST alpha A)"
  "_n_uapred_assign_st A x e" == "CONST PAssignA x (CONST alpha A) e"
  "_n_uapred_meet_st A p q"   == "CONST MeetTS A p q"
  "_n_uapred_join_st A p q"   == "CONST JoinTS A p q"
  "_n_uapred_wfp A x p"       == "CONST WfpTS A (\<lambda>x. p)"
  "_n_uapred_sfp A x p"       == "CONST SfpTS A (\<lambda>x. p)"

no_notation
  WFP ("\<mu>") and SFP ("\<nu>")

locale UTP_CTX =
  fixes US :: "('m::TYPED_MODEL, 'e::type) utp_struct_scheme" (structure)

locale UTP_THY_CTX = 
  UTP_CTX "US" for US :: "('m::TYPED_MODEL, 'e::type) thy_struct_scheme" (structure) +
  assumes thy_is_theory: "UTP_THEORY \<T>" and alpha_of_theory: "\<Sigma> \<in> alphas \<T>"

locale UTP_THY_LAT_CTX =
   UTP_CTX +
   assumes thy_lat: "complete_lattice (OrderT \<T> \<Sigma>)"
begin

  abbreviation "Mono F \<equiv> isotone (OrderT \<T> \<Sigma>) (OrderT \<T> \<Sigma>) F"

  lemma WFP_unfold:
    assumes "Mono F" "F \<in> \<lbrakk>\<T>\<rbrakk>[\<Sigma>]\<T> \<rightarrow> \<lbrakk>\<T>\<rbrakk>[\<Sigma>]\<T>"
    shows "\<mu> F = F(\<mu> F)"
    by (metis assms(1) assms(2) complete_lattice.GFP_unfold partial_object.select_convs(1) thy_lat)

  lemma SFP_unfold:
    assumes "Mono F" "F \<in> \<lbrakk>\<T>\<rbrakk>[\<Sigma>]\<T> \<rightarrow> \<lbrakk>\<T>\<rbrakk>[\<Sigma>]\<T>"
    shows "\<nu> F = F(\<nu> F)"
    by (metis assms(1) assms(2) complete_lattice.LFP_unfold partial_object.select_convs(1) thy_lat)

end

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
