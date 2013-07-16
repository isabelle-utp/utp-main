(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_reactive.thy                                                     *)
(* Authors: Simon Foster, University of York                                  *)
(******************************************************************************)

header {* Reactive Processes *}

theory utp_reactive
imports 
  utp_designs
  utp_theory
begin

default_sort REACTIVE_SORT

abbreviation "wait \<equiv> MkPlainP ''wait'' True TYPE(bool) TYPE('m)"
abbreviation "tr   \<equiv> MkPlainP ''tr'' True TYPE('m EVENT ULIST) TYPE('m)"
abbreviation "ref  \<equiv> MkPlainP ''ref'' True TYPE('m EVENT UFSET) TYPE('m)"

definition SkipREA :: "'a WF_PREDICATE" where
"SkipREA = `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok' \<and> II\<^bsub>REL_VAR - OKAY\<^esub>)`"

syntax 
  "_upred_skiprea" :: " upred" ("II\<^bsub>rea\<^esub>")

translations
  "_upred_skiprea" == "CONST SkipREA"

declare SkipREA_def [eval, evalr]

text {* R1 ensures that the trace only gets longer *}

definition R1 :: " 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"R1(P) = `P \<and> ($tr \<le> $tr\<acute>)`"

text {* R2 ensures that the trace only gets longer *}

definition R2 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"R2(P) = `P[\<langle>\<rangle> / tr][($tr\<acute> - $tr) / tr\<acute>]`"

definition R3 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"R3(P) = `II\<^bsub>rea\<^esub> \<lhd> $wait \<rhd> P`"

syntax 
  "_upred_R1" :: "upred \<Rightarrow> upred" ("R1'(_')")
  "_upred_R2" :: "upred \<Rightarrow> upred" ("R2'(_')")
  "_upred_R3" :: "upred \<Rightarrow> upred" ("R3'(_')")

translations
  "_upred_R1 P" == "CONST R1 P"
  "_upred_R2 P" == "CONST R2 P"
  "_upred_R3 P" == "CONST R3 P"

declare R1_def [eval, evalr, evalrr, evalrx]
declare R2_def [eval, evalr, evalrr, evalrx]
declare R3_def [eval, evalr, evalrr, evalrx]
declare is_healthy_def [eval, evalr, evalrr, evalrx]
declare SkipREA_def [eval, evalr, evalrr, evalrx]

lemma R1_idempotent : "`R1(R1(P))` = `R1(P)`" by (utp_rel_tac)

lemma R2_idempotent : "`R2(R2(P))` = `R2(P)`" sorry

lemma R3_idempotent : "`R3(R3(P))` = `R3(P)`" by (utp_pred_auto_tac)

lemma R1_monotonic : "[P \<Rightarrow> Q] \<Longrightarrow> [R1(P) \<Rightarrow> R1(Q)]" by(utp_pred_tac)
lemma R2_monotonic : "[P \<Rightarrow> Q] \<Longrightarrow> [R2(P) \<Rightarrow> R2(Q)]" by(utp_pred_tac)
lemma R3_monotonic : "[P \<Rightarrow> Q] \<Longrightarrow> [R3(P) \<Rightarrow> R3(Q)]" by(utp_pred_tac)

lemma SkipREA_is_R1: "`II\<^bsub>rea\<^esub> \<and> ($tr \<le> $tr\<acute>)`= `II\<^bsub>rea\<^esub>`" sorry
lemma R1_true_is_R2 : "`($tr \<le> $tr\<acute>)[($tr\<acute> - $tr)/tr\<acute>][\<langle>\<rangle>/tr]` = `($tr \<le> $tr\<acute>)`"sorry
lemma SkipREA_is_R2 : "`II\<^bsub>rea\<^esub>[($tr\<acute> - $tr)/tr\<acute>][\<langle>\<rangle>/tr]` = `II\<^bsub>rea\<^esub>`" sorry
lemma wait_is_R2 : "`$wait[($tr\<acute> - $tr)/tr\<acute>][\<langle>\<rangle>/tr]` = `$wait`" sorry

lemma R1_R3_commute : "R1 (R3 P) = R3 (R1 P)" 
proof - 
  have "R1 (R3 P) = `(II\<^bsub>rea\<^esub> \<lhd> $wait \<rhd> P) \<and> ($tr \<le> $tr\<acute>)`" by (utp_rel_tac)
  also have "... = `(II\<^bsub>rea\<^esub> \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait \<rhd> (P \<and> ($tr \<le> $tr\<acute>))`" by (utp_pred_auto_tac)
  ultimately show ?thesis by (simp add:SkipREA_is_R1, utp_rel_tac)
qed

lemma R1_R2_commute : "R1 (R2 P) = R2 (R1 P)" 
proof -
  have "R2 (R1 P) = `(P \<and> ($tr \<le> $tr\<acute>))[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>]`" by (utp_rel_tac)
  also have "... = `P[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>] \<and> ($tr \<le> $tr\<acute>)`" 
    sorry(*by (simp add:usubst erasure typing defined closure R1_true_is_R2)*)
  ultimately show ?thesis by (utp_rel_tac)
qed
lemma R2_R3_commute : "R2 (R3 P) = R3 (R2 P)" 
proof - 
  have "R2 (R3 P) = `(II\<^bsub>rea\<^esub> \<lhd> $wait \<rhd> P)[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>]`" by (utp_rel_tac)
  also have "... = `II\<^bsub>rea\<^esub> \<lhd> $wait \<rhd> (P[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>])`"sorry(* by (simp add:usubst erasure typing defined closure SkipREA_is_R2 wait_is_R2)*)
  ultimately show ?thesis by (utp_rel_tac)
qed

definition R :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where 
"R P = (R1 \<circ> R2 \<circ> R3)P"

declare R_def [eval, evalr, evalrr, evalrx]
syntax 
  "_upred_R" :: "upred \<Rightarrow> upred" ("R'(_')")

translations
  "_upred_R P" == "CONST R P"

lemma SkipREA_CondR_SkipR: 
  "`II\<^bsub>rea\<^esub>` = `II \<lhd> ok \<rhd> ($tr \<le> $tr\<acute>)`"
proof -

  have "`II \<lhd> ok \<rhd> ($tr \<le> $tr\<acute>)` = `($okay\<acute> = $okay \<and> II\<^bsub>REL_VAR - OKAY\<^esub>) \<lhd> ok \<rhd> ($tr \<le> $tr\<acute>)`"
    by (simp add:SkipR_as_SkipRA SkipRA_unfold[of "okay\<down>"] closure erasure typing)

  also 
  have "... = `($okay\<acute> = $okay \<and> II\<^bsub>REL_VAR - OKAY\<^esub>)[true/okay] 
               \<lhd> ok \<rhd> 
               (($tr \<le> $tr\<acute>)[false/okay])`"
    by (simp add:erasure, rule_tac CondR_VarP_aux[of "okay\<down>"], simp_all)

  also have "... = `(ok' \<and> II\<^bsub>REL_VAR - OKAY\<^esub>) \<lhd> ok \<rhd> ($tr \<le> $tr\<acute>)`"
    by (simp add:usubst typing defined closure)

  also have "... = `(ok \<and> ok' \<and> II\<^bsub>REL_VAR - OKAY\<^esub>) \<or> (\<not> ok \<and> ($tr \<le> $tr\<acute>))`"
    by (utp_pred_auto_tac)

  also have "... = `II\<^bsub>rea\<^esub>`"
    apply (simp add:SkipREA_def)
    apply (rule_tac x="okay\<down>" in BoolType_aux_var_split_eq_intro)
    apply (simp_all add:usubst closure typing defined urename)
    apply (utp_pred_auto_tac)
    apply (drule_tac x="tr\<down>" in bspec)
    apply (simp_all add:var_dist closure)
  done
  finally show ?thesis ..
qed

end