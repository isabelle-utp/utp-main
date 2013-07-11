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
"SkipREA = `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok\<acute> \<and> II\<^bsub>REL_VAR - OKAY\<^esub>)`"

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

definition R :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where 
"R P = (R1 \<circ> R2 \<circ> R3)P"

syntax 
  "_upred_R1" :: "upred \<Rightarrow> upred" ("R1'(_')")
  "_upred_R2" :: "upred \<Rightarrow> upred" ("R2'(_')")
  "_upred_R3" :: "upred \<Rightarrow> upred" ("R3'(_')")
  "_upred_R" :: "upred \<Rightarrow> upred" ("R'(_')")

translations
  "_upred_R1 P" == "CONST R1 P"
  "_upred_R2 P" == "CONST R2 P"
  "_upred_R3 P" == "CONST R3 P"
  "_upred_R P" == "CONST R P"

lemma PVAR_VAR_inj [dest]:
  fixes x y :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "x\<down> = y\<down>"
  shows "x = y"
   by (metis PVAR_VAR_inv assms)

lemma PSubstPE_PVarPE_neq [usubst]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  and   x :: "('b :: DEFINED, 'm :: VALUE) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "x\<down> \<noteq> y\<down>" "v \<rhd>\<^sub>* y"
  shows "PSubstPE (PVarPE x) v y = PVarPE x"
  using assms by (auto simp add:eval typing defined pevar_compat_def)

lemma var_name_uniq [simp]: 
  "name x \<noteq> name y \<Longrightarrow> x \<noteq> y"
  by (auto)

lemma name_str_uniq [simp]: 
  "name_str x \<noteq> name_str y \<Longrightarrow> x \<noteq> y"
  by (auto)

declare EvalPE_PSubstPE [evalp]

lemma SubstP_PSubstPE [usubst]:
  fixes v :: "('a :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  and   e :: "('b :: DEFINED, 'm :: VALUE) WF_PEXPRESSION"
  assumes "TYPEUSOUND('a, 'm)" "TYPEUSOUND('b, 'm)" "v \<rhd>\<^sub>* x"
  shows "e\<down>[v\<down>/\<^sub>ex\<down>] = (PSubstPE e v x)\<down>"
  using assms by (auto simp add:evale typing defined evalp)

term "(PVarPE x)"

lemma PVarPE_VarP [simp]:
  fixes x :: "(bool, 'm::BOOL_SORT) PVAR"
  shows "((PVarPE x)\<down> ==\<^sub>p (TruePE\<down>)) = VarP (x\<down>)"
  apply (utp_pred_auto_tac)
  apply (metis BOOL_SORT_class.Inverse)
done


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
    apply (simp_all add:usubst closure typing defined)
  sorry

  finally show ?thesis ..
qed

end