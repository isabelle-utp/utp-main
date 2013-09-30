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

abbreviation "REA \<equiv> OKAY \<union> {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}"

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

definition R2s :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"R2s(P) = `P[\<langle>\<rangle> / tr][($tr\<acute> - $tr) / tr\<acute>]`"

definition R2 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"R2(P) = R1 (R2s P)"

definition R3 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"R3(P) = `II\<^bsub>rea\<^esub> \<lhd> $wait \<rhd> P`"

definition R :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where 
"R P = (R1 \<circ> R2 \<circ> R3)P"

declare R1_def [eval, evalr, evalrr, evalrx]
declare R2_def [eval, evalr, evalrr, evalrx]
declare R2s_def [eval, evalr, evalrr, evalrx]
declare R3_def [eval, evalr, evalrr, evalrx]
declare is_healthy_def [eval, evalr, evalrr, evalrx]
declare SkipREA_def [eval, evalr, evalrr, evalrx]
declare R_def [eval, evalr, evalrr, evalrx]

subsection {* Closure Laws *}

lemma WF_RELATION_UNREST:
  "NON_REL_VAR \<sharp> P \<Longrightarrow> P \<in> WF_RELATION"
  by (simp add:WF_RELATION_def)

lemma SkipREA_rel_closure [closure]:
  "`II\<^bsub>rea\<^esub>` \<in> WF_RELATION"
  by (simp add:SkipREA_def closure unrest erasure WF_RELATION_UNREST)

lemma R1_rel_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> R1(P) \<in> WF_RELATION"
  by (simp add:R1_def closure unrest WF_RELATION_UNREST)

lemma R2s_rel_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> R2s(P) \<in> WF_RELATION"
  by (simp add:R2s_def unrest typing defined closure)

lemma R2_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> R2(P) \<in> WF_RELATION"
  by (simp add:R2_def closure)

lemma R3_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> R3(P) \<in> WF_RELATION"
  by (simp add:R3_def closure)

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

lemma H1_SkipREA: 
  "`H1(II\<^bsub>rea\<^esub>)` = `H1(II)`"
proof -
  have "`H1(II\<^bsub>rea\<^esub>)` = `ok \<Rightarrow> II\<^bsub>rea\<^esub>`"
    by (simp add:H1_def)

  also have "... = `ok \<Rightarrow> (II \<lhd> ok \<rhd> ($tr \<le> $tr\<acute>))`"
    by (simp add:SkipREA_CondR_SkipR)

  also have "... = `ok \<Rightarrow> II`"
    by (metis (lifting, no_types) CondR_true_cond ImpliesP_export)

  finally show ?thesis
    by (simp add:H1_def)
qed

lemma H2_SkipREA:
  "`H2(II\<^bsub>rea\<^esub>)` = `II\<^bsub>rea\<^esub>`"
proof -
  have "`H2(II\<^bsub>rea\<^esub>)` = `II\<^bsub>rea\<^esub>\<^sup>f \<or> (II\<^bsub>rea\<^esub>\<^sup>t \<and> ok')`"
    by (simp add:H2_def J_split closure)

  also have "... = `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> II\<^bsub>REL_VAR - OKAY\<^esub> \<and> ok'`"
    apply (simp add:SkipREA_def usubst typing defined closure)
    apply (utp_pred_auto_tac)
  done

  also have "... = `II\<^bsub>rea\<^esub>`"
    apply (simp add:SkipREA_def)
    apply (utp_pred_auto_tac)
  done

  finally show ?thesis .
qed

lemma R1_idempotent:
  "R1(R1(P)) = R1(P)"
  by (utp_rel_tac)

lemma R1_AndP:
  "`R1(P \<and> Q)` = `R1(P) \<and> R1(Q)`"
  by (utp_pred_auto_tac)

lemma R1_OrP:
  "`R1(P \<or> Q)` = `R1(P) \<or> R1(Q)`"
  by (utp_pred_auto_tac)
  
lemma R1_CondR:
  "`R1(P \<lhd> b \<rhd> Q)` = `R1(P) \<lhd> b \<rhd> R1(Q)`"
by (utp_pred_auto_tac)
  
lemma R1_SkipR:
  "R1(II) = II"
  by (auto simp add:eval closure)

lemma R1_by_refinement:
  "P is R1 \<longleftrightarrow> `$tr \<le> $tr\<acute>` \<sqsubseteq> P" 
  by (utp_pred_auto_tac)

lemma tr_leq_trans:
  "`($tr \<le> $tr\<acute>) ; ($tr \<le> $tr\<acute>)` = `($tr \<le> $tr\<acute>)`"
  by (auto intro: binding_equiv_trans simp add:closure typing defined unrest closure evalr evalp relcomp_unfold urename)

theorem R1_SemiR [closure]:
  assumes
    "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
    "P is R1" "Q is R1"
  shows "(P ; Q) is R1"
  using assms
  apply (unfold R1_by_refinement)
  apply (rule order_trans)
  apply (rule SemiR_mono_refine)
  apply (simp_all, simp add:tr_leq_trans)
done

lemma R1_tr_leq_tr':
  "`R1($tr \<le> $tr\<acute>)` = `$tr \<le> $tr\<acute>`"
  by (simp add:R1_def)

lemma R1_H2_commute:
  "P \<in> WF_RELATION \<Longrightarrow> H2(R1(P)) = R1(H2(P))"
  apply (simp add: H2_def J_split usubst unrest closure)
  apply (simp add: R1_def usubst typing defined)
  apply (utp_pred_auto_tac)
done

lemma SkipRA_is_R1 : 
  "`R1(II\<^bsub>REL_VAR - OKAY\<^esub>)` = `II\<^bsub>REL_VAR - OKAY\<^esub>`"
  by (auto simp add:var_dist closure eval)

lemma SkipRA_is_R2 : "`R2(II\<^bsub>REL_VAR - OKAY\<^esub>)` = `II\<^bsub>REL_VAR - OKAY\<^esub>`"
  apply (utp_pred_auto_tac)
  apply (drule_tac x="tr\<down>" in bspec)
  apply (auto simp add:var_dist closure eval typing defined)
sorry

lemma SkipREA_is_R1:
  "`R1(II\<^bsub>rea\<^esub>)` = `II\<^bsub>rea\<^esub>`"
  by (simp add:SkipREA_CondR_SkipR R1_CondR R1_SkipR R1_tr_leq_tr')

lemma SkipREA_is_R2 : "`R2(II\<^bsub>rea\<^esub>)` = `II\<^bsub>rea\<^esub>`"
proof-
  have "`R2(II\<^bsub>rea\<^esub>)` = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok' \<and> R2(II\<^bsub>REL_VAR - OKAY\<^esub>))`" 
    by (simp add: R2_def R1_def SkipREA_def R2s_def usubst typing defined closure, utp_pred_auto_tac)
  thus ?thesis 
    by (simp add:SkipRA_is_R2 SkipREA_def)
qed

(*
lemma Skip_is_R2s : "`R2s(II\<^bsub>REL_VAR - OKAY\<^esub>)` = `II\<^bsub>REL_VAR - OKAY\<^esub>`"
  apply (utp_pred_auto_tac)
  apply (drule_tac x="tr\<down>" in bspec)
  apply (auto simp add:var_dist closure eval)[1]
sorry
*)

lemma tr_conserved_is_R2 : "`R2s($tr = $tr\<acute>)` = `($tr = $tr\<acute>)`"
  apply(simp add:R2s_def usubst typing defined closure, utp_pred_auto_tac)
sorry

(*
lemma R3_wait: "`R3(P) \<and> $wait` = `II\<^bsub>rea\<^esub>`"
  apply (simp add:R3_def)
  apply (subst AndP_comm)
  apply (subst CondR_true_cond)
  apply (utp_pred_auto_tac)
*)

lemma helper1 : "`$wait \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub>` = `$wait \<and> $wait\<acute> \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub>`"
  by (auto simp add:var_dist closure evalr evale)
lemma helper2: "`($wait\<acute> \<and> Q) ; R3(P)` = `$wait\<acute> \<and> Q`" sorry
lemma helper3 : "`(\<not> ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) ; P` = `(\<not> ok \<and> $wait \<and> ($tr \<le> $tr\<acute>))`"sorry
lemma helper4 : "`\<langle>\<rangle> = ($tr\<acute> - $tr)` =`$tr\<acute> = $tr`" sorry
lemma wait_then_P_equals_wait : "`(($wait \<and> II\<^bsub>rea\<^esub>) \<and> ($tr \<le> $tr\<acute>)) ; P` = `(($wait \<and> II\<^bsub>rea\<^esub>) \<and> ($tr \<le> $tr\<acute>))`" sorry
lemma R2s_R3_commute : "R2s (R3 P) = R3 (R2s P)" sorry
lemma Assist : "`P[false/okay\<acute>] \<or> P[true/okay\<acute>]` = `P`"sorry
lemma Assist7 : "`(($tr < $tr\<acute>) \<and> ($tr^\<langle>a\<rangle> =$tr\<acute>))` = `($tr^\<langle>a\<rangle> =$tr\<acute>)`" sorry

lemma tr_conserved_is_R1 : "`R1($tr = $tr\<acute>)` = `($tr = $tr\<acute>)`" by (simp add:R1_def, utp_pred_auto_tac)

lemma R2s_idempotent : "`R2s(R2s(P))` = `R2s(P)`"
  apply (simp add:R2s_def)
  apply (subst SubstP_twice_3) back
  apply (simp_all add:typing defined closure unrest)
  apply (simp add:usubst typing defined closure)
done

lemma wait_is_R2s : "`R2s($wait)` = `$wait`" by(simp add:R2s_def usubst closure typing defined)
lemma R2s_destroys_R1 : "R2s (R1 P) = R2s P" by(simp add:R2s_def R1_def usubst closure typing defined, utp_pred_auto_tac)
lemma conj_distributes_through_conditional : "`(P \<lhd> b \<rhd> Q) \<and> S` = `(P \<and> S)\<lhd> b \<rhd>(Q \<and> S)`"by utp_pred_auto_tac
lemma R2s_distributes_through_conjunction : "`R2s(P \<and> Q)` = `R2s(P) \<and> R2s(Q)`" by utp_pred_auto_tac
lemma R2s_distributes_through_conditional : "`R2s(P \<lhd> b \<rhd> Q)` = `R2s(P)\<lhd> R2s(b) \<rhd>R2s(Q)`"by utp_pred_auto_tac
lemma R2_distributes_through_conditional : "`R2(P \<lhd> b \<rhd> Q)` =`R2(P) \<lhd> R2s(b) \<rhd> R2(Q)`" by utp_pred_auto_tac
lemma R3_distributes_through_disjunction :"`R3(P \<or> Q)` = `R3(P) \<or> R3(Q)`"by utp_pred_auto_tac
lemma R3_distributes_through_conditional :"`R3(P \<lhd> b \<rhd> Q)` = `R3(P) \<lhd> R3(b) \<rhd> R3(Q)`"by utp_pred_auto_tac
lemma seq_comp_assoc : "`(P ; Q) ; S` = `P ; (Q ; S)`"by (metis SemiR_assoc)
lemma R2s_distributes_through_disjunction: "`R2s(A \<or> C)` = `R2s(A) \<or> R2s(C)`" by utp_pred_auto_tac
lemma R1_not_ok : "`(\<not> ok \<and> ($tr \<le> $tr\<acute>))` = `R1(\<not> ok)`" by (simp add:R1_def)
lemma not_ok_is_R2s : "`R2s(\<not> ok)` = `\<not> ok`" by (simp add:R2s_def usubst typing defined closure) 
lemma ok_dash_is_R2s : "`R2s(ok')` = `ok'`"by (simp add:R2s_def usubst typing defined closure)
lemma Assist5 : "`R1(P \<and> Q)` = `P \<and> R1(Q)`" by utp_pred_auto_tac
lemma wait_is_R2 : "`$wait[($tr\<acute> - $tr)/tr\<acute>][\<langle>\<rangle>/tr]` = `$wait`" by(simp add:usubst typing defined closure)
lemma not_wait_is_R2 : "`(\<not> $wait)[($tr\<acute> - $tr)/tr\<acute>][\<langle>\<rangle>/tr]` = `\<not> $wait`" by(simp add:usubst typing defined closure)
lemma conj_through_dist_2 : "`P \<and> Q \<or> S` = `(P \<and> Q) \<or> (P \<and> S)`" by utp_pred_auto_tac
lemma negation_of_disjunction  : "`\<not>(P \<or> Q)` = `(\<not>P \<and> \<not>Q)`" by utp_pred_auto_tac
lemma DesignD_form : "`(P \<turnstile> Q)` = `\<not>ok \<or> \<not>P \<or> (ok' \<and> Q)`" by(simp add:DesignD_def, utp_pred_auto_tac)
lemma aider3 : "`$okay\<acute> \<and> II\<^bsub>rea\<^esub>[true/okay\<acute>]` = `$okay\<acute> \<and> II\<^bsub>rea\<^esub>`"by(simp add:SkipREA_def usubst typing defined closure, utp_pred_auto_tac)

lemma R2_idempotent : "`R2(R2(P))` = `R2(P)`" by(simp add:R2_def R2s_destroys_R1 R2s_idempotent)
lemma R3_idempotent : "`R3(R3(P))` = `R3(P)`" by (utp_pred_auto_tac)

lemma R1_monotonic : "[P \<Rightarrow> Q] \<Longrightarrow> [R1(P) \<Rightarrow> R1(Q)]" by utp_pred_tac
lemma R2_monotonic : "[P \<Rightarrow> Q] \<Longrightarrow> [R2(P) \<Rightarrow> R2(Q)]" by utp_pred_tac
lemma R3_monotonic : "[P \<Rightarrow> Q] \<Longrightarrow> [R3(P) \<Rightarrow> R3(Q)]" by utp_pred_tac

lemma R1_R2_commute : "R1 (R2 P) = R2 (R1 P)" by (simp add:R2_def R1_idempotent R2s_destroys_R1)

lemma R1_R3_commute : "R1 (R3 P) = R3 (R1 P)" 
proof - 
  have "R1 (R3 P) = `(II\<^bsub>rea\<^esub> \<lhd> $wait \<rhd> P) \<and> ($tr \<le> $tr\<acute>)`" by utp_rel_tac
  also have "... = `(II\<^bsub>rea\<^esub> \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait \<rhd> (P \<and> ($tr \<le> $tr\<acute>))`" by utp_pred_auto_tac
  also have "... = `II\<^bsub>rea\<^esub> \<lhd> $wait \<rhd> (P \<and> ($tr \<le> $tr\<acute>))`" by (metis R1_def SkipREA_is_R1)
  ultimately show ?thesis by utp_pred_auto_tac
qed

lemma R2_R3_commute : "R2 (R3 P) = R3 (R2 P)" 
proof - 
  have "R2 (R3 P) = `R2(II\<^bsub>rea\<^esub>) \<lhd> R2s($wait) \<rhd> R2(P)`" by (simp add:R3_def R2_distributes_through_conditional)
  also have "... = `II\<^bsub>rea\<^esub> \<lhd> $wait \<rhd> R2(P)`" by(simp add: SkipREA_is_R2, simp add:R2s_def usubst closure typing defined)
  ultimately show ?thesis by utp_pred_tac
qed



subsection {* The theory of Reactive Processes *}

lift_definition REACTIVE :: "'VALUE WF_THEORY" 
is "({vs. vs \<subseteq> REL_VAR \<and> REA \<subseteq> vs}, {R1,R2,R3})"
  by (simp add:WF_THEORY_def IDEMPOTENT_OVER_def R1_idempotent R2_idempotent R3_idempotent)

end