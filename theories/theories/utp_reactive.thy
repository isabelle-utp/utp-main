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
  "reactive/utp_reactive_lemmas"
begin

default_sort REACTIVE_SORT

abbreviation "ref  \<equiv> MkPlainP ''ref'' True TYPE('m EVENT USET) TYPE('m)"

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

definition RH :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where 
"RH P = (R1 \<circ> R2 \<circ> R3)P"

declare R1_def [eval, evalr, evalrr, evalrx]
declare R2_def [eval, evalr, evalrr, evalrx]
declare R2s_def [eval, evalr, evalrr, evalrx]
declare R3_def [eval, evalr, evalrr, evalrx]
declare is_healthy_def [eval, evalr, evalrr, evalrx]
declare SkipREA_def [eval, evalr, evalrr, evalrx]
declare RH_def [eval, evalr, evalrr, evalrx]

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

lemma R2_rel_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> R2(P) \<in> WF_RELATION"
  by (simp add:R2_def closure)

lemma R3_rel_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> R3(P) \<in> WF_RELATION"
  by (simp add:R3_def closure)

lemma RH_rel_closure [closure]: 
  "P \<in> WF_RELATION \<Longrightarrow> RH(P) \<in> WF_RELATION"
  by (simp add:RH_def closure)

subsection {* Sorried Laws *}

(* Trace sequence relation *)
lemma Aida : "`(($tr \<le> $tr\<acute>) ; ((\<not>ok \<and> $wait) \<and> ($tr \<le> $tr\<acute>)))`=`($tr \<le> $tr\<acute>)`"
  apply (subst SemiR_remove_middle_unrest1[of _ _ "{okay\<down>, wait\<down>}"])
  apply (simp_all add: closure typing defined unrest WF_RELATION_UNREST)
  apply (utp_pred_tac)
  apply (rule_tac x="\<B>(okay\<down> :=\<^sub>b FalseV, wait\<down> :=\<^sub>b TrueV)" in exI)
  apply (simp add:typing)
  apply (metis tr_leq_trans)
done
    
lemma Aidb : "`$okay \<and> ($okay\<acute> = $okay)` = `$okay \<and> $okay\<acute>`" by (utp_pred_auto_tac)
lemma Aidc : "`$wait \<and> ($wait\<acute> = $wait)` = `$wait \<and> $wait\<acute>`" by (utp_pred_auto_tac)
lemma Aidd : "`II\<^bsub>REL_VAR - OKAY\<^esub>\<^sub>t`=`$wait\<acute> \<and> II\<^bsub>REL_VAR - OKAY - {wait\<down>, wait\<down>\<acute>}\<^esub>`"
  apply (subst SkipRA_unfold[of "wait \<down>"])
  apply (simp_all)
  apply (metis MkPlain_UNDASHED PVAR_VAR_MkPVAR)
  apply (metis MkPlain_UNDASHED PVAR_VAR_MkPVAR UNDASHED_dash_DASHED)
  apply (metis MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED) 
  apply (utp_pred_auto_tac)
  apply (simp add: usubst typing closure defined)
  apply (subst VarP_EqualP_aux)
  apply (simp_all add:typing erasure)
done

subsection {* SkipREA Laws *}

(* Additional lemmas *)

lemma SkipRA_is_R1 : 
  "`R1(II\<^bsub>REL_VAR - OKAY\<^esub>)` = `II\<^bsub>REL_VAR - OKAY\<^esub>`"
  by (auto simp add:var_dist closure eval)

lemma tr_conserved_is_R1 : "`R1($tr\<acute> = $tr)` = `($tr\<acute> = $tr)`" 
  by (simp add:R1_def, utp_pred_auto_tac)

lemma R1_monotonic: "P \<sqsubseteq> Q \<Longrightarrow> R1(P) \<sqsubseteq> R1(Q)" 
  by utp_pred_tac

(*L1 H1-wait-okay' *)

lemma H1_wait_true: 
  "(H1(P))\<^sub>t = H1(P\<^sub>t)"
by(utp_pred_auto_tac)

lemma H1_wait_false: 
  "(H1(P))\<^sub>f = H1(P\<^sub>f)"
by(utp_pred_auto_tac)

lemma H1_okay'_true: 
  "(H1(P))\<^sup>t = H1(P\<^sup>t)"
by(utp_pred_auto_tac)

lemma H1_okay'_false: 
  "(H1(P))\<^sup>f = H1(P\<^sup>f)"
by(utp_pred_auto_tac)

(*L3 II_rea-II_rel-conditional *)

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

(*L2 II_rea-II_rel *)

lemma SkipREA_SkipR: 
  "`II\<^bsub>rea\<^esub>` = `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> II`"
proof -
  have "`II\<^bsub>rea\<^esub>` = `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> II)`" by(simp add: OrP_comm SkipREA_CondR_SkipR CondR_def)
  also have "... = `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not> ok \<and> ($tr \<le> $tr\<acute>) \<and> II) \<or> (ok \<and> II)`" by utp_pred_auto_tac
  also have "... = `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not> ok \<and> II) \<or> (ok \<and> II)`"
  proof -
    have "`($tr \<le> $tr\<acute>) \<and> II` = `R1(II)`"
      by utp_pred_auto_tac
    also have "... = `R1($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - {tr\<down>,tr\<down>\<acute>}\<^esub>`"
      apply(simp add:SkipR_as_SkipRA)
      apply(subst SkipRA_unfold[of "tr \<down>"])
      apply(simp_all)
      apply(metis MkPlain_UNDASHED PVAR_VAR_MkPVAR)
      apply(metis MkPlain_UNDASHED PVAR_VAR_MkPVAR UNDASHED_dash_DASHED)
      apply(metis MkPlain_UNDASHED PVAR_VAR_MkPVAR)
      apply(simp add:typing closure defined erasure)
      apply(utp_pred_auto_tac)
      done
    also have "... = `($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - {tr\<down>,tr\<down>\<acute>}\<^esub>`"
      by(utp_pred_auto_tac)
    finally have "`($tr \<le> $tr\<acute>) \<and> II` = `II`" 
      apply(simp add: SkipR_as_SkipRA)
      apply(subst SkipRA_unfold[of "tr \<down>"]) back
      apply(simp_all)
      apply(metis MkPlain_UNDASHED PVAR_VAR_MkPVAR)
      apply(metis MkPlain_UNDASHED PVAR_VAR_MkPVAR UNDASHED_dash_DASHED)
      apply(metis MkPlain_UNDASHED PVAR_VAR_MkPVAR)
      apply(simp add:typing closure defined erasure)
      done 
    thus ?thesis by metis
  qed
  finally show ?thesis by utp_pred_auto_tac
qed

(*L4 okay-II_rea-II_rel *)

lemma ok_SkipREA_SkipR : 
  "`ok \<and> II\<^bsub>rea\<^esub>` = `ok \<and> II`"
proof -
  have "`ok \<and> II\<^bsub>rea\<^esub>` = `ok \<and> ok' \<and> II\<^bsub>REL_VAR - OKAY\<^esub>`" 
    by(utp_pred_auto_tac)
  also have "... = `ok \<and> II\<^bsub>REL_VAR\<^esub>`" 
  proof -
      have "`ok \<and> ok'` = `ok \<and> ($okay\<acute> = $okay)`"
        by (metis Aidb)
      thus ?thesis
        apply(simp add: SkipRA_unfold[of "okay \<down>"] closure erasure typing defined)
        apply(utp_pred_auto_tac)
        done
  qed
  finally show ?thesis 
    by (metis SkipR_as_SkipRA)
qed

(*L5 okay-II_rea-sequence-unit *)

lemma okay_SkipREA_sequence_unit : 
assumes 
  "P \<in> WF_RELATION"
shows
  "`(ok \<and> II\<^bsub>rea\<^esub>) ; P` = `ok \<and> P`"
proof -
  have "`(ok \<and> II\<^bsub>rea\<^esub>) ; P` = `(ok \<and> II) ; P`" 
    by (metis ok_SkipREA_SkipR)
  also  have "... = `ok \<and> (II ; P)`"
    by (subst SemiR_AndP_left_precond, simp_all add:SkipR_closure assms MkPlainP_UNDASHED PUNDASHED_WF_CONDITION)
  finally show ?thesis 
    by(simp)
qed

(*L6 II_rea-H2 *)

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

(*L7 H1-II_rea-II_rel *)

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

subsection {* R1 Laws *}

(* L1 R1-idempotent *)

lemma R1_idempotent:
  "R1(R1(P)) = R1(P)"
  by (utp_rel_tac)

(* L2 R1-\<and> *)

lemma R1_AndP:
  "`R1(P \<and> Q)` = `R1(P) \<and> R1(Q)`"
  by (utp_pred_auto_tac)

(* L3 R1-\<or> *)

lemma R1_OrP:
  "`R1(P \<or> Q)` = `R1(P) \<or> R1(Q)`"
  by (utp_pred_auto_tac)
  
(* L4 R1-extend-\<and> *)

lemma R1_extend_AndP : 
  "`R1(P) \<and> Q` = `R1(P \<and> Q)`"
  by (utp_pred_auto_tac)

(* L5 R1-conditional *)

lemma R1_CondR:
  "`R1(P \<lhd> b \<rhd> Q)` = `R1(P) \<lhd> b \<rhd> R1(Q)`"
  by (utp_pred_auto_tac)

(* L6 R1-negate-R1 *)

lemma R1_negate_R1: 
  "`R1(\<not>R1(P))` = `R1(\<not>P)`"
  by(utp_pred_auto_tac)
  
(* L7 R1-wait-okay' *)

lemma R1_wait_true: 
  "(R1(P))\<^sub>t = R1(P\<^sub>t)"
by(utp_pred_auto_tac)

lemma R1_wait_false: 
  "(R1(P))\<^sub>f = R1(P\<^sub>f)"
by(utp_pred_auto_tac)

lemma R1_okay'_true: 
  "(R1(P))\<^sup>t = R1(P\<^sup>t)"
by(utp_pred_auto_tac)

lemma R1_okay'_false: 
  "(R1(P))\<^sup>f = R1(P\<^sup>f)"
by(utp_pred_auto_tac)

(* L8 II_rel-R1 *)

lemma R1_SkipR:
  "R1(II) = II"
  by (auto simp add:eval closure)

(* L9 II_rea-R1 *)

lemma R1_SkipREA:
  "`R1(II\<^bsub>rea\<^esub>)` = `II\<^bsub>rea\<^esub>`"
  by (auto simp add:eval closure)

lemma R1_tr_leq_tr':
  "`R1($tr \<le> $tr\<acute>)` = `$tr \<le> $tr\<acute>`"
  by (simp add:R1_def)

lemma SkipREA_is_R1:
  "`R1(II\<^bsub>rea\<^esub>)` = `II\<^bsub>rea\<^esub>`"
  by (simp add:SkipREA_CondR_SkipR R1_CondR R1_SkipR R1_tr_leq_tr')

(* L10 R1-\<and>-closure *)

lemma R1_AndP_closure: 
assumes "P is R1" "Q is R1"
shows "`(P \<and> Q)` is R1"
by (metis Healthy_intro Healthy_simp R1_extend_AndP assms(1))

(* L11 R1-\<or>-closure *)

lemma R1_OrP_closure: 
assumes "P is R1" "Q is R1"
shows "`(P \<or> Q)` is R1"
by (metis R1_OrP assms(1) assms(2) is_healthy_def)

(* L12 R1-conditional-closure *)

lemma R1_CondR_closure: 
assumes "P is R1" "Q is R1"
shows "`(P \<lhd> b \<rhd> Q)` is R1"
by (metis Healthy_intro Healthy_simp R1_CondR assms(1) assms(2))

(* L13 R10-sequence-closure *)

lemma R1_by_refinement:
  "P is R1 \<longleftrightarrow> `$tr \<le> $tr\<acute>` \<sqsubseteq> P" 
  by (utp_pred_auto_tac)

theorem R1_SemiR_closure [closure]:
  assumes
    "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
    "P is R1" "Q is R1"
  shows "(P ; Q) is R1"
  using assms
  apply (unfold R1_by_refinement)
  apply (rule order_trans)
  apply (rule SemiR_mono_refine)
  apply (simp_all)
  apply (simp add:tr_leq_trans)
done

(* L14 II_rea-R1-H1 *)

lemma SkipREA_R1_H1: 
  "`II\<^bsub>rea\<^esub>` = `R1(H1(II\<^bsub>rea\<^esub>))`"
proof -
  from SkipREA_is_R1 have "`II\<^bsub>rea\<^esub>` = `R1(II\<^bsub>rea\<^esub>)`" 
    ..
  thus ?thesis 
    by(utp_pred_auto_tac)
qed

(* L15 R1-H2-commutativity *)

lemma R1_H2_commute:
  assumes "P \<in> WF_RELATION"
  shows "H2(R1(P)) = R1(H2(P))"
  apply (simp add: H2_def J_split unrest closure)
  apply (subst J_split)
  apply (metis R1_rel_closure assms)
  apply (subst J_split)
  apply (metis assms)
  apply (simp add: R1_def usubst typing defined)
  apply (utp_pred_auto_tac)
done

subsection {* R2 Laws *}

(* L3 R2-idempotent *)

lemma R2s_idempotent: "`R2s(R2s(P))` = `R2s(P)`"
  apply (simp add:R2s_def)
  apply (subst SubstP_twice_3) back
  apply (simp_all add:typing defined closure unrest)
  apply (simp add:usubst typing defined closure)
done

lemma R2s_destroys_R1: "R2s (R1 P) = R2s P" 
  by (simp add:R2s_def R1_def usubst closure typing defined)

lemma R2_idempotent: "`R2(R2(P))` = `R2(P)`" 
  by (simp add:R2_def R2s_destroys_R1 R2s_idempotent)

(* L4 R2-\<and>-closure *)

lemma R2s_AndP: 
  "`R2s(P \<and> Q)` = `R2s(P) \<and> R2s(Q)`" 
  by (utp_pred_auto_tac)

lemma R2_AndP: "`R2(P \<and> Q)` = `R2(P) \<and> R2(Q)`"
  by (utp_pred_auto_tac)

lemma R2_AndP_closure: 
assumes "P is R2" "Q is R2"
shows "`P \<and> Q` is R2"
by (metis R2_AndP assms(1) assms(2) is_healthy_def)

(* L5 R2-\<or>-closure *)

lemma R2s_OrP: 
  "`R2s(A \<or> C)` = `R2s(A) \<or> R2s(C)`" 
  by (utp_pred_auto_tac)

lemma R2_OrP: "`R2(P \<or> Q)` = `R2(P) \<or> R2(Q)`"
  by (utp_pred_auto_tac)

lemma R2_OrP_closure: 
assumes "P is R2" "Q is R2"
shows "`P \<or> Q` is R2"
by (metis R2_OrP assms(1) assms(2) is_healthy_def)

(* L7 R2-cond-closure-2 *)

lemma R2s_CondR: 
  "`R2s(P \<lhd> b \<rhd> Q)` = `R2s(P) \<lhd> R2s(b) \<rhd> R2s(Q)`"
  by (utp_pred_auto_tac)

lemma R2_CondR: 
  "`R2(P \<lhd> b \<rhd> Q)` =`R2(P) \<lhd> R2s(b) \<rhd> R2(Q)`" 
  by (utp_pred_auto_tac)

lemma R2_CondR_alt: 
  "`R2(P \<lhd> b \<rhd> Q)` =`R2(P) \<lhd> R2(b) \<rhd> R2(Q)`" 
  by (utp_pred_auto_tac)

lemma R2_negate: 
  "`R2(\<not> b)` = `R1(\<not>R2(b))`"
by(utp_pred_auto_tac)

lemma R2_CondR_closure_2: 
assumes "P is R2" "Q is R2" "b is R2"
shows "`P \<lhd> b \<rhd> Q` is R2"
using assms
proof -
  have "`R2(P \<lhd> b \<rhd> Q)`  = `(R2(b) \<and> R2(P)) \<or> (R1(\<not> R2(b)) \<and> R2(Q))`"
    by(simp add:CondR_def R2_OrP R2_AndP R2_negate)
  also have "... = `(R2(b) \<and> R2(P)) \<or> (\<not> R2(b) \<and> R2(Q))`"
    by(utp_pred_auto_tac)
  also from assms have "... = `(b \<and> P) \<or> (\<not> b \<and> Q)`" 
    by(simp add:is_healthy_def)
  finally show ?thesis
    by (simp add:is_healthy_def CondR_def)
qed

(* L6 R2-cond-closure-1 *)

lemma tr_conserved_is_R2 : "`R2($tr\<acute> = $tr)` = `($tr\<acute> = $tr)`"
  apply(simp add:R2_def R2s_def R1_def usubst typing defined closure)
  apply (metis EqualP_sym tr_prefix_as_nil)
done

lemma R2_CondR_closure_1: 
assumes "P is R2" "Q is R2"
shows "`P \<lhd> ($tr\<acute> = $tr) \<rhd> Q` is R2"
by(subst R2_CondR_closure_2, simp_all add:assms, simp add:is_healthy_def tr_conserved_is_R2)

(* L9 R2-composition *)
(*R2 *)
lemma R2_sequential_composition: 
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "`R2(P);R2(Q)` = `R2(P ; R2(Q))`"
proof -
have "`R2(P;R2(Q))` = `R2(\<exists> tr\<acute>\<acute>\<acute> . (P[$tr\<acute>\<acute>\<acute>/tr\<acute>]);(R2(Q)[$tr\<acute>\<acute>\<acute>/tr]))`"
  apply(subst SemiR_extract_variable[where x="tr \<down>"])
  apply (metis assms(1))
  apply (metis R2_rel_closure assms(2))
  apply (metis MkPlain_UNDASHED PVAR_VAR_MkPVAR)
  apply (simp add:closure typing defined erasure)
  done
also have "... = `R1(

(\<exists> tr\<acute>\<acute>\<acute> . P[$tr\<acute>\<acute>\<acute>/tr\<acute>];(Q[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>] \<and>  ($tr \<le> $tr\<acute>))[$tr\<acute>\<acute>\<acute>/tr])

[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>]

)`"
  by(simp add:R2_def R1_def R2s_def)
also have "... = `R1(\<exists> tr\<acute>\<acute>\<acute> . (P[$tr\<acute>\<acute>\<acute>/tr\<acute>];(Q[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>] \<and>  ($tr \<le> $tr\<acute>))[$tr\<acute>\<acute>\<acute>/tr])[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>])`"
  apply(subst SubstP_ExistsP)
  apply(simp_all add:unrest typing defined closure)
  apply(subst SubstP_ExistsP)
  apply(simp_all add:unrest typing defined closure)
  done
also have "... = `R1(\<exists> tr\<acute>\<acute>\<acute> . (P[\<langle>\<rangle>/tr][$tr\<acute>\<acute>\<acute>/tr\<acute>];(Q[\<langle>\<rangle>/tr][(($tr\<acute> - $tr) - $tr\<acute>\<acute>\<acute>)/tr\<acute>] \<and>  ($tr\<acute>\<acute>\<acute> \<le> ($tr\<acute> - $tr)))))`"
   apply(subst SubstP_SemiR_left[of "tr \<down>"])
   apply (metis MkPlain_UNDASHED PVAR_VAR_MkPVAR)
   apply(simp_all add:unrest typing defined closure)
   sorry (*distributing substitution through SemiR *)
also have "... = `R1(\<exists> tr\<acute>\<acute>\<acute>\<acute> . \<exists> tr\<acute>\<acute>\<acute> . $tr\<acute>\<acute>\<acute>\<acute> = $tr^$tr\<acute>\<acute>\<acute> \<and> (P[\<langle>\<rangle>/tr][($tr\<acute>\<acute>\<acute>\<acute> - $tr)/tr\<acute>];(Q[\<langle>\<rangle>/tr][(($tr\<acute> - $tr) - ($tr\<acute>\<acute>\<acute>\<acute> - $tr))/tr\<acute>] \<and>  (($tr\<acute>\<acute>\<acute>\<acute> - $tr) \<le> ($tr\<acute> - $tr)))))`" sorry (*introduce fresh quantifier *)
also have "... = `R1(\<exists> tr\<acute>\<acute>\<acute>\<acute> . (P[\<langle>\<rangle>/tr][($tr\<acute>\<acute>\<acute>\<acute> - $tr)/tr\<acute>];(Q[\<langle>\<rangle>/tr][(($tr\<acute> - $tr) - ($tr\<acute>\<acute>\<acute>\<acute> - $tr))/tr\<acute>] \<and>  (($tr\<acute>\<acute>\<acute>\<acute> - $tr) \<le> ($tr\<acute> - $tr)))))`" sorry (*remove old quantifier *)
also have "... = `R1(\<exists> tr\<acute>\<acute>\<acute>\<acute> . (P[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>][$tr\<acute>\<acute>\<acute>\<acute>/tr\<acute>];(Q[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>][$tr\<acute>\<acute>\<acute>\<acute>/tr\<acute>] \<and>  ($tr \<le> $tr\<acute>\<acute>\<acute>\<acute>) \<and> ($tr\<acute>\<acute>\<acute>\<acute> \<le> $tr\<acute>))))`" sorry (*resolving substitutions *)
also have "... = `R1(\<exists> tr\<acute>\<acute>\<acute>\<acute> . ((P[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>][$tr\<acute>\<acute>\<acute>\<acute>/tr\<acute>] \<and> ($tr \<le> $tr\<acute>)[$tr\<acute>\<acute>\<acute>\<acute>/tr\<acute>]);(Q[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>][$tr\<acute>\<acute>\<acute>\<acute>/tr] \<and> ($tr \<le> $tr\<acute>)[$tr\<acute>\<acute>\<acute>\<acute>/tr])))`" sorry (*resolving substitutions *)
also have "... = `R1(\<exists> tr\<acute>\<acute>\<acute>\<acute> . ((P[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>] \<and> ($tr \<le> $tr\<acute>))[$tr\<acute>\<acute>\<acute>\<acute>/tr\<acute>];(Q[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>] \<and> ($tr \<le> $tr\<acute>))[$tr\<acute>\<acute>\<acute>\<acute>/tr]))`" 
  by(simp add:usubst)
also have "... = `R1(\<exists> tr\<acute>\<acute>\<acute> . ((P[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>] \<and> ($tr \<le> $tr\<acute>))[$tr\<acute>\<acute>\<acute>/tr\<acute>];(Q[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>] \<and> ($tr \<le> $tr\<acute>))[$tr\<acute>\<acute>\<acute>/tr]))`" sorry (*rename quantifier*)
also have "... = `R1(\<exists> tr\<acute>\<acute>\<acute> . (R2(P)[$tr\<acute>\<acute>\<acute>/tr\<acute>];R2(Q)[$tr\<acute>\<acute>\<acute>/tr]))`" 
  by(simp add:R1_def R2_def R2s_def)
also have "... = `R1(R2(P);R2(Q))`"
  apply(subst SemiR_extract_variable[where x="tr \<down>"]) back
  apply (metis R2_rel_closure assms(1))
  apply (metis R2_rel_closure assms(2))
  apply (metis MkPlain_UNDASHED PVAR_VAR_MkPVAR)
  apply (simp add:closure typing defined erasure)
  done
also have "... = `R2(P);R2(Q)`"
  proof -
  have "`R2(P);R2(Q)` is R1" 
    by(subst R1_SemiR_closure, simp_all add: assms R2_rel_closure, simp_all add:R2_def is_healthy_def R1_idempotent)
  thus ?thesis 
    by (metis Healthy_simp)
  qed
finally show ?thesis by simp 
qed

lemma R2_composition: 
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "R2(P ; R2(Q)) = R2(P) ; R2(Q)"
by (metis R2_sequential_composition assms(1) assms(2))
    
(* L8 R2-sequence-closure *)

lemma R2_SemiR_closure: 
assumes "P is R2" "Q is R2" "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
shows "`P;Q` is R2"
proof -
  have "`R2(P;Q)`=`R2(P;R2(Q))`"
    by(metis assms(2) is_healthy_def)
  also have "... = R2(P);R2(Q)"
    by(metis R2_composition assms(3) assms(4))
  also have "... = P ; Q"
    by(metis assms is_healthy_def)
  finally show ?thesis 
    by (simp add:is_healthy_def)
qed

(* L10 R2-wait-okay' *)

lemma R2_wait_true: "(R2(P))\<^sub>t = R2(P\<^sub>t)"
  apply(simp add:R2_def R1_wait_true R2s_def)
  apply(subst SubstP_twice_3) back
  apply(simp_all)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(simp_all add:usubst typing defined closure)
  apply(simp add:unrest closure typing defined)
  apply(subst SubstP_twice_3) back back
  apply(simp_all)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(simp_all add:usubst typing defined closure)
  apply(simp add:unrest closure typing defined)
  done

lemma R2_wait_false: "(R2(P))\<^sub>f = R2(P\<^sub>f)"
  apply(simp add:R2_def R1_wait_false R2s_def)
  apply(subst SubstP_twice_3) back
  apply(simp_all)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(simp_all add:usubst typing defined closure)
  apply(simp add:unrest closure typing defined)
  apply(subst SubstP_twice_3) back back
  apply(simp_all)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(simp_all add:usubst typing defined closure)
  apply(simp add:unrest closure typing defined)
  done

lemma R2_okay'_true: "(R2(P))\<^sup>t = R2(P\<^sup>t)"  
  apply(simp add:R2_def R1_okay'_false R2s_def)
  apply(subst SubstP_twice_3) back
  apply(simp_all)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(simp_all add:usubst typing defined closure)
  apply(simp add:unrest closure typing defined)
  apply(subst SubstP_twice_3) back back
  apply(simp_all)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(simp_all add:usubst typing defined closure)
  apply(simp add:unrest closure typing defined)
  apply (metis (hide_lams, no_types) PVAR_VAR_pvdash R1_okay'_true)
  done

lemma R2_okay'_false: "(R2(P))\<^sup>f = R2(P\<^sup>f)"
  apply(simp add:R2_def R1_okay'_false R2s_def)
  apply(subst SubstP_twice_3) back
  apply(simp_all)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(simp_all add:usubst typing defined closure)
  apply(simp add:unrest closure typing defined)
  apply(subst SubstP_twice_3) back back
  apply(simp_all)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(simp_all add:usubst typing defined closure)
  apply(simp add:unrest closure typing defined)
  apply (metis (hide_lams, no_types) PVAR_VAR_pvdash R1_okay'_false)
  done

(* L11 J-R2 *)

lemma J_is_R2: 
  "J is R2"

proof -
  have "R2 J = `R1 ((ok \<Rightarrow> ok') \<and> (($tr\<acute> - $tr) = \<langle>\<rangle>) \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>}\<^esub>)`"
    apply (simp add:J_pred_def)
    apply (subst SkipRA_unfold[of "tr \<down>"])
    apply (simp_all)
    apply (metis MkPlain_UNDASHED PVAR_VAR_MkPVAR)
    apply (metis MkPlain_UNDASHED PVAR_VAR_MkPVAR UNDASHED_dash_DASHED)
    apply (metis MkPlain_UNDASHED PVAR_VAR_MkPVAR)
    apply (utp_pred_auto_tac)
    apply (simp add:is_healthy_def R2_def R2s_def)
    apply (simp add:usubst typing defined closure)
    done
  also have "... = `(ok \<Rightarrow> ok') \<and> R1(($tr\<acute> - $tr) = \<langle>\<rangle>) \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>}\<^esub>`"
    by (utp_pred_auto_tac)
  also have "... = `(ok \<Rightarrow> ok') \<and> ($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>}\<^esub>`"
    by (simp add:R1_def tr_prefix_as_nil)
  also have "... = J"
    apply(simp add:J_pred_def)
    apply(subst SkipRA_unfold[of "tr \<down>"]) back
    apply(simp_all)
    apply (metis MkPlain_UNDASHED PVAR_VAR_MkPVAR)
    apply (metis MkPlain_UNDASHED PVAR_VAR_MkPVAR UNDASHED_dash_DASHED)
    apply (metis MkPlain_UNDASHED PVAR_VAR_MkPVAR)
    apply (utp_pred_auto_tac)
    apply(simp add:closure typing defined erasure)
    done
  finally show ?thesis 
    by (simp add:is_healthy_def)
qed

(* L12 commutativity-R2-H1 *)
(*No longer holds in original form since R2 has R1 like properties *)

lemma H1_R2s_commute: "H1 (R2s P) = R2s (H1 P)"
  by(simp add:H1_def R2s_def usubst typing defined closure)

(* L13 commutativity R2-H2 *)

lemma H2_R2_commute: 
  assumes "P \<in> WF_RELATION"
  shows "H2 (R2 P) = R2 (H2 P)" 
proof -
  have "H2 (R2 P) = (R2 P);(R2 J)" 
    by(metis H2_def J_is_R2 is_healthy_def)
  also have "... = R2 (P ; (R2 J))"
    apply(subst R2_composition)
    apply (metis assms)
    apply (metis J_closure)
    apply (simp)
    done
  also have "... = R2 (P ; J) " 
    by(metis J_is_R2 is_healthy_def)
  finally show ?thesis 
    by(simp add:H2_def)
qed

(* L14 commutativity R2-R1 *)

lemma R1_R2_commute: 
  "R1 (R2 P) = R2 (R1 P)" 
by (simp add:R2_def R1_idempotent R2s_destroys_R1)

(* Additional lemmas *)

lemma R2_monotonic: "P \<sqsubseteq> Q \<Longrightarrow> R2(P) \<sqsubseteq> R2(Q)" 
  by utp_pred_tac

lemma SkipRA_is_R2 : "`R2(II\<^bsub>REL_VAR - OKAY\<^esub>)` = `II\<^bsub>REL_VAR - OKAY\<^esub>`"
proof -
  have "`R2(II\<^bsub>REL_VAR - OKAY\<^esub>)` = `(($tr\<acute> - $tr) = \<langle>\<rangle> \<and> II\<^bsub>REL_VAR - OKAY - TR\<^esub>) \<and> ($tr \<le> $tr\<acute>)`"
    apply (simp add:R1_def R2_def R2s_def)
    apply (subst SkipRA_unfold[of "tr\<down>"])
    apply (auto simp add:closure)
    apply (simp add:usubst closure typing defined)
  done

  also have "... = `(($tr\<acute> - $tr) = \<langle>\<rangle> \<and> ($tr \<le> $tr\<acute>)) \<and> II\<^bsub>REL_VAR - OKAY - TR\<^esub>`"
    by (metis (hide_lams, no_types) AndP_assoc AndP_comm)

  also have "... = `$tr\<acute> = $tr \<and> II\<^bsub>REL_VAR - OKAY - TR\<^esub>`"
    by (metis EqualP_sym tr_prefix_as_nil)

  also have "... = `II\<^bsub>REL_VAR - OKAY\<^esub>`"
    apply (subst SkipRA_unfold[of "tr\<down>"]) back
    apply (auto simp add:closure erasure typing)
  done

  finally show ?thesis .
qed

lemma SkipREA_is_R2 : "`R2(II\<^bsub>rea\<^esub>)` = `II\<^bsub>rea\<^esub>`"
proof-
  have "`R2(II\<^bsub>rea\<^esub>)` = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok' \<and> R2(II\<^bsub>REL_VAR - OKAY\<^esub>))`" 
    apply (simp add: R2_def R1_def SkipREA_def R2s_def usubst typing defined closure)
    apply(utp_pred_auto_tac)
    done
  thus ?thesis 
    by (simp add:SkipRA_is_R2 SkipREA_def)
qed

subsection {* R3 Laws *}

(* L1 R3-wait-true *)

lemma R3_wait_true: 
  "`(R3(P))\<^sub>t` = `(II\<^bsub>rea\<^esub>)\<^sub>t` "
by(simp add:R3_def usubst typing defined closure CondR_def)

(* L2 R3-wait-false *)

lemma R3_wait_false: 
  "`(R3(P))\<^sub>f` = `P\<^sub>f` "
by(simp add:R3_def usubst typing defined closure CondR_def)

(* L3 R3-okay' *)

lemma R3_okay'_true: 
  "(R3(P))\<^sup>t = `II\<^bsub>rea\<^esub>\<^sup>t \<lhd> $wait \<rhd>(P\<^sup>t)`"
by(simp add:R3_def usubst typing defined closure)

lemma R3_okay'_false: 
  "(R3(P))\<^sup>f = `II\<^bsub>rea\<^esub>\<^sup>f \<lhd> $wait \<rhd>(P\<^sup>f)`"
by(simp add:R3_def usubst typing defined closure)

(* L4 closure-\<and>-R3 *)

lemma R3_AndP: 
  "`R3(P \<and> Q)` = `R3(P) \<and> R3(Q)`"
by(utp_pred_auto_tac)

lemma R3_AndP_closure:
  assumes "P is R3" "Q is R3"
  shows "`P \<and> Q` is R3"
by(metis is_healthy_def R3_AndP assms)

(* L5 closure-\<or>-R3 *)

lemma R3_OrP: 
  "`R3(P \<or> Q)` = `R3(P) \<or> R3(Q)`"
by(utp_pred_auto_tac)

lemma R3_OrP_closure:
  assumes "P is R3" "Q is R3"
  shows "`P \<or> Q` is R3"
by(metis is_healthy_def R3_OrP assms)
  
(* L6 closure-conditional-R3 *)

lemma R3_CondR: 
  "`R3(P  \<lhd> b \<rhd> Q)` = `R3(P) \<lhd> b \<rhd> R3(Q)`"
by(utp_pred_auto_tac)

lemma R3_CondR_closure:
  assumes "P is R3" "Q is R3"
  shows "`P \<lhd> b \<rhd> Q` is R3"
by(metis is_healthy_def R3_CondR assms)

(* L7 closure-sequence-R3 *)

lemma R3_form : "`R3(P)` = `(\<not>ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait  \<and> II) \<or> (\<not>$wait \<and> P)`"
  apply(simp add:R3_def SkipREA_CondR_SkipR CondR_def)
  apply(utp_pred_auto_tac)
done

lemma R3_form_2 : "`R3(P)` = `(\<not>ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait  \<and> II) \<or> (\<not>$wait \<and> P\<^sub>f )`"
proof -
  have "`\<not>$wait \<and> P` = `\<not>$wait \<and> P\<^sub>f`"
    by (subst NotP_PVarPE_PSubstPE, simp_all add:typing)
  thus ?thesis
    by(simp add:R3_form)
qed

lemma R3_wait: "`R3(P) \<and> $wait` = `II\<^bsub>rea\<^esub> \<and> $wait`"
  apply (simp add:R3_def)
  apply (subst AndP_comm)
  apply (subst CondR_true_cond)
  apply (subst AndP_comm)
  apply (rule refl)
done

theorem R3_SemiR_closure [closure]:
  assumes
    "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
    "P is R3" "Q is R3" "Q is R1"
  shows "(P ; Q) is R3"
proof -
  have "`(\<not>ok \<and> $wait \<and> ($tr \<le> $tr\<acute>));Q` = `\<not>ok \<and> $wait \<and> (($tr \<le> $tr\<acute>);Q)`"
    apply(subst SemiR_AndP_left_precond)
    apply (metis MkPlainP_UNDASHED PUNDASHED_WF_CONDITION R1_def R1_rel_closure WF_CONDITION_WF_RELATION)
    apply (metis assms(2))
    apply (metis TopD_cond_closure TopD_def)
    apply(subst SemiR_AndP_left_precond)
    apply (simp_all)
    apply (metis R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
    apply (metis assms(2))
    apply (metis MkPlainP_UNDASHED PUNDASHED_WF_CONDITION)
    done
  moreover have "`($tr \<le> $tr\<acute>) ; Q ` = `($tr \<le> $tr\<acute>)`"
  proof-
    have 1: "`(($tr \<le> $tr\<acute>) ; (\<not>ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)))`=`($tr \<le> $tr\<acute>)`"
      by (metis (hide_lams, no_types) Aida AndP_assoc)
    have 2: "`(($tr \<le> $tr\<acute>);(ok \<and> $wait \<and> II))` is R1" 
      apply(subst R1_SemiR_closure)
      apply(simp_all)
      apply (metis R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
      apply (metis AndP_rel_closure MkPlainP_UNDASHED PUNDASHED_WF_CONDITION SkipR_closure WF_CONDITION_WF_RELATION)
      apply (metis R1_by_refinement order_refl)
      apply (metis (full_types) AndP_comm Healthy_intro R1_SkipR R1_extend_AndP)
      done
    have 3: "`(($tr \<le> $tr\<acute>);(\<not>$wait \<and> Q))` is R1"
      apply(subst R1_SemiR_closure)
      apply(simp_all)
      apply (metis R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
      apply (metis AndP_rel_closure MkPlainP_UNDASHED NotP_rel_closure PUNDASHED_WF_CONDITION WF_CONDITION_WF_RELATION assms(2))
      apply (metis R1_by_refinement order_refl)  
      apply (metis (full_types) AndP_comm R1_extend_AndP assms(5) is_healthy_def)
      done
    have "`($tr \<le> $tr\<acute>) ; Q` = `($tr \<le> $tr\<acute>) ; R3(Q)`"
      by (metis Healthy_simp assms)
    also have "... = `(($tr \<le> $tr\<acute>) ; (\<not>ok \<and> $wait \<and> ($tr \<le> $tr\<acute>))) \<or> (($tr \<le> $tr\<acute>);(ok \<and> $wait \<and> II)) \<or> (($tr \<le> $tr\<acute>);(\<not>$wait \<and> Q))`"
      by(simp add:R3_form SemiR_OrP_distl)
    also have "... = `($tr \<le> $tr\<acute>) \<or> R1(($tr \<le> $tr\<acute>);(ok \<and> $wait \<and> II)) \<or> R1(($tr \<le> $tr\<acute>);(\<not>$wait \<and> Q))`"
      by(metis 1 2 3 is_healthy_def)
    also have "... = `($tr \<le> $tr\<acute>)`"
      by(utp_pred_auto_tac)
    finally show ?thesis 
      ..
  qed
  ultimately have 1: "`(\<not>ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) ; Q` = `\<not>ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)`" by metis
  have a : "`((($okay \<and> $wait \<and> II) \<and> ($okay)\<acute>) \<and> ($wait)\<acute>)` = `ok \<and> ok' \<and> $wait \<and> $wait\<acute> \<and> II`"
    by (smt AndP_assoc AndP_comm ConvR_VarP_1 MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED PVAR_VAR_pvdash)
  have 2: "`(ok \<and> $wait \<and> II);Q` = `ok \<and> $wait \<and> II`"
    proof -
      have "`ok \<and> $wait \<and> II` = `ok \<and> $wait \<and> ($okay\<acute> = $okay) \<and> ($wait\<acute> = $wait) \<and> II`"
        apply (simp add:SkipR_as_SkipRA)
        apply (subst SkipRA_unfold[of "okay \<down>"])
        apply(simp_all)
        apply (metis MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED)
        apply(utp_pred_auto_tac)
        apply (metis MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED)
        apply (subst SkipRA_unfold[of "okay \<down>"]) back
        apply(simp_all)
        apply (metis MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED)
        apply(utp_pred_auto_tac)
        apply (metis MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED)
        apply (subst SkipRA_unfold[of "wait \<down>"])
        apply(simp_all)
        apply (metis MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED)
        apply(utp_pred_auto_tac)
        apply (metis MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED)
        apply(utp_pred_auto_tac)
        apply (subst SkipRA_unfold[of "wait \<down>"]) back
        apply(simp_all)
        apply (metis MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED)
        apply(utp_pred_auto_tac)
        apply (metis MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED)
        apply(utp_pred_auto_tac)
        apply(simp add:erasure typing defined closure)
        apply (smt AndP_assoc AndP_idem)
        done
      also have "... = `ok \<and> ok' \<and> $wait \<and> $wait\<acute> \<and> II`"
        by (smt AndP_assoc AndP_comm Aidb Aidc)
      finally have "`(ok \<and> $wait \<and> II);R3(Q)` = `(ok \<and> ok' \<and> $wait \<and> $wait\<acute> \<and> II);R3(Q)`" 
        by metis
      also have "... = `(ok \<and> $wait \<and> II);(ok \<and> $wait \<and> R3(Q))`" 
        apply(subst SemiR_AndP_right_precond)
        apply (metis AndP_rel_closure MkPlainP_UNDASHED PUNDASHED_WF_CONDITION SkipR_closure WF_CONDITION_WF_RELATION)
        apply (metis AndP_rel_closure MkPlainP_UNDASHED PUNDASHED_WF_CONDITION WF_CONDITION_WF_RELATION assms(2) assms(4) is_healthy_def)
        apply (metis MkPlainP_UNDASHED PUNDASHED_WF_CONDITION)
        apply(subst SemiR_AndP_right_precond)
        apply (smt AndP_rel_closure ConvR_rel_closure MkPlainP_UNDASHED PUNDASHED_WF_CONDITION SkipR_closure WF_CONDITION_WF_RELATION)
        apply (metis R3_rel_closure assms(2))
        apply (metis MkPlainP_UNDASHED PUNDASHED_WF_CONDITION)
        apply (metis a)
        done
      also have "... = `(ok \<and> $wait \<and> II);(ok \<and> $wait \<and> II)`"
        proof -
          have "`ok \<and> $wait \<and> R3(Q)` = `ok \<and> $wait \<and> II`" 
            apply(simp add:R3_form) 
            apply(utp_pred_auto_tac) 
            done
          thus ?thesis 
            by metis
        qed
      also have "... = `(ok \<and> ok' \<and> $wait \<and> $wait\<acute> \<and> II);II`"
        apply(subst SemiR_AndP_right_precond)
        apply (metis AndP_rel_closure MkPlainP_UNDASHED PUNDASHED_WF_CONDITION SkipR_closure WF_CONDITION_WF_RELATION)
        apply (metis (full_types) AndP_rel_closure MkPlainP_UNDASHED PUNDASHED_WF_CONDITION SkipR_closure WF_CONDITION_WF_RELATION)
        apply (metis MkPlainP_UNDASHED PUNDASHED_WF_CONDITION)
        apply(subst SemiR_AndP_right_precond)
        apply (smt AndP_rel_closure ConvR_rel_closure MkPlainP_UNDASHED PUNDASHED_WF_CONDITION SkipR_closure WF_CONDITION_WF_RELATION)
        apply (metis SkipR_closure)
        apply (metis MkPlainP_UNDASHED PUNDASHED_WF_CONDITION)
        apply (metis a)
        done
      also have "... = `ok \<and> ok' \<and> $wait \<and> $wait\<acute> \<and> II`"by (metis SemiR_SkipR_right)
      also have "... = `ok \<and> $wait \<and> II`"
      proof -
        have "`ok \<and> ok' \<and> $wait \<and> $wait\<acute> \<and> II` =  `ok \<and> $wait \<and> ($okay\<acute> = $okay) \<and> ($wait\<acute> = $wait) \<and> II`"
          by (smt AndP_assoc AndP_comm Aidb Aidc)
        also have "... = `ok \<and> $wait \<and> II`"
          apply (simp add:SkipR_as_SkipRA)
          apply (subst SkipRA_unfold[of "okay \<down>"])
          apply(simp_all)
          apply (metis MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED)
          apply(utp_pred_auto_tac)
          apply (metis MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED)
          apply (subst SkipRA_unfold[of "okay \<down>"]) back
          apply(simp_all)
          apply (metis MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED)
          apply(utp_pred_auto_tac)
          apply (metis MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED)
          apply (subst SkipRA_unfold[of "wait \<down>"])
          apply(simp_all)
          apply (metis MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED)
          apply(utp_pred_auto_tac)
          apply (metis MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED)
          apply(utp_pred_auto_tac)
          apply (subst SkipRA_unfold[of "wait \<down>"]) back
          apply(simp_all)
          apply (metis MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED)
          apply(utp_pred_auto_tac)
          apply (metis MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED)
          apply(utp_pred_auto_tac)
          apply(simp add:erasure typing defined closure)
          apply (smt AndP_assoc AndP_idem)
          done
        finally show ?thesis
          ..
      qed
      finally show ?thesis 
        by (metis assms(4) is_healthy_def)
    qed
  have 3: "`(\<not> $wait \<and> P);Q` = `\<not> $wait \<and> (P;Q)`"
    by(subst SemiR_AndP_left_precond, simp_all add:assms, utp_pred_auto_tac)
  have "`P ; Q` = `R3(P) ; Q`" 
    by (metis assms(3) is_healthy_def)
  also have "... = `(\<not>ok \<and> $wait \<and> ($tr \<le> $tr\<acute>));Q  \<or> (ok \<and> $wait \<and> II);Q \<or> (\<not> $wait \<and> P);Q`" 
    by(simp add:R3_form SemiR_OrP_distr)
  also have "... = `(\<not>ok \<and> $wait \<and> ($tr \<le> $tr\<acute>))  \<or> (ok \<and> $wait \<and> II) \<or> (\<not> $wait \<and> (P;Q))`"
    by (metis "1" "2" "3") 
  finally show ?thesis 
    by (simp add:R3_form is_healthy_def)
qed

(* L8 R3-idempotent *)

lemma R3_idempotent: "`R3(R3(P))` = `R3(P)`" 
  by (utp_pred_auto_tac)

(* L9 commutativity-R3-H2 *)

lemma H2_R3_commute: 
  assumes "P \<in> WF_RELATION"
  shows "H2 (R3 P) = R3 (H2 P)" 
  apply(simp add:R3_def CondR_def H2_def SemiR_OrP_distr)
  apply(subst SemiR_AndP_left_precond[of _ _ "`$wait`"])
  apply(simp_all add:SkipREA_rel_closure J_closure MkPlainP_UNDASHED PUNDASHED_WF_CONDITION)
  apply(subst SemiR_AndP_left_precond[of _ _ "`\<not>$wait`"])
  apply(simp_all add:assms J_closure MkPlainP_UNDASHED NotP_cond_closure PUNDASHED_WF_CONDITION) 
  apply (metis H2_SkipREA H2_def)
  done

(* L10 commutativity-R3-R1 *)

lemma R1_R3_commute: "R1 (R3 P) = R3 (R1 P)" 
proof - 
  have "R1 (R3 P) = `(II\<^bsub>rea\<^esub> \<lhd> $wait \<rhd> P) \<and> ($tr \<le> $tr\<acute>)`" 
    by utp_rel_tac
  also have "... = `(II\<^bsub>rea\<^esub> \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait \<rhd> (P \<and> ($tr \<le> $tr\<acute>))`" 
    by utp_pred_auto_tac
  also have "... = `II\<^bsub>rea\<^esub> \<lhd> $wait \<rhd> (P \<and> ($tr \<le> $tr\<acute>))`" 
    by (metis R1_def SkipREA_is_R1)
  ultimately show ?thesis by utp_pred_auto_tac
qed

(* L11 commutativite-R3-R2 *)

theorem R2_R3_commute: 
  "R2 (R3 P) = R3 (R2 P)" 
proof - 
  have "R2 (R3 P) = `R2(II\<^bsub>rea\<^esub>) \<lhd> R2s($wait) \<rhd> R2(P)`" 
    by (simp add:R3_def R2_CondR)
  also have "... = `II\<^bsub>rea\<^esub> \<lhd> $wait \<rhd> R2(P)`"
    by (simp add: SkipREA_is_R2 R2s_def usubst typing defined closure)
  finally show ?thesis 
    by (simp add: R3_def R2_def)
qed

(* L12 R3-H1-sub-commutativity *)

lemma R3_H1_sub_commute: 
  "H1 (R3 P) = H1 (R3 (H1 P))"
by(utp_pred_auto_tac)

(* L13 R3-H1-R1-sub-commutativity *)

lemma R3_H1_R1_sub_commute: 
  "R3 (R1 (H1 P)) = R1 (H1 (R3 P))"
proof -
  have "R3 (R1 (H1 P)) = `($wait \<and> II\<^bsub>rea\<^esub>) \<or> (\<not>$wait \<and> ($tr\<le>$tr\<acute>) \<and> \<not>ok) \<or> (\<not>$wait \<and> ($tr\<le>$tr\<acute>) \<and> P)`" 
    by utp_pred_auto_tac
  also have "... = `($wait \<and> II\<^bsub>rea\<^esub> \<and> ($tr\<le>$tr\<acute>)) \<or> (\<not>$wait \<and> ($tr\<le>$tr\<acute>) \<and> \<not>ok) \<or> (\<not>$wait \<and> ($tr\<le>$tr\<acute>) \<and> P)`"
    proof -
      have "`II\<^bsub>rea\<^esub>` = `II\<^bsub>rea\<^esub> \<and> ($tr\<le>$tr\<acute>)` "
        by (metis R1_def SkipREA_is_R1)
      thus ?thesis 
        by metis
    qed
  finally show ?thesis 
    by utp_pred_auto_tac
qed

(* Additional Lemmas *)

lemma R3_SkipREA: "`R3(II\<^bsub>rea\<^esub>)` = `II\<^bsub>rea\<^esub>`"
  by (simp add:R3_def CondR_idem)

lemma R3_monotonic: "P \<sqsubseteq> Q \<Longrightarrow> R3(P) \<sqsubseteq> R3(Q)" 
  by utp_pred_tac

subsection {* RH Laws *}

lemma RH_is_R1:
  "P is RH \<Longrightarrow> P is R1"
  by (metis Healthy_intro Healthy_simp R1_idempotent RH_def comp_apply)

lemma RH_is_R2:
  "P is RH \<Longrightarrow> P is R2"
  by (metis Healthy_intro Healthy_simp R1_idempotent R2_R3_commute R2_def R3_idempotent RH_def comp_apply)

lemma RH_is_R3:
  "P is RH \<Longrightarrow> P is R3"
  by (metis Healthy_intro Healthy_simp R1_R3_commute R1_idempotent R2_R3_commute R2_def R3_idempotent RH_def o_eq_dest_lhs)

lemma R_intro: "\<lbrakk> P is R1; P is R2; P is R3 \<rbrakk> \<Longrightarrow> P is RH"
  by (metis RH_def comp_apply is_healthy_def)

(* L1 reactive-left-zero *)

lemma R1_true_left_zero: 
  assumes "P is R1" "P is R3" "P \<in> WF_RELATION"
  shows "`($tr \<le> $tr\<acute>) ; P` = `($tr \<le> $tr\<acute>)`"
proof -
  have 1: "`(($tr \<le> $tr\<acute>) ; (\<not>ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)))`=`($tr \<le> $tr\<acute>)`"
    by (metis (hide_lams, no_types) Aida AndP_assoc)
  have 2: "`(($tr \<le> $tr\<acute>);(ok \<and> $wait \<and> II))` is R1" 
    apply(subst R1_SemiR_closure)
    apply(simp_all)
    apply (metis R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
    apply (metis AndP_rel_closure MkPlainP_UNDASHED PUNDASHED_WF_CONDITION SkipR_closure WF_CONDITION_WF_RELATION)
    apply (metis R1_by_refinement order_refl)
    apply (metis (full_types) AndP_comm Healthy_intro R1_SkipR R1_extend_AndP)
    done
  have 3: "`(($tr \<le> $tr\<acute>);(\<not>$wait \<and> P))` is R1"
    apply(subst R1_SemiR_closure)
    apply(simp_all)
    apply (metis R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
    apply (metis AndP_rel_closure MkPlainP_UNDASHED NotP_rel_closure PUNDASHED_WF_CONDITION WF_CONDITION_WF_RELATION assms(3))
    apply (metis R1_by_refinement order_refl)  
    apply (metis (full_types) AndP_comm R1_extend_AndP RH_is_R1 assms(1) is_healthy_def)
    done
  have "`($tr \<le> $tr\<acute>) ; P` = `($tr \<le> $tr\<acute>) ; R3(P)`"
    by (metis Healthy_simp RH_is_R3 assms)
  also have "... = `(($tr \<le> $tr\<acute>) ; (\<not>ok \<and> $wait \<and> ($tr \<le> $tr\<acute>))) \<or> (($tr \<le> $tr\<acute>);(ok \<and> $wait \<and> II)) \<or> (($tr \<le> $tr\<acute>);(\<not>$wait \<and> P))`"
    by(simp add:R3_form SemiR_OrP_distl)
  also have "... = `($tr \<le> $tr\<acute>) \<or> R1(($tr \<le> $tr\<acute>);(ok \<and> $wait \<and> II)) \<or> R1(($tr \<le> $tr\<acute>);(\<not>$wait \<and> P))`"
    by(metis 1 2 3 is_healthy_def)
  also have "... = `($tr \<le> $tr\<acute>)`"
    by(utp_pred_auto_tac)
  finally show ?thesis 
    ..
qed

(* L2 restricted-identity *)

lemma SkipREA_restricted_identity:
  assumes "P is RH" "P \<in> WF_RELATION"
  shows " `II\<^bsub>rea\<^esub>; P` = `P \<lhd> ok \<rhd> ($tr \<le> $tr\<acute>)`"
  apply (simp add:SkipREA_CondR_SkipR CondR_def SemiR_OrP_distr)
  apply (subst SemiR_AndP_left_precond[of _ _ "`ok`"])
  apply (simp_all add:SkipR_closure assms(2) MkPlainP_UNDASHED PUNDASHED_WF_CONDITION)
  apply (subst SemiR_AndP_left_precond[of _ _ "`\<not>ok`"])
  apply (simp_all add:assms(2))
  apply (metis R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
  apply (metis TopD_cond_closure TopD_def)
  apply (subst R1_true_left_zero)
  apply (simp_all add:assms)
  apply (metis RH_is_R1 assms(1))
  apply (metis RH_is_R3 assms(1))
  done

(* L3 R-wait-false *)

lemma RH_wait_false: 
  "`(RH(P))\<^sub>f` = `R1(R2(P\<^sub>f))`"
by(simp add:RH_def R1_wait_false R2_wait_false R3_wait_false)

(* L4 R-wait-true *)

lemma RH_wait_true: 
  "`(RH(P))\<^sub>t` = `II\<^bsub>rea\<^esub>\<^sub>t`"
proof -
  have 1: "`II\<^bsub>rea\<^esub>\<^sub>t` = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok' \<and> $wait\<acute> \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>}\<^esub>)`"
    apply(simp add:SkipREA_def usubst typing defined closure)
    apply (metis (hide_lams, no_types) Aidd PVAR_VAR_pvdash)
    done
  have "`(RH(P))\<^sub>t` = R1 (R2 `II\<^bsub>rea\<^esub>\<^sub>t`)"
    by(simp add: RH_def R1_wait_true R2_wait_true R3_wait_true)
  also from 1 have "... = R1 (R2 `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok' \<and> $wait\<acute> \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>}\<^esub>)`)"
    by(metis)
  also have "... = `R1 (\<not>ok) \<or> R1 (ok' \<and> $wait\<acute> \<and> (($tr\<acute> - $tr) = \<langle>\<rangle>) \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>}\<^esub>)`" 
    apply(simp add: R2_def R1_idempotent)
    apply(subst SkipRA_unfold[of "tr \<down>"])
    apply(simp_all)
    apply (metis MkPlain_UNDASHED PVAR_VAR_MkPVAR)
    apply (metis MkPlain_UNDASHED PVAR_VAR_MkPVAR UNDASHED_dash_DASHED)
    apply (metis MkPlain_UNDASHED PVAR_VAR_MkPVAR)
    apply (smt HOMOGENEOUS_REL_VAR HOMOGENEOUS_empty HOMOGENEOUS_insert HOMOGENEOUS_minus MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED)
    apply(simp add:R2s_def usubst typing defined closure R1_OrP)
    done
  also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok' \<and> $wait\<acute> \<and> R1(($tr\<acute> - $tr) = \<langle>\<rangle>) \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>}\<^esub>)`"
    by(utp_pred_auto_tac)
  also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok' \<and> $wait\<acute> \<and> ($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>}\<^esub>)`"
    by (smt R1_def tr_prefix_as_nil)
  also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok' \<and> $wait\<acute> \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>}\<^esub>)`"
    apply(subst SkipRA_unfold[of "tr \<down>"]) back
    apply(simp_all)
    apply (metis MkPlain_UNDASHED PVAR_VAR_MkPVAR)
    apply (metis MkPlain_UNDASHED PVAR_VAR_MkPVAR UNDASHED_dash_DASHED)
    apply (metis MkPlain_UNDASHED PVAR_VAR_MkPVAR)
    apply (smt HOMOGENEOUS_REL_VAR HOMOGENEOUS_empty HOMOGENEOUS_insert HOMOGENEOUS_minus MkPlainP_UNDASHED PVAR_VAR_PUNDASHED_UNDASHED)
    apply(simp add:erasure typing closure defined)
    done
  also from 1 have "... = `II\<^bsub>rea\<^esub>\<^sub>t`" 
    by metis
  finally show ?thesis
    ..
qed

(* L5 R-okay' *)

lemma RH_okay'_true: 
  "(RH(P))\<^sup>t = `II\<^bsub>rea\<^esub>\<^sup>t \<lhd> $wait \<rhd>R1(R2(P\<^sup>t))`"
proof-
  have "(R1(R2(P)))\<^sup>t = R1(R2(P\<^sup>t))" 
    by (metis R1_okay'_true R2_okay'_true)
  hence "(R3(R1(R2(P))))\<^sup>t = `II\<^bsub>rea\<^esub>\<^sup>t \<lhd> $wait \<rhd>R1(R2(P\<^sup>t))`" 
    by (smt R3_okay'_true)
  thus ?thesis 
    by(simp add:RH_def R2_R3_commute R1_R3_commute)
qed

lemma RH_okay'_false: 
  "(RH(P))\<^sup>f = `II\<^bsub>rea\<^esub>\<^sup>f \<lhd> $wait \<rhd>R1(R2(P\<^sup>f))`"
proof-
  have "(R1(R2(P)))\<^sup>f = R1(R2(P\<^sup>f))" 
    by (metis R1_okay'_false R2_okay'_false)
  hence "(R3(R1(R2(P))))\<^sup>f = `II\<^bsub>rea\<^esub>\<^sup>f \<lhd> $wait \<rhd>R1(R2(P\<^sup>f))`" 
    by (smt R3_okay'_false)
  thus ?thesis 
    by(simp add:RH_def R2_R3_commute R1_R3_commute)
qed

(* L6 closure-\<and>-R *)

lemma RH_AndP_closure:
  assumes "P is RH" "Q is RH"
  shows "`P \<and> Q` is RH"
proof -
  have "`R3(P \<and> Q)` = `P \<and> Q`" 
    by (metis Healthy_simp R3_AndP RH_is_R3 assms(1) assms(2))
  hence "`R2(R3(P \<and> Q))` = `P \<and> Q`" 
    by (metis R2_AndP RH_is_R2 assms(1) assms(2) is_healthy_def)
  hence "`R1(R2(R3(P \<and> Q)))` = `P \<and> Q`" 
    by (metis R1_idempotent R2_def)
  thus ?thesis 
    by(simp add:is_healthy_def RH_def)
qed

(* L7 closure-\<or>-R *)

lemma RH_OrP_closure:
  assumes "P is RH" "Q is RH"
  shows "`P \<or> Q` is RH"
proof -
  have "`R3(P \<or> Q)` = `P \<or> Q`" 
    by (metis Healthy_simp R3_OrP RH_is_R3 assms(1) assms(2))
  hence "`R2(R3(P \<or> Q))` = `P \<or> Q`" 
    by (metis R2_OrP RH_is_R2 assms(1) assms(2) is_healthy_def)
  hence "`R1(R2(R3(P \<or> Q)))` = `P \<or> Q`" 
    by (metis R1_idempotent R2_def)
  thus ?thesis 
    by(simp add:is_healthy_def RH_def)
qed

(* L8 closure-cond-R *)

lemma RH_CondR_closure:
  assumes "P is RH" "Q is RH" "b is R2s"
  shows "`P \<lhd> b \<rhd> Q` is RH"
proof -
  have "`R3(P \<lhd> b \<rhd> Q)` = `P \<lhd> b \<rhd> Q`" by (metis Healthy_simp R3_CondR RH_is_R3 assms(1) assms(2))
  hence "`R2(R3(P \<lhd> b \<rhd> Q))` = `P \<lhd> b \<rhd> Q`" by (metis R2_CondR RH_is_R2 assms(1) assms(2) assms(3) is_healthy_def)
  hence "`R1(R2(R3(P \<lhd> b \<rhd> Q)))` = `P \<lhd> b \<rhd> Q`" by (metis R1_idempotent R2_def)
  thus ?thesis by(simp add:is_healthy_def RH_def)
qed

(* L9 closure-sequence-R *)

lemma RH_SemiR_closure:
  assumes "P \<in> WF_RELATION" "Q\<in> WF_RELATION" "P is RH" "Q is RH"
  shows "`P ; Q` is RH"
proof -
  have "`R3(P ; Q)` = `P ; Q`"
    by (metis Healthy_simp R3_SemiR_closure RH_is_R1 RH_is_R3 assms(1) assms(2) assms(3) assms(4))
  hence "`R2(R3(P ; Q))` = `P ; Q`" 
    by (metis R2_SemiR_closure RH_is_R2 assms is_healthy_def)
  hence "`R1(R2(R3(P ; Q)))` = `P ; Q`" 
    by (metis R1_idempotent R2_def)
  thus ?thesis by(simp add:is_healthy_def RH_def)
qed

lemma RH_form: 
  assumes "P \<in> WF_RELATION" "P is RH"
  shows "P = `(\<not>ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (\<not>$wait \<and> R2(P\<^sub>f))`"
proof-
  have "P = RH P" by(metis is_healthy_def assms(2))
  thus ?thesis
  apply(simp add:RH_def R2_R3_commute R1_R3_commute)
  apply(simp add:R3_form_2 R1_def)
  apply(simp add:usubst typing defined closure)
  apply(simp add:R2_wait_false)
  apply(simp add:R2_def R1_def)
  apply (metis (hide_lams, no_types) R1_def R1_idempotent)
  done
qed

subsection {* The theory of Reactive Processes *}

lift_definition REACTIVE :: "'VALUE WF_THEORY" 
is "({vs. vs \<subseteq> REL_VAR \<and> REA \<subseteq> vs}, {R1,R2,R3})"
  by (simp add:WF_THEORY_def IDEMPOTENT_OVER_def R1_idempotent R2_idempotent R3_idempotent)
      
end