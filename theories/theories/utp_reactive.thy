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
abbreviation "ref  \<equiv> MkPlainP ''ref'' True TYPE('m EVENT USET) TYPE('m)"

abbreviation "TR \<equiv> {tr\<down>, tr\<down>\<acute>}"
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
  apply (simp_all)
  apply (simp add:tr_leq_trans)
done

lemma R1_tr_leq_tr':
  "`R1($tr \<le> $tr\<acute>)` = `$tr \<le> $tr\<acute>`"
  by (simp add:R1_def)

lemma R1_H2_commute:
  "P \<in> WF_RELATION \<Longrightarrow> H2(R1(P)) = R1(H2(P))"
  apply (simp add: H2_def J_split unrest closure)
  apply (simp add: R1_def usubst typing defined)
  apply (utp_pred_auto_tac)
done

lemma SkipRA_is_R1 : 
  "`R1(II\<^bsub>REL_VAR - OKAY\<^esub>)` = `II\<^bsub>REL_VAR - OKAY\<^esub>`"
  by (auto simp add:var_dist closure eval)

lemma DestList_tr_dcarrier [typing]: 
  "set (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>)) \<subseteq> dcarrier EventType"
  apply (rule DestList_elem_type)
  apply (simp add:closure)
  apply (auto intro:typing)[1]
done

lemma DestList_tr'_dcarrier [typing]: 
  "set (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>\<acute>)) \<subseteq> dcarrier EventType"
  apply (rule DestList_elem_type)
  apply (simp add:closure)
  apply (auto intro:typing)[1]
done

lemma prefix_Cons_elim [elim]:
  assumes "prefix (x # xs) ys"
  obtains ys' where "ys = x # ys'" "prefix xs ys'"
  using assms 
  apply (auto elim!: prefixE)
  apply (metis (full_types) prefix_order.le_less prefixeq_Cons_elim)
done

lemma prefix_map_inj:
  "\<lbrakk> inj_on f (set xs \<union> set ys); prefix (map f xs) (map f ys) \<rbrakk> \<Longrightarrow>
   prefix xs ys"
  apply (induct xs arbitrary:ys)
  apply (auto)
  apply (metis map.simps(1) prefix_bot.bot_less)
  apply (erule prefix_Cons_elim)
  apply (auto)
  apply (metis (hide_lams, full_types) image_insert insertI1 insert_Diff_if singletonE)
done

lemma prefix_map_inj_eq [simp]:
  "inj_on f (set xs \<union> set ys) \<Longrightarrow>
   prefix (map f xs) (map f ys) \<longleftrightarrow> prefix xs ys"
  by (metis inj_on_map_eq_map map_prefixeqI prefix_map_inj prefix_order.less_le)

lemma prefix_DestEvent_simp [simp]:
  "prefix (map DestEvent (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>))) (map DestEvent (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>\<acute>)))
  = prefix (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>)) (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>\<acute>))"
  apply (subgoal_tac "inj_on DestEvent (set (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>)) \<union> set (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>\<acute>)))")
  apply (simp)
  apply (rule subset_inj_on[of _ "dcarrier EventType"])
  apply (simp)
  apply (metis DestList_tr'_dcarrier DestList_tr_dcarrier le_sup_iff)
done

lemma prefixeq_DestEvent_simp [simp]:
  "prefixeq (map DestEvent (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>))) (map DestEvent (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>\<acute>)))
  = prefixeq (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>)) (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>\<acute>))"
  apply (subgoal_tac "inj_on DestEvent (set (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>)) \<union> set (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>\<acute>)))")
  apply (simp)
  apply (rule subset_inj_on[of _ "dcarrier EventType"])
  apply (simp)
  apply (metis DestList_tr'_dcarrier DestList_tr_dcarrier le_sup_iff)
done

lemma tr_prefix_as_nil:
  "`($tr\<acute> - $tr) = \<langle>\<rangle> \<and> ($tr \<le> $tr\<acute>)` = `$tr = $tr\<acute>`"
  apply (utp_pred_auto_tac)
  apply (subgoal_tac "set (drop (length (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>))) (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>\<acute>))) \<subseteq> dcarrier (EventType :: 'a UTYPE)")
  defer
  apply (rule subset_trans, rule set_drop_subset, rule DestList_tr'_dcarrier)
  apply (simp add:MkList_inj_simp typing closure)
  apply (metis (full_types) le_antisym prefix_length_eq prefixeq_length_le)
done

lemma tr_prefix_app:
  "`($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> ($tr \<le> $tr\<acute>)` = `($tr ^ \<langle>a\<rangle> = $tr\<acute>)`"
  apply (utp_pred_auto_tac)
  apply (metis prefixeq_def)
done

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

lemma tr_conserved_is_R1 : "`R1($tr = $tr\<acute>)` = `($tr = $tr\<acute>)`" 
  by (simp add:R1_def, utp_pred_auto_tac)

lemma tr_conserved_is_R2 : "`R2($tr = $tr\<acute>)` = `($tr = $tr\<acute>)`"
  apply(simp add:R2_def R2s_def R1_def usubst typing defined closure)
  apply (metis EqualP_sym tr_prefix_as_nil)
done

lemma R3_wait: "`R3(P) \<and> $wait` = `II\<^bsub>rea\<^esub> \<and> $wait`"
  apply (simp add:R3_def)
  apply (subst AndP_comm)
  apply (subst CondR_true_cond)
  apply (subst AndP_comm)
  apply (rule refl)
done

lemma R2s_idempotent: "`R2s(R2s(P))` = `R2s(P)`"
  apply (simp add:R2s_def)
  apply (subst SubstP_twice_3) back
  apply (simp_all add:typing defined closure unrest)
  apply (simp add:usubst typing defined closure)
done

lemma R2s_wait: "`R2s($wait)` = `$wait`" 
  by (simp add:R2s_def usubst closure typing defined)

lemma R2s_destroys_R1: "R2s (R1 P) = R2s P" 
  by (simp add:R2s_def R1_def usubst closure typing defined, utp_pred_auto_tac)

lemma R2s_distributes_through_conjunction: 
  "`R2s(P \<and> Q)` = `R2s(P) \<and> R2s(Q)`" 
  by (utp_pred_auto_tac)

lemma R2s_CondR: 
  "`R2s(P \<lhd> b \<rhd> Q)` = `R2s(P) \<lhd> R2s(b) \<rhd> R2s(Q)`"
  by (utp_pred_auto_tac)

lemma R2_idempotent: "`R2(R2(P))` = `R2(P)`" 
  by (simp add:R2_def R2s_destroys_R1 R2s_idempotent)

lemma R2_CondR: 
  "`R2(P \<lhd> b \<rhd> Q)` =`R2(P) \<lhd> R2s(b) \<rhd> R2(Q)`" 
  by (utp_pred_auto_tac)

lemma R2_CondR_alt: 
  "`R2(P \<lhd> b \<rhd> Q)` =`R2(P) \<lhd> R2(b) \<rhd> R2(Q)`" 
  by (utp_pred_auto_tac)

lemma R2s_OrP: 
  "`R2s(A \<or> C)` = `R2s(A) \<or> R2s(C)`" 
  by (utp_pred_auto_tac)

lemma R1_not_ok: "`R1(\<not> ok)` = `(\<not> ok \<and> ($tr \<le> $tr\<acute>))`" 
  by (simp add:R1_def)

lemma R2s_not_ok: "`R2s(\<not> ok)` = `\<not> ok`" 
  by (simp add:R2s_def usubst typing defined closure) 

lemma R2_not_ok: "`R2(\<not> ok)` = `R1(\<not> ok)`"
  by (simp add:R2_def usubst typing defined closure R2s_not_ok) 

lemma R2_AndP: "`R2(P \<and> Q)` = `R2(P) \<and> R2(Q)`"
  by (utp_pred_auto_tac)

lemma R2_OrP: "`R2(P \<or> Q)` = `R2(P) \<or> R2(Q)`"
  by (utp_pred_auto_tac)

lemma R3_AndP: "`R3(P \<and> Q)` = `R3(P) \<and> R3(Q)`"
  by (utp_pred_auto_tac)

lemma R3_OrP:
  "`R3(P \<or> Q)` = `R3(P) \<or> R3(Q)`"
  by (utp_pred_auto_tac)

lemma R3_CondR:
  "`R3(P \<lhd> b \<rhd> Q)` = `R3(P) \<lhd> R3(b) \<rhd> R3(Q)`"
  by (utp_pred_auto_tac)

lemma R3_idempotent: "`R3(R3(P))` = `R3(P)`" 
  by (utp_pred_auto_tac)

lemma R1_monotonic: "P \<sqsubseteq> Q \<Longrightarrow> R1(P) \<sqsubseteq> R1(Q)" 
  by utp_pred_tac

lemma R2_monotonic: "P \<sqsubseteq> Q \<Longrightarrow> R2(P) \<sqsubseteq> R2(Q)" 
  by utp_pred_tac

lemma R3_monotonic: "P \<sqsubseteq> Q \<Longrightarrow> R3(P) \<sqsubseteq> R3(Q)" 
  by utp_pred_tac

lemma R1_R2_commute: "R1 (R2 P) = R2 (R1 P)" 
  by (simp add:R2_def R1_idempotent R2s_destroys_R1)

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

theorem R2_R3_commute: 
  "R2 (R3 P) = R3 (R2 P)" 
proof - 
  have "R2 (R3 P) = `R2(II\<^bsub>rea\<^esub>) \<lhd> R2s($wait) \<rhd> R2(P)`" 
    by (simp add:R3_def R2_CondR)
  also have "... = `II\<^bsub>rea\<^esub> \<lhd> $wait \<rhd> R2(P)`" 
    by (simp add: SkipREA_is_R2 R2s_wait)
  finally show ?thesis 
    by (simp add: R3_def R2_def)
qed

lemma helper1 : "`$wait \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub>` = `$wait \<and> $wait\<acute> \<and> II\<^bsub>REL_VAR - {okay\<down>, okay\<down>\<acute>}\<^esub>`"
  by (auto simp add:var_dist closure evalr evale)

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

(*
lemma helper2: "`($wait\<acute> \<and> Q) ; R3(P)` = `$wait\<acute> \<and> Q`" sorry
lemma helper4 : "`\<langle>\<rangle> = ($tr\<acute> - $tr)` =`$tr\<acute> = $tr`" sorry
lemma wait_then_P_equals_wait : "`(($wait \<and> II\<^bsub>rea\<^esub>) \<and> ($tr \<le> $tr\<acute>)) ; P` = `(($wait \<and> II\<^bsub>rea\<^esub>) \<and> ($tr \<le> $tr\<acute>))`" sorry
lemma R2s_R3_commute : "R2s (R3 P) = R3 (R2s P)" sorry
lemma Assist : "`P[false/okay\<acute>] \<or> P[true/okay\<acute>]` = `P`"sorry
lemma Assist7 : "`(($tr < $tr\<acute>) \<and> ($tr^\<langle>a\<rangle> =$tr\<acute>))` = `($tr^\<langle>a\<rangle> =$tr\<acute>)`" sorry

lemma conj_distributes_through_conditional : "`(P \<lhd> b \<rhd> Q) \<and> S` = `(P \<and> S)\<lhd> b \<rhd>(Q \<and> S)`"by utp_pred_auto_tac
lemma R2s_distributes_through_conjunction : "`R2s(P \<and> Q)` = `R2s(P) \<and> R2s(Q)`" by utp_pred_auto_tac
lemma R2s_distributes_through_conditional : "`R2s(P \<lhd> b \<rhd> Q)` = `R2s(P)\<lhd> R2s(b) \<rhd>R2s(Q)`"by utp_pred_auto_tac
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
lemma aider3 : "`$okay\<acute> \<and> II\<^bsub>rea\<^esub>[true/okay\<acute>]` = `$okay\<acute> \<and> II\<^bsub>rea\<^esub>`"by(simp add:SkipREA_def usubst typing defined closure, utp_pred_auto_tac)
*)

subsection {* The theory of Reactive Processes *}

lift_definition REACTIVE :: "'VALUE WF_THEORY" 
is "({vs. vs \<subseteq> REL_VAR \<and> REA \<subseteq> vs}, {R1,R2,R3})"
  by (simp add:WF_THEORY_def IDEMPOTENT_OVER_def R1_idempotent R2_idempotent R3_idempotent)

end