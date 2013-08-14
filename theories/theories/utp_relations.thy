(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_relations.thy                                                    *)
(* Authors: Simon Foster, University of York                                  *)
(******************************************************************************)

header {* UTP Theory of Relations *}

theory utp_relations
imports 
  utp_base
begin

subsection {* Relational Healthiness Condition *}

definition RELH :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"RELH(P) = (\<exists>\<^sub>p NON_REL_VAR. P)"

declare RELH_def [eval,evalr,evalrx]

lemma RELH_idem:
  "RELH (RELH P) = RELH P"
  by (simp add:RELH_def eval)

lemma RELH_mono:
  "p \<sqsubseteq> q \<Longrightarrow> RELH p \<sqsubseteq> RELH q"
  by (utp_pred_auto_tac)

lemma RELH_WF_RELATION [closure]:
  "RELH P \<in> WF_RELATION"
  by (simp add:RELH_def WF_RELATION_def unrest)

lemma RELH_iff_WF_RELATION:
  "P = RELH P \<longleftrightarrow> P \<in> WF_RELATION"
  apply (rule)
  apply (simp_all add:RELH_def WF_RELATION_def unrest)
  apply (metis (full_types) UNREST_ExistsP_simple subset_refl)
  apply (utp_pred_tac)
done

end