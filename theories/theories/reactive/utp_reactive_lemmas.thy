(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_reactive_lemmas.thy                                              *)
(* Authors: Simon Foster, University of York                                  *)
(******************************************************************************)

header {* Lemmas for the theory of reactive processes *}

theory utp_reactive_lemmas
imports 
  "../utp_designs"
  "../utp_theory"
begin

default_sort REACTIVE_SORT

abbreviation "tr   \<equiv> MkPlainP ''tr'' True TYPE('m EVENT ULIST) TYPE('m)"

abbreviation "TR \<equiv> {tr\<down>, tr\<down>\<acute>}"

lemma tr_leq_trans:
  "`($tr \<le> $tr\<acute>) ; ($tr \<le> $tr\<acute>)` = `($tr \<le> $tr\<acute>)`"
  by (auto intro: binding_equiv_trans simp add:closure typing defined unrest closure evalr evalp relcomp_unfold urename)

lemma nil_prefixeq [simp]:
  "`\<langle>\<rangle> \<le> x` = `true`"
  by (utp_pred_auto_tac)

lemma nil_append [simp]:
  "|\<langle>\<rangle> ^ x| = |x|"
  by (auto simp add:evalp)

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

end