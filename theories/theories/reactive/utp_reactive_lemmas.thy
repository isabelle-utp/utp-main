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

abbreviation "wait \<equiv> MkPlainP ''wait'' True TYPE(bool) TYPE('m)"
abbreviation "tr   \<equiv> MkPlainP ''tr'' True TYPE('m EVENT ULIST) TYPE('m)"

abbreviation "TR \<equiv> {tr\<down>, tr\<down>\<acute>}"
abbreviation "WAIT \<equiv> {wait\<down>, wait\<down>\<acute>}"

abbreviation wait_true :: 
  "'VALUE WF_PREDICATE \<Rightarrow> 'VALUE WF_PREDICATE" ("_\<^sub>t"[150]) where
"p\<^sub>t \<equiv> `p[true/wait]`"

abbreviation wait_false :: 
  "'VALUE WF_PREDICATE \<Rightarrow> 'VALUE WF_PREDICATE" ("_\<^sub>f"[150]) where
"p\<^sub>f \<equiv> `p[false/wait]`"

syntax
  "_upred_wait_true"    :: "upred \<Rightarrow> upred" ("_\<^sub>t" [1000] 1000)
  "_upred_wait_false"   :: "upred \<Rightarrow> upred" ("_\<^sub>f" [1000] 1000)

translations
  "_upred_wait_true p"  == "CONST wait_true p"
  "_upred_wait_false p" == "CONST wait_false p"

lemma ok_wait_commute_t_t: 
  "`P\<^sup>t\<^sub>t` = `P\<^sub>t\<^sup>t`"
  apply (subst SubstP_twice_3)
  apply (simp_all add: typing defined unrest)
  apply (simp add:usubst typing defined)
done

lemma ok_wait_commute_f_f: 
  "`P\<^sup>f\<^sub>f` = `P\<^sub>f\<^sup>f`"
  apply (subst SubstP_twice_3)
  apply (simp_all add: typing defined unrest)
  apply (simp add:usubst typing defined)
done

lemma ok_wait_commute_t_f: 
  "`P\<^sup>t\<^sub>f` = `P\<^sub>f\<^sup>t`"
  apply (subst SubstP_twice_3)
  apply (simp_all add: typing defined unrest)
  apply (simp add:usubst typing defined)
done

lemma ok_wait_commute_f_t: 
  "`P\<^sup>f\<^sub>t` = `P\<^sub>t\<^sup>f`"
  apply (subst SubstP_twice_3)
  apply (simp_all add:typing defined unrest)
  apply (simp add:usubst typing defined)
done

lemma tr_eq_rel_closure: 
  "`($tr\<acute> = $tr)` \<in> WF_RELATION"
 by (simp add:closure unrest typing)

lemma var_eq_trans:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR"
  assumes "TYPEUSOUND('a, 'm)" "x \<in> PUNDASHED" "pvaux x"
  shows "`($x\<acute> = $x) ; ($x\<acute> = $x)` = `($x\<acute> = $x)`"
  apply (subst SemiR_algebraic)
  apply (simp_all add:closure unrest typing assms urename PermPV_PVAR)
  apply (simp add:eval evalp evale typing defined closure assms)
  apply (subst TypeUSound_ProjU_inv)
  apply (simp_all add:typing closure defined assms pvaux_aux[THEN sym])
  apply (auto)
  apply (rule_tac x="b(x\<down>\<acute>\<acute> :=\<^sub>b \<langle>b\<rangle>\<^sub>b x\<down>)" in exI)
  apply (simp)
done

lemma DestList_event_dcarrier [typing]: 
  fixes xs :: "('m EVENT ULIST, 'm :: REACTIVE_SORT) PVAR"
  assumes "pvaux xs"
  shows "set (DestList (\<langle>b\<rangle>\<^sub>b xs\<down>)) \<subseteq> dcarrier EventType"
  apply (rule DestList_elem_type)
  apply (simp add:closure)
  apply (auto intro:typing assms)[1]
done

lemma DestList_event'_dcarrier [typing]: 
  fixes xs :: "('m EVENT ULIST, 'm :: REACTIVE_SORT) PVAR"
  assumes "pvaux xs"
  shows "set (DestList (\<langle>b\<rangle>\<^sub>b xs\<down>\<acute>)) \<subseteq> dcarrier EventType"
  apply (rule DestList_elem_type)
  apply (simp add:closure)
  apply (rule typing)
  apply (auto intro:typing assms)[1]
  apply (metis assms aux_dash pvaux_aux)
done

lemma DestList_event''_dcarrier [typing]: 
  fixes xs :: "('m EVENT ULIST, 'm :: REACTIVE_SORT) PVAR"
  assumes "pvaux xs"
  shows "set (DestList (\<langle>b\<rangle>\<^sub>b xs\<down>\<acute>\<acute>)) \<subseteq> dcarrier EventType"
  apply (rule DestList_elem_type)
  apply (simp add:closure)
  apply (rule typing)
  apply (auto intro:typing assms)[1]
  apply (metis assms aux_dash pvaux_aux)
done

lemma DestList_event'''_dcarrier [typing]: 
  fixes xs :: "('m EVENT ULIST, 'm :: REACTIVE_SORT) PVAR"
  assumes "pvaux xs"
  shows "set (DestList (\<langle>b\<rangle>\<^sub>b xs\<down>\<acute>\<acute>\<acute>)) \<subseteq> dcarrier EventType"
  apply (rule DestList_elem_type)
  apply (simp add:closure)
  apply (rule typing)
  apply (auto intro:typing assms)[1]
  apply (metis assms aux_dash pvaux_aux)
done

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

lemma tr_eq_trans:
  "`($tr\<acute> = $tr) ; ($tr\<acute> = $tr)` = `($tr\<acute> = $tr)`"
  by (simp add:var_eq_trans typing defined closure)

(* () TYPE('m) *)

definition Rep_binding_typed :: 
  "'m WF_BINDING \<Rightarrow> ('a, 'm) PVAR \<Rightarrow> 'a" where
"Rep_binding_typed b x = ProjU (\<langle>b\<rangle>\<^sub>b x\<down>)"

lemma prefix_implies_concat_minus:
  "`($tr \<le> $tr\<acute>) \<Rightarrow> $tr ^ ($tr\<acute> - $tr) = $tr\<acute>`"
  apply (utp_pred_auto_tac)
  apply (subgoal_tac "set (drop (length (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>))) (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>\<acute>))) \<subseteq> dcarrier (EventType :: 'a UTYPE)")
  defer
  apply (rule subset_trans, rule set_drop_subset, rule DestList_tr'_dcarrier)
  apply (simp_all add:MkList_inj_simp typing closure prefixeq_drop)
  apply (metis prefixeq_drop)
done

lemma tr_prefix_implies_concat:
  assumes "pvaux ttx"
  shows "`($tr \<le> $tr\<acute>) \<Rightarrow> (\<exists> ttx\<acute>\<acute>\<acute>. $tr\<acute> = $tr ^ $ttx\<acute>\<acute>\<acute>)`"
  using assms
  apply (rule_tac ExistsP_assm_witness[of "|($tr\<acute> - $tr)|\<down>"])
  apply (simp add:typing defined closure)
  apply (simp add:usubst typing defined closure)
  apply (metis EqualP_sym prefix_implies_concat_minus)
done

lemma tr_prefix_as_concat:
  assumes "pvaux ttx" 
  shows "`($tr \<le> $tr\<acute>)` = `(\<exists> ttx\<acute>\<acute>\<acute>. $tr\<acute> = $tr ^ $ttx\<acute>\<acute>\<acute>)`"
  apply (rule_tac ImpliesP_eq_intro)
  apply (metis (hide_lams, no_types) assms tr_prefix_implies_concat)
  apply (insert assms, utp_pred_auto_tac)
done

lemma tr_eq_tr_leq:
  "`($tr\<acute> = $tr) ; ($tr \<le> $tr\<acute>)` = `($tr \<le> $tr\<acute>)`"
  apply (subst tr_prefix_as_concat[of "tr"], simp)
  apply (subst tr_prefix_as_concat[of "tr"], simp)
  apply (subst SemiR_algebraic)
  apply (simp_all add:closure unrest typing assms urename)
sorry

lemma tr_leq_trans:
  "`($tr \<le> $tr\<acute>) ; ($tr \<le> $tr\<acute>)` = `($tr \<le> $tr\<acute>)`"
  by (auto intro: binding_equiv_trans simp add:closure typing defined unrest closure evalr evalp relcomp_unfold urename)

lemma nil_prefixeq [simp]:
  "`\<langle>\<rangle> \<le> x` = `true`"
  by (utp_pred_auto_tac)

lemma nil_append [simp]:
  "|\<langle>\<rangle> ^ x| = |x|"
  by (auto simp add:evalp)

lemma tr_prefix_as_nil:
  "`($tr\<acute> - $tr) = \<langle>\<rangle> \<and> ($tr \<le> $tr\<acute>)` = `$tr\<acute> = $tr`"
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