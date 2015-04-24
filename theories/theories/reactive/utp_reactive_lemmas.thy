(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_reactive_lemmas.thy                                              *)
(* Authors: Simon Foster and Samuel Canham, University of York                *)
(******************************************************************************)

header {* Lemmas for the theory of reactive processes *}

theory utp_reactive_lemmas
imports 
  "utp_designs"
  "utp_reactive_sig"
begin

abbreviation wait_true :: 
  "'a upred \<Rightarrow> 'a upred" ("_\<^sub>t"[150]) where
"p \<^sub>t \<equiv> `p[true/wait]`"

abbreviation wait_false :: 
  "'a upred \<Rightarrow> 'a upred" ("_\<^sub>f"[150]) where
"p \<^sub>f \<equiv> `p[false/wait]`"

syntax
  "_n_upred_wait_true"    :: "n_upred \<Rightarrow> n_upred" ("_\<^sub>t" [1000] 1000)
  "_n_upred_wait_false"   :: "n_upred \<Rightarrow> n_upred" ("_\<^sub>f" [1000] 1000)

translations
  "_n_upred_wait_true p"  == "CONST wait_true p"
  "_n_upred_wait_false p" == "CONST wait_false p"

lemma ok_wait_commute_t_t: 
  "`P\<^sup>t\<^sub>t` = `P \<^sub>t\<^sup>t`"
  apply (subst SubstP_twice_3)
  apply (simp_all add: typing defined unrest)
  apply (simp add:usubst typing defined)
done

lemma ok_wait_commute_f_f: 
  "`P\<^sup>f\<^sub>f` = `P \<^sub>f\<^sup>f`"
  apply (subst SubstP_twice_3)
  apply (simp_all add: typing defined unrest)
  apply (simp add:usubst typing defined)
done

lemma ok_wait_commute_t_f: 
  "`P\<^sup>t\<^sub>f` = `P \<^sub>f\<^sup>t`"
  apply (subst SubstP_twice_3)
  apply (simp_all add: typing defined unrest)
  apply (simp add:usubst typing defined)
done

lemma ok_wait_commute_f_t: 
  "`P\<^sup>f\<^sub>t` = `P \<^sub>t\<^sup>f`"
  apply (subst SubstP_twice_3)
  apply (simp_all add:typing defined unrest)
  apply (simp add:usubst typing defined)
done

lemma tr_eq_rel_closure[closure]: 
  "`($tr\<acute> = $tr)` \<in> WF_RELATION"
 by (simp add:closure)

lemma tr_leq_rel_closure[closure]: 
  "`($tr \<le> $tr\<acute>)` \<in> WF_RELATION"
by(simp add: closure)

lemma DestList_event_dcarrier [typing]: 
  fixes xs :: "('m event ULIST, 'm :: REACTIVE_SORT) pvar"
  assumes "pvaux xs"
  shows "set (DestList (\<langle>b\<rangle>\<^sub>b xs\<down>)) \<subseteq> dcarrier EventType"
  apply (rule DestList_subset_dcarrier)
  apply (simp add: typing)
  apply (metis assms aux_defined pvaux_aux)
done

lemma DestList_event'_dcarrier [typing]: 
  fixes xs :: "('m event ULIST, 'm :: REACTIVE_SORT) pvar"
  assumes "pvaux xs"
  shows "set (DestList (\<langle>b\<rangle>\<^sub>b xs\<down>\<acute>)) \<subseteq> dcarrier EventType"
  apply (rule DestList_subset_dcarrier)
  apply (simp add: closure)
  apply (simp add: typing)
  apply (metis assms aux_dash aux_defined pvaux_aux)
done

lemma DestList_event''_dcarrier [typing]: 
  fixes xs :: "('m event ULIST, 'm :: REACTIVE_SORT) pvar"
  assumes "pvaux xs"
  shows "set (DestList (\<langle>b\<rangle>\<^sub>b xs\<down>\<acute>\<acute>)) \<subseteq> dcarrier EventType"
  apply (rule DestList_subset_dcarrier)
  apply (simp add: closure)
  apply (simp add: typing)
  apply (metis assms aux_dash aux_defined pvaux_aux)
done

lemma DestList_event'''_dcarrier [typing]: 
  fixes xs :: "('m event ULIST, 'm :: REACTIVE_SORT) pvar"
  assumes "pvaux xs"
  shows "set (DestList (\<langle>b\<rangle>\<^sub>b xs\<down>\<acute>\<acute>\<acute>)) \<subseteq> dcarrier EventType"
  apply (rule DestList_subset_dcarrier)
  apply (simp add: closure)
  apply (simp add: typing)
  apply (metis assms aux_dash aux_defined pvaux_aux)
done

lemma DestList_tr_dcarrier [typing]: 
  "set (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>)) \<subseteq> dcarrier EventType"
  apply (rule DestList_subset_dcarrier)
  apply (simp add: closure)
  apply (simp add: typing defined)
done

lemma DestList_tr'_dcarrier [typing]: 
  "set (DestList (\<langle>b\<rangle>\<^sub>b tr\<down>\<acute>)) \<subseteq> dcarrier EventType"
  apply (rule DestList_subset_dcarrier)
  apply (simp add: closure)
  apply (simp add: typing defined)
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
  by (simp add:var_eq_trans typing closure)

(* () TYPE('m) *)

lemma tr_prefix_as_concat:
  assumes "pvaux ttx" 
  shows "`($tr \<le> $tr\<acute>)` = `(\<exists> ttx\<acute>\<acute>. $tr\<acute> = $tr ^ $ttx\<acute>\<acute>)`"
  apply (rule prefix_as_concat)
  apply (simp_all add:typing defined assms closure)
done

lemma tr_eq_tr_leq:
  "`($tr\<acute> = $tr) ; ($tr \<le> $tr\<acute>)` = `($tr \<le> $tr\<acute>)`"
  by (utp_prel_auto_tac)

lemma tr_leq_trans:
  "`($tr \<le> $tr\<acute>) ; ($tr \<le> $tr\<acute>)` = `($tr \<le> $tr\<acute>)`"
  by (utp_prel_auto_tac)

lemma tr_eq_is_R1:
  "`($tr\<acute>= $tr) \<and> ($tr \<le> $tr\<acute>)` = `$tr\<acute> = $tr` "
  by (utp_prel_auto_tac)

lemma tr_prefix_as_nil:
  "`($tr\<acute> - $tr) = \<langle>\<rangle> \<and> ($tr \<le> $tr\<acute>)` = `$tr\<acute> = $tr`"
  by (metis PEqualP_sym UTypedef_Event UTypedef_ULIST prefix_eq_nil)

lemma tr_prefix_app:
  "`($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> ($tr \<le> $tr\<acute>)` = `($tr ^ \<langle>a\<rangle> = $tr\<acute>)`"
  by (metis UTypedef_Event UTypedef_ULIST prefix_app)
 
lemma Leq_alt: "`($tr \<le> $tr\<acute>)` = `($tr < $tr\<acute>) \<or> ($tr = $tr\<acute>)`"
  by(utp_poly_auto_tac)

lemma Subst_NotEq:
  assumes "`P[x/y]` \<noteq> `Q[x/y]`"
  shows "`P` \<noteq> `Q`"
by (metis assms)

lemma Seq_split_ok:
  assumes "P \<in> REL" "Q \<in> REL"
  shows "`P;Q` = `(P[true/ok\<acute>];(Q[true/ok])) \<or> (P[false/ok\<acute>];(Q[false/ok]))`"
proof-
have "`P;Q` = `\<exists> ok\<acute>\<acute>. ($ok\<acute>\<acute> \<or> \<not> $ok\<acute>\<acute>) \<and> (P[$ok\<acute>\<acute>/ok\<acute>];(Q[$ok\<acute>\<acute>/ok]))`"
  by(subst SemiR_extract_variable_ty[of "ok" "ok\<acute>\<acute>"],simp_all add:typing defined closure unrest assms OrP_excluded_middle)
also have "... = `(\<exists> ok\<acute>\<acute>. ($ok\<acute>\<acute> \<and> (P[$ok\<acute>\<acute>/ok\<acute>];(Q[$ok\<acute>\<acute>/ok])))) \<or> (\<exists> ok\<acute>\<acute>. (\<not> $ok\<acute>\<acute>\<and> (P[$ok\<acute>\<acute>/ok\<acute>];(Q[$ok\<acute>\<acute>/ok]))))`"
  by(simp add:AndP_OrP_distr ExistsP_OrP_dist)
also have "... = `(\<exists> ok\<acute>\<acute>. ((P[$ok\<acute>\<acute>/ok\<acute>];(Q[$ok\<acute>\<acute>/ok])) \<and> $ok\<acute>\<acute>=true)) \<or> (\<exists> ok\<acute>\<acute>. ((P[$ok\<acute>\<acute>/ok\<acute>];(Q[$ok\<acute>\<acute>/ok]))\<and> $ok\<acute>\<acute>=false))`"
  by(simp add: EqualP_as_EqualPE[THEN sym] typing defined closure AndP_comm)
also have "... = `(P[$ok\<acute>\<acute>/ok\<acute>];(Q[$ok\<acute>\<acute>/ok]))[true/(ok\<acute>\<acute>)] \<or> (\<exists> ok\<acute>\<acute>. ((P[$ok\<acute>\<acute>/ok\<acute>];(Q[$ok\<acute>\<acute>/ok]))\<and> $ok\<acute>\<acute>=false))`"
  by(subst ExistsP_one_point_ty[of _ "ok\<acute>\<acute>",THEN sym],simp_all add: typing defined closure unrest)
also have "... = `(P[$ok\<acute>\<acute>/ok\<acute>];(Q[$ok\<acute>\<acute>/ok]))[true/(ok\<acute>\<acute>)] \<or> (P[$ok\<acute>\<acute>/ok\<acute>];(Q[$ok\<acute>\<acute>/ok]))[false/ok\<acute>\<acute>]`"
  by(subst ExistsP_one_point_ty[of _ "ok\<acute>\<acute>",THEN sym],simp_all add: typing defined closure unrest)
also have "... = `(P[true/ok\<acute>];(Q[true/ok])) \<or> (P[false/ok\<acute>];(Q[false/ok]))`"
  by(simp add: usubst(36) typing defined closure unrest SubstP_twice_2 assms usubst(7) usubst(24))
finally show ?thesis .
qed

lemma Seq_split_wait:
  assumes "P \<in> REL" "Q \<in> REL"
  shows "`P;Q` = `(P[true/wait\<acute>];(Q[true/wait])) \<or> (P[false/wait\<acute>];(Q[false/wait]))`"
proof-
have "`P;Q` = `\<exists> wait\<acute>\<acute>. ($wait\<acute>\<acute> \<or> \<not> $wait\<acute>\<acute>) \<and> (P[$wait\<acute>\<acute>/wait\<acute>];(Q[$wait\<acute>\<acute>/wait]))`"
by(subst SemiR_extract_variable_ty[of "wait" "wait\<acute>\<acute>"],simp_all add:typing defined closure unrest assms OrP_excluded_middle)
also have "... = `(\<exists> wait\<acute>\<acute>. ($wait\<acute>\<acute> \<and> (P[$wait\<acute>\<acute>/wait\<acute>];(Q[$wait\<acute>\<acute>/wait])))) \<or> (\<exists> wait\<acute>\<acute>. (\<not> $wait\<acute>\<acute>\<and> (P[$wait\<acute>\<acute>/wait\<acute>];(Q[$wait\<acute>\<acute>/wait]))))`"
  by(simp add:AndP_OrP_distr ExistsP_OrP_dist)
also have "... = `(\<exists> wait\<acute>\<acute>. ((P[$wait\<acute>\<acute>/wait\<acute>];(Q[$wait\<acute>\<acute>/wait])) \<and> $wait\<acute>\<acute>=true)) \<or> (\<exists> wait\<acute>\<acute>. ((P[$wait\<acute>\<acute>/wait\<acute>];(Q[$wait\<acute>\<acute>/wait]))\<and> $wait\<acute>\<acute>=false))`"
  by(simp add: EqualP_as_EqualPE[THEN sym] typing defined closure AndP_comm)
also have "... = `(P[$wait\<acute>\<acute>/wait\<acute>];(Q[$wait\<acute>\<acute>/wait]))[true/wait\<acute>\<acute>] \<or> (\<exists> wait\<acute>\<acute>. ((P[$wait\<acute>\<acute>/wait\<acute>];(Q[$wait\<acute>\<acute>/wait]))\<and> $wait\<acute>\<acute>=false))`"
  by(subst ExistsP_one_point_ty[of _ "wait\<acute>\<acute>",THEN sym],simp_all add: typing defined closure unrest)
also have "... = `(P[$wait\<acute>\<acute>/wait\<acute>];(Q[$wait\<acute>\<acute>/wait]))[true/wait\<acute>\<acute>] \<or> (P[$wait\<acute>\<acute>/wait\<acute>];(Q[$wait\<acute>\<acute>/wait]))[false/wait\<acute>\<acute>]`"
  by(subst ExistsP_one_point_ty[of _ "wait\<acute>\<acute>",THEN sym],simp_all add: typing defined closure unrest)
also have "... = `(P[true/wait\<acute>];(Q[true/wait])) \<or> (P[false/wait\<acute>];(Q[false/wait]))`"
  by(simp add: usubst(36) typing defined closure unrest SubstP_twice_2 assms usubst(7) usubst(24))
finally show ?thesis .
qed

lemma tr_diff_neq:
  "`$tr^\<langle>x\<rangle> = $tr` = `false`"
by(utp_poly_auto_tac)

lemma tr_prefix_as_a: 
  "`\<langle>a\<rangle> = ($tr \<acute>-$tr) \<and> ($tr \<le> $tr \<acute>)` = `$tr^\<langle>a\<rangle> = $tr \<acute>`"
apply(utp_poly_auto_tac)
apply (metis prefixeq_drop)
apply (metis append_eq_conv_conj)
apply (metis prefixeqI)
done

lemma a_notin_ref_closure[closure]:
  assumes "NON_REL_VAR \<sharp> a"
  shows "`a \<notin> $ref\<acute>` \<in> WF_RELATION"
apply(simp add:WF_RELATION_def)
apply(simp add:closure unrest assms typing defined)
done

lemma tr_prefix_a_closure[closure]:
  assumes "NON_REL_VAR \<sharp> a"
  shows "`$tr^\<langle>a\<rangle> = $tr\<acute>` \<in> WF_RELATION"
apply(simp add:WF_RELATION_def)
apply(simp add:closure unrest assms typing defined)
done

lemma tr_less_eq_self: 
  fixes x :: "('a::DEFINED ULIST, 'm::REACTIVE_SORT) pvar"  
  shows "`($x \<le> $x)` = `true`"
  by (utp_poly_auto_tac)

lemma tr_leq_ident:
  fixes x :: "('a::DEFINED ULIST, 'm::REACTIVE_SORT) pvar"
  shows "`($x \<le> $y) \<and> ($y \<le> $x)` = `$y = $x`"
  by (utp_poly_auto_tac)
  
lemma SubstP_EqualP_swap:
  fixes x :: "('a :: DEFINED, 'm :: TYPED_MODEL) pvar"
  assumes "UTYPEDEF('a, 'm)" "pvaux x" "pvaux y" "pvaux z"
  shows "`P[$x/y] \<and> ($z = $x)` = `P[$z/y] \<and> ($z = $x)`"
  using assms
  by (utp_poly_auto_tac)

lemma SubstP_ident: 
  fixes x :: "('a :: DEFINED, 'm :: TYPED_MODEL) pvar"
  assumes "UTYPEDEF('a, 'm)" "pvaux x"
  shows "`P[$x/x]` = `P`"
  using assms
  by (utp_poly_tac)

end