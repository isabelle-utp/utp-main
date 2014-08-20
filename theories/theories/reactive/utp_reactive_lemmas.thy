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
 by (simp add:closure unrest typing)


lemma tr_leq_rel_closure[closure]: 
  "`($tr \<le> $tr\<acute>)` \<in> WF_RELATION"
  apply(simp add:WF_RELATION_def)
  apply (simp add:closure unrest typing)
done

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
  by (simp add:var_eq_trans typing defined closure)

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
  apply (subst prefix_eq_nil[of "tr\<acute>" "tr"])
  apply (simp_all add:typing defined closure PEqualP_sym)
done

lemma tr_prefix_app:
  "`($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> ($tr \<le> $tr\<acute>)` = `($tr ^ \<langle>a\<rangle> = $tr\<acute>)`"
  apply (rule prefix_app)
  apply (simp add:closure typing)
done

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
also have "... =`(P[true/ok\<acute>];(Q[true/ok])) \<or> (P[false/ok\<acute>];(Q[false/ok]))`"
apply(subst PVarPE_VarP[THEN sym])
apply(subst NotP_PVarPE_VarP[THEN sym])
apply(subst AndP_comm)
apply(subst AndP_OrP_distl)
apply(subst ExistsP_OrP_dist)
apply(subst EqualP_as_EqualPE,simp add:typing defined closure)+
apply(subst ExistsP_one_point_ty) defer defer defer defer
apply(subst ExistsP_one_point_ty)
apply(simp add:typing defined closure unrest)+ defer
apply(simp add:typing defined closure unrest)+
apply(subst usubst) back back back back back back back back back back
apply(simp_all add:typing defined closure unrest)
apply(subst usubst) back back back back back back back back back back back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_2,simp_all add:typing defined closure unrest assms)+
apply(simp add:usubst typing defined closure)
done
finally show ?thesis .
qed

lemma Seq_split_wait:
  assumes "P \<in> REL" "Q \<in> REL"
  shows "`P;Q` = `(P[true/wait\<acute>];(Q[true/wait])) \<or> (P[false/wait\<acute>];(Q[false/wait]))`"
proof-
have "`P;Q` = `\<exists> wait\<acute>\<acute>. ($wait\<acute>\<acute> \<or> \<not> $wait\<acute>\<acute>) \<and> (P[$wait\<acute>\<acute>/wait\<acute>];(Q[$wait\<acute>\<acute>/wait]))`"
by(subst SemiR_extract_variable_ty[of "wait" "wait\<acute>\<acute>"],simp_all add:typing defined closure unrest assms OrP_excluded_middle)
also have "... =`(P[true/wait\<acute>];(Q[true/wait])) \<or> (P[false/wait\<acute>];(Q[false/wait]))`"
apply(subst PVarPE_VarP[THEN sym])
apply(subst NotP_PVarPE_VarP[THEN sym])
apply(subst AndP_comm)
apply(subst AndP_OrP_distl)
apply(subst ExistsP_OrP_dist)
apply(subst EqualP_as_EqualPE,simp add:typing defined closure)+
apply(subst ExistsP_one_point_ty) defer defer defer defer
apply(subst ExistsP_one_point_ty)
apply(simp add:typing defined closure unrest)+ defer
apply(simp add:typing defined closure unrest)+
apply(subst usubst) back back back back back back back back back back
apply(simp_all add:typing defined closure unrest)
apply(subst usubst) back back back back back back back back back back back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_2,simp_all add:typing defined closure unrest assms)+
apply(simp add:usubst typing defined closure)
done
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

lemma prime_ref_a: 
  assumes "D\<^sub>0 \<sharp> a"
  shows "`($ref = {a})\<acute>` = `$ref\<acute> = {a}`"
sorry

lemma less_eq_self: "`($x \<le> $x)` = `true`"
sorry

lemma tr_leq_ident:
  "`($x \<le> $y) \<and> ($y \<le> $x)` = `$y = $x`"
sorry

lemma SubstP_EqualP_swap:
  "`P[$x/y] \<and> ($z = $x)` = `P[$z/y] \<and> ($z = $x)`"
sorry 

lemma SubstP_ident: 
  "`P[$x/x]` = `P`"
sorry

end