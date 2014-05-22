(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_designs_laws.thy                                                 *)
(* Authors: Simon Foster, University of York                                  *)
(******************************************************************************)

header {* UTP Designs Laws *}

theory utp_designs_laws
imports 
  utp_designs_sig
begin

theorem DesignD_extreme_point_true:
  "false \<turnstile> false = false \<turnstile> true"
  "false \<turnstile> true = true"
  by (utp_pred_tac+)

theorem DesignD_extreme_point_nok:
  "`true \<turnstile> false` = `\<not> $ok`"
  "`\<not> $ok` = `\<top>\<^sub>D`"
  by (utp_poly_tac+)

theorem DesignD_assumption:
  assumes "{ok\<down>\<acute>} \<sharp> P"
  shows "`\<not> (P \<turnstile> Q)\<^sup>f` = `P \<and> $ok`"
  using assms
  by (utp_poly_auto_tac)

theorem DesignD_assumption_alt:
  assumes "OKAY \<sharp> P"
  shows "`\<not> (P \<turnstile> Q)\<^bsup>tf\<^esup>` = `P`"
  using assms
  by (utp_poly_auto_tac)

theorem DesignD_commitment:
  assumes
    "OKAY \<sharp> P" 
    "OKAY \<sharp> Q" 
  shows "`(P \<turnstile> Q)\<^sup>t` = `($ok \<and> P \<Rightarrow> Q)`"
  using assms by (utp_poly_auto_tac)

theorem DesignD_commitment_alt:
  assumes
    "OKAY \<sharp> P" 
    "OKAY \<sharp> Q" 
  shows "`(P \<turnstile> Q)\<^bsup>tt\<^esup>` = `P \<Rightarrow> Q`"
  using assms by (utp_poly_auto_tac)

theorem DesignD_export_precondition:
  "(P \<turnstile> Q) = (P \<turnstile> P \<and>\<^sub>p Q)"
  by (utp_pred_tac)

theorem DesignD_embed_right: 
  "`P \<turnstile> (Q \<turnstile> R)` = `P \<turnstile> (Q \<Rightarrow> R)`"
  by (utp_pred_auto_tac)

theorem DesignD_SkipD_right:
  "`P \<turnstile> II\<^sub>D` = `P \<turnstile> II`"
  by (simp add:SkipD_def DesignD_embed_right)

theorem DesignD_AssignD_right:
  "P \<turnstile> (x :=\<^sub>D v) = P \<turnstile> (x :=\<^bsub>(REL_VAR - OKAY)\<^esub> v)"
  by (simp add:AssignD_def DesignD_embed_right)

theorem DesignD_AssignD_true [simp]:
  "true \<turnstile> x :=\<^sub>D v = x :=\<^sub>D v"
  by (simp add:AssignD_def DesignD_embed_right)

lemma SkipD_SkipDA_right_link:
  assumes 
    "HOMOGENEOUS vs"
    "D\<^sub>1 - out vs \<sharp> P"
    "ok\<down> \<in> vs" 
  shows "P ;\<^sub>R II\<^sub>D = P ;\<^sub>R II\<^bsub>D[vs]\<^esub>"
  using assms
  apply (subst SemiR_ExistsP_insert_right[of "D\<^sub>0 - (in vs \<union> {ok\<down>})"])
  apply (simp add:var_dist)
  apply (rule UNREST_subset)
  apply (auto simp add:SkipDA_def DesignD_def ImpliesP_def ExistsP_OrP_dist)
  apply (subst ExistsP_AndP_expand2[THEN sym])
  apply (auto intro:unrest)
  apply (simp add:SkipRA_alt_in_def ExistsP_union[THEN sym] var_dist closure)
  apply (subst ExistsP_ident)
  apply (auto intro:unrest)
done  

lemma SkipD_SkipDA_left_link:
  assumes 
    "HOMOGENEOUS vs"
    "D\<^sub>0 - in vs \<sharp> P"
    "ok\<down>\<acute> \<in> vs" 
  shows "II\<^sub>D ;\<^sub>R P = II\<^bsub>D[vs]\<^esub> ;\<^sub>R P" 
  using assms
  apply (subst SemiR_ExistsP_insert_left[of "D\<^sub>1 - (out vs \<union> {ok\<down>\<acute>})"])
  apply (simp add:var_dist)
  apply (rule UNREST_subset)
  apply (auto simp add:SkipDA_def DesignD_def ImpliesP_def ExistsP_OrP_dist)
  apply (metis (hide_lams, no_types) Diff_disjoint Diff_iff Int_absorb1 UNDASHED_minus_in VAR_subset dash_undash_DASHED hom_alphabet_undash in_VAR in_vars_diff out_member)
  apply (subst ExistsP_AndP_expand2[THEN sym])
  apply (auto intro:unrest)
  apply (simp add:SkipRA_alt_out_def ExistsP_union[THEN sym] var_dist closure)
  apply (subst ExistsP_ident)
  apply (auto intro:unrest)
  apply (metis DesignD_extreme_point_nok(2) Diff_iff MkPlain_UNDASHED PVAR_VAR_MkPVAR UNDASHED_eq_dash_contra UNREST_TopD dash_undash_DASHED)
done  

text {* Design refinement law *}

theorem DesignD_refinement:
  assumes 
    "OKAY \<sharp> P1" 
    "OKAY \<sharp> P2"
    "OKAY \<sharp> Q1" 
    "OKAY \<sharp> Q2"
  shows "`P1 \<turnstile> Q1 \<sqsubseteq> P2 \<turnstile> Q2` = `[P1 \<Rightarrow> P2] \<and> [P1 \<and> Q2 \<Rightarrow> Q1]`"
proof -
  have "`(P1 \<turnstile> Q1) \<sqsubseteq> (P2 \<turnstile> Q2)` = `[P2 \<turnstile> Q2 \<Rightarrow> P1 \<turnstile> Q1]`"
    by (utp_pred_tac)

  also have "... = `[($ok \<and> P2 \<Rightarrow> $ok\<acute> \<and> Q2) \<Rightarrow> ($ok \<and> P1 \<Rightarrow> $ok\<acute> \<and> Q1)]`"
    by (utp_pred_tac)

  also with assms have "... = `[(P2 \<Rightarrow> $ok\<acute> \<and> Q2) \<Rightarrow> (P1 \<Rightarrow> $ok\<acute> \<and> Q1)]`"
    apply (rule_tac trans)
    apply (rule_tac x="ok\<down>" in BoolType_aux_var_split_taut)
    apply (simp_all add:usubst unrest typing defined)
  done

  also from assms have "... = `[(\<not> P2 \<Rightarrow> \<not> P1) \<and> ((P2 \<Rightarrow> Q2) \<Rightarrow> (P1 \<Rightarrow> Q1))]`"
    apply (rule_tac trans)
    apply (rule_tac x="ok\<acute>\<down>" in BoolType_aux_var_split_taut)
    apply (simp_all add:usubst typing defined)
  done

  also have "... = `[(P1 \<Rightarrow> P2) \<and> ((P2 \<Rightarrow> Q2) \<Rightarrow> (P1 \<Rightarrow> Q1))]`"
    by (utp_pred_auto_tac)

  also have "... = `[(P1 \<Rightarrow> P2)] \<and> [P1 \<and> Q2 \<Rightarrow> Q1]`"
    by (utp_pred_auto_tac)

  finally show ?thesis .
qed

theorem DesignD_refine [refine]:
  assumes 
    "P2 \<sqsubseteq> P1" "Q1 \<sqsubseteq> P1 \<and>\<^sub>p Q2" 
  shows "P1 \<turnstile> Q1 \<sqsubseteq> P2 \<turnstile> Q2"
  using assms by (utp_poly_tac)

theorem DesignD_diverge:
  "`(P \<turnstile> Q)[false/ok]` = true"
  by (simp add:DesignD_def usubst typing defined evalp)

theorem DesignD_left_zero:
  assumes 
    "P \<in> WF_RELATION"
    "Q \<in> WF_RELATION"
  shows "true ;\<^sub>R (P \<turnstile> Q) = true"
proof -

  from assms have "`true ; (P \<turnstile> Q)` = `\<exists> ok\<acute>\<acute>. true[$ok\<acute>\<acute>/ok\<acute>] ; (P \<turnstile> Q)[$ok\<acute>\<acute>/ok]`"
    by (simp add:SemiR_extract_variable erasure typing closure unrest)

  also from assms have "... = `(true[false/ok\<acute>] ; (P \<turnstile> Q)[false/ok]) \<or> (true[true/ok\<acute>] ; (P \<turnstile> Q)[true/ok])`"
    apply (rule_tac trans)
    apply (rule BoolType_aux_var_split_exists, simp_all)
    apply (simp add:erasure typing inju)
    apply (simp add: usubst)
    apply (simp add: SubstP_TrueP SubstP_NON_REL_VAR unrest closure)
    apply (simp add: SubstP_twice_2 unrest usubst typing defined)
  done

  also have "... = `((true ; true) \<or> (true ; ((P \<turnstile> Q)[true/ok])))`"
    by (simp add:usubst closure typing DesignD_diverge)

  ultimately show ?thesis
    by (simp add:closure SemiR_TrueP_precond)
qed

theorem DesignD_OrP:
  "`(P1 \<turnstile> Q1) \<or> (P2 \<turnstile> Q2)` = `(P1 \<and> P2 \<turnstile> Q1 \<or> Q2)`"
  by (utp_pred_auto_tac)

theorem DesignD_AndP:
  "`(P1 \<turnstile> Q1) \<and> (P2 \<turnstile> Q2)` = 
   `(P1 \<or> P2 \<turnstile> (P1 \<Rightarrow> Q1) \<and> (P2 \<Rightarrow> Q2))`"
  by (utp_pred_auto_tac)

theorem DesignD_OrDistP:
  "I \<noteq> {} \<Longrightarrow> `\<Or> i:I. P<i> \<turnstile> Q<i>` = `(\<And> i:I. P<i>) \<turnstile> (\<Or> i:I. Q<i>)`"
  by (utp_pred_auto_tac)

theorem DesignD_AndDistP:
  "I \<noteq> {} \<Longrightarrow> `\<And> i:I. P<i> \<turnstile> Q<i>` = `(\<Or> i:I. P<i>) \<turnstile> (\<And> i:I. P<i> \<Rightarrow> Q<i>)`"
  by (utp_pred_auto_tac)

text {* The choice of two designs conjoins the assumptions and disjoins the commitments *}

theorem DesignD_choice:
  "(P1 \<turnstile> Q1) \<sqinter> (P2 \<turnstile> Q2) = `(P1 \<and> P2 \<turnstile> Q1 \<or> Q2)`"
  by (utp_pred_auto_tac)

theorem DesignD_cond:
  "`(P1 \<turnstile> Q1) \<lhd> b \<rhd> (P2 \<turnstile> Q2)` = `((P1 \<lhd> b \<rhd> P2) \<turnstile> (Q1 \<lhd> b \<rhd> Q2))`"
  by (utp_pred_auto_tac)

theorem DesignD_composition:
  assumes 
  "(P1 \<in> REL)" "(P2 \<in> REL)" 
  "(Q1 \<in> REL)" "(Q2 \<in> REL)" 
  "{ok\<down>\<acute>} \<sharp> P1" "{ok\<down>} \<sharp> P2" "{ok\<down>\<acute>} \<sharp> Q1" "{ok\<down>} \<sharp> Q2"
  shows "`(P1 \<turnstile> Q1) ; (P2 \<turnstile> Q2)` = `((\<not> ((\<not> P1) ; true)) \<and> \<not> (Q1 ; (\<not> P2))) \<turnstile> (Q1 ; Q2)`"
proof -

  have " `(P1 \<turnstile> Q1) ; (P2 \<turnstile> Q2)` 
        = `\<exists> ok\<acute>\<acute> . ((P1 \<turnstile> Q1)[$ok\<acute>\<acute>/ok\<acute>] ; (P2 \<turnstile> Q2)[$ok\<acute>\<acute>/ok])`"
    by (rule SemiR_extract_variable_ty, simp_all add:closure typing unrest assms)

  also have "... = ` ((P1 \<turnstile> Q1)[false/ok\<acute>] ; (P2 \<turnstile> Q2)[false/ok]) 
                      \<or> ((P1 \<turnstile> Q1)[true/ok\<acute>] ; (P2 \<turnstile> Q2)[true/ok])`"
    by (simp add:ucases typing usubst defined closure unrest DesignD_def assms erasure inju SubstP_VarP_single_UNREST)


  also from assms
  have "... = `(($ok \<and> P1 \<Rightarrow> Q1) ; (P2 \<Rightarrow> $ok\<acute> \<and> Q2)) \<or> ((\<not> ($ok \<and> P1)) ; true)`"
    by (simp add: typing usubst defined unrest DesignD_def OrP_comm erasure SubstP_VarP_single_UNREST)

  also have "... = `((\<not> ($ok \<and> P1) ; (P2 \<Rightarrow> $ok\<acute> \<and> Q2)) \<or> \<not> ($ok \<and> P1) ; true) 
                       \<or> Q1 ; (P2 \<Rightarrow> $ok\<acute> \<and> Q2)`"
    by (smt OrP_assoc OrP_comm SemiR_OrP_distr ImpliesP_def)

  also have "... = `(\<not> ($ok \<and> P1) ; true) \<or> Q1 ; (P2 \<Rightarrow> $ok\<acute> \<and> Q2)`"
    by (smt SemiR_OrP_distl utp_pred_simps(9))

  also have "... = `(\<not>$ok ; true) \<or> (\<not>P1 ; true) \<or> (Q1 ; \<not>P2) \<or> ($ok\<acute> \<and> (Q1 ; Q2))`"
  proof -
    from assms have "`Q1 ; (P2 \<Rightarrow> $ok\<acute> \<and> Q2)` = `(Q1 ; \<not>P2) \<or> ($ok\<acute> \<and> (Q1 ; Q2))`"
      by (simp add:ImpliesP_def SemiR_OrP_distl AndP_comm SemiR_AndP_right_postcond closure)
    
    thus ?thesis by (smt OrP_assoc SemiR_OrP_distr demorgan2)
  qed

  also have "... = `(\<not> (\<not> P1 ; true) \<and> \<not> (Q1 ; \<not> P2)) \<turnstile> (Q1 ; Q2)`"
  proof -
    have "`(\<not> $ok) ; true \<or> (\<not> P1) ; true` = `\<not> $ok \<or> (\<not> P1) ; true`"
      by (simp add: SemiR_TrueP_precond closure)

    thus ?thesis
      by (smt DesignD_def ImpliesP_def OrP_assoc demorgan2 demorgan3)
  qed

  finally show ?thesis .
qed

theorem DesignD_composition_cond:
  assumes 
    "p1 \<in> COND" 
    "P2 \<in> REL" 
    "Q1 \<in> REL" 
    "Q2 \<in> REL"
    "{ok\<down>\<acute>} \<sharp> p1" 
    "{ok\<down>} \<sharp> P2" 
    "{ok\<down>\<acute>} \<sharp> Q1" 
    "{ok\<down>} \<sharp> Q2"
  shows "`(p1 \<turnstile> Q1) ; (P2 \<turnstile> Q2)` = `(p1 \<and> \<not> (Q1 ; \<not> P2)) \<turnstile> (Q1 ; Q2)`"
  by (simp add:DesignD_composition closure assms unrest)

theorem DesignD_composition_wp:
  assumes 
    "p1 \<in> COND" 
    "P2 \<in> REL" 
    "Q1 \<in> REL" 
    "Q2 \<in> REL"
    "{ok\<down>\<acute>} \<sharp> p1" 
    "{ok\<down>} \<sharp> P2" 
    "{ok\<down>\<acute>} \<sharp> Q1" 
    "{ok\<down>} \<sharp> Q2"
  shows "`(p1 \<turnstile> Q1) ; (P2 \<turnstile> Q2)` = `(p1 \<and> (Q1 wp P2)) \<turnstile> (Q1 ; Q2)`"
  by (simp add: DesignD_composition_cond closure WeakPrecondP_def assms)

theorem DesignD_TopD_left:
  assumes "P \<in> REL" "Q \<in> REL" "OKAY \<sharp> P" "OKAY \<sharp> Q"
  shows "`\<top>\<^sub>D ; (P \<turnstile> Q)` = `\<top>\<^sub>D`"
  apply (simp add:DesignD_extreme_point_nok[THEN sym])
  apply (subst DesignD_composition)
  apply (simp_all add:assms closure unrest)
done  

theorem DesignD_TopD_right:
  assumes "P \<in> REL" "Q \<in> REL" "OKAY \<sharp> P" "OKAY \<sharp> Q"
  shows "`(P \<turnstile> Q); \<top>\<^sub>D` = `(\<not> ((\<not> P) ; true) \<turnstile> false)`"
  apply (simp add:DesignD_extreme_point_nok[THEN sym])
  apply (subst DesignD_composition)
  apply (simp_all add:assms closure unrest)
done

theorem AssignD_idem :
  assumes 
    "x \<in> D\<^sub>0" 
    "x \<notin> OKAY"
    "OKAY \<union> (VAR - (in vs - {x})) \<sharp> v"
    "v \<rhd>\<^sub>e x"
  shows "x :=\<^sub>D v ;\<^sub>R x :=\<^sub>D v = x :=\<^sub>D v"
  using assms
  apply (simp add:AssignD_def)
  apply (subst DesignD_composition_wp)
  apply (simp_all add:closure unrest wp typing defined UNREST_EXPR_subset)
  apply (rule closure)
  apply (simp_all)
  apply (rule UNREST_EXPR_subset)
  apply (simp)
  apply (auto)[1]
  apply (metis (full_types) UNDASHED_not_NON_REL_VAR in_mono utp_var.in_UNDASHED)
  apply (rule unrest) back
  apply (simp_all)
  apply (rule UNREST_EXPR_subset)
  apply (simp)
  apply (auto)[1]
  apply (metis (full_types) UNDASHED_not_NON_REL_VAR utp_var.in_UNDASHED set_mp)
  apply (rule unrest) back
  apply (simp_all)
  apply (rule UNREST_EXPR_subset)
  apply (simp)
  apply (auto)[1]
  apply (metis (full_types) UNDASHED_not_NON_REL_VAR in_mono utp_var.in_UNDASHED)
  apply (subst AssignRA_idem)
  apply (simp_all add:var_dist closure)
  apply (rule UNREST_EXPR_subset)
  apply (auto)
  apply (metis (full_types) utp_var.in_UNDASHED set_mp)
done

theorem ParallelD_DesignD:
  assumes 
    "OKAY \<sharp> P1" 
    "OKAY \<sharp> P2" 
    "OKAY \<sharp> Q1" 
    "OKAY \<sharp> Q2"
  shows "`(P1 \<turnstile> P2) \<parallel> (Q1 \<turnstile> Q2)` = `(P1 \<and> Q1) \<turnstile> (P2 \<and> Q2)`"
  using assms 
  by (utp_poly_auto_tac)

theorem ParallelD_comm:
  "P \<parallel> Q = Q \<parallel> P"
  by (utp_pred_auto_tac)

theorem ParallelD_assoc:
  fixes P :: "'a upred"
  shows "P \<parallel> Q \<parallel> R = (P \<parallel> Q) \<parallel> R"
  by (utp_poly_auto_tac)

end
