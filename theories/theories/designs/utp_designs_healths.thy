(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_designs_healths.thy                                              *)
(* Authors: Simon Foster, University of York                                  *)
(******************************************************************************)

header {* UTP Designs Healtiness Conditions *}

theory utp_designs_healths
imports 
  utp_designs_laws
begin

subsection {* H1: Only observation after starting *}

definition "H1(P) = `$ok \<Rightarrow> P`"

declare H1_def [eval,evalr,evalrx,evalpp,evalpr]

theorem H1_true [closure]:
  "true is H1"
  by (utp_pred_tac)

theorem H1_DesignD [closure]:
  "H1(P \<turnstile> Q) = P \<turnstile> Q"
  by (utp_pred_auto_tac)

theorem DesignD_is_H1 [closure]:
  "P \<turnstile> Q is H1"
  by (utp_pred_auto_tac)

theorem SkipD_is_H1 [closure]:
  "II\<^sub>D is H1"
  by (simp add:SkipDA_def closure)

theorem H1_TrueP:
  "H1(true) = true"
  by (utp_pred_auto_tac)

theorem H1_FalseP:
  "H1(false) = \<top>\<^sub>D"
  by (utp_pred_auto_tac)

theorem H1_TopD:
  "H1(\<top>\<^sub>D) = \<top>\<^sub>D"
  by (utp_pred_auto_tac)

lemma H1_below_TopD: 
  "p is H1 \<longleftrightarrow> p \<sqsubseteq> \<top>\<^sub>D"
  by (utp_poly_auto_tac)

theorem H1_AndP: "`H1(p \<and> q)` = `H1(p) \<and> H1(q)`"
  by (utp_pred_auto_tac)

theorem H1_OrP: "`H1(p \<or> q)` = `H1(p) \<or> H1(q)`"
  by (utp_pred_auto_tac)

theorem H1_AndDistP:
  "H1 (\<And>\<^sub>p ps) = \<And>\<^sub>p {H1(p) | p. p \<in> ps}"
  by (simp add:H1_def ImpliesP_AndDistP_dist)

theorem AndDistP_is_H1:
  "\<lbrakk> \<forall> p\<in>ps. p is H1 \<rbrakk> \<Longrightarrow> \<And>\<^sub>p ps is H1"
  by (utp_pred_auto_tac)

theorem H1_OrDistP:
  "ps \<noteq> {} \<Longrightarrow> H1 (\<Or>\<^sub>p ps) = \<Or>\<^sub>p {H1(p) | p. p \<in> ps}"
  by (simp add: H1_def ImpliesP_OrDistP_dist)

theorem OrDistP_is_H1:
  "\<lbrakk> \<forall> p\<in>ps. p is H1; ps \<noteq> {} \<rbrakk> \<Longrightarrow> \<Or>\<^sub>p ps is H1"
  apply (simp add:is_healthy_def H1_OrDistP)
  apply (subgoal_tac "{H1 p |p. p \<in> ps} = ps")
  apply (simp)
  apply (auto, metis)
done

theorem H1_CondR: 
  "`H1(P \<lhd> c \<rhd> Q)` = `H1(P) \<lhd> c \<rhd> H1(Q)`"
  by (utp_pred_auto_tac)

theorem H1_algebraic_intro:
  assumes 
    "(true ;\<^sub>R R = true)" 
    "(II\<^sub>D ;\<^sub>R R = R)"
  shows "R is H1"
proof -
  let ?vs = "REL_VAR - OKAY"
  have "R = II\<^sub>D ;\<^sub>R R" by (simp add: assms)

  also have "... = `(true \<turnstile> II\<^bsub>?vs\<^esub>) ; R`"
    by (simp add:SkipDA_def)

  also have "... = `($ok \<Rightarrow> ($ok\<acute> \<and> II\<^bsub>?vs\<^esub>)) ; R`"
    by (simp add:DesignD_def)

  also have "... = `($ok \<Rightarrow> ($ok \<and> $ok\<acute> \<and> II\<^bsub>?vs\<^esub>)) ; R`"
    by (metis (hide_lams, no_types) ImpliesP_export)

  also have "... = `($ok \<Rightarrow> ($ok \<and> $ok\<acute> = $ok \<and> II\<^bsub>?vs\<^esub>)) ; R`"
    apply (simp add:VarP_EqualP_aux typing defined erasure)
    apply (auto simp add:evalr unrest closure evale relcomp_unfold)
  done

  also have "... = `($ok \<Rightarrow> II) ; R`"
    by (simp add:SkipRA_unfold[THEN sym] 
        SkipR_as_SkipRA ImpliesP_export[THEN sym] erasure closure typing)

  also have "... = `((\<not> $ok) ; R \<or> R)`"
    by (simp add:ImpliesP_def SemiR_OrP_distr)

  also have "... = `(((\<not> $ok) ; true) ; R \<or> R)`"
    by (simp add:SemiR_TrueP_precond closure)

  also have "... = `((\<not> $ok) ; true \<or> R)`"
    by (simp add:SemiR_assoc[THEN sym] assms)

  also have "... = `$ok \<Rightarrow> R`"
    by (simp add:SemiR_TrueP_precond closure ImpliesP_def)

  finally show ?thesis by (simp add:is_healthy_def H1_def)
qed

declare EvalP_SemiR [evalpp]
declare ImpliesP_def [evalpr]

theorem H1_left_zero:
  assumes "P is H1"
  shows "`true ; P` = `true`"
proof -
  from assms have "`true ; P` = `true ; ($ok \<Rightarrow> P)`"
    by (utp_pred_tac)

  also have "... = `true ; (\<not> $ok \<or> P)`"
    by (simp add:ImpliesP_def)

  also have "... = `(true ; \<not> $ok) \<or> (true ; P)`"
    by (metis SemiR_OrP_distl)

  also from assms have "... = `true \<or> (true ; P)`"
    by (simp add:SemiR_precond_left_zero closure)

  finally show ?thesis by simp
qed

theorem H1_left_unit:
  assumes "P is H1"
  shows "`II\<^sub>D ; P` = `P`"
proof -
  let ?vs = "REL_VAR - OKAY"
  have "`II\<^sub>D ; P` = `(true \<turnstile> II\<^bsub>?vs\<^esub>) ; P`" by (simp add:SkipDA_def)
  also have "... = `($ok \<Rightarrow> $ok\<acute> \<and> II\<^bsub>?vs\<^esub>) ; P`" 
    by (simp add:DesignD_def)
  also have "... = `($ok \<Rightarrow> $ok \<and> $ok\<acute> \<and> II\<^bsub>?vs\<^esub>) ; P`" 
    by (smt ImpliesP_export)
  also have "... = `($ok \<Rightarrow> $ok \<and> $ok\<acute> = $ok \<and> II\<^bsub>?vs\<^esub>) ; P`"
    by (simp add:VarP_EqualP_aux erasure typing closure, utp_pred_tac)
  also have "... = `($ok \<Rightarrow> II) ; P`"
    by (simp add: SkipR_as_SkipRA SkipRA_unfold[of "ok\<down>"] ImpliesP_export[THEN sym]
                  erasure typing closure)
  also have "... = `((\<not> $ok) ; P \<or> P)`"
    by (simp add:ImpliesP_def SemiR_OrP_distr)
  also have "... = `(((\<not> $ok) ; true) ; P \<or> P)`"
    by (simp add: SemiR_TrueP_precond closure)
  also have "... = `((\<not> $ok) ; (true ; P) \<or> P)`"
    by (metis SemiR_assoc)
  also from assms have "... = `($ok \<Rightarrow> P)`"
    by (simp add:H1_left_zero ImpliesP_def SemiR_TrueP_precond closure)
  finally show ?thesis using assms
    by (simp add:H1_def is_healthy_def)
qed

theorem SkipD_left_unit:
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "`II\<^sub>D ; (P \<turnstile> Q)` = `P \<turnstile> Q`"
  by (simp add: DesignD_is_H1 DesignD_rel_closure H1_left_unit assms)

theorem H1_algebraic:
  "P is H1 \<longleftrightarrow> (`true ; P` = `true`) \<and> (`II\<^sub>D ; P` = `P`)"
   by (metis H1_algebraic_intro H1_left_unit H1_left_zero assms)
  
theorem H1_false:
  "H1 false \<noteq> false"
  by (metis H1_FalseP TopD_FalseP_uniqs(1))

theorem H1_TopD_left_zero:
  assumes "P is H1"
  shows "`\<top>\<^sub>D ; P` = `\<top>\<^sub>D`"
  using assms
  by (metis (full_types) H1_left_zero SemiR_TrueP_precond SemiR_assoc TopD_cond_closure) 

theorem H1_ImpliesP_SemiR:
  assumes "p \<in> COND" "R is H1"
  shows "`p \<Rightarrow> (Q ; R)` = `(p \<Rightarrow> Q) ; R`"
proof -

  have "`(p \<Rightarrow> Q) ; R` = `\<not> p ; R \<or> (Q ; R)`"
    by (metis ImpliesP_def SemiR_OrP_distr)

  also have "... = `(\<not> p ; true) ; R \<or> (Q ; R)`"
    by (metis NotP_cond_closure SemiR_TrueP_precond assms(1))

  also have "... = `\<not> p \<or> (Q ; R)`"
    by (metis H1_left_zero SemiR_assoc assms SemiR_condition_comp utp_pred_simps(3))

  ultimately show ?thesis
    by (metis ImpliesP_def)

qed

theorem SemiR_is_H1:
  assumes "P is H1" "Q is H1"
  shows "`P ; Q` is H1"
proof -
  have "`H1(P ; Q)` = `$ok \<Rightarrow> (P ; Q)`"
    by (metis H1_def)

  also have "... = `($ok \<Rightarrow> P) ; Q`"
    by (simp add:H1_ImpliesP_SemiR[THEN sym] assms(2) closure)

  finally show ?thesis using assms
    by (simp add:is_healthy_def H1_def)
qed

theorem H1_idempotent:
  "H1 (H1 p) = H1 p"
  by (rule, simp add:H1_def eval)

theorem H1_monotone:
  "p \<sqsubseteq> q \<Longrightarrow> H1 p \<sqsubseteq> H1 q"
  by (utp_pred_tac)

subsection {* H2: No requirement of non-termination *}

definition "H2(P) = `P ; J`"

declare H2_def [eval,evalr,evalrx,evalp]

theorem J_split:
  "`P ; J` = `P\<^sup>f \<or> (P\<^sup>t \<and> $ok\<acute>)`"
proof -

  let ?vs = "(REL_VAR - OKAY) :: 'a uvar set"

  have "`P ; J` = `P ; (($ok \<Rightarrow> $ok\<acute>) \<and> II\<^bsub>?vs\<^esub>)`"
    by (simp add:JA_pred_def)

  also have "... = `P ; (($ok \<Rightarrow> $ok \<and> $ok\<acute>) \<and> II\<^bsub>?vs\<^esub>)`"
    by (metis ImpliesP_export)

  also have "... = `P ; ((\<not> $ok \<or> ($ok \<and> $ok\<acute>)) \<and> II\<^bsub>?vs\<^esub>)`"
    by (utp_rel_auto_tac)

  also have "... = `(P ; (\<not> $ok \<and> II\<^bsub>?vs\<^esub>)) \<or> (P ; ($ok \<and> (II\<^bsub>?vs\<^esub> \<and> $ok\<acute>)))`"
    by (smt AndP_OrP_distr AndP_assoc AndP_comm SemiR_OrP_distl)
    
  also have "... = `P\<^sup>f \<or> (P\<^sup>t \<and> $ok\<acute>)`"
  proof -
    from assms have "`(P ; (\<not> $ok \<and> II\<^bsub>?vs\<^esub>))` = `P\<^sup>f`"
      by (simp add: VarP_NotP_EqualP_aux SemiR_left_one_point closure typing defined unrest urename usubst SemiR_SkipRA_right var_dist erasure)

    moreover have "`(P ; ($ok \<and> (II\<^bsub>?vs\<^esub> \<and> $ok\<acute>)))` = `(P\<^sup>t \<and> $ok\<acute>)`"
    proof -
      have "`(P ; ($ok \<and> (II\<^bsub>?vs\<^esub> \<and> $ok\<acute>)))` = `(P ; ($ok \<and> II\<^bsub>?vs\<^esub>)) \<and> $ok\<acute>`"
        apply (insert SemiR_TrueP_postcond[OF VarP_precond_closure[of "ok\<down>\<acute>",simplified]])
        apply (subst AndP_assoc)
        apply (subst SemiR_AndP_right_UNDASHED) 
        apply (simp add:unrest typing defined closure)
        apply (simp)
     done

      moreover from assms have "`(P ; ($ok \<and> II\<^bsub>?vs\<^esub>))` =  `P\<^sup>t`"
        by (simp add: VarP_EqualP_aux SemiR_left_one_point closure typing defined unrest urename usubst SemiR_SkipRA_right var_dist erasure)
     
      finally show ?thesis .
    qed

    ultimately show ?thesis by (simp)
  qed

  finally show ?thesis .
qed

theorem J_split_alt: "`P ; J` = `P\<^sup>f \<or> (P \<and> $ok\<acute>)`"
  by (subst J_split, utp_poly_auto_tac)

theorem H2_split:
  "`H2(P)` = `P\<^sup>f \<or> (P\<^sup>t \<and> $ok\<acute>)`"
  by (metis H2_def J_split)

theorem H2_equivalence:
  "P is H2 \<longleftrightarrow> `P\<^sup>f \<Rightarrow> P\<^sup>t`"
proof -
  have "`[P \<Leftrightarrow> (P ; J)]` = `[P \<Leftrightarrow> (P\<^sup>f \<or> (P\<^sup>t \<and> $ok\<acute>))]`"
    by (simp add:J_split)

  also have "... = `[(P \<Leftrightarrow> P\<^sup>f \<or> P\<^sup>t \<and> $ok\<acute>)\<^sup>f \<and> (P \<Leftrightarrow> P\<^sup>f \<or> P\<^sup>t \<and> $ok\<acute>)\<^sup>t]`"
    by (simp add: ucases erasure)

  also have "... = `[(P\<^sup>f \<Leftrightarrow> P\<^sup>f) \<and> (P\<^sup>t \<Leftrightarrow> P\<^sup>f \<or> P\<^sup>t)]`"
    by (simp add:usubst closure typing defined erasure)

  also have "... = `[P\<^sup>t \<Leftrightarrow> (P\<^sup>f \<or> P\<^sup>t)]`"
    by (utp_pred_tac)

  ultimately show ?thesis
    by (utp_pred_auto_tac)
qed

theorem H2_equivalence_ref:
  "P is H2 \<longleftrightarrow> P\<^sup>t \<sqsubseteq> P\<^sup>f"
  by (simp add:H2_equivalence assms less_eq_upred_def RefP_def)

theorem J_is_H2:
  "H2(J) = J"
proof -
  have "H2(J) = `J\<^sup>f \<or> (J\<^sup>t \<and> $ok\<acute>)`"
    by (simp add:H2_def closure J_split)

  also have "... = `((\<not> $ok \<and> II\<^bsub>(REL_VAR - OKAY)\<^esub>) \<or> II\<^bsub>(REL_VAR - OKAY)\<^esub> \<and> $ok\<acute>)`"
    by (simp add:JA_pred_def usubst typing defined closure erasure)

  also have "... = `(\<not> $ok \<or> $ok\<acute>) \<and> II\<^bsub>REL_VAR - OKAY\<^esub>`"
    by (utp_pred_auto_tac)

  also have "... = `($ok \<Rightarrow> $ok\<acute>) \<and> II\<^bsub>REL_VAR - OKAY\<^esub>`"
    by (utp_pred_tac)

  ultimately show ?thesis
    by (metis JA_pred_def)
qed

theorem J_idempotent [simp]: "`J ; J` = J"
  by (simp add:H2_def[THEN sym] J_is_H2)

theorem H2_idempotent:
  "H2 (H2 p) = H2 p"
  apply (simp add:H2_def)
  apply (metis J_idempotent SemiR_assoc)
done

theorem H2_monotone:
  "p \<sqsubseteq> q \<Longrightarrow> H2 p \<sqsubseteq> H2 q"
  by (utp_rel_auto_tac)

theorem H2_DesignD:
  "{ok\<down>\<acute>} \<sharp> P \<Longrightarrow> H2(P \<turnstile> Q) = P \<turnstile> Q"
  apply (simp add: H2_def J_split DesignD_def usubst typing closure defined)
  apply (utp_poly_auto_tac)
done

theorem DesignD_is_H2 [closure]:
  "{ok\<down>\<acute>} \<sharp> P \<Longrightarrow> P \<turnstile> Q is H2"
  by (metis H2_DesignD Healthy_intro)

theorem H1_H2_commute: "H1 (H2 P) = H2 (H1 P)"
  apply (simp add:H1_def H2_def ImpliesP_def)
  apply (smt DesignD_is_H2 FalseP_rel_closure H2_def SemiR_OrP_distr TrueP_rel_closure UNREST_FalseP UNREST_TrueP DesignD_extreme_point_nok is_healthy_def)
done

theorem H1_H2_is_DesignD:
  assumes "P is H1" "P is H2"
  shows "P = `\<not>P\<^sup>f \<turnstile> P\<^sup>t`"
proof -
  from assms have "P = `$ok \<Rightarrow> P`"
    by (utp_pred_tac)
  also from assms have "... = `$ok \<Rightarrow> H2(P)`"
    by (utp_pred_tac)
  also have "... = `$ok \<Rightarrow> (P\<^sup>f \<or> (P\<^sup>t \<and> $ok\<acute>))`"
    by (metis H2_split assms)
  also have "... = `$ok \<and> (\<not> P\<^sup>f) \<Rightarrow> $ok\<acute> \<and> P\<^sup>t`"
    by (utp_pred_auto_tac)
  also have "... = `(\<not> P\<^sup>f) \<turnstile> P\<^sup>t`"
    by (metis DesignD_def)
  finally show ?thesis .
qed

theorem H1_H2_is_DesignD':
  assumes "P is H1" "P is H2"
  shows "P = `\<not>P\<^bsup>tf\<^esup> \<turnstile> P\<^bsup>tt\<^esup>`"
  apply (subst H1_H2_is_DesignD)
  apply (simp_all add: assms)
  apply (simp add: DesignD_def)
  apply (utp_poly_auto_tac)
done

theorem H2_AndP_closure:
  assumes "P is H2" "Q is H2"
  shows "`P \<and> Q` is H2"
  using assms
  apply (simp add:H2_equivalence closure usubst)
  apply (utp_pred_auto_tac)
done

theorem H1_J: "`H1(J)` = II\<^sub>D"
  by (utp_pred_tac)

theorem H2_TrueP: "`H2(true)` = true"
  apply (subst DesignD_extreme_point_true(2)[THEN sym])
  apply (simp add: H2_DesignD unrest)
  apply (utp_pred_tac)
done

theorem H2_FalseP: "`H2(false)` = false"
  by (utp_pred_tac)

theorem H2_TopD: "`H2(\<top>\<^sub>D)` = `\<top>\<^sub>D`"
  apply (subst DesignD_extreme_point_nok(2)[THEN sym])
  apply (subst DesignD_extreme_point_nok(1)[THEN sym])
  apply (simp add: H2_DesignD unrest)  
  apply (utp_pred_auto_tac)
done

theorem H2_OrP:
  "`H2(P \<or> Q)` = `H2(P) \<or> H2(Q)`"
  by (simp add:H2_def SemiR_OrP_distr)

lemma H2_OrDistP:
  "H2(\<Or>\<^sub>p ps) = \<Or>\<^sub>p {H2(p) | p. p \<in> ps}"
  by (simp add:H2_def OrDistP_SemiR_dist)

lemma H2_OrDistP_closure:
  assumes "\<forall>p\<in>ps. p is H2"
  shows "\<Or>\<^sub>p ps is H2"
  apply (simp add: is_healthy_def H2_OrDistP)
  apply (subgoal_tac "{H2 p |p. p \<in> ps} = ps")
  apply (simp)
  apply (insert assms)
  apply (auto simp add:is_healthy_def, metis)
done

lemma H2_AndDistP_closure:
  assumes "ps \<subseteq> WF_RELATION" "\<forall>p\<in>ps. p is H2"
  shows "\<And>\<^sub>p ps is H2"
proof -
  from assms have "\<forall>p\<in>ps. p\<^sup>t \<sqsubseteq> p\<^sup>f"
    by (force simp add:H2_equivalence_ref)

  with assms(1) show ?thesis
    apply (simp add: H2_equivalence_ref closure usubst assms(1))
    apply (simp add: Inf_upred_def[THEN sym])
    apply (auto intro: Inf_mono)
  done
qed

theorem H2_CondR:
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "c \<in> WF_CONDITION"
  shows "`H2(P \<lhd> c \<rhd> Q)` = `H2(P) \<lhd> c \<rhd> H2(Q)`"
  by (simp add:H2_def CondR_SemiR_distr assms closure)

theorem H2_SemiR:
  "`H2(P ; Q)` = `P ; H2(Q)`"
  by (simp add:H2_def SemiR_assoc)

theorem SemiR_is_H2:
  "Q is H2 \<Longrightarrow> `P ; Q` is H2"
  by (metis H2_SemiR Healthy_intro Healthy_simp)

text {* H1 and H2 can be distinguished by the following counterexample *}

abbreviation "NoTerminate \<equiv> `$ok \<Rightarrow> \<not> $ok\<acute>`"

theorem NoTerminate_H1: 
  "NoTerminate is H1"
  by (utp_pred_auto_tac)

theorem NoTerminate_not_H2:
  "\<not> (NoTerminate is H2)"
  apply (simp add:H2_equivalence closure usubst typing defined)
  apply (utp_poly_tac)
  apply (rule_tac x="\<B>(ok :=\<^sub>* True)" in exI, simp add:typing defined inju)
done

subsection {* H3: Assumption is a condition *}

definition "H3(P) = `P ; II\<^sub>D`"
declare H3_def [eval,evalr,evalrx,evalp]

theorem SkipD_idempotent:
  "`II\<^sub>D ; II\<^sub>D` = `II\<^sub>D`"
  by (utp_xrel_auto_tac)

theorem H3_idempotent:
  "H3 (H3 p) = H3 p"
  by (metis (hide_lams, no_types) H3_def SemiR_assoc SkipD_idempotent)

theorem H3_monotone:
  "p \<sqsubseteq> q \<Longrightarrow> H3 p \<sqsubseteq> H3 q"
  by (utp_rel_auto_tac)

theorem H3_WF_CONDITION: 
  assumes "P \<in> WF_CONDITION"
  shows "P is H3"
proof -
  from assms have "`P ; II\<^sub>D` = `P ; (true ; II\<^sub>D)`"
    by (metis SemiR_TrueP_precond SemiR_assoc)

  also have "... = `P ; true`"
    by (metis H1_left_zero SkipD_is_H1 SkipD_rel_closure)

  finally show ?thesis
    by (metis H3_def Healthy_intro SemiR_TrueP_precond assms)
qed

theorem H3_DesignD_precondition:
  assumes 
    "{ok\<down>\<acute>} \<sharp> p" "{ok\<down>\<acute>} \<sharp> Q"
    "p \<in> WF_CONDITION" "Q \<in> WF_RELATION"
  shows "H3(p \<turnstile> Q) = p \<turnstile> Q"
proof -
  have "`(p \<turnstile> Q) ; II\<^sub>D` = `(p \<turnstile> Q) ; (true \<turnstile> II\<^bsub>REL_VAR - OKAY\<^esub>)`"
    by (simp add:SkipDA_def)

  also from assms have "... = `p \<turnstile> (Q ; II\<^bsub>REL_VAR - OKAY\<^esub>)`"
    by (simp add:DesignD_composition_cond closure unrest)

  also have "... = `p \<turnstile> Q`"
    by (simp add:SemiR_SkipRA_right closure assms unrest var_dist)
    
  finally show ?thesis 
    by (simp add:H3_def is_healthy_def)
qed

theorem DesignD_precondition_H3 [closure]:
  assumes 
    "{ok\<down>\<acute>} \<sharp> p" "{ok\<down>\<acute>} \<sharp> Q"
    "p \<in> WF_CONDITION" "Q \<in> WF_RELATION"
  shows "(p \<turnstile> Q) is H3"
  by (simp add:assms H3_DesignD_precondition is_healthy_def)

theorem H3_OrP: "`H3(P \<or> Q)` = `H3(P) \<or> H3(Q)`"
  by (simp add:H3_def SemiR_OrP_distr)

lemma DesignD_neg_assumption:
  "OKAY \<sharp> P \<Longrightarrow> `(P \<turnstile> Q)[false/ok\<acute>]` = `\<not> ($ok \<and> P)`"
  by (simp add:DesignD_def usubst typing defined)

lemma SkipD_neg_assump: "`II\<^sub>D[false/ok\<acute>]` = `\<not> $ok`"
  by (simp only:SkipDA_def DesignD_neg_assumption unrest, simp)

lemma H3_neg_assm:
  assumes "P is H3"
  shows "`P[false/ok\<acute>]` = `P ; \<top>\<^sub>D`"
proof -
  have "`P[false/ok\<acute>]` = `(P ; II\<^sub>D)[false/ok\<acute>]`"
    by (metis H3_def Healthy_simp assms)

  also have "... = `(P ; \<not> $ok)`"
    by (simp only:usubst closure typing defined unrest SkipD_neg_assump)

  finally show ?thesis by (simp add:TopD_def)
qed


theorem H1_H3_commute: "H1 (H3 P) = H3 (H1 P)"
  apply (simp add:H1_def H3_def ImpliesP_def SemiR_OrP_distr TopD_def[THEN sym])
  apply (metis H3_WF_CONDITION H3_def Healthy_simp TopD_cond_closure)
done

theorem SkipD_absorbs_J_1 [simp]: 
  "`II\<^sub>D ; J` = `II\<^sub>D`"
  by (utp_xrel_auto_tac)

theorem H3_absorbs_H2_1:
  "H2 (H3 P) = H3 P"
  by (simp add:H2_def H3_def SemiR_assoc[THEN sym])

theorem SkipD_absorbs_J_2 [simp]:
  "`J ; II\<^sub>D` = `II\<^sub>D`"
  by (utp_xrel_auto_tac)

theorem H3_absorbs_H2_2:
  "H3 (H2 P) = H3 P"
  by (simp add:H2_def H3_def SemiR_assoc[THEN sym])

theorem H3_implies_H2:
  "P is H3 \<Longrightarrow> P is H2"
  by (metis H3_absorbs_H2_1 is_healthy_def)

theorem H3_assm_UNREST_DASHED:
  assumes "P is H3"
  shows "D\<^sub>1 \<sharp> P\<^sup>f"
proof -
  have "`P\<^sup>f` = `(P ; \<top>\<^sub>D)`"
    by (metis H3_neg_assm assms)

  thus ?thesis
    by (metis H1_TopD_left_zero H1_true SemiR_assoc TrueP_right_UNREST_DASHED)
qed

theorem H3_assm_CONDITION [closure]:
  assumes "P \<in> WF_RELATION" "P is H3"
  shows "P\<^sup>f \<in> WF_CONDITION"
  by (metis H3_neg_assm SemiR_second_CONDITION TopD_cond_closure assms)

theorem H1_H3_is_DesignD:
  assumes "P is H1" "P is H3"
  shows "P = `\<not>P\<^sup>f \<turnstile> P\<^sup>t`"
  by (metis H1_H2_is_DesignD H3_implies_H2 assms)

theorem H1_H3_is_DesignD':
  assumes "P is H1" "P is H3"
  shows "P = `\<not>P\<^bsup>tf\<^esup> \<turnstile> P\<^bsup>tt\<^esup>`"
  by (metis H1_H2_is_DesignD' H3_implies_H2 assms)

theorem AndP_is_H3:
  assumes 
    "P \<in> REL" "Q \<in> REL"
    "P is H1" "Q is H1" "P is H3" "Q is H3"
  shows "`P \<and> Q` is H3"
proof -
  have "`P \<and> Q` = `(\<not>P\<^sup>f \<turnstile> P\<^sup>t) \<and> (\<not>Q\<^sup>f \<turnstile> Q\<^sup>t)`"
    by (metis H1_H3_is_DesignD assms)

  also have "... = `(\<not>P\<^sup>f \<or> \<not>Q\<^sup>f) \<turnstile> (\<not>P\<^sup>f \<Rightarrow> P\<^sup>t) \<and> (\<not>Q\<^sup>f \<Rightarrow> Q\<^sup>t)`"
    by (simp add: DesignD_AndP)

  also have "... = `H3((\<not>P\<^sup>f \<or> \<not>Q\<^sup>f) \<turnstile> (\<not>P\<^sup>f \<Rightarrow> P\<^sup>t) \<and> (\<not>Q\<^sup>f \<Rightarrow> Q\<^sup>t))`"
    apply (subst H3_DesignD_precondition)
    apply (simp_all add: assms unrest closure defined typing)
    apply (metis H3_assm_CONDITION NotP_cond_closure OrP_cond_closure PVAR_VAR_pvdash assms)
  done

  ultimately show ?thesis
     by (metis Healthy_intro)
qed

theorem AndDistP_is_H3:
  assumes 
    "ps \<subseteq> WF_RELATION"
    "\<forall> p\<in>ps. p is H1" 
    "\<forall> p\<in>ps. p is H3" 
    "ps \<noteq> {}"
  shows "(\<And>\<^sub>p ps) is H3"
proof -
  from assms have "ps = {`\<not>p\<^sup>f \<turnstile> p\<^sup>t` | p. p \<in> ps}"
    by (auto, (metis H1_H3_is_DesignD PVAR_VAR_pvdash)+)

  moreover have "(\<And>\<^sub>p {`\<not>p\<^sup>f \<turnstile> p\<^sup>t` | p. p \<in> ps}) = (\<And>\<^sub>p p:ps. `\<not>p\<^sup>f \<turnstile> p\<^sup>t`)"
    apply (simp only: ANDI_def)
    apply (rule cong[of AndDistP])
    apply (auto)
  done

  moreover have "... = `(\<Or> p:ps. \<not>p\<^sup>f) \<turnstile> (\<And> p:ps. \<not>p\<^sup>f \<Rightarrow> p\<^sup>t)`"
    by (simp add: DesignD_AndDistP assms(4))

  moreover from assms have "... = `H3((\<Or> p:ps. \<not>p\<^sup>f) \<turnstile> (\<And> p:ps. \<not>p\<^sup>f \<Rightarrow> p\<^sup>t))`"
    apply (rule_tac H3_DesignD_precondition[THEN sym])
    apply (simp add:typing defined unrest closure)
    apply (simp add:typing defined unrest closure)
    apply (rule closure)
    apply (rule closure)
    apply (rule closure)
    apply (force)
    apply (force)
    apply (rule closure)
    apply (rule closure)
    apply (rule closure)
    apply (rule closure)
    apply (simp_all add:closure unrest typing defined)
    apply (force)
    apply (rule closure) 
    apply (force)
    apply (simp add:unrest typing defined)
    apply (simp add:closure)
    apply (simp add:typing defined)
  done

  ultimately show ?thesis
    by (metis Healthy_intro)
qed

text {* H2-H3 commutivity is vacuously true *}

theorem H2_H3_commute: "H2 (H3 P) = H3 (H2 P)"
  by (metis H3_absorbs_H2_1 H3_absorbs_H2_2)

subsection {* H4: Feasibility *}

definition "H4(P) = `(P ; true) \<Rightarrow> P`"

definition "isH4(P) \<equiv> `P ; true` = `true`"

declare H4_def [eval,evalr,evalrx,evalp]
declare isH4_def [eval,evalr,evalrx,evalp]

theorem H4_idempotent: "H4 (H4 P) = H4 P"
  by (utp_rel_tac)

theorem H4_equiv: "P \<in> WF_RELATION \<Longrightarrow> P is H4 \<longleftrightarrow> isH4(P)"
  by (utp_xrel_auto_tac)

text {* This lemma shows intuitively what H4 means: there exists an output
        for every input. *}

lemma H4_soundness:
  assumes "P \<in> WF_RELATION"
  shows "P is H4 \<longleftrightarrow> (\<exists>\<^sub>p DASHED. P)" 
proof -
  have "P is H4 \<longleftrightarrow> (`P ; true` = `true`)"
    by (simp add:H4_equiv assms isH4_def)

  moreover have "`P ; true` = (\<exists>\<^sub>p DASHED. P)"
    by (metis TrueP_right_ExistsP)

  finally show ?thesis by (utp_pred_tac)
qed

theorem SkipR_is_H4 [closure]:
  "II is H4"
  by (simp add:is_healthy_def H4_def)
theorem SkipR_not_H1: 
  "\<not> (II is H1)"
proof -
  have "`$ok \<Rightarrow> II` = (`II` :: 'a upred) \<longleftrightarrow> (`true` :: 'a upred) = `II[false/ok]`"
    by (unfold BoolType_pvaux_cases[of "ok" "`$ok \<Rightarrow> II`" "II", simplified], utp_subst_tac)

  moreover have "`II[false/ok]` = `($ok\<acute> = $ok \<and> II\<^bsub>REL_VAR - OKAY\<^esub>)[false/ok]`"
    by (simp add: SkipR_as_SkipRA SkipRA_unfold[of "ok\<down>"] typing defined closure erasure)
    
  also have "... = `$ok\<acute> = false \<and> II\<^bsub>REL_VAR - OKAY\<^esub>`"
    by (utp_subst_tac)

  also have "... \<noteq> true"
    apply (utp_poly_auto_tac)
    apply (rule_tac x="\<B>(ok\<acute> :=\<^sub>* True)" in exI)
    apply (simp add:typing defined inju)
  done

  ultimately show ?thesis
    by (simp add:is_healthy_def H1_def, metis)
qed

theorem SkipD_is_H4 [closure]:
  "II\<^sub>D is H4"
  by (utp_xrel_auto_tac)

text {* No condition other than true is feasible *}

theorem H4_condition:
  "p \<in> WF_CONDITION \<Longrightarrow> H4(p) = true"
  by (simp add:H4_def SemiR_TrueP_precond)

theorem H4_TopD:
  "H4(\<top>\<^sub>D) = true"
  by (simp add:H4_def SemiR_TrueP_precond closure)

theorem TopD_not_H4: 
  "\<not> \<top>\<^sub>D is H4"
  by (simp add:is_healthy_def H4_TopD)

theorem H1_H4_commute:
  "P \<in> WF_RELATION \<Longrightarrow> H1(H4(P)) = H4(H1(P))"
  by (utp_xrel_auto_tac)

theorem H2_H4_commute:
  "P \<in> WF_RELATION \<Longrightarrow> H2(H4(P)) = H4(H2(P))"
  by (utp_xrel_auto_tac)

theorem H3_H4_commute:
  assumes "P \<in> WF_RELATION"
  shows "H3(H4(P)) = H4(H3(P))"
proof -
  have "H4(H3(P)) = `((P ; II\<^sub>D) ; true \<Rightarrow> P ; II\<^sub>D)`" 
    by (simp add:H3_def H4_def)

  also have "... = `(P ; true) \<Rightarrow> P ; II\<^sub>D`"
    by (metis H1_left_unit H1_true SemiR_assoc TrueP_rel_closure)

  also have "... = `\<not> (P ; true) \<or> P ; II\<^sub>D`"
    by (metis ImpliesP_def)
    
  also have "... = `\<not> (P ; true) ; true \<or> P ; II\<^sub>D`"
    by (metis SemiR_TrueP_compl assms)

  also have "... = `\<not> (P ; true) ; (true ; II\<^sub>D) \<or> P ; II\<^sub>D`"
    by (metis H1_left_zero SkipD_is_H1 SkipD_rel_closure)

  also have "... = `\<not> (P ; true) ; II\<^sub>D \<or> P ; II\<^sub>D`"
    by (metis SemiR_TrueP_compl SemiR_assoc assms)

  also have "... = `(\<not> (P ; true) \<or> P) ; II\<^sub>D`"
    by (metis SemiR_OrP_distr)

  finally show ?thesis
    by (metis H3_def H4_def ImpliesP_def)
qed
    
theorem H4_top: "true \<turnstile> true is H4"
  by (utp_xrel_auto_tac)
end
