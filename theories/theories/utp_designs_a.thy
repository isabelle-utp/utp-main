theory utp_designs_a
imports utp_designs
begin

definition DESIGN_ALPHABET :: "'a ALPHABET set" where
"DESIGN_ALPHABET = {a \<in> REL_ALPHABET. \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace> \<subseteq>\<^sub>f a}"

lemma REL_ALPHABET_DESIGN_ALPHABET [closure]:
  "a \<in> DESIGN_ALPHABET \<Longrightarrow> a \<in> REL_ALPHABET"
  by (simp add:DESIGN_ALPHABET_def)

lemma DESIGN_ALPHABET_ok [closure]:
  "a \<in> DESIGN_ALPHABET \<Longrightarrow> okay\<down> \<in> \<langle>a\<rangle>\<^sub>f"
  by (auto simp add:DESIGN_ALPHABET_def)

lemma DESIGN_ALPHABET_ok' [closure]:
  "a \<in> DESIGN_ALPHABET \<Longrightarrow> okay\<down>\<acute> \<in> \<langle>a\<rangle>\<^sub>f"
  by (auto simp add:DESIGN_ALPHABET_def)

lift_definition DesignA :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 
   'a WF_ALPHA_PREDICATE \<Rightarrow> 
   'a WF_ALPHA_PREDICATE" (infixr "\<turnstile>\<^sub>\<alpha>" 60)
is "\<lambda> P Q. (\<alpha> P \<union>\<^sub>f \<alpha> Q \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>, (\<pi> P) \<turnstile> (\<pi> Q))"
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (auto intro:unrest)
done

definition SkipDA :: "'a ALPHABET \<Rightarrow> 'a WF_ALPHA_PREDICATE" where
"SkipDA a = true\<^bsub>a\<^esub> \<turnstile>\<^sub>\<alpha> II\<alpha>\<^bsub>a -\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>\<^esub>"

notation SkipDA ("II\<^bsub>D[_]\<^esub>")

lift_definition AH1 :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 
   'a WF_ALPHA_PREDICATE"
is "\<lambda> P. (\<alpha> P \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>, H1(\<pi> P))"
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def H1_def)
  apply (auto intro:unrest)
done

lift_definition AH2 :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 
   'a WF_ALPHA_PREDICATE"
is "\<lambda> P. (\<alpha> P \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>, H2(\<pi> P))"
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def H2_def)
oops

lemma REL_ALPHABET_in_alpha [closure]: "in\<^sub>\<alpha>a \<in> REL_ALPHABET"
  by (auto simp add:REL_ALPHABET_def var_defs)

lemma REL_ALPHABET_out_alpha [closure]: "out\<^sub>\<alpha>a \<in> REL_ALPHABET"
  by (auto simp add:REL_ALPHABET_def var_defs)

lemma DesignA_alphabet [alphabet]:
  "\<alpha> (P \<turnstile>\<^sub>\<alpha> Q) = \<alpha> P \<union>\<^sub>f \<alpha> Q \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>"
  by (simp add:DesignA.rep_eq pred_alphabet_def)

lemma DesignA_evala [evala]:
  "\<lbrakk>P \<turnstile>\<^sub>\<alpha> Q\<rbrakk>\<pi> = \<lbrakk>P\<rbrakk>\<pi> \<turnstile> \<lbrakk>Q\<rbrakk>\<pi>"
  by (simp add:EvalA_def DesignA.rep_eq)

lemma DesignA_rel_closure [closure]:
  "\<lbrakk> P \<in> WF_ALPHA_REL; Q \<in> WF_ALPHA_REL \<rbrakk> \<Longrightarrow> P \<turnstile>\<^sub>\<alpha> Q \<in> WF_ALPHA_REL"
  apply (simp add:WF_ALPHA_REL_def REL_ALPHABET_def alphabet)
  apply (simp add:closure)
done

lemma SkipDA_alphabet [alphabet]:
  "a \<in> REL_ALPHABET \<Longrightarrow>
   \<alpha>(II\<^bsub>D[a]\<^esub>) = a \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>"
  by (auto simp add:SkipDA_def alphabet closure)

lemma SkipDA_rel_closure [closure]:
  "a \<in> REL_ALPHABET \<Longrightarrow> II\<^bsub>D[a]\<^esub> \<in> WF_ALPHA_REL"
  apply (simp add:WF_ALPHA_REL_def REL_ALPHABET_def alphabet)
  apply (simp add:closure)
done

lemma AH1_alphabet [alphabet]:
  "\<alpha>(AH1(P)) = \<alpha> P \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>"
  by (simp add:AH1.rep_eq pred_alphabet_def)

lemma EvalA_AH1 [evala]:
  "\<lbrakk>AH1(P)\<rbrakk>\<pi> = H1\<lbrakk>P\<rbrakk>\<pi>"
  by (simp add:EvalA_def AH1.rep_eq)

lemma WF_ALPHA_REL_EvalA_WF_RELATION [closure]:
  "P \<in> WF_ALPHA_REL \<Longrightarrow> \<lbrakk>P\<rbrakk>\<pi> \<in> WF_RELATION"
  apply (simp add:WF_ALPHA_REL_def WF_RELATION_def REL_ALPHABET_def)
  apply (rule UNREST_subset)
  apply (rule unrest) back back back
  apply (auto)
done

lemma UNREST_OKAY_alpha [unrest]: "\<lbrakk> okay\<down> \<notin>\<^sub>f \<alpha> P; okay\<down>\<acute> \<notin>\<^sub>f \<alpha> P \<rbrakk> \<Longrightarrow> OKAY \<sharp> \<lbrakk>P\<rbrakk>\<pi>"
  apply (rule UNREST_subset)
  apply (rule EvalA_UNREST)
  apply (auto)
done

theorem DesignA_composition:
  assumes 
  "P1 \<in> WF_ALPHA_REL" "P2 \<in> WF_ALPHA_REL"
  "Q1 \<in> WF_ALPHA_REL" "Q2 \<in> WF_ALPHA_REL"
  "okay\<down> \<notin>\<^sub>f \<alpha> P1" "okay\<down>\<acute> \<notin>\<^sub>f \<alpha> P1"
  "okay\<down> \<notin>\<^sub>f \<alpha> P2" "okay\<down>\<acute> \<notin>\<^sub>f \<alpha> P2"
  "okay\<down> \<notin>\<^sub>f \<alpha> Q1" "okay\<down>\<acute> \<notin>\<^sub>f \<alpha> Q1"
  "okay\<down> \<notin>\<^sub>f \<alpha> Q2" "okay\<down>\<acute> \<notin>\<^sub>f \<alpha> Q2"
  shows "(P1 \<turnstile>\<^sub>\<alpha> Q1) ;\<^sub>\<alpha> (P2 \<turnstile>\<^sub>\<alpha> Q2) = ((\<not>\<^sub>\<alpha> ((\<not>\<^sub>\<alpha> P1) ;\<^sub>\<alpha> true\<^bsub>in\<^sub>\<alpha> (\<alpha> P1)\<^esub>)) \<and>\<^sub>\<alpha> \<not>\<^sub>\<alpha> (Q1 ;\<^sub>\<alpha> (\<not>\<^sub>\<alpha> P2))) \<turnstile>\<^sub>\<alpha> (Q1 ;\<^sub>\<alpha> Q2)"
  using assms
  apply (utp_alpha_tac)
  apply (rule conjI)
  apply (simp add:alphabet_dist closure)
  defer
  apply (subst DesignD_composition)
  apply (simp_all add:closure unrest)
  apply (auto)[1]
done

lemma AH1_DesignA:
  assumes "okay\<down> \<notin>\<^sub>f \<alpha> P" "okay\<down>\<acute> \<notin>\<^sub>f \<alpha> P"
          "okay\<down> \<notin>\<^sub>f \<alpha> Q" "okay\<down>\<acute> \<notin>\<^sub>f \<alpha> Q"
  shows "AH1(P \<turnstile>\<^sub>\<alpha> Q) = P \<turnstile>\<^sub>\<alpha> Q"
  by (utp_alpha_tac, utp_pred_auto_tac)

lemma finsert_member [simp]: "x \<in>\<^sub>f xs \<Longrightarrow> finsert x xs = xs"
  by auto

lemma EvalR_ExprP'':
  "\<lbrakk>ExprP e\<rbrakk>R = {(b1, b2). DestBool (\<lbrakk>e\<rbrakk>\<^sub>e (b1 \<oplus>\<^sub>b SS\<bullet>b2 on D\<^sub>1))
                        \<and> b1 \<in> WF_REL_BINDING 
                        \<and> b2 \<in> WF_REL_BINDING
                        \<and> b1 \<cong> b2 on NON_REL_VAR}"
  apply (auto simp add:evalr evale BindR_def urename RenameB_override_distr1 closure typing defined)
  apply (metis RenameB_equiv_VAR_RENAME_ON_2 SS_VAR_RENAME_ON UNDASHED_DASHED_inter(16) binding_override_left_eq)
  apply (rule_tac x="xa \<oplus>\<^sub>b SS\<bullet>y on D\<^sub>1" in exI)
  apply (auto)
  apply (metis WF_REL_BINDING_bc_DASHED_eq binding_override_equiv)
  apply (simp add:urename RenameB_override_distr1 closure)
  apply (metis (hide_lams, no_types) NON_REL_VAR_UNDASHED_DASHED SS_REL_VAR_overshadow WF_REL_BINDING_bc_DASHED_eq binding_equiv_override binding_override_assoc binding_override_minus binding_override_simps(2))
done

theorem undash_image_inter:
  assumes "vs1 \<subseteq> DASHED" "vs2 \<subseteq> DASHED"
  shows "undash ` (vs1 \<inter> vs2) = undash ` vs1 \<inter> undash ` vs2"
  using assms
  by (auto, metis IntI UnI1 Un_absorb1 dash_undash_DASHED imageI)

(*
theorem 
  assumes
  "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  "VAR - vs1 \<sharp> P"
  "VAR - vs2 \<sharp> Q"
  "vs1 \<subseteq> vs2"
  shows "P ; Q = P ; (\<exists>\<^sub>p vs2 - vs1. Q)"
  apply (subgoal_tac "(\<exists>\<^sub>p vs2 - vs1 . Q) \<in> WF_RELATION")
  apply (simp add:SemiR_algebraic_rel assms urename closure typing defined)
*)

theorem SkipRA_left_to_ExistsP:
  assumes 
    "p \<in> WF_RELATION" 
    "HOMOGENEOUS vs2"
    "vs2 \<subseteq> REL_VAR"
    "vs1 \<subseteq> UNDASHED"
    "out vs2 \<subseteq> dash ` vs1"
    "UNDASHED - vs1 \<sharp> p"
  shows "II\<^bsub>vs2\<^esub> ; p = (\<exists>\<^sub>p vs1 - in vs2. p)"
  using assms
  apply (subst SemiR_ExistsP_right[THEN sym, of _ _ "out vs2" "vs1"])
  apply (simp_all add:unrest closure)
  apply (auto intro:UNREST_subset unrest)[1]
  apply (subst SemiR_SkipRA_left)
  apply (simp_all add:unrest closure var_dist)
  apply (rule unrest)
  apply (rule UNREST_subset)
  apply (simp)
  apply (auto)[1]
  apply (rule unrest)
  apply (rule UNREST_subset)
  apply (simp)
  apply (auto)[1]
done

lemma WF_RELATION_REL_ALPHABET [closure]: 
  "\<alpha> P \<in> REL_ALPHABET \<Longrightarrow> \<lbrakk>P\<rbrakk>\<pi> \<in> WF_RELATION"
  by (auto intro:closure simp add:WF_ALPHA_REL_def)

lemma [simp]: "a \<in> REL_ALPHABET \<Longrightarrow> (in\<^sub>\<alpha> a) \<union>\<^sub>f (out\<^sub>\<alpha> a) = a"
  by (metis REL_ALPHABET_UNDASHED_DASHED alphabet_simps(14))

thm SkipRA_closure

lemma SkipRA_closure' [closure]:
  "a \<in> REL_ALPHABET \<Longrightarrow> II\<^bsub>\<langle>a\<rangle>\<^sub>f\<^esub> \<in> WF_RELATION"
  by (metis EvalA_SkipA SkipA_closure WF_ALPHA_REL_EvalA_WF_RELATION)
 
lemma HOMOGENEOUS_HOM_ALPHA [closure]:
  "a \<in> HOM_ALPHABET \<Longrightarrow> HOMOGENEOUS \<langle>a\<rangle>\<^sub>f"
  by (metis (mono_tags) HOM_ALPHABET_def HOM_ALPHA_HOMOGENEOUS mem_Collect_eq)

lemma WF_ALPHA_REL_REL_ALPHABET [closure]:
  "\<alpha> P \<in> REL_ALPHABET \<Longrightarrow> P \<in> WF_ALPHA_REL"
  by (simp add:WF_ALPHA_REL_def)

lemma SkipD_SkipDA_link:
  assumes 
    "\<alpha> R \<in> DESIGN_ALPHABET" "\<alpha> R \<in> HOM_ALPHABET"
  shows "II\<^sub>D ; \<lbrakk>R\<rbrakk>\<pi> = \<lbrakk>R\<rbrakk>\<pi> \<longleftrightarrow> (II\<^bsub>D[\<alpha> R]\<^esub> ;\<^sub>\<alpha> R = R)"
proof -
  have "II\<^sub>D ; \<lbrakk>R\<rbrakk>\<pi> = (true \<turnstile> II\<^bsub>\<langle>\<alpha> R -\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>\<rangle>\<^sub>f\<^esub>) ; \<lbrakk>R\<rbrakk>\<pi>"
    apply (simp add:SkipD_def DesignD_def)
    apply (subst BoolType_pvaux_cases[of "okay"])
    apply (simp)
    apply (subgoal_tac "HOMOGENEOUS (\<langle>\<alpha> R\<rangle>\<^sub>f)")
    apply (simp add:usubst typing defined closure unrest assms)
    apply (subst AndP_comm)
    apply (subst SemiR_AndP_left_postcond)
    apply (simp_all add: closure assms urename)
    apply (subst AndP_comm) back
    apply (subst SemiR_AndP_left_postcond)
    apply (simp_all add: closure assms urename)
    apply (metis (hide_lams, full_types) UNREST_SkipRA_NON_REL_VAR WF_RELATION_def mem_Collect_eq)
    apply (subst SkipRA_left_to_ExistsP[of _ _ "D\<^sub>0"])
    apply (simp_all add:closure var_dist unrest assms)
    apply (subst SkipRA_left_to_ExistsP[of _ _ "in \<langle>\<alpha> R\<rangle>\<^sub>f"])
    apply (insert assms)
    apply (simp_all add:closure var_dist unrest)
    apply (auto simp add:DESIGN_ALPHABET_def REL_ALPHABET_def)
  done

  also from assms have "in\<^sub>\<alpha> (\<alpha> R) \<union>\<^sub>f (in\<^sub>\<alpha> (\<alpha> R) -\<^sub>f \<lbrace>okay\<down>\<rbrace> \<union>\<^sub>f out\<^sub>\<alpha> (\<alpha> R)) = \<alpha> R" (is "?lhs = ?rhs")
  proof -
    have "?lhs = in\<^sub>\<alpha> (\<alpha> R) \<union>\<^sub>f out\<^sub>\<alpha> (\<alpha> R)"
      by (auto)

    thus ?thesis
      by (simp add:closure assms)
  qed

  ultimately show ?thesis using assms
    apply (simp add:SkipDA_def)
    apply (utp_alpha_tac)
    apply (simp add:alphabet_dist closure)
  done
qed

declare [[coercion TautologyA]]

theorem AH1_idem:
  "AH1 (AH1 R) = AH1 R"
  by (utp_alpha_tac, metis H1_idempotent)

theorem AH1_monotone:
  "P \<sqsubseteq> Q \<Longrightarrow> AH1 P \<sqsubseteq> AH1 Q"
  apply (utp_alpha_tac)
oops

theorem AH1_algebraic:
  assumes 
    "\<alpha> R \<in> DESIGN_ALPHABET"
    "\<alpha> R \<in> HOM_ALPHABET"
  shows 
    "((true\<^bsub>\<alpha> R\<^esub> ;\<^sub>\<alpha> R = true\<^bsub>\<alpha> R\<^esub>) \<and> (II\<^bsub>D[\<alpha> R]\<^esub> ;\<^sub>\<alpha> R = R)) \<longleftrightarrow> AH1(R) = R"
  using assms
  apply (simp add: SkipD_SkipDA_link[THEN sym] closure alphabet_dist)
  apply (utp_alpha_tac)
  apply (metis H1_algebraic HOM_ALPHABET_REL_ALPHABET Healthy_elim Healthy_intro WF_RELATION_REL_ALPHABET)
done
  


end