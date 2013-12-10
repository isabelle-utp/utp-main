theory utp_designs_a
imports utp_designs
begin

subsection {* Design Alphabets *}

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

subsection {* Design Turnstile *}

lift_definition DesignA :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 
   'a WF_ALPHA_PREDICATE \<Rightarrow> 
   'a WF_ALPHA_PREDICATE" (infixr "\<turnstile>\<^sub>\<alpha>" 60)
is "\<lambda> P Q. (\<alpha> P \<union>\<^sub>f \<alpha> Q \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>, (\<pi> P) \<turnstile> (\<pi> Q))"
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (auto intro:unrest)
done

lift_definition SkipAD :: "'a ALPHABET \<Rightarrow> 'a WF_ALPHA_PREDICATE" ("II\<alpha>\<^bsub>D[_]\<^esub>")
is "\<lambda> a. ((a :: 'a ALPHABET) \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>, II\<^bsub>D[\<langle>a\<rangle>\<^sub>f]\<^esub> :: 'a WF_PREDICATE)"
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (rule UNREST_subset)
  apply (rule unrest)
  apply (auto)
done

abbreviation ok_alpha_true :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 'a WF_ALPHA_PREDICATE" ("_\<^sup>t" [1000] 1000) where
"p\<^sup>t \<equiv> ``p[true/okay\<acute>]``"

abbreviation ok_alpha_false :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 'a WF_ALPHA_PREDICATE" ("_\<^sup>f" [1000] 1000) where
"p\<^sup>f \<equiv> ``p[false/okay\<acute>]``"

syntax
  "_uapred_design"   :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr "\<turnstile>" 30)
  "_uapred_SkipD"    :: "'a ALPHABET \<Rightarrow> uapred" ("II\<^bsub>D[_]\<^esub>")
  "_uapred_ok_true"  :: "uapred \<Rightarrow> uapred" ("_\<^sup>t" [1000] 1000)
  "_uapred_ok_false" :: "uapred \<Rightarrow> uapred" ("_\<^sup>f" [1000] 1000)

translations
  "_uapred_design p q"   == "CONST DesignA p q"
  "_uapred_SkipD a"      == "CONST SkipAD a"
  "_uapred_ok_true p"    == "CONST ok_alpha_true p"
  "_uapred_ok_false p"   == "CONST ok_alpha_false p"

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
   \<alpha>(II\<alpha>\<^bsub>D[a]\<^esub>) = a \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>"
  by (simp add:pred_alphabet_def SkipAD.rep_eq)

lemma EvalA_SkipDA [evala]:
  "\<lbrakk>II\<alpha>\<^bsub>D[a]\<^esub>\<rbrakk>\<pi> = II\<^bsub>D[\<langle>a\<rangle>\<^sub>f]\<^esub>"
  by (simp add:EvalA_def SkipAD.rep_eq)

lemma SkipDA_rel_closure [closure]:
  "a \<in> REL_ALPHABET \<Longrightarrow> II\<alpha>\<^bsub>D[a]\<^esub> \<in> WF_ALPHA_REL"
  apply (simp add:WF_ALPHA_REL_def REL_ALPHABET_def alphabet)
  apply (simp add:closure)
done

lemma UNREST_OKAY_alpha [unrest]: "\<lbrakk> okay\<down> \<notin>\<^sub>f \<alpha> P; okay\<down>\<acute> \<notin>\<^sub>f \<alpha> P \<rbrakk> \<Longrightarrow> OKAY \<sharp> \<lbrakk>P\<rbrakk>\<pi>"
  apply (rule UNREST_subset)
  apply (rule EvalA_UNREST)
  apply (auto)
done

theorem DesignA_extreme_point_true:
  "``false\<^bsub>a\<^esub> \<turnstile> false\<^bsub>a\<^esub>`` = ``false\<^bsub>a\<^esub> \<turnstile> true\<^bsub>a\<^esub>``"
  "``false\<^bsub>a\<^esub> \<turnstile> true\<^bsub>a\<^esub>``  = ``false\<^bsub>a\<^esub> \<turnstile> true\<^bsub>a\<^esub>``"
  apply (utp_alpha_tac, utp_pred_tac)
  apply (utp_alpha_tac)
done

syntax
  "_uapred_evar"    :: "(bool, 'm) PVAR \<Rightarrow> uapred" ("$_" [999] 999)

translations
  "_uapred_evar x"      == "CONST VarA x\<down>"

theorem DesignA_extreme_point_nok:
  "``true\<^bsub>a\<^esub> \<turnstile> false\<^bsub>a\<^esub>`` = ``\<not> $okay \<oplus> (a \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>)``"
  by (utp_alpha_tac, utp_pred_tac, auto)

theorem DesignA_export_precondition:
  "``(P \<turnstile> Q)`` = ``(P \<turnstile> P \<and> Q)``"
  by (utp_alpha_tac, utp_pred_auto_tac)

theorem DesignA_composition:
  assumes 
  "P1 \<in> WF_ALPHA_REL" "P2 \<in> WF_ALPHA_REL"
  "Q1 \<in> WF_ALPHA_REL" "Q2 \<in> WF_ALPHA_REL"
  "okay\<down> \<notin>\<^sub>f \<alpha> P1" "okay\<down>\<acute> \<notin>\<^sub>f \<alpha> P1"
  "okay\<down> \<notin>\<^sub>f \<alpha> P2" "okay\<down>\<acute> \<notin>\<^sub>f \<alpha> P2"
  "okay\<down> \<notin>\<^sub>f \<alpha> Q1" "okay\<down>\<acute> \<notin>\<^sub>f \<alpha> Q1"
  "okay\<down> \<notin>\<^sub>f \<alpha> Q2" "okay\<down>\<acute> \<notin>\<^sub>f \<alpha> Q2"
  shows "``(P1 \<turnstile> Q1) ; (P2 \<turnstile> Q2)`` = ``((\<not> ((\<not> P1) ; true\<^bsub>in\<^sub>\<alpha> (\<alpha> P1)\<^esub>)) \<and> \<not> (Q1 ; (\<not> P2))) \<turnstile> (Q1 ; Q2)``"
  using assms
  apply (utp_alpha_tac)
  apply (rule conjI)
  apply (auto)
  apply (subst DesignD_composition)
  apply (simp_all add:closure unrest)
done

subsection {* Healthiness Conditions *}

lift_definition AH1 :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 
   'a WF_ALPHA_PREDICATE"
is "\<lambda> P. (\<alpha> P \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>, H1(\<pi> P))"
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def H1_def)
  apply (auto intro:unrest)
done

lemma AH1_alphabet [alphabet]:
  "\<alpha>(AH1(P)) = \<alpha> P \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>"
  by (simp add:AH1.rep_eq pred_alphabet_def)

lemma EvalA_AH1 [evala]:
  "\<lbrakk>AH1(P)\<rbrakk>\<pi> = H1\<lbrakk>P\<rbrakk>\<pi>"
  by (simp add:EvalA_def AH1.rep_eq)

lemma AH1_DesignA:
  assumes "okay\<down> \<notin>\<^sub>f \<alpha> P" "okay\<down>\<acute> \<notin>\<^sub>f \<alpha> P"
          "okay\<down> \<notin>\<^sub>f \<alpha> Q" "okay\<down>\<acute> \<notin>\<^sub>f \<alpha> Q"
  shows "AH1(P \<turnstile>\<^sub>\<alpha> Q) = P \<turnstile>\<^sub>\<alpha> Q"
  by (utp_alpha_tac, utp_pred_auto_tac)

lemma WF_RELATION_REL_ALPHABET [closure]: 
  "\<alpha> P \<in> REL_ALPHABET \<Longrightarrow> \<lbrakk>P\<rbrakk>\<pi> \<in> WF_RELATION"
  by (auto intro:closure simp add:WF_ALPHA_REL_def)

theorem AH1_idem:
  "AH1 (AH1 R) = AH1 R"
  by (utp_alpha_tac, metis H1_idempotent)

theorem AH1_monotone:
  "P \<sqsubseteq> Q \<Longrightarrow> AH1 P \<sqsubseteq> AH1 Q"
  apply (utp_alpha_tac)
  apply (metis H1_monotone RefP_def TrueP_eq_ClosureP less_eq_WF_PREDICATE_def utp_pred_simps(21))
done

lemma SkipRA_closure' [closure]:
  "a \<in> REL_ALPHABET \<Longrightarrow> II\<^bsub>\<langle>a\<rangle>\<^sub>f\<^esub> \<in> WF_RELATION"
  by (metis EvalA_SkipA SkipA_closure WF_ALPHA_REL_EvalA_WF_RELATION)
 
lemma HOMOGENEOUS_HOM_ALPHA [closure]:
  "a \<in> HOM_ALPHABET \<Longrightarrow> HOMOGENEOUS \<langle>a\<rangle>\<^sub>f"
  by (metis (mono_tags) HOM_ALPHABET_def HOM_ALPHA_HOMOGENEOUS mem_Collect_eq)

lemma WF_ALPHA_REL_REL_ALPHABET [closure]:
  "\<alpha> P \<in> REL_ALPHABET \<Longrightarrow> P \<in> WF_ALPHA_REL"
  by (simp add:WF_ALPHA_REL_def)

theorem AH1_algebraic:
  assumes 
    "\<alpha> R \<in> DESIGN_ALPHABET"
    "\<alpha> R \<in> HOM_ALPHABET"
  shows 
    "((true\<^bsub>\<alpha> R\<^esub> ;\<^sub>\<alpha> R = true\<^bsub>\<alpha> R\<^esub>) \<and> (II\<alpha>\<^bsub>D[\<alpha> R]\<^esub> ;\<^sub>\<alpha> R = R)) \<longleftrightarrow> AH1(R) = R"
  using assms
  apply (utp_alpha_tac)
  apply (subst SkipD_SkipDA_left_link[THEN sym])
  apply (simp_all add:closure)
  apply (auto intro:unrest UNREST_subset)[1]
  apply (metis H1_algebraic Healthy_elim Healthy_intro REL_ALPHABET_DESIGN_ALPHABET WF_RELATION_REL_ALPHABET)
done

lemma DASHED_minus_out:
  "D\<^sub>1 - out vs = D\<^sub>1 - vs"
  by (auto simp add:var_defs)

lemma HOMOGENEOUS_minus_nrel [simp]:
  "HOMOGENEOUS (vs1 - nrel vs2) = HOMOGENEOUS vs1"
  by (simp add:HOMOGENEOUS_def COMPOSABLE_def var_dist)

lemma JA_as_J_left:
  "\<lbrakk>HOMOGENEOUS vs; okay\<down>\<acute> \<in> vs\<rbrakk> \<Longrightarrow> J\<^bsub>vs\<^esub> = (\<exists>\<^sub>p D\<^sub>1 - vs. J)"
  apply (simp add:JA_pred_def)
  apply (subst ExistsP_AndP_expand2[THEN sym])
  apply (rule unrest)
  apply (rule unrest)
  apply (force)
  apply (auto intro:unrest)[1]
  apply (simp add: SkipRA_alt_out_def closure var_dist closure ExistsP_union[THEN sym] in_vars_diff DASHED_minus_out)
done

lemma JA_as_J_right:
  "\<lbrakk>HOMOGENEOUS vs; okay\<down> \<in> vs\<rbrakk> \<Longrightarrow> J\<^bsub>vs\<^esub> = (\<exists>\<^sub>p D\<^sub>0 - vs. J)"
  apply (simp add:JA_pred_def)
  apply (subst ExistsP_AndP_expand2[THEN sym])
  apply (auto intro:unrest)[1]
  apply (simp add: SkipRA_alt_in_def closure var_dist closure ExistsP_union[THEN sym] in_vars_diff UNDASHED_minus_in)
done

lemma SemiR_JA_right:
  assumes 
    "vs \<subseteq> REL_VAR"
    "HOMOGENEOUS vs"
    "okay\<down> \<in> vs" 
    "D\<^sub>1 - out vs \<sharp> p"
  shows "p ;\<^sub>R J = p ;\<^sub>R J\<^bsub>vs\<^esub>"
  using assms
  apply (subst SemiR_ExistsP_insert_right[of "D\<^sub>0 - (in vs \<union> {okay\<down>})"])
  apply (rule UNREST_subset)
  apply (auto)
  apply (metis (full_types) hom_alphabet_dash in_member in_out_union set_mp sup_ge2)
  apply (simp add: UNDASHED_minus_in closure)
  apply (simp add: JA_as_J_right)
done  

lift_definition AH2 :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 
   'a WF_ALPHA_PREDICATE"
is "\<lambda> P. (\<alpha> P \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>, H2(\<pi> P))"
proof -
  fix P :: "'a WF_ALPHA_PREDICATE"
  show "(\<alpha> P \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>, H2(\<pi> P)) \<in> WF_ALPHA_PREDICATE"
    apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def H2_def)
    apply (subst SemiR_JA_right[of "homr (\<langle>\<alpha> P\<rangle>\<^sub>f \<union> OKAY) - nrel \<langle>\<alpha> P\<rangle>\<^sub>f"])
    apply (simp_all add:closure var_dist)
    apply (auto simp add:var_defs)[1]
    apply (auto simp add:var_defs)[1]
    apply (rule UNREST_subset)
    apply (rule WF_ALPHA_PREDICATE_UNREST) 
    apply (force)
    apply (rule UNREST_SemiR_general[of "VAR - (\<langle>\<alpha> P\<rangle>\<^sub>f \<union> OKAY)"])
    apply (rule UNREST_subset)
    apply (rule WF_ALPHA_PREDICATE_UNREST) 
    apply (force)
    apply (rule unrest)
    apply (simp add:var_dist closure nrel_insert_NON_REL_VAR nrel_insert_UNDASHED nrel_insert_DASHED nrel_vars_def[THEN sym])
    apply (auto simp add:var_defs)
  done
qed

lemma AH2_alphabet [alphabet]:
  "\<alpha> (AH2(P)) = \<alpha> P \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>"
  by (simp add:pred_alphabet_def AH2.rep_eq)

lemma EvalA_AH2 [evala]:
  "\<lbrakk>AH2(P)\<rbrakk>\<pi> = H2(\<lbrakk>P\<rbrakk>\<pi>)"
  by (simp add:EvalA_def AH2.rep_eq)

lemma AH2_idem: 
  "AH2 (AH2 p) = AH2 (p)"
  by (utp_alpha_tac, metis H2_idempotent)

lemma AH2_mono:
  "p \<sqsubseteq> q \<Longrightarrow> AH2(p) \<sqsubseteq> AH2(q)"
  apply (simp add:EvalA_RefinementA)
  apply (utp_alpha_tac)
  apply (metis H2_monotone)
done

theorem AH1_AH2_is_DesignA:
  assumes "\<alpha>(P) \<in> DESIGN_ALPHABET" "AH1(P) = P" "AH2(P) = P"
  shows "P = ``\<not>P\<^sup>f \<turnstile> P\<^sup>t``"
  using assms
  apply (utp_alpha_tac)
  apply (rule)
  apply (auto simp add:closure)[1]
  apply (subst H1_H2_is_DesignD)
  apply (simp_all add:closure is_healthy_def)
done

lift_definition AH3 :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 
   'a WF_ALPHA_PREDICATE"
is "\<lambda> P. (\<alpha> P \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>, H3(\<pi> P))"
proof -
  fix P :: "'a WF_ALPHA_PREDICATE"
  show "(\<alpha> P \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>, H3(\<pi> P)) \<in> WF_ALPHA_PREDICATE"
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def H3_def)
  apply (subst SkipD_SkipDA_right_link[of "homr (\<langle>\<alpha> P\<rangle>\<^sub>f \<union> OKAY) - nrel \<langle>\<alpha> P\<rangle>\<^sub>f"])
    apply (simp_all add:closure var_dist)
    apply (auto simp add:var_defs)[1]
    apply (auto simp add:var_defs)[1]
    apply (rule UNREST_SemiR_general[of "VAR - (\<langle>\<alpha> P\<rangle>\<^sub>f \<union> OKAY)"])
    apply (rule UNREST_subset)
    apply (rule WF_ALPHA_PREDICATE_UNREST) 
    apply (force)
    apply (rule unrest)
    apply (simp add:var_dist closure nrel_insert_NON_REL_VAR nrel_insert_UNDASHED nrel_insert_DASHED nrel_vars_def[THEN sym])
    apply (auto simp add:var_defs)
  done
qed

lemma AH3_alphabet [alphabet]:
  "\<alpha> (AH3(P)) = \<alpha> P \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>"
  by (simp add:pred_alphabet_def AH3.rep_eq)

lemma EvalA_AH3 [evala]:
  "\<lbrakk>AH3(P)\<rbrakk>\<pi> = H3(\<lbrakk>P\<rbrakk>\<pi>)"
  by (simp add:EvalA_def AH3.rep_eq)

theorem AH3_idem:
  "\<alpha> p \<in> REL_ALPHABET \<Longrightarrow> AH3 (AH3 p) = AH3 (p)"
  apply (utp_alpha_tac)
  apply (metis H3_idempotent)
done

theorem AH3_implies_AH2:
  "P is AH3 \<Longrightarrow> P is AH2"
  apply (simp add:is_healthy_def)
  apply (utp_alpha_tac)
  apply (metis H3_absorbs_H2_1)
done

lift_definition AH4 :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 
   'a WF_ALPHA_PREDICATE"
is "\<lambda> P. (\<alpha> P \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>, H4(\<pi> P))"
proof -
  fix P :: "'a WF_ALPHA_PREDICATE"
  show "(\<alpha> P \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>, H4(\<pi> P)) \<in> WF_ALPHA_PREDICATE"
    apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def H4_def)
    apply (rule unrest)
    apply (rule UNREST_SemiR_general)
    apply (rule UNREST_subset[of _ _ "VAR - insert okay\<down> (insert okay\<down>\<acute> \<langle>\<alpha> P\<rangle>\<^sub>f)"])
    apply (rule WF_ALPHA_PREDICATE_UNREST)
    apply (force)
    apply (rule UNREST_TrueP[of "VAR - insert okay\<down> (insert okay\<down>\<acute> \<langle>\<alpha> P\<rangle>\<^sub>f)"])
    apply (auto simp add:var_defs)[1]
    apply (auto intro:unrest)
  done
qed
  
lemma AH4_alphabet [alphabet]:
  "\<alpha> (AH4(P)) = \<alpha> P \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>"
  by (simp add:pred_alphabet_def AH4.rep_eq)

lemma EvalA_AH4 [evala]:
  "\<lbrakk>AH4(P)\<rbrakk>\<pi> = H4(\<lbrakk>P\<rbrakk>\<pi>)"
  by (simp add:EvalA_def AH4.rep_eq)

theorem AH4_idem:
  "AH4 (AH4 p) = AH4 (p)"
  apply (utp_alpha_tac)
  apply (metis H4_idempotent)
done

lift_definition DESIGNS :: "'a WF_THEORY" 
is "(DESIGN_ALPHABET, {AH1,AH2})"
  by (auto simp add:WF_THEORY_def IDEMPOTENT_OVER_def AH1_idem AH2_idem)

lift_definition NORMAL_DESIGNS :: "'a WF_THEORY" 
is "(DESIGN_ALPHABET, {AH1,AH3})"
  by (auto simp add:WF_THEORY_def IDEMPOTENT_OVER_def AH1_idem AH3_idem closure)

lift_definition FEASIBLE_DESIGNS :: "'a WF_THEORY" 
is "(DESIGN_ALPHABET, {AH1,AH3,AH4})"
  by (auto simp add:WF_THEORY_def IDEMPOTENT_OVER_def AH1_idem AH3_idem AH4_idem closure)

lemma NORMAL_DESIGNS_are_DESIGNS [closure]: 
  "P \<in> \<lbrakk>NORMAL_DESIGNS\<rbrakk>\<T> \<Longrightarrow> P \<in> \<lbrakk>DESIGNS\<rbrakk>\<T>"
  by (auto simp add:THEORY_PRED_def utp_alphabets_def NORMAL_DESIGNS.rep_eq DESIGNS.rep_eq healthconds_def AH3_implies_AH2)

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





  


end