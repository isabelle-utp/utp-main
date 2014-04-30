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

abbreviation ok'_alpha_true :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 'a WF_ALPHA_PREDICATE" ("_\<^sup>t" [1000] 1000) where
"p\<^sup>t \<equiv> ``p[true/okay\<acute>]``"

abbreviation ok'_alpha_false :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 'a WF_ALPHA_PREDICATE" ("_\<^sup>f" [1000] 1000) where
"p\<^sup>f \<equiv> ``p[false/okay\<acute>]``"

abbreviation ok_true_ok'_alpha_true :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 'a WF_ALPHA_PREDICATE" ("_\<^bsup>tt\<^esup>" [1000] 1000) where
"p\<^bsup>tt\<^esup> \<equiv> ``p[true/okay][true/okay\<acute>]``"

abbreviation ok_true_ok'_alpha_false :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 'a WF_ALPHA_PREDICATE" ("_\<^bsup>tf\<^esup>" [1000] 1000) where
"p\<^bsup>tf\<^esup> \<equiv> ``p[true/okay][false/okay\<acute>]``"

syntax
  "_uapred_design"    :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr "\<turnstile>" 30)
  "_uapred_SkipD"     :: "'a ALPHABET \<Rightarrow> uapred" ("II\<^bsub>D[_]\<^esub>")
  "_uapred_ok'_true"  :: "uapred \<Rightarrow> uapred" ("_\<^sup>t" [1000] 1000)
  "_uapred_ok'_false" :: "uapred \<Rightarrow> uapred" ("_\<^sup>f" [1000] 1000)
  "_uapred_ok_true_ok'_true"  :: "uapred \<Rightarrow> uapred" ("_\<^bsup>tt\<^esup>" [1000] 1000)
  "_uapred_ok_true_ok'_false" :: "uapred \<Rightarrow> uapred" ("_\<^bsup>tf\<^esup>" [1000] 1000)

translations
  "_uapred_design p q"   == "CONST DesignA p q"
  "_uapred_SkipD a"      == "CONST SkipAD a"
  "_uapred_ok'_true p"   == "CONST ok'_alpha_true p"
  "_uapred_ok'_false p"  == "CONST ok'_alpha_false p"
  "_uapred_ok_true_ok'_true p"   == "CONST ok_true_ok'_alpha_true p"
  "_uapred_ok_true_ok'_false p"  == "CONST ok_true_ok'_alpha_false p"

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

lemma SkipAD_alphabet [alphabet]:
  "a \<in> REL_ALPHABET \<Longrightarrow>
   \<alpha>(II\<alpha>\<^bsub>D[a]\<^esub>) = a \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>"
  by (simp add:pred_alphabet_def SkipAD.rep_eq)

lemma EvalA_SkipAD [evala]:
  "\<lbrakk>II\<alpha>\<^bsub>D[a]\<^esub>\<rbrakk>\<pi> = II\<^bsub>D[\<langle>a\<rangle>\<^sub>f]\<^esub>"
  by (simp add:EvalA_def SkipAD.rep_eq)

lemma SkipAD_rel_closure [closure]:
  "a \<in> REL_ALPHABET \<Longrightarrow> II\<alpha>\<^bsub>D[a]\<^esub> \<in> WF_ALPHA_REL"
  apply (simp add:WF_ALPHA_REL_def REL_ALPHABET_def alphabet)
  apply (simp add:closure)
done

lemma UNREST_OKAY_alpha [unrest]: "\<lbrakk> okay\<down> \<notin>\<^sub>f \<alpha> P; okay\<down>\<acute> \<notin>\<^sub>f \<alpha> P \<rbrakk> \<Longrightarrow> OKAY \<sharp> \<lbrakk>P\<rbrakk>\<pi>"
  apply (rule UNREST_subset)
  apply (rule UNREST_EvalA)
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

definition TopAD :: "'a ALPHABET \<Rightarrow> 'a WF_ALPHA_PREDICATE" where
"TopAD a = ``(\<not> $okay)\<^bsub>+a\<^esub>``"

declare TopAD_def [evala]

theorem DesignA_extreme_point_nok:
  "a \<in> DESIGN_ALPHABET \<Longrightarrow> ``true\<^bsub>a\<^esub> \<turnstile> false\<^bsub>a\<^esub>`` = TopAD a"
  by (utp_alpha_tac, utp_pred_tac)

theorem DesignA_export_precondition:
  "``(P \<turnstile> Q)`` = ``(P \<turnstile> P \<and> Q)``"
  by (utp_alpha_tac, utp_pred_auto_tac)

theorem DesignA_OrA:
  "``(P1 \<turnstile> Q1) \<or> (P2 \<turnstile> Q2)`` = ``(P1 \<and> P2) \<turnstile> (Q1 \<or> Q2)``"
  by (utp_alpha_tac, utp_pred_auto_tac)

theorem DesignA_AndA:
  "``(P1 \<turnstile> Q1) \<and> (P2 \<turnstile> Q2)`` = 
   ``(P1 \<or> P2 \<turnstile> (P1 \<Rightarrow> Q1) \<and> (P2 \<Rightarrow> Q2))``"
  by (utp_alpha_tac, utp_pred_auto_tac)

definition UNREST_ALPHA :: 
  "'a VAR set \<Rightarrow> 'a WF_ALPHA_PREDICATE \<Rightarrow> bool" where
"UNREST_ALPHA vs p = vs \<sharp> (\<pi> p)"

adhoc_overloading
  unrest UNREST_ALPHA

lemma UNREST_ALPHA_EvalA [unrest]:
  "vs \<sharp> p \<Longrightarrow> vs \<sharp> \<lbrakk>p\<rbrakk>\<pi>"
  by (metis EvalA_def UNREST_ALPHA_def)

lemma UNREST_ALPHA_alphabet [unrest]:
  "UNREST_ALPHA (- \<langle>\<alpha>(p)\<rangle>\<^sub>f) p"
  by (simp add:UNREST_ALPHA_def unrest)

theorem DesignA_composition:
  assumes 
  "P1 \<in> WF_ALPHA_REL" "P2 \<in> WF_ALPHA_REL"
  "Q1 \<in> WF_ALPHA_REL" "Q2 \<in> WF_ALPHA_REL"
  "{okay\<down>\<acute>} \<sharp> P1" "{okay\<down>} \<sharp> P2" "{okay\<down>\<acute>} \<sharp> Q1" "{okay\<down>} \<sharp> Q2"
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
  by (utp_alpha_tac)

theorem AH1_idem:
  "AH1 (AH1 R) = AH1 R"
  by (utp_alpha_tac, metis H1_idempotent)

theorem AH1_monotone:
  "P \<sqsubseteq> Q \<Longrightarrow> AH1 P \<sqsubseteq> AH1 Q"
  apply (utp_alpha_tac)
  apply (metis H1_monotone RefP_def TrueP_eq_ClosureP less_eq_WF_PREDICATE_def utp_pred_simps(21))
done

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

lemma AH1_AH2_commute:
  "AH1 (AH2 p) = AH2 (AH1 p)"
  by (utp_alpha_tac, metis H1_H2_commute)

lemma AH2_mono:
  "p \<sqsubseteq> q \<Longrightarrow> AH2(p) \<sqsubseteq> AH2(q)"
  apply (simp add:EvalA_RefinementA)
  apply (utp_alpha_tac)
  apply (metis H2_monotone)
done

theorem DesignA_refinement:
  assumes 
    "OKAY \<sharp> P1" 
    "OKAY \<sharp> P2"
    "OKAY \<sharp> Q1" 
    "OKAY \<sharp> Q2"
  shows "``P1 \<turnstile> Q1 \<sqsubseteq> P2 \<turnstile> Q2`` = ``[P1 \<Rightarrow> P2] \<and> [P1 \<and> Q2 \<Rightarrow> Q1]``"
  apply (utp_alpha_tac)
  apply (rule DesignD_refinement)
  apply (simp_all add:assms unrest)
done

lemma DESIGN_ALPHABET_AH1:
  "\<alpha>(P) \<in> REL_ALPHABET \<Longrightarrow>
   \<alpha>(AH1(P)) \<in> DESIGN_ALPHABET"
  apply (simp add:DESIGN_ALPHABET_def)
  apply (auto simp add:alphabet closure)
done


theorem AH1_AH2_is_DesignA:
  assumes "\<alpha> P \<in> REL_ALPHABET" "P is AH1" "P is AH2"
  shows "P = ``\<not>P\<^sup>f \<turnstile> P\<^sup>t``"
  using assms
  apply (subgoal_tac "\<alpha>(P) \<in> DESIGN_ALPHABET")
  apply (utp_alpha_tac)
  apply (rule)
  apply (auto simp add:closure)[1]
  apply (subst H1_H2_is_DesignD)
  apply (simp_all add:closure is_healthy_def)
  apply (metis DESIGN_ALPHABET_AH1)
done

theorem AH1_AH2_is_DesignA':
  assumes "\<alpha> P \<in> REL_ALPHABET" "P is AH1" "P is AH2"
  shows "P = ``\<not>P\<^bsup>tf\<^esup> \<turnstile> P\<^bsup>tt\<^esup>``"
  using assms
  apply (subgoal_tac "\<alpha>(P) \<in> DESIGN_ALPHABET")
  apply (utp_alpha_tac)
  apply (rule)
  apply (auto simp add:closure)[1]
  apply (subst H1_H2_is_DesignD')
  apply (simp_all add:closure is_healthy_def)
  apply (metis DESIGN_ALPHABET_AH1)
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
    apply (rule UNREST_subset[of _ _ "- insert okay\<down> (insert okay\<down>\<acute> \<langle>\<alpha> P\<rangle>\<^sub>f)"])
    apply (rule WF_ALPHA_PREDICATE_UNREST)
    apply (force)
    apply (rule UNREST_TrueP[of "- insert okay\<down> (insert okay\<down>\<acute> \<langle>\<alpha> P\<rangle>\<^sub>f)"])
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

definition "DESIGNS = \<lparr> alphas = DESIGN_ALPHABET, health = (AH1 \<circ> AH2) \<rparr>"

interpretation designs: UTP_THEORY DESIGNS
  apply (unfold_locales)
  apply (simp add:DESIGNS_def IDEMPOTENT_OVER_def)
  apply (metis AH1_AH2_commute AH1_idem AH2_idem)
done

theorem DESIGNS_form:
  "P \<in> \<lbrakk>DESIGNS\<rbrakk>\<T> \<Longrightarrow> P = ``\<not>P\<^sup>f \<turnstile> P\<^sup>t``"
  apply (erule THEORY_PRED_elim)
  apply (simp add:DESIGNS_def)
  apply (metis (no_types) AH1_AH2_commute AH1_AH2_is_DesignA AH2_idem PVAR_VAR_pvdash REL_ALPHABET_DESIGN_ALPHABET comp_apply is_healthy_def)
done

theorem DESIGNS_form':
  "P \<in> \<lbrakk>DESIGNS\<rbrakk>\<T> \<Longrightarrow> P = ``\<not>P\<^bsup>tf\<^esup> \<turnstile> P\<^bsup>tt\<^esup>``"
  apply (erule THEORY_PRED_elim, simp add:DESIGNS_def)
  apply (metis (no_types) AH1_AH2_commute AH1_AH2_is_DesignA' AH2_idem PVAR_VAR_pvdash REL_ALPHABET_DESIGN_ALPHABET comp_apply is_healthy_def)
done

theorem TopAD_DESIGNS_greatest:
  "\<lbrakk> p \<in> \<lbrakk>DESIGNS\<rbrakk>[a]\<T> \<rbrakk> \<Longrightarrow> p \<sqsubseteq> TopAD a"
  apply (erule THEORY_PRED_OVER_elim)
  apply (erule THEORY_PRED_elim)
  apply (simp add:DESIGNS_def)
  apply (clarify)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done

lemma DESIGNS_THEORY_alphabet [alphabet]:
  "\<A>\<^bsub>DESIGNS\<^esub> = DESIGN_ALPHABET"
  by (simp add:DESIGNS_def)

lemma DESIGNS_THEORY_healthconds [simp]:
  "\<H>\<^bsub>DESIGNS\<^esub> = AH1 \<circ> AH2"
  by (simp add:DESIGNS_def)

theorem DesignA_DESIGNS_closure [closure]:
  "\<lbrakk> a \<in> DESIGN_ALPHABET; \<alpha> P = a; \<alpha> Q = a; {okay\<down>\<acute>} \<sharp> P \<rbrakk> 
   \<Longrightarrow> ``P \<turnstile> Q`` \<in> \<lbrakk>DESIGNS\<rbrakk>[a]\<T>"
  apply (rule THEORY_PRED_OVER_intro)
  apply (rule THEORY_PRED_intro)
  apply (simp_all add:alphabet closure)
  apply (utp_alpha_tac)
  apply (metis (lifting, no_types) H1_DesignD H2_DesignD UNREST_ALPHA_EvalA)
done

theorem TrueA_DESIGNS [closure]:
  "a \<in> DESIGN_ALPHABET \<Longrightarrow> true\<^bsub>a\<^esub> \<in> \<lbrakk>DESIGNS\<rbrakk>[a]\<T>"
  apply (rule THEORY_PRED_OVER_intro)
  apply (rule THEORY_PRED_intro)
  apply (simp_all add:alphabet)
  apply (utp_alpha_tac, metis H1_TrueP H2_TrueP)
done

theorem TrueA_DESIGNS_least:
  "\<lbrakk> p \<in> \<lbrakk>DESIGNS\<rbrakk>[a]\<T> \<rbrakk> \<Longrightarrow> true\<^bsub>a\<^esub> \<sqsubseteq> p"
  by (utp_alpha_tac, utp_pred_auto_tac)

theorem DESIGNS_lattice: 
  "a \<in> DESIGN_ALPHABET \<Longrightarrow> lattice (OrderT DESIGNS a)"
  apply (unfold_locales)
  apply (rule_tac x="``x \<and> y``" in exI)
  apply (rule least_UpperI)
  apply (simp_all add:Upper_def)
  apply (utp_alpha_tac)
  apply (metis RefineP_seperation THEORY_PRED_OVER_alphabet dual_order.refl fset_simps(5))
  apply (utp_alpha_tac)
  apply (metis RefineP_seperation fset_simps(5))
  apply (rule)
  apply (rule)
  apply (simp add:alphabet DESIGNS_def)
  apply (simp add:DESIGNS_def THEORY_PRED_OVER_def THEORY_PRED_def)
  apply (utp_alpha_tac)
  apply (erule THEORY_PRED_OVER_elim)
  apply (erule THEORY_PRED_OVER_elim)
  apply (simp)
  apply (rule)
  apply (auto simp add:DESIGN_ALPHABET_def)[1]
  apply (metis (hide_lams, no_types) AH1_AH2_commute AH2_idem DESIGNS_THEORY_healthconds EvalA_AH1 EvalA_AH2 H1_AndP H2_AndP_closure THEORY_PRED_elim comp_apply is_healthy_def)
  apply (simp add:alphabet THEORY_PRED_OVER_alphabet)
  apply (rule_tac x="``x \<or> y``" in exI)
  apply (rule greatest_LowerI, simp_all)
  apply (utp_alpha_tac)
  apply (metis OrP_comm OrP_ref THEORY_PRED_OVER_alphabet fset_simps(5))
  apply (simp add:Lower_def)
  apply (utp_alpha_tac)
  apply (metis OrP_refine fset_simps(5))
  apply (simp add:DESIGNS_def THEORY_PRED_OVER_def THEORY_PRED_def)
  apply (utp_alpha_tac)
  apply (metis H1_OrP H2_OrP)
done

lemma WF_ALPHA_PREDICATE_OVER_THEORY [closure]: 
  "ps \<subseteq> \<lbrakk>T\<rbrakk>[a]\<T> \<Longrightarrow> ps \<subseteq> WF_ALPHA_PREDICATE_OVER a"
  by (auto)

lemma THEORY_subset_alphabet :
  "\<lbrakk> ps \<subseteq> \<lbrakk>T\<rbrakk>[a]\<T>; p \<in> ps \<rbrakk> \<Longrightarrow> \<alpha> p = a"
  by (auto)

theorem DESIGNS_TrueA_least:
  "a \<in> DESIGN_ALPHABET \<Longrightarrow> least (OrderT DESIGNS a) true\<^bsub>a\<^esub> \<lbrakk>DESIGNS\<rbrakk>[a]\<T>"
  by (simp add: least_def closure TrueA_DESIGNS_least)

lemma true_eq_taut [simp]: "x = true \<longleftrightarrow> [x]"
  by (utp_pred_tac)

lemma RefineP_ClosureP [simp]:
  "`p \<sqsubseteq> q` \<longleftrightarrow> p \<sqsubseteq> q"
  by (utp_pred_tac)

lemma is_healthyD [intro?]: "P is H \<Longrightarrow> H(P) = P"
  by (simp add:is_healthy_def)

lemma subsetE:
  "\<lbrakk> A \<subseteq> B; \<lbrakk> \<And> x. x\<in>A \<Longrightarrow> x\<in>B \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" 
  by auto

lemma DESIGN_ALPHABET_WF_RELATION [closure]:
  "\<alpha>(P) \<in> DESIGN_ALPHABET \<Longrightarrow> \<lbrakk>P\<rbrakk>\<pi> \<in> WF_RELATION"
  by (metis REL_ALPHABET_DESIGN_ALPHABET WF_RELATION_REL_ALPHABET)
  
theorem EvalA_AndDistA' [evala] :
  "ps \<subseteq> WF_ALPHA_PREDICATE_OVER t \<Longrightarrow> \<lbrakk>\<And>\<^bsub>t\<^esub> ps\<rbrakk>\<pi> = \<And>\<^sub>p {\<lbrakk>p\<rbrakk>\<pi> | p. p \<in> ps}"
  by (simp add:EvalA_AndDistA WF_ALPHA_PREDICATE_OVER_member)

theorem EvalA_OrDistA' [evala] :
  "ps \<subseteq> WF_ALPHA_PREDICATE_OVER t \<Longrightarrow> \<lbrakk>\<Or>\<^bsub>t\<^esub> ps\<rbrakk>\<pi> = \<Or>\<^sub>p {\<lbrakk>p\<rbrakk>\<pi> | p. p \<in> ps}"
  by (simp add:EvalA_OrDistA WF_ALPHA_PREDICATE_OVER_member)

theorem H1_DistAndA_closure:
  "\<lbrakk>a \<in> DESIGN_ALPHABET; A \<subseteq> \<lbrakk>DESIGNS\<rbrakk>[a]\<T>\<rbrakk> \<Longrightarrow> \<And>\<^bsub>a\<^esub> A is AH1"
  apply (utp_alpha_tac)
  apply (rule is_healthyD)
  apply (rule AndDistP_is_H1)
  apply (auto)
  apply (drule subsetD, simp_all)
  apply (erule THEORY_PRED_OVER_elim)
  apply (erule THEORY_PRED_elim)
  apply (utp_alpha_tac)
  apply (metis H1_idempotent)
done

theorem H2_DistAndA_closure:
  "\<lbrakk>a \<in> DESIGN_ALPHABET; A \<subseteq> \<lbrakk>DESIGNS\<rbrakk>[a]\<T>\<rbrakk> \<Longrightarrow> \<And>\<^bsub>a\<^esub> A is AH2"
  apply (utp_alpha_tac)
  apply (rule is_healthyD)
  apply (rule H2_AndDistP_closure)
  apply (auto intro:closure)
  apply (drule subsetD, simp_all)
  apply (erule THEORY_PRED_OVER_elim)
  apply (erule THEORY_PRED_elim)
  apply (utp_alpha_tac)
  apply (metis H1_H2_commute H2_idempotent)
done

theorem AH1_DistOrA_closure:
  "\<lbrakk>a \<in> DESIGN_ALPHABET; A \<subseteq> \<lbrakk>DESIGNS\<rbrakk>[a]\<T>; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Or>\<^bsub>a\<^esub> A is AH1"
  apply (utp_alpha_tac)
  apply (rule is_healthyD)
  apply (rule OrDistP_is_H1)
  apply (clarsimp)
  apply (drule subsetD, simp_all)
  apply (erule THEORY_PRED_OVER_elim)
  apply (erule THEORY_PRED_elim)
  apply (utp_alpha_tac)
  apply (metis H1_idempotent)
done

theorem AH2_DistOrA_closure:
  "\<lbrakk>a \<in> DESIGN_ALPHABET; A \<subseteq> \<lbrakk>DESIGNS\<rbrakk>[a]\<T>; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<Or>\<^bsub>a\<^esub> A is AH2"
  apply (utp_alpha_tac)
  apply (rule is_healthyD)
  apply (rule H2_OrDistP_closure)
  apply (clarsimp)
  apply (drule subsetD, simp_all)
  apply (erule THEORY_PRED_OVER_elim)
  apply (erule THEORY_PRED_elim)
  apply (utp_alpha_tac)
  apply (metis H1_H2_commute H2_idempotent)
done

lemma AndDistA_alphabet_theory [alphabet]:
  "A \<subseteq> \<lbrakk>T\<rbrakk>[a]\<T> \<Longrightarrow> \<alpha> (\<And>\<^bsub>a\<^esub> A) = a"
  by (metis AndDistA_alphabet_alt WF_ALPHA_PREDICATE_OVER_THEORY)

lemma OrDistA_alphabet_theory [alphabet]:
  "A \<subseteq> \<lbrakk>T\<rbrakk>[a]\<T> \<Longrightarrow> \<alpha> (\<Or>\<^bsub>a\<^esub> A) = a"
  by (metis OrDistA_alphabet_alt WF_ALPHA_PREDICATE_OVER_THEORY)

theorem SupA_DESIGNS_closure:
  "\<lbrakk>a \<in> DESIGN_ALPHABET; A \<subseteq> \<lbrakk>DESIGNS\<rbrakk>[a]\<T>\<rbrakk> \<Longrightarrow> (\<And>\<^bsub>a\<^esub> A) \<in> \<lbrakk>DESIGNS\<rbrakk>[a]\<T>"
  apply (rule THEORY_PRED_OVER_intro)
  apply (rule THEORY_PRED_intro)
  apply (simp_all add:alphabet)
  apply (metis H1_DistAndA_closure H2_DistAndA_closure Healthy_intro comp_def is_healthyD)
done

theorem SupA_is_lub: 
  "\<lbrakk> a \<in> DESIGN_ALPHABET; A \<subseteq> \<lbrakk>DESIGNS\<rbrakk>[a]\<T> \<rbrakk> \<Longrightarrow> 
    is_lub (OrderT DESIGNS a) (\<And>\<^bsub>a\<^esub> A) A"
  apply (rule least_UpperI)
  apply (metis (full_types) SupA_def SupA_is_sup WF_ALPHA_PREDICATE_OVER_THEORY alpha_complete_lattice.sup_upper gorder.select_convs(1))
  apply (simp add:Upper_def)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (simp_all)
  apply (metis SupA_DESIGNS_closure)
done

theorem InfA_DESIGNS_closure:
  "\<lbrakk>a \<in> DESIGN_ALPHABET; A \<subseteq> \<lbrakk>DESIGNS\<rbrakk>[a]\<T>; A \<noteq> {}\<rbrakk> \<Longrightarrow> (\<Or>\<^bsub>a\<^esub> A) \<in> \<lbrakk>DESIGNS\<rbrakk>[a]\<T>"
  apply (rule THEORY_PRED_OVER_intro)
  apply (rule THEORY_PRED_intro)
  apply (simp_all add:alphabet)
  apply (metis AH1_DistOrA_closure AH2_DistOrA_closure Healthy_elim Healthy_intro comp_def)
done

theorem InfA_is_glb:
  "\<lbrakk> a \<in> DESIGN_ALPHABET; A \<subseteq> \<lbrakk>DESIGNS\<rbrakk>[a]\<T>; A \<noteq> {} \<rbrakk> \<Longrightarrow> 
     is_glb (OrderT DESIGNS a) (\<Or>\<^bsub>a\<^esub> A) A"
  apply (rule greatest_LowerI, simp_all add:Lower_def)
  apply (metis InfA_def InfA_is_inf WF_ALPHA_PREDICATE_OVER_THEORY alpha_complete_lattice.inf_lower)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (metis InfA_DESIGNS_closure)
done

lemma UNREST_EvalA [unrest]: "vs \<sharp> \<lbrakk>p\<rbrakk>\<pi> \<Longrightarrow> vs \<sharp> p"
  by (metis EvalA_def UNREST_ALPHA_def)

theorem DESIGNS_complete_lattice: 
  assumes  "a \<in> DESIGN_ALPHABET"
  shows "complete_lattice (OrderT DESIGNS a)"
proof -
  interpret lat: lattice "OrderT DESIGNS a"
    by (metis DESIGNS_lattice assms)
  from assms show ?thesis
    apply (unfold_locales)
    apply (rule_tac x="\<And>\<^bsub>a\<^esub> A" in exI)
    apply (simp add: SupA_is_lub)
    apply (case_tac "A = {}")
    apply (simp)
    apply (rule_tac x="``true\<^bsub>a\<^esub> \<turnstile> false\<^bsub>a\<^esub>``" in exI)
    apply (simp add:greatest_def)
    apply (rule conjI)
    apply (rule closure)
    apply (simp_all add:alphabet)
    apply (rule unrest)
    apply (simp add:unrest evala)
    apply (utp_alpha_tac)
    apply (metis DesignA_evala DesignA_extreme_point_nok EvalA_FalseA EvalA_RefinementA EvalA_TrueA THEORY_PRED_OVER_alphabet TopAD_DESIGNS_greatest)
    apply (rule_tac x="\<Or>\<^bsub>a\<^esub> A" in exI)
    apply (simp add:InfA_is_glb)
  done
qed

theorem DESIGNS_bot:
  assumes "a \<in> DESIGN_ALPHABET"
  shows "``\<bottom>\<^bsub>DESIGNS[a]\<^esub>`` = ``true\<^bsub>a\<^esub>``"
proof -
  interpret lat: complete_lattice "OrderT DESIGNS a"
    by (metis DESIGNS_complete_lattice assms)
  show ?thesis
    apply (rule sym)
    apply (rule lat.bottom_eq)
    apply (simp_all)
    apply (metis TrueA_DESIGNS assms)
    apply (metis TrueA_DESIGNS_least)
 done
qed

theorem DESIGNS_top:
  assumes "a \<in> DESIGN_ALPHABET"
  shows "``\<top>\<^bsub>DESIGNS[a]\<^esub>`` = ``true\<^bsub>a\<^esub> \<turnstile> false\<^bsub>a\<^esub>``"
proof -
  interpret lat: complete_lattice "OrderT DESIGNS a"
    by (metis DESIGNS_complete_lattice assms)
  from assms show ?thesis
    apply (rule_tac sym)
    apply (rule lat.top_eq)
    apply (simp_all)
    apply (rule closure)
    apply (simp_all add:closure alphabet)
    apply (simp add:unrest evala)
    apply (metis DesignA_extreme_point_nok TopAD_DESIGNS_greatest)
 done
qed

(* Galois Connection *)

lemma DesignA_DESIGN_ALPHABET [closure]:
  "\<lbrakk> \<alpha> P \<in> REL_ALPHABET; \<alpha> Q \<in> REL_ALPHABET \<rbrakk> \<Longrightarrow>
     \<alpha>(``P \<turnstile> Q``) \<in> DESIGN_ALPHABET"
  apply (auto simp add:DESIGN_ALPHABET_def alphabet REL_ALPHABET_def)
  apply (simp_all add:closure)
done

definition "Des(R) = AH1(AH2(``R \<and> $okay\<acute>``))"

declare Des_def [evala]

lemma Des_alphabet [alphabet]: "\<alpha>(Des(R)) = \<alpha> R \<union>\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>"
  by (simp add:Des_def alphabet)

definition "Rel(D) = ``D[true/okay][true/okay\<acute>]``"

declare Rel_def [evala]

lemma DESIGNS_DESIGN_ALPHABET [closure]:
  "p \<in> \<lbrakk>DESIGNS\<rbrakk>\<T> \<Longrightarrow> \<alpha>(p) \<in> DESIGN_ALPHABET"
  by (auto simp add:alphabet)

lemma Rel_alphabet [alphabet]: 
  "\<alpha> D \<in> DESIGN_ALPHABET \<Longrightarrow> \<alpha>(Rel(D)) = \<alpha> D -\<^sub>f \<lbrace>okay\<down>, okay\<down>\<acute>\<rbrace>"
  by (auto simp add:Rel_def alphabet closure typing)

theorem Rel_DesignD:
  "\<lbrakk> okay\<down> \<notin>\<^sub>f \<alpha> P; okay\<down> \<notin>\<^sub>f \<alpha> Q
   ; okay\<down>\<acute> \<notin>\<^sub>f \<alpha> P; okay\<down>\<acute> \<notin>\<^sub>f \<alpha> Q \<rbrakk> \<Longrightarrow> Rel(``P \<turnstile> Q``) = ``P \<Rightarrow> Q``"
  apply (utp_alpha_tac)
  apply (rule conjI)
  apply (force)
  apply (simp add:DesignD_def usubst typing defined unrest)
done
  
theorem Des_as_DesignD:
  "Des(R) = ``true\<^bsub>\<alpha>(R)\<^esub> \<turnstile> R``"
  apply (simp add:Des_def)
  apply (utp_alpha_tac)
  apply (simp add:H2_split usubst typing defined)
  apply (utp_poly_auto_tac)
done

theorem DesignD_refine_iff:
  assumes 
    "OKAY \<sharp> P1" "OKAY \<sharp> P2"
    "OKAY \<sharp> Q1" "OKAY \<sharp> Q2"
  shows "`P1 \<turnstile> Q1` \<sqsubseteq> `P2 \<turnstile> Q2` \<longleftrightarrow> `P1 \<Rightarrow> P2` \<and> `P1 \<and> Q2 \<Rightarrow> Q1`"
  apply (unfold less_eq_WF_PREDICATE_def)
  apply (simp add:DesignD_refinement assms)
  apply (utp_pred_tac)
done

lemma DesignD_galois_lemma:
  assumes "OKAY \<sharp> P" "OKAY \<sharp> Q" "OKAY \<sharp> R"
  shows "`P \<turnstile> Q` \<sqsubseteq> `true \<turnstile> R` \<longleftrightarrow> `(P \<Rightarrow> Q)` \<sqsubseteq> `R`"
proof -
  have "`P \<turnstile> Q` \<sqsubseteq> `true \<turnstile> R` \<longleftrightarrow> `P \<Rightarrow> true` \<and> `P \<and> R \<Rightarrow> Q`"
    by (simp add:DesignD_refine_iff assms unrest)
  also have "... \<longleftrightarrow> `(P \<Rightarrow> Q) \<sqsubseteq> R`"
    by (utp_pred_auto_tac)
  finally show ?thesis 
    by (utp_pred_tac)
qed
  
lemma insert_inject:
  "\<lbrakk> x \<notin> xs; x \<notin> ys \<rbrakk> \<Longrightarrow> insert x xs = insert x ys \<longleftrightarrow> xs = ys"
  by (auto)

theorem DesignA_RelA_galois:
  assumes
    "\<alpha> P \<in> REL_ALPHABET" "\<alpha> Q \<in> REL_ALPHABET"
    "okay\<down> \<notin>\<^sub>f \<alpha>(P)" "okay\<down> \<notin>\<^sub>f \<alpha>(Q)"
    "okay\<down>\<acute> \<notin>\<^sub>f \<alpha>(P)" "okay\<down>\<acute> \<notin>\<^sub>f \<alpha>(Q)" 
    "okay\<down> \<notin>\<^sub>f \<alpha>(R)" "okay\<down>\<acute> \<notin>\<^sub>f \<alpha>(R)"
  shows "``P \<turnstile> Q`` \<sqsubseteq> Des(R) \<longleftrightarrow> Rel(``P \<turnstile> Q``) \<sqsubseteq> R"
using assms
  apply (simp add: Rel_DesignD Des_as_DesignD assms closure)
  apply (utp_alpha_tac)
  apply (subst DesignD_galois_lemma)
  apply (simp_all add:unrest)
  apply (subgoal_tac "(finsert okay\<down> (finsert okay\<down>\<acute> (\<alpha> P \<union>\<^sub>f \<alpha> Q)) = finsert okay\<down> (finsert okay\<down>\<acute> (\<alpha> R))) \<longleftrightarrow> (\<alpha> P \<union>\<^sub>f \<alpha> Q = \<alpha> R)")
  apply (simp)
  apply (simp add: Rep_fset_inject[THEN sym] insert_inject)
done

(*
definition TheoryRes :: "'a THEORY \<Rightarrow> 'a ALPHABET set \<Rightarrow> 'a THEORY" (infixl "'/\<^sub>T" 70) where
"T/\<^sub>TA = \<lparr> alphas = (alphas T) - A, healths = healths T \<rparr>"

lemma TheoryRes_closure:
  "UTP_THEORY T \<Longrightarrow> UTP_THEORY (T/\<^sub>TA)"
  apply (unfold_locales)
  apply (simp add:TheoryRes_def IDEMPOTENT_OVER_def, safe)
  apply (metis Healthy_apply UTP_THEORY.healths_idem is_healthy_def)
done

theorem DESIGNS_RelA_galois:
  assumes "P \<in> \<lbrakk>DESIGNS\<rbrakk>\<T>" "Q \<in> \<lbrakk>REL\<rbrakk>\<T>" 
  shows "P \<sqsubseteq> Des(Q) \<longleftrightarrow> Rel(P) \<sqsubseteq> Q"
  using assms
  apply (subst DESIGNS_form'[of "P"], simp)
  apply (subst DESIGNS_form'[of "P"]) back back
  apply (simp)
  apply (subst DesignA_RelA_galois)
  apply (simp_all add:alphabet closure typing defined unrest assms)
done

abbreviation "Rel_Des \<equiv> \<lparr> orderA = (OrderTA DESIGNS)
                        , orderB = (OrderTA REL)
                        , lower = Rel, upper = Des \<rparr>"

declare THEORY_PRED_OVER_alphabet [alphabet del]

theorem AH1_AH2_commute:
  "AH1(AH2(P)) = AH2(AH1(P))"
  by (utp_alpha_tac, metis H1_H2_commute)

theorem Rel_Des_Galois:
  "galois_connection Rel_Des"
  apply (unfold_locales, simp_all)
  apply (simp_all add: ftype_pred)
  apply (clarify)
  apply (rule)
  apply (subst alphabet)
  apply (simp add:closure)
  apply (simp add:alphabet)
  apply (metis DESIGNS_DESIGN_ALPHABET REL_ALPHABET_DESIGN_ALPHABET REL_ALPHABET_minus)
  apply (simp add:RELH_REL_ALPHABET closure)
  apply (simp add:alphabet closure)
  apply (clarify)
  apply (rule)
  apply (simp add:alphabet closure)
  apply (erule THEORY_PRED_elim)
  apply (simp add:DESIGN_ALPHABET_def)
  apply (metis (lifting, no_types) DesignA_DESIGN_ALPHABET DesignA_alphabet REL_ALPHABET_DESIGN_ALPHABET fset_simps(1) fset_simps(5) funion_finsert_right)
  apply (simp add:is_healthy_def Des_def)
  apply (metis (lifting, no_types) AH1_AH2_commute AH1_idem AH2_idem)
  apply (simp add:DESIGNS_form)
  apply (subst AH1_AH2_is_DesignA) back back
  apply (simp_all add:closure alphabet)
  apply (simp add:Des_def)
  apply (metis AH1_idem Healthy_intro)
  apply (simp add:alphabet closure)
  apply (simp add:closure)
  apply (subst Rel_alphabet)
  apply (simp add:alphabet closure)
  apply (simp add:DESIGN_ALPHABET_def)
  apply (simp add:closure)
  apply (simp add:alphabet closure)
  apply (simp)

lift_definition DESIGNS :: "'a THEORY" 
is "(DESIGN_ALPHABET, {AH1,AH2})"
  by (auto simp add:WF_THEORY_def IDEMPOTENT_OVER_def AH1_idem AH2_idem)

lemma DESIGNS_intro:
  "\<lbrakk> \<alpha> P \<in> REL_ALPHABET; P is AH1; P is AH2 \<rbrakk> 
  \<Longrightarrow> P \<in> \<lbrakk>DESIGNS\<rbrakk>\<T>"
  apply (simp add:THEORY_PRED_def DESIGNS.rep_eq DESIGN_ALPHABET_def is_healthy_def)
  apply (utp_alpha_tac)
  apply (auto)
  apply (smt finsert.rep_eq insert_iff)+
done

lift_definition NORMAL_DESIGNS :: "'a WF_THEORY" 
is "(DESIGN_ALPHABET, {AH1,AH3})"
  by (auto simp add:WF_THEORY_def IDEMPOTENT_OVER_def AH1_idem AH3_idem closure)

lift_definition FEASIBLE_DESIGNS :: "'a WF_THEORY" 
is "(DESIGN_ALPHABET, {AH1,AH3,AH4})"
  by (auto simp add:WF_THEORY_def IDEMPOTENT_OVER_def AH1_idem AH3_idem AH4_idem closure)

lemma NORMAL_DESIGNS_are_DESIGNS [closure]: 
  "P \<in> \<lbrakk>NORMAL_DESIGNS\<rbrakk>\<T> \<Longrightarrow> P \<in> \<lbrakk>DESIGNS\<rbrakk>\<T>"
  by (auto simp add:THEORY_PRED_def NORMAL_DESIGNS.rep_eq DESIGNS.rep_eq AH3_implies_AH2)

theorem AH1_true:
  "a \<in> DESIGN_ALPHABET \<Longrightarrow> true\<^bsub>a \<^esub>is AH1"
  by (utp_alpha_tac, utp_pred_tac)

theorem AH2_true:
  "a \<in> DESIGN_ALPHABET \<Longrightarrow> true\<^bsub>a \<^esub>is AH2"
  by (utp_alpha_tac, metis H3_WF_CONDITION H3_implies_H2 Healthy_elim TrueP_cond_closure)

theorem AH1_AndP:
  "P
  
lemma "a \<in> DESIGN_ALPHABET \<Longrightarrow> \<top>\<^bsub>DESIGNS[a]\<^esub> = ``true\<^bsub>a\<^esub> \<turnstile> false\<^bsub>a\<^esub>``"
  apply (simp add:top_theory_def)
  apply (rule the_equality)
  apply (auto simp add:alphabet closure)
  apply (rule DESIGNS_intro)
  apply (simp_all add:alphabet)
  apply (metis DESIGN_ALPHABET_ok DESIGN_ALPHABET_ok' REL_ALPHABET_DESIGN_ALPHABET Rep_fset_inject finsert.rep_eq insert_absorb)
  apply (simp add:is_healthy_def)
  apply (utp_alpha_tac, utp_pred_tac)
  apply (simp add:is_healthy_def)
  apply (utp_alpha_tac)
oops

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

*)



  


end