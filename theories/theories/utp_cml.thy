(******************************************************************************)
(* Project: Mechanation of the UTP                                            *)
(* File: utp_csp.thy                                                          *)
(* Authors: Samuel Canham and Simon Foster, University of York                *)
(******************************************************************************)

header {* CML Processes *}

theory utp_cml
imports 
  utp_csp_prime
begin

definition tock :: "('m EVENT USET) CHAN" where
"tock = MkCHAN (bName ''tock'', TYPE(('m EVENT USET)))"

definition SemiR_REA :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" (infix ";\<^bsub>REA\<^esub>" 50 ) where
"P ;\<^bsub>REA\<^esub> Q = `\<exists> tt1\<acute>\<acute>\<acute> . (\<exists> tt2\<acute>\<acute>\<acute> . P[$tt1\<acute>\<acute>\<acute>/tt\<acute>\<acute>\<acute>];Q[$tt2\<acute>\<acute>\<acute>/tt\<acute>\<acute>\<acute>] \<and> ($tt\<acute>\<acute>\<acute> = $tt1\<acute>\<acute>\<acute>^$tt2\<acute>\<acute>\<acute>))`"

definition DesignREA :: 
"'a WF_PREDICATE \<Rightarrow>
 'a WF_PREDICATE \<Rightarrow>
 'a WF_PREDICATE \<Rightarrow>
 'a WF_PREDICATE" (infixr "\<turnstile>_\<diamond>" 80) where
"p \<turnstile> q \<diamond> r = `p \<turnstile> (q \<lhd> $wait\<acute> \<rhd> r)`"

definition CML1 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"CML1 P = R1 `P[($tr\<acute>-$tr)/tt\<acute>\<acute>\<acute>]`"

definition CML2 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"CML2 P = `P \<lhd> ok \<rhd> ($tr \<le> $tr\<acute>)`"

definition CML3 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"CML3 P = `II\<^bsub>REA \<union> OKAY\<^esub> \<lhd> ok \<and> $wait \<rhd> P`"

definition RC :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"RC = CML1 \<circ> CML2 \<circ> CML3"

syntax
  "_upred_design_rea"   :: "upred \<Rightarrow> upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<turnstile>_\<diamond>" 50)
  "_upred_cml1"         :: "upred \<Rightarrow> upred" ("CML1'(_')")
  "_upred_cml2"         :: "upred \<Rightarrow> upred" ("CML2'(_')")
  "_upred_cml3"         :: "upred \<Rightarrow> upred" ("CML3'(_')")
  "_upred_rc"           :: "upred \<Rightarrow> upred" ("RC'(_')")
  "_upred_semir_rea"   :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infix ";\<^bsub>REA\<^esub>" 50)

translations
  "_upred_design_rea p q r"   == "CONST DesignREA p q r"
  "_upred_cml1 p"   == "CONST CML1 p"
  "_upred_cml2 p"   == "CONST CML2 p"
  "_upred_cml3 p"   == "CONST CML3 p"
  "_upred_rc p"     == "CONST RC p"
  "_upred_semir_rea p q" == "CONST SemiR_REA p q"

abbreviation "NON_CML_VAR \<equiv> REL_VAR - REA - OKAY"

definition Skip2CML :: "'a WF_PREDICATE" ("SKIP2") where
"SKIP2 = `RC(true \<turnstile> false \<diamond> ($tt\<acute>\<acute>\<acute>= \<langle>\<rangle> \<and> II\<^bsub>NON_CML_VAR\<^esub>))`"

lemma Skip2_form:
 "SKIP2 = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II\<^bsub>REA \<union> OKAY\<^esub>) \<or>
     (ok \<and> \<not> $wait \<and> II\<^bsub>REL_VAR - {ref \<down>,ref \<down>\<acute>}\<^esub>) `" (is "?lhs = ?rhs")
proof-
  have  "SKIP2 =  `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> R1(II\<^bsub>REA \<union> OKAY\<^esub>)) \<or> (ok \<and> \<not>$wait \<and> ok' \<and> \<not>$wait\<acute> \<and> ($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>)`"
    apply(simp add:Skip2CML_def RC_def CML3_def CML2_def CML1_def R1_def DesignREA_def DesignD_def CondR_def ImpliesP_def)
    apply(simp add:usubst typing defined closure)
    apply(simp add:AndP_OrP_distr AndP_OrP_distl AndP_assoc[THEN sym])
    apply(subst AndP_assoc)
    apply(subst AndP_idem)
    apply(subst AndP_comm) back back back back back back back back back back back back back
    apply(subst AndP_assoc) back back back back back back back back
    apply(subst tr_prefix_as_nil)
    apply(utp_poly_auto_tac)
  done
  also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> ($tr\<acute> = $tr) \<and> II\<^bsub>REA \<union> OKAY - {tr \<down>,tr \<down>\<acute>}\<^esub> \<and> ($tr \<le> $tr\<acute>)) \<or>
     (ok \<and> \<not> $wait \<and> ok' \<and> \<not> $wait\<acute> \<and> ($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>) `"
    apply(simp add:R1_def)
    apply(subst SkipRA_unfold_aux_ty[of "tr "])
    apply(simp_all add:closure typing)
    apply(utp_poly_auto_tac)
    done
  also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and>  II\<^bsub>REA \<union> OKAY\<^esub>) \<or> (ok \<and> \<not> $wait \<and>  II\<^bsub>REL_VAR - {ref \<down>,ref \<down>\<acute>}\<^esub>) `"  
    proof - 
      have 1: "REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {okay\<down>, okay\<down>\<acute>} = REL_VAR - {ref\<down>, ref\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>} - {okay\<down>, okay\<down>\<acute>}"
        by (auto)
      show ?thesis
        apply(subst AndP_comm) back back back back
        apply(subst AndP_assoc) back back
        apply(subst tr_eq_is_R1)
        apply(subst SkipRA_unfold_aux_ty[of "tr"]) back back
        apply(simp_all add:typing closure)
        apply(subst SkipRA_unfold_aux_ty[of "wait"]) back back back
        apply(simp_all add:typing closure)
        apply(subst SkipRA_unfold_aux_ty[of "tr"]) back back back
        apply(simp_all add:typing closure)
        apply(subst SkipRA_unfold_aux_ty[of "okay"]) back back back
        apply(simp_all add:typing closure)
        apply(subst 1)
        apply(utp_poly_auto_tac)
        done
    qed
      finally show ?thesis
      .
    qed
    
syntax
  "_upred_skip_cml"   :: "upred" ("SKIP2")

translations
  "_upred_skip_cml"   == "CONST Skip2CML"


definition CML4 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"CML4 P = `SKIP2 ; P`"

definition CML5 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"CML5 P = `P ; SKIP2`"

syntax
  "_upred_cml4"         :: "upred \<Rightarrow> upred" ("CML4'(_')")
  "_upred_cml5"         :: "upred \<Rightarrow> upred" ("CML5'(_')")

translations
  "_upred_cml4 p"   == "CONST CML4 p"
  "_upred_cml5 p"   == "CONST CML5 p"


definition CML :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"CML = CML1 \<circ> CML2 \<circ> CML3 \<circ> CML4 \<circ> CML5"
 
syntax
  "_upred_cml"         :: "upred \<Rightarrow> upred"("CML'(_')")  
translations
  "_upred_cml p"   == "CONST CML p" 

declare CML1_def [eval, evalr, evalrr, evalrx, evalp]
declare CML2_def [eval, evalr, evalrr, evalrx, evalp]
declare CML3_def [eval, evalr, evalrr, evalrx, evalp]
declare CML4_def [eval, evalr, evalrr, evalrx, evalp]
declare CML5_def [eval, evalr, evalrr, evalrx, evalp]
declare CML_def [eval, evalr, evalrr, evalrx, evalp]
declare RC_def [eval, evalr, evalrr, evalrx, evalp]
declare Skip2CML_def [eval, evalr, evalrr, evalrx, evalp]

lemma CML1_CML2_commute: "CML1 (CML2 P) = CML2 (CML1 P)" sorry
lemma CML1_CML3_commute: "CML1 (CML3 P) = CML3 (CML1 P)" sorry
lemma CML1_CML4_commute: "CML1 (CML4 P) = CML4 (CML1 P)" sorry
lemma CML1_CML5_commute: "CML1 (CML5 P) = CML5 (CML1 P)" sorry
lemma CML2_CML3_commute: "CML2 (CML3 P) = CML3 (CML2 P)" sorry
lemma CML2_CML4_commute: "CML2 (CML4 P) = CML4 (CML2 P)" sorry
lemma CML2_CML5_commute: "CML2 (CML5 P) = CML5 (CML2 P)" sorry
lemma CML3_CML4_commute: "CML3 (CML4 P) = CML4 (CML3 P)" sorry
lemma CML3_CML5_commute: "CML3 (CML5 P) = CML5 (CML3 P)" sorry
lemma CML4_CML5_commute: "CML4 (CML5 P) = CML5 (CML4 P)" sorry

lemma CML1_idempotent: "CML1 (CML1 P) = CML1 P" sorry
lemma CML2_idempotent: "CML2 (CML2 P) = CML2 P" sorry
lemma CML3_idempotent: "CML3 (CML3 P) = CML3 P" sorry
lemma CML4_idempotent: "CML4 (CML4 P) = CML4 P" sorry
lemma CML5_idempotent: "CML5 (CML5 P) = CML5 P" sorry

lemma DesignREA_form: 
  "`RC( A \<turnstile> B \<diamond> C )` = `(\<not>ok \<and> ($tr \<le> $tr \<acute>)) \<or> (ok \<and> $wait \<and> II\<^bsub>REA \<union> OKAY\<^esub>) \<or> (ok \<and> \<not>$wait \<and> CML1(\<not>A)) \<or> (ok \<and> \<not>$wait \<and> ok' \<and> $wait\<acute> \<and> CML1(A \<and> B)) \<or> (ok \<and> \<not>$wait \<and> ok' \<and> \<not>$wait\<acute> \<and> CML1(A \<and> C))`" (is "?lhs = ?rhs")
    apply(simp add:RC_def CML1_CML2_commute CML1_CML3_commute)
    apply(simp add:CML2_def CML3_def CML1_def R1_def DesignREA_def DesignD_def)
    apply(simp add:usubst typing defined closure)
    apply(utp_poly_auto_tac)
  done
 

lemma DesignREA_form_2: 
  "`RC( A \<turnstile> B \<diamond> C )` = `(\<not>ok \<and> ($tr \<le> $tr \<acute>)) \<or> (ok \<and> $wait \<and> II\<^bsub>REA \<union> OKAY\<^esub>) \<or> (ok \<and> \<not>$wait \<and> CML1(\<not>A)) \<or> (ok \<and> \<not>$wait \<and> ok' \<and> $wait\<acute> \<and> CML1(B)) \<or> (ok \<and> \<not>$wait \<and> ok' \<and> \<not>$wait\<acute> \<and> CML1(C))`" (is "?lhs = ?rhs")
    apply(simp add:RC_def CML1_CML2_commute CML1_CML3_commute)
    apply(simp add:CML2_def CML3_def CML1_def R1_def DesignREA_def DesignD_def)
    apply(simp add:usubst typing defined closure)
    apply(utp_poly_auto_tac)
  done

lemma CML1_CML2_SemiR_left_zero: 
  assumes "Q is CML1" "Q is CML2" "Q \<in> WF_RELATION"
  shows "`(\<not>ok \<and> ($tr \<le> $tr\<acute>));Q` = `(\<not>ok \<and> ($tr \<le> $tr\<acute>))`"
proof -
  have "`(\<not>ok \<and> ($tr \<le> $tr\<acute>));Q` = `(\<not>ok \<and> ($tr \<le> $tr\<acute>) \<and> (ok' \<or> \<not> ok')) ;Q`"
    by(subst OrP_excluded_middle,simp)
  also have "... = `((\<not>ok\<and> ($tr \<le> $tr\<acute>)) ; (ok \<and> Q)) \<or> ((\<not>ok \<and> ($tr \<le> $tr\<acute>)) ;(\<not>ok \<and> CML2(Q)))`"
    apply(simp add:AndP_OrP_distl SemiR_OrP_distr)
    apply(subst SemiR_AndP_right_precond)
    apply(simp_all add:closure typing defined assms urename)
    apply (metis DesignD_extreme_point_nok(2) R1_def R1_rel_closure TopD_rel_closure)
    apply(subst SemiR_AndP_right_precond)
    apply(simp_all add:closure typing defined assms urename)
    apply (metis DesignD_extreme_point_nok(2) R1_def R1_rel_closure TopD_rel_closure)
    apply (metis Healthy_simp assms(2) assms(3))
    apply (smt AndP_OrP_distl AndP_comm AndP_contra PVAR_VAR_pvdash R1_OrP R1_def R1_extend_AndP SemiR_OrP_distr TopD_def assms(1) assms(2) calculation demorgan3 is_healthy_def utp_pred_simps(1) utp_pred_simps(6))
    done
  also have "... = `R1((\<not>ok \<and> ($tr \<le> $tr\<acute>)) ; (ok \<and> Q)) \<or> ((\<not>ok \<and> ($tr \<le> $tr\<acute>)) ; (\<not>ok \<and> ($tr \<le> $tr\<acute>)))`" 
  proof - 
    have "`(\<not>ok \<and> ($tr \<le> $tr\<acute>)) ; (ok \<and> CML1(Q))` is R1"
      apply(subst R1_SemiR_closure)
      apply(simp_all add:closure typing defined assms is_healthy_def R1_def AndP_assoc[THEN sym])
      apply (metis DesignD_extreme_point_nok(2) R1_def R1_rel_closure TopD_rel_closure)
      apply(subst Healthy_simp[ of "Q" "CML1"])
      apply(simp_all add:assms closure)
      apply(simp add:CML1_def R1_def AndP_assoc[THEN sym])
    done
    hence  "`(\<not>ok \<and> ($tr \<le> $tr\<acute>)) ; (ok \<and> Q)` is R1"
      by(metis assms is_healthy_def)
    hence 1: "`R1((\<not>ok \<and> ($tr \<le> $tr\<acute>)) ; (ok \<and> Q))` = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) ; (ok \<and> Q)`"
      apply(subst Healthy_simp[of _ "R1"])
      apply(simp_all)
      done
    show ?thesis  
      apply(simp add:CML2_def CondR_def AndP_OrP_distl AndP_assoc)
      apply(subst AndP_comm) back back back
      apply(subst AndP_contra)
      apply(simp add:1)
      done
  qed
  also have "... = `\<not>ok \<and> ($tr \<le> $tr\<acute>)`"
    apply(subst SemiR_remove_middle_unrest1[of _ _ "{okay \<down>}"]) back    
    apply(simp_all add:closure typing defined unrest)
    apply (metis R1_def R1_rel_closure TopD_def TopD_rel_closure)
    apply (smt AndP_idem PVAR_VAR_pvdash PVarPE_def R1_def R1_rel_closure R2_def R2s_def SubstP_TrueP TrueP_rel_closure VAR_PVAR_erase_simps(2) bot_list_def bot_nat_def utp_pred_simps(3) utp_pred_simps(6))
    apply (subst SemiR_AndP_left_precond)
    apply(simp_all add:closure typing defined)
    apply (smt AndP_idem PVAR_VAR_pvdash PVarPE_def R1_def R1_rel_closure R2_def R2s_def SubstP_TrueP TrueP_rel_closure VAR_PVAR_erase_simps(2) bot_list_def bot_nat_def utp_pred_simps(3) utp_pred_simps(6))
    apply (metis AndP_rel_closure NotP_rel_closure TopD_def TopD_rel_closure assms(3) utp_pred_simps(3))
    apply (subst SemiR_AndP_left_precond)
    apply(simp_all add:closure typing defined)
    apply (smt AndP_idem PVAR_VAR_pvdash PVarPE_def R1_def R1_rel_closure R2_def R2s_def SubstP_TrueP TrueP_rel_closure VAR_PVAR_erase_simps(2) bot_list_def bot_nat_def utp_pred_simps(3) utp_pred_simps(6))
    apply(subst tr_leq_trans)
    apply(simp add:R1_def AndP_assoc[THEN sym])
    apply(subst AndP_comm) back back
    apply(subst AndP_assoc)
    apply(utp_poly_auto_tac)
    done
finally show ?thesis ..
qed  

lemma CML3_SemiR_left_zero: 
  assumes "Q is CML3" "Q \<in> WF_RELATION"
  shows "`(ok \<and> $wait \<and> II\<^bsub>{okay \<down>,okay \<down>\<acute>,wait \<down>,wait \<down>\<acute>,tr \<down>,tr \<down>\<acute>,ref \<down>,ref \<down>\<acute>}\<^esub>);Q` = `ok \<and> $wait \<and> II\<^bsub>REA \<union> OKAY\<^esub>`"
proof -
  have 1: "`ok \<and> $wait \<and> ($okay\<acute> = $okay) \<and> ($wait\<acute> = $wait) \<and> II\<^bsub>{tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>` = `ok \<and> $wait \<and> II\<^bsub>{tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub> \<and> ok' \<and> $wait\<acute>`"
    by(utp_poly_auto_tac)
  have "`(ok \<and> $wait \<and> II\<^bsub>REA \<union> OKAY\<^esub>);Q` =  `(ok \<and> $wait \<and> II\<^bsub>REA - {wait \<down>,wait \<down>\<acute>}\<^esub>);(ok \<and> $wait \<and> Q)`"
    apply(subst SkipRA_unfold_aux_ty[of "okay"])
    apply(simp_all add:closure typing)
    apply(subst SkipRA_unfold_aux_ty[of "wait"])
    apply(simp_all add:closure typing)
    apply(subst SemiR_AndP_right_precond)
    apply(simp_all add:closure typing)
    apply (metis (full_types) AndP_rel_closure MkPlainP_UNDASHED PUNDASHED_WF_CONDITION WF_CONDITION_WF_RELATION assms(2))
    apply(subst SemiR_AndP_right_precond)
    apply(simp_all add:closure typing urename)
    apply (metis assms(2))
    apply(simp add:AndP_assoc[THEN sym])
    apply(subst 1)
    apply(simp)
    done
  also have "... = `(ok \<and> $wait \<and> II\<^bsub>REA - {wait \<down>,wait \<down>\<acute>}\<^esub>);(ok \<and> $wait \<and> CML3(Q))`"
    by(metis assms Healthy_simp)
  also have "... = `(ok \<and> $wait \<and> II\<^bsub>REA - {wait \<down>,wait \<down>\<acute>}\<^esub>);(ok \<and> $wait \<and> II\<^bsub>REA \<union> OKAY\<^esub>)`"
    apply(simp add:CML3_def CondR_def AndP_OrP_distl)
    apply(subst AndP_assoc) back
    apply(subst AndP_assoc) back
    apply(subst AndP_idem)
    apply(subst AndP_assoc) back
    apply(subst AndP_assoc) back
    apply(subst AndP_contra)
    apply(simp)
    apply(subst AndP_assoc[THEN sym])
    apply(simp)
    done
  also have "... = `(ok \<and> $wait \<and> II\<^bsub>REA \<union> OKAY\<^esub>);II\<^bsub>REA \<union> OKAY\<^esub>`"
    proof -
      have 1 : "{okay\<down>, okay\<down>\<acute>, wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>} - {okay\<down>, okay\<down>\<acute>} = {tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}" 
        by(auto)
      have 2 : "`$okay \<and> $wait \<and> ($wait\<acute> = $wait) \<and> ($okay\<acute> = $okay) \<and> II\<^bsub>{tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>` = `$okay \<and> $wait \<and> II\<^bsub>{tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub> \<and> $okay\<acute> \<and> $wait\<acute>`"
        by(utp_poly_auto_tac)
      show ?thesis
        apply(subst SemiR_AndP_right_precond)
        apply(simp_all add:closure typing)
        apply(subst SemiR_AndP_right_precond)
        apply(simp_all add:closure typing urename)
        apply(subst SkipRA_unfold_aux_ty[of "wait "]) back back
        apply(simp_all add:closure typing)
        apply(subst SkipRA_unfold_aux_ty[of "okay "]) back back
        apply(simp_all add:closure typing defined)
        apply(subst 1)
        apply(subst 2)
        apply(simp add:AndP_assoc)
        done
    qed
    also have "... = `ok \<and> $wait \<and> II\<^bsub>REA \<union> OKAY\<^esub>`"
      apply(subst SemiR_AndP_left_precond)
      apply(simp_all add:closure typing)
      apply(subst SemiR_AndP_left_precond)
      apply(simp_all add:closure typing)
      done
    finally show ?thesis by (smt Un_commute Un_left_commute bot_set_def inf_sup_aci(5) inf_sup_aci(7) insert_commute insert_compr insert_is_Un sup.commute sup.left_commute sup_commute sup_left_commute)
qed

lemma CML4_form:
  assumes "P \<in> WF_RELATION" "P is CML1" "P is CML2" "P is CML3" "{ref \<down>} \<sharp> P\<^sub>f"
  shows "P is CML4"
proof - 
have "CML4 P = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II\<^bsub>REA \<union> OKAY\<^esub>) \<or> (ok \<and> \<not> $wait \<and> (II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub> ;  P))`"
apply(simp add:CML4_def Skip2_form SemiR_OrP_distr)
apply(subst CML1_CML2_SemiR_left_zero)
apply(simp_all add:assms)
apply(subst OrP_comm) back
apply(simp add:OrP_assoc)
apply(subst OrP_comm) back
apply(subst CML3_SemiR_left_zero)
apply(simp_all add:assms)
apply(subst SemiR_AndP_left_precond)
apply(simp_all add:assms closure typing)
apply(subst SemiR_AndP_left_precond)
apply(simp_all add:assms closure typing)
apply(simp add: OrP_assoc[THEN sym])
apply(subst OrP_comm)
apply(simp add: OrP_assoc[THEN sym])
apply(subst OrP_comm) back
apply(simp)
done
also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II\<^bsub>REA \<union> OKAY\<^esub>) \<or> (ok \<and> \<not> $wait \<and> (II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub> ; (\<not>$wait \<and>  P\<^sub>f)))`"
sorry (* utp_poly_laws / expr *)
also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II\<^bsub>REA \<union> OKAY\<^esub>) \<or> (ok \<and> \<not> $wait \<and> P\<^sub>f)`"
proof -
  have 1: " D\<^sub>0 - in (REL_VAR - {ref\<down>, ref\<down>\<acute>}) = {ref \<down>}" 
    apply(auto)
    apply(simp_all add:closure typing defined var_dist)
    done
  show ?thesis
    apply(subst SkipRA_left_unit)
    apply(simp_all add:closure typing defined assms unrest)
    apply(rule unrest)
    apply(simp add:typing defined closure unrest)
    apply(subst 1)
    apply(simp add:assms)
    apply(simp add:AndP_assoc)
    done
qed
also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II\<^bsub>REA \<union> OKAY\<^esub>) \<or> (ok \<and> \<not> $wait \<and> P)`"
sorry
also have "... = `CML2 (CML3 (P))`"
apply(simp add:CML2_def CML3_def CondR_def)
apply(utp_poly_auto_tac)
done
finally have "CML4 P = P" 
by (metis assms is_healthy_def)
thus ?thesis 
by(simp add:is_healthy_def)
 qed   

lemma SkipCML_rel_closure: 
  "SKIP2 \<in> WF_RELATION"
sorry

lemma CML1_AndP: 
  "`CML1(A \<and> B)` = `CML1(A) \<and> CML1(B)`"sorry

lemma UNREST_CML1: 
  assumes " vs \<sharp> P" " tr \<down> \<notin> vs" "tr \<down>\<acute> \<notin> vs"
  shows "vs \<sharp> `CML1(P)`"
sorry

theorem AndP_post_closure [closure]:
  "\<lbrakk> p \<in> WF_POSTCOND; q \<in> WF_POSTCOND \<rbrakk> \<Longrightarrow> p \<and>\<^sub>p q \<in> WF_POSTCOND"
  by (auto simp add:WF_POSTCOND_def intro:unrest closure)

theorem OrP_post_closure [closure]:
  "\<lbrakk> p \<in> WF_POSTCOND; q \<in> WF_POSTCOND \<rbrakk> \<Longrightarrow> p \<or>\<^sub>p q \<in> WF_POSTCOND"
  by (auto simp add:WF_POSTCOND_def intro:unrest closure)

theorem NotP_post_closure [closure]:
  "p \<in> WF_POSTCOND \<Longrightarrow> \<not>\<^sub>p p \<in> WF_POSTCOND"
  by (auto simp add:WF_POSTCOND_def intro:unrest closure)

lemma CML5_form: 
  assumes "`RC(A \<turnstile> B \<diamond> C)` \<in> WF_RELATION" 
          "D\<^sub>2 \<sharp> A"  "D\<^sub>2 \<sharp> B"  "D\<^sub>2 \<sharp> C" 
          "`CML1(A)` \<in> WF_RELATION" "`CML1(\<not>A)` \<in> WF_RELATION" "`CML1(B)` \<in> WF_RELATION" "`CML1(C)` \<in> WF_RELATION" 
          "D\<^sub>1 \<sharp> A" "D\<^sub>1 - out (REA \<union> OKAY) \<sharp> B" "{ref \<down>\<acute>} \<sharp> C"
          "`CML1(\<not>A);($tr \<le> $tr\<acute>)` = `CML1(\<not>A)`"
  shows "`RC(A \<turnstile> B \<diamond> C)` is CML5"
proof -
 have "`CML5 (RC(A \<turnstile> B \<diamond> C))` = ` (\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok\<and> $wait \<and> II\<^bsub>REA \<union> OKAY\<^esub>) \<or>
     (ok \<and> \<not> $wait \<and> CML1(\<not> A) \<and> (ok' \<or> \<not>ok')) ; SKIP2 \<or> (ok \<and> \<not> $wait \<and> CML1(A \<and> B) \<and> $wait\<acute> \<and> ok' ) ; SKIP2 \<or> (ok \<and> \<not> $wait \<and> CML1(A \<and> C) \<and> \<not> $wait\<acute> \<and> ok') ; SKIP2`"
 apply(simp add:CML5_def DesignREA_form SemiR_OrP_distr)
 apply(subst CML1_CML2_SemiR_left_zero)
 apply(simp add:Skip2CML_def is_healthy_def RC_def CML1_idempotent)
 apply(simp add:Skip2CML_def is_healthy_def RC_def CML1_CML2_commute CML2_idempotent)
 apply(simp add:SkipCML_rel_closure)
 apply(subst CML3_SemiR_left_zero)
 apply(simp add:Skip2CML_def is_healthy_def RC_def CML1_CML3_commute CML2_CML3_commute CML3_idempotent)
 apply(simp add:SkipCML_rel_closure)
 apply(subst OrP_excluded_middle)
 apply(simp)
apply(smt AndP_comm AndP_assoc)
done
  also have "... = ` (\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok\<and> $wait \<and> II\<^bsub>REA \<union> OKAY\<^esub>) \<or>
     (ok \<and> \<not> $wait \<and> CML1(\<not> A)) ; (ok \<and> SKIP2 )\<or> 
     (ok \<and> \<not> $wait \<and> CML1(\<not> A)) ; (\<not>ok \<and> SKIP2 ) \<or> 
     (ok \<and> \<not> $wait \<and> CML1(A \<and> B)) ;($wait \<and> ok \<and> SKIP2) \<or> 
     (ok \<and> \<not> $wait \<and> CML1(A \<and> C)) ; (\<not>$wait \<and> ok \<and> SKIP2)`"
    apply(simp add: AndP_OrP_distl)
    apply(subst SemiR_OrP_distr)
    apply(simp add:OrP_assoc[THEN sym])
    apply(subst SemiR_algebraic)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp add:CML1_def R1_def)
    apply(rule unrest)
    apply(rule UNREST_SubstP[of _ _ "D\<^sub>2" _ "D\<^sub>2"])
    apply(simp_all add:typing defined closure unrest)
    apply(rule unrest)
    apply(simp add:assms)
    apply(simp add:Skip2_form)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp_all add:closure typing defined unrest)
    apply(subst SemiR_algebraic)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp add:CML1_def R1_def)
    apply(rule unrest)
    apply(rule UNREST_SubstP[of _ _ "D\<^sub>2" _ "D\<^sub>2"])
    apply(simp_all add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp add:assms)
    apply(simp add:Skip2_form)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp_all add:closure typing defined unrest)
    apply(subst SemiR_algebraic)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp add:CML1_def R1_def)
    apply(rule unrest)
    apply(rule UNREST_SubstP[of _ _ "D\<^sub>2" _ "D\<^sub>2"])
    apply(simp_all add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp_all add:assms)
    apply(simp add:Skip2_form)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp_all add:closure typing defined unrest)
    apply(subst SemiR_algebraic)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp add:CML1_def R1_def)
    apply(rule unrest)
    apply(rule UNREST_SubstP[of _ _ "D\<^sub>2" _ "D\<^sub>2"])
    apply(simp_all add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp_all add:assms)
    apply(simp add:Skip2_form)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp_all add:closure typing defined unrest)
    apply(subst SemiR_algebraic)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(simp add:CML1_def R1_def)
    apply(rule unrest)
    apply(rule UNREST_SubstP[of _ _ "D\<^sub>2" _ "D\<^sub>2"])
    apply(simp_all add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp_all add:assms)
    apply(simp add:Skip2_form)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp_all add:closure typing defined unrest)
    apply(subst SemiR_algebraic)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(simp add:CML1_def R1_def)
    apply(rule unrest)
    apply(rule UNREST_SubstP[of _ _ "D\<^sub>2" _ "D\<^sub>2"])
    apply(simp_all add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp_all add:assms)
    apply(simp add:Skip2_form)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp_all add:closure typing defined unrest)
    apply(subst SemiR_algebraic)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(simp add:CML1_def R1_def)
    apply(rule unrest)
    apply(rule UNREST_SubstP[of _ _ "D\<^sub>2" _ "D\<^sub>2"])
    apply(simp_all add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp_all add:assms)
    apply(simp add:Skip2_form)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp_all add:closure typing defined unrest)
    apply(subst SemiR_algebraic)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(simp add:CML1_def R1_def)
    apply(rule unrest)
    apply(rule UNREST_SubstP[of _ _ "D\<^sub>2" _ "D\<^sub>2"])
    apply(simp_all add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp_all add:assms)
    apply(simp add:Skip2_form)
    apply(rule unrest)
    apply(simp add:closure typing defined unrest)
    apply(rule unrest)
    apply(simp_all add:closure typing defined unrest)
    apply(simp add:urename closure typing defined AndP_assoc[THEN sym])
    done
also have "... = 
    `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     (ok \<and> $wait \<and> II\<^bsub>{okay\<down>, okay\<down>\<acute>, wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>) \<or>
     (ok \<and> \<not> $wait \<and> CML1(\<not> A)) ; ($okay \<and> $wait \<and> II\<^bsub>{okay\<down>, okay\<down>\<acute>, wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>) \<or> 
     (ok \<and> \<not> $wait \<and> CML1(\<not> A)) ; ($okay \<and> \<not> $wait \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>) \<or>
     (ok \<and> \<not> $wait \<and> CML1(\<not> A)) ; (\<not> $okay \<and> ($tr \<le> $tr\<acute>)) \<or>
     (ok \<and> \<not> $wait \<and> CML1(A \<and> B) \<and> ok' \<and> $wait \<acute>) ; II\<^bsub>{okay\<down>, okay\<down>\<acute>, wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub> \<or> 
     (ok \<and> \<not> $wait \<and> CML1(A \<and> C) \<and> ok' \<and> \<not> $wait \<acute>) ;  II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>`"
  proof -
    have 1: "`ok \<and> SKIP2` = `(ok \<and> $wait \<and> II\<^bsub>REA \<union> OKAY\<^esub>) \<or> (ok \<and> \<not>$wait \<and> II\<^bsub>REL_VAR - {ref \<down>,ref \<down>\<acute>}\<^esub>)`" 
      apply(simp add:Skip2_form)
      apply(utp_poly_auto_tac)
      done
    have 2: "`\<not>ok \<and> SKIP2` = `\<not>ok \<and> ($tr \<le> $tr \<acute>)`"
      apply(simp add:Skip2_form)
      apply(utp_poly_auto_tac)
      done
    have 3: "`\<not>$wait \<and> ok \<and> SKIP2` = `(ok \<and> \<not>$wait \<and> II\<^bsub>REL_VAR - {ref \<down>,ref \<down>\<acute>}\<^esub>)`"
      apply(simp add:Skip2_form)
      apply(utp_poly_auto_tac)
      done
    have 4: "`$wait \<and> ok \<and> SKIP2` =  `(ok \<and> $wait \<and> II\<^bsub>REA \<union> OKAY\<^esub>)`" 
      apply(simp add:Skip2_form)
      apply(utp_poly_auto_tac)
      done
    show ?thesis
      apply(simp add:3 4)
      apply(simp add:1 2 SemiR_OrP_distl OrP_assoc[THEN sym])
      apply(subst SemiR_algebraic) back back back
      defer 
      defer 
      apply(subst SemiR_algebraic) back back back
      defer 
      defer 
      apply(subst SemiR_algebraic) back back back back back back
      defer 
      defer 
      apply(subst SemiR_algebraic) back back back back back back
      defer 
      defer 
      apply(simp add:urename closure typing defined AndP_assoc[THEN sym])
      apply(simp_all add:typing defined closure unrest)
      apply(rule unrest)
      defer 
      apply(rule unrest)
      defer
      apply(simp add:CML1_def R1_def)
      apply(rule unrest)
      defer
      defer 
      apply(rule unrest)
      defer
      apply(rule unrest)
      defer 
      apply(simp add:CML1_def R1_def)
      apply(rule unrest)
      defer
      apply(rule unrest)
      defer
      apply(rule unrest)
      defer 
      apply(rule unrest)
      defer
      apply(simp add:CML1_def R1_def)
      apply(rule unrest)
      defer
      defer 
      apply(rule unrest)
      defer
      apply(rule unrest)
      defer 
      apply(simp add:CML1_def R1_def)
      apply(rule unrest)
      defer
      apply(rule unrest)
      defer
      apply(simp_all add:typing defined closure unrest)
      apply(subst UNREST_SubstP[of _ _ "D\<^sub>2" _ "D\<^sub>2"])    
      apply(simp_all add:typing defined closure unrest)
      apply(rule unrest)
      apply(simp_all add:assms)
      apply(subst UNREST_SubstP[of _ _ "D\<^sub>2" _ "D\<^sub>2"])    
      apply(simp_all add:typing defined closure unrest)
      apply(rule unrest)
      apply(simp_all add:assms)
      apply(rule unrest)
      apply(subst UNREST_SubstP[of _ _ "D\<^sub>2" _ "D\<^sub>2"])    
      apply(simp_all add:typing defined closure unrest)
      apply(rule unrest)
      apply(simp_all add:assms)
      apply(rule unrest)
      apply(subst UNREST_SubstP[of _ _ "D\<^sub>2" _ "D\<^sub>2"])    
      apply(simp_all add:typing defined closure unrest)
      apply(rule unrest)
      apply(simp_all add:assms)
      done
qed
also have "... = 
    `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     (ok \<and> $wait \<and> II\<^bsub>{okay\<down>, okay\<down>\<acute>, wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>) \<or>
     (ok \<and> \<not> $wait \<and> CML1(\<not> A)) ; ($okay \<and> $wait \<and> II\<^bsub>{okay\<down>, okay\<down>\<acute>, wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>) \<or> 
     (ok \<and> \<not> $wait \<and> CML1(\<not> A)) ; ($okay \<and> \<not> $wait \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>) \<or>
     (ok \<and> \<not> $wait \<and> CML1(\<not> A)) ; (\<not> $okay \<and> ($tr \<le> $tr\<acute>)) \<or>
     (ok \<and> \<not> $wait \<and> CML1(A \<and> B) \<and> ok' \<and> $wait \<acute>) \<or> 
     (ok \<and> \<not> $wait \<and> CML1(A \<and> C) \<and> ok' \<and> \<not> $wait \<acute>)`"
apply(subst SkipRA_right_unit)
apply(simp_all add:typing defined closure unrest assms CML1_AndP)
apply(rule unrest)
apply(simp add:typing defined closure unrest assms)
apply(rule unrest)
apply(simp add:typing defined closure unrest assms)
apply(rule unrest)
apply(rule unrest)
apply(simp_all add:typing defined closure unrest assms CML1_AndP)
defer 
defer 
apply(subst SkipRA_right_unit)
apply(simp_all add:typing defined closure unrest assms CML1_AndP)
apply(rule unrest)
apply(simp add:typing defined closure unrest assms)
apply(rule unrest)
apply(simp add:typing defined closure unrest assms)
apply(rule unrest)
apply(rule unrest)
apply(simp_all add:typing defined closure unrest assms CML1_AndP)
apply(subst UNREST_CML1)
apply(subst UNREST_subset[of "D\<^sub>1"] )
apply(simp_all add:assms)
apply(subst UNREST_CML1)
apply(subst UNREST_subset[of "{ref \<down>\<acute>}"] )
apply(simp_all add:assms)
defer 
apply(subst UNREST_CML1)
apply(subst UNREST_subset[of "D\<^sub>1"] )
apply(simp_all add:assms)
apply(subst UNREST_CML1)
apply(subst UNREST_subset[of "D\<^sub>1 - out(REA \<union> OKAY)"] )
apply(subst assms)
apply(simp_all add:assms var_dist closure)
done
also have "... = 
    `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     (ok \<and> $wait \<and> II\<^bsub>{okay\<down>, okay\<down>\<acute>, wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>) \<or>
     (ok \<and> \<not> $wait \<and> CML1(\<not> A)) ; (ok \<and> $wait \<and> II\<^bsub>{ tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub> \<and> (ok' \<and> $wait\<acute>)) \<or> 
     (ok \<and> \<not> $wait \<and> CML1(\<not> A)) ; (ok \<and> \<not>$wait \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>,okay \<down>,okay \<down>\<acute>,wait \<down>,wait \<down>\<acute>}\<^esub> \<and> (ok' \<and> \<not>$wait\<acute>)) \<or>
     (ok \<and> \<not> $wait \<and> CML1(\<not> A)) ; ( \<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     (ok \<and> \<not> $wait \<and> CML1(A \<and> B) \<and> ok' \<and> $wait \<acute>) \<or> 
     (ok \<and> \<not> $wait \<and> CML1(A \<and> C) \<and> ok' \<and> \<not> $wait \<acute>)`"
proof -
  have 1: "`(ok \<and> $wait \<and> II\<^bsub>{okay\<down>, okay\<down>\<acute>, wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>) ` = `(ok \<and> $wait \<and> II\<^bsub>{tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub> \<and> ($okay\<acute> \<and> $wait\<acute>))`" 
          apply(subst SkipRA_unfold_aux_ty[of "okay"])
          apply(simp_all add:typing closure)
          apply(subst SkipRA_unfold_aux_ty[of "wait"])
          apply(simp_all add:typing closure)
          apply(utp_poly_auto_tac)
          done
  have 2: " `($okay \<and> \<not> $wait \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>)` = `(ok \<and> \<not>$wait \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>,okay \<down>,okay \<down>\<acute>,wait \<down>,wait \<down>\<acute>}\<^esub> \<and> (ok' \<and> \<not>$wait\<acute>))`"
    apply(subst SkipRA_unfold_aux_ty[of "okay"])
    apply(simp_all add:typing closure)
    apply(subst SkipRA_unfold_aux_ty[of "wait"])
    apply(simp_all add:typing closure)
    apply(utp_poly_auto_tac)
    sorry
    show ?thesis by(simp add:1 2) qed
also have "... = 
    `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     (ok \<and> $wait \<and> II\<^bsub>{okay\<down>, okay\<down>\<acute>, wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>) \<or>
     (((ok \<and> \<not> $wait \<and> CML1(\<not> A)) ; II\<^bsub>{ tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>) \<and> ok' \<and> $wait\<acute>) \<or> 
     (((ok \<and> \<not> $wait \<and> CML1(\<not> A)) ; II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>,okay \<down>,okay \<down>\<acute>,wait \<down>,wait \<down>\<acute>}\<^esub>) \<and> ok' \<and> \<not>$wait\<acute>) \<or>
     (ok \<and> \<not> $wait \<and> CML1(\<not> A)) ; ($tr \<le> $tr\<acute>) \<or>
     (ok \<and> \<not> $wait \<and> CML1(A \<and> B) \<and> ok' \<and> $wait \<acute>) \<or> 
     (ok \<and> \<not> $wait \<and> CML1(A \<and> C) \<and> ok' \<and> \<not> $wait \<acute>)`"
apply(subst AndP_assoc) back back
apply(subst SemiR_remove_middle_unrest1[of _ _ "{okay \<down>,wait \<down>}"])
apply(simp_all add:typing defined closure unrest assms)
apply(rule unrest) defer 
apply(rule unrest) defer 
apply(rule UNREST_CML1) 
apply(rule unrest)
apply(rule UNREST_subset[of "D\<^sub>1"])
apply(simp_all add:typing defined closure assms unrest)
apply(rule unrest)
apply(rule UNREST_subset[of "VAR - {tr \<down>,tr \<down>\<acute>,ref \<down>,ref \<down>\<acute>}"])
apply(simp_all add:typing defined closure assms unrest)
apply(utp_poly_auto_tac)
defer 
apply(subst AndP_assoc) back back back back
apply(subst SemiR_remove_middle_unrest1[of _ _ "{okay \<down>,wait \<down>}"]) back
apply(simp_all add:typing defined closure unrest assms)
apply(rule unrest) defer 
apply(rule unrest) defer 
apply(rule UNREST_CML1) 
apply(rule unrest)
apply(rule UNREST_subset[of "D\<^sub>1"])
apply(simp_all add:typing defined closure assms unrest)
apply(rule unrest)
apply(rule UNREST_subset[of "VAR - (REL_VAR - {ref \<down>,ref \<down>\<acute>,okay \<down>,okay \<down>\<acute>,wait \<down>,wait \<down>\<acute>})"])
apply(rule UNREST_SkipRA)
apply(auto)[1]
apply(simp_all add:typing defined closure assms unrest)
apply(utp_poly_auto_tac)
defer 
apply(subst SemiR_remove_middle_unrest1[of _ _ "{okay \<down>}"]) back back
apply(simp_all add:typing defined closure unrest assms)
apply (smt AndP_idem PVAR_VAR_pvdash R1_def R1_rel_closure R2_def R2s_def SubstP_TrueP TrueP_rel_closure VAR_PVAR_erase_simps(2) bot_list_def bot_nat_def utp_pred_simps(3) utp_pred_simps(6))
apply(rule unrest) back back
apply(simp_all add:typing defined closure unrest assms)
apply(rule unrest) back back
apply(simp_all add:typing defined closure unrest assms)
apply(rule UNREST_CML1)
apply(rule unrest) back back
apply(rule UNREST_subset[of "D\<^sub>1"])
apply(simp_all add:typing defined closure unrest assms)
apply(subst SemiR_AndP_right_postcond)
apply(simp_all add:typing defined closure assms)
apply(subst SemiR_AndP_right_postcond)
apply(simp_all add:typing defined closure assms)
apply(rule_tac x="\<B>(okay :=\<^sub>* True, wait :=\<^sub>* True)" in exI, simp add:typing defined closure)
apply(rule_tac x="\<B>(okay :=\<^sub>* True, wait :=\<^sub>* False)" in exI, simp add:typing defined closure)
done
also have "... = 
    `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     (ok \<and> $wait \<and> II\<^bsub>{okay\<down>, okay\<down>\<acute>, wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>) \<or>
     (ok \<and> \<not> $wait \<and> CML1(\<not> A) \<and> ok' ) \<or>
     (ok \<and> \<not> $wait \<and> CML1(\<not> A)) ; ($tr \<le> $tr\<acute>) \<or>
     (ok \<and> \<not> $wait \<and> CML1(A \<and> B) \<and> ok' \<and> $wait \<acute>) \<or> 
     (ok \<and> \<not> $wait \<and> CML1(A \<and> C) \<and> ok' \<and> \<not> $wait \<acute>)`"
apply(subst SkipRA_right_unit)
apply(simp_all add:closure typing defined assms unrest)
apply(rule unrest) defer 
apply(rule unrest) defer 
apply(rule UNREST_CML1)
apply(rule unrest)
apply(rule UNREST_subset[of "D\<^sub>1"])
apply(simp_all add:assms closure typing defined unrest)
apply(subst SkipRA_right_unit)
apply(simp_all add:closure typing defined assms unrest)
apply(rule unrest) defer 
apply(rule unrest) defer 
apply(rule UNREST_CML1)
apply(rule unrest)
apply(rule UNREST_subset[of "D\<^sub>1"])
apply(simp_all add:assms closure typing defined unrest)
apply(utp_poly_auto_tac)
done
also have "... = 
    `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     (ok \<and> $wait \<and> II\<^bsub>{okay\<down>, okay\<down>\<acute>, wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>) \<or>
     (ok \<and> \<not> $wait \<and> CML1(\<not> A)) ; ($tr \<le> $tr\<acute>) \<or>
     (ok \<and> \<not> $wait \<and> CML1(A \<and> B) \<and> ok' \<and> $wait \<acute>) \<or> 
     (ok \<and> \<not> $wait \<and> CML1(A \<and> C) \<and> ok' \<and> \<not> $wait \<acute>)`"
sorry
also have "... = 
    `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     (ok \<and> $wait \<and> II\<^bsub>{okay\<down>, okay\<down>\<acute>, wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>) \<or>
     (ok \<and> \<not> $wait \<and> CML1(\<not> A)) \<or>
     (ok \<and> \<not> $wait \<and> CML1(A \<and> B) \<and> ok' \<and> $wait \<acute>) \<or> 
     (ok \<and> \<not> $wait \<and> CML1(A \<and> C) \<and> ok' \<and> \<not> $wait \<acute>)`"
apply(subst AndP_assoc) back
apply(subst SemiR_AndP_left_precond[of _ _ "`ok \<and> \<not>$wait`"])
apply(simp_all add:closure typing defined assms)
apply (smt AndP_idem PVAR_VAR_pvdash R1_def R1_rel_closure R2_def R2s_def SubstP_TrueP TrueP_rel_closure VAR_PVAR_erase_simps(2) bot_list_def bot_nat_def utp_pred_simps(3) utp_pred_simps(6))
apply (simp add: AndP_assoc[THEN sym])
done
also have "... = `RC(A \<turnstile> B \<diamond> C)`" 
apply(simp add:DesignREA_form) 
apply(utp_poly_auto_tac) 
done
finally show ?thesis by(simp add:is_healthy_def) 
qed


lemma RC_DesignREA_rel_closure: 
  assumes "`CML1(\<not>A)` \<in> WF_RELATION" "`CML1(A)` \<in> WF_RELATION" "`CML1(B)` \<in> WF_RELATION" "`CML1(C)` \<in> WF_RELATION"
  shows " `RC( A \<turnstile> B \<diamond> C)` \<in> WF_RELATION"
sorry

lemma DesignREA_closure: 
  assumes "REA \<union> D\<^sub>1 \<sharp> A" "REA \<union> D\<^sub>1 - {ref\<down>\<acute>} \<sharp> B" "REA \<sharp> C" "`RC( A \<turnstile> B \<diamond> C )` \<in> WF_RELATION" 
      "`CML1(A)` \<in> WF_RELATION" "`CML1(\<not>A)` \<in> WF_RELATION" "`CML1(B)` \<in> WF_RELATION" "`CML1(C)` \<in> WF_RELATION"
      "D\<^sub>2 \<sharp> A" "D\<^sub>2 \<sharp> B" "D\<^sub>2 \<sharp> C" "`CML1(\<not>A);($tr \<le> $tr\<acute>)` = `CML1(\<not>A)`"
  shows "`RC( A \<turnstile> B \<diamond> C )` is CML"
proof -
  have 1: "`RC( A \<turnstile> B \<diamond> C )` is CML1" 
    by(simp add:is_healthy_def RC_def CML1_idempotent)
  have 2: "`RC( A \<turnstile> B \<diamond> C )` is CML2" 
    by(simp add:is_healthy_def RC_def CML2_idempotent CML1_CML2_commute)
  have 3: "`RC( A \<turnstile> B \<diamond> C )` is CML3" 
    by(simp add:is_healthy_def RC_def CML3_idempotent CML1_CML3_commute CML2_CML3_commute)
  have 4: "`RC( A \<turnstile> B \<diamond> C )` is CML4" 
    apply(subst CML4_form)
    apply(simp_all add:assms closure typing defined 1 2 3)
    apply(simp add:RC_def CML1_def DesignREA_def DesignD_def ImpliesP_def CML2_def CML3_def  R1_def CondR_def usubst typing defined closure)
    apply(simp add:AndP_OrP_distr AndP_OrP_distl)
    apply(simp add:AndP_assoc[THEN sym])
    apply(rule unrest) back
    apply(rule unrest) back
    apply(rule unrest) back
    defer 
    apply(rule unrest) back
    apply(rule unrest) back
    apply(rule unrest) back
    defer 
    apply(rule UNREST_SubstP[of _ _ "{ref \<down>}" _ "{ref \<down>}"])
    apply(simp_all add:typing defined closure unrest)
    apply(rule UNREST_SubstP[of _ _ "{ref \<down>}" _ "{ref \<down>}"])
    apply(simp_all add:typing defined closure unrest)
    apply(rule UNREST_subset[of "REA \<union> D\<^sub>1"])
    apply (metis Un_commute assms(1))
    apply(auto)
    apply(rule unrest) back
    apply(rule unrest) back
    defer 
    apply(rule unrest) back
    defer 
    apply(rule unrest) back
    defer 
    apply(rule unrest) back
    apply(rule UNREST_SubstP[of _ _ "{ref \<down>}" _ "{ref \<down>}"])
    apply(simp_all add:typing defined closure unrest)
    apply(rule UNREST_SubstP[of _ _ "{ref \<down>}" _ "{ref \<down>}"])
    apply(simp_all add:typing defined closure unrest)
    apply(rule UNREST_subset[of "REA \<union> D\<^sub>1 - {ref \<down>\<acute>}"])
    apply (metis Un_commute assms(2))
    apply(auto)
    apply(rule unrest) back
    defer 
    apply(rule unrest) back
    defer 
    apply(rule unrest) back
    defer 
    apply(rule unrest) back
    apply(rule UNREST_SubstP[of _ _ "{ref \<down>}" _ "{ref \<down>}"])
    apply(simp_all add:typing defined closure unrest)
    apply(rule UNREST_SubstP[of _ _ "{ref \<down>}" _ "{ref \<down>}"])
    apply(simp_all add:typing defined closure unrest)
    apply(rule UNREST_subset[of "REA"])
    apply (metis Un_commute assms(3))
    apply(auto)
  done
  have 5: "`RC( A \<turnstile> B \<diamond> C )` is CML5"
  apply(subst CML5_form)
  apply(simp_all add:assms closure typing defined unrest)
  apply(subst UNREST_subset[of "REA \<union> D\<^sub>1"])
  apply(rule assms)
  apply(auto)
  apply(subst UNREST_subset[of "REA \<union> D\<^sub>1 - {ref \<down>\<acute>}"])
  apply(rule assms)
  apply(auto)
  apply(subst UNREST_subset[of "REA"])
  apply(rule assms)
  apply(auto)
  done
  show ?thesis
  by (metis (no_types) "3" "4" "5" "2" "1" CML_def Healthy_intro Healthy_simp RC_def o_eq_dest_lhs)
qed

lemma Precondition_SemiR: 
  assumes "{okay \<down>\<acute>} \<sharp> P" "Q is RC" "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "`P ; Q` = `P ; ($tr \<le> $tr\<acute>)`"
proof -
  have "`P ; Q` = `(P \<and> (ok' \<or> \<not>ok'));Q`" sorry
  also have "... = `(P ; (ok \<and> Q)) \<or> (P ; (\<not>ok \<and> Q))`" 
    apply(simp add:R1_def AndP_assoc[THEN sym])
    apply(subst SemiR_AndP_right_precond)
    apply(simp_all add:closure typing defined assms)
    apply(subst SemiR_AndP_right_precond)
    apply(simp_all add:closure typing defined assms)
    apply(simp add:urename SemiR_OrP_distr AndP_OrP_distl typing defined closure)
    done
  also have "... = `(P ; (ok \<and> RC(Q))) \<or> (P ; (\<not>ok \<and> RC(Q)))`" 
    by(metis assms is_healthy_def)
  also have "... = `(P ; (ok \<and> R1(RC(Q)))) \<or> (P ; (\<not>ok \<and> CML2(RC(Q))))`" 
    apply(simp add:RC_def CML1_CML2_commute CML2_idempotent)
    apply(simp add:CML1_CML2_commute[THEN sym])
    apply(simp add:CML1_def R1_idempotent)
    done
  also have "... = `(P ; (ok \<and> R1(Q))) \<or> (P ; (\<not>ok \<and> CML2(Q)))`" 
    by(metis assms is_healthy_def)
  also have "... = `P ; ($tr \<le> $tr\<acute>)`"
    apply(simp add:CML2_def CondR_def AndP_OrP_distl AndP_assoc)
    apply(subst AndP_comm) back
    apply(simp add:AndP_contra)
    apply(subst SemiR_remove_middle_unrest1[of _ _ "{okay \<down>}"]) back
    apply(simp_all add:closure typing defined assms unrest)
    apply (smt R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
    apply(subst AndP_comm)
    apply(simp add: R1_extend_AndP SemiR_OrP_distl[THEN sym])
    apply(simp add:R1_def)
    apply (smt AndP_comm R1_OrP R1_def demorgan3 utp_pred_simps(12) utp_pred_simps(13) utp_pred_simps(15) utp_pred_simps(4) utp_pred_simps(7))
    done
  finally show ?thesis
    ..
qed

lemma CML1_OrP: 
  "`CML1(P \<or> Q)` = `CML1(P) \<or> CML1(Q)`" sorry

lemma CML1_SemiR: 
  "`CML1(P);CML1(Q)` = `CML1(\<exists> tt1\<acute>\<acute>\<acute> . \<exists> tt2\<acute>\<acute>\<acute> . P[$tt1\<acute>\<acute>\<acute>/tt\<acute>\<acute>\<acute>];Q[$tt2\<acute>\<acute>\<acute>/tt\<acute>\<acute>\<acute>] \<and> ($tt\<acute>\<acute>\<acute> = $tt1\<acute>\<acute>\<acute>^$tt2\<acute>\<acute>\<acute>))`"
sorry

lemma CML1_AndP_NotP: 
  "`CML1(P) \<and> \<not>CML1(Q)` = `CML1(P \<and> \<not>Q)`" sorry

lemma DesignREA_SemiR: 
  assumes "`CML1(\<not>D)` \<in> WF_RELATION" "`CML1(D)` \<in> WF_RELATION" "`CML1(E)` \<in> WF_RELATION" "`CML1(F)` \<in> WF_RELATION" "`RC( D \<turnstile> E \<diamond> F)` \<in> WF_RELATION"
          "`CML1(\<not>A)` \<in> WF_RELATION" "`CML1(A)` \<in> WF_RELATION" "`CML1(B)` \<in> WF_RELATION" "`CML1(C)` \<in> WF_RELATION" 
      "{okay  \<down>\<acute>} \<sharp> `CML1(\<not>A)`"  "`CML1(\<not>A);($tr \<le> $tr\<acute>)` = `CML1(\<not>A)`" "{okay \<down>,wait \<down>} \<sharp> `CML1(\<not>D)`"  "{okay \<down>\<acute>,wait \<down>\<acute>} \<sharp> `CML1(C)`" "{okay \<down>,wait \<down>} \<sharp> `CML1(E)`" "{okay \<down>,wait \<down>} \<sharp> `CML1(F)`"
       "D\<^sub>1 - {tr \<down>\<acute>} \<sharp> `CML1(A)`" "D\<^sub>1 - out(REA \<union> OKAY) \<sharp> `CML1(B)`"
  shows  "`RC( A \<turnstile> B \<diamond> C ) ; RC( D \<turnstile> E \<diamond> F)` =  `RC( (A \<and> \<not>(C ;\<^bsub>REA\<^esub> (\<not>D) )) \<turnstile> (B \<or> (C ;\<^bsub>REA\<^esub> E)) \<diamond> ( C ;\<^bsub>REA\<^esub> F) )`" (is "?lhs = ?rhs")
proof - have "?lhs = 
    `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     (ok \<and> $wait \<and> II\<^bsub>{okay\<down>, okay\<down>\<acute>, wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>) \<or>
     (ok \<and> \<not> $wait \<and> CML1(\<not> A)) \<or> 
     (ok \<and> \<not> $wait \<and> CML1(B)) ; (ok \<and> $wait \<and> RC(D \<turnstile>E\<diamond> F)) \<or> 
     (ok \<and> \<not> $wait \<and> CML1(C)) ; (ok \<and> \<not> $wait \<and>  RC(D \<turnstile>E\<diamond> F))`"
  apply(subst DesignREA_form_2)
  apply(simp add: SemiR_OrP_distr)
  apply(subst CML1_CML2_SemiR_left_zero)
  apply(simp add:RC_def is_healthy_def CML1_idempotent)
  apply(simp add:RC_def is_healthy_def CML2_idempotent CML1_CML2_commute)
  apply(subst RC_DesignREA_rel_closure)
  apply(simp_all add:assms)
  apply(subst CML3_SemiR_left_zero)
  apply(simp add:RC_def is_healthy_def CML3_idempotent CML1_CML3_commute CML2_CML3_commute)
  apply(subst RC_DesignREA_rel_closure)
  apply(simp_all add:assms)
  apply(subst Precondition_SemiR)
  apply(simp_all add:assms closure typing defined unrest)
  apply(simp add:RC_def is_healthy_def CML1_CML2_commute CML1_CML3_commute CML1_idempotent CML2_CML3_commute CML2_idempotent CML3_idempotent)
  apply(subst AndP_assoc) back
  apply(subst SemiR_AndP_left_precond)
  apply(simp_all add:assms typing defined closure)
  apply (smt R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
  apply(simp add:AndP_assoc[THEN sym])
  apply(subst AndP_assoc)back back back back back back back back back back back
  apply(subst SemiR_AndP_right_precond)
  apply(simp_all add:typing closure defined assms CML1_AndP urename)
  apply(subst AndP_assoc)back back back back
  apply(subst AndP_comm) back back back back back back back back
  apply(simp add:AndP_assoc[THEN sym])
  apply(subst AndP_assoc)back back back back back back back back back back back back back back
  apply(subst SemiR_AndP_right_precond)
  apply(simp_all add:typing closure defined assms CML1_AndP urename)
  apply(subst AndP_assoc)back back back back back back back 
  apply(subst AndP_comm) back back back back back back back back back back back back
  apply(simp add:AndP_assoc[THEN sym])
done
  also have "... = 
    `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     (ok \<and> $wait \<and> II\<^bsub>REA \<union> OKAY\<^esub>) \<or>
     (ok \<and> \<not> $wait \<and> CML1(\<not> A)) \<or>
     (ok \<and> \<not> $wait \<and> CML1(B) \<and> ok' \<and> $wait\<acute>) \<or> 
     (ok \<and> \<not> $wait \<and> CML1(C) ; CML1(\<not> D)) \<or> 
     (ok \<and> \<not> $wait \<and> CML1(C) ; CML1(E) \<and> ok' \<and> $wait\<acute>) \<or> 
     (ok \<and> \<not> $wait \<and> CML1(C) ; CML1(F) \<and> ok' \<and> \<not> $wait\<acute>)`"
  proof - 
    have 1: "`ok \<and> $wait \<and> RC(D \<turnstile> E \<diamond> F)` = `(ok \<and> $wait) \<and> II\<^bsub>REA \<union> OKAY\<^esub>`" sorry
    have 2: "`ok \<and> \<not>$wait \<and> RC(D \<turnstile> E \<diamond> F)` = `((ok \<and> \<not>$wait) \<and> CML1(\<not>D)) \<or> ((ok \<and> \<not>$wait) \<and> CML1(E) \<and> ok' \<and> $wait\<acute>) \<or> ((ok \<and> \<not>$wait) \<and> CML1(F) \<and> ok' \<and> \<not>$wait\<acute>)`" sorry
    show ?thesis 
      apply(simp add:1 2)
      apply(simp add:SemiR_OrP_distl CML1_AndP)
      apply(subst SemiR_AndP_right_precond)
      apply(simp_all add:typing closure defined assms)
      apply(subst SkipRA_right_unit)
      apply(simp_all add:typing closure defined assms unrest)
      apply(rule unrest)
      apply(rule unrest) defer 
      apply(rule unrest) defer defer
      apply(simp_all add:closure typing defined assms unrest urename)
      apply(simp add:AndP_assoc[THEN sym])
      apply(subst AndP_assoc) back back back back back back
      apply(subst SemiR_remove_middle_unrest1[of  _ _ "{okay \<down>,wait \<down>}"])
      apply(simp_all add:typing closure defined unrest assms)
      defer 
      apply(subst AndP_assoc) back back back back back
      apply(subst SemiR_AndP_left_precond)
      apply(simp_all add:typing defined closure assms AndP_assoc[THEN sym])
      apply(subst AndP_assoc) back back back back back back
      apply(subst SemiR_AndP_left_precond)
      apply(simp_all add:typing defined closure assms AndP_assoc[THEN sym])
      apply(subst AndP_assoc) back back back back back back back
      apply(subst SemiR_remove_middle_unrest1[of  _ _ "{okay \<down>,wait \<down>}"])
      apply(simp_all add:typing closure defined unrest assms)
      defer 
      apply(subst SemiR_AndP_right_postcond)
      apply(simp_all add:assms typing defined closure)
      apply(subst AndP_assoc) back back back back back back back back back
      apply(subst SemiR_AndP_left_precond)
      apply(simp_all add:typing defined closure assms)
      apply(subst AndP_assoc) back back back back back back back back back
      apply(subst SemiR_remove_middle_unrest1[of _ _ "{okay \<down>,wait \<down>}"])
      apply(simp_all add:typing defined closure assms unrest) defer 
      apply(subst SemiR_AndP_right_postcond)
      apply(simp_all add:typing defined closure assms)
      apply(simp add:AndP_assoc[THEN sym])
      sorry
      qed
      also have "... = 
    `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or>
     (ok \<and> $wait \<and> II\<^bsub>REA \<union> OKAY\<^esub>) \<or>
     (ok \<and> \<not> $wait \<and> (CML1(\<not> A) \<or> CML1(C) ; CML1(\<not> D))) \<or>
     (ok \<and> \<not> $wait  \<and> ok' \<and> $wait\<acute>\<and> (CML1(B) \<or> CML1(C) ; CML1(E))) \<or>
     (ok \<and> \<not> $wait \<and>  ok' \<and> \<not> $wait\<acute> \<and> CML1(C) ; CML1(F))`"
     by(utp_poly_auto_tac)
     also have "... = `RC( (A \<and> \<not>(\<exists> tt1\<acute>\<acute>\<acute>. \<exists> tt2\<acute>\<acute>\<acute>. C[$tt1\<acute>\<acute>\<acute>/tt\<acute>\<acute>\<acute>] ; (\<not> D)[$tt2\<acute>\<acute>\<acute>/tt\<acute>\<acute>\<acute>] \<and> ($tt\<acute>\<acute>\<acute> = $tt1\<acute>\<acute>\<acute> ^ $tt2\<acute>\<acute>\<acute>))) \<turnstile> (B \<or> (\<exists> tt1\<acute>\<acute>\<acute>. \<exists> tt2\<acute>\<acute>\<acute>. C[$tt1\<acute>\<acute>\<acute>/tt\<acute>\<acute>\<acute>] ; E[$tt2\<acute>\<acute>\<acute>/tt\<acute>\<acute>\<acute>] \<and> ($tt\<acute>\<acute>\<acute> =$tt1\<acute>\<acute>\<acute> ^ $tt2\<acute>\<acute>\<acute>))) \<diamond> (\<exists> tt1\<acute>\<acute>\<acute>. \<exists> tt2\<acute>\<acute>\<acute>. C[$tt1\<acute>\<acute>\<acute>/tt\<acute>\<acute>\<acute>] ; F[$tt2\<acute>\<acute>\<acute>/tt\<acute>\<acute>\<acute>] \<and> ($tt\<acute>\<acute>\<acute> =$tt1\<acute>\<acute>\<acute> ^ $tt2\<acute>\<acute>\<acute>)))`"
     apply(subst CML1_SemiR)
     apply(subst CML1_OrP[THEN sym])
     apply(subst CML1_SemiR)
     apply(subst CML1_OrP[THEN sym])
     apply(subst CML1_SemiR)
     apply(subst DesignREA_form_2)
     apply(simp add:demorgan2)
     done
     also have "... = `RC( (A \<and> \<not>(C ;\<^bsub>REA\<^esub> (\<not>D) )) \<turnstile> (B \<or> (C ;\<^bsub>REA\<^esub> E)) \<diamond> ( C ;\<^bsub>REA\<^esub> F) )`"
     by(simp add:SemiR_REA_def)
     finally show ?thesis ..
qed

definition StopCML :: "'a WF_PREDICATE" ("STOP\<^bsub>CML\<^esub>") where
"StopCML = `RC( true \<turnstile> $tt\<acute>\<acute>\<acute> = \<langle>\<rangle> \<diamond> false )`"

definition ChaosCML :: "'a WF_PREDICATE" ("CHAOS\<^bsub>CML\<^esub>") where 
"ChaosCML = `RC( false \<turnstile> false \<diamond> false)`"

definition MiracleCML :: "'a WF_PREDICATE" ("MIRACLE\<^bsub>CML\<^esub>") where 
"MiracleCML = `RC( true \<turnstile> false \<diamond> false)`"

definition PrefixSkipCML :: "('m EVENT, 'm) WF_PEXPRESSION \<Rightarrow> 'm WF_PREDICATE" ("@\<^bsub>CML\<^esub>_") where
"PrefixSkipCML a = `RC( true \<turnstile> ($tt\<acute>\<acute>\<acute> = \<langle>\<rangle> \<and> a \<notin> $ref\<acute>) \<diamond> ($tt\<acute>\<acute>\<acute> = \<langle>a\<rangle> \<and> II\<^bsub>REL_VAR - REA\<^esub>))`"

syntax
  "_upred_StopCML" :: "upred" ("STOP\<^bsub>CML\<^esub>")
  "_upred_ChaosCML" :: "upred" ("CHAOS\<^bsub>CML\<^esub>")
  "_upred_MiracleCML" :: "upred" ("MIRACLE\<^bsub>CML\<^esub>")
  "_upred_PrefixSkipCML" :: "uexpr \<Rightarrow> upred" ("@\<^bsub>CML\<^esub>_")
  
translations
  "_upred_StopCML" == "CONST StopCML"
  "_upred_ChaosCML" == "CONST ChaosCML"
  "_upred_MiracleCML" == "CONST MiracleCML"
  "_upred_PrefixSkipCML a" == "CONST PrefixSkipCML a"

declare StopCML_def [eval, evalr, evalrr, evalrx, evalp]
declare ChaosCML_def [eval, evalr, evalrr, evalrx, evalp]
declare MiracleCML_def [eval, evalr, evalrr, evalrx, evalp]
declare PrefixSkipCML_def [eval, evalr, evalrr, evalrx, evalp]

lemma "`STOP\<^bsub>CML\<^esub> ; CHAOS\<^bsub>CML\<^esub>` = `STOP\<^bsub>CML\<^esub>`"
  proof -
    from UNREST_as_ExistsP[of "{tt1 \<down>\<acute>\<acute>\<acute>,tt2 \<down>\<acute>\<acute>\<acute>}" "false"]
  have 1: "(\<exists>\<^sub>p {tt1\<down>\<acute>\<acute>\<acute>,tt2\<down>\<acute>\<acute>\<acute>} . false) = false" 
  apply(subst UNREST_as_ExistsP[of "{tt1 \<down>\<acute>\<acute>\<acute>,tt2 \<down>\<acute>\<acute>\<acute>}" "false",THEN sym])
  apply(simp add:unrest typing defined closure)
  done
  show ?thesis
  apply(simp add:StopCML_def ChaosCML_def)
  apply(subst DesignREA_SemiR)
  apply(simp_all add:closure typing defined CML1_def usubst unrest R1_def)
  apply (metis R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
  apply(subst RC_DesignREA_rel_closure)
  apply(simp_all add:closure typing defined CML1_def usubst RC_DesignREA_rel_closure unrest R1_def tr_prefix_as_nil)
  apply (metis R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
  apply (metis R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
  defer 
  apply(simp add:SemiR_REA_def usubst typing defined closure)
  apply(simp add: ExistsP_union[THEN sym])
  apply (metis (hide_lams, no_types) "1" OrP_comm insert_commute utp_pred_simps(1) utp_pred_simps(10))
done

lemma "SKIP2 is CML"
apply(simp add:Skip2CML_def)
apply(subst DesignREA_closure)
apply(simp_all add:unrest closure typing defined)
apply(rule unrest)
apply(simp add:unrest closure typing defined)
apply(subst UNREST_subset[of "VAR - (REL_VAR - REA - OKAY)" _ "REA"])
apply(subst UNREST_SkipRA[of "REL_VAR - REA - OKAY"])
apply(simp_all add:closure typing defined CML1_def usubst)
apply(subst RC_DesignREA_rel_closure)
apply(simp_all add:closure typing defined CML1_def usubst)
apply(simp add:R1_extend_AndP[THEN sym])
apply(simp add:R1_def tr_prefix_as_nil)
apply(rule closure) back
apply(simp add:tr_eq_rel_closure)
apply (metis (hide_lams, no_types) UNREST_SkipRA_NON_REL_VAR Un_commute WF_RELATION_UNREST)
apply(simp add:R1_extend_AndP[THEN sym])
apply(simp add:R1_def tr_prefix_as_nil)
apply(rule closure) back
apply(simp add:tr_eq_rel_closure)
apply (metis (hide_lams, no_types) UNREST_SkipRA_NON_REL_VAR Un_commute WF_RELATION_UNREST)
apply(simp add:R1_def)
done

lemma "STOP\<^bsub>CML\<^esub> is CML"
apply(simp add:StopCML_def)
apply(subst DesignREA_closure)
apply(simp_all add:unrest closure typing defined)
apply(subst RC_DesignREA_rel_closure)
apply(simp_all add:CML1_def typing defined closure usubst)
apply(simp_all add:R1_def tr_prefix_as_nil tr_eq_rel_closure)
done

lemma "CHAOS\<^bsub>CML\<^esub> is CML"
apply(simp add:ChaosCML_def)
apply(subst DesignREA_closure)
apply(simp_all add:unrest closure typing defined)
apply(subst RC_DesignREA_rel_closure)
apply(simp_all add:CML1_def typing defined closure usubst)
apply(simp_all add:R1_def tr_leq_trans)
done

lemma "MIRACLE\<^bsub>CML\<^esub> is CML"
apply(simp add:MiracleCML_def)
apply(subst DesignREA_closure)
apply(simp_all add:unrest closure typing defined)
apply(subst RC_DesignREA_rel_closure)
apply(simp_all add:CML1_def typing defined closure usubst)
apply(simp add:R1_def)
done

definition PrefixCML :: 
  "('a EVENT, 'a) WF_PEXPRESSION \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" ("_\<rightarrow>\<^bsub>CML\<^esub>_") where
"a\<rightarrow>\<^bsub>CML\<^esub>P = `@\<^bsub>CML\<^esub>a ; P`"

(*
definition InputCSP :: "'b::type CHAN \<Rightarrow> ('b \<Rightarrow> 'a WF_PREDICATE) \<Rightarrow> 'a WF_PREDICATE" where
"InputCSP n P = ExistsShP (\<lambda> v. PrefixCSP (LitPE (PEV n v)) (P v))"

definition OutputCSP :: 
  "'b::type CHAN \<Rightarrow> ('b, 'a) WF_PEXPRESSION \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"OutputCSP n v P = PrefixCSP (EventPE n v) P"

*)

definition ExternalChoiceCSP :: 
  "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" (infixl "\<box>" 65) where
"P \<box> Q = `CSP2((P \<and> Q)\<lhd> STOP \<rhd>(P \<or> Q))`"

definition MergeCSP :: 
  "('a EVENT USET, 'a) WF_PEXPRESSION \<Rightarrow> 
   ('a VAR set * 'a WF_PREDICATE)" where
  "MergeCSP A = ( {okay\<down>\<acute>, wait\<down>\<acute>, ref\<down>\<acute>, tr\<down>\<acute>}
              , `(($okay\<acute> = $okay\<^bsub>0\<^esub>\<acute> \<and> $okay\<^bsub>1\<^esub>\<acute>) \<and> 
                 ($wait\<acute> = $wait\<^bsub>0\<^esub>\<acute> \<or> $wait\<^bsub>1\<^esub>\<acute>) \<and> 
                 ($ref\<acute> = $ref\<^bsub>0\<^esub>\<acute> \<union> $ref\<^bsub>1\<^esub>\<acute>) \<and> 
                 (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>A \<^esub>($tr\<^bsub>1 \<^esub>- $tr))) ; SKIP`)"

definition HideCSP ::
  "'m WF_PREDICATE \<Rightarrow>
   ('m EVENT USET, 'm) WF_PEXPRESSION \<Rightarrow>
   'm WF_PREDICATE" where
"HideCSP P A = `RH(\<exists> tr\<acute>\<acute>. P[$tr\<acute>\<acute>/tr\<acute>][($ref\<acute> \<union> A)/ref\<acute>] 
                   \<and> $tr\<acute> = $tr ^ (($tr\<acute>\<acute> - $tr)\<upharpoonright>A)) ; SKIP`"

definition GuardCSP ::
  "'a WF_PREDICATE \<Rightarrow>
   'a WF_PREDICATE \<Rightarrow>
   'a WF_PREDICATE" where
"GuardCSP g P = P \<lhd> g \<rhd> STOP"

definition ParallelCSP :: 
  "'a WF_PREDICATE \<Rightarrow> 
   ('a EVENT USET, 'a) WF_PEXPRESSION \<Rightarrow> 
   'a WF_PREDICATE \<Rightarrow> 
   'a WF_PREDICATE" (infix "\<parallel>\<^bsub>CSP'(_')\<^esub>" 100) where
"P \<parallel>\<^bsub>CSP(A)\<^esub> Q = P \<parallel>\<^bsub>MergeCSP A\<^esub> Q"

definition InterleaveCSP 
  :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" (infix "|||\<^bsub>CSP\<^esub>" 100) where
"P |||\<^bsub>CSP\<^esub> Q = ParallelCSP P |{}| Q"

syntax
  "_upred_ChaosCSP" :: "upred" ("CHAOS")
  "_upred_prefixed"  :: "pexpr \<Rightarrow> upred \<Rightarrow> upred" ("_ -> _")
  "_upred_input"     :: "'a CHAN \<Rightarrow> pttrn \<Rightarrow> upred \<Rightarrow> upred" ("_?_ -> _")
  "_upred_output"    :: "'a CHAN \<Rightarrow> pexpr \<Rightarrow> upred \<Rightarrow> upred" ("_!_ -> _")
  "_upred_extchoice" :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixl "[]" 65)
  "_upred_guardcsp"  :: "upred \<Rightarrow> upred \<Rightarrow> upred" ("[_] & _" [0, 100] 100)
  "_upred_parallel"  :: "upred \<Rightarrow> pexpr \<Rightarrow> upred \<Rightarrow> upred" (infixr "||\<^bsub>_\<^esub>" 100)

syntax (xsymbols)
  "_upred_prefixed"  :: "pexpr \<Rightarrow> upred \<Rightarrow> upred" ("_ \<rightarrow> _")
  "_upred_input"     :: "'a CHAN \<Rightarrow> pttrn \<Rightarrow> upred \<Rightarrow> upred" ("_?_ \<rightarrow> _")
  "_upred_output"    :: "'a CHAN \<Rightarrow> pexpr \<Rightarrow> upred \<Rightarrow> upred" ("_!_ \<rightarrow> _")
  "_upred_extchoice" :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixl "\<box>" 65)
  "_upred_parallel"  :: "upred \<Rightarrow> pexpr \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<parallel>\<^bsub>_\<^esub>" 100)
  "_upred_interleave" :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infix "|||" 100)

translations
  "_upred_ChaosCSP" == "CONST ChaosCSP"
  "_upred_prefixed a P"   == "CONST PrefixCSP a P"
  "_upred_input n v p"    == "CONST InputCSP n (\<lambda> v. p)"
  "_upred_output n v p"   == "CONST OutputCSP n v p"
  "_upred_extchoice P Q"  == "CONST ExternalChoiceCSP P Q"
  "_upred_guardcsp b P"   == "CONST GuardCSP b P"
  "_upred_parallel P A Q" == "CONST ParallelCSP P A Q"
  "_upred_interleave P Q" == "CONST InterleaveCSP P Q"

definition CSP_Pre
  :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE " where
"CSP_Pre P = `\<not>P\<^sup>f[true/okay]\<^sub>f`"

definition CSP_Post
  :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE " where
"CSP_Post P = `P\<^sup>t[true/okay]\<^sub>f`"

declare CSP1_def [eval, evalr, evalrr, evalrx]
declare CSP_def [eval, evalr, evalrr, evalrx]
declare StopCSP_def [eval, evalr, evalrr, evalrx]
declare PrefixSkipCSP_def [eval, evalr, evalrr, evalrx]
declare SkipCSP_def [eval, evalr, evalrr, evalrx]
declare ChaosCSP_def [eval, evalr, evalrr, evalrx]
declare PrefixCSP_def [eval, evalr, evalrr, evalrx]
declare ExternalChoiceCSP_def [eval, evalr, evalrr, evalrx]
declare MergeCSP_def [eval, evalr, evalrr, evalrx]
declare ParallelCSP_def [eval, evalr, evalrr, evalrx]
declare InterleaveCSP_def [eval, evalr, evalrr, evalrx]

lemma CSP1_rel_closure[closure]:
  "P \<in> WF_RELATION \<Longrightarrow> CSP1(P) \<in> WF_RELATION"
by (metis CSP1_def DesignD_extreme_point_nok(2) OrP_rel_closure R1_def R1_rel_closure TopD_rel_closure)

lemma CSP2_rel_closure[closure]: 
  "P \<in> WF_RELATION \<Longrightarrow> CSP2(P) \<in> WF_RELATION"
by (metis H2_def J_closure SemiR_closure)

subsection {* CSP1 laws *}

lemma CSP1_idempotent: "`CSP1(CSP1(P))` = `CSP1(P)`" 
  by (utp_pred_auto_tac)

lemma CSP1_monotonic: 
  "P \<sqsubseteq> Q \<Longrightarrow> CSP1(P) \<sqsubseteq> CSP1(Q)"
  by (utp_pred_tac)

lemma CSP1_R1_commute: "CSP1 (R1 P) = R1 (CSP1 (P))"by utp_pred_auto_tac
lemma CSP1_R2_commute: "CSP1 (R2 P) = R2 (CSP1 (P))"by(simp add:CSP1_def R2_def R2s_def usubst typing defined closure, utp_pred_auto_tac)
lemma CSP1_R3_commute: "CSP1 (R3 P) = R3 (CSP1 (P))"by utp_pred_auto_tac

lemma CSP1_AndP: 
  "`CSP1(P \<and> Q)` = `CSP1(P) \<and> CSP1(Q)`"
  by utp_pred_auto_tac

lemma CSP1_OrP: 
  "`CSP1(P \<or> Q)` = `CSP1(P) \<or> CSP1(Q)`"
  by utp_pred_auto_tac

lemma CSP1_CondR: 
  "`CSP1(P \<lhd> b \<rhd> Q)` = `CSP1(P) \<lhd> b \<rhd> CSP1(Q)`"
  by utp_pred_auto_tac

lemma CSP1_Extend_OrP: 
  "`CSP1(P) \<or> Q` = `CSP1(P \<or> Q)`"
  by utp_pred_auto_tac

lemma CSP1_R1_compose: 
  assumes "P is R1"
  shows "CSP1(P) = `CSP1(ok \<and> P)`"
proof -
  have "CSP1(P) = CSP1 (R1 P)" 
    by (metis Healthy_simp assms)
  thus ?thesis 
    by(utp_pred_auto_tac)
qed

lemma ok_AndP:
  "`ok \<and> P` = `ok \<and> P[true/okay]`"
apply(subst PVarPE_PSubstPE)
apply(simp_all add:typing closure)
done

lemma CSP1_R1_form: 
  assumes "P is R1"
  shows "CSP1(P) = `CSP1(ok \<and> P[true/okay])`"
by (metis CSP1_R1_compose assms ok_AndP)

lemma CSP1_R1_form_2: 
  assumes "P is R1"
  shows "CSP1(P) = `CSP1(ok \<and> P)`"
by (metis CSP1_R1_compose assms)

lemma CSP1_R1_R3_compose: 
  assumes "P is R1"
  shows "R3(CSP1(P)) = `(\<not>ok \<and> ($tr\<le>$tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not>$wait \<and> P[true/okay][false/wait])`"
  apply(subst CSP1_R1_form)
  apply(metis assms)
  apply(simp add:R3_form_2 CSP1_def)
  apply(utp_pred_auto_tac)
done


lemma CSP1_R1_R3_compose_2: 
  assumes "P is R1"
  shows "R3(CSP1(P)) = `(\<not>ok \<and> ($tr\<le>$tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not>$wait \<and> P)`"
  apply(subst CSP1_R1_form_2)
  apply(metis assms)
  apply(simp add:R3_form CSP1_def)
  apply(utp_pred_auto_tac)
done

lemma CSP1_R3_okay': 
"`CSP1(ok' \<and> R3(P))` = `CSP1(R3(ok' \<and> P))`"
by(utp_pred_auto_tac)

subsection {* CSP2 laws *}

lemma CSP2_idempotent: "`CSP2(CSP2(P))` = `CSP2(P)`"
  by (metis H2_idempotent)

lemma CSP2_monotonic:
  "P \<sqsubseteq> Q \<Longrightarrow> CSP2(P) \<sqsubseteq> CSP2(Q)"
  by (metis H2_monotone)

lemma CSP1_CSP2_commute:
  assumes "P \<in> WF_RELATION"
  shows "CSP1 (CSP2 P) = CSP2 (CSP1 P)" 
  apply (simp add: CSP1_def usubst typing defined closure H2_def SemiR_OrP_distr)
  apply (metis (hide_lams, no_types) DesignD_extreme_point_nok(2) H1_H2_commute H1_def H2_def R1_H2_commute R1_def SemiR_FalseP_left TopD_rel_closure utp_pred_simps(15))
done
  
lemma CSP2_form:  
  assumes "P \<in> WF_RELATION"
  shows "`CSP2(P)` = `P\<^sup>f \<or> ok'\<and> P\<^sup>t`"
    apply(simp add:H2_def)
    apply(subst J_split)
    apply (metis assms)
    apply(simp add:AndP_comm)
    done

lemma CSP2_R1_commute: 
  assumes "P \<in> WF_RELATION"
  shows "CSP2 (R1 P) = R1 (CSP2 (P))"
by (metis R1_H2_commute assms)
(*
lemma CSP2_R2_commute:
  assumes "P \<in> WF_RELATION"
  shows"CSP2 (R2 P) = R2 (CSP2 (P))"
by (metis H2_R2_commute assms) *)

lemma CSP2_R3_commute: 
  assumes "P \<in> WF_RELATION"
  shows "CSP2 (R3 P) = R3 (CSP2 (P))" 
proof -
have "CSP2 (R3 P) = `($wait \<and> H2(II\<^bsub>rea\<^esub>)) \<or> (\<not> $wait \<and> CSP2(P))`"
  apply(subst CSP2_form)
  apply (metis R3_rel_closure assms)
  apply(simp add:H2_SkipREA)
  apply(simp add:R3_def CondR_def SkipREA_def usubst typing defined closure)
  apply (subst CSP2_form)
  apply (metis assms)
  apply(utp_pred_auto_tac)
done
thus ?thesis by (simp add:H2_SkipREA CondR_def R3_def)
qed

lemma J_ok: 
  "`ok \<and> J` = `ok \<and> II`"
proof -
  have "`ok \<and> J` = `ok \<and> ok' \<and> II\<^bsub>REL_VAR - OKAY\<^esub>`" 
    by(simp add:J_pred_def, utp_pred_auto_tac)
  also have "... = `(ok \<and> ($okay\<acute>=$okay)) \<and> II\<^bsub>REL_VAR - OKAY\<^esub>`" 
    by(subst Aidb, utp_pred_auto_tac)
  also have "... = `ok \<and> ($okay\<acute>=$okay) \<and> II\<^bsub>REL_VAR - OKAY\<^esub>`" 
    by( utp_pred_auto_tac)
  finally show ?thesis 
    apply(simp add:SkipR_as_SkipRA)
    apply(subst SkipRA_unfold[of "okay \<down>"])
    apply(utp_pred_auto_tac)
    apply(utp_pred_auto_tac)
    apply(utp_pred_auto_tac)
    apply(utp_pred_auto_tac)
    apply(simp add:closure typing defined erasure)
    done
qed

lemma CSP2_okay': 
  assumes "P \<in> WF_RELATION"
  shows "`P \<and> ok'` is CSP2"
proof -
  have 1:"DASHED - out REL_VAR = {}" 
    by (metis Diff_cancel out_vars_def set_extra_simps(4))
  have "`(P \<and> ok');J` = `P ; (ok \<and> J)`"
    apply(subst SemiR_AndP_right_precond)
    apply(metis assms)
    apply (metis J_closure)
    apply(utp_pred_auto_tac)
    apply(simp add:urename closure typing defined)
    done
  also have "... = `P ; (ok \<and> II)`" 
    by(metis J_ok)
  also have "... = `(P \<and> ok') ; II`"
    apply(subst SemiR_AndP_right_precond)
    apply(metis assms)
    apply (metis SkipR_closure)
    apply(utp_pred_auto_tac)
    apply(simp add:urename closure typing defined)
    done
  also have "... = `P \<and> ok'`"
    apply(simp add:SkipR_as_SkipRA)
    apply(subst SkipRA_right_unit)
    apply(simp_all)
    apply(subst AndP_rel_closure)
    apply(metis assms)
    apply(utp_pred_auto_tac)
    apply(simp_all add:typing unrest closure defined)
    apply(subst 1)
    apply (metis UNREST_empty)
    done
  finally show ?thesis 
    by(simp add:is_healthy_def H2_def)
qed

subsection {* CSP laws *}
  
lemma CSP_form: 
assumes "P is CSP" "P \<in> WF_RELATION"
shows "P = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P))) \<or> (ok \<and> \<not>$wait \<and>  ok' \<and> R2(CSP_Post(P)))`"
proof-
  have "P = CSP P" 
    by(metis assms(1) is_healthy_def)
  also have "... = `R3(CSP1(R1(CSP2(R2(P)))))`"
  sorry (*
    by (metis CSP1_CSP2_commute CSP1_R2_commute CSP1_R3_commute CSP1_idempotent CSP_def H2_R2_commute H2_R3_commute R1_R3_commute R1_idempotent R2_R3_commute R2_def R2_rel_closure RH_def assms(2) calculation comp_apply)
  *) also have "...  = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not>$wait \<and> ($tr \<le> $tr\<acute>) \<and> R2s(P)\<^sup>f[true/okay]\<^sub>f) \<or> (ok \<and> \<not>$wait \<and> ($tr \<le> $tr\<acute>) \<and> ok' \<and> R2s(P)\<^sup>t[true/okay]\<^sub>f)`" 
    apply(subst CSP1_R1_R3_compose)
    apply (metis Healthy_intro R1_idempotent)
    apply(subst CSP2_form)
    apply(metis assms(2) R2_rel_closure)
    apply(simp add:R1_def usubst typing defined closure)
    apply(utp_pred_auto_tac)
    done
  also have "... =  `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not>$wait \<and>  R2(P)\<^sup>f[true/okay]\<^sub>f) \<or> (ok \<and> \<not>$wait \<and> ok' \<and> R2(P)\<^sup>t[true/okay]\<^sub>f)`" 
    apply(simp add:R2_def R1_def usubst typing defined closure)
    apply(utp_pred_auto_tac)
    done
  finally show ?thesis 
  apply(simp add:CSP_Pre_def CSP_Post_def R2_wait_false[THEN sym] R2_okay_true[THEN sym])
  by (smt PVAR_VAR_pvdash R2_okay'_false R2_okay'_true)
qed

lemma CSP_is_RH: 
assumes "P is CSP" "P \<in> WF_RELATION"
shows "P is RH"
proof -
  have "RH (P) = RH (CSP (P))" 
    by (metis Healthy_simp assms(1))
  also have "... = CSP P"
    apply(simp add:CSP_def RH_def)
    apply(subst CSP2_R1_commute)
    apply(metis assms(2) R2_rel_closure R3_rel_closure) 
    sorry show ?thesis sorry qed 
    (*
    apply(subst CSP2_R2_commute)
    apply(metis assms(2) R3_rel_closure)
    apply(subst CSP2_R3_commute)
    apply(metis assms(2))
    apply(subst CSP2_R1_commute)
    apply(metis assms(2) R2_rel_closure R3_rel_closure)
    apply(subst CSP2_R2_commute)
    apply(metis assms(2) R3_rel_closure)
    apply(subst CSP2_R3_commute)
    apply(metis assms(2))
    apply(simp add: CSP1_R1_commute CSP1_R2_commute CSP1_R3_commute)
    apply(simp add:R2_R3_commute R1_R3_commute R3_idempotent R1_R2_commute R2_idempotent R1_idempotent)
    done
  finally show ?thesis
    by (metis Healthy_intro Healthy_simp assms(1))
qed*)

lemma CSP_Design: 
assumes "P is CSP" "P \<in> WF_RELATION"
shows "P = `RH ( CSP_Pre(P) \<turnstile> CSP_Post(P))`"
apply(subst CSP_form)
apply(metis assms(1))
apply(metis assms(2))
apply(simp add:RH_def R2_R3_commute R1_R3_commute)
apply(simp add:R2_def R1_idempotent DesignD_def R2s_def)
apply(simp add:usubst typing defined closure)
apply(simp add:R3_form R1_def)
apply(utp_pred_auto_tac)
done

subsection {* Stop laws *}

lemma Stop_form : "`STOP`= `CSP1(R3(ok' \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>))`" 
  by(utp_pred_auto_tac)

lemma Stop_expansion  :  "`STOP`= `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait \<and> ok \<and> II) \<or> (\<not> $wait \<and> ok \<and> ok' \<and> ($tr\<acute> = $tr) \<and> $wait\<acute>)`" 
  apply(simp add:Stop_form CSP1_R3_commute)
  apply(subst CSP1_R1_R3_compose)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
done

lemma Stop_is_R1 : "R1 STOP = STOP "
apply(simp add:Stop_form CSP1_R3_commute R1_R3_commute)
apply(utp_pred_auto_tac)
done

lemma Stop_is_R2 : "R2 STOP = STOP"
proof - 
have "R2 STOP = `CSP1(R3(R2(ok' \<and> ($tr \<acute>=$tr) \<and> $wait \<acute>)))`"
  by(simp add:Stop_form CSP1_R2_commute CSP1_R3_commute R2_R3_commute)
also have "... = `CSP1(R3(ok' \<and> R1(($tr \<acute>-$tr)=\<langle>\<rangle>) \<and> $wait \<acute>))`" 
  by(simp add:R2_def R2s_def usubst typing defined closure, utp_pred_auto_tac)
finally show ?thesis
  by(simp add:R1_def tr_prefix_as_nil Stop_form)
qed

lemma Stop_is_R3 : "R3 STOP = STOP" 
  by(simp add:Stop_form CSP1_R3_commute R3_idempotent)
  
lemma Stop_is_CSP1 : "CSP1 STOP = STOP" 
  by(simp add:Stop_form CSP1_idempotent)

lemma Stop_is_CSP2 :
"CSP2 STOP = STOP"
proof -
  have "CSP2 STOP = `CSP1(CSP2(ok' \<and> \<delta>))`"
    apply(subst CSP1_CSP2_commute)
    apply(subst AndP_rel_closure)
    apply(utp_pred_auto_tac)
    apply(simp add:\<delta>_rel_closure)
    apply(simp_all add:StopCSP_def)
    done
  moreover have "`CSP2(ok' \<and> \<delta>)` = `ok' \<and> \<delta>`"
    by (metis AndP_comm CSP2_okay' \<delta>_rel_closure is_healthy_def)
  ultimately show ?thesis
    by(metis StopCSP_def)
qed

lemma Stop_rel_closure[closure]: 
  "STOP \<in> WF_RELATION"
by(simp add:StopCSP_def closure)

lemma Stop_Design_form:
  "STOP = `RH( true \<turnstile> $wait\<acute> \<and> ($tr\<acute> = $tr))`"
  apply(subst CSP_Design)
  apply (metis CSP_def Healthy_intro RH_def Stop_is_CSP1 Stop_is_CSP2 Stop_is_R1 Stop_is_R2 Stop_is_R3 comp_apply)
  apply (metis Stop_rel_closure)
  apply (subst Stop_expansion)
  apply (subst Stop_expansion)
  apply(simp add:usubst typing defined closure)
  apply( simp add:DesignD_def CSP_Pre_def CSP_Post_def)
  apply(utp_pred_auto_tac)
done

lemma Stop_precondition: 
  "`\<not>STOP\<^sup>f\<^sub>f` = `\<not>CSP1(false)`"
  by(simp add:Stop_expansion usubst typing defined closure CSP1_def)

lemma Stop_postcondition: 
  "`STOP\<^sup>t\<^sub>f` = `CSP1($wait\<acute> \<and> ($tr\<acute> = $tr))`"
  apply(simp add:Stop_expansion usubst typing defined closure CSP1_def)
  apply(utp_pred_auto_tac)
  done

lemma Stop_precondition_2: 
  "`CSP_Pre(STOP)` = `true`"
  by(simp add:CSP_Pre_def Stop_expansion usubst typing defined closure CSP1_def)

lemma Stop_postcondition_2: 
  "`CSP_Post(STOP)` = `($tr\<acute> = $tr) \<and> $wait\<acute>`"
 by(simp add:CSP_Post_def Stop_expansion usubst typing defined closure)

subsection {* Skip laws *}

lemma Skip_form : "`SKIP`= `CSP1(R3(II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>))`" 
proof- 
have "`SKIP`= ` RH (CSP1( \<exists> ref. ok \<and> ($ref\<acute> = $ref) \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>))`"
  apply(simp add:SkipCSP_def SkipREA_CondR_SkipR CondR_def SkipR_as_SkipRA)
  apply(subst SkipRA_unfold[of "ref \<down>"])
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac) 
  apply(utp_pred_auto_tac)
  apply(simp add:ExistsP_OrP_dist)
  apply(subst ExistsP_ident) back
  apply(simp add:unrest closure typing defined)
  apply(simp add:CSP1_def closure typing defined erasure)
  done
also have "... = ` RH (CSP1( \<exists> ref. ($ref\<acute> = $ref) \<and> (ok \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>)))`"
  by(utp_pred_auto_tac)
also have "... = ` RH (CSP1( (\<exists> ref. ($ref\<acute> = $ref)) \<and> (ok \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>)))`"
  proof-
  have "`\<exists> ref. ($ref\<acute> = $ref) \<and> (ok \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>)` = `(\<exists> ref. ($ref\<acute> = $ref)) \<and> (ok \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>)`"
    apply(subst ExistsP_AndP_expand1[THEN sym])
    apply (rule unrest) back
    apply(simp_all add:unrest)
    apply (rule UNREST_subset)
    apply (rule UNREST_SkipRA)
    apply (auto)
  done
  thus ?thesis 
    by metis
  qed
also have "... = ` RH (CSP1(ok \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>))`"
  proof-
  have "`\<exists> ref. ($ref\<acute> = $ref)` = `true`"
    sorry
    thus ?thesis by (metis utp_pred_simps(6))
  qed
also have "... = ` RH (CSP1(II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>))`"
  apply(subst CSP1_R1_compose) back
  apply(simp_all)
  apply(subst SkipRA_unfold[of "tr \<down>"])
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(simp add:is_healthy_def R1_def)
  apply(utp_pred_auto_tac)
  done
also have "... = `CSP1(RH (II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>))`"
  by(simp add:RH_def CSP1_R1_commute CSP1_R2_commute CSP1_R3_commute)
also have "... =  `CSP1 (R3 (R1 (($tr\<acute> - $tr) = \<langle>\<rangle>) \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>}\<^esub>))`"
  apply(subst SkipRA_unfold[of "tr \<down>"])
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(simp add:RH_def R2_R3_commute R1_R3_commute)
  apply(simp add:R2_def R1_idempotent R2s_def)
  apply(simp add:usubst typing defined closure)
  apply(simp add:R1_def)
  apply(utp_pred_auto_tac)
  done
also have "... = `CSP1 (R3 (($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>}\<^esub>))`"
  by(simp add:R1_def tr_prefix_as_nil)
finally show ?thesis
  apply(subst SkipRA_unfold[of "tr \<down>"])
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(simp add:erasure closure typing defined)
  done
qed

lemma Skip_expansion: 
  "`SKIP`= `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not>$wait \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>)`"
apply(simp add:Skip_form CSP1_R3_commute)
apply(subst CSP1_R1_R3_compose_2)
apply(subst SkipRA_unfold[of "tr \<down>"])
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(simp add:is_healthy_def)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
done


lemma Skip_expansion_2:
  "SKIP = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> ok' \<and> \<not>$wait \<and> \<not>$wait\<acute> \<and> ($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - REA\<^esub>)`"
  apply(simp add:Skip_expansion)
  apply(subst SkipRA_unfold[of "tr \<down>"])
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(subst SkipRA_unfold[of "wait \<down>"])
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(subst SkipRA_unfold[of "okay \<down>"])
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  apply(utp_pred_auto_tac)
  sorry

lemma Skip_is_R1: 
  "SKIP is R1"
by(utp_pred_auto_tac)

lemma Skip_is_R2: 
  "SKIP is R2"
proof -
have "`R2(SKIP)` = `R1 (\<not>ok) \<or> 
  (ok \<and> $wait \<and> R1(($tr\<acute> - $tr) = \<langle>\<rangle>) \<and> II\<^bsub>REL_VAR - {tr\<down>, tr\<down>\<acute>}\<^esub>) \<or> 
  (ok \<and> \<not> $wait \<and> R1(($tr\<acute> - $tr) = \<langle>\<rangle>) \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>}\<^esub>)`"
apply(simp add:Skip_expansion R2_def R2s_def SkipR_as_SkipRA)
apply(subst SkipRA_unfold[of "tr \<down>"])
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(subst SkipRA_unfold[of "tr \<down>"]) back
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(simp add:usubst typing defined closure)
apply(utp_pred_auto_tac)
done
also have "... = `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> 
  (ok \<and> $wait \<and> ($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - {tr\<down>, tr\<down>\<acute>}\<^esub>) \<or> 
  (ok \<and> \<not> $wait \<and> ($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>}\<^esub>)`"
by(simp add:R1_def tr_prefix_as_nil)
also have "... =`(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> 
  (ok \<and> $wait \<and> II\<^bsub>REL_VAR\<^esub>) \<or> 
  (ok \<and> \<not> $wait \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>}\<^esub>)`"
apply(subst SkipRA_unfold[of "tr \<down>"])back back
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(subst SkipRA_unfold[of "tr \<down>"])back back back
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(simp add:erasure closure typing defined)
done
finally show ?thesis 
  by(simp add:is_healthy_def Skip_expansion SkipR_as_SkipRA)
qed

lemma Skip_is_R3: 
  "SKIP is R3"
by(simp add:Skip_form is_healthy_def CSP1_R3_commute R3_idempotent)

lemma Skip_is_CSP1: 
  "SKIP is CSP1"
by(simp add:Skip_form is_healthy_def CSP1_idempotent)

lemma Skip_rel_closure: 
  "SKIP \<in> WF_RELATION"
sorry

lemma Skip_is_CSP2: 
  "SKIP is CSP2"
proof -
have "CSP2 SKIP = `CSP1((ok \<and> $wait \<and> II\<^bsub>REL_VAR - OKAY\<^esub>) \<or> (ok \<and> \<not>$wait \<and> ($tr\<acute>=$tr) \<and> ok' \<and> \<not>$wait\<acute> \<and> II\<^bsub>REL_VAR - REA\<^esub>))`"
apply(simp add: CSP1_def H2_def)
apply(subst J_split)
apply(simp add:Skip_rel_closure)
apply(simp add:Skip_expansion_2 usubst typing defined closure)
apply(simp add:SkipR_as_SkipRA)
apply(subst SkipRA_unfold[of "okay \<down>"])
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(subst SkipRA_unfold[of "okay \<down>"]) back
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(utp_pred_auto_tac)
apply(simp add:usubst typing defined closure erasure unrest urename)

sorry
thus ?thesis sorry qed

lemma Skip_Design_form: 
  "SKIP = `RH( true \<turnstile> \<not>$wait\<acute> \<and> ($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - REA\<^esub>)`"
  apply(subst CSP_Design)
  apply (metis (full_types) CSP_def R1_idempotent R2_def RH_def Skip_is_CSP1 Skip_is_CSP2 Skip_is_R2 Skip_is_R3 comp_def is_healthy_def)
  apply (metis Skip_rel_closure)
  apply (subst Skip_expansion_2)
  apply (subst Skip_expansion_2)
  apply(simp add:usubst typing defined closure CSP_Pre_def CSP_Post_def)
  done

lemma Skip_precondition: 
  "CSP_Pre(SKIP) = true"
by(simp add:CSP_Pre_def Skip_expansion_2 usubst typing defined closure)

lemma Skip_postcondition: 
  "CSP_Post(SKIP) = `\<not>$wait\<acute> \<and> ($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - REA\<^esub>`"
by(simp add:CSP_Post_def Skip_expansion_2 usubst typing defined closure)

subsection {* Chaos laws *}

lemma Chaos_form : "`CHAOS`= `CSP1(R3(R1(true)))`"
  apply(simp add:ChaosCSP_def RH_def R2_R3_commute R1_R3_commute)
  apply(simp add:R2_def R2s_def R1_idempotent usubst typing closure defined)
  done

lemma Chaos_expansion : "`CHAOS`= `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($wait \<and> ok \<and> II) \<or> (\<not> $wait \<and> ($tr \<le> $tr\<acute>))`"
apply(simp add:Chaos_form CSP1_R3_commute)
apply(simp add:R1_def)
apply(subst CSP1_R1_R3_compose)
apply (metis R1_by_refinement order_refl)
apply(utp_pred_auto_tac)
done

lemma Chaos_is_R1: 
  "CHAOS is R1"
by(utp_pred_auto_tac)

lemma Chaos_is_R2: 
  "CHAOS is R2"
apply(simp add:is_healthy_def Chaos_form R1_def CSP1_R3_commute R2_R3_commute)
apply(simp add:R2_def CSP1_def R2s_def usubst typing defined closure)
apply(utp_pred_auto_tac)
done

lemma Chaos_is_R3: 
  "CHAOS is R3"
by(simp add:Chaos_form R1_def is_healthy_def CSP1_R3_commute R3_idempotent)

lemma Chaos_is_CSP1: 
  "CHAOS is CSP1"
by(simp add:Chaos_form is_healthy_def CSP1_idempotent)

lemma Chaos_is_CSP2: 
  "CHAOS is CSP2"
apply(simp add:Chaos_form is_healthy_def CSP1_CSP2_commute[THEN sym] closure CSP2_R3_commute CSP2_R1_commute)
by (metis H1_left_zero H3_absorbs_H2_1 H3_def SkipD_is_H1 SkipD_rel_closure)

lemma Chaos_rel_closure: 
  "CHAOS \<in> WF_RELATION"
by(simp add:ChaosCSP_def closure)

lemma Chaos_Design_form: 
  "CHAOS = `RH (false \<turnstile> true )`"
apply(subst CSP_Design)
apply (metis (full_types) CSP_def Chaos_is_CSP1 Chaos_is_CSP2 Chaos_is_R1 Chaos_is_R2 Chaos_is_R3 RH_def comp_def is_healthy_def)
apply(metis Chaos_rel_closure)
apply(simp add:Chaos_expansion)
apply(simp add:usubst typing defined closure CSP_Pre_def CSP_Post_def)
apply(simp add:DesignD_def)
apply(simp add:RH_def R2_R3_commute R1_R3_commute)
apply(simp add:R2_def R1_idempotent R2s_def)
apply(simp add:usubst typing defined closure)
done

lemma Chaos_precondition: 
  "CSP_Pre(CHAOS) = `\<not> R1(true)`"
by(simp add:CSP_Pre_def Chaos_expansion usubst typing defined closure R1_def)

lemma Chaos_postcondition: 
  "CSP_Post(CHAOS) = R1 true"
by(simp add:CSP_Post_def Chaos_expansion usubst typing defined closure R1_def) 

subsection {*Prefix laws *}

lemma Prefix_form :  
  assumes "TR \<sharp> a" 
  shows "`@a`= `CSP1(R3(ok' \<and> (((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>))))`"
apply(simp add:PrefixSkipCSP_def)
apply(subst doA_form)
apply(metis assms)
apply (metis (hide_lams, no_types) CSP1_R3_okay' PVAR_VAR_pvdash)
done

lemma Prefix_expansion: 
  assumes "TR \<sharp> a"
  shows "`@a`= `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> ok' \<and> $wait\<acute>\<and> \<not> $wait \<and> (a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> ok' \<and> \<not> $wait\<acute> \<and> \<not> $wait \<and> ($tr ^ \<langle>a\<rangle> = $tr\<acute>))`" 
proof -
have 1:"`($tr ^ \<langle>a\<rangle> = $tr\<acute>)` =`($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> ($tr \<le> $tr\<acute>)` "
by (metis tr_prefix_app)
show ?thesis
apply(subst Prefix_form)
apply(metis assms)
apply(simp add:CSP1_R3_commute)
apply(subst CSP1_R1_R3_compose_2)
apply(subst 1)
apply(utp_pred_auto_tac)
apply(simp add:R1_def CondR_def)
apply(utp_pred_auto_tac)
done
qed

lemma Prefix_is_R1: 
  "`@a` is R1"
by(utp_pred_auto_tac)

lemma Prefix_is_R2:
  assumes "TR \<sharp> a" 
  shows "`@a` is R2"
oops

lemma Prefix_is_R3: 
  "`@a` is R3"
proof -
  have 1: "`do\<A>(a)` = `R3 ( do\<A>(a) )`" by(simp add:doA_is_R3)
  have 2: "`@a` = `CSP1(R3(ok' \<and>do\<A>(a))) `"
    apply(simp add:PrefixSkipCSP_def is_healthy_def)
    apply(subst 1)
    apply (metis CSP1_R3_okay' PVAR_VAR_pvdash)
    done
  show ?thesis 
    apply(simp add:is_healthy_def)
    apply(subst 2)
    apply(subst 2)
    apply(simp add:CSP1_R3_commute R3_idempotent)
    done
qed

lemma Prefix_is_CSP1: 
  "`@a` is CSP1"
by(simp add:PrefixSkipCSP_def is_healthy_def CSP1_idempotent)

lemma Prefix_is_CSP2: 
  assumes "TR \<sharp> a" 
  shows "`@a` is CSP2"
sorry

lemma Prefix_rel_closure: 
  assumes "TR \<sharp> a" 
  shows "`@a` \<in> WF_RELATION"
sorry

lemma Prefix_is_CSP: "`@a` is CSP" 
sorry

lemma Prefix_Design_form:
  assumes "TR \<sharp> a" "{okay\<down>\<acute>,okay\<down>, wait\<down>} \<sharp> a"
  shows "`@a` = `RH ( true \<turnstile> (((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)))`"
proof -
  have 2: "`($tr ^ \<langle>a\<rangle> = $tr\<acute>)\<^sup>t[true/okay]\<^sub>f` = `($tr ^ \<langle>a\<rangle> = $tr\<acute>)`"
    using assms
    apply(simp add:usubst typing defined closure UNREST_subset unrest)
    sorry
  have 3: "`(a \<notin> $ref\<acute>)\<^sup>t[true/okay]\<^sub>f` = `(a \<notin> $ref\<acute>)`" 
    sorry
  have "`@a` =  `RH (true \<turnstile> ($wait\<acute> \<and> (a \<notin> $ref\<acute>)\<^sup>t[true/okay]\<^sub>f \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not> $wait\<acute> \<and> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)\<^sup>t[true/okay]\<^sub>f))`"
apply(subst CSP_Design)
apply(metis Prefix_is_CSP)
apply(metis Prefix_rel_closure assms)
apply(subst Prefix_expansion)
apply(metis assms)
apply(subst Prefix_expansion)
apply(metis assms)
apply(simp add:usubst typing defined closure)
sorry
also have "... = `RH (true \<turnstile> ($wait\<acute> \<and> (a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not> $wait\<acute> \<and> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)))`"
  by (metis "2" "3")
finally have 4: "`@a` =  `RH (true \<turnstile> (((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)))`"
  by(utp_pred_auto_tac)
show ?thesis
  by(subst 4,simp)
qed

lemma Prefix_precondition: 
assumes "TR \<sharp> a"
shows "CSP_Pre `@a` = true"
by(simp add:CSP_Pre_def Prefix_expansion assms usubst typing defined closure)

lemma Prefix_postcondition: 
assumes "TR \<sharp> a"
shows "CSP_Post `@a` = `((a \<notin> $ref\<acute>) \<and> ($tr \<le> $tr\<acute>)) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)`"
sorry

subsection {* Sequential composition *}

lemma Seq_comp_closure: 
assumes "P is CSP" "Q is CSP"
shows "(P ; Q) is CSP"
oops


lemma Seq_comp_form: 
assumes "P is CSP" "Q is CSP" "P \<in> WF_RELATION" "Q\<in> WF_RELATION"
shows "(P ; Q) = `RH (\<not>(\<not>CSP_Pre(P);R1(true)) \<and> \<not>(CSP_Post(P)[false/wait\<acute>];(\<not>CSP_Pre(Q))) \<turnstile> CSP_Post(P);(II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> CSP_Post(Q)))`"
 sorry (* proof -
have 1: "`(\<not>ok \<and> ($tr \<le> $tr\<acute>));Q` = `(\<not>ok \<and> ($tr \<le> $tr\<acute>))`"
proof-
have "Q = CSP1(R1(Q))"
  by (metis CSP1_idempotent CSP_def CSP_is_RH RH_is_R1 assms(2) assms(4) comp_apply is_healthy_def)
hence "`(\<not>ok \<and> ($tr \<le> $tr\<acute>));Q` = `(\<not>ok \<and> ($tr \<le> $tr\<acute>));CSP1(R1(Q))`"
  by metis
also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>));(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not>ok \<and> ($tr \<le> $tr\<acute>));(Q \<and> ($tr \<le> $tr\<acute>))`" 
  by (metis (hide_lams, no_types) CSP1_R1_commute CSP1_def OrP_comm R1_def SemiR_OrP_distl)
also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not>ok \<and> ($tr \<le> $tr\<acute>));(Q \<and> ($tr \<le> $tr\<acute>))`" 
  apply(subst SemiR_remove_middle_unrest1[of "`\<not>ok \<and> ($tr \<le> $tr\<acute>)`" "`($tr \<le> $tr\<acute>)`" "{okay \<down>}" "`\<not>ok`"])
  apply(simp_all add:closure typing defined unrest)
  apply (metis R1_def R1_rel_closure TopD_def TopD_rel_closure) 
  apply (smt R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
  apply(subst SemiR_AndP_left_precond)
  apply (smt R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6)) sorry
also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not>ok \<and> ($tr \<le> $tr\<acute>);(Q \<and> ($tr \<le> $tr\<acute>)))`"
  apply(subst SemiR_AndP_left_precond)
  apply(simp_all add:closure)
  defer
  apply(subst AndP_rel_closure)
  apply(simp_all add:assms)
  by (metis (full_types) R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not>ok \<and> R1(true);R1(Q))`"
  by(utp_pred_auto_tac)
also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not>ok \<and> R1(R1(true);R1(Q)))`"
  proof - 
    have "`R1(true);R1(Q)` is R1" 
      apply(subst R1_SemiR_closure)
      apply(simp_all add:closure assms is_healthy_def R1_idempotent)
      done
   thus ?thesis 
      by(metis is_healthy_def)
   qed
also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>))`"
  by(utp_pred_auto_tac)
finally show ?thesis 
  ..
qed
have 2: " `(ok \<and> $wait \<and> II);Q` = `ok \<and> $wait \<and> II`"
proof -
have "`(ok \<and> $wait \<and> II);Q` = `ok \<and> $wait \<and> R3(Q)`" 
  apply(subst SemiR_AndP_left_precond)
  apply(simp_all add:closure assms(4))
  apply(subst SemiR_AndP_left_precond)
  apply(simp_all add:closure assms(4))
  apply (metis CSP_is_RH Healthy_simp RH_is_R3 assms(2) assms(4))
  done
also have "... = `ok \<and> $wait \<and> II`"
  apply(simp add:R3_form)
  apply(utp_pred_auto_tac)
  done
finally show ?thesis 
  ..
qed
have 3: " `(ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P)));Q` = `ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P);R1(true))`"
proof -
have "`(ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P)));Q` = `(ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P)));CSP1(R1(Q))`" sorry
also have "... = `(ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P)));(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P)));(ok \<and> Q \<and> ($tr \<le> $tr \<acute>))`" sorry
show ?thesis sorry qed
have 4:  "`(ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (\<not>ok \<and> ($tr \<le> $tr\<acute>))`  = `false`"
proof -
have "`(ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (\<not>ok \<and> ($tr \<le> $tr\<acute>))`  = `(ok \<and> \<not> $wait \<and> R2 (CSP_Post(P)) \<and> ok') ; (\<not>ok \<and> ($tr \<le> $tr\<acute>))`"
  by (metis AndP_comm)
also have "... = `(ok \<and> \<not> $wait \<and> R2 (CSP_Post(P)) \<and> ok' \<and> \<not>ok') ; ($tr \<le> $tr\<acute>)`" 
  apply(subst SemiR_AndP_right_precond)
  apply(simp_all add:closure urename AndP_assoc)
  apply(subst AndP_rel_closure)
  apply(subst AndP_rel_closure)
  apply(simp_all add:closure)
  apply(subst R2_rel_closure)
  apply(simp_all add:CSP_Post_def)
  defer 
  apply (smt R1_def R1_rel_closure TrueP_rel_closure utp_pred_simps(6))
  apply(subst SubstP_rel_closure)
  apply(subst SubstP_rel_closure)
  apply(subst SubstP_rel_closure)
  apply(simp_all add:closure assms typing defined)
  apply (metis TruePE_erasure UNREST_EXPR_TrueE)
  apply (metis FalsePE_erasure UNREST_EXPR_FalseE)
  done
also have "... = false" 
  apply(subst AndP_contra)
  apply(utp_pred_auto_tac)
  done
finally show ?thesis 
  ..
qed
have 5: "`(ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (ok \<and> \<not> $wait \<and> R2 (\<not> CSP_Pre(Q)))` = `ok \<and> \<not>$wait \<and> R2(CSP_Post(P)[false/wait\<acute>];R2(\<not>CSP_Pre(Q)))`"
proof - 
have "`(ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (ok \<and> \<not> $wait \<and> R2 (\<not> CSP_Pre(Q)))` = `ok \<and> \<not> $wait \<and> R2(\<not>$wait\<acute> \<and> CSP_Post(P)) ; R2 (ok \<and> \<not> CSP_Pre(Q))`"
  sorry
also have "... = `ok \<and> \<not>$wait \<and> R2(CSP_Post(P)[false/wait\<acute>];R2(\<not>CSP_Pre(Q)))`" sorry (*
  apply(subst R2_sequential_composition)
  apply(simp_all add:CSP_Post_def CSP_Pre_def closure)
  apply(subst AndP_rel_closure)
  apply(simp_all add:closure)
  apply(subst SubstP_rel_closure)
  apply(subst SubstP_rel_closure)
  apply(subst SubstP_rel_closure)
  apply(simp_all add:closure assms typing defined)
  apply (metis TruePE_erasure UNREST_EXPR_TrueE)
  apply (metis FalsePE_erasure UNREST_EXPR_FalseE)
  apply(subst AndP_rel_closure)
  apply(simp_all add:closure)
  apply(subst SubstP_rel_closure)
  apply(subst SubstP_rel_closure)
  apply(subst SubstP_rel_closure)
  apply(simp_all add:closure assms typing defined)
  apply (metis FalsePE_erasure UNREST_EXPR_FalseE)
  apply (metis TruePE_erasure UNREST_EXPR_TrueE)
  apply(subst NotP_PVarPE_PSubstPE[of "wait \<acute>"])
sorry *)
have 6: "`(ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(Q)))` = `(ok \<and> \<not>$wait \<and> ok' \<and> R2(CSP_Post(P);(II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> CSP_Post(Q))))`"
sorry
have "P ; Q = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P);R1(true))) \<or> ((ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (\<not>ok \<and> ($tr \<le> $tr\<acute>))) \<or> ((ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (ok \<and> \<not> $wait \<and> R2 (\<not> CSP_Pre(Q)))) \<or> ((ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(P))) ; (ok \<and> \<not> $wait \<and> ok' \<and> R2 (CSP_Post(Q))))`"
apply(subst CSP_Design)
apply(metis assms(1))
apply(metis assms(3))
apply(subst RH_expansion)
apply(simp add:SemiR_OrP_distr)
apply(simp add:1 2 3)
apply(subst CSP_Design[of "Q"])
apply(metis assms(2))
apply(metis assms(4))
apply(subst RH_expansion)
apply(simp add:SemiR_OrP_distl)
apply(utp_pred_auto_tac)
done
also have "... = `(\<not>ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok \<and> $wait \<and> II) \<or> (ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P);R1(true))) \<or> (ok \<and> \<not>$wait \<and> R2(CSP_Post(P)[false/wait\<acute>];\<not>CSP_Pre(Q))) \<or> (ok \<and> \<not>$wait \<and> ok' \<and> R2(CSP_Post(P);(II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> CSP_Post(Q))))`"
apply(subst 4)
apply(subst 5)
apply(subst 6)
apply(utp_pred_auto_tac)
done 
also have "... = `RH (\<not>(\<not>CSP_Pre(P);R1(true)) \<and> \<not>(CSP_Post(P)[false/wait\<acute>];(\<not>CSP_Pre(Q))) \<turnstile> CSP_Post(P);(II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> CSP_Post(Q)))`"
apply(simp add:RH_expansion)
apply(utp_pred_auto_tac)
done
finally show ?thesis ..
qed*)

subsection {* Prefixed laws *}

lemma 
  assumes "TR \<sharp> a" "{okay\<down>\<acute>, okay\<down>, wait\<down>} \<sharp> a"
  shows "`a \<rightarrow> SKIP` = `@a`" 
apply(simp add:PrefixCSP_def)
apply(subst Prefix_Design_form) back
apply(metis assms(1))
apply(metis assms(2))
apply(subst Seq_comp_form)
apply(metis Prefix_is_CSP)
apply (metis (full_types) CSP_def Healthy_intro Healthy_simp R1_idempotent R2_R3_commute R2_def RH_def Skip_is_CSP1 Skip_is_CSP2 Skip_is_R2 Skip_is_R3 o_eq_dest_lhs)
apply(subst Prefix_rel_closure)
apply(simp_all add:assms Skip_rel_closure)
apply(subst Prefix_expansion)
apply(metis assms(1))
apply(subst Prefix_expansion)
apply(metis assms(1))
apply(subst Prefix_expansion)
apply(metis assms(1))
apply(simp add:Skip_expansion_2)
oops

subsection {*CSP laws*}
(*
lemma L1 : 
  assumes "P is CSP" "P \<in> WF_RELATION"
  shows "`CHAOS ; P` = `CHAOS`"
proof -
  have a: "`((\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($tr \<le> $tr\<acute>)) ; R1 (true)` = `($tr \<le> $tr\<acute>)`"
  proof -
    have 1: "`(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($tr \<le> $tr\<acute>)` = `($tr \<le> $tr\<acute>)`" 
      by(utp_pred_auto_tac)
    have "`((\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($tr \<le> $tr\<acute>)) ; R1 (true)` =`($tr \<le> $tr\<acute>);($tr \<le> $tr\<acute>)`"
      by(simp add: R1_def "1")
    thus ?thesis 
      by(simp add: tr_leq_trans)
  qed
show ?thesis
apply(subst Chaos_Design_form) back
apply(subst Seq_comp_form)
apply (metis CSP_def Chaos_is_CSP1 Chaos_is_CSP2 Chaos_is_R1 Chaos_is_R2 Chaos_is_R3 Healthy_comp R_intro is_healthy_def)
apply(metis assms(1))
apply (metis Chaos_rel_closure)
apply (metis assms(2))
apply(simp add:Chaos_expansion)
apply(simp add:usubst typing defined closure)
apply(simp add:DesignD_def)
apply(subst "a")
apply(simp add:RH_def R1_R2_commute R1_R3_commute)
apply(simp add:R1_def)
apply(utp_pred_auto_tac)
done
qed

thm DesignD_composition

lemma L2 : 
assumes "P is CSP" "P \<in> WF_RELATION"
shows "`STOP ; P` = `STOP`"



proof -
  have 1: "`STOP\<^sup>f[true/okay]\<^sub>f` = `false`" by (metis Stop_precondition_2 utp_pred_simps(2) utp_pred_simps(3))
  have 2: "`STOP\<^sup>t[true/okay]\<^sub>f` = `($tr = $tr\<acute>) \<and> $wait\<acute>`" by (metis EqualP_sym Stop_postcondition_2)
  have " `STOP ; P` = `RH (true \<turnstile> (($tr = $tr\<acute>) \<and> $wait\<acute>) ; (II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> (P\<^sup>t[true/okay]\<^sub>f)))`"
    apply(subst Seq_comp_form_2)
    apply (metis CSP_def Healthy_intro RH_def Stop_is_CSP1 Stop_is_CSP2 Stop_is_R1 Stop_is_R2 Stop_is_R3 comp_apply)
    apply(metis assms(1))
    apply(metis Stop_rel_closure)
    apply(metis assms(2))
    apply(subst 1)
    apply(subst 2)
    apply(subst 2)
    apply(subst SemiR_FalseP_left)
    apply(simp add:usubst typing defined closure)
    done
  also have "... = `RH (true \<turnstile> ($tr = $tr\<acute>) ; ($wait \<and> (II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> (P\<^sup>t[true/okay]\<^sub>f))))`"
    apply(subst SemiR_AndP_right_precond)
    apply(simp add:closure unrest typing defined)
    defer
    apply(utp_pred_auto_tac)
    apply (simp add:urename typing defined closure)
    apply(subst CondR_rel_closure)
    apply(simp_all add:closure)
    sorry
  also have "... = `RH (true \<turnstile> ($tr = $tr\<acute>) ; ($wait \<and> II\<^bsub>REL_VAR-OKAY\<^esub>))`"
    proof -
      have "`($wait \<and> (II\<^bsub>REL_VAR-OKAY\<^esub> \<lhd> $wait \<rhd> (P\<^sup>t[true/okay]\<^sub>f)))` = `$wait \<and> II\<^bsub>REL_VAR-OKAY\<^esub>`"by utp_pred_auto_tac
      thus ?thesis by metis
    qed
  also have "... = `RH (true \<turnstile> (($tr = $tr\<acute>) \<and> $wait\<acute>) ; II)`"
    apply(subst SemiR_AndP_right_precond)
    sorry
  also have "... =`RH (true \<turnstile> ($tr = $tr\<acute>) \<and> $wait\<acute>)`"
    by (metis SemiR_SkipR_right)
  also have "... = STOP" 
    by (metis AndP_comm EqualP_sym Stop_Design_form)
  finally show ?thesis
    ..
qed

lemma L3 : "(P \<sqinter> Q) \<box> S = (P \<box> S) \<sqinter> (Q \<box> S)"
oops

lemma L4 : "P \<sqinter> (Q \<box> S) = (P \<sqinter> Q) \<box> (P \<sqinter> S)"
oops

lemma L5 : 
  assumes "P is CSP1" 
  shows "`P \<box> SKIP` \<sqsubseteq> `SKIP` "
oops

lemma L6sub : "`((a1\<rightarrow>P1) \<box> (a2\<rightarrow>P2)); Q` = `(a1\<rightarrow>(P1;Q)) \<box> (a2\<rightarrow>(P2;Q))`"
oops
*)
lemma Prefixed_precondition: "`\<not>(a \<rightarrow> P)\<^sup>f[true/okay]\<^sub>f` = undefined"oops
lemma Prefixed_postcondition: "`(a \<rightarrow> P)\<^sup>t[true/okay]\<^sub>f` = undefined"oops

lemma External_precondition: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
shows"`CSP_Pre(P \<box> Q)` = `CSP_Pre(P) \<and> CSP_Pre(Q)`"
apply(simp add:ExternalChoiceCSP_def H2_def CSP_Pre_def)
apply(subst J_split)
apply(simp add:assms closure)
apply(simp add:CondR_def Stop_expansion usubst typing defined closure)
apply(utp_pred_auto_tac)
done

lemma External_postcondition:
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
shows "`CSP_Post(P \<box> Q)` = `\<not>CSP_Pre(P) \<or> \<not>CSP_Pre(Q) \<or> (CSP_Post(P) \<and> CSP_Post(Q) \<and> ($tr\<acute>=$tr) \<and> $wait\<acute>) \<or> ((CSP_Post(P) \<or> CSP_Post(Q)) \<and> \<not>(($tr\<acute>=$tr) \<and> $wait\<acute>))`"
apply(simp add:ExternalChoiceCSP_def H2_def CSP_Post_def CSP_Pre_def)
apply(subst J_split)
apply(simp add:assms closure)
apply(simp add:CondR_def Stop_expansion)
apply(simp add:usubst typing defined closure erasure)
apply(utp_pred_auto_tac)
done

lemma External_is_R1: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is R1" "Q is R1"
shows "P \<box> Q is R1"
apply(simp add:is_healthy_def ExternalChoiceCSP_def)
apply(subst CSP2_R1_commute[THEN sym])
apply(simp add:closure assms)
apply(simp add:R1_CondR R1_AndP R1_OrP)
apply(metis assms is_healthy_def)
done

lemma External_is_R2: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is R2" "Q is R2"
shows "P \<box> Q is R2"
apply(simp add:is_healthy_def ExternalChoiceCSP_def) sorry (*
apply(subst CSP2_R2_commute[THEN sym])
apply(simp add:closure assms)
apply(simp add:R2_CondR_alt R2_AndP R2_OrP)
apply(metis assms is_healthy_def Stop_is_R2)
done *)

lemma External_is_R3: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is R3" "Q is R3"
shows "P \<box> Q is R3"
apply(simp add:is_healthy_def ExternalChoiceCSP_def)
apply(subst CSP2_R3_commute[THEN sym])
apply(simp add:closure assms)
apply(simp add:R3_CondR R3_AndP R3_OrP)
apply(metis assms is_healthy_def)
done

lemma External_is_CSP1: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is CSP1" "Q is CSP1"
shows "P \<box> Q is CSP1"
apply(simp add:is_healthy_def ExternalChoiceCSP_def)
apply(subst CSP1_CSP2_commute)
apply(simp add:closure assms)
apply(simp add:CSP1_CondR CSP1_AndP CSP1_OrP)
apply(metis assms is_healthy_def)
done

lemma External_is_CSP2: 
  "P \<box> Q is CSP2"
by(simp add:ExternalChoiceCSP_def is_healthy_def CSP2_idempotent)

lemma External_rel_closure: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
shows "P \<box> Q \<in> WF_RELATION"
by(simp add:ExternalChoiceCSP_def closure assms)

lemma External_is_CSP:
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is CSP" "Q is CSP" 
shows  "P \<box> Q is CSP"
proof -
  have "CSP(P \<box> Q) = CSP1 (CSP2 (R1 (R2 (R3 (P \<box> Q)))))"
    by(simp add:CSP_def RH_def)
  also from External_is_R3[of "P" "Q"]  have "... =  CSP1 (CSP2 (R1 (R2 (P \<box> Q))))"
    by(metis is_healthy_def assms CSP_is_RH RH_is_R3)
  also from External_is_R2[of "P" "Q"]  have "... =  CSP1 (CSP2 (R1 (P \<box> Q)))"
    by(metis is_healthy_def assms CSP_is_RH RH_is_R2)
  also from External_is_R1[of "P" "Q"]  have "... =  CSP1 (CSP2 (P \<box> Q))"
    by(metis is_healthy_def assms CSP_is_RH RH_is_R1)
  also from External_is_CSP2[of "P" "Q"] have "... = CSP1 (P \<box> Q)"
    by(simp add:is_healthy_def)
  also from External_is_CSP1[of "P" "Q"] have "... = P \<box> Q"
    by (metis CSP1_idempotent CSP_def assms comp_apply is_healthy_def)
  finally show ?thesis
    by(simp add:is_healthy_def)
qed

lemma External_form: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is CSP" "Q is CSP"
shows "P \<box> Q = `RH((CSP_Pre(P) \<and> CSP_Pre(Q)) \<turnstile> ((CSP_Post(P) \<and> CSP_Post(Q)) \<lhd> ($tr\<acute>=$tr) \<and> $wait\<acute> \<rhd> (CSP_Post(P) \<or> CSP_Post(Q))))`"
apply(subst CSP_Design[of "P \<box> Q"])
apply(simp add: External_is_CSP assms)
apply(simp add: External_rel_closure assms(1) assms(2))
apply(subst External_precondition)
apply(metis assms(1))
apply(metis assms(2))
apply(subst External_postcondition)
apply(metis assms(1))
apply(metis assms(2))
apply(simp add:DesignD_def CSP_Pre_def CSP_Post_def)
apply(utp_pred_auto_tac)
done

lemma Parallel_precondition: "`\<not>(P \<parallel>\<^bsub>vs\<^esub> Q)\<^sup>f[true/okay]\<^sub>f` = undefined"oops
lemma Parallel_postcondition: "`(P \<parallel>\<^bsub>vs\<^esub> Q)\<^sup>t[true/okay]\<^sub>f` = undefined"oops

lemma Law_1: 
  assumes "`P \<box> Q` = `P`" 
  shows "`P\<^sup>f[true/okay]\<^sub>f \<Rightarrow> Q\<^sup>f[true/okay]\<^sub>f \<and> (P\<^sup>t[true/okay]\<^sub>f \<and> STOP) \<Rightarrow> Q\<^sup>t[true/okay]\<^sub>f`" "`(Q\<^sup>t[true/okay]\<^sub>f \<and> \<not>STOP) \<Rightarrow> P\<^sup>t[true/okay]\<^sub>f`"
oops

lemma Law_2: 
  assumes "`P\<^sup>f[true/okay]\<^sub>f \<Rightarrow> Q\<^sup>f[true/okay]\<^sub>f \<and> (P\<^sup>t[true/okay]\<^sub>f \<and> STOP) \<Rightarrow> Q\<^sup>t[true/okay]\<^sub>f \<and> (Q\<^sup>t[true/okay]\<^sub>f \<and> \<not>STOP) \<Rightarrow> P\<^sup>t[true/okay]\<^sub>f`"
  shows "`P \<box> Q` = `P`" 
sorry

lemma Law_3: 
  "`P \<box> Q` = `P` \<longleftrightarrow> `P\<^sup>f[true/okay]\<^sub>f \<Rightarrow> Q\<^sup>f[true/okay]\<^sub>f` \<and> `(P\<^sup>t[true/okay]\<^sub>f \<and> STOP) \<Rightarrow> Q\<^sup>t[true/okay]\<^sub>f` \<and> `(Q\<^sup>t[true/okay]\<^sub>f \<and> \<not>STOP) \<Rightarrow> P\<^sup>t[true/okay]\<^sub>f`"
sorry

lemma Law_4: 
  assumes "`P` = `(a \<rightarrow> R) \<box> S`" "`[Q \<Rightarrow> a \<notin> elems ($tr\<acute>-$tr) \<union> $ref \<union> $ref\<acute>]`" "(VAR - aa) \<sharp> a" "aa \<sharp> P" "aa \<sharp> Q" 
  shows "`P \<parallel>\<^bsub>vs\<^esub> Q` = `(P \<parallel>\<^bsub>vs\<^esub> Q) \<box> (a \<rightarrow> (R \<parallel>\<^bsub>vs\<^esub> Q)) `"
apply(subst Law_2)
sorry

end