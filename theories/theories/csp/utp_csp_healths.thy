(******************************************************************************)
(* Project: Mechanation of the UTP                                            *)
(* File: utp_csp.thy                                                          *)
(* Authors: Samuel Canham and Simon Foster, University of York                *)
(******************************************************************************)

header {* CSP Process Healthiness Conditions *}

theory utp_csp_healths
imports 
  "../utp_reactive"
begin

text {* If CSP1 processes are unstable, the only thing that can be said is that they are also R1 *}

definition CSP1 :: "'a upred \<Rightarrow> 'a upred" where
"CSP1 P = `P \<or> (\<not> $ok \<and> ($tr \<le> $tr\<acute>))`"

text {* CSP2 is H2 *}

abbreviation "CSP2 \<equiv> H2"

text {* R3c processes are similar to R3 processes, except they can be CSP1 unstable even when waiting *}

definition R3c :: "'a upred \<Rightarrow> 'a upred" where
"R3c P = `CSP1(II) \<lhd> $wait \<rhd> P`"

text {* RHc is the composition of R1, R2 and R3c *}

definition RHc :: "'a upred \<Rightarrow> 'a upred" where
"RHc P = (R1 \<circ> R2 \<circ> R3c) P"

text {* CSP is the composition of CSP1, CSP2 and RHc *}

definition CSP :: "'a upred \<Rightarrow> 'a upred" where
"CSP P = (CSP1 \<circ> CSP2 \<circ> RHc) P"

declare R3c_def [eval, evalr, evalrr, evalrx, evalp]
declare RHc_def [eval, evalr, evalrr, evalrx, evalp]
declare CSP1_def [eval, evalr, evalrr, evalrx, evalp]
declare CSP_def [eval, evalr, evalrr, evalrx, evalp]

subsection {* Closure laws *}

lemma CSP1_rel_closure[closure]:
  "P \<in> WF_RELATION \<Longrightarrow> CSP1(P) \<in> WF_RELATION"
by (metis CSP1_def DesignD_extreme_point_nok(2) OrP_rel_closure R1_def R1_rel_closure TopD_rel_closure)

lemma CSP2_rel_closure[closure]: 
  "P \<in> WF_RELATION \<Longrightarrow> CSP2(P) \<in> WF_RELATION"
by (metis H2_def J_closure SemiR_closure)

lemma R3c_rel_closure[closure]: 
  "P \<in> WF_RELATION \<Longrightarrow> R3c(P) \<in> WF_RELATION"
by (simp add:R3c_def closure)

lemma RHc_rel_closure[closure]:
  "P \<in> WF_RELATION \<Longrightarrow> RHc(P) \<in> WF_RELATION"
by (metis  R1_rel_closure R2_rel_closure R3c_rel_closure RHc_def o_eq_dest_lhs)

lemma CSP_rel_closure[closure]:
  "P \<in> WF_RELATION \<Longrightarrow> CSP(P) \<in> WF_RELATION"
by (metis RHc_rel_closure CSP1_rel_closure CSP2_rel_closure CSP_def o_eq_dest_lhs)

subsection {* CSP1 laws *}

lemma CSP1_idempotent: "`CSP1(CSP1(P))` = `CSP1(P)`" 
  by (utp_pred_auto_tac)

lemma CSP1_monotonic: 
  "P \<sqsubseteq> Q \<Longrightarrow> CSP1(P) \<sqsubseteq> CSP1(Q)"
  by (utp_pred_tac)

lemma CSP1_R1_commute: "CSP1 (R1 P) = R1 (CSP1 (P))"by utp_pred_auto_tac
lemma CSP1_R2_commute: "CSP1 (R2 P) = R2 (CSP1 (P))"by(simp add:CSP1_def R2_def R2s_def usubst typing defined closure, utp_pred_auto_tac)
lemma CSP1_R3c_commute: "CSP1 (R3c P) = R3c (CSP1 (P))"by(simp add:CSP1_def R3c_def, utp_poly_auto_tac)

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
  shows "CSP1(P) = `CSP1($ok \<and> P)`"
using assms
by(utp_poly_auto_tac)

lemma CSP1_R1_form: 
  assumes "P is R1"
  shows "CSP1(P) = `CSP1($ok \<and> P[true/ok])`"
proof -
  have "CSP1(P) = `CSP1($ok \<and> P)`"
    by(simp add: CSP1_R1_compose assms)
  also have "... = `CSP1 ($ok \<and> P[true/ok])`"
    by (subst PVarPE_PSubstPE,simp_all add: typing)
  finally show ?thesis .
qed

lemma CSP1_R1_form_2: 
  assumes "P is R1"
  shows "CSP1(P) = `CSP1($ok \<and> P)`"
by (metis CSP1_R1_compose assms)

lemma CSP1_SemiR_closure:
  assumes "P is CSP1" "Q is CSP1" "Q is R1"
  shows " `P ; Q` is CSP1"
proof -
have "`P ; Q` = `CSP1(P);Q`" by (metis assms is_healthy_def)
also have "... = `(P;Q) \<or> (\<not>$ok \<and> ($tr \<le> $tr\<acute>));R1(CSP1(Q))`" 
apply(subst CSP1_def, simp add: SemiR_OrP_distr)
apply(metis assms is_healthy_def)
done
also have "... = ` (P ; Q) \<or> (\<not> $ok \<and> ($tr \<le> $tr\<acute>)) ; ((Q \<or> true) \<and> ($tr \<le> $tr\<acute>))`"
apply(subst AndP_OrP_distr)
apply(simp add:R1_def CSP1_def AndP_OrP_distr AndP_assoc[THEN sym] SemiR_OrP_distl)
apply(subst SemiR_remove_middle_unrest1[of _ _ "{ok \<down>}"],simp_all add:typing closure unrest) back
done
also have "... = `CSP1(P ; Q)`"
by(simp add:SemiR_AndP_left_precond typing closure defined tr_leq_trans CSP1_def)
finally show ?thesis by (metis is_healthy_def)
qed

subsection {* CSP2 laws *}

lemma CSP2_idempotent: "`CSP2(CSP2(P))` = `CSP2(P)`"
  by (metis H2_idempotent)

lemma CSP2_monotonic:
  "P \<sqsubseteq> Q \<Longrightarrow> CSP2(P) \<sqsubseteq> CSP2(Q)"
  by (metis H2_monotone)

lemma CSP1_CSP2_commute:
   "CSP1 (CSP2 P) = CSP2 (CSP1 P)" 
by(simp add:H2_split CSP1_def usubst typing defined closure,utp_poly_auto_tac) 

lemma CSP2_R1_commute: 
   "CSP2 (R1 P) = R1 (CSP2 (P))"
by(simp add:H2_split R1_def usubst typing defined closure,utp_pred_auto_tac)

lemma CSP2_R2_commute:
  "CSP2 (R2 P) = R2 (CSP2 (P))"
apply(simp add:H2_split R2_OrP)
apply(subst R2_def) back back back
apply(simp add:R2s_AndP R1_extend_AndP[THEN sym])
apply(simp add:R2_def[THEN sym])
apply(simp add:R2s_def usubst typing defined closure)
apply (metis (hide_lams, no_types) PVAR_VAR_pvdash R2_ok'_false R2_ok'_true)
done

lemma CSP1_SkipR: "`CSP1(II)` = `(\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($ok \<and> $ok\<acute> \<and> II\<^bsub>REL_VAR - OKAY\<^esub>)`"
apply(simp add:R1_SkipR is_healthy_def CSP1_R1_form,simp add: SkipR_as_SkipRA)
apply(subst SkipRA_unfold_aux_ty[of "ok"], simp_all add:usubst typing defined closure)
apply(utp_poly_auto_tac)
done

lemma CSP2_R3c_commute: 
  "CSP2 (R3c P) = R3c (CSP2 (P))"
apply(simp add:H2_split usubst typing closure defined CSP1_SkipR R3c_def)
apply(utp_poly_auto_tac)
done

lemma CSP2_SemiR_closure:
  assumes "Q is CSP2"
  shows " `P ; Q` is CSP2"
by(metis assms SemiR_is_H2)

subsection {* R3c laws *}

lemma R3c_idempotent: "`R3c(R3c(P))` = `R3c(P)`"
by(utp_poly_auto_tac)

lemma R3c_monotonic: 
  "P \<sqsubseteq> Q \<Longrightarrow> R3c(P) \<sqsubseteq> R3c(Q)"
  by (utp_pred_tac)

lemma R1_R3c_commute: "`R1(R3c(P))` =`R3c(R1(P))`"
  apply(simp add:R3c_def SkipR_as_SkipRA)
  apply(subst SkipRA_unfold_aux_ty[of "tr "], simp_all add:closure typing)
  apply(subst SkipRA_unfold_aux_ty[of "tr "], simp_all add:closure typing) back
  apply(utp_poly_auto_tac)
done

lemma R2_R3c_commute: "`R2(R3c(P))` =`R3c(R2(P))`"
  apply(simp add:R3c_def SkipR_as_SkipRA)
  apply(subst SkipRA_unfold_aux_ty[of "tr "], simp_all add:closure typing)
  apply(subst SkipRA_unfold_aux_ty[of "tr "], simp_all add:closure typing) back
  apply(simp add:CSP1_def R2_def R2s_def usubst typing defined closure R1_OrP R1_CondR R1_extend_AndP[THEN sym])
  apply(simp add:R1_def tr_prefix_as_nil)
  done

lemma R3c_AndP: 
  "`R3c(P \<and> Q)` = `R3c(P) \<and> R3c(Q)`"
  by utp_pred_auto_tac

lemma R3c_OrP: 
  "`R3c(P \<or> Q)` = `R3c(P) \<or> R3c(Q)`"
  by utp_pred_auto_tac

lemma R3c_CondR: 
  "`R3c(P \<lhd> b \<rhd> Q)` = `R3c(P) \<lhd> b \<rhd> R3c(Q)`"
  by utp_pred_auto_tac

lemma R3c_form : "`R3c(P)` = `(\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> ($ok \<and> $wait  \<and> II) \<or> (\<not>$wait \<and> P \<^sub>f)`"
apply(simp add:R3c_def CondR_def)
apply(subst NotP_PVarPE_PSubstPE,simp_all add:typing CSP1_R1_form_2 R1_SkipR is_healthy_def)
apply (utp_poly_auto_tac)
done

lemma CSP1_R1_R3c_compose: 
  assumes "P is R1"
  shows "R3c(CSP1(P)) = `(\<not>$ok \<and> ($tr\<le>$tr\<acute>)) \<or> ($ok \<and> $wait \<and> II) \<or> ($ok \<and> \<not>$wait \<and> P[true/ok][false/wait])`"
  by (simp add:assms CSP1_R1_form, simp add:R3c_form CSP1_def,utp_poly_auto_tac)

lemma CSP1_R3_ok': 
"`CSP1($ok\<acute> \<and> R3c(P))` = `CSP1(R3c($ok\<acute> \<and> P))`"
  apply (simp add:R3c_form CSP1_def SkipR_as_SkipRA)
  apply (subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:closure typing)
  apply (subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:closure typing) back
  apply (utp_poly_auto_tac)
done

lemma R3c_seq_comp_1: 
  assumes "Q is R3c" "Q is R1" "Q \<in> WF_RELATION"
  shows "`(\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>));Q` = `\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)`"
proof -
  have "`(\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>));Q` = `(\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>));R1(R3c(Q))`"
    by(metis assms is_healthy_def)
  also have "... = `\<not>$ok \<and> $wait \<and> (
                       ($tr \<le> $tr\<acute>) ; (\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or>
                       ($tr \<le> $tr\<acute>) ; ($ok \<and> $wait \<and> ($ok\<acute>=$ok) \<and> ($wait\<acute>=$wait) \<and> II\<^bsub>REL_VAR - {ok\<down>, ok\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>}\<^esub> \<and> ($tr \<le> $tr\<acute>)) \<or>
                       ($tr \<le> $tr\<acute>) ; (\<not> $wait \<and> Q[false/wait] \<and> ($tr \<le> $tr\<acute>)))`"
    apply(simp add: SemiR_AndP_left_precond closure typing defined assms)
    apply(simp add:R1_def R3c_form SemiR_OrP_distl AndP_OrP_distr AndP_assoc[THEN sym] SkipR_as_SkipRA)
    apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing closure)
    apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add:typing closure)
    apply(simp add:AndP_assoc[THEN sym])
    done
  also have "... = `\<not>$ok \<and> $wait \<and> (
                       ($tr \<le> $tr\<acute>) ; (\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or>
                       ($tr \<le> $tr\<acute>) ; (($ok \<and> $wait \<and> $ok\<acute> \<and> $wait\<acute>) \<and> II\<^bsub>REL_VAR - {ok\<down>, ok\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>}\<^esub> \<and> ($tr \<le> $tr\<acute>)) \<or>
                       ($tr \<le> $tr\<acute>) ; (\<not> $wait \<and> Q[false/wait] \<and> ($tr \<le> $tr\<acute>)))`"
    proof -
      have 0: "`$ok \<and> $wait \<and> ($ok\<acute>=$ok) \<and> ($wait\<acute>=$wait)`= `$ok \<and> $wait \<and> $ok\<acute> \<and> $wait\<acute>`"
        by(utp_poly_auto_tac)
      show ?thesis 
        by(subst 0[THEN sym],simp add:AndP_assoc[THEN sym])
   qed
 also have "... = `\<not>$ok \<and> $wait \<and> (
                       ($tr \<le> $tr\<acute>) ; ($tr \<le> $tr\<acute>) \<or>
                       ($tr \<le> $tr\<acute>) ; ($ok\<acute> \<and> $wait\<acute> \<and> II\<^bsub>REL_VAR - {ok\<down>, ok\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>}\<^esub> \<and> ($tr \<le> $tr\<acute>)) \<or>
                       ($tr \<le> $tr\<acute>) ; (Q[false/wait] \<and> ($tr \<le> $tr\<acute>)))`"
    apply(simp add:AndP_assoc[THEN sym])
    apply(simp add: SemiR_remove_middle_unrest1[of _ _ "{ok \<down>}"] typing closure defined unrest assms)
    apply(simp add: SemiR_remove_middle_unrest1[of _ _ "{wait \<down>}"] typing closure defined unrest assms)
    apply(subst SemiR_remove_middle_unrest1[of _ _ "{ok \<down>}"],simp_all add: typing closure defined unrest)
defer 
apply(utp_poly_auto_tac)
apply(rule unrest) back back
apply(simp_all add:unrest closure typing)
apply(rule unrest) back back
apply(simp_all add:unrest closure typing)
apply(rule unrest) back back
apply(simp_all add:unrest closure typing)
apply(rule unrest) back back
apply(subst UNREST_subset)
apply(subst UNREST_SkipRA)
apply(simp_all add:typing closure defined unrest) 
done
also have "... = `\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>);((true \<or> ($ok\<acute> \<and> $wait\<acute> \<and> II\<^bsub>REL_VAR - {ok \<down>,ok \<down>\<acute>} - {wait \<down>,wait \<down>\<acute>}\<^esub>) \<or> Q[false/wait]) \<and> ($tr \<le> $tr\<acute>))`"
apply(subst AndP_OrP_distr)
apply(simp add:AndP_OrP_distr SemiR_OrP_distl AndP_assoc[THEN sym])
done
also have "... = `\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)`"
  by(simp add:utp_pred_simps(8) tr_leq_trans)
  finally show ?thesis
    by this
qed

lemma R3c_seq_comp_2: 
  assumes "Q is R3c"
  shows "`($ok \<and> $wait \<and> II);Q` = `$ok \<and> $wait \<and> II`"
proof -
  have "`($ok \<and> $wait \<and> II);Q` =`($ok \<and> $wait \<and> II\<^bsub>REL_VAR - OKAY - {wait \<down>,wait \<down>\<acute>}\<^esub>);($ok \<and> $wait \<and> Q)`"
    apply(simp add:SkipR_as_SkipRA SemiR_AndP_right_precond typing closure urename assms AndP_assoc[THEN sym])
    apply(subst SkipRA_unfold_aux_ty[of "ok"], simp_all add:closure typing)
    apply(subst SkipRA_unfold_aux_ty[of "wait"], simp_all add:closure typing)
    apply(utp_poly_auto_tac)
    done
  also have "... = `($ok \<and> $wait \<and> II\<^bsub>REL_VAR - OKAY - {wait \<down>,wait \<down>\<acute>}\<^esub>);($ok \<and> $wait \<and> R3c(Q))`"
    proof -
      have 1: "Q = `R3c(Q)`"
        by(metis is_healthy_def assms)
      show ?thesis
        by(subst 1,simp)
    qed
  also have "... = `($ok \<and> $wait \<and> II\<^bsub>REL_VAR - OKAY - {wait \<down>,wait \<down>\<acute>}\<^esub>);($ok \<and> $wait \<and> II)`"
    apply(simp add:R3c_def CSP1_def)
    apply(utp_poly_auto_tac)
    done
  also have "... = `($ok \<and> $wait \<and> II\<^bsub>REL_VAR - OKAY - {wait \<down>,wait \<down>\<acute>}\<^esub> \<and> $ok\<acute> \<and> $wait\<acute>)`"
    by(simp add:SemiR_AndP_right_precond assms closure typing urename AndP_assoc[THEN sym])
  also have "... = `$ok \<and> $wait \<and> II`"
    apply(simp add:SkipR_as_SkipRA)
    apply(subst SkipRA_unfold_aux_ty[of "ok"], simp_all add:closure typing) back
    apply(subst SkipRA_unfold_aux_ty[of "wait"], simp_all add:closure typing) back
    apply(utp_poly_auto_tac)
    done
  finally show ?thesis
    by this
qed

lemma R3c_SemiR_closure:
  assumes "P is R3c" "Q is R3c" "P \<in> WF_RELATION" "Q\<in> WF_RELATION" "Q is R1"
  shows " `P ; Q` is R3c"
proof -
have "`P;Q` = `R3c(P);Q`"by(metis assms is_healthy_def)
also have "... = `R3c(P;Q)`"
   apply(simp add:R3c_form)
   apply(subst SubstP_SemiR_left,simp_all add:typing defined closure unrest)
   apply(simp add: SemiR_OrP_distr R3c_seq_comp_1 assms R3c_seq_comp_2)
   apply(subst SemiR_AndP_left_precond,simp_all add:typing closure defined unrest assms)
   done
finally show ?thesis by (metis is_healthy_def)
qed

subsection {* RHc laws *}

lemma RHc_is_R1: 
  assumes "P is RHc"
  shows "P is R1"
by (metis Healthy_elim Healthy_intro R1_idempotent RHc_def assms comp_apply)

lemma RHc_is_R2: 
  assumes "P is RHc"
  shows "P is R2"
by (metis Healthy_elim Healthy_intro R1_R2_commute R2_idempotent RHc_def assms comp_apply)

lemma RHc_is_R3c: 
  assumes "P is RHc"
  shows "P is R3c"
by (metis Healthy_elim Healthy_intro R1_R3c_commute R2_R3c_commute R3c_idempotent RHc_def assms comp_apply)

end