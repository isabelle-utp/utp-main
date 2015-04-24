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
  have "`P ; Q` = `CSP1(P);Q`" 
    by (metis assms is_healthy_def)
  also have "... = `(P;Q) \<or> (\<not>$ok \<and> ($tr \<le> $tr\<acute>));Q`" 
    by(subst CSP1_def, simp add: SemiR_OrP_distr)
  also have "... = `(P;Q) \<or> (\<not>$ok \<and> ($tr \<le> $tr\<acute>));R1(CSP1(Q))`" 
    by(metis assms is_healthy_def)
  also have "... = `(P ; Q \<or> (\<not> $ok \<and> ($tr \<le> $tr\<acute>)) ; (Q \<and> ($tr \<le> $tr\<acute>)) \<or> (\<not> $ok \<and> ($tr \<le> $tr\<acute>)) ; ($tr \<le> $tr\<acute>))`"
    by(simp add:R1_def CSP1_def AndP_OrP_distr AndP_assoc[THEN sym] SemiR_OrP_distl SemiR_remove_middle_unrest1[of _ _ "{ok \<down>}"] typing closure unrest)
  also have "... = `(P ; Q \<or> (\<not> $ok \<and> ($tr \<le> $tr\<acute>)) ; ($tr \<le> $tr\<acute>))`"
    by(utp_poly_auto_tac)
  also have "... = `CSP1(P;Q)`"
    by(simp add:SemiR_AndP_left_precond typing closure defined tr_leq_trans CSP1_def[THEN sym])
  finally show ?thesis 
    by (metis is_healthy_def)
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
proof-
  have "R2( CSP2 P) = `R2 (P\<^sup>f) \<or> R2 (P\<^sup>t) \<and> R2s ($ok\<acute>)`"
      by(simp add:H2_split R1_OrP R1_extend_AndP R2s_AndP R2s_OrP R2_def)
  also have "... = `R2 (P)\<^sup>f \<or> R2 (P)\<^sup>t \<and> $ok\<acute>`"
      by(simp add: R2_ok'_true[simplified]  R2_ok'_false[simplified] R2s_def usubst typing defined closure)
  also have "... = CSP2 (R2 P)"
      by(simp add:H2_split)
  finally show ?thesis ..
qed


lemma CSP1_SkipR: "`CSP1(II)` = `(\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($ok \<and> $ok\<acute> \<and> II\<^bsub>REL_VAR - OKAY\<^esub>)`"
proof -
  have "`CSP1(II)` = `CSP1($ok \<and> II[true/ok])`"
    by(simp add:closure CSP1_R1_form)
  also have "... = `CSP1 ($ok \<and> (($ok\<acute> = $ok) \<and> II\<^bsub>REL_VAR - OKAY\<^esub>)[true/ok])`"
    by(simp add:SkipRA_unfold_aux_ty[of "ok"] closure typing defined SkipR_as_SkipRA)
  also have "... = `CSP1($ok \<and> $ok\<acute>=true \<and> II\<^bsub>REL_VAR - OKAY\<^esub>)`"
    by(simp add:usubst typing defined closure)
  also have "... = `CSP1($ok \<and> $ok\<acute> \<and> II\<^bsub>REL_VAR - OKAY\<^esub>)`"
    by(utp_poly_auto_tac)
  finally show ?thesis by(simp add:CSP1_def OrP_comm)
qed

lemma CSP2_R3c_commute: 
  "CSP2 (R3c P) = R3c (CSP2 (P))"
proof - 
have 0: "CSP1 II is CSP2"
proof -
  have "`CSP2(CSP1(II))` = `(\<not> $ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($ok \<and> II\<^bsub>REL_VAR - OKAY\<^esub> \<and> $ok\<acute>)`"
    by(simp add:CSP1_SkipR H2_split usubst typing defined closure AndP_OrP_distr OrP_assoc OrP_AndP_absorb AndP_assoc)
  also have "... = `CSP1(II)`"
    by(simp add:CSP1_SkipR AndP_comm)
  finally show ?thesis by (metis is_healthy_def)
qed
have "CSP2(R3c P) = `(($wait \<and> CSP1(II)) ; J \<or> (\<not> $wait \<and> P) ; J)`"
by(simp add:H2_def R3c_def CondR_def SemiR_OrP_distr)
also have "... = `(($wait \<and> CSP1(II) ; J) \<or> \<not> $wait \<and> P ; J)`"
by(simp add: SemiR_AndP_left_DASHED unrest typing defined closure)
also have "... = `(($wait \<and> CSP1(II)) \<or> \<not> $wait \<and> P ; J)`"
by(metis H2_def[THEN sym] is_healthy_def 0)
also have "... = R3c(CSP2 P)"
by(simp add:H2_def R3c_def CondR_def SemiR_OrP_distr)
finally show ?thesis .
qed

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
  proof-
  have "`R1(R3c(P))` = `R1 (CSP1 (($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - TR\<^esub>) \<lhd> $wait \<rhd> P)`"
    by(simp add:R3c_def SkipR_as_SkipRA closure typing SkipRA_unfold_aux_ty[of "tr"])
  also have "... = `CSP1 (($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - TR\<^esub>) \<lhd> $wait \<rhd> R1 (P)`"  
    by(utp_poly_auto_tac)
  also have "... = `R3c(R1(P))`"
    by(simp add:R3c_def SkipRA_unfold_aux_ty[of "tr "] SkipR_as_SkipRA closure typing) 
  finally show ?thesis .
qed

lemma R2_R3c_commute: "`R2(R3c(P))` =`R3c(R2(P))`"
  by(simp add:R3c_def R2_CondR R2s_def usubst typing defined closure CSP1_R2_commute[THEN sym] SkipRA_is_R2)

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
proof -
have "`R3c(P)` =  `($wait \<and> CSP1 ($ok \<and> II)) \<or> (\<not> $wait \<and> P)`"
by(simp add:R3c_def CondR_def NotP_PVarPE_PSubstPE[THEN sym] typing CSP1_R1_form_2 R1_SkipR is_healthy_def)
also have "... = `(\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> ($ok \<and> $wait  \<and> II) \<or> (\<not>$wait \<and> P \<^sub>f)`"
by (utp_poly_auto_tac)
finally show ?thesis .
qed

lemma CSP1_R1_R3c_compose: 
  assumes "P is R1"
  shows "R3c(CSP1(P)) = `(\<not>$ok \<and> ($tr\<le>$tr\<acute>)) \<or> ($ok \<and> $wait \<and> II) \<or> ($ok \<and> \<not>$wait \<and> P[true/ok][false/wait])`"
  by (simp add:assms CSP1_R1_form, simp add:R3c_form CSP1_def,utp_poly_auto_tac)

lemma CSP1_R3_ok': 
"`CSP1($ok\<acute> \<and> R3c(P))` = `CSP1(R3c($ok\<acute> \<and> P))`"
  by (simp add:R3c_form CSP1_def SkipR_as_SkipRA SkipRA_unfold_aux_ty[of "ok" "REL_VAR"] closure typing usubst,utp_poly_auto_tac)

lemma R3c_seq_comp_1: 
  assumes "Q is R3c" "Q is R1" "Q \<in> WF_RELATION"
  shows "`(\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>));Q` = `\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)`"
proof -
  have "`(\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>));Q` = `(\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>));R1(R3c(Q))`"
    by(metis assms is_healthy_def)
  also have "... = `\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>);R1(R3c(Q))`"
    by(simp add: SemiR_AndP_left_precond closure typing defined assms)
  also have "... = `\<not>$ok \<and> $wait \<and> (
                       ($tr \<le> $tr\<acute>) ; (\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or>
                       ($tr \<le> $tr\<acute>) ; ($ok \<and> $wait \<and> ($ok\<acute>=$ok) \<and> ($wait\<acute>=$wait) \<and> II\<^bsub>REL_VAR - {ok\<down>, ok\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>}\<^esub> \<and> ($tr \<le> $tr\<acute>)) \<or>
                       ($tr \<le> $tr\<acute>) ; (\<not> $wait \<and> Q[false/wait] \<and> ($tr \<le> $tr\<acute>)))`"
    by(simp add:R1_def R3c_form SemiR_OrP_distl AndP_OrP_distr SkipR_as_SkipRA  SkipRA_unfold_aux_ty[of "ok" "REL_VAR"]  SkipRA_unfold_aux_ty[of "wait" "REL_VAR - OKAY"] typing closure AndP_assoc[THEN sym])
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
                       ($tr \<le> $tr\<acute>) ; ($ok \<and> $wait \<and> $ok\<acute> \<and> $wait\<acute> \<and> II\<^bsub>REL_VAR - {ok\<down>, ok\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>}\<^esub> \<and> ($tr \<le> $tr\<acute>)) \<or>
                       ($tr \<le> $tr\<acute>) ; (Q[false/wait] \<and> ($tr \<le> $tr\<acute>)))`"
    by(simp add:AndP_assoc[THEN sym] SemiR_remove_middle_unrest1[of "`$tr\<le>$tr\<acute>`" "`$wait \<and> ($tr\<le>$tr\<acute>)`" "{ok \<down>}" "`\<not>$ok`"] SemiR_remove_middle_unrest1[of "`$tr\<le>$tr\<acute>`" "`Q[false/wait] \<and> ($tr\<le>$tr\<acute>)`" "{wait \<down>}" "`\<not>$wait`"] SemiR_remove_middle_unrest1[of "`$tr\<le>$tr\<acute>`" "`($tr\<le>$tr\<acute>)`" "{wait \<down>}" "`$wait`"] typing closure defined unrest assms)
 also have "... = `\<not>$ok \<and> $wait \<and> (
                       ($tr \<le> $tr\<acute>) ; ($tr \<le> $tr\<acute>) \<or>
                       ($tr \<le> $tr\<acute>) ; ($ok\<acute> \<and> $wait\<acute> \<and> II\<^bsub>REL_VAR - {ok\<down>, ok\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>}\<^esub> \<and> ($tr \<le> $tr\<acute>)) \<or>
                       ($tr \<le> $tr\<acute>) ; (Q[false/wait] \<and> ($tr \<le> $tr\<acute>)))`"
    by(utp_poly_auto_tac)
also have "... = `\<not>$ok \<and> $wait \<and> ($tr \<le> $tr\<acute>);((true \<or> ($ok\<acute> \<and> $wait\<acute> \<and> II\<^bsub>REL_VAR - {ok \<down>,ok \<down>\<acute>} - {wait \<down>,wait \<down>\<acute>}\<^esub>) \<or> Q[false/wait]) \<and> ($tr \<le> $tr\<acute>))`"
  by(utp_poly_auto_tac)
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
    by(simp add:SkipR_as_SkipRA SemiR_AndP_right_precond urename assms AndP_assoc[THEN sym] SkipRA_unfold_aux_ty[of "ok" "REL_VAR"] SkipRA_unfold_aux_ty[of "wait" "REL_VAR - OKAY"] closure typing, utp_poly_auto_tac)
  also have "... = `($ok \<and> $wait \<and> II\<^bsub>REL_VAR - OKAY - {wait \<down>,wait \<down>\<acute>}\<^esub>);($ok \<and> $wait \<and> R3c(Q))`"
    proof -
      have 1: "Q = `R3c(Q)`"
        by(metis is_healthy_def assms)
      show ?thesis
        by(subst 1,simp)
    qed
  also have "... = `($ok \<and> $wait \<and> II\<^bsub>REL_VAR - OKAY - {wait \<down>,wait \<down>\<acute>}\<^esub>);($ok \<and> $wait \<and> II)`"
    by(utp_poly_auto_tac)
  also have "... = `($ok \<and> $wait \<and> II\<^bsub>REL_VAR - OKAY - {wait \<down>,wait \<down>\<acute>}\<^esub> \<and> $ok\<acute> \<and> $wait\<acute>)`"
    by(simp add:SemiR_AndP_right_precond assms closure typing urename AndP_assoc[THEN sym])
  also have "... = `$ok \<and> $wait \<and> II`"
    by(simp add:SkipR_as_SkipRA SkipRA_unfold_aux_ty[of "ok" "REL_VAR"] SkipRA_unfold_aux_ty[of "wait" "REL_VAR - OKAY"] closure typing,utp_poly_auto_tac)
  finally show ?thesis
    by this
qed

lemma R3c_SemiR_closure:
  assumes "P is R3c" "Q is R3c" "P \<in> WF_RELATION" "Q\<in> WF_RELATION" "Q is R1"
  shows " `P ; Q` is R3c"
proof -
have "`P;Q` = `R3c(P);Q`"by(metis assms is_healthy_def)
also have "... = `(\<not> $ok \<and> $wait \<and> ($tr \<le> $tr\<acute>)) \<or> ($ok \<and> $wait \<and> II) \<or> (\<not> $wait \<and> P[false/wait]) ; Q `"
   by(simp add:R3c_form SemiR_OrP_distr R3c_seq_comp_1 assms R3c_seq_comp_2)
also have "... = `R3c(P;Q)`"
   by(simp add: SemiR_AndP_left_precond typing closure defined unrest assms R3c_form SubstP_SemiR_left)
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