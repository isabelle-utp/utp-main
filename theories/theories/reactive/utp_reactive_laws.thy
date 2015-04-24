(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_reactive.thy                                                     *)
(* Authors: Simon Foster and Samuel Canham, University of York                *)
(******************************************************************************)

header {* Reactive Process Laws *}

theory utp_reactive_laws
imports 
  utp_reactive_healths
begin

definition RH :: "'a upred \<Rightarrow> 'a upred" where 
"RH P = (R1 \<circ> R2 \<circ> R3)P"

declare RH_def [eval, evalr, evalrr, evalrx, evalpp, evalpr]

lemma RH_rel_closure [closure]: 
  "P \<in> WF_RELATION \<Longrightarrow> RH(P) \<in> WF_RELATION"
  by (simp add:RH_def closure)

lemma RH_is_R1:
  "P is RH \<Longrightarrow> P is R1"
  by (metis Healthy_intro Healthy_simp R1_idempotent RH_def comp_apply)

lemma RH_is_R2:
  "P is RH \<Longrightarrow> P is R2"
  by (metis Healthy_intro Healthy_simp R1_idempotent R2_R3_commute R2_def R3_idempotent RH_def comp_apply)

lemma RH_is_R3:
  "P is RH \<Longrightarrow> P is R3"
  by (metis Healthy_intro Healthy_simp R1_R3_commute R1_idempotent R2_R3_commute R2_def R3_idempotent RH_def o_eq_dest_lhs)

lemma R_intro: "\<lbrakk> P is R1; P is R2; P is R3 \<rbrakk> \<Longrightarrow> P is RH"
  by (metis RH_def comp_apply is_healthy_def)

(* L1 reactive-left-zero *)

lemma R1_true_left_zero: 
  assumes "P is R1" "P is R3" "P \<in> WF_RELATION"
  shows "`($tr \<le> $tr\<acute>) ; P` = `($tr \<le> $tr\<acute>) \<and> ($wait\<acute> \<or> ($tr \<le> $tr\<acute>);P \<^sub>f)`"
proof -
have "`($tr \<le> $tr\<acute>) ; P` is R1"
by(simp add: R1_SemiR_closure assms closure)
 hence "`($tr \<le> $tr\<acute>) ; P` = `R1(($tr \<le> $tr\<acute>) ; R3(R1(P)))`"
 by (metis assms is_healthy_def)
also have "... =  `R1(($tr \<le> $tr\<acute>) \<and> $wait\<acute>) \<or> R1(($tr \<le> $tr\<acute>) ; (\<not> $wait \<and> R1(P)))`"
  by(simp add:R3_def CondR_def SemiR_OrP_distl SemiR_AndP_right_precond typing closure defined urename R1_OrP)
also have "... =  `(($tr \<le> $tr\<acute>) \<and> $wait\<acute>) \<or> R1(($tr \<le> $tr\<acute>) ; (\<not> $wait \<and> R1(P \<^sub>f)))`"
  by(subst AndP_comm,subst NotP_PVarPE_PSubstPE,simp_all add:typing defined R1_def usubst closure AndP_assoc[THEN sym],subst AndP_comm,simp)
also have "... =  `($tr \<le> $tr\<acute>) \<and> ($wait\<acute> \<or> (($tr \<le> $tr\<acute>) ; R1(P \<^sub>f)))`" 
  by(subst SemiR_remove_middle_unrest1[of _ _ "{wait\<down>}"],simp_all add:typing defined closure unrest assms R1_def,utp_poly_auto_tac) 
also have "... =  `($tr \<le> $tr\<acute>) \<and> ($wait\<acute> \<or> (($tr \<le> $tr\<acute>) ; P \<^sub>f))`" 
  by(subst R1_wait_false[THEN sym],metis assms is_healthy_def)
finally show ?thesis .
qed

(* L2 restricted-identity *)

lemma Skip_identity:
  "`II ; P` = P"
by (metis SemiR_SkipR_left)

(* L3 R-wait-false *)

lemma RH_wait_false: 
  "`(RH(P))\<^sub>f` = `R1(R2(P \<^sub>f))`"
by(simp add:RH_def R1_wait_false R2_wait_false R3_wait_false)

(* L4 R-wait-true *)

lemma RH_wait_true: 
  "`(RH(P))\<^sub>t` = `II \<^sub>t`"
by(simp add:RH_def R2_R3_commute R1_R3_commute R3_wait_true)

(* L6 closure-\<and>-R *)

lemma RH_AndP_closure:
  assumes "P is RH" "Q is RH"
  shows "`P \<and> Q` is RH"
using assms
by(utp_poly_auto_tac)

(* L7 closure-\<or>-R *)

lemma RH_OrP_closure:
  assumes "P is RH" "Q is RH"
  shows "`P \<or> Q` is RH"
using assms
by(utp_poly_auto_tac)

(* L8 closure-cond-R *)

lemma RH_CondR_closure:
  assumes "P is RH" "Q is RH" "b is R2s"
  shows "`P \<lhd> b \<rhd> Q` is RH"
using assms
by(utp_poly_auto_tac)

(* L9 closure-sequence-R *)

lemma RH_SemiR_closure:
  assumes "P \<in> WF_RELATION" "Q\<in> WF_RELATION" "P is RH" "Q is RH"
  shows "`P ; Q` is RH"
by (metis R1_SemiR_closure R2_SemiR_closure R3_SemiR_closure RH_is_R1 RH_is_R2 RH_is_R3 R_intro assms(1) assms(2) assms(3) assms(4))

lemma tr_seq_eq:
  assumes "P is R1" "Q is R1" "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "`(P;Q) \<and> ($tr\<acute>=$tr)` = `(P \<and> ($tr\<acute>=$tr));(Q \<and> ($tr\<acute>=$tr))`"
proof-
have 4: "`($tr\<acute> = $tr)[$tr\<acute>\<acute>/tr\<acute>]` = `$tr\<acute>\<acute> = $tr`"
by(simp add:usubst typing defined closure) 
have 5: "`($tr\<acute> = $tr)[$tr\<acute>\<acute>/tr]` = `$tr\<acute> = $tr\<acute>\<acute>`"
by(simp add:usubst typing defined closure) 
  have "`(P \<and> ($tr\<acute>=$tr));(Q \<and> ($tr\<acute>=$tr))` = `\<exists> tr\<acute>\<acute> . (P \<and> ($tr\<acute> = $tr))[$tr\<acute>\<acute>/tr\<acute>] ; (Q \<and> ($tr\<acute> = $tr))[$tr\<acute>\<acute>/tr]`"
    by(subst SemiR_extract_variable_id[of "tr\<down>"],simp_all add:unrest closure assms typing erasure)
  also have "... = `\<exists> tr\<acute>\<acute> . (P[$tr\<acute>\<acute>/tr\<acute>] \<and> ($tr\<acute>\<acute> = $tr)) ; (Q[$tr\<acute>\<acute>/tr] \<and> ($tr\<acute> = $tr\<acute>\<acute>))`"
    by(subst 4[THEN sym], subst 5[THEN sym],simp add:usubst)
  also have "... = `\<exists> tr\<acute>\<acute> . (($tr\<acute>\<acute> = $tr) \<and> P[$tr\<acute>\<acute>/tr\<acute>]) ; (Q[$tr\<acute>\<acute>/tr] \<and> ($tr\<acute> = $tr\<acute>\<acute>))`"
    by(utp_poly_auto_tac)
  also have "... = `\<exists> tr\<acute>\<acute> . ($tr\<acute>\<acute> = $tr) \<and> (P[$tr\<acute>\<acute>/tr\<acute>] ; (Q[$tr\<acute>\<acute>/tr] \<and> ($tr\<acute> = $tr\<acute>\<acute>)))`"
    by(simp add: SemiR_AndP_left_DASHED typing defined closure unrest)
  also have "... = `\<exists> tr\<acute>\<acute> . ($tr\<acute>\<acute> = $tr) \<and> (P[$tr\<acute>\<acute>/tr\<acute>] ; Q[$tr\<acute>\<acute>/tr]) \<and> ($tr\<acute> = $tr\<acute>\<acute>)`"
    by(simp add: SemiR_AndP_right_UNDASHED typing defined closure unrest)
  finally have A: "`(P \<and> ($tr\<acute>=$tr));(Q \<and> ($tr\<acute>=$tr))` =  `\<exists> tr\<acute>\<acute> . (P[$tr\<acute>\<acute>/tr\<acute>] ; Q[$tr\<acute>\<acute>/tr]) \<and> ($tr\<acute>\<acute> = $tr) \<and> ($tr\<acute> = $tr\<acute>\<acute>)`"
    by utp_poly_auto_tac
have 1: "`($tr \<le> $tr\<acute>)[$tr\<acute>\<acute>/tr\<acute>]` = `$tr \<le> $tr\<acute>\<acute>`"
by(simp add:usubst typing defined closure) 
have 2: "`($tr \<le> $tr\<acute>)[$tr\<acute>\<acute>/tr]` = `$tr\<acute>\<acute> \<le> $tr\<acute>`"
by(simp add:usubst typing defined closure) 
have 3: "`($tr \<le> $tr\<acute>\<acute>) \<and> ($tr\<acute>\<acute> \<le> $tr\<acute>) \<and> ($tr\<acute> = $tr)` = `($tr\<acute>\<acute> = $tr) \<and> ($tr\<acute> = $tr\<acute>\<acute>)`" 
by(utp_poly_auto_tac)
have "`(P;Q) \<and> ($tr\<acute>=$tr)` = `R1(P);R1(Q) \<and> ($tr\<acute>=$tr)`"
    by (metis assms is_healthy_def)
  also have "... = `(\<exists> tr\<acute>\<acute> . (P[$tr\<acute>\<acute>/tr\<acute>] \<and> ($tr \<le> $tr\<acute>\<acute>)) ; (Q[$tr\<acute>\<acute>/tr] \<and> ($tr\<acute>\<acute> \<le> $tr\<acute>))) \<and> ($tr\<acute> = $tr)`"
    by(simp add:assms typing defined closure unrest SemiR_extract_variable_id[of "tr\<down>"] R1_def usubst erasure 1[THEN sym] 2[THEN sym])
  also have "... = `(\<exists> tr\<acute>\<acute> . (($tr \<le> $tr\<acute>\<acute>) \<and> P[$tr\<acute>\<acute>/tr\<acute>]) ; (Q[$tr\<acute>\<acute>/tr] \<and> ($tr\<acute>\<acute> \<le> $tr\<acute>))) \<and> ($tr\<acute> = $tr)`"
    by(metis AndP_comm)
  also have "... = `(\<exists> tr\<acute>\<acute> . ($tr \<le> $tr\<acute>\<acute>) \<and> (P[$tr\<acute>\<acute>/tr\<acute>] ; (Q[$tr\<acute>\<acute>/tr]\<and> ($tr\<acute>\<acute> \<le> $tr\<acute>)))) \<and> ($tr\<acute> = $tr)`"
    by(subst SemiR_AndP_left_DASHED, simp_all add:unrest typing defined closure)
  also have "... = `(\<exists> tr\<acute>\<acute> . ($tr \<le> $tr\<acute>\<acute>) \<and> (P[$tr\<acute>\<acute>/tr\<acute>] ; Q[$tr\<acute>\<acute>/tr])\<and> ($tr\<acute>\<acute> \<le> $tr\<acute>)) \<and> ($tr\<acute> = $tr)`"
    by(simp add:SemiR_AndP_left_DASHED SemiR_AndP_right_UNDASHED unrest typing defined closure)
  also have "... = `\<exists> tr\<acute>\<acute> . ($tr \<le> $tr\<acute>\<acute>) \<and> (P[$tr\<acute>\<acute>/tr\<acute>] ; Q[$tr\<acute>\<acute>/tr])\<and> ($tr\<acute>\<acute> \<le> $tr\<acute>) \<and> ($tr\<acute> = $tr)`"
   by(subst ExistsP_AndP_expand1, simp_all add:unrest typing defined AndP_assoc[THEN sym])
  also have "... =`\<exists> tr\<acute>\<acute> . (P[$tr\<acute>\<acute>/tr\<acute>] ; Q[$tr\<acute>\<acute>/tr])\<and> ($tr \<le> $tr\<acute>\<acute>) \<and> ($tr\<acute>\<acute> \<le> $tr\<acute>) \<and> ($tr\<acute> = $tr)`"
    by(utp_poly_auto_tac)
  finally have B: "`(P;Q) \<and> ($tr\<acute>=$tr)` = `\<exists> tr\<acute>\<acute>. P[$tr\<acute>\<acute>/tr\<acute>] ; Q[$tr\<acute>\<acute>/tr] \<and> ($tr\<acute>\<acute> = $tr) \<and> ($tr\<acute> = $tr\<acute>\<acute>)`" 
    by(simp add: 3)
show ?thesis
  by (metis A B)
qed



lemma grow:
  assumes "P \<in> REL" "P is R1" "NON_REL_VAR \<sharp> x"
  shows "`($tr^\<langle>x\<rangle> = $tr\<acute>);P`= `(($tr^\<langle>x\<rangle> = $tr\<acute>);P) \<and> ($tr < $tr\<acute>)`"
proof-
  have 1: "`($tr^\<langle>x\<rangle> = $tr\<acute>)` is R1"
    by(simp add:is_healthy_def R1_def tr_prefix_app)
  have 0: "`(($tr ^ \<langle>x\<rangle> = $tr\<acute>) ; P) \<and> ($tr = $tr\<acute>)` = `false`"
proof - have "`(($tr ^ \<langle>x\<rangle> = $tr\<acute>) ; P) \<and> ($tr = $tr\<acute>)` =`(($tr ^ \<langle>x\<rangle> = $tr\<acute>) ; P) \<and> ($tr\<acute> = $tr)`"
by(simp add:PEqualP_sym)
also have "... =  ` ((($tr ^ \<langle>x\<rangle> = $tr\<acute>) \<and> ($tr\<acute> = $tr)) ; (P \<and> ($tr\<acute> = $tr)))`"
by(simp add: tr_seq_eq assms closure 1)
finally show ?thesis by utp_poly_auto_tac qed
  have "`($tr^\<langle>x\<rangle> = $tr\<acute>);P` = `R1(($tr^\<langle>x\<rangle> = $tr\<acute>);P)`"
     by(metis 1 is_healthy_def R1_SemiR_closure assms)   
  also have "... = `($tr ^ \<langle>x\<rangle> = $tr\<acute>) ; P \<and> (($tr < $tr\<acute>) \<or> ($tr = $tr\<acute>))`"
    by(simp add:R1_def Leq_alt)
  also have "... = `($tr ^ \<langle>x\<rangle> = $tr\<acute>) ; P \<and> ($tr < $tr\<acute>)`"
    by(simp add:AndP_OrP_distl 0)
finally show ?thesis .
qed

lemma Seq_tr_preserve:
  fixes P :: "'m upred"
  assumes "P \<in> REL" "Q \<in> REL" "`$tr < $tr\<acute>` \<sqsubseteq> P" "Q is R1"
  shows "`(P ; Q)[$tr/tr\<acute>]` = `false`"
proof -  
  have "`(P ; Q)[$tr/tr\<acute>]` = `((P \<and> ($tr < $tr\<acute>)) ; (Q \<and> ($tr \<le> $tr\<acute>)))[$tr/tr\<acute>]`"
      by (metis AndP_comm R1_def RefP_AndP assms is_healthy_def)
  also have "... = `(\<exists> tr\<acute>\<acute>. ((($tr < $tr\<acute>\<acute>) \<and> P[$tr\<acute>\<acute>/tr\<acute>]); (Q[$tr\<acute>\<acute>/tr] \<and> ($tr\<acute>\<acute> \<le> $tr\<acute>))))[$tr/tr\<acute>]`"
    by (simp add: SemiR_extract_variable_ty[of "tr" "tr\<acute>\<acute>"] AndP_comm assms closure typing defined unrest usubst)
  also have "... = `(\<exists> tr\<acute>\<acute>. (($tr < $tr\<acute>\<acute>) \<and> (P[$tr\<acute>\<acute>/tr\<acute>]; Q[$tr\<acute>\<acute>/tr]) \<and> ($tr\<acute>\<acute> \<le> $tr\<acute>)))[$tr/tr\<acute>]`"
    by (simp add: SemiR_AndP_left_DASHED SemiR_AndP_right_UNDASHED AndP_assoc typing defined unrest closure)
  also have "... = `\<exists> tr\<acute>\<acute>. (($tr < $tr\<acute>\<acute>) \<and> (P[$tr\<acute>\<acute>/tr\<acute>]; Q[$tr\<acute>\<acute>/tr])[$tr/tr\<acute>] \<and> ($tr\<acute>\<acute> \<le> $tr))`"
    by (utp_subst_tac)
  also have "... = `false`"
  proof -
    have "`($tr < $tr\<acute>\<acute>) \<and> ($tr\<acute>\<acute> \<le> $tr)` = (`false` :: 'm upred)"
      by (utp_poly_auto_tac)
    thus ?thesis
      by (simp add: AndP_assoc AndP_comm unrest, metis UNREST_FalseP UNREST_as_ExistsP)
  qed
  finally show ?thesis .
qed

end