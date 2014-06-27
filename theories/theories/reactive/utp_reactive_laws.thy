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
  assumes "P is RH" "P \<in> WF_RELATION"
  shows " `II ; P` = P"
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
  assumes "P is R1" "Q is R1" "P \<in> REL" "Q \<in> REL"
  shows "`(P;Q) \<and> ($tr\<acute>=$tr)` = `(P \<and> ($tr\<acute>=$tr));(Q \<and> ($tr\<acute>=$tr))`"
proof-
have 0: "P = R1(P)" "Q = R1(Q)" by (metis assms is_healthy_def)+
have 1: "`($tr \<le> $tr\<acute>)[$tr\<acute>\<acute>/tr\<acute>]` = `$tr \<le> $tr\<acute>\<acute>`" 
apply(subst usubst) defer 
apply(subst usubst)
apply(subst usubst) defer defer 
apply(subst usubst) back back
apply(simp_all add:typing closure defined)
done
have 2: "`($tr \<le> $tr\<acute>)[$tr\<acute>\<acute>/tr]` = `$tr\<acute>\<acute> \<le> $tr\<acute>`" 
apply(subst usubst) defer 
apply(subst usubst)
apply(subst usubst) back defer defer 
apply(subst usubst) back back
apply(simp_all add:typing closure defined)
done
have 3: "`($tr \<le> $tr\<acute>\<acute>) \<and> ($tr\<acute>\<acute> \<le> $tr\<acute>) \<and> ($tr\<acute> = $tr)` = `($tr\<acute>\<acute> = $tr) \<and> ($tr\<acute> = $tr\<acute>\<acute>)`" 
by(utp_poly_auto_tac)
have 4: "`($tr\<acute> = $tr)[$tr\<acute>\<acute>/tr\<acute>]` = `$tr\<acute>\<acute> = $tr`" 
apply(subst usubst) defer 
apply(subst usubst)
apply(subst usubst) back defer defer 
apply(subst usubst) back back
apply(simp_all add:typing closure defined)
done
have 5: "`($tr\<acute> = $tr)[$tr\<acute>\<acute>/tr]` = `$tr\<acute> = $tr\<acute>\<acute>`" 
apply(subst usubst) defer 
apply(subst usubst)
apply(subst usubst) defer defer 
apply(subst usubst) back back
apply(simp_all add:typing closure defined)
done
have "`(P;Q) \<and> ($tr\<acute>=$tr)` = 
      `(\<exists> tr\<acute>\<acute> . (P[$tr\<acute>\<acute>/tr\<acute>] \<and> ($tr \<le> $tr\<acute>\<acute>)) ; (Q[$tr\<acute>\<acute>/tr] \<and> ($tr\<acute>\<acute> \<le> $tr\<acute>))) \<and> ($tr\<acute> = $tr)`"
apply(subst 0,subst 0(2))
apply(simp add: R1_def)
apply(subst SemiR_extract_variable_id[of "tr\<down>"],simp_all add:typing closure defined unrest assms)
apply(simp add:usubst typing defined closure)
apply(subst 1[THEN sym],subst 2[THEN sym],simp add:erasure typing closure defined)
done
also have "... = `(\<exists> tr\<acute>\<acute> . (($tr\<acute>\<acute> = $tr) \<and> P[$tr\<acute>\<acute>/tr\<acute>]) ; (Q[$tr\<acute>\<acute>/tr] \<and> ($tr\<acute> = $tr\<acute>\<acute>)))` "
apply(subst SemiR_AndP_right_UNDASHED,simp add:typing closure defined unrest)
apply(subst AndP_comm)
apply(subst SemiR_AndP_left_DASHED,simp add:typing closure defined unrest)
apply(subst AndP_comm)
apply(subst ExistsP_AndP_expand1,simp_all add:AndP_assoc[THEN sym] typing defined closure unrest)
apply(subst 3,simp add:AndP_assoc)
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym])
apply(subst SemiR_AndP_right_UNDASHED,simp add:typing closure defined unrest)
apply(subst SemiR_AndP_left_DASHED,simp_all add:typing closure defined unrest AndP_assoc[THEN sym])
done
also have "... = `(($tr\<acute>=$tr) \<and> P);(Q \<and> ($tr\<acute>=$tr))` "
apply(subst 4[THEN sym],subst 5[THEN sym],simp add:SubstP_AndP[THEN sym])
apply(subst SemiR_extract_variable_id[of "tr\<down>"],simp_all add:typing defined closure unrest assms) back
apply(simp add:typing closure defined erasure)
done
finally show ?thesis
by (metis AndP_comm)
qed

lemma grow:
  assumes "P \<in> REL" "P is R1" "NON_REL_VAR \<sharp> x"
  shows "`($tr^\<langle>x\<rangle> = $tr\<acute>);P`= `(($tr^\<langle>x\<rangle> = $tr\<acute>);P) \<and> ($tr < $tr\<acute>)`"
proof-
have 0: "`($tr^\<langle>x\<rangle> = $tr\<acute>);P` is R1"
apply(subst R1_SemiR_closure)
apply(simp_all add:closure assms)
apply(simp add:R1_def is_healthy_def)
apply (metis tr_prefix_app)
done
have 1: "`($tr^\<langle>x\<rangle>=$tr\<acute>) \<and> ($tr\<acute>=$tr)` = `false`"
by(utp_poly_auto_tac)
have 2: "`(($tr^\<langle>x\<rangle> = $tr\<acute>);P) \<and> ($tr\<acute>=$tr)`= `false`"
apply(subst tr_seq_eq,simp_all add:assms closure)
apply(simp add:R1_def is_healthy_def)
apply (metis tr_prefix_app)
apply(simp add: 1)
done
from 0 have "`($tr^\<langle>x\<rangle> = $tr\<acute>);P`= `(($tr^\<langle>x\<rangle> = $tr\<acute>);P) \<and> ($tr \<le> $tr\<acute>)`"
by(simp add:is_healthy_def R1_def)
also have "... = `(($tr^\<langle>x\<rangle> = $tr\<acute>);P) \<and> (($tr < $tr\<acute>) \<or> ($tr\<acute> = $tr))`"
by (metis Leq_alt PEqualP_sym)
also have "... = ` (($tr ^ \<langle>x\<rangle> = $tr\<acute>) ; P) \<and> ($tr < $tr\<acute>)`"
by(simp add: AndP_OrP_distl 2)
finally show ?thesis .
qed

lemma Seq_tr_pres:
  assumes "P \<in> REL" "P is R1" "Q \<in> REL" "Q is R1"
  shows "`(P;Q)[$tr/tr\<acute>]` = `P[$tr/tr\<acute>];(Q[$tr/tr\<acute>])`"
proof-
have 0: "`P;Q` = `\<exists> tr\<acute>\<acute>. (P[$tr\<acute>\<acute>/tr\<acute>];Q[$tr\<acute>\<acute>/tr]) \<and> ($tr\<le> $tr\<acute>\<acute>) \<and> ($tr\<acute>\<acute> \<le> $tr\<acute>)`"
proof-
from assms have "`P;Q` = `R1(P);R1(Q)`" by (metis is_healthy_def)
also have "... = `\<exists> tr\<acute>\<acute>. (P[$tr\<acute>\<acute>/tr\<acute>];Q[$tr\<acute>\<acute>/tr]) \<and> ($tr\<le> $tr\<acute>\<acute>) \<and> ($tr\<acute>\<acute> \<le> $tr\<acute>)`"
apply(subst SemiR_extract_variable_ty[of "tr" "tr\<acute>\<acute>"],simp_all add:typing defined closure unrest assms)
apply(simp add:R1_def usubst typing defined closure)
apply(subst SemiR_AndP_right_UNDASHED,simp add:typing closure defined unrest)
apply(subst AndP_comm)
apply(subst SemiR_AndP_left_DASHED,simp add:typing closure defined unrest)
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym])
done
finally show ?thesis .
qed
have "`(P;Q)[$tr/tr\<acute>]` = `(\<exists> tr\<acute>\<acute> . (P[$tr\<acute>\<acute>/tr\<acute>] ; Q[$tr\<acute>\<acute>/tr])[$tr/tr\<acute>] \<and> ($tr\<acute>\<acute> = $tr))`"
apply(subst 0,simp add:usubst typing defined closure)
apply(subst SubstP_ExistsP,simp add:typing defined closure unrest)
apply(utp_poly_auto_tac)
apply(simp add:usubst typing defined closure)
apply(subst tr_leq_ident,simp)
done
also have "... =`(P[$tr\<acute>\<acute>/tr\<acute>] ; Q[$tr\<acute>\<acute>/tr][$tr\<acute>\<acute>/tr\<acute>])[$tr/tr\<acute>\<acute>]`"
apply(subst SubstP_EqualP_swap)
apply(subst ExistsP_one_point_ty,simp_all add:typing defined closure unrest)
apply(subst SubstP_SemiR_right,simp_all add:typing defined closure unrest)
done
also have "... = `P[$tr/tr\<acute>] ; (Q[$tr/tr][$tr/tr\<acute>])`"
apply(subst usubst,simp add:typing closure defined) defer
apply(subst SubstP_twice_2) defer
apply(subst SubstP_twice_3,simp_all add:typing closure defined unrest) back
apply(subst SubstP_twice_2) defer
apply(simp add:usubst typing defined closure)
apply(simp_all add:typing defined closure assms unrest)
sorry
finally show ?thesis
by(subst SubstP_ident[of "Q" "tr",THEN sym],simp)
qed

end