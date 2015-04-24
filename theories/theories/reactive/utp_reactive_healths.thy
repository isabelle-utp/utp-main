(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_reactive.thy                                                     *)
(* Authors: Simon Foster and Samuel Canham, University of York                *)
(******************************************************************************)

header {* Healthiness Conditions for Reactive Processes *}

theory utp_reactive_healths
imports 
  utp_reactive_lemmas
begin

text {* R1 ensures that the trace only gets longer *}

definition R1 :: "'a upred \<Rightarrow> 'a upred" where
"R1(P) = `P \<and> ($tr \<le> $tr\<acute>)`"

text {* R2s ensures that processes are independent of the history of the trace  *}

definition R2s :: "'a upred \<Rightarrow> 'a upred" where
"R2s(P) = `P[\<langle>\<rangle> / tr][($tr\<acute> - $tr) / tr\<acute>]`"

text{* R2 is the composition of R1 and R2s *}

definition R2 :: "'a upred \<Rightarrow> 'a upred" where
"R2(P) = R1 (R2s P)"

text {* R3 enforces that processes do nothing while waiting to start *}

definition R3 :: "'a upred \<Rightarrow> 'a upred" where
"R3(P) = `II \<lhd> $wait \<rhd> P`"

declare R1_def [eval, evalr, evalrr, evalrx, evalpp, evalpr]
declare R2_def [eval, evalr, evalrr, evalrx, evalpp, evalpr]
declare R2s_def [eval, evalr, evalrr, evalrx, evalpp, evalpr]
declare R3_def [eval, evalr, evalrr, evalrx, evalpp, evalpr]
declare is_healthy_def [eval, evalr, evalrr, evalrx, evalpp, evalpr]

subsection {* Closure Laws *}

lemma R1_rel_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> R1(P) \<in> WF_RELATION"
  by (simp add:R1_def closure unrest WF_RELATION_UNREST)

lemma R2s_rel_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> R2s(P) \<in> WF_RELATION"
  by (simp add:R2s_def unrest typing defined closure)

lemma R2_rel_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> R2(P) \<in> WF_RELATION"
  by (simp add:R2_def closure)

lemma R3_rel_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> R3(P) \<in> WF_RELATION"
  by (simp add:R3_def closure)

subsection {* R1 Laws *}

lemma R1_monotonic: "P \<sqsubseteq> Q \<Longrightarrow> R1(P) \<sqsubseteq> R1(Q)" 
  by utp_pred_tac

(* L1 R1-idempotent *)

lemma R1_idempotent:
  "R1(R1(P)) = R1(P)"
  by (utp_rel_tac)

(* L2 R1-\<and> *)

lemma R1_AndP:
  "`R1(P \<and> Q)` = `R1(P) \<and> R1(Q)`"
  by (utp_pred_auto_tac)

(* L3 R1-\<or> *)

lemma R1_OrP:
  "`R1(P \<or> Q)` = `R1(P) \<or> R1(Q)`"
  by (utp_pred_auto_tac)
  
(* L4 R1-extend-\<and> *)

lemma R1_extend_AndP : 
  "`R1(P) \<and> Q` = `R1(P \<and> Q)`"
  by (utp_pred_auto_tac)

(* L5 R1-conditional *)

lemma R1_CondR:
  "`R1(P \<lhd> b \<rhd> Q)` = `R1(P) \<lhd> b \<rhd> R1(Q)`"
  by (utp_pred_auto_tac)

(* L6 R1-negate-R1 *)

lemma R1_negate_R1: 
  "`R1(\<not>R1(P))` = `R1(\<not>P)`"
  by(utp_pred_auto_tac)
  
(* L7 R1-wait *)

lemma R1_wait_true: 
  "(R1(P))\<^sub>t = R1(P \<^sub>t)"
by( utp_poly_auto_tac)

lemma R1_wait_false: 
  "(R1(P))\<^sub>f = R1(P \<^sub>f)"
by(utp_poly_auto_tac)

(* L8 II_rel-R1 *)

lemma R1_SkipR:
  "R1(II) = II"
  by (auto simp add:eval evalp closure Rep_binding_ty_def)

lemma R1_SkipR_closure [closure]:
  "II is R1"
  by (metis Healthy_intro R1_SkipR)

(* L10 R1-\<and>-closure *)

lemma R1_AndP_closure: 
assumes "P is R1" "Q is R1"
shows "`(P \<and> Q)` is R1"
by (metis Healthy_intro Healthy_simp R1_extend_AndP assms(1))

(* L11 R1-\<or>-closure *)

lemma R1_OrP_closure: 
assumes "P is R1" "Q is R1"
shows "`(P \<or> Q)` is R1"
by (metis R1_OrP assms(1) assms(2) is_healthy_def)

(* L12 R1-conditional-closure *)

lemma R1_CondR_closure [closure]: 
assumes "P is R1" "Q is R1"
shows "`(P \<lhd> b \<rhd> Q)` is R1"
by (metis Healthy_intro Healthy_simp R1_CondR assms(1) assms(2))

(* L9 II_rea-R1 *)

lemma R1_tr_leq_tr' [closure]:
  "`$tr \<le> $tr\<acute>` is R1"
  by (simp add:R1_def is_healthy_def)

(* L13 R10-sequence-closure *)

lemma R1_by_refinement:
  "P is R1 \<longleftrightarrow> `$tr \<le> $tr\<acute>` \<sqsubseteq> P" 
  by (utp_pred_auto_tac)

theorem R1_SemiR_closure [closure]:
  assumes
    "P is R1" "Q is R1"
  shows "(P ;\<^sub>R Q) is R1"
  using assms
  apply (unfold R1_by_refinement)
  apply (rule order_trans)
  apply (rule SemiR_mono_refine)
  apply (simp_all)
  apply (simp add:tr_leq_trans)
done

lemma R1_ok'_true: 
  "(R1(P))\<^sup>t = R1(P\<^sup>t)"
by(simp add:R1_def, utp_poly_auto_tac)

lemma R1_ok_true: 
  "`(R1(P))[true/ok]` = `R1(P[true/ok])`"
by(simp add:R1_def, utp_poly_auto_tac)

lemma R1_ok'_false: 
  "(R1(P))\<^sup>f = R1(P\<^sup>f)"
by(simp add:R1_def, utp_poly_auto_tac)

lemma R1_NotP_R1: "`R1(\<not>R1(P))` = `R1(\<not>P)`"
by(utp_poly_auto_tac)

lemma SemiR_R1_true_right: "`(x;($tr\<le>$tr\<acute>)) \<or> x` = `x;($tr\<le>$tr\<acute>)`"
proof-
  have "`(x;($tr\<le>$tr\<acute>)) \<or> x` = `(x;($tr\<le>$tr\<acute>)) \<or> x;II`"
    by simp
  also have "... = `x;(($tr\<le>$tr\<acute>) \<or> II)`"
    by (metis SemiR_OrP_distl)
  also have "... = `x;($tr\<le>$tr\<acute>)`"
    by (metis R1_SkipR_closure R1_by_refinement RefP_OrP)
  finally show ?thesis .
qed

subsection {* R2 Laws *}

(* L3 R2-idempotent *)

lemma R2s_idempotent: "`R2s(R2s(P))` = `R2s(P)`"
  apply (simp add:R2s_def)
  apply (subst SubstP_twice_2, simp_all add:unrest typing defined closure)
  apply (simp add:usubst typing defined closure)
done

declare UTypedef.InjU_inverse [evalp]

lemma R2s_destroys_R1: "R2s (R1 P) = R2s P" 
  by (utp_poly_tac)

lemma R2_idempotent: "`R2(R2(P))` = `R2(P)`" 
  by (simp add:R2_def R2s_destroys_R1 R2s_idempotent)

(* L4 R2-\<and>-closure *)

lemma R2s_AndP: 
  "`R2s(P \<and> Q)` = `R2s(P) \<and> R2s(Q)`" 
  by (utp_pred_auto_tac)

lemma R2_AndP: "`R2(P \<and> Q)` = `R2(P) \<and> R2(Q)`"
  by (utp_pred_auto_tac)

lemma R2_AndP_closure: 
assumes "P is R2" "Q is R2"
shows "`P \<and> Q` is R2"
  by (metis R2_AndP assms is_healthy_def)

(* L5 R2-\<or>-closure *)

lemma R2s_OrP: 
  "`R2s(A \<or> C)` = `R2s(A) \<or> R2s(C)`" 
  by (utp_pred_auto_tac)

lemma R2_OrP: "`R2(P \<or> Q)` = `R2(P) \<or> R2(Q)`"
  by (utp_pred_auto_tac)

lemma R2_OrP_closure: 
assumes "P is R2" "Q is R2"
shows "`P \<or> Q` is R2"
by (metis R2_OrP assms(1) assms(2) is_healthy_def)

(* L7 R2-cond-closure-2 *)

lemma R2s_CondR: 
  "`R2s(P \<lhd> b \<rhd> Q)` = `R2s(P) \<lhd> R2s(b) \<rhd> R2s(Q)`"
  by (utp_pred_auto_tac)

lemma R2_CondR: 
  "`R2(P \<lhd> b \<rhd> Q)` =`R2(P) \<lhd> R2s(b) \<rhd> R2(Q)`" 
  by (utp_pred_auto_tac)

lemma R2_CondR_alt: 
  "`R2(P \<lhd> b \<rhd> Q)` =`R2(P) \<lhd> R2(b) \<rhd> R2(Q)`" 
  by (utp_pred_auto_tac)

lemma R2_negate: 
  "`R2(\<not> b)` = `R1(\<not>R2(b))`"
by(utp_pred_auto_tac)

lemma R2_CondR_closure:
  assumes "P is R2" "Q is R2" "b is R2s"
  shows "`P \<lhd> b \<rhd> Q` is R2"
by(metis assms is_healthy_def R2_CondR)

lemma R2_CondR_closure_2: 
assumes "P is R2" "Q is R2" "b is R2"
shows "`P \<lhd> b \<rhd> Q` is R2"
using assms
by(utp_poly_auto_tac)

(* L6 R2-cond-closure-1 *)

lemma tr_conserved_is_R2 : "`R2($tr\<acute> = $tr)` = `($tr\<acute> = $tr)`"
  by(simp add:R2_def R2s_def R1_def usubst typing defined closure tr_prefix_as_nil)

lemma R2_CondR_closure_1: 
assumes "P is R2" "Q is R2"
shows "`P \<lhd> ($tr\<acute> = $tr) \<rhd> Q` is R2"
by(subst R2_CondR_closure_2, simp_all add:assms, simp add:is_healthy_def tr_conserved_is_R2)

lemma SS1_UNREST_d3 [unrest]:
  "P \<in> WF_RELATION \<Longrightarrow> {x\<acute>\<acute>\<acute>} \<sharp> (SS1\<bullet>P)"
  apply (rule UNREST_RenameP[of "{x\<acute>\<acute>\<acute>}"])
  apply (simp_all add:unrest urename)
done

lemma SS2_UNREST_d3 [unrest]:
  "P \<in> WF_RELATION \<Longrightarrow> {x\<acute>\<acute>\<acute>} \<sharp> (SS2\<bullet>P)"
  apply (rule UNREST_RenameP[of "{x\<acute>\<acute>\<acute>}"])
  apply (simp_all add:unrest urename)
done

(* L9 R2-composition *)

abbreviation "tt1   \<equiv> MkPlainP ''tt1'' True TYPE('m event ULIST) TYPE('m)"
abbreviation "tt2   \<equiv> MkPlainP ''tt2'' True TYPE('m event ULIST) TYPE('m)"
abbreviation "tt   \<equiv> MkPlainP ''tt'' True TYPE('m event ULIST) TYPE('m)"

lemma R2_form:
  assumes "{ttx\<down>\<acute>\<acute>} \<sharp> P" "pvaux ttx" 
  shows "R2(P) = (\<exists>\<^sub>p {ttx\<down>\<acute>\<acute>} . `P[\<langle>\<rangle>/tr][$ttx\<acute>\<acute>/tr\<acute>] \<and> ($tr\<acute> = $tr ^ $ttx\<acute>\<acute>)`)"
proof -
  have "`$tr \<le> $tr\<acute>` = (\<exists>\<^sub>p {ttx\<down>\<acute>\<acute>} . `$tr\<acute> = $tr ^ $ttx\<acute>\<acute>`)"
    by (metis (hide_lams, no_types) PVAR_VAR_pvdash assms tr_prefix_as_concat)
  hence "R2(P) = R2s(P) \<and>\<^sub>p (\<exists>\<^sub>p {ttx\<down>\<acute>\<acute>} .  `$tr\<acute> = $tr ^ $ttx\<acute>\<acute>`)"
    by(metis R2_def R1_def)
  also have "... = (\<exists>\<^sub>p {ttx\<down>\<acute>\<acute>} . R2s(P) \<and>\<^sub>p `$tr\<acute> = $tr ^ $ttx\<acute>\<acute>`)"
    apply (subst ExistsP_AndP_expand2)
    apply (simp add:R2s_def)
    apply (simp_all add:unrest typing closure assms)
  done  
  also have "... = (\<exists>\<^sub>p {ttx\<down>\<acute>\<acute>} . `$tr\<acute> = $tr ^ $ttx\<acute>\<acute> \<and> R2s(P)`)"
    by (subst AndP_comm, simp)
  also have  "... = (\<exists>\<^sub>p {ttx\<down>\<acute>\<acute>} . `R2s(P)[($tr ^ $ttx\<acute>\<acute>)/tr\<acute>] \<and> $tr\<acute> = $tr ^ $ttx\<acute>\<acute>`)"
    apply(simp add:erasure typing defined closure)
    apply(subst EqualP_SubstP)
    apply(simp_all add: typing defined closure assms AndP_comm)
  done
  also have "... = (\<exists>\<^sub>p {ttx\<down>\<acute>\<acute>} . `P[\<langle>\<rangle>/tr][$ttx\<acute>\<acute>/tr\<acute>] \<and> ($tr\<acute> = $tr ^ $ttx\<acute>\<acute>)`)" 
    apply(simp add:R2s_def)
    apply(subst SubstP_twice_1)
    apply(simp add:usubst typing defined closure assms)
    apply(subst app_minus)
    apply(simp_all add:typing closure)
  done 
  finally show ?thesis 
    by (metis assms(1))
qed


thm SubstP_UNREST_OKAY
thm SubstE_VarE_single_UNREST
thm SubstP_twice_3

(* FIXMES: SubstP_twice_3 seems not to be safe with the above.
   
   Remove from simpset (Frank Zeyda).
*)

lemma R2_SemiR_form: 
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "R2(P) ;\<^sub>R R2(Q) =  `(\<exists> tt1\<acute>\<acute>. \<exists> tt2\<acute>\<acute>.  P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>/tr\<acute>] ; Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>/tr\<acute>] \<and> ($tr\<acute> = $tr ^ $tt1\<acute>\<acute> ^ $tt2\<acute>\<acute>))`"
proof -
    have "R2(P) ;\<^sub>R R2(Q) = `( \<exists> tr \<acute>\<acute> . 
      (\<exists> tt1\<acute>\<acute> . (P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>/tr\<acute>] \<and> ($tr\<acute>\<acute> = $tr ^ $tt1\<acute>\<acute>)));
      (\<exists> tt2\<acute>\<acute> . (Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>/tr\<acute>] \<and> ($tr\<acute> = $tr\<acute>\<acute> ^ $tt2\<acute>\<acute>)))
     )`"
        apply(simp add: SemiR_extract_variable_id_ty[of "tr"] closure assms typing unrest)
        apply(subst R2_form[of "tt1"])
        apply(simp_all add:closure assms unrest)
        apply(subst R2_form[of "tt2"])
        apply(simp_all add:closure assms unrest)
        apply(subst SubstP_ExistsP)
        apply(simp_all add:closure typing defined unrest)
        apply(simp add:usubst typing defined assms)
        apply(subst SubstP_ExistsP)
        apply(simp_all add: closure typing defined unrest)
        apply(simp add: usubst typing defined assms unrest del: SubstP_twice_3)
(* Adding del: SubstP_twice_3 the following seems not necessary anymore. Bad design. *)
(*
        apply(simp add: SubstE_PSubstPE SubstE_PSubstPE_dash PSubstPE_Op2PE PSubstPE_PVarPE PSubstPE_PVarPE_different closure typing defined)
        apply(subst SubstP_twice_2) back back
        apply(simp add:typing defined closure assms unrest)
        apply(subst SubstE_PSubstPE)
        apply(simp_all add:typing closure defined usubst)
*)
     done

  also have "... = `(\<exists> tt1\<acute>\<acute>. \<exists> tt2\<acute>\<acute>. \<exists> tr\<acute>\<acute>. ($tr\<acute>\<acute> = $tr ^ $tt1\<acute>\<acute>) \<and> P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>/tr\<acute>] ; Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>/tr\<acute>] \<and> ($tr\<acute> = $tr\<acute>\<acute> ^ $tt2\<acute>\<acute>))`"
    apply (subst ExistsP_SemiR_NON_REL_VAR_expand2)
    apply (simp add:unrest typing closure assms)
    apply (simp add:closure)
    apply (subst ExistsP_SemiR_NON_REL_VAR_expand1)
    apply (simp add:unrest typing closure assms)
    apply (simp add:closure)
    apply (subst AndP_comm)
    apply (subst SemiR_AndP_left_DASHED)
    apply (simp add:unrest typing defined closure assms)
    apply (subst SemiR_AndP_right_UNDASHED)
    apply (simp add:unrest typing defined closure assms)
    apply (metis (lifting, no_types) ExistsP_norm_test)
  done

  also have "... = `(\<exists> tt1\<acute>\<acute>. \<exists> tt2\<acute>\<acute>.  P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>/tr\<acute>] ; Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>/tr\<acute>] \<and> (\<exists> tr\<acute>\<acute>. ($tr\<acute> = $tr\<acute>\<acute> ^ $tt2\<acute>\<acute>) \<and> ($tr\<acute>\<acute> = $tr ^ $tt1\<acute>\<acute>)))`"
    apply (subst AndP_comm)
    apply (subst AndP_assoc[THEN sym])
    apply (subst ExistsP_AndP_expand2)
    apply (simp_all add:unrest typing defined closure assms)
  done

  also have "... = `(\<exists> tt1\<acute>\<acute>. \<exists> tt2\<acute>\<acute>.  P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>/tr\<acute>] ; Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>/tr\<acute>] \<and> ($tr\<acute> = $tr ^ $tt1\<acute>\<acute> ^ $tt2\<acute>\<acute>))`"
    proof -
      have  "`(\<exists> tr\<acute>\<acute>. ($tr\<acute> = $tr\<acute>\<acute> ^ $tt2\<acute>\<acute>) \<and> ($tr\<acute>\<acute> = $tr ^ $tt1\<acute>\<acute>))` = `($tr\<acute> = $tr ^ $tt1\<acute>\<acute> ^ $tt2\<acute>\<acute>)`" 
        apply(simp add:erasure typing defined closure)
        apply(subst ExistsP_one_point)
        apply(simp_all add:unrest typing defined closure)
        apply(subst SubstP_EqualP)
        apply(simp add:usubst typing defined closure append_assoc)
      done
      thus ?thesis 
        by metis
    qed
  finally show ?thesis by this
qed

lemma R2_SemiR_distribute:
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "R2(R2(P) ;\<^sub>R R2(Q)) = R2(P) ;\<^sub>R R2(Q)"
proof-
  have "R2(R2(P) ;\<^sub>R R2(Q)) =  `(\<exists> tt1\<acute>\<acute>. \<exists> tt2\<acute>\<acute> . \<exists> tt\<acute>\<acute>. P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>/tr\<acute>] ; Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>/tr\<acute>] \<and> ($tt\<acute>\<acute> = $tt1\<acute>\<acute> ^ $tt2\<acute>\<acute>) \<and> ($tr\<acute> = $tr ^ $tt\<acute>\<acute>))`"
     apply(subst R2_form[of "tt"])
     apply(simp_all add:closure assms typing defined unrest)
     apply(subst R2_SemiR_form)
     apply(simp_all add: assms)
     apply(subst SubstP_ExistsP)
     apply(simp_all add:unrest closure typing defined)
     apply(subst SubstP_ExistsP)
     apply(simp_all add:unrest closure typing defined)
     apply(subst SubstP_AndP)
     apply(subst SubstP_SemiR_left)
     apply(simp_all add:unrest closure typing defined)
     apply(subst SubstP_twice_2) back
     apply(simp_all add:unrest closure typing defined)
     apply(subst SubstP_ExistsP)
     apply(simp_all add:unrest closure typing defined)
     apply(subst SubstP_ExistsP)
     apply(simp_all add:unrest closure typing defined)
     apply(subst SubstP_AndP)
     apply(subst SubstP_SemiR_right)
     apply(simp_all add:unrest closure typing defined)
     apply(subst SubstP_twice_1)
     apply(simp add:usubst typing defined closure)
     apply(subst ExistsP_AndP_expand1)
     apply(simp add:unrest closure typing defined)
     apply(subst ExistsP_AndP_expand1)
     apply(simp add:unrest closure typing defined)
     apply(subst AndP_assoc[THEN sym])
     apply(simp add: ExistsP_union[THEN sym])
     apply (metis insert_commute)
   done
   also have "... = `(\<exists> tt1\<acute>\<acute>. \<exists> tt2\<acute>\<acute>. P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>/tr\<acute>] ; Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>/tr\<acute>] \<and> (\<exists> tt\<acute>\<acute>. ($tt\<acute>\<acute> = $tt1\<acute>\<acute> ^ $tt2\<acute>\<acute>) \<and> ($tr\<acute> = $tr ^ $tt\<acute>\<acute>)))`"
     apply(subst ExistsP_AndP_expand2[THEN sym])
     apply(simp_all add:unrest closure typing defined assms)
   done
   also have "... = `(\<exists> tt1\<acute>\<acute> . \<exists> tt2\<acute>\<acute> . P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>/tr\<acute>] ; Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>/tr\<acute>] \<and> ($tr\<acute> = $tr ^ $tt1\<acute>\<acute> ^ $tt2\<acute>\<acute>))`"
     apply(subst AndP_comm) back
     apply(subst ExistsP_one_point_ty[of _ "tt\<acute>\<acute>"])
     apply(simp_all add: typing defined closure)
     apply(simp add:closure typing defined unrest erasure)
     apply(simp add:usubst typing defined closure)
   done 

   also have "... = R2(P);\<^sub>RR2(Q)" 
     by (subst R2_SemiR_form, simp_all add:assms)

   finally show ?thesis .
qed

lemma R2_SemiR_closure: 
  assumes "P is R2" "Q is R2" "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "P ;\<^sub>R Q is R2"
  by (metis Healthy_intro Healthy_simp R2_SemiR_distribute assms)

declare SubstP_UNREST [usubst del]
declare SubstP_VarP_single_UNREST[usubst del]
declare SubstE_VarE_single_UNREST[usubst del]
declare SubstP_VarP_aux[usubst del]
declare SubstP_UNREST_OKAY[usubst del]

declare PSubstPE_VarP_single_UNREST[usubst del]

declare EvalP_SemiR [evalp]

lemma UNREST_R2 [unrest]:
  "\<lbrakk> xs \<sharp> P; tr\<down> \<notin> xs; tr\<down>\<acute> \<notin> xs \<rbrakk> \<Longrightarrow> xs \<sharp> R2(P)"
  by (simp add:R2_def R2s_def R1_def unrest typing closure)

lemma R2_SemiR_distribute':
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "R2(R2(P) ;\<^sub>R R2(Q)) = R2(P ;\<^sub>R R2(Q))"
proof -
  have "R2(R2(P) ;\<^sub>R R2(Q)) =
        `(\<exists> tt\<acute>\<acute>. (\<exists> tt1\<acute>\<acute>. \<exists> tt2\<acute>\<acute>. (P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>/tr\<acute>] ; Q [\<langle>\<rangle>/tr][$tt2\<acute>\<acute>/tr\<acute>])
                                   \<and> $tt\<acute>\<acute> = ($tt1\<acute>\<acute> ^ $tt2\<acute>\<acute>))
                 \<and> $tr\<acute> = ($tr ^ $tt\<acute>\<acute>))`"
    apply (simp add: R2_SemiR_form assms)
    apply (subst R2_form[of "tt"])
    apply (simp_all add:unrest assms typing closure)
    apply (simp add:SubstP_ExistsP unrest typing closure assms)
    apply (simp add:usubst typing defined assms closure)
    apply (subst SubstP_SemiR_left)
    apply (simp_all add:closure typing unrest)
    apply (subst SubstP_SemiR_right)
    apply (simp_all add:closure typing unrest)
    apply (simp add:usubst typing defined closure)
    apply (subst SubstP_twice_3) back
    apply (simp_all add:unrest typing closure)
    apply (simp add:usubst typing closure defined)
  done

  also 
  have "... = `(\<exists> tt1\<acute>\<acute>. \<exists> tt2\<acute>\<acute>. 
                  ((P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>/tr\<acute>] ; Q [\<langle>\<rangle>/tr][$tt2\<acute>\<acute>/tr\<acute>])
                   \<and> (\<exists> tt\<acute>\<acute>. ($tt\<acute>\<acute> = ($tt1\<acute>\<acute> ^ $tt2\<acute>\<acute>) \<and> $tr\<acute> = ($tr ^ $tt\<acute>\<acute>)))))`"
    apply (subst ExistsP_AndP_expand1) 
    apply (simp add:unrest typing closure assms)
    apply (subst ExistsP_AndP_expand1) 
    apply (simp_all add:unrest typing closure assms)
    apply (subst ExistsP_commute)
    apply (subst ExistsP_commute) back
    apply (subst AndP_assoc[THEN sym])
    apply (subst ExistsP_AndP_expand2[THEN sym])
    apply (simp_all add:unrest typing defined closure assms)
  done

  also have "... = `(\<exists> tt1\<acute>\<acute>. \<exists> tt2\<acute>\<acute>. 
                     ((P[\<langle>\<rangle>/tr][$tt1\<acute>\<acute>/tr\<acute>] ; Q [\<langle>\<rangle>/tr][$tt2\<acute>\<acute>/tr\<acute>])
                      \<and> ($tr\<acute> = ($tr ^ ($tt1\<acute>\<acute> ^ $tt2\<acute>\<acute>)))))`"
  proof -
    have "`(\<exists> tt\<acute>\<acute>. ($tt\<acute>\<acute> = ($tt1\<acute>\<acute> ^ $tt2\<acute>\<acute>) \<and> $tr\<acute> = ($tr ^ $tt\<acute>\<acute>)))` = 
          (`($tr\<acute> = ($tr ^ ($tt1\<acute>\<acute> ^ $tt2\<acute>\<acute>)))` :: 'a upred)"
      apply (utp_poly_auto_tac)
      apply (metis AppendUL.rep_eq UTypedef.axm4 UTypedef_Event UTypedef_ULIST)
    done

    thus ?thesis by simp
  qed

  also have "... = `(\<exists> tt\<acute>\<acute>. (\<exists> tt2\<acute>\<acute>. (P[\<langle>\<rangle>/tr] ; (Q[\<langle>\<rangle>/tr][$tt2\<acute>\<acute>/tr\<acute>] \<and> $tt\<acute>\<acute> = $tr ^ $tt2\<acute>\<acute>)))
                                      \<and> $tr\<acute> = $tr ^ $tt\<acute>\<acute>)`"
  proof -
    have p1: "`\<exists> tt\<acute>\<acute>. (($tt\<acute>\<acute> = $tt1\<acute>\<acute> ^ $tt2\<acute>\<acute>) \<and> ($tr\<acute> = $tr ^ $tt\<acute>\<acute>))` =
                       (`$tr\<acute> = ($tr ^ $tt1\<acute>\<acute> ^ $tt2\<acute>\<acute>)` :: 'a upred)"
      apply (utp_poly_auto_tac)
      apply (metis AppendUL.rep_eq UTypedef.axm4 UTypedef_Event UTypedef_ULIST)
    done

    show ?thesis
      apply (subst SemiR_extract_variable_ty[of "tr" "tt1\<acute>\<acute>"]) back
      apply (simp_all add:typing closure assms unrest)
      apply (simp add:usubst typing defined closure)
      apply (subst SubstP_twice_3) back back back back 
      apply (simp_all add:unrest typing closure)
      apply (simp add:usubst typing defined closure assms)
      apply (subst AndP_comm)
      apply (subst SemiR_AndP_right_UNDASHED)
      apply (simp add:unrest typing closure)
      apply (subst ExistsP_AndP_expand1)
      apply (simp add:unrest typing closure)
      apply (subst ExistsP_AndP_expand1)
      apply (simp add:unrest typing closure)
      apply (subst AndP_assoc[THEN sym])
      apply (subst ExistsP_commute) back
      apply (subst ExistsP_commute) back back
      apply (subst ExistsP_AndP_expand2[THEN sym]) back
      apply (simp add:unrest typing closure assms)
      apply (simp add: p1[simplified])
      apply (subst AndP_comm) back
      apply (simp add:ExistsP_commute)
    done
  qed


  also have "... = R2(P ;\<^sub>R R2(Q))"
    apply (subst R2_form[of "tt"])
    apply (simp_all add:unrest assms typing closure)
    apply (subst R2_form[of "tt2"])
    apply (simp_all add:unrest assms typing closure)
    apply (subst SubstP_SemiR_left)
    apply (simp_all add:closure typing unrest)
    apply (subst SubstP_SemiR_right)
    apply (simp_all add:closure typing unrest)
    apply (simp add:SubstP_ExistsP unrest typing closure assms)
    apply (simp add:usubst typing defined assms closure)
    apply (subst ExistsP_SemiR_NON_REL_VAR_expand1)
    apply (simp add:unrest typing defined closure assms)
    apply (simp_all add:closure)
  done

  finally show ?thesis .
qed


lemma R2_sequential_composition: 
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "`R2(P) ; R2(Q)` = `R2(P ; R2(Q))`"
  by (metis R2_SemiR_distribute R2_SemiR_distribute' assms(1) assms(2))

   (* L10 R2-wait-okay' *)

lemma R2_wait_true: "(R2(P))\<^sub>t = R2(P \<^sub>t)"
  apply (simp add:R2_def R1_wait_true R2s_def)
  apply (subst SubstP_twice_3,simp_all add:unrest typing)back
  apply (simp add:usubst typing defined closure)
  apply (subst SubstP_twice_3,simp_all add:unrest typing defined closure)
  apply (simp add:usubst typing defined closure)
done

lemma R2_wait_false: "(R2(P))\<^sub>f = R2(P \<^sub>f)"
  apply(simp add:R2_def R1_wait_false R2s_def)
  apply(subst SubstP_twice_3) back
  apply (simp_all add:unrest typing)
  apply (simp add:usubst typing defined closure)
  apply (subst SubstP_twice_3) back back
  apply (simp_all add:unrest typing defined closure)
  apply (simp add:usubst typing defined closure)
done

lemma R2_ok'_true: "(R2(P))\<^sup>t = R2(P\<^sup>t)"
proof -
  have "(R2(P))\<^sup>t = R1((R2s(P))\<^sup>t)"
    by (metis R2_def PVAR_VAR_pvdash R1_ok'_true)
  also have "... = R2(P\<^sup>t)"
    apply(simp add:R2_def R2s_def)
    apply (subst SubstP_twice_3) back
    apply (simp_all add:unrest typing)
    apply (simp add:usubst typing defined closure)
    apply (subst SubstP_twice_3) back back
    apply (simp_all add:unrest typing defined closure)
    apply (simp add:usubst typing defined closure)
    done
  finally show ?thesis by this
qed

lemma R2_ok'_false: "(R2(P))\<^sup>f = R2(P\<^sup>f)"
proof -
  have "(R2(P))\<^sup>f = R1((R2s(P))\<^sup>f)"
    by (metis R2_def PVAR_VAR_pvdash R1_ok'_false)
  also have "... = R2(P\<^sup>f)"
    apply(simp add:R2_def R2s_def)
    apply (subst SubstP_twice_3) back
    apply (simp_all add:unrest typing)
    apply (simp add:usubst typing defined closure)
    apply (subst SubstP_twice_3) back back
    apply (simp_all add:unrest typing defined closure)
    apply (simp add:usubst typing defined closure)
    done
  finally show ?thesis by this
qed

lemma R2_ok_true: "`(R2(P))[true /ok]` =` R2(P[true/ok])`"
proof -
  have "`(R2(P))[true/ok]` = `R1((R2s(P))[true/ok])`"
    by (metis R2_def PVAR_VAR_pvdash R1_ok_true)
  also have "... =`R2(P[true/ok])`"
    apply(simp add:R2_def R2s_def)
    apply (subst SubstP_twice_3) back
    apply (simp_all add:unrest typing)
    apply (simp add:usubst typing defined closure)
    apply (subst SubstP_twice_3) back back
    apply (simp_all add:unrest typing defined closure)
    apply (simp add:usubst typing defined closure)
    done
  finally show ?thesis by this
qed

(* L14 commutativity R2-R1 *)

lemma R1_R2_commute: 
  "R1 (R2 P) = R2 (R1 P)" 
  by (simp add:R2_def R1_idempotent R2s_destroys_R1)

(* Additional lemmas *)

lemma R2_monotonic: "P \<sqsubseteq> Q \<Longrightarrow> R2(P) \<sqsubseteq> R2(Q)" 
  by utp_pred_tac

lemma SkipRA_is_R2 : "`R2(II)` = `II`"
proof -
  have "`R2(II)` = `R2( ($tr\<acute>=$tr) \<and> II\<^bsub>REL_VAR - TR\<^esub>)`"
    by(simp add: SkipRA_unfold_aux_ty[of "tr",THEN sym] typing defined closure SkipR_as_SkipRA)
  also have "... = `R1 ($tr\<acute> - $tr = \<langle>\<rangle>) \<and> II\<^bsub>REL_VAR - TR\<^esub>`"
    by(simp add:R2_def R2s_def usubst typing defined closure R1_extend_AndP)
  also have "... = II"
    by(simp add:R1_def tr_prefix_as_nil SkipRA_unfold_aux_ty[of "tr",THEN sym] typing defined closure SkipR_as_SkipRA)
  finally show ?thesis .
qed

lemma NotP_R2s: "`\<not>R2s(P)` = `R2s(\<not>P)`"by(simp add:R2s_def usubst typing defined closure)

lemma R2_NotP: "`R2(\<not>P)` = `R1(\<not>R2(P))`" by(utp_poly_auto_tac)

subsection {* R3 Laws *}

(* L1 R3-wait-true *)

lemma R3_wait_true: 
  "`(R3(P))\<^sub>t` = `II \<^sub>t` "
  by (simp add:R3_def usubst typing defined closure CondR_def)

(* L2 R3-wait-false *)

lemma R3_wait_false: 
  "`(R3(P))\<^sub>f` = `P \<^sub>f` "
  by (simp add:R3_def usubst typing defined closure CondR_def)

(* L4 closure-\<and>-R3 *)

lemma R3_AndP: 
  "`R3(P \<and> Q)` = `R3(P) \<and> R3(Q)`"
  by (utp_pred_auto_tac)

lemma R3_AndP_closure:
  assumes "P is R3" "Q is R3"
  shows "`P \<and> Q` is R3"
  by (metis is_healthy_def R3_AndP assms)

(* L5 closure-\<or>-R3 *)

lemma R3_OrP: 
  "`R3(P \<or> Q)` = `R3(P) \<or> R3(Q)`"
  by (utp_pred_auto_tac)

lemma R3_OrP_closure:
  assumes "P is R3" "Q is R3"
  shows "`P \<or> Q` is R3"
  by (metis is_healthy_def R3_OrP assms)
  
(* L6 closure-conditional-R3 *)

lemma R3_CondR: 
  "`R3(P  \<lhd> b \<rhd> Q)` = `R3(P) \<lhd> b \<rhd> R3(Q)`"
  by (utp_pred_auto_tac)

lemma R3_CondR_closure:
  assumes "P is R3" "Q is R3"
  shows "`P \<lhd> b \<rhd> Q` is R3"
  by (metis is_healthy_def R3_CondR assms)

(* L7 closure-sequence-R3 *)

lemma R3_form : "`R3(P)` = `($wait  \<and> II) \<or> (\<not>$wait \<and> P)`"
  by (simp add:R3_def CondR_def)

lemma R3_wait: "`R3(P) \<and> $wait` = `II \<and> $wait`"
  by(utp_poly_auto_tac)

lemma wait_and_II: "`$wait \<and> II` =`$wait \<and> II \<and> $wait\<acute>`"
  proof -
    have "`$wait \<and> II` = `$wait \<and> ($wait\<acute>=$wait) \<and> II\<^bsub>REL_VAR - {wait\<down>,wait\<down>\<acute>}\<^esub>`"
      by(subst SkipRA_unfold_aux_ty[of "wait",THEN sym],simp_all add:typing defined closure SkipR_as_SkipRA)
    also have "... = `$wait \<and> (($wait\<acute>=$wait) \<and> II\<^bsub>REL_VAR - {wait\<down>,wait\<down>\<acute>}\<^esub>) \<and> $wait\<acute>`"
      by(utp_poly_auto_tac)
    also have "... = `$wait \<and> II\<^bsub>REL_VAR\<^esub> \<and> $wait\<acute>`"
      by(subst SkipRA_unfold_aux_ty[of "wait",THEN sym],simp_all add:typing defined closure SkipR_as_SkipRA)
    finally show ?thesis by (simp add:SkipR_as_SkipRA)
qed

theorem R3_SemiR_form:
  shows "R3(P) ;\<^sub>R R3(Q) = R3(P ;\<^sub>R R3(Q))"
  proof-
    have "`R3(P);R3(Q)` = ` (($wait \<and> II \<and> $wait\<acute>) ; R3 (Q)) \<or> (\<not> $wait \<and> P) ; R3 (Q)`"
      by(simp add:R3_form[of "P"] SemiR_OrP_distr wait_and_II)
    also have "... = ` (($wait \<and> II) ; ($wait \<and>  R3 (Q))) \<or> (\<not> $wait \<and> P) ; R3 (Q)`"
      by(subst SemiR_AndP_right_DASHED,simp_all add:typing defined closure unrest urename AndP_assoc)
    also have " \<dots> = ` (($wait \<and> II) ; ($wait \<and> II)) \<or> (\<not> $wait \<and> P) ; R3 (Q)`"
      by(metis AndP_comm R3_wait)
    also have "... = ` ($wait \<and> II) \<or> (\<not> $wait \<and> P) ; R3 (Q)`"
      by(subst SemiR_AndP_right_DASHED,simp_all add:typing defined closure unrest urename AndP_assoc[THEN sym] wait_and_II)
    also have "... = ` ($wait \<and> II) \<or> (\<not> $wait \<and> (P ; R3 (Q)))`"
      by(simp add: SemiR_AndP_left_precond typing defined closure unrest)
    finally show ?thesis
      by (metis R3_form)
qed

lemma R3_SemiR_closure[closure]: 
  assumes "P is R3" "Q is R3"
  shows "P ;\<^sub>R Q is R3"
  by (metis Healthy_intro Healthy_simp R3_SemiR_form assms)

(* L8 R3-idempotent *)

lemma R3_idempotent: "`R3(R3(P))` = `R3(P)`" 
  by (utp_pred_auto_tac)

(* L10 commutativity-R3-R1 *)

lemma R1_R3_commute: "R1 (R3 P) = R3 (R1 P)"
by(metis R3_def R1_CondR R1_SkipR) 

(* L11 commutativite-R3-R2 *)

theorem R2_R3_commute: 
  "R2 (R3 P) = R3 (R2 P)"
    by(simp add:R3_def R2_CondR R2s_def usubst typing defined closure SkipRA_is_R2)

(* Additional Lemmas *)

lemma R3_SkipR: "`R3(II)` = `II`"
  by (simp add:R3_def CondR_idem)

lemma R3_monotonic: "P \<sqsubseteq> Q \<Longrightarrow> R3(P) \<sqsubseteq> R3(Q)"
  by utp_poly_tac 

end