(******************************************************************************)
(* Project: Mechanation of the UTP                                            *)
(* File: utp_csp.thy                                                          *)
(* Authors: Samuel Canham and Simon Foster, University of York                *)
(******************************************************************************)

header {* CSP Processes *}

theory utp_csp_refine
imports 
  utp_csp_process_laws
begin

lemma DesignREA_refine:
assumes 
    "`\<not>A` \<sqsubseteq> `\<not>C`"
    "`A \<Rightarrow> B` \<sqsubseteq> `D`"
shows"`RHc (A \<turnstile> B)` \<sqsubseteq> `RHc (C \<turnstile> D)`"
proof -
have 1: " `(\<not> A \<or> (B \<and> $ok\<acute>))` \<sqsubseteq> `(D \<and> $ok\<acute>)`"
proof -
  have "`(\<not> A \<or> (B \<and> $ok\<acute>))` = `((\<not> A \<and> ($ok\<acute> \<or> \<not>$ok\<acute>)) \<or> (B \<and> $ok\<acute>))`"
    by(simp add: OrP_excluded_middle)
  hence 1: "`(\<not> A \<or> (B \<and> $ok\<acute>))` = `((\<not> A \<or> B) \<and> $ok\<acute>) \<or> (\<not> A \<and> \<not>$ok\<acute>)`"
    apply(simp add:AndP_OrP_distl)
    apply(subst OrP_comm)
    apply(simp add:OrP_assoc[THEN sym])
    apply(subst AndP_OrP_distr[THEN sym])
    apply(subst OrP_comm)
    apply(simp)
    done
  have 2: "`(\<not> A \<or> (B \<and> $ok\<acute>))` \<sqsubseteq>`((\<not> A \<or> B) \<and> $ok\<acute>)`" "`((\<not> A \<or> B) \<and> $ok\<acute>)` \<sqsubseteq> `D \<and> $ok\<acute>`"
  apply(subst 1)
  apply (metis OrP_ref)
  apply(subst AndP_mono_refine)
  apply (metis ImpliesP_def assms(2))
  apply(simp_all add:eq_iff)
  done
  from 2 show ?thesis
  by (smt dual_order.trans)
qed
from 1 have 0: 
  "`R2(B) \<and> $ok\<acute>` = `R2(B \<and> $ok\<acute>)`"
  "`R2(D) \<and> $ok\<acute>` = `R2(D \<and> $ok\<acute>)`" 
  "`(\<not> A \<or> (B \<and> $ok\<acute>))` \<sqsubseteq> `(\<not> C \<or> (D \<and> $ok\<acute>))`" 
apply(simp_all add:R2_def R2s_def usubst typing defined closure R1_extend_AndP)
apply(subst OrP_refine)
apply (metis AndP_OrP_absorb RefineP_seperation assms(1))
apply(simp)
apply(simp)
done
from 0 show ?thesis
apply(simp add:DesignREA_form)
apply(subst OrP_mono_refine)
apply (metis AndP_idem RefP_AndP)
apply(subst OrP_mono_refine)
apply (metis eq_iff)
apply(simp add:AndP_OrP_distl[THEN sym])
apply(subst AndP_mono_refine)
apply(metis eq_iff)
apply(subst AndP_mono_refine)
apply(metis eq_iff)
apply(simp add:R2_OrP[THEN sym])
apply(subst R2_monotonic)
apply(simp)
apply(simp)
done
qed

lemma aid2:
assumes 
  "NON_REL_VAR\<sharp> a" 
  "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>} \<sharp> a"
  "`P \<Rightarrow> Q` \<sqsubseteq> `((a \<notin> $ref\<acute>) \<and> ($tr\<acute> = $tr)) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)`"
shows "`RHc(P \<turnstile> Q)` \<sqsubseteq> `@a`"
apply(simp add:assms Prefix_design)
apply(subst DesignREA_refine)
apply(simp add:R2s_def usubst typing defined closure)
apply (metis RefineP_FalseP_refine)
apply (metis PVAR_VAR_pvdash assms(3))
apply(simp)
done

lemma aid3:
  assumes "`a \<Rightarrow> b` \<sqsubseteq> `c`"
  shows "`c \<Rightarrow> b` \<sqsubseteq> `a`"
proof -
  have "`(a \<Rightarrow> b) \<and> a` \<sqsubseteq> `c \<and> a`"
    by (metis AndP_mono_refine assms eq_iff)
  hence "`b \<and> a` \<sqsubseteq> `c \<and> a`"
    by (metis AndP_comm ImpliesP_AndP_pre utp_pred_simps(13) utp_pred_simps(7))  
  hence "`b` \<sqsubseteq> `c \<and> a`"
    by (metis RefineP_seperation)
  hence 1: "`b` \<sqsubseteq> `a \<and> c`"
    by (metis AndP_comm)
  hence "`b \<and> c` \<sqsubseteq> `a \<and> c`"
    by (metis AndP_refines_2 RefineP_seperation_refine dual_order.refl)
  hence "`(c \<Rightarrow> b) \<and> c` \<sqsubseteq> `a \<and> c`"
    by (metis "1" AndP_assoc AndP_comm AndP_idem RefineP_seperation RefineP_seperation_refine SemiR_spec_refine)
  hence "`(c \<Rightarrow> b)` \<sqsubseteq> `a`"
    by (metis "1" AndP_comm SemiR_spec_refine)
  thus ?thesis .
qed

lemma aid4:
assumes 
  "NON_REL_VAR\<sharp> a" 
  "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>} \<sharp> a"
  "`(((a \<notin> $ref\<acute>) \<and> ($tr\<acute> = $tr)) \<lhd> $wait\<acute> \<rhd> ($tr ^ \<langle>a\<rangle> = $tr\<acute>)) \<Rightarrow> Q` \<sqsubseteq> `P`"
shows "`RHc(P \<turnstile> Q)` \<sqsubseteq> `@a`"
apply(subst aid2)
apply(simp_all add:assms)
apply(subst aid3)
apply (metis (hide_lams, no_types) PVAR_VAR_pvdash assms(3))
apply(simp)
done

lemma aid5:
assumes 
  "NON_REL_VAR\<sharp> a" 
  "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>} \<sharp> a"
  "D\<^sub>2 \<sharp> Q"
shows "`RHc((CSP_Post(@a) \<Rightarrow> Q) \<turnstile> Q)` \<sqsubseteq> `@a`"
proof - 
have 0: "{ok\<down>, wait\<down>, ok\<down>\<acute>} \<sharp> a"
proof - have 1: "{ok\<down>, wait\<down>, ok\<down>\<acute>} \<subseteq> {tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>}" 
by (metis doubleton_eq_iff subset_insertI subset_insertI2)
show ?thesis
by (smt "1" UNREST_PEXPR_subset assms(2))
qed
show ?thesis
apply(subst aid4)
apply(simp_all add:assms)
apply(subst Prefix_post)
apply(simp add:0)
apply (metis (lifting, no_types) AndP_idem PVAR_VAR_pvdash RefP_AndP)
done
qed

lemma hand:
  assumes "`P` \<sqsubseteq> `a \<and> R`"
  shows"`P \<or> (\<not>a \<and> Q)` \<sqsubseteq> `a \<and> R`"
by (metis AndP_OrP_absorb RefineP_seperation assms)

lemma hand2:
  assumes "`P \<or> Q` \<sqsubseteq> `R`"
  shows "`P \<or> (a \<and> Q)` \<sqsubseteq> `a \<and> R`"
by (metis AndP_OrP_distl OrP_AndP_distl OrP_assoc RefP_OrP assms)

lemma hand3:
  assumes "`P` \<sqsubseteq> `\<not>a \<and> R`"
  shows"`P \<or> (a \<and> Q)` \<sqsubseteq> `\<not>a \<and> R`"
by (metis AndP_OrP_absorb RefineP_seperation assms)

lemma CSP4_Design_refine:
assumes 
  "P is CSP" "Q is CSP" "P is CSP4" "Q is CSP4" "P \<in> REL" "Q \<in> REL" 
  "A = CSP_Pre(P)" "B = CSP_Post(P)" "C= CSP_Pre(Q)" "D = CSP_Post(Q)"
  "`((\<not> A) ; ($tr \<le> $tr\<acute>))` \<sqsubseteq> `((\<not> C) ; ($tr \<le> $tr\<acute>))`"
  "`(((\<not> A) ; ($tr \<le> $tr\<acute>)) \<or> B[true/wait\<acute>])` \<sqsubseteq> `D[true/wait\<acute>]`"
  "`(((\<not> A) ; ($tr \<le> $tr\<acute>)) \<or> (\<exists> ref\<acute> . B[false/wait\<acute>]))` \<sqsubseteq> `(\<exists> ref\<acute> . D[false/wait\<acute>])`"
shows
 "P \<sqsubseteq> Q"
apply(subst CSP4_Design_form,simp_all add:assms)
apply(subst CSP4_Design_form,simp_all add:assms) back back back back back back back back back back back back back back back back back
apply(subst DesignREA_refine)
apply(simp_all add:CondR_def ImpliesP_def OrP_assoc[THEN sym])
apply (metis assms(11) assms(7) assms(9))
apply(simp_all add: assms(7)[THEN sym] assms(8)[THEN sym] assms(9)[THEN sym] assms(10)[THEN sym]) 
apply(subst OrP_refine)
apply(subst OrP_assoc)
apply(subst hand)
apply(subst hand2)
apply (metis PVAR_VAR_pvdash assms(12))
apply(simp_all)
apply(subst OrP_comm) back
apply(subst OrP_assoc)
apply(subst hand3)
apply(subst hand2)
apply (metis (hide_lams, no_types) PVAR_VAR_pvdash assms(13)) 
apply(simp)
done

lemma 
  assumes   "NON_REL_VAR \<sharp> a"
    "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>,wait\<down>\<acute>,ref\<down>\<acute>} \<sharp> a" 
  shows "`@a \<box> SKIP` \<sqsubseteq> `SKIP`"
proof-
have 1:" {tr\<down>, tr\<down>\<acute>, ok\<down>\<acute>} \<sharp> a" 
    by(auto intro: assms UNREST_PEXPR_subset)
have 3:" {ok\<down>, wait\<down>, ok\<down>\<acute>} \<sharp> a"
    by(auto intro: assms UNREST_PEXPR_subset)
have 5: "{wait\<down>\<acute>}\<sharp>a"
    by(auto intro: assms UNREST_PEXPR_subset)
have a: "REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>} =
    REL_VAR - {wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>, ok\<down>, ok\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>}"
by(utp_poly_auto_tac)
have 4: "`($tr\<acute> =$tr) \<and> II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub>` = `II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>, ok\<down>, ok\<down>\<acute>}\<^esub>`"
apply(subst SkipRA_unfold_aux_ty[of "tr"]) back
apply(simp_all add:typing closure defined)
apply(metis a)
done
have 6: "in(REL_VAR) = D\<^sub>0"
by (metis in_out_UNDASHED_DASHED(1) in_out_UNDASHED_DASHED(3) in_vars_union sup_bot_right)

have 2: "`SKIP;SKIP` = `SKIP`"
proof -
have "`SKIP;SKIP` = `
 RHc (true \<turnstile>
         (($tr\<acute>=$tr) \<and> II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub> \<and> \<not> $wait\<acute>) ;
         (($tr\<acute> = $tr) \<and>
          II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub> \<and>  \<not> $wait\<acute>))`"
apply(subst Seq_comp_form,simp_all add:closure typing defined Skip_CSP)
apply(simp add:Skip_pre Skip_post)
apply(simp add:R2s_def R2_def R1_def usubst typing defined closure)
apply(simp add:CondR_def AndP_assoc[THEN sym] OrP_assoc[THEN sym] SemiR_OrP_distl)
apply(simp add: SemiR_AndP_right_precond typing defined closure urename)
apply(subst AndP_comm) back back
apply(subst AndP_comm) back
apply(simp add:AndP_assoc[THEN sym])
apply(subst AndP_assoc)
apply(simp add:AndP_contra)
apply(subst AndP_comm) back
apply(simp add:AndP_assoc[THEN sym])
 apply(subst AndP_comm) back back back back
apply(subst AndP_comm) back back back
apply(simp add:AndP_assoc[THEN sym])
apply(subst AndP_assoc) back
apply(simp add:tr_prefix_as_nil)
done
also have "... = `RHc(true \<turnstile> (II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>,ref\<down>, ref\<down>\<acute>,ok\<down>, ok\<down>\<acute>}\<^esub>) ;
         (\<not> $wait \<and> II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>,ok\<down>, ok\<down>\<acute>}\<^esub> \<and>  \<not> $wait\<acute>))`"
apply(simp add:AndP_assoc 4)
apply(simp add:AndP_assoc[THEN sym])
apply(subst SemiR_AndP_right_precond) back
apply(simp_all add:typing closure defined urename) 
done
also have "... = `RHc(true \<turnstile> (II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>,ref\<down>, ref\<down>\<acute>,ok\<down>, ok\<down>\<acute>}\<^esub> ;
         II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>,ok\<down>, ok\<down>\<acute>}\<^esub>) \<and>  \<not> $wait\<acute>)`"
apply(subst SemiR_remove_middle_unrest1[of _ _ "{wait \<down>}"])
apply(simp_all add:typing closure defined unrest)
apply(subst UNREST_subset[of "-(REL_VAR - {wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>, ok\<down>, ok\<down>\<acute>})"])
apply(subst UNREST_SkipRA,simp)
defer 
apply(rule unrest) back
apply(subst UNREST_subset[of "-(REL_VAR - {wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>, ok\<down>, ok\<down>\<acute>})"])
apply(subst UNREST_SkipRA,simp) defer 
apply(simp add:typing closure defined unrest)
apply(subst SemiR_AndP_right_postcond)
apply(simp_all add:typing closure defined)
done
also have "... = `SKIP`"
apply(subst SemiR_SkipRA_left)
apply(simp_all add:typing closure defined unrest)
apply(subst UNREST_subset[of "-(REL_VAR - {wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>, ok\<down>, ok\<down>\<acute>})"])
apply(subst UNREST_SkipRA,simp) defer 
apply(subst Skip_design)
apply(subst 4[THEN sym])
apply(subst AndP_comm) back back back
apply(simp add:AndP_assoc[THEN sym])
apply(subst in_vars_diff)
apply(subst 6)
apply(simp add:typing closure defined)
apply (smt in_vars_def inf.orderI inf_bot_left inf_sup_aci(1) inf_sup_aci(2) insert_inter_insert)
done
finally show ?thesis . qed
show ?thesis
apply(subst CSP4_Design_refine)
apply(subst External_CSP)
apply(simp_all add:closure typing defined assms Skip_CSP)
apply(subst Prefix_CSP, simp_all add:1)
defer 
apply(simp add:CSP4_def is_healthy_def)
apply(simp add:2)
apply(subst External_pre,simp_all add:closure typing defined assms)
apply(simp add:Prefix_pre)
apply(subst External_pre,simp_all add:closure typing defined assms)
apply(subst External_post,simp_all add:closure typing defined assms)
apply(simp_all add:Prefix_pre Prefix_post 3 4 Skip_pre Skip_post)
apply(simp_all add:usubst typing defined closure 5 6 PSubstPE_VarP_single_UNREST PVAR_VAR_pvdash)
apply(simp add:RefineP_FalseP_refine)
apply(subst External_pre,simp_all add:closure typing defined assms)
apply(subst External_post,simp_all add:closure typing defined assms)
apply(simp_all add:Prefix_pre Prefix_post 3 4 Skip_pre Skip_post)
apply(simp_all add:usubst typing defined closure 5 6 PSubstPE_VarP_single_UNREST PVAR_VAR_pvdash)
apply(subst 4)
apply(simp add:ExistsP_OrP_dist)
apply(subst OrP_comm)
apply(simp add: OrP_ref)
apply(subst External_CSP4)
apply(simp_all add:assms Skip_CSP closure Prefix_CSP 1 Prefix_CSP4)
apply(simp add:is_healthy_def CSP4_def 2)
done
qed

lemma foot1: assumes "`P \<and> B` \<sqsubseteq> `A \<and> B`"
  shows "`P` \<sqsubseteq> `A \<and> B`"
by (metis RefineP_seperation assms)

lemma foot2:
  assumes"`P` \<sqsubseteq> `b \<and> Q`" "`P` \<sqsubseteq> `\<not>b \<and> R`" 
  shows "`P` \<sqsubseteq> `Q  \<lhd> b \<rhd> R`" 
  apply(simp add:CondR_def)
  apply(metis OrP_refine PVAR_VAR_pvdash assms(1) assms(2))
done

lemma foot3: assumes "`P` \<sqsubseteq> `A \<and> B`"
  shows "`P \<and> B` \<sqsubseteq> `A \<and> B`"
by (metis RefineP_seperation assms dual_order.refl)

(* Broken lemma *)

lemma
  assumes "P is CSP" "P is CSP4" "P \<in> REL"
          "A \<in> REL" "B \<in> REL" "{ok\<down>,wait\<down>,ok\<down>\<acute>}\<sharp>`A`" "{ok\<down>,wait\<down>,ok\<down>\<acute>}\<sharp>`B`" "`\<not>A` is R2" "`B` is R2"
          "`(\<not>A) ;($tr \<le> $tr\<acute>)` \<sqsubseteq> `(\<not>CSP_Pre(P)); ($tr \<le> $tr\<acute>)`" 
          "`(((\<not> A); ($tr \<le> $tr\<acute>)) \<or> B) \<sqsubseteq> (CSP_Post(P) \<and> $wait\<acute>)`"
          "`(((\<not> A); ($tr \<le> $tr\<acute>)) \<or> (\<exists> ref\<acute> .B))` \<sqsubseteq> `(\<exists> ref\<acute> . CSP_Post(P)) \<and> \<not> $wait\<acute>`"
  shows "`CSP4(RHc(A \<turnstile> B))` \<sqsubseteq> `P`" 
proof - 
have 1: "`((\<not> A[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>][false/ok\<acute>][true/ok][false/wait] \<and> ($tr \<le> $tr\<acute>)) ;
     ($tr \<le> $tr\<acute>))` \<sqsubseteq>
    `(P[false/ok\<acute>][true/ok][false/wait] ; ($tr \<le> $tr\<acute>))`"
proof -
have a: "`P` = `R1(P)`" by (metis assms CSP_is_RHc RHc_is_R1 is_healthy_def)
  have "`(\<not>CSP_Pre(R2(\<not> A))) ;($tr \<le> $tr\<acute>)` \<sqsubseteq>
    `(\<not>CSP_Pre(P)); ($tr \<le> $tr\<acute>)`" 

apply(simp add: CSP_Pre_R2_commute)
apply(subst CSP_Pre_UNREST) back
apply(rule unrest)
apply(simp_all add:assms)
apply(metis assms is_healthy_def)
done
  thus ?thesis 
  apply(simp add:R2_def R2s_def R1_def CSP_Pre_def)
  apply(simp add:usubst typing defined closure)
  done
qed
have 2:"`(false = true)` = `false`" by(utp_poly_auto_tac)
have 3:"`(true = true)` = `true`" by(utp_poly_auto_tac)
have 6:"D\<^sub>1 - out (REL_VAR - {ok\<down>, ok\<down>\<acute>}) = {ok\<down>\<acute>}" 
apply(utp_poly_auto_tac)
apply(simp add:out_vars_diff typing closure defined)
done
have 8:  "`\<not> (\<not> R2(A) ; ($tr \<le> $tr\<acute>)) \<Rightarrow>
     ((R2 (A \<Rightarrow> B) \<and> $wait\<acute>) \<or>
     (R2 (A \<Rightarrow> B) ;
     (\<not> $wait \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>,ok\<down>, ok\<down>\<acute>}\<^esub>)))` \<sqsubseteq>
    `CSP_Post(P)[true/wait\<acute>] \<lhd> $wait\<acute> \<rhd> (\<exists> ref\<acute> . CSP_Post(P)[false/wait\<acute>])`"
proof-
have a: "`P` = `R1(P)`" by (metis assms CSP_is_RHc RHc_is_R1 is_healthy_def)
have b: "`$tr\<le>$tr\<acute>`=`R2($tr\<le>$tr\<acute>)`"
by(simp add:R2_def R2s_def usubst typing closure defined R1_def)
have c: "`((\<not> ($tr \<le> $tr\<acute>)) ; ($tr \<le> $tr\<acute>)) \<and> ($tr \<le> $tr\<acute>)` = `false`"

sorry
have d: "` R1 (CSP_Post(P)[true/wait\<acute>])` = `CSP_Post(P)[true/wait\<acute>]`"
apply(subst a) back
apply(subst CSP_Post_R1_commute)
apply(simp add:R1_def usubst typing defined closure)
done
from assms(11) have e: "`(((\<not> A); ($tr \<le> $tr\<acute>)) \<or> B) \<sqsubseteq> (CSP_Post(P)[true/wait\<acute>] \<and> $wait\<acute>)`"
by(utp_poly_auto_tac)
have f: "`R2(\<not>A)` = `\<not>A`" by(metis assms is_healthy_def)
have g: "`R2(B)` = `B`" by(metis assms is_healthy_def)
have h: "D\<^sub>1 - out (REL_VAR - {ref\<down>, ref\<down>\<acute>, ok\<down>, ok\<down>\<acute>}) = {ref\<down>\<acute>,ok\<down>\<acute>}" 
proof -
have x: "D\<^sub>1 = out(REL_VAR)"
by (metis Un_empty_left in_out_UNDASHED_DASHED(2) in_out_UNDASHED_DASHED(4) out_vars_union)
have y: "out({ref\<down>,ref\<down>\<acute>,ok\<down>,ok\<down>\<acute>}) = {ref\<down>\<acute>,ok\<down>\<acute>}" sorry
show ?thesis
by(simp add:out_vars_diff typing defined closure x[THEN sym] y)
qed
show ?thesis
apply(subst SemiR_AndP_right_precond,simp_all add:typing closure urename f)
apply(subst SemiR_extract_variable_id[of "ref\<down>"],simp_all add:typing defined unrest assms closure)back
apply(simp add:usubst typing defined closure)
apply(subst ExistsP_SemiR_NON_REL_VAR_expand2[THEN sym])
apply(simp_all add:typing closure defined unrest)
apply(subst SemiR_SkipRA_right)
apply(simp add:typing closure defined unrest) defer 
apply(subst ExistsP_AndP_expand1[THEN sym])
apply(simp add:typing closure defined unrest)
apply(subst AndP_comm)
apply(subst AndP_comm) back
apply(subst CondR_def[THEN sym])
apply(subst foot2)
apply(subst AndP_comm)
apply(subst foot1) defer
apply(simp)
apply(subst AndP_comm)
apply(subst foot1) defer
apply(simp) defer 
apply(subst AndP_comm) back
apply(simp add:CondR_def ImpliesP_def AndP_OrP_distl AndP_assoc AndP_contra R2_OrP)
apply(simp add:AndP_OrP_distl[THEN sym])
apply(subst AndP_comm) back
apply(subst foot3,simp_all)
apply(subst a)
apply(subst CSP_Post_R1_commute)
apply(simp add:g R2_def)
apply(subst foot7[THEN sym])
apply(subst foot6[THEN sym])
apply(simp add:R2_def[THEN sym] f)
apply(simp add:R1_def usubst typing defined closure AndP_assoc[THEN sym]g)
apply(subst AndP_comm) back
apply(subst AndP_assoc)
apply(subst foot1)
apply(simp add:R1_def[THEN sym] R1_OrP R1_idempotent)
apply(simp add:R1_OrP[THEN sym])
apply(subst OrP_assoc)
apply(subst foot4,simp add:R1_def)
apply(subst foot3,simp add:R1_def[THEN sym] R1_extend_AndP[THEN sym])
apply(simp_all add:h) defer defer
apply(rule unrest) apply(rule unrest)
apply(rule unrest) apply(simp_all add:typing defined closure unrest ImpliesP_def)
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:typing defined closure unrest assms)
sorry
qed
have a: "REL_VAR - {ref\<down>, ref\<down>\<acute>, ok\<down>, ok\<down>\<acute>} - {wait\<down>, wait\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>} = REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}"
by(utp_poly_auto_tac)
have b: "`\<not>$wait \<and> ($wait\<acute>=$wait)`=`\<not>$wait \<and> \<not>$wait\<acute>`"
by(utp_poly_auto_tac)
have 7: "`\<not> (\<not> R2(A) ; ($tr \<le> $tr\<acute>)) \<Rightarrow>
     ((R2 (A \<Rightarrow> B) \<and> $wait\<acute>) \<or>
     (R2 (A \<Rightarrow> B) ;
     (\<not> $wait \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>,ok\<down>, ok\<down>\<acute>}\<^esub>)))`
        = `\<not> (\<not> R2(A) ; ($tr \<le> $tr\<acute>)) \<Rightarrow>
     ((R2 (A \<Rightarrow> B) \<and> $wait\<acute>) \<or>
     (R2 (A \<Rightarrow> B) ;
     (\<not> $wait \<and> \<not> $wait\<acute> \<and> ($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub>)))`"
apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add:typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing defined closure)
apply(subst a)
apply(subst AndP_assoc)
apply(subst b)
apply(simp add:AndP_assoc[THEN sym])
done
have 5: "`(\<not> (\<not>CSP_Pre(R2(\<not>A)) ; ($tr \<le> $tr\<acute>)) \<Rightarrow>
     (CSP_Post(R2(\<not> A)) \<or> CSP_Post(R2(B))) ;
     (II\<^bsub>REL_VAR - {ok\<down>, ok\<down>\<acute>}\<^esub> \<lhd> $wait \<rhd> 
      ((($tr\<acute> - $tr = \<langle>\<rangle>) \<and> \<not> $wait\<acute> \<and>
      II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub>) \<and> ($tr \<le> $tr\<acute>))))` 
      \<sqsubseteq>
    `CSP_Post(P)[true/wait\<acute>] \<lhd> $wait\<acute> \<rhd> (\<exists> ref\<acute> . CSP_Post(P)[false/wait\<acute>])`"
apply(simp add:CSP_Pre_R2_commute CSP_Post_R2_commute)
apply(simp add: CSP_Pre_UNREST CSP_Post_UNREST unrest assms R2_OrP[THEN sym] ImpliesP_def[THEN sym])
apply(simp add:CondR_def SemiR_OrP_distl)
apply(subst SemiR_AndP_right_precond,simp_all add:typing defined closure urename)
apply(subst SemiR_SkipRA_right,simp_all add:6 typing defined closure)
apply(rule unrest) back back
apply(rule unrest)
apply(rule unrest) back back
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms unrest)
apply(simp add:AndP_assoc[THEN sym])
apply(subst AndP_assoc) back
apply(subst AndP_comm) back back back back
apply(subst AndP_comm) back back back back back back
apply(simp add:AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back
apply(subst tr_prefix_as_nil)
sorry
have 4: "`(\<not> ((\<not> A[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>][false/ok\<acute>][true/ok][false/wait] \<and> ($tr \<le> $tr\<acute>)) ;
         ($tr \<le> $tr\<acute>)) \<Rightarrow>
     ((\<not> A[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>][true/ok\<acute>][true/ok][false/wait] \<and> ($tr \<le> $tr\<acute>)) \<or>
      B[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>][true/ok\<acute>][true/ok][false/wait] \<and> ($tr \<le> $tr\<acute>)) ;
     (II\<^bsub>REL_VAR -
        {ok\<down>, ok\<down>\<acute>}\<^esub> \<lhd> $wait \<rhd> ((($tr\<acute> - $tr = \<langle>\<rangle>) \<and>
                                 \<not> $wait\<acute> \<and>
                                 II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub>) \<and>
                                ($tr \<le> $tr\<acute>))))` \<sqsubseteq>
    `P[true/ok\<acute>][true/ok][false/wait][true/wait\<acute>] \<lhd> $wait\<acute> \<rhd> (\<exists> ref\<acute> .
                        P[true/ok\<acute>][true/ok][false/wait][false/wait\<acute>])`"
proof -
from 5 show ?thesis
by(simp add:R2_def CSP_Pre_def R1_def R2s_def usubst typing defined closure CSP_Post_def)
have "`CSP4(RHc(A \<turnstile> B))` \<sqsubseteq> `P`"
apply(subst CSP4_Design_form)
apply(simp_all add:assms)
apply(simp add:CSP4_def)
apply(subst DesignREA_form) back
apply(subst Seq_comp_form[of _ "SKIP"])
apply(simp_all add:closure typing defined assms Skip_CSP)
apply(simp add:is_healthy_def CSP_def RHc_def)
apply(simp add: R1_R3c_commute R2_R3c_commute)
apply(simp add:R2_def R1_idempotent SkipR_as_SkipRA)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing defined closure)
apply(simp add:R2s_def R1_def usubst typing defined closure AndP_OrP_distr)
apply(subst AndP_assoc) back
apply(subst AndP_comm) back back back
apply(simp add:AndP_assoc[THEN sym] tr_prefix_as_nil)
apply(subst AndP_assoc) back
apply(subst AndP_comm) back back back
apply(subst AndP_assoc) back
apply(subst SkipRA_unfold_aux_ty[of "tr" "REL_VAR",THEN sym],simp_all add:typing defined closure)
apply(simp add:AndP_OrP_distl[THEN sym])
apply(subst AndP_comm) back back
apply(simp add:CondR_def[THEN sym])
apply(simp add:CSP1_CSP2_commute CSP1_R3c_commute)
apply(simp add:CSP1_def)
apply(subst OrP_comm) back back
apply(simp add:OrP_assoc)
apply(simp add:R3c_def)
apply(subst CSP1_R1_form)
apply (metis R1_SkipR_closure) 
apply(simp add:CSP1_def SkipR_as_SkipRA CondR_def AndP_OrP_distr AndP_OrP_distl AndP_assoc[THEN sym] OrP_assoc[THEN sym])
apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing closure defined)
apply(simp add:usubst typing defined closure)
apply(subst OrP_assoc) back
apply(simp add:AndP_OrP_distr[THEN sym])
apply(simp add: OrP_excluded_middle)
apply(subst AndP_assoc) back back
apply(subst AndP_comm) back back back back
apply(subst AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back back
apply(subst AndP_comm) back back back back back
apply(simp add:AndP_contra)
apply(subst AndP_assoc)
apply(subst AndP_comm)
apply(subst AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back
apply(subst AndP_comm) back back back back
apply(simp add:AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back back
apply(simp add:AndP_idem)
apply(subst AndP_assoc) back back back back
apply(subst AndP_comm) back back back back back back back
apply(subst AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back back back back
apply(simp add:AndP_idem)
apply(subst SubstP_twice_3) back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_1)
apply(simp add:typing defined closure usubst)
apply(subst SubstP_twice_3) back back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_1)
apply(simp add:typing defined closure usubst)
apply(subst AndP_comm) back back back back back back back back back back
apply(subst OrP_assoc)
apply(subst OrP_comm)
apply(simp add:OrP_assoc[THEN sym])
apply(simp add:H2_split usubst typing defined closure)
apply(subst SubstP_twice_3,simp_all add:typing defined closure unrest) back
apply(subst SubstP_twice_3,simp_all add:typing defined closure unrest)
apply(simp add:usubst typing defined closure)
apply(subst SubstP_VarP_single_UNREST)
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
apply(simp add: 2 3 OrP_assoc[THEN sym] AndP_OrP_distr)
apply(subst OrP_assoc) back
apply(subst OrP_comm) back
apply(subst OrP_assoc[THEN sym])
apply(subst OrP_assoc)
apply(subst OrP_AndP_absorb)
apply(subst OrP_assoc) back
apply(subst OrP_comm) back
apply(subst OrP_assoc[THEN sym])
apply(subst OrP_assoc) back back
apply(subst SubstP_twice_3) back back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_3) back
apply(simp_all add:typing defined closure unrest)
apply(simp add:typing defined closure usubst)
apply(subst SubstP_VarP_single_UNREST)back back
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
apply(subst OrP_AndP_absorb)
apply(subst SubstP_twice_3) back back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_3) back
apply(simp_all add:typing defined closure unrest)
apply(simp add:typing defined closure usubst)
apply(subst SubstP_VarP_single_UNREST) back back
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
apply(simp add:AndP_assoc[THEN sym])
apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing defined closure) back
apply(utp_poly_auto_tac) 
apply(simp add:Skip_pre Skip_post)
apply(subst DesignREA_refine)
apply(simp_all)
apply(simp add:CSP_Pre_def CSP_Post_def usubst typing defined closure)
apply(simp add:R2_def R2s_def R1_def usubst typing defined closure)
apply (metis (lifting, mono_tags) "1" AndP_comm PVAR_VAR_pvdash)
sorry
qed
show ?thesis sorry
oops

end