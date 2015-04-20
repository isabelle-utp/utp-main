(******************************************************************************)
(* Project: Mechanation of the UTP                                            *)
(* File: utp_csp.thy                                                          *)
(* Authors: Samuel Canham and Simon Foster, University of York                *)
(******************************************************************************)

header {* CSP Processes *}

theory utp_csp_process_laws
imports 
  utp_csp_processes
begin

lemma Prefix_L1A:
  assumes "P is CSP" "P \<in> REL" "\<D> a" "VAR \<sharp> a"
  shows "`STOP` \<noteq> `a \<rightarrow> P`"
proof-
have Z : "{tr\<down>\<acute>} \<sharp> a" "{wait\<down>} \<sharp> a" "{tr\<down>} \<sharp> a" "{ok\<down>}\<sharp>a" "{ok\<down>\<acute>}\<sharp>a" "{wait\<down>\<acute>}\<sharp>a" "{ref\<down>\<acute>}\<sharp>a" "NON_REL_VAR \<sharp> a" "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>, wait\<down>\<acute>,ref\<down>\<acute>} \<sharp> a" "D\<^sub>0 \<sharp> a" "D\<^sub>1 \<sharp> a" 
    by(auto intro: assms UNREST_PEXPR_subset)
have 0: "`$tr ^ \<langle>a\<rangle> \<le> $tr` = `false`" 
  by(utp_poly_auto_tac)
have 1: "`a \<notin> {a}` = `false`"
  by(utp_poly_auto_tac)
have A: "`STOP[true/ok][false/wait][true/ok\<acute>][true/wait\<acute>][$tr/tr\<acute>][{a}/ref\<acute>]` = `true`"
apply(subst Stop_design,simp add:DesignREA_form R2_def R2s_AndP R1_extend_AndP[THEN sym])
apply(simp add:R2s_def usubst typing defined closure R1_def tr_prefix_as_nil)
apply(subst SubstP_VarP_single_UNREST,simp add:typing defined closure unrest)
apply(utp_poly_auto_tac)
done
have "`(a \<rightarrow> P)[true/ok][false/wait][true/ok\<acute>][true/wait\<acute>][$tr/tr\<acute>][{a}/ref\<acute>]` = 
`(\<exists> tr\<acute>\<acute> .
      (
          ($tr\<acute>\<acute> \<le> $tr) \<and>
          (\<exists> ref\<acute>\<acute> .
          (P[false/ok\<acute>][true/ok][false/wait][true/ok\<acute>][true/wait\<acute>][$tr\<acute>\<acute>/tr][$ref\<acute>\<acute>/ref][$tr/tr\<acute>][{a}/ref\<acute>]) \<or>
          (P[true/ok\<acute>][true/ok][false/wait][true/ok\<acute>][true/wait\<acute>][$tr\<acute>\<acute>/tr][$ref\<acute>\<acute>/ref][$tr/tr\<acute>][{a}/ref\<acute>])) 
      ) \<and>($tr\<acute>\<acute> = $tr ^ \<langle>a\<rangle>))`"
apply(subst Prefixed_design,simp_all add:assms Z)
apply(subst UNREST_PEXPR_subset[of "{tr\<down>,tr\<down>\<acute>,ok\<down>,ok\<down>\<acute>,wait\<down>,wait\<down>\<acute>,ref\<down>\<acute>}"])
apply(simp_all add:assms Z)
apply(simp add:DesignREA_form) 
apply(subst Healthy_simp[of _ "R2"]) defer
apply(subst Healthy_simp[of _ "R2"]) defer
apply(simp add:usubst typing defined closure)
apply(subst OrP_comm) back
apply(subst OrP_assoc)
apply(simp add:SubstP_OrP[THEN sym] SemiR_OrP_distl[THEN sym] ImpliesP_def[THEN sym])
apply(simp add:SubstP_SemiR_left SubstP_SemiR_right typing defined closure unrest)
apply(simp add:PSubstPE_VarP_single_UNREST typing defined closure Z)
apply(simp add:typing defined closure usubst PSubstPE_VarP_single_UNREST Z)
apply(subst OrP_comm)
apply(subst usubst) defer
apply(subst usubst) back
apply(subst usubst) back back back defer
apply(subst PSubstPE_VarP_single_UNREST) defer
apply(subst SubstP_VarP_single_UNREST) defer
apply(subst OrP_comm)
apply(subst SemiR_extract_variable_ty[of "tr" "tr\<acute>\<acute>"],simp_all add:typing defined closure) defer defer
apply(simp add:usubst typing defined closure)
apply(subst SemiR_AndP_left_DASHED) defer
apply(subst SemiR_extract_variable_ty[of "ref" "ref\<acute>\<acute>"],simp_all add:typing defined closure) defer defer
apply(simp add:usubst typing defined closure)
apply(subst SemiR_SkipRA_left,simp add:typing defined closure) defer
apply(subst Healthy_simp[of "P" "R1",THEN sym]) defer
apply(subst Healthy_simp[of "P" "R1",THEN sym]) back defer
apply(subst SubstP_ExistsP) defer defer 
apply(subst SubstP_ExistsP) defer defer
apply(simp add:SubstP_AndP)
apply(subst SubstP_ExistsP) defer defer
apply(subst SubstP_ExistsP) defer defer
apply(simp add:CSP_Pre_def CSP_Post_def ImpliesP_def usubst typing defined closure R1_def AndP_OrP_distr[THEN sym])
apply(subst SubstP_VarP_single_UNREST) defer
apply(subst AndP_comm)
apply(subst AndP_comm)
apply(subst SubstP_VarP_single_UNREST) defer
apply(subst ExistsP_AndP_expand2[THEN sym]) back defer
apply(simp add:usubst typing defined closure PSubstPE_VarP_single_UNREST Z)
apply(subst PEqualP_sym,simp add:1) defer defer
apply(simp add:typing closure defined unrest assms Z)
apply(simp add:typing closure defined unrest assms Z)
apply(simp add:typing closure defined unrest assms Z) defer 
apply(simp add:typing closure defined unrest assms Z)
apply(simp add:typing closure defined unrest assms Z PSubstPE_VarP_single_UNREST)
apply(subst UNREST_subset[of "-(REL_VAR - REA - OKAY)"],subst UNREST_SkipRA,simp) defer
apply(simp add:typing closure defined unrest assms Z) defer
apply(metis assms is_healthy_def CSP_is_RHc RHc_is_R1)
apply(simp add:typing closure defined unrest assms Z)
apply(simp add:typing closure defined unrest assms Z) defer
apply(simp add:typing closure defined unrest assms Z)
apply(simp add:typing closure defined unrest assms Z)
apply(simp add:typing closure defined unrest assms Z) defer
apply(simp add:typing closure defined unrest assms Z) 
apply(simp add:typing closure defined unrest assms Z PSubstPE_VarP_single_UNREST)
apply(simp add:typing closure defined unrest assms Z)
apply(simp add:typing closure defined unrest assms Z)
apply(subst R2_SemiR_closure)
apply(simp add:is_healthy_def R2_def R2s_def R1_extend_AndP[THEN sym] usubst typing defined closure)
apply(simp add:R1_def tr_prefix_as_a PSubstPE_VarP_single_UNREST Z)
apply(simp add:is_healthy_def CSP_Pre_R2_commute[THEN sym])
apply(metis assms is_healthy_def CSP_is_RHc RHc_is_R2)  
apply(subst closure)
apply(subst closure)
apply(simp add:assms Z,simp)
apply(subst closure,simp)
apply(simp add:closure Z typing defined assms)
apply(subst R2_OrP_closure)
apply(simp add:R2_def is_healthy_def R2s_def R1_def tr_prefix_as_nil AndP_assoc[THEN sym] usubst typing defined closure PSubstPE_VarP_single_UNREST Z)
apply(subst R2_SemiR_closure)
apply(simp add:is_healthy_def R2_def R2s_def R1_extend_AndP[THEN sym] usubst typing defined closure)
apply(simp add:R1_def tr_prefix_as_a PSubstPE_VarP_single_UNREST Z)
apply(simp add:is_healthy_def CSP_Post_R2_commute[THEN sym])
apply(metis assms Z is_healthy_def CSP_is_RHc RHc_is_R2)  
apply(subst closure)
apply(subst closure)
apply(simp add:assms Z,simp)
apply(subst closure,simp)
apply(simp add:closure typing defined assms)
apply(subst unrest)
apply(subst closure)
apply(simp add:typing defined closure assms Z)
apply(subst closure,simp)
apply(utp_poly_auto_tac)
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,tr\<down>,ref\<down>}"])
apply(simp add:ImpliesP_def SubstP_NotP[THEN sym] SubstP_OrP[THEN sym])
apply(subst unrest,simp add:typing defined closure unrest)
apply(subst unrest,simp add:typing defined closure unrest)
apply(subst unrest,simp add:typing defined closure unrest)
apply(subst unrest,simp add:typing defined closure unrest)
apply(simp add:CSP_Pre_def CSP_Post_def SubstP_OrP[THEN sym])
apply(subst unrest,simp add:typing defined closure unrest)
apply(subst unrest,simp add:typing defined closure unrest)
apply(subst UNREST_subset[of "{}"])
apply(simp add:typing defined closure unrest)
apply(utp_poly_auto_tac)
apply(simp)
apply(simp add:in_vars_diff)
apply(rule conjI) defer
apply(rule conjI) defer
apply (smt Diff_iff UnI2 Un_commute Un_def in_member inf_sup_aci(5) subsetI sup_commute)
apply(rule unrest,simp add:typing closure)
apply(rule unrest)
apply(subst UNREST_PEXPR_subset[of "NON_REL_VAR"],simp_all add:Z assms typing defined closure unrest)
apply(rule unrest,simp add:typing closure)
apply(rule unrest)
apply(subst UNREST_PEXPR_subset[of "NON_REL_VAR"],simp_all add:Z assms typing defined closure unrest)
apply(utp_rel_tac)+
done
also have "... = `false`"
apply(subst ExistsP_one_point_ty,simp_all add:typing defined closure unrest Z assms) defer
apply(simp add:usubst typing defined closure)
apply(subst usubst) defer
apply(subst usubst)
apply(subst usubst) back defer defer
apply(subst usubst) back back defer
apply(simp add:0)
apply(subst UNREST_PEXPR_subset[of "NON_REL_VAR"])
apply(simp_all add:typing defined closure unrest assms Z)
done
finally have B: "`(a \<rightarrow> P)[true/ok][false/wait][true/ok\<acute>][true/wait\<acute>][$tr/tr\<acute>][{a}/ref\<acute>]` = `false`" .
have "`STOP[true/ok][false/wait][true/ok\<acute>][true/wait\<acute>][$tr/tr\<acute>][{a}/ref\<acute>]` \<noteq> `(a \<rightarrow> P)[true/ok][false/wait][true/ok\<acute>][true/wait\<acute>][$tr/tr\<acute>][{a}/ref\<acute>]`"
by(subst A, subst B, utp_poly_auto_tac)
thus ?thesis by metis
qed

lemma Prefix_L1B:
assumes "a \<noteq> b" "\<D> a"  "\<D> b" "P \<in> REL" "P is CSP" "VAR \<sharp> a" "Q \<in> REL" "Q is CSP" "VAR \<sharp> b"
shows "`a \<rightarrow> P` \<noteq> `b \<rightarrow> Q`"
proof -
have Z : "NON_REL_VAR \<sharp> a" "NON_REL_VAR \<sharp> b" "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>, wait\<down>\<acute>, ref\<down>\<acute>} \<sharp> a" "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>, wait\<down>\<acute>, ref\<down>\<acute>} \<sharp> b" "{tr\<acute>\<down>} \<sharp> a" "{tr\<acute>\<down>} \<sharp> b" "{wait\<acute>\<down>} \<sharp> a" "{wait\<acute>\<down>} \<sharp> b" "{ref\<down>\<acute>} \<sharp> a" "{ref\<down>\<acute>} \<sharp> b" 
    by(auto intro: assms UNREST_PEXPR_subset)
have 0: "`$tr=$tr`=`true`" by(utp_poly_auto_tac)
have "`CSP_Post(a \<rightarrow> P)[true/wait\<acute>][$tr/tr\<acute>]` = 
  `(((($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>) ; (CSP_Pre(P) \<Rightarrow> CSP_Post(P))[true/wait\<acute>])[$tr/tr\<acute>] \<or>
     (a[true/wait\<acute>][$tr/tr\<acute>] \<notin> $ref\<acute>))`"
apply(subst Prefixed_post,simp_all add:assms ImpliesP_def)
apply(auto intro: assms UNREST_PEXPR_subset)
apply(simp add:usubst typing defined closure 0)
apply(simp add:SubstP_SemiR_right typing closure defined unrest)
apply(subst OrP_comm) back
apply(subst OrP_assoc)
apply(simp add:SubstP_NotP[THEN sym] SubstP_OrP[THEN sym] SemiR_OrP_distl[THEN sym] ImpliesP_def[THEN sym])
done
also have "... = `(a[true/wait\<acute>][$tr/tr\<acute>] \<notin> $ref\<acute>)`"
proof-
have 0: "P = R1(P)" by (metis assms is_healthy_def CSP_is_RHc RHc_is_R1)
show ?thesis
apply(subst Seq_tr_preserve)
apply(simp_all add:assms typing defined closure Z)
apply(simp add:CSP_Post_def CSP_Pre_def ImpliesP_def)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(simp_all add:typing defined closure unrest assms)
apply(utp_poly_auto_tac)
apply(metis prefixI')
apply(simp add:CSP_Pre_def CSP_Post_def ImpliesP_def SubstP_OrP[THEN sym])
apply(subst 0)
apply(subst 0) back
apply(simp add:R1_def usubst typing defined closure AndP_OrP_distr[THEN sym])
apply(simp add:R1_def[THEN sym])
apply (metis (lifting, no_types) Healthy_intro R1_idempotent)
done
qed
also have "... = `(a \<notin> $ref\<acute>)`"
by (metis PSubstPE_VarP_single_UNREST Z(5) Z(7))
finally have A: "`CSP_Post(a \<rightarrow> P)[true/wait\<acute>][$tr/tr\<acute>]` = `(a \<notin> $ref\<acute>)`" .
have "`CSP_Post(b \<rightarrow> Q)[true/wait\<acute>][$tr/tr\<acute>]` = 
  `(((($tr ^ \<langle>b\<rangle> = $tr\<acute>) \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>) ; (CSP_Pre(Q) \<Rightarrow> CSP_Post(Q))[true/wait\<acute>])[$tr/tr\<acute>] \<or>
     (b[true/wait\<acute>][$tr/tr\<acute>] \<notin> $ref\<acute>))`"
apply(subst Prefixed_post,simp_all add:assms ImpliesP_def)
apply(auto intro: assms UNREST_PEXPR_subset)
apply(simp add:usubst typing defined closure 0)
apply(simp add:SubstP_SemiR_right typing closure defined unrest)
apply(subst OrP_comm) back
apply(subst OrP_assoc)
apply(simp add:SubstP_NotP[THEN sym] SubstP_OrP[THEN sym] SemiR_OrP_distl[THEN sym] ImpliesP_def[THEN sym])
done
also have "... = `(b[true/wait\<acute>][$tr/tr\<acute>] \<notin> $ref\<acute>)`"
proof-
have 0: "Q = R1(Q)" by (metis assms is_healthy_def CSP_is_RHc RHc_is_R1)
show ?thesis
apply(subst Seq_tr_preserve)
apply(simp_all add:assms typing defined closure Z)
apply(simp add:CSP_Post_def CSP_Pre_def ImpliesP_def)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(simp_all add:typing defined closure unrest assms)
apply(utp_poly_auto_tac)
apply(metis prefixI')
apply(simp add:CSP_Pre_def CSP_Post_def ImpliesP_def SubstP_OrP[THEN sym])
apply(subst 0)
apply(subst 0) back
apply(simp add:R1_def usubst typing defined closure AndP_OrP_distr[THEN sym])
apply(simp add:R1_def[THEN sym])
apply (metis (lifting, no_types) Healthy_intro R1_idempotent)
done
qed
also have "... = `(b \<notin> $ref\<acute>)`"
by (metis PSubstPE_VarP_single_UNREST Z(6) Z(8))
finally have B: "`CSP_Post(b \<rightarrow> Q)[true/wait\<acute>][$tr/tr\<acute>]` = `(b \<notin> $ref\<acute>)`" .
have C: "`a \<notin> {a}` = `false`"
by utp_poly_auto_tac
from assms(1) assms(6) assms(9) have D: "`b \<notin> {a}` = `true`"
apply(utp_poly_auto_tac)
apply (metis UNREST_PEXPR_def binding_override_simps(10))
done
have "`(a \<notin> $ref\<acute>)[{a}/ref\<acute>]` \<noteq> `(b \<notin> $ref\<acute>)[{a}/ref\<acute>]`"
apply(simp add:usubst typing defined closure)
apply(subst usubst) defer
apply(subst usubst) 
apply(subst typing,simp_all add:typing closure defined assms) 
apply(subst usubst)  
apply(subst usubst) back
apply(subst usubst) back back back back defer
apply(subst usubst) back back
apply(subst typing,simp_all add:typing closure defined assms) 
apply(subst PSubstPE_VarP_single_UNREST,simp add:Z typing defined closure erasure)
apply(subst PSubstPE_VarP_single_UNREST,simp add:Z typing defined closure erasure)
apply(subst C)
apply(subst D)
apply (metis TrueP_noteq_FalseP)
done
hence "`(a \<notin> $ref\<acute>)` \<noteq> `(b \<notin> $ref\<acute>)`" 
by metis
hence "`CSP_Post(a \<rightarrow> P)[true/wait\<acute>][$tr/tr\<acute>]` \<noteq> `CSP_Post(b \<rightarrow> Q)[true/wait\<acute>][$tr/tr\<acute>]`"
by(metis A B)
thus ?thesis 
by metis
qed

lemma Prefix_precondition_alt: 
assumes "P \<in> REL" "P is CSP" "NON_REL_VAR \<sharp> a" "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>, wait\<down>\<acute>} \<sharp> a" "D\<^sub>0 \<sharp> a" "D\<^sub>1 \<sharp> a" "\<D> a" "{ref\<down>} \<sharp> P"
shows "`CSP_Pre(a \<rightarrow> P)` = `CSP_Pre(P)[($tr^\<langle>a\<rangle>)/tr]`"
proof-
have Z : "{tr\<acute>\<down>} \<sharp> a"  "{tr\<down>} \<sharp> a"
    by(auto intro: assms UNREST_PEXPR_subset)
have 0 : "D\<^sub>0 = (D\<^sub>0 - {tr\<down>}) \<union> {tr\<down>}"
by(auto,simp add:typing defined closure)
have 1: "`($tr ^ \<langle>a\<rangle> = $tr\<acute>)[$tr\<acute>\<acute>/tr\<acute>]` = `$tr ^ \<langle>a\<rangle> = $tr\<acute>\<acute>`"
apply(subst usubst,simp add:typing closure defined)
apply(subst usubst)
apply(subst usubst) back
apply(subst usubst,simp_all add:typing closure defined)
apply(subst usubst) back back back
apply(simp_all add:typing closure defined)
apply(simp add:typing closure defined usubst)
apply (metis Z PSubstPE_VarP_single_UNREST)
done
have L:"in REL_VAR = D\<^sub>0" 
by (metis Un_empty_right in_out_UNDASHED_DASHED(1) in_out_UNDASHED_DASHED(3) in_vars_union)
have M:"in OKAY = {ok\<down>}"
by(utp_rel_auto_tac)
have N:"in REA = {wait\<down>,tr\<down>,ref\<down>}"
by(utp_rel_auto_tac)
have "`CSP_Pre(a \<rightarrow> P)` = `(\<forall>tr\<acute>\<acute>. \<not>((($tr^\<langle>a\<rangle>=$tr\<acute>) \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>)[$tr\<acute>\<acute>/tr\<acute>];((\<not>CSP_Pre(P))[$tr\<acute>\<acute>/tr])))`"
apply(subst Prefixed_pre,simp_all add:assms)
apply(subst SemiR_extract_variable_id[of "tr\<down>"],simp_all add:typing defined closure unrest assms ForallP_def)
apply(simp add:erasure typing defined closure)
done
also have "... =  `(\<forall>tr\<acute>\<acute>. \<not>((($tr\<acute>\<acute>=$tr^\<langle>a\<rangle>) \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>);((\<not>CSP_Pre(P))[$tr\<acute>\<acute>/tr])))`"
apply(subst SubstP_AndP)
apply(subst 1)
apply(subst PEqualP_sym)
apply(simp add:usubst typing defined closure)
done
also have "... = `\<not> (\<exists> tr\<acute>\<acute> .
         II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub> ; (\<not> CSP_Pre (P))[$tr\<acute>\<acute>/tr] \<and>
         ($tr\<acute>\<acute> = $tr ^ \<langle>a\<rangle>))`"
apply(subst SemiR_AndP_left_DASHED)
apply(simp add:unrest assms typing defined closure)
apply(simp_all add:typing closure defined)
apply(simp add:ForallP_def)
apply(subst AndP_comm,simp)
done
also have "... = `CSP_Pre(P)[($tr^\<langle>a\<rangle>)/tr]`"
apply(subst ExistsP_one_point_ty,simp_all add:typing defined closure unrest Z assms) defer
apply(subst SkipRA_left_as_ExistsP[of _ "D\<^sub>0 - {tr\<down>}"])
apply(simp_all add:typing defined closure unrest)
apply(subst ExistsP_ident) defer
apply(subst SubstP_twice_2)
apply(simp add:typing closure defined unrest assms)
apply(simp add:usubst typing defined closure)
apply(subst usubst,simp add:typing defined closure unrest) defer
apply(subst usubst) back back defer
apply(simp)
apply(subst unrest)
apply(simp add:typing defined closure unrest)
apply(subst unrest)
apply(subst UNREST_PEXPR_subset[of "NON_REL_VAR"],simp_all add:typing closure defined assms)
apply(simp add:typing defined closure unrest)
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ref\<down>}"]) defer defer
apply(simp)defer
apply(simp add:in_vars_diff)
apply(rule conjI) defer
apply(rule conjI) defer
apply(simp_all add:L M N)
apply(utp_poly_auto_tac) defer
apply(utp_poly_auto_tac)
apply(utp_poly_auto_tac)
apply(rule unrest,simp add:typing defined closure unrest)
apply(simp add:CSP_Pre_def)
apply(rule unrest,simp add:typing defined closure unrest)
apply(rule unrest,simp add:typing defined closure unrest)
apply(rule unrest,simp add:typing defined closure unrest)
apply(subst UNREST_subset[of "{ref\<down>}"]) defer
apply(utp_poly_auto_tac,simp_all add:assms)
done
finally show ?thesis .
qed

lemma Prefix_L1D: 
assumes "`a \<rightarrow> P` = `a \<rightarrow> Q`" "P \<in> REL" "Q \<in> REL" "P is CSP" "Q is CSP" "{ref\<down>}\<sharp> P" "{ref\<down>}\<sharp>Q" "NON_REL_VAR \<sharp> a" "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>, wait\<down>\<acute>} \<sharp> a" "D\<^sub>0 \<sharp> a" "D\<^sub>1 \<sharp> a" "\<D> a"
shows "`P` = `Q`"
oops

(* Modification by Frank Zeyda *)

(* I changed REL into WF_RELATION due to an issue with overloading. Review! *)

lemma Nondet_L1:
  assumes "P \<in> WF_RELATION" 
  shows "`P \<sqinter> P` = `P`"
by (metis sup_idem)

lemma Nondet_L2: 
  assumes "P \<in> REL" "Q \<in> WF_RELATION"
  shows "`P \<sqinter> Q` = `Q \<sqinter> P `"
by (metis sup_commute)

lemma Nondet_L3: 
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "R \<in> WF_RELATION"
  shows "`P \<sqinter> (Q \<sqinter> R)` = `(P \<sqinter> Q) \<sqinter> R`"
by (metis sup_assoc)

lemma Nondet_L4:
  assumes "P \<in> REL" "Q \<in> REL" "P is CSP" "Q is CSP"  "NON_REL_VAR \<sharp> a" "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>, wait\<down>\<acute>} \<sharp> a"
  shows "`a \<rightarrow> (P \<sqinter> Q)` = `(a \<rightarrow> P) \<sqinter> (a \<rightarrow> Q)`"
proof-
have Z :"{ok\<down>}\<sharp>a" "{wait\<down>}\<sharp>a" "{ok\<down>\<acute>}\<sharp>a" "{tr\<down>}\<sharp>a" "{tr\<down>\<acute>}\<sharp>a" 
by(subst UNREST_PEXPR_subset[of "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>, wait\<down>\<acute>}"],simp_all add:typing closure defined assms)+
show ?thesis
apply(subst CSP_Design[of "`a \<rightarrow> (P \<sqinter> Q)`"])
apply(subst Prefixed_CSP,subst Internal_CSP,simp_all add:assms)defer defer
apply(subst Internal_design,subst Prefixed_CSP,simp_all add:assms closure)defer
apply(subst Prefixed_CSP,simp_all add:assms) defer
apply(simp add:PrefixCSP_def closure assms)
apply(simp add:PrefixCSP_def closure assms)
apply(subst Prefixed_design,simp_all add:typing closure defined assms Internal_CSP)defer
apply(subst Prefixed_design,simp_all add:typing closure defined assms Internal_CSP)defer
apply(simp add:assms Internal_pre Internal_post DesignREA_pre DesignREA_post demorgan2)
apply(simp add:ImpliesP_def)
apply(subst Healthy_simp[of _ "R2"]) defer
apply(subst Healthy_simp[of _ "R2"]) defer
apply(subst CSP_Pre_def,simp add:SubstP_SemiR_left SubstP_SemiR_right typing defined closure unrest)
apply(subst CSP_Post_def,simp add:SubstP_OrP SubstP_SemiR_left SubstP_SemiR_right typing defined closure unrest)
apply(simp add:usubst typing defined closure)
apply(simp add: PSubstPE_VarP_single_UNREST Z)
apply(subst DesignREA_Pre_Post)
apply(subst AndP_comm) back back
apply(simp add:AndP_OrP_distr)
apply(subst SubstP_VarP_single_UNREST,simp add:CSP_Pre_def CSP_Post_def typing closure defined unrest)+
apply(simp add:AndP_contra)
apply(simp add:AndP_OrP_distr[THEN sym])
apply(subst AndP_comm) back back back back
apply(subst DesignREA_Pre_Post[THEN sym])
apply(simp add: Prefixed_pre assms SemiR_OrP_distl[THEN sym] demorgan1[THEN sym])
apply(simp add:Prefixed_post assms OrP_assoc[THEN sym])
apply(subst OrP_comm,simp add:OrP_assoc[THEN sym]) back
apply(subst OrP_comm,simp add:OrP_assoc[THEN sym]) back back back 
apply(subst OrP_comm,simp add:OrP_assoc[THEN sym]) back
apply(subst OrP_assoc)
apply(simp add:SemiR_OrP_distl[THEN sym])
apply(subst DesignREA_Pre_Post) back
apply(subst AndP_comm) back back back back back back
apply(simp add:AndP_OrP_distr AndP_contra)
apply(simp add:AndP_OrP_distr[THEN sym])
apply(subst AndP_comm) back back back back back back back back back
apply(subst DesignREA_Pre_Post[THEN sym])
apply(subst OrP_comm) back back back back
apply(simp add:OrP_assoc[THEN sym] SemiR_OrP_distl[THEN sym])
apply(subst UNREST_PEXPR_subset[of "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>, wait\<down>\<acute>}"],simp_all add:assms typing defined closure)defer
apply(subst CSP_Pre_def,simp add:SubstP_SemiR_left SubstP_SemiR_right typing closure defined unrest)
apply(simp add:usubst typing defined closure)
apply(simp add: PSubstPE_VarP_single_UNREST Z)
apply(subst SubstP_VarP_single_UNREST,simp add:CSP_Pre_def CSP_Post_def unrest typing closure defined)+
defer
apply(simp add:is_healthy_def CSP_Post_R2_commute[THEN sym] R2_OrP)
apply(subst Healthy_simp[of _ "R2"]) defer
apply(subst Healthy_simp[of _ "R2"]) back defer
apply(simp add:R2_def R2s_def R1_def usubst typing defined closure AndP_assoc[THEN sym] tr_prefix_as_nil)
apply(simp add:PSubstPE_VarP_single_UNREST Z) defer 
apply(subst R2_SemiR_closure) defer
apply(simp add:is_healthy_def R2_OrP CSP_Pre_R2_commute[THEN sym])
apply(metis assms is_healthy_def CSP_is_RHc RHc_is_R2) defer
apply(simp_all add:closure assms typing defined)
apply(subst R2_SemiR_closure)
apply(simp add:is_healthy_def R2_def R2s_def usubst typing closure defined R1_extend_AndP[THEN sym])
apply(simp add:R1_def tr_prefix_as_a PSubstPE_VarP_single_UNREST Z)
apply(simp add:is_healthy_def R2_OrP CSP_Post_R2_commute[THEN sym])
apply(metis assms is_healthy_def CSP_is_RHc RHc_is_R2)
apply(simp_all add:closure typing defined assms)
apply(utp_rel_tac)
apply(simp add:closure assms)
done
qed

lemma General_L1:
  assumes "P \<in> REL" "P is CSP"
  shows "P \<box> P = P"
by(simp add: External_design assms,subst CSP_Design[THEN sym],simp_all add:assms)

lemma General_L2:
  assumes "P \<in> REL" "P is CSP""Q \<in> REL" "Q is CSP"
  shows "P \<box> Q = Q \<box> P"
by(simp add:External_design assms,metis AndP_comm OrP_comm)

lemma General_L3:
  assumes "P \<in> REL" "P is CSP""Q \<in> REL" "Q is CSP""R \<in> REL" "R is CSP"
  shows "(P \<box> Q) \<box> R = P \<box> (Q \<box> R)"
proof-
have 0: "R2(P) = P" "R2(Q) = Q" "R2(R) = R"
apply(metis assms is_healthy_def CSP_is_RHc RHc_is_R2)+
done
have "(P \<box> Q) \<box> R =  `RHc (CSP_Pre(P) \<and> CSP_Pre(Q) \<and> CSP_Pre(R) \<turnstile>
         ((CSP_Post(P) \<and> CSP_Post(Q) \<and> CSP_Post(R)) 
            \<lhd> ($tr\<acute> = $tr) \<and> $wait\<acute> \<rhd> (CSP_Post(P) \<or> CSP_Post(Q) \<or> CSP_Post(R))))`"
apply(subst External_design)
apply(simp add:assms)+
apply(subst External_design)
apply(simp add:assms closure)+
apply(subst DesignREA_CSP)
apply(simp add:closure typing defined unrest CSP_Pre_def CSP_Post_def)+
apply(simp add:assms)
apply(subst DesignREA_pre,simp add:CSP_Pre_NotP CSP_Pre_AndP CSP_Pre_twice R2_OrP CSP_Pre_R2_commute[THEN sym])
apply(simp add: demorgan2[THEN sym] AndP_assoc[THEN sym] 0)
apply(subst DesignREA_Pre_Post)
apply(simp add: DesignREA_post ImpliesP_def CSP_Post_OrP CSP_Post_NotP CSP_Post_AndP CSP_Post_CondR CSP_Post_twice CSP_Post_Pre)
apply(simp add:demorgan2 R2_OrP R2_CondR_alt)
apply(subst R2_def) back back back
apply(subst R2_def) back back back back back back back back
apply(simp add:R2_AndP CSP_Pre_R2_commute[THEN sym] CSP_Post_R2_commute[THEN sym] 0)
apply(subst CSP_Post_def) back back
apply(subst CSP_Post_def) back back
apply(subst CSP_Post_def) back back back back back back back
apply(subst CSP_Post_def) back back back back back back back
apply(simp add:R2s_AndP R1_extend_AndP[THEN sym])
apply(simp add:R2s_def usubst typing defined closure R1_def tr_prefix_as_nil)
apply(simp add:CondR_def AndP_OrP_distl AndP_OrP_distr AndP_assoc[THEN sym] OrP_assoc[THEN sym])
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym] AndP_contra) back back back back back
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym] AndP_contra) back back back back back
apply(subst OrP_comm,simp add:OrP_assoc[THEN sym])
apply(subst AndP_assoc,simp add:AndP_contra)
apply(subst AndP_assoc,simp add:AndP_contra)
apply(subst AndP_assoc) back back back back
apply(subst AndP_assoc,simp add:AndP_contra)
apply(subst AndP_assoc) back back back back
apply(subst AndP_assoc,simp add:AndP_contra)
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back
apply(subst AndP_comm,simp add:AndP_contra)
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back
apply(subst AndP_comm,simp add:AndP_contra)
apply(subst AndP_assoc) back back back back back
apply(subst AndP_assoc) back back back back
apply(subst AndP_comm,simp add:AndP_contra)
apply(simp add:AndP_OrP_distl[THEN sym])
apply(subst AndP_assoc) back back
apply(subst AndP_assoc) back
apply(subst DesignREA_Pre_Post[THEN sym])
apply(subst OrP_assoc) back
apply(subst OrP_assoc)
apply(simp add:AndP_OrP_distl[THEN sym])
apply(subst OrP_comm) back back
apply(subst AndP_assoc) back
apply(subst AndP_assoc) back back
apply(subst AndP_assoc,simp)
apply(simp add:AndP_assoc)
done
moreover have "P \<box> (Q \<box> R) =  `RHc (CSP_Pre(P) \<and> CSP_Pre(Q) \<and> CSP_Pre(R) \<turnstile>
         ((CSP_Post(P) \<and> CSP_Post(Q) \<and> CSP_Post(R)) 
            \<lhd> ($tr\<acute> = $tr) \<and> $wait\<acute> \<rhd> (CSP_Post(P) \<or> CSP_Post(Q) \<or> CSP_Post(R))))`"
apply(subst General_L2,simp_all add:assms closure External_CSP)
apply(subst External_design)
apply(simp add:assms)+
apply(subst External_design)
apply(simp add:assms closure)+
apply(subst DesignREA_CSP)
apply(simp add:closure typing defined unrest CSP_Pre_def CSP_Post_def)+
apply(simp add:assms)
apply(subst DesignREA_pre,simp add:CSP_Pre_NotP CSP_Pre_AndP CSP_Pre_twice R2_OrP CSP_Pre_R2_commute[THEN sym])
apply(simp add: demorgan2[THEN sym] AndP_assoc[THEN sym] 0)
apply(subst DesignREA_Pre_Post)
apply(simp add: DesignREA_post ImpliesP_def CSP_Post_OrP CSP_Post_NotP CSP_Post_AndP CSP_Post_CondR CSP_Post_twice CSP_Post_Pre)
apply(simp add:demorgan2 R2_OrP R2_CondR_alt)
apply(subst R2_def) back back back
apply(subst R2_def) back back back back back back back back
apply(simp add:R2_AndP CSP_Pre_R2_commute[THEN sym] CSP_Post_R2_commute[THEN sym] 0)
apply(subst CSP_Post_def) back back
apply(subst CSP_Post_def) back back
apply(subst CSP_Post_def) back back back back back back back
apply(subst CSP_Post_def) back back back back back back back
apply(simp add:R2s_AndP R1_extend_AndP[THEN sym])
apply(simp add:R2s_def usubst typing defined closure R1_def tr_prefix_as_nil)
apply(simp add:CondR_def AndP_OrP_distl AndP_OrP_distr AndP_assoc[THEN sym] OrP_assoc[THEN sym])
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym] AndP_contra) back back back back back
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym] AndP_contra) back back back back back
apply(subst OrP_comm,simp add:OrP_assoc[THEN sym])
apply(subst AndP_assoc,simp add:AndP_contra)
apply(subst AndP_assoc,simp add:AndP_contra)
apply(subst AndP_assoc) back back back back
apply(subst AndP_assoc,simp add:AndP_contra)
apply(subst AndP_assoc) back back back back
apply(subst AndP_assoc,simp add:AndP_contra)
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back
apply(subst AndP_comm,simp add:AndP_contra)
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back
apply(subst AndP_comm,simp add:AndP_contra)
apply(subst AndP_assoc) back back back back back
apply(subst AndP_assoc) back back back back
apply(subst AndP_comm,simp add:AndP_contra)
apply(simp add:AndP_OrP_distl[THEN sym])
apply(subst AndP_assoc) back back
apply(subst AndP_assoc) back
apply(subst DesignREA_Pre_Post[THEN sym])
apply(subst OrP_assoc) back
apply(subst OrP_assoc)
apply(simp add:AndP_OrP_distl[THEN sym])
apply(subst OrP_comm) back back
apply(subst AndP_assoc) back
apply(subst AndP_assoc) back back
apply(subst AndP_assoc,simp)
apply(subst AndP_assoc) back back back back
apply(simp add:CondR_def[THEN sym])
apply(subst AndP_assoc)
apply(subst AndP_comm) back
apply(subst AndP_assoc) back
apply(subst AndP_comm) back back back
apply(subst OrP_assoc)
apply(subst OrP_comm,simp) back
done
ultimately show ?thesis
by metis
qed

lemma General_L4:
  assumes "P \<in> REL" "P is CSP"
  shows "P \<box> STOP = P"
apply(subst External_design,simp_all add:assms closure Stop_CSP Stop_pre Stop_post)
apply(subst CondR_def)
apply(subst AndP_assoc)
apply(subst AndP_comm) back
apply(subst AndP_assoc[THEN sym])
apply(subst AndP_idem)
apply(subst AndP_comm) back back back
apply(simp add:AndP_OrP_distr AndP_contra)
apply(subst AndP_comm)
apply(subst AndP_comm) back back
apply(subst CondR_def[THEN sym])
apply(subst CondR_idem)
apply(subst CSP_Design[THEN sym])
apply(simp_all add:assms)
done

lemma General_L6:
    assumes "P \<in> REL" "P is CSP""Q \<in> REL" "Q is CSP""R \<in> REL" "R is CSP"
    shows "`P \<box> (Q \<sqinter> R)` = `(P \<box> Q) \<sqinter> (P \<box> R)`"
proof-
have 0: "R2(P) = P" "R2(Q) = Q" "R2(R) = R"
apply(metis assms is_healthy_def CSP_is_RHc RHc_is_R2)+
done
show ?thesis
apply(simp add:Internal_design assms External_design closure DesignREA_CSP)
apply(subst External_design,simp_all add:assms closure)
apply(subst DesignREA_CSP)
apply(simp add:unrest CSP_Pre_def closure assms typing)
apply(simp add:unrest CSP_Post_def closure assms typing)
apply(simp_all add:DesignREA_pre CSP_Pre_NotP CSP_Pre_AndP CSP_Pre_twice R2_OrP CSP_Pre_R2_commute[THEN sym] 0)
apply(simp add:demorgan1, subst DesignREA_Pre_Post)
apply(simp add: DesignREA_post ImpliesP_def demorgan2 CSP_Post_NotP CSP_Post_OrP CSP_Post_Pre CSP_Post_twice R2_OrP CSP_Post_R2_commute[THEN sym] CSP_Pre_R2_commute[THEN sym])
apply(simp add: OrP_assoc[THEN sym] CondR_def AndP_OrP_distr AndP_OrP_distl AndP_assoc[THEN sym] 0)
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back
apply(subst AndP_comm,simp add:AndP_contra)
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back back
apply(subst AndP_comm,simp add:AndP_contra)
apply(subst OrP_comm,simp add:OrP_assoc[THEN sym])
apply(subst OrP_comm,simp add:OrP_assoc[THEN sym])
apply(subst OrP_comm,simp add:OrP_assoc[THEN sym])
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back
apply(subst AndP_comm,simp add:AndP_contra)
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back back
apply(subst AndP_comm,simp add:AndP_contra)
apply(simp add:AndP_OrP_distl[THEN sym])
apply(subst AndP_assoc) back back
apply(subst AndP_assoc) back
apply(subst DesignREA_Pre_Post[THEN sym])
apply(subst OrP_comm,simp add:OrP_assoc[THEN sym])
apply(subst OrP_comm,simp add:OrP_assoc[THEN sym])
apply(subst OrP_assoc)
apply(simp add:AndP_OrP_distl[THEN sym])
apply(subst AndP_assoc,simp add:CondR_def[THEN sym])
apply(subst AndP_assoc[of "`$tr\<acute>=$tr`"])+
apply(simp add:CondR_def[THEN sym])
apply(subst Internal_design,simp_all add:assms closure typing defined)
apply(simp add:DesignREA_CSP assms closure typing defined unrest CSP_Pre_def CSP_Post_def)
apply(simp add:DesignREA_CSP assms closure typing defined unrest CSP_Pre_def CSP_Post_def)
apply(simp add:DesignREA_pre DesignREA_post CSP_Pre_NotP CSP_Pre_OrP CSP_Pre_twice CSP_Pre_AndP R2_OrP CSP_Pre_R2_commute[THEN sym] 0)
apply(simp add:ImpliesP_def CSP_Post_NotP CSP_Post_AndP CSP_Post_OrP CSP_Post_CondR CSP_Post_twice CSP_Post_Pre R2_CondR_alt R2_OrP demorgan2 CSP_Pre_R2_commute[THEN sym] 0)
apply(subst R2_def) back
apply(subst R2_def) back back back back
apply(simp add:R2s_AndP R1_extend_AndP[THEN sym] R2_AndP CSP_Post_R2_commute[THEN sym] 0)
apply(subst CSP_Post_def) back back back back back back back back
apply(subst CSP_Post_def) back back back back back back back back
apply(subst CSP_Post_def) back back back back back back back back back back back back
apply(subst CSP_Post_def) back back back back back back back back back back back back
apply(simp add:R2s_def usubst typing defined closure R1_def tr_prefix_as_nil)
apply(simp add:demorgan1 AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back back back back
apply(subst AndP_assoc,simp)
apply(subst DesignREA_Pre_Post) back
apply(simp_all add:AndP_OrP_distl AndP_OrP_distr AndP_assoc[THEN sym])
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back
apply(subst AndP_comm) back back back back back back back back back
apply(simp add:AndP_contra)
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back back
apply(subst AndP_comm,simp add:AndP_contra)
apply(subst OrP_comm,simp add:OrP_assoc[THEN sym]) back
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back
apply(subst AndP_comm,simp add:AndP_contra)
apply(simp add:AndP_OrP_distl[THEN sym])
apply(subst AndP_assoc) back back back
apply(subst AndP_assoc) back back
apply(subst DesignREA_Pre_Post[THEN sym])
apply(subst CondR_def) back
apply(subst CondR_def) back
apply(subst OrP_assoc) back
apply(subst OrP_comm) back back back back back
apply(simp add:OrP_assoc[THEN sym])
apply(subst OrP_assoc) back
apply(simp add:AndP_OrP_distl[THEN sym])
apply(subst CondR_def[THEN sym])
apply(subst OrP_assoc[THEN sym])
apply(subst OrP_comm) back back back back back
apply(simp add:OrP_assoc[THEN sym],simp add:OrP_assoc)
done
qed

lemma General_L7:
    assumes "P \<in> REL" "P is CSP""Q \<in> REL" "Q is CSP""R \<in> REL" "R is CSP"
    shows "`P \<sqinter> (Q \<box> R)` = `(P \<sqinter> Q) \<box> (P \<sqinter> R)`"
proof - 
have 0: "R2(P) = P" "R2(Q) = Q" "R2(R) = R"
apply(metis assms is_healthy_def CSP_is_RHc RHc_is_R2)+
done
have "`P \<sqinter> (Q \<box> R)` = ` RHc ((CSP_Pre(P) \<and> CSP_Pre(Q) \<and> CSP_Pre(R)) \<turnstile>
         (CSP_Post(P) \<or> ((CSP_Post(Q) \<and> CSP_Post(R)) \<lhd> ($tr\<acute> = $tr) \<and> $wait\<acute> \<rhd> (CSP_Post(Q) \<or> CSP_Post (R)))))`"
apply(simp add:External_design Internal_design assms)
apply(subst Internal_design,simp_all add:assms closure)
apply(simp add:DesignREA_CSP unrest typing CSP_Pre_def CSP_Post_def assms)
apply(simp add:DesignREA_pre CSP_Pre_OrP CSP_Pre_NotP CSP_Pre_AndP CSP_Pre_twice R2_OrP CSP_Pre_R2_commute[THEN sym] 0)
apply(simp add:DesignREA_post CSP_Post_OrP CSP_Post_NotP CSP_Post_AndP CSP_Post_twice CSP_Post_Pre ImpliesP_def demorgan2 R2_OrP CSP_Post_CondR R2_CondR_alt)
apply(subst R2_def) back back back
apply(simp add:R2_AndP CSP_Pre_R2_commute[THEN sym] CSP_Post_R2_commute[THEN sym] 0 R2s_AndP R1_extend_AndP[THEN sym])
apply(subst CSP_Post_def) back back back
apply(subst CSP_Post_def) back back back
apply(simp add:R2s_def usubst typing defined closure R1_def tr_prefix_as_nil)
apply(simp add:demorgan1 demorgan2 AndP_assoc[THEN sym])
apply(subst DesignREA_Pre_Post)
apply(simp add:AndP_OrP_distl AndP_OrP_distr AndP_assoc[THEN sym] CondR_def)
apply(subst OrP_comm,simp add:OrP_assoc[THEN sym])
apply(simp add:AndP_contra)
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back
apply(subst AndP_comm,simp add:AndP_contra)
apply(simp add:AndP_OrP_distl[THEN sym])
apply(subst AndP_assoc) back back
apply(subst AndP_assoc) back
apply(subst DesignREA_Pre_Post[THEN sym])
apply(subst AndP_assoc) back
apply(subst OrP_assoc,simp add:AndP_OrP_distl[THEN sym])
apply(subst OrP_assoc)
apply(subst CondR_def[THEN sym])
apply(subst OrP_comm) back
apply(subst AndP_assoc) back back
apply(subst CondR_def[THEN sym],simp)
done
moreover have "`(P \<sqinter> Q) \<box> (P \<sqinter> R)` = undefined"
apply(simp add: Internal_design assms)
apply(subst External_design,simp_all add:assms closure)
apply(simp add:DesignREA_CSP assms closure typing unrest CSP_Pre_def CSP_Post_def)
apply(simp add:DesignREA_CSP assms closure typing unrest CSP_Pre_def CSP_Post_def)
apply(simp add:DesignREA_pre CSP_Pre_NotP CSP_Pre_AndP CSP_Pre_twice R2_OrP CSP_Pre_R2_commute[THEN sym] 0)
apply(simp add:demorgan1 AndP_assoc[THEN sym])
apply(subst AndP_assoc) back
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back
apply(subst AndP_assoc,simp)
apply(simp add:DesignREA_post CSP_Post_CondR CSP_Post_NotP CSP_Post_AndP CSP_Post_OrP CSP_Post_twice CSP_Post_Pre ImpliesP_def demorgan2 R2_OrP CSP_Post_R2_commute[THEN sym] CSP_Pre_R2_commute[THEN sym] 0 OrP_assoc[THEN sym])
apply(simp add:CondR_def AndP_OrP_distl AndP_OrP_distr AndP_assoc[THEN sym] OrP_assoc[THEN sym])
apply(subst DesignREA_Pre_Post)
apply(subst AndP_comm) back back back back
apply(simp add:AndP_OrP_distr AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back back
apply(subst AndP_comm,simp add:AndP_contra)
apply(subst AndP_assoc) back back back back
apply(subst AndP_comm,simp add:AndP_contra)
apply(subst AndP_assoc) back back back back
apply(subst AndP_comm,simp add:AndP_contra)
apply(subst AndP_assoc) back back back back
apply(subst AndP_comm,simp add:AndP_contra)
apply(subst AndP_assoc) back back back
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back back back
apply(subst AndP_assoc) back back back back
apply(subst AndP_comm,simp add:AndP_contra)
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back back back
apply(subst AndP_comm,simp add:AndP_contra)
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back back back
apply(subst AndP_comm,simp add:AndP_contra)
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back back back
apply(subst AndP_comm,simp add:AndP_contra)
oops

lemma Divergence_L1 :
  assumes "P is CSP" "P \<in> REL"
  shows "`P \<sqinter> CHAOS` = `CHAOS`"
apply(subst Internal_design,simp_all add:assms closure Chaos_CSP Chaos_pre Chaos_post)
apply(subst Chaos_design,simp add:R1_def DesignREA_form demorgan2 R2_def R2s_def usubst typing defined closure)
done

lemma Divergence_L2D :
  assumes "P is CSP" "P \<in> REL"
  shows "`P \<box> CHAOS` = `CHAOS`"
proof-
have 0: "P = R1(P)"
by (metis assms is_healthy_def CSP_is_RHc RHc_is_R1)
show ?thesis
apply(simp add:External_design assms closure Chaos_CSP Chaos_pre Chaos_post R1_def)
apply(subst 0,simp add:CSP_Pre_def R1_def usubst typing defined closure demorgan2 AndP_OrP_distr)
apply(subst OrP_comm)
apply(subst AndP_comm,simp add:OrP_AndP_absorb)
apply(subst DesignREA_form)
apply(simp add:R2_def R2s_def usubst typing defined closure R1_def)
apply(subst AndP_comm) back back back back back back back back
apply(simp add:AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back back
apply(subst AndP_assoc) back back
apply(subst OrP_AndP_absorb)
apply(simp add:Chaos_design DesignREA_form R2_def R2s_def usubst typing defined closure R1_def)
apply(subst AndP_assoc) back back back back back
apply(subst AndP_assoc) back back back back
apply(subst OrP_AndP_absorb,simp)
done
qed

lemma Divergence_L3 :
  assumes "NON_REL_VAR \<sharp> a" "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>, wait\<down>\<acute>} \<sharp> a" "D\<^sub>1 \<sharp> a" "\<D> a"
  shows "`a \<rightarrow> CHAOS` \<noteq> `CHAOS`"
proof - 
have Z: "{tr\<down>}\<sharp>a" "{tr\<down>\<acute>}\<sharp>a"
  by(subst UNREST_PEXPR_subset[of "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>, wait\<down>\<acute>}"],simp_all add:assms typing defined closure)+
have 1: "`R2(CSP_Pre(CHAOS))` = `false`"
by(simp add:Chaos_pre R1_def R2s_def usubst typing defined closure R2_def)
have 2: "`R2(CSP_Pre(a \<rightarrow> CHAOS))` = `R1 (\<not> ($tr ^ \<langle>a\<rangle> \<le> $tr\<acute>))`"
proof -
have "`R2(CSP_Pre(a \<rightarrow> CHAOS))` = `R1 (\<not> (\<exists> tr\<acute>\<acute> . (($tr ^ \<langle>a\<rangle> = $tr\<acute>\<acute>) \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>) ; ($tr\<acute>\<acute> \<le> $tr\<acute>)))`"
apply(subst Prefixed_pre,simp_all add:assms closure Chaos_CSP Chaos_pre R1_def)
apply(subst R2_NotP)
apply(subst Healthy_simp[of _ "R2"])
apply(subst R2_SemiR_closure)
apply(simp_all add:closure typing defined is_healthy_def R2_def R2s_def)
apply(simp_all add:usubst typing defined closure)
apply(simp add:R1_extend_AndP[THEN sym])
apply(simp add:R1_def tr_prefix_as_a PSubstPE_VarP_single_UNREST Z) 
apply(simp_all add:R1_def)
apply(simp add:closure assms)
apply(subst SemiR_extract_variable_ty[of "tr" "tr\<acute>\<acute>"],simp_all add:typing defined unrest closure assms)
apply(simp add:usubst typing defined closure PSubstPE_VarP_single_UNREST Z)
done
also have "... = `R1 (\<not> (\<exists> tr\<acute>\<acute>. (($tr ^ \<langle>a\<rangle> = $tr\<acute>\<acute>) \<and> II\<^bsub>REL_VAR - REA - OKAY\<^esub>) ; (true \<and> ($tr\<acute>\<acute> \<le> $tr\<acute>))))`"
by simp
also have "... = `R1 (\<not> (\<exists> tr\<acute>\<acute> . ($tr\<acute>\<acute> = $tr ^ \<langle>a\<rangle>) \<and> ($tr\<acute>\<acute> \<le> $tr\<acute>)))`"
apply(subst SemiR_AndP_left_DASHED)
apply(simp add:typing defined closure unrest assms)
apply(subst SemiR_AndP_right_UNDASHED)
apply(simp add:typing defined closure unrest assms)
apply(simp)
apply(subst SemiR_SkipRA_left,simp_all add:typing defined closure unrest)
apply (metis PEqualP_sym)
done
also have "... = `R1 (\<not> ($tr ^ \<langle>a\<rangle> \<le> $tr\<acute>))`"
apply(subst AndP_comm,subst ExistsP_one_point_ty,simp_all add:typing defined closure unrest assms)
apply(subst unrest,simp_all add:typing defined closure unrest,subst unrest)
apply(subst UNREST_PEXPR_subset[of "NON_REL_VAR"],simp add:assms)
apply(simp_all add:typing defined closure unrest)
apply(simp add:R1_def usubst typing defined closure)
apply(subst usubst) defer
apply(subst usubst)
apply(subst usubst) back back back defer defer
apply(subst usubst) back back defer
apply(simp add:R1_def[THEN sym])
apply(simp_all add:typing defined closure assms)
done
finally show ?thesis .
qed
have "`R2(CSP_Pre(a \<rightarrow> CHAOS))[$tr/tr\<acute>]` \<noteq> `R2(CSP_Pre(CHAOS))[$tr/tr\<acute>]`"
apply(subst 1)
apply(subst 2)
apply (utp_poly_tac)
apply(subst UTypedef.InjU_inverse, metis UTypedef_Event UTypedef_ULIST)+
apply (simp add: inju defined typing)
done
thus ?thesis by metis
qed

definition CSP3:: "'a upred \<Rightarrow> 'a upred" where
"CSP3 P = `SKIP;P`"

definition CSP4:: "'a upred \<Rightarrow> 'a upred" where
"CSP4 P = `P;SKIP`"

lemma SemiR_Skip_left:
  assumes "P is CSP" "P \<in> REL" "{ref\<down>} \<sharp> `P \<^sub>f`"
  shows "P is CSP3"
proof -
have 0: "REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>} = REL_VAR - {wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>, ok\<down>, ok\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>}"
by(utp_poly_auto_tac)
have 1: "{wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>, ok\<down>, ok\<down>\<acute>} = {ref\<down>, ok\<down>,wait\<down>} \<union> { ref\<down>\<acute>, ok\<down>\<acute>, wait\<down>\<acute>}"
by(utp_poly_auto_tac)
have "`SKIP ; P` =`RHc((\<not> (( \<not> $wait\<acute> \<and> II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>,ok\<down>, ok\<down>\<acute>}\<^esub>) ;
             (\<not> $wait \<and> \<not> CSP_Pre(P))) \<turnstile>
         ( \<not> $wait\<acute> \<and> II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>,ok\<down>, ok\<down>\<acute>}\<^esub>) ;
         (II\<^bsub>REL_VAR - {ok\<down>, ok\<down>\<acute>}\<^esub> \<lhd> $wait \<rhd> CSP_Post (P))))`"
apply(subst Seq_comp_form,simp_all add:assms closure Skip_CSP)
apply(simp add:Skip_pre Skip_post 0)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing defined closure) back back back
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing defined closure) back back back back
apply(subst AndP_assoc, subst AndP_comm[of "`$tr\<acute>=$tr`"],subst AndP_assoc[THEN sym])
apply(subst AndP_assoc) back
apply(subst AndP_comm[of "`$tr\<acute>=$tr`"],simp add:AndP_assoc[THEN sym]) back
done
also have "... = P"
apply(subst AndP_comm)
apply(subst AndP_comm) back back
apply(simp add:SemiR_AndP_left_UNDASHED typing closure defined unrest urename)
apply(subst AndP_assoc,simp add:CondR_false_cond)
apply(subst SemiR_remove_middle_unrest1[of _ _ "{wait\<down>}"],simp_all add:typing closure defined unrest assms) defer defer
apply(subst SemiR_remove_middle_unrest1[of _ _ "{wait\<down>}"],simp_all add:typing closure defined unrest assms) defer defer
apply(subst SemiR_SkipRA_left,simp_all add:typing closure defined unrest) defer
apply(subst SemiR_SkipRA_left,simp_all add:typing closure defined unrest) defer
apply(subst CSP_Design[THEN sym],simp_all add:assms)
apply(subst UNREST_subset[of "-(REL_VAR - {wait\<down>,wait\<down>\<acute>,ref\<down>,ref\<down>\<acute>,ok\<down>,ok\<down>\<acute>})"],subst UNREST_SkipRA,simp_all add:typing defined closure)
apply(simp add:typing closure defined unrest CSP_Pre_def)
apply(simp add:typing closure defined unrest CSP_Post_def)
apply(simp add:CSP_Pre_def)
apply(subst SubstP_twice_3,simp_all add:typing closure defined) back
apply(simp add:typing defined closure unrest)
apply(simp add:typing defined closure usubst)
apply(subst unrest) defer
apply(subst SubstP_twice_3,simp_all add:typing closure defined) 
apply(simp add:typing defined closure unrest)
apply(simp add:typing defined closure usubst)
apply(subst unrest) defer
apply(subst UNREST_subset[of "{ref\<down>} \<union> {wait\<down>}"])
apply(subst UNREST_union)
apply(simp add:assms)
apply(subst unrest,simp_all add:typing closure defined unrest) defer
apply(simp add:CSP_Post_def)
apply(subst SubstP_twice_3,simp_all add:typing closure defined) back
apply(simp add:typing defined closure unrest)
apply(simp add:typing defined closure usubst)
apply(subst unrest) defer
apply(subst SubstP_twice_3,simp_all add:typing closure defined) 
apply(simp add:typing defined closure unrest)
apply(simp add:typing defined closure usubst)
apply(subst unrest) defer
apply(subst UNREST_subset[of "{ref\<down>} \<union> {wait\<down>}"])
apply(subst UNREST_union)
apply(simp add:assms)
apply(simp_all add:typing defined closure unrest)
apply(simp add:in_vars_diff)
apply(subst Diff_subset_conv)+
apply(subst UNDASHED_minus_in)
apply(subst Un_least,simp_all) 
apply(subst inf_absorb1)
apply(utp_poly_auto_tac)
apply(subst 1,subst in_vars_union,subst Un_least,simp_all)
apply(utp_poly_auto_tac)+
done
finally show ?thesis by (metis is_healthy_def CSP3_def)
qed

lemma SemiR_Skip_right:
  assumes "P is CSP" "P \<in> WF_RELATION" "`\<not>((\<not>CSP_Pre(P));($tr\<le>$tr\<acute>))` = CSP_Pre(P)" "`(CSP_Post(P) \<lhd> $wait\<acute> \<rhd> (\<exists> ref\<acute>\<acute> . CSP_Post(P)[($ref\<acute>\<acute>)/ref\<acute>]))` = CSP_Post(P)"
  shows "P is CSP4"
proof-
have 1: " `II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub>` =  `II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>} - {wait \<down>,wait \<down>\<acute>}\<^esub>`"
by (smt Diff_insert2 insert_commute)
have "`P ; SKIP` = `RHc (CSP_Pre(P) \<turnstile>  (CSP_Post(P) ; ($wait \<and> II\<^bsub>REL_VAR - {ok\<down>, ok\<down>\<acute>}\<^esub>)) \<or>
         (CSP_Post(P) ; (\<not> $wait \<and> II\<^bsub>REL_VAR - {ref\<down>, ref\<down>\<acute>} - OKAY\<^esub>)))`"
apply(subst Seq_comp_form, simp_all add:assms(1) assms(2) closure Skip_CSP)
apply(simp add:Skip_pre Skip_post R2_def R2s_def usubst typing closure defined R1_extend_AndP[THEN sym])
apply(simp add:R1_def tr_prefix_as_nil CondR_def SemiR_OrP_distl SemiR_OrP_distr assms(3))
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing closure)back back back
apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add:typing closure)back back back
apply(subst 1)
apply(utp_poly_auto_tac)
done
also have "... = `RHc (CSP_Pre(P) \<turnstile> CSP_Post(P))`"
apply(simp add:SemiR_AndP_right_precond closure typing assms urename)
apply(subst SemiR_SkipRA_right,simp_all add:typing closure defined assms unrest)
apply(rule unrest, simp add:CSP_Post_def typing closure defined assms unrest)
apply(rule unrest, simp_all add: typing closure defined assms unrest)
apply(rule unrest, simp_all add: typing closure defined assms unrest)
apply(rule unrest, simp_all add: typing closure defined assms unrest) defer
apply(subst SemiR_extract_variable_id_ty[of "ref "])
apply(simp_all add:typing closure defined unrest assms)
apply(simp add:usubst typing defined closure)
apply(subst SemiR_SkipRA_right,simp_all add:typing closure defined assms unrest)
apply(rule unrest)
apply(rule unrest, simp add:CSP_Post_def typing closure defined assms unrest)
apply(simp add:CSP_Post_def)
apply(rule unrest, simp add: typing closure defined assms unrest)
apply(rule unrest, simp add: typing closure defined assms unrest)
apply(rule unrest, simp add: typing closure defined assms unrest) defer 
apply(rule unrest, simp add: typing closure defined assms unrest)
apply(subst ExistsP_AndP_expand1[THEN sym], simp add:typing closure defined unrest)
apply(subst assms(4)[THEN sym]) back back
apply(simp add:CondR_def,utp_poly_auto_tac)
apply(subst UNREST_subset[of "{}"],simp_all add:typing closure defined unrest)
apply(utp_poly_auto_tac)
apply(subst UNREST_subset[of "{}"],simp_all add:typing closure defined unrest)
apply(utp_poly_auto_tac)
done
also have "... = P"
apply(subst CSP_Design[of "P"]) back back
apply(simp_all add:assms)
done
finally show ?thesis  by (metis is_healthy_def CSP4_def)
qed

lemma Stop_CSP3: "STOP is CSP3" 
apply(subst SemiR_Skip_left,simp_all add:assms closure Stop_CSP)
apply(simp add:Stop_design DesignREA_form R2_def R2s_AndP R1_extend_AndP[THEN sym])
apply(simp add:R2s_def R1_def usubst typing defined closure tr_prefix_as_nil)
apply(simp add:unrest typing defined closure)
done

lemma Stop_CSP4: "STOP is CSP4" 
apply(subst SemiR_Skip_right,simp_all add:assms closure Stop_CSP)
apply(simp add:Stop_pre)
apply(simp add:Stop_post usubst typing defined closure)
apply(subst ExistsP_ident,simp add:unrest typing defined closure)
apply(simp add:CondR_idem)
done

lemma Skip_CSP3: "SKIP is CSP3" 
apply(subst SemiR_Skip_left,simp_all add:assms closure Skip_CSP)
apply(simp add:Skip_design DesignREA_form R2_def R2s_AndP R1_extend_AndP[THEN sym])
apply(simp add:R2s_def R1_def usubst typing defined closure tr_prefix_as_nil)
apply(rule unrest, simp add:unrest typing defined closure) back
apply(rule unrest, simp add:unrest typing defined closure) back
apply(subst AndP_comm) back back
apply(rule unrest, simp add:unrest typing defined closure) back
apply(rule unrest, simp add:unrest typing defined closure) back
apply(rule unrest, simp add:unrest typing defined closure) back
apply(subst UNREST_subset[of "-(REL_VAR-REA-OKAY)"],subst UNREST_SkipRA,simp_all add:typing closure defined)
done

lemma Skip_CSP4: "SKIP is CSP4" 
apply(subst SemiR_Skip_right,simp_all add:assms closure Skip_CSP)
apply(simp add:Skip_pre)
apply(simp add:Skip_post usubst typing defined closure)
apply(subst ExistsP_ident,simp add:unrest typing defined closure)
apply(simp add:CondR_idem)
done

lemma Chaos_CSP3: "CHAOS is CSP3" 
apply(subst SemiR_Skip_left,simp_all add:assms closure Chaos_CSP)
apply(simp add:Chaos_design DesignREA_form R2_def R2s_AndP R1_extend_AndP[THEN sym])
apply(simp add:R2s_def R1_def usubst typing defined closure tr_prefix_as_nil)
apply(simp add:unrest typing defined closure)
done

lemma Chaos_CSP4: "CHAOS is CSP4"  
apply(subst SemiR_Skip_right,simp_all add:assms closure Chaos_CSP)
apply(simp add:Chaos_pre R1_def tr_leq_trans)
apply(simp add:Chaos_post R1_def usubst typing defined closure)
apply(subst ExistsP_ident,simp add:unrest typing defined closure)
apply(simp add:CondR_idem)
done

lemma PrefixSkip_CSP3: 
  assumes "{tr \<down>,tr \<down>\<acute>,ok\<down>,ok \<down>\<acute>,wait\<down>,ref\<down>} \<sharp> a" "NON_REL_VAR \<sharp> a" 
shows"@a is CSP3"
proof-
have Z: "{tr \<down>,tr \<down>\<acute>,ok \<down>\<acute>} \<sharp> a" "{ok \<down>,wait \<down>,ok \<down>\<acute>} \<sharp> a" "{ref \<down>} \<sharp> a" "{tr\<down>}\<sharp> a" "{tr\<down>\<acute>}\<sharp> a" "{wait\<down>}\<sharp>a"
by(subst UNREST_PEXPR_subset[of "{tr \<down>,tr \<down>\<acute>,ok\<down>,ok \<down>\<acute>,wait\<down>,ref\<down>}"],simp_all add:assms typing closure defined)+
show ?thesis
apply(subst SemiR_Skip_left,simp_all add:Z assms closure Prefix_CSP)
apply(subst CSP_Design,simp add:Prefix_CSP Z assms)
apply(simp add:Prefix_pre Prefix_post assms Z DesignREA_form R2_def R2s_AndP)
apply(simp add:R2s_def R1_def usubst typing defined closure tr_prefix_as_nil)
apply(simp add:Z PSubstPE_VarP_single_UNREST typing defined closure unrest)
apply(rule unrest, simp add:unrest typing defined closure Z) back
apply(rule unrest, simp add:unrest typing defined closure Z) back
apply(subst AndP_comm) back back back
apply(rule unrest, simp add:unrest typing defined closure Z) back
apply(subst AndP_comm) back back
apply(rule unrest, simp add:unrest typing defined closure Z) back
apply(rule unrest, simp add:unrest typing defined closure Z)
apply(rule unrest, simp add:unrest typing defined closure Z) back
apply(subst UNREST_subset[of "-(REL_VAR - REA - OKAY)"],subst UNREST_SkipRA)
apply(simp_all add:typing defined closure unrest)
done
qed

lemma PrefixSkip_CSP4: 
  assumes "{tr \<down>,tr \<down>\<acute>,ok\<down>,ok \<down>\<acute>,wait\<down>,ref\<down>\<acute>} \<sharp> a" "NON_REL_VAR \<sharp> a" 
  shows "@a is CSP4" 
proof-
have Z: "{tr \<down>,tr \<down>\<acute>,ok \<down>\<acute>} \<sharp> a" "{ok \<down>,wait \<down>,ok \<down>\<acute>} \<sharp> a" "{ref \<down>\<acute>} \<sharp> a" "{tr\<down>}\<sharp> a" "{tr\<down>\<acute>}\<sharp> a" "{wait\<down>}\<sharp>a"
by(subst UNREST_PEXPR_subset[of "{tr \<down>,tr \<down>\<acute>,ok\<down>,ok \<down>\<acute>,wait\<down>,ref\<down>\<acute>}"],simp_all add:assms typing closure defined)+
show ?thesis
apply(subst SemiR_Skip_right,simp_all add:assms closure Prefix_CSP Z)
apply(simp add:Prefix_pre tr_leq_trans)
apply(simp add:Prefix_post assms usubst typing defined closure Z)
apply(subst PSubstPE_VarP_single_UNREST,simp add:assms Z)+
apply(subst CondR_def) back back
apply(simp add:ExistsP_OrP_dist ExistsP_AndP_expand2[THEN sym] unrest typing defined closure)
apply(subst CondR_def[THEN sym])
apply(subst CondR_unreachable_branch)
apply(subst ExistsP_ident)
apply(subst unrest) back back
apply(simp add:typing defined closure unrest assms Z)
apply(subst UNREST_subset[of "-(REL_VAR - REA - OKAY)"],subst UNREST_SkipRA,simp_all add:typing defined closure)
apply(utp_poly_auto_tac)
done
qed

lemma Sequential_L1a:
  assumes "P is CSP3"
  shows "`SKIP;P` = P"
by(metis assms is_healthy_def CSP3_def)

lemma Sequential_L1b:
  assumes "P is CSP4"
  shows "`P;SKIP` = P"
by(metis assms is_healthy_def CSP4_def)

lemma Sequential_L2:
  "`(P;Q);R` = `P;(Q;R)`"
by (metis SemiR_assoc)

lemma Sequential_L4: "`(a \<rightarrow> P);Q` = `a \<rightarrow> (P ;Q)`"
by(simp add:PrefixCSP_def SemiR_assoc[THEN sym])

lemma Sequential_L5:
  assumes "P is CSP" "P \<in> REL"
  shows "`STOP;P` = `STOP`"
apply(subst Seq_comp_form,simp_all add:assms closure Stop_CSP Stop_pre Stop_post CondR_def SemiR_OrP_distl)
apply(simp add:SemiR_AndP_right_DASHED typing closure defined unrest urename AndP_assoc[THEN sym] AndP_contra)
apply(subst SemiR_SkipRA_right,simp_all add:typing defined closure unrest Stop_design)
done

(***********************)
(* REVIEWED UNTIL HERE *)
(***********************)

lemma Chaos_design_alt:
  "`RHc(\<not>R1(true) \<turnstile> b)` = CHAOS"
apply(simp add:Chaos_design DesignD_def R1_def)
apply(simp add:RHc_def)
apply(subst R1_idempotent[THEN sym],subst R1_R2_commute, simp add:R1_R3c_commute)
apply(subst R1_def) back
apply(utp_poly_tac)
apply(subst UTypedef.InjU_inverse, metis UTypedef_Event UTypedef_ULIST)+
apply (metis NilUL.rep_eq prefix_bot.bot.extremum)
done

lemma Sequential_L5b:
  assumes "P is CSP" "P \<in> REL"
  shows "`CHAOS;P` = `CHAOS`"
proof-
  have A: "P = `R1(P)`" by (metis assms is_healthy_def RHc_is_R1 CSP_is_RHc)
  have 0: "`CSP_Pre(CHAOS;P)` = `\<not>R1(true)`" 
  apply(subst Seq_comp_form,simp_all add:assms closure Chaos_CSP Chaos_pre Chaos_post R1_def DesignREA_pre tr_leq_trans demorgan2 CSP_Pre_R2_commute[THEN sym])
  apply(subst Healthy_simp[of _ "R1",THEN sym]) back back back back back defer
  apply(simp add:R1_def,subst AndP_comm,simp add:OrP_AndP_absorb)
  apply(simp add:R2_def R2s_def R1_def CSP_Pre_def usubst typing defined closure tr_prefix_as_nil)
  apply(subst closure,simp_all add:typing closure defined assms)
  apply(simp add:is_healthy_def R1_def AndP_assoc[THEN sym])
  apply(simp add:R1_def[THEN sym])
  apply(subst Healthy_simp[of _ "R1"],simp_all)
  apply(subst A)
  apply(subst CSP_Pre_def)
  apply(subst R1_ok'_false)
  apply(simp add:R1_ok_true R1_wait_false is_healthy_def R1_idempotent)
done
  show ?thesis
 apply(subst CSP_Design) back
 apply(subst Seq_comp_form,simp_all add:assms closure Chaos_CSP)
 apply(subst DesignREA_CSP,simp_all add:Chaos_pre Chaos_post R1_def)
 apply(simp add:CSP_Pre_def typing closure defined unrest)
 apply(simp add:CSP_Post_def typing closure defined unrest)
 apply(simp add:0 Chaos_design_alt)
done
qed
end