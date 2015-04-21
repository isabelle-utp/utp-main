(******************************************************************************)
(* Project: Mechanation of the UTP                                            *)
(* File: utp_csp.thy                                                          *)
(* Authors: Samuel Canham and Simon Foster, University of York                *)
(******************************************************************************)

header {* CSP Process Laws*}

theory utp_csp_laws
imports 
  utp_csp_healths
begin

definition CSP_Pre
  :: "'a upred \<Rightarrow> 'a upred " where
"CSP_Pre P = `\<not>P\<^sup>f[true/ok]\<^sub>f`"

definition CSP_Post
  :: "'a upred \<Rightarrow> 'a upred " where
"CSP_Post P = `P\<^sup>t[true/ok]\<^sub>f`"

subsection {* Closure laws *}

lemma CSP_Post_rel_closure[closure]: 
  assumes "P \<in> WF_RELATION"
  shows "CSP_Post P \<in> WF_RELATION"
by(simp add:CSP_Post_def closure typing defined unrest assms)

lemma CSP_Pre_rel_closure[closure]: 
  assumes "P \<in> WF_RELATION"
  shows "CSP_Pre P \<in> WF_RELATION"
by(simp add:CSP_Pre_def closure typing defined unrest assms)

subsection {* CSP laws *}

lemma CSP_is_CSP1:
  assumes "P is CSP"
  shows "P is CSP1"
proof-
from assms have 1: "P = CSP(P)" by(metis is_healthy_def)
show ?thesis 
  apply(subst 1)
  apply(simp add:is_healthy_def CSP_def CSP1_idempotent)
  done
qed

lemma CSP_is_CSP2:
  assumes "P is CSP"
  shows "P is CSP2"
proof-
from assms have 1: "P = CSP(P)" by(metis is_healthy_def)
show ?thesis 
  apply(subst 1)
  apply(simp add:is_healthy_def CSP_def CSP1_CSP2_commute CSP2_idempotent)
  done
qed

lemma CSP_is_RHc: 
assumes "P is CSP"
shows "P is RHc" 
proof -
  from assms have 1: "P = CSP(P)" 
    by (metis Healthy_simp)
  have 2: "CSP(P) is RHc"
    apply(simp add:is_healthy_def)
    apply(simp add:CSP_def RHc_def)
    apply(simp add:CSP2_R1_commute CSP2_R2_commute CSP2_R3c_commute assms closure)
    apply(simp add:CSP1_R1_commute CSP1_R2_commute CSP1_R3c_commute)
    apply(simp add:R1_R2_commute R1_R3c_commute R1_idempotent)
    apply(simp add:R2_R3c_commute R2_idempotent R3c_idempotent)
    done
  show ?thesis 
    by (metis "1" "2")
qed

lemma CSP_form: 
assumes "P is CSP" 
shows "P = `(\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($ok \<and> $wait \<and> II) \<or> ($ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P))) \<or> ($ok \<and> \<not>$wait \<and> $ok\<acute> \<and> R2(CSP_Post(P)))`"
proof-
  have "P = `($ok \<and> $wait \<and> P) \<or> ($ok \<and> \<not>$wait \<and> P) \<or> (\<not>$ok \<and> P)`"
  by(simp add: OrP_assoc AndP_OrP_distr[THEN sym] AndP_OrP_distl[THEN sym] OrP_excluded_middle)
  also have "... = `($ok \<and> $wait \<and> R3c(P)) \<or> ($ok \<and> \<not>$wait \<and> R2(CSP2(P))) \<or> (\<not>$ok \<and> CSP1(P))`"
  by(metis assms is_healthy_def CSP_is_CSP1 CSP_is_CSP2 CSP_is_RHc RHc_is_R2 RHc_is_R3c)
  also have "... = `(\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($ok \<and> $wait \<and> II) \<or> ($ok \<and> \<not>$wait \<and> R2(P\<^sup>f)) \<or> ($ok \<and> \<not>$wait \<and>  $ok\<acute> \<and> R2(P\<^sup>t))`"
  apply(simp add:R3c_form H2_split R2s_OrP R2_def R2s_AndP R1_OrP R1_extend_AndP[THEN sym])
  apply(simp add:R2_def[THEN sym],simp add:R2s_def usubst typing defined closure)
  apply(subst CSP1_R1_form_2,simp_all add:assms CSP_is_RHc RHc_is_R1 CSP1_def)
  apply(utp_poly_auto_tac)
  done
  also have "... =   `(\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($ok \<and> $wait \<and> II) \<or> ($ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P))) \<or> ($ok \<and> \<not>$wait \<and> $ok\<acute> \<and> R2(CSP_Post(P)))`"
  apply(subst PVarPE_PSubstPE,simp add:typing) back back
  apply(subst PVarPE_PSubstPE,simp add:typing) back back back
  apply(simp add:usubst typing defined closure R2_ok_true)
  apply(subst NotP_PVarPE_PSubstPE,simp_all add:typing) back
  apply(subst NotP_PVarPE_PSubstPE,simp_all add:typing) back back
  apply(simp add:usubst typing defined closure R2_wait_false CSP_Pre_def CSP_Post_def)
  done
finally show ?thesis .
qed

subsection {* CSP as Reactive Designs *}

lemma DesignD_form: "`(P \<turnstile> Q)` = `\<not>$ok \<or> ($ok \<and> \<not>P) \<or> ($ok \<and> P \<and> $ok\<acute> \<and> Q)`"
by(utp_pred_auto_tac)

lemma CSP_Design: 
assumes "P is CSP" 
shows "P = `RHc ( CSP_Pre(P) \<turnstile> CSP_Post(P))`"
apply(subst CSP_form, simp_all add: assms)
apply(simp add:DesignD_form RHc_def R2_R3c_commute)
apply(simp add: R2_def R2s_def usubst typing defined closure R3c_def SkipR_as_SkipRA)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing defined closure) back
apply(utp_poly_auto_tac)
done

lemma DesignREA_form: 
  "`RHc( P \<turnstile> Q)` = `(\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($ok \<and> $wait \<and> II) \<or> ($ok \<and> \<not>$wait \<and> R2(\<not>P)) \<or> ($ok \<and> \<not>$wait \<and> R2(Q) \<and> $ok\<acute>)`"
apply(simp add:DesignD_form RHc_def R3c_form SkipR_as_SkipRA)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:closure typing)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:closure typing)back
apply(simp add:R2_def R1_idempotent R2s_def usubst typing defined closure)
apply(simp add:R1_OrP)
apply(simp add:R1_def AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back back
apply(subst AndP_comm) back back back back
apply(simp add:AndP_assoc[THEN sym] tr_prefix_as_nil)
apply(utp_poly_auto_tac)
done

lemma DesignREA_form2:  "`RHc( P \<turnstile> Q)` = `(\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or> ($ok \<and> $wait \<and> II) \<or> ($ok \<and> \<not>$wait \<and> R2(\<not>P)) \<or> ($ok \<and> \<not>$wait \<and> \<not>R2(\<not>P) \<and> R2(Q) \<and> $ok\<acute>)`"
by(simp add:DesignREA_form,utp_poly_auto_tac)

subsection {* CSP_Pre and CSP_Post laws *}

lemma CSP_Pre_R2: 
  assumes "P is R2"
  shows "`\<not>CSP_Pre(P)` is R2"
proof-
from assms have "`\<not>CSP_Pre(P)` = `\<not>CSP_Pre(R2(P))`"
by(metis is_healthy_def)
also have "... = `R2(\<not>CSP_Pre(P))`"
apply(subst CSP_Pre_def)
apply(subst R2_ok'_false)
apply(subst R2_ok_true)
apply(subst R2_wait_false)
apply(subst NotP_NotP[THEN sym]) back back back back back back
apply(subst CSP_Pre_def)
apply(simp add: NotP_NotP)
done
finally show ?thesis by(metis is_healthy_def)
qed

lemma CSP_Post_R2: 
  assumes "P is R2"
  shows "`CSP_Post(P)` is R2"
proof -
from assms have "`CSP_Post(P)` = `CSP_Post(R2(P))`" by (metis assms is_healthy_def)
also have "... = `R2(CSP_Post(P))`"
apply(subst CSP_Post_def)
apply(subst R2_ok'_true)
apply(subst R2_ok_true)
apply(subst R2_wait_false)
apply(subst CSP_Post_def[THEN sym])
apply(simp)
done
finally show ?thesis by(metis is_healthy_def)
qed

lemma CSP_Pre_DesignREA:
  assumes "{ok\<down>}\<sharp>A" "{ok\<down>\<acute>}\<sharp>A" "{wait\<down>}\<sharp>A" "`\<not>A` is R2"
  shows "`CSP_Pre(RHc( A \<turnstile> B))` = `A`"
proof -
have "`CSP_Pre(RHc( A \<turnstile> B))` = `\<not>(R2(\<not>A))`"
apply(simp add:DesignREA_form CSP_Pre_def usubst typing defined closure R2_def R1_def R2s_def)
apply(subst SubstP_twice_3) back
apply(simp_all add:unrest typing defined closure)
apply(subst SubstP_twice_3) back back
apply(simp_all add:unrest typing defined closure)
apply(subst SubstP_twice_3) back back back
apply(simp_all add:unrest typing defined closure)
apply(subst SubstP_twice_3)
apply(simp_all add:unrest typing defined closure)
apply(subst SubstP_twice_3) back
apply(simp_all add:unrest typing defined closure)
apply(subst SubstP_twice_3) back back
apply(simp_all add:unrest typing defined closure)
apply(simp add:usubst typing defined closure)
apply(simp add:SubstP_VarP_single_UNREST assms demorgan2 ImpliesP_def)
done
also have "... = A"
by (metis NotP_NotP assms(4) is_healthy_def)
finally show ?thesis .
qed

lemma CSP_Post_DesignREA:
  assumes "{ok\<down>}\<sharp>`A\<Rightarrow>B`" "{ok\<down>\<acute>}\<sharp>`A\<Rightarrow>B`" "{wait\<down>}\<sharp>`A\<Rightarrow>B`" "`A \<Rightarrow> B` is R2"
  shows"`CSP_Post(RHc( A \<turnstile> B))` = `A \<Rightarrow> B`"
proof -
have "`CSP_Post(RHc( A \<turnstile> B))` = `R1(CSP_Post(R2s(A \<Rightarrow> B)))`"
by(simp add:DesignREA_form CSP_Post_def usubst typing defined closure R2_def R1_def R2s_def AndP_OrP_distr[THEN sym] ImpliesP_def)
also have "... = `R2(CSP_Post(A \<Rightarrow> B))`"
apply(simp add:CSP_Post_def R2s_def)
apply(subst SubstP_twice_3) back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_3) back back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_3) back back back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_3)
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_3) back
apply(simp_all add:typing defined closure unrest)
apply(subst SubstP_twice_3) back back
apply(simp_all add:typing defined closure unrest)
apply(simp add:usubst typing defined closure R2_def R2s_def)
done
also have "... = `R2(A \<Rightarrow> B)`"
by(simp add:CSP_Post_def SubstP_VarP_single_UNREST assms)
finally show ?thesis
by (metis Healthy_simp assms(4))
qed

lemma CSP_Pre_UNREST: 
  assumes "{ok\<down>,wait\<down>,ok\<down>\<acute>} \<sharp> `P`"
  shows "`CSP_Pre(P)` = `\<not>P`"
apply(simp add:CSP_Pre_def)
apply(subst SubstP_VarP_single_UNREST)
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
apply(subst SubstP_VarP_single_UNREST)
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
apply(subst SubstP_VarP_single_UNREST)
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
done

lemma CSP_Post_UNREST: 
  assumes "{ok\<down>,wait\<down>,ok\<down>\<acute>} \<sharp> `P`"
  shows "`CSP_Post(P)` = `P`"
apply(simp add:CSP_Post_def)
apply(subst SubstP_VarP_single_UNREST)
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
apply(subst SubstP_VarP_single_UNREST)
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
apply(subst SubstP_VarP_single_UNREST)
apply(subst UNREST_subset[of "{ok\<down>,wait\<down>,ok\<down>\<acute>}"])
apply(simp_all add:assms)
done

lemma CSP_Pre_R2_commute:
  "`\<not>CSP_Pre(R2(P))` = `R2(\<not>CSP_Pre(P))`"
apply(subst CSP_Pre_def) back
apply(subst NotP_NotP)
apply(subst R2_wait_false[THEN sym])
apply(subst R2_ok_true[THEN sym])
apply(simp add:R2_def[THEN sym] CSP_Pre_def)
apply (metis PVAR_VAR_pvdash R2_ok'_false)
done

lemma CSP_Post_R1_commute:
  "`CSP_Post(R1(P))` = `R1(CSP_Post(P))`"
by(simp add:CSP_Post_def R1_def usubst typing defined closure)

lemma CSP_Post_R2_commute:
  "`CSP_Post(R2(P))` = `R2(CSP_Post(P))`"
apply(simp add:CSP_Post_def)
apply(simp add: R2_wait_false[THEN sym] R2_ok_true[THEN sym])
apply (metis PVAR_VAR_pvdash R2_ok'_true)
done


lemma CSP_Pre_OrP:
  "`CSP_Pre(A \<or> B)` = `CSP_Pre(A) \<and> CSP_Pre(B)`"
by(simp add:CSP_Pre_def demorgan1 usubst)

lemma CSP_Pre_AndP:
  "`CSP_Pre(A \<and> B)` = `CSP_Pre(A) \<or> CSP_Pre(B)`"
by(simp add:CSP_Pre_def demorgan2 usubst)

lemma CSP_Pre_NotP:
  "`CSP_Pre(\<not>A)` = `\<not>CSP_Pre(A)`"
by(simp add:CSP_Pre_def usubst)

lemma CSP_Pre_twice:
  "`CSP_Pre(CSP_Pre(P))` = `\<not>CSP_Pre(P)`"
apply(simp add:CSP_Pre_def SubstP_NotP)
apply(subst SubstP_twice_3,simp_all add:typing closure defined unrest) back back
apply(subst SubstP_twice_3,simp_all add:typing closure defined unrest) back
apply(simp add:usubst typing defined closure)
apply(subst SubstP_twice_3,simp_all add:typing closure defined unrest) back back
apply(simp add:usubst typing defined closure)
done

lemma CSP_Post_OrP:
  "`CSP_Post(A \<or> B)` = `CSP_Post(A) \<or> CSP_Post(B)`"
by(simp add:CSP_Post_def usubst)

lemma CSP_Post_AndP:
  "`CSP_Post(A \<and> B)` = `CSP_Post(A) \<and> CSP_Post(B)`"
by(simp add:CSP_Post_def usubst)

lemma CSP_Post_NotP:
  "`CSP_Post(\<not>A)` = `\<not>CSP_Post(A)`"
by(simp add:CSP_Post_def usubst)

lemma CSP_Post_CondR: 
  "`CSP_Post(A \<lhd> x \<rhd> B)` = `CSP_Post(A) \<lhd> CSP_Post(x) \<rhd> CSP_Post(B)`"
by(simp add:CondR_def CSP_Post_def usubst)

lemma CSP_Post_twice:
  "`CSP_Post(CSP_Post(P))` = `CSP_Post(P)`"
apply(simp add:CSP_Post_def)
apply(subst SubstP_twice_3,simp_all add:typing closure defined unrest) back back
apply(subst SubstP_twice_3,simp_all add:typing closure defined unrest) back
apply(simp add:usubst typing defined closure)
apply(subst SubstP_twice_3,simp_all add:typing closure defined unrest) back back
apply(simp add:usubst typing defined closure)
done

lemma CSP_Post_Pre:
  "`CSP_Post(CSP_Pre(P))` = `CSP_Pre(P)`"
apply(simp add:CSP_Pre_def CSP_Post_def SubstP_NotP)
apply(subst SubstP_twice_3,simp_all add:typing closure defined unrest) back back
apply(subst SubstP_twice_3,simp_all add:typing closure defined unrest) back
apply(simp add:usubst typing defined closure)
apply(subst SubstP_twice_3,simp_all add:typing closure defined unrest) back back
apply(simp add:usubst typing defined closure)
done

lemma CSP_Pre_Post:
  "`CSP_Pre(CSP_Post(P))` = `\<not> CSP_Post(P)`"
apply(simp add:CSP_Pre_def CSP_Post_def)
apply(subst SubstP_twice_3,simp_all add:typing closure defined unrest) back back
apply(subst SubstP_twice_3,simp_all add:typing closure defined unrest) back
apply(simp add:usubst typing defined closure)
apply(subst SubstP_twice_3,simp_all add:typing closure defined unrest) back back
apply(simp add:usubst typing defined closure)
done

lemma DesignREA_pre:
  shows "`CSP_Pre(RHc(A \<turnstile> B))` = `\<not>R2(\<not>CSP_Pre(\<not>A))`"
apply(subst DesignREA_form,simp add:CSP_Pre_def usubst typing defined closure)
apply(simp add:SubstP_NotP[THEN sym])
apply(subst SubstP_NotP)apply(subst SubstP_NotP)apply(subst SubstP_NotP)
apply(subst R2_wait_false[THEN sym])
apply(subst R2_ok_true[THEN sym])
apply (metis PVAR_VAR_pvdash R2_ok'_false)
done

lemma DesignREA_post:
  shows "`CSP_Post(RHc(A \<turnstile> B))` = `R2(CSP_Post(A \<Rightarrow> B))`"
apply(subst DesignREA_form,simp add:CSP_Post_def usubst typing defined closure ImpliesP_def)
apply(simp add:SubstP_OrP[THEN sym] SubstP_NotP[THEN sym] R2_OrP[THEN sym])
apply(simp add:ImpliesP_def[THEN sym])
apply(subst R2_wait_false[THEN sym])
apply(subst R2_ok_true[THEN sym])
apply (metis PVAR_VAR_pvdash R2_ok'_true)
done

lemma RHc_idempotent:
  "`RHc(RHc(P))` = `RHc(P)`"
by(simp add: R1_R2_commute R1_R3c_commute R1_idempotent R2_R3c_commute R2_idempotent R3c_idempotent RHc_def)

lemmas R_commutes = R1_R2_commute R1_R3c_commute R2_R3c_commute
lemmas CSP_R_commutes = CSP1_R1_commute CSP1_R2_commute CSP1_R3c_commute CSP2_R1_commute CSP2_R2_commute CSP2_R3c_commute

lemma DesignD_pre: 
  assumes "{ok\<down>\<acute>} \<sharp> A"  "{ok\<down>\<acute>} \<sharp> B"
  shows "`(A \<turnstile> B)[false / ok\<acute>]` = `(\<not> $ok \<or> \<not> A)`"
by(simp add:DesignD_def usubst typing defined closure SubstP_VarP_single_UNREST assms demorgan2)

lemma DesignD_post: 
  assumes "{ok\<down>\<acute>} \<sharp> A"  "{ok\<down>\<acute>} \<sharp> B"
  shows "`(A \<turnstile> B)[true / ok\<acute>]` = `($ok \<and>  A) \<Rightarrow> B`"
by(simp add:DesignD_def usubst typing defined closure SubstP_VarP_single_UNREST assms)

lemma DesignREA_CSP:
  assumes "{ok\<down>\<acute>} \<sharp> A"  "{ok\<down>\<acute>} \<sharp> B"
  shows "`RHc (A \<turnstile> B)` is CSP"
proof-
  have "`CSP(RHc(A \<turnstile> B))` =  `RHc(CSP1(CSP2(A \<turnstile> B)))`"
    by (metis (no_types) CSP_R_commutes CSP_def RHc_def RHc_idempotent comp_apply)
  also have "... = `RHc (CSP1 ((\<not>$ok \<or> \<not> A) \<or> (($ok \<and> A) \<Rightarrow> B) \<and> $ok\<acute>))`"
    by (simp add: H2_split DesignD_pre[simplified] DesignD_post[simplified] assms)
  also have "... = `RHc(A \<turnstile> B)`"
    by (utp_poly_auto_tac)
  finally show ?thesis
    by (metis Healthy_intro)
qed

lemma DesignREA_Pre_Post:
  "`RHc(A\<turnstile>B)` = `RHc(A \<turnstile> A \<and> B)`"
by(utp_poly_auto_tac)

lemma Design_Eq:
  assumes "A is R2s" "C is R2s" "`A` = `C`" "`A \<Rightarrow> B` = `C \<Rightarrow> D`"
  shows "`RHc(A \<turnstile> B)` = `RHc(C \<turnstile> D)`"
proof -
  have 0: "`RHc(A \<turnstile> B)` = `RHc(C \<turnstile> (C \<Rightarrow> D))`"
  apply(simp add:assms(3) assms(4)[THEN sym])
  apply(simp add: DesignREA_form ImpliesP_def R2_OrP AndP_OrP_distl AndP_OrP_distr)
  apply(subst OrP_assoc,simp add:AndP_assoc OrP_AndP_absorb) back back back back
  done
  show ?thesis
  apply(subst 0, simp add: DesignREA_form ImpliesP_def R2_OrP AndP_OrP_distl AndP_OrP_distr)
  apply(subst OrP_assoc,simp add:AndP_assoc OrP_AndP_absorb) back back 
  done
qed

subsection {* Sequential composition *}

lemma left_form_P:
  assumes "P is CSP"
  shows "P = `
  (\<not>$ok \<and> ($tr \<le> $tr\<acute>)) \<or> 
  ($ok \<and> $wait \<and> II) \<or> 
  ($ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P))) \<or> 
  ($ok \<and> \<not>$wait \<and> R2(CSP_Post(P)) \<and> $ok\<acute>)`"
  by(subst CSP_Design,simp_all add: DesignREA_form assms)

lemma Seq_comp_1: 
  assumes "Q is CSP" "Q \<in> WF_RELATION"
  shows "`(\<not>$ok \<and> ($tr \<le> $tr\<acute>));Q` = `\<not>$ok \<and> ($tr \<le> $tr\<acute>)`"
proof -
  have "`(\<not>$ok \<and> ($tr \<le> $tr\<acute>));Q` = `(\<not>$ok \<and> ($tr \<le> $tr\<acute>));CSP1(R1(Q))`"
    by(metis assms is_healthy_def CSP_is_CSP1 CSP_is_RHc RHc_is_R1)
  also have "... = `\<not>$ok \<and> ($tr \<le> $tr\<acute>)`"
    apply(subst SemiR_AndP_left_precond,simp_all add:closure typing defined assms)
    apply(subst CSP1_R1_form, simp add:is_healthy_def R1_idempotent)
    apply(simp add:CSP1_def SemiR_OrP_distl)
    apply(subst SemiR_remove_middle_unrest1[of _ _ "{ok \<down>}"],simp_all add:typing closure defined assms unrest)
    apply(subst SemiR_remove_middle_unrest1[of _ _ "{ok \<down>}"],simp_all add:typing closure defined unrest)
    apply(simp add:R1_def usubst typing defined closure SemiR_OrP_distl[THEN sym])
    apply(subst tr_leq_trans[THEN sym]) back back back
    apply(utp_poly_auto_tac)
    done
  finally show ?thesis
    by this
qed

lemma Seq_comp_2: 
  assumes "Q is CSP"
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
        by(metis is_healthy_def assms CSP_is_RHc RHc_is_R3c)
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

lemma Seq_comp_3: 
  assumes "Q is CSP" "Q\<in> WF_RELATION" "P\<in> WF_RELATION"
  shows "`($ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P)));Q` = `$ok \<and> \<not>$wait \<and> (R2(\<not>CSP_Pre(P));($tr\<le>$tr\<acute>))`"
proof -
  have "`($ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P)));Q` = `($ok \<and> \<not>$wait \<and> R2(\<not>CSP_Pre(P)));CSP1(R1(Q))`"
    by(metis assms is_healthy_def CSP_is_CSP1 CSP_is_RHc RHc_is_R1)
  also have "... = `$ok \<and> \<not>$wait \<and> (R2(\<not>CSP_Pre(P));($tr\<le>$tr\<acute>))`"
    apply(subst SemiR_AndP_left_precond,simp_all add:closure typing defined assms)
    apply(subst SemiR_AndP_left_precond,simp_all add:closure typing defined assms)
    apply(subst CSP1_R1_form, simp add:is_healthy_def R1_idempotent)
    apply(simp add:CSP1_def SemiR_OrP_distl)
    apply(subst SemiR_remove_middle_unrest1[of _ _ "{ok \<down>}"],simp_all add:typing closure defined assms unrest)
    apply(simp add:typing closure defined assms unrest CSP_Pre_def R2_def R2s_def R1_def)
    apply(subst SemiR_remove_middle_unrest1[of _ _ "{ok \<down>}"],simp_all add:typing closure defined unrest assms)
    apply(simp add:typing closure defined assms unrest CSP_Pre_def R2_def R2s_def R1_def)
    apply(simp add:R1_def usubst typing defined closure SemiR_OrP_distl[THEN sym] AndP_assoc[THEN sym])
    apply(utp_poly_auto_tac)
    done
  finally show ?thesis
    by this
qed

lemma CSP_SemiR_closure: 
  assumes "P is CSP" "Q is CSP" "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows " `P ; Q` is CSP"
proof -
have 0: 
  "P is R1" "P is R2" "P is R3c" "P is CSP1"
  "Q is R1" "Q is R2" "Q is R3c" "Q is CSP1" "Q is CSP2"
  apply(metis assms CSP_is_RHc RHc_is_R1)
  apply(metis assms CSP_is_RHc RHc_is_R2)
  apply(metis assms CSP_is_RHc RHc_is_R3c)
  apply(metis assms CSP_is_CSP1)
  apply(metis assms CSP_is_RHc RHc_is_R1)
  apply(metis assms CSP_is_RHc RHc_is_R2)
  apply(metis assms CSP_is_RHc RHc_is_R3c)
  apply(metis assms CSP_is_CSP1)
  apply(metis assms CSP_is_CSP2)
done
have 1: "`P;Q` is R1" 
  by(simp add: 0 R1_SemiR_closure assms)
have 2: "`P;Q` is R2" 
  by(simp add: 0 R2_SemiR_closure assms)
have 3: "`P;Q` is R3c" 
  by(simp add: 0 R3c_SemiR_closure assms)
have 4: "`P;Q` is CSP1" 
  by(simp add: 0 CSP1_SemiR_closure assms)
have 5: "`P;Q` is CSP2" 
  by(simp add: 0 CSP2_SemiR_closure assms)
show ?thesis
apply(simp add: is_healthy_def CSP_def RHc_def)
apply(metis 1 2 3 4 5 is_healthy_def)
done
qed

end