(******************************************************************************)
(* Project: Mechanation of the UTP                                            *)
(* File: utp_csp.thy                                                          *)
(* Authors: Samuel Canham and Simon Foster, University of York                *)
(******************************************************************************)

header {* CSP Parallel Processes *}

theory utp_csp_parallel_processes
imports 
  utp_csp_processes
begin

definition MergeCSP :: 
  "('a event USET, 'a) pexpr \<Rightarrow> 
   ('a uvar set * 'a upred)" where
  "MergeCSP A = ( { wait\<down>, ref\<down>, tr\<down>}
              , `R1(
                  (\<not>$ok \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>''0''\<^esub> - $tr) \<parallel>\<^bsub>A \<^esub>($tr\<^bsub>''1'' \<^esub>- $tr))) \<or>
                  ($ok \<and> ($ref\<acute> = ($ref\<^bsub>''0''\<^esub> \<union> $ref\<^bsub>''1''\<^esub>)) \<and> 
                 (($tr\<acute> - $tr) \<in> ($tr\<^bsub>''0''\<^esub> - $tr) \<parallel>\<^bsub>A \<^esub>($tr\<^bsub>''1'' \<^esub>- $tr))
                 \<and> (($wait\<^bsub>''0''\<^esub> \<or> $wait\<^bsub>''1''\<^esub>)\<lhd> $wait\<acute> \<rhd>(\<not>$wait\<^bsub>''0''\<^esub>\<and>\<not>$wait\<^bsub>''1''\<^esub>) )
                 \<and> $ok\<acute>)
                 ) ; SKIP`)"

definition ParallelCSP :: 
  "'a upred \<Rightarrow> 
   ('a event USET, 'a) pexpr \<Rightarrow> 
   'a upred \<Rightarrow> 
   'a upred" (infix "\<parallel>\<^bsub>CSP'(_')\<^esub>" 100) where
"P \<parallel>\<^bsub>CSP(A)\<^esub> Q = P \<parallel>\<^bsub>MergeCSP A\<^esub> Q"

definition InterleaveCSP 
  :: "'a upred \<Rightarrow> 'a upred \<Rightarrow> 'a upred" (infix "|||\<^bsub>CSP\<^esub>" 100) where
"P |||\<^bsub>CSP\<^esub> Q = ParallelCSP P |{}| Q"

definition HideCSP ::
  "'m upred \<Rightarrow>
   ('m event USET, 'm) pexpr \<Rightarrow>
   'm upred" where
"HideCSP P A = `RHc(CSP1(\<exists> tr\<acute>\<acute>. P[$tr\<acute>\<acute>/tr\<acute>][($ref\<acute> \<union> A)/ref\<acute>] 
                   \<and> $tr\<acute> = $tr ^ (($tr\<acute>\<acute> - $tr)\<upharpoonright>A))) ; SKIP`"

syntax
 "_upred_parallel"  :: "n_upred \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixr "||\<^bsub>_\<^esub>" 100)
 "_upred_hide"      :: "n_upred \<Rightarrow> n_pexpr \<Rightarrow> n_upred" (infixr "\\" 100)
 "_upred_interleave" :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixr "|||" 100)

syntax (xsymbols)
  "_upred_parallel"  :: "n_upred \<Rightarrow> n_pexpr \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixr "\<parallel>\<^bsub>_\<^esub>" 100)

translations
 "_upred_parallel P A Q" == "CONST ParallelCSP P A Q"
 "_upred_interleave P Q" == "CONST InterleaveCSP P Q"
 "_upred_hide P A" == "CONST HideCSP P A"

declare MergeCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare ParallelCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare InterleaveCSP_def [eval, evalr, evalrr, evalrx, evalp]
declare HideCSP_def [eval, evalr, evalrr, evalrx, evalp]

subsection {* Merge laws *}

subsection {* Parallel laws *}

subsection {* Interleave laws *}

subsection {* Hide laws *}

lemma Hide_closure_form:
  assumes "P \<in> REL" "NON_REL_VAR \<sharp> A"
  shows "`(\<exists> tr\<acute>\<acute> . P[$tr\<acute>\<acute>/tr\<acute>][($ref\<acute> \<union> A)/ref\<acute>] \<and> ($tr\<acute> = $tr ^ RestrictUS($tr\<acute>\<acute> - $tr,A)))` \<in> REL"
sorry

lemma Hide_R1:
  assumes "P \<in> REL" "NON_REL_VAR \<sharp> A"
  shows "`P\\A` is R1"
apply(subst HideCSP_def)
apply(subst R1_SemiR_closure,simp_all add:closure Skip_R1) defer
apply(simp add:is_healthy_def RHc_def R1_idempotent)
apply(subst closure,simp_all)
apply(subst closure,simp_all)
apply (metis (lifting, no_types) Hide_closure_form PVAR_VAR_pvdash assms(1) assms(2))
done

lemma Hide_R2:
  assumes "P \<in> REL" "NON_REL_VAR \<sharp> A"
  shows "`P\\A` is R2"
apply(subst HideCSP_def)
apply(subst R2_SemiR_closure,simp_all add:closure Skip_R2)
apply(simp add:is_healthy_def RHc_def R1_R2_commute R2_idempotent)
apply(subst closure,simp_all)
apply(subst closure,simp_all)
apply (metis (lifting, no_types) Hide_closure_form PVAR_VAR_pvdash assms(1) assms(2))
done

lemma Hide_R3c:
  assumes "P \<in> REL" "NON_REL_VAR \<sharp> A"
  shows "`P\\A` is R3c"
apply(subst HideCSP_def)
apply(subst R3c_SemiR_closure,simp_all add:closure Skip_R3c Skip_R1)
apply(simp add:is_healthy_def RHc_def R1_R3c_commute R2_R3c_commute R3c_idempotent)
apply(subst closure,simp_all)
apply(subst closure,simp_all)
apply (metis (lifting, no_types) Hide_closure_form PVAR_VAR_pvdash assms(1) assms(2))
done

lemma Hide_CSP1:
  "`P\\A` is CSP1"
apply(subst HideCSP_def)
apply(subst CSP1_SemiR_closure,simp_all add:closure Skip_CSP1 Skip_R1)
apply(simp add:is_healthy_def RHc_def CSP1_R1_commute CSP1_R2_commute CSP1_R3c_commute CSP1_idempotent)
done

lemma Hide_CSP2:
  "`P\\A` is CSP2"
apply(simp add: HideCSP_def is_healthy_def H2_SemiR)
apply(metis Skip_CSP2 is_healthy_def)
done

lemma Hide_CSP:
  assumes "P \<in> REL" "NON_REL_VAR \<sharp> A"
  shows "`P\\A` is CSP"
oops

lemma Hide_pre:
  assumes "P is R2"
  shows "`CSP_Pre(P\\A)` = 
`\<forall> tr\<acute>\<acute>. (($tr \<le> $tr\<acute>\<acute>) \<and> ($tr^RestrictUS($tr\<acute>\<acute>-$tr,A) \<le> $tr\<acute>)) \<Rightarrow> CSP_Pre(P)[$tr\<acute>\<acute>/tr\<acute>]`"
proof-
have 0: "`($tr \<le> $tr\<acute>)` = `R2($tr \<le> $tr\<acute>)`" by(simp add:R2_def R2s_def R1_def usubst typing defined closure tr_prefix_as_nil)
show ?thesis
apply(simp add:HideCSP_def)
apply(subst Seq_comp_form,simp_all add:closure Skip_CSP) defer defer
apply(simp add:DesignREA_pre) 
apply(simp add: CSP_Pre_NotP CSP_Pre_AndP CSP_Pre_OrP CSP_Pre_twice CSP_Pre_Post Skip_pre)
apply(simp add: RHc_def R2_def R1_idempotent)
apply(simp add:R2_def[THEN sym] CSP_Pre_R2_commute R3c_def CondR_def CSP_Pre_OrP CSP_Pre_AndP CSP_Pre_NotP CSP1_def SkipR_as_SkipRA)
apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add:typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add:typing defined closure)
apply(simp add:CSP_Pre_def usubst typing defined closure)
apply(subst SubstP_SemiR_right,simp_all add:typing defined closure unrest)
apply(subst SubstP_SemiR_left,simp_all add:typing defined closure unrest)
apply(subst SubstP_SemiR_left,simp_all add:typing defined closure unrest)
apply(simp add:R2_ok_true R2_wait_false)
apply(simp add:usubst typing defined closure)
apply(subst 0)
apply(subst R2_SemiR_distribute) defer defer
apply(subst R2_def,simp add:R2s_def R1_def usubst typing defined closure tr_prefix_as_nil) back
apply(subst SubstP_twice_3,simp_all add:typing closure defined unrest) back back back
apply(simp add:typing closure defined usubst)
apply(subst SubstP_ExistsP,simp_all add:typing closure defined unrest)+
apply(simp add:usubst typing defined closure)
apply(subst Healthy_simp[of _ "R2"]) defer
oops

lemma CSP_Post_prefix:
  assumes "P is CSP2"
  shows "`CSP_Post(P ; ($tr\<le> $tr\<acute>))` = `CSP_Post(P);($tr\<le>$tr\<acute>)`"
sorry

lemma Hide_post:
  shows "`CSP_Post(P\\A)` = undefined"
apply(simp add: HideCSP_def)
apply(subst Seq_comp_form,simp_all add:closure Skip_CSP) defer defer
apply(simp add:DesignREA_post)
apply(simp add:CSP_Post_NotP CSP_Post_OrP CSP_Post_AndP ImpliesP_def Skip_pre)
apply(subst CSP_Post_prefix) defer
apply(simp add:CSP_Post_NotP CSP_Post_Pre)
oops

end