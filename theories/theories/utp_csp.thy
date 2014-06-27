(******************************************************************************)
(* Project: Mechanation of the UTP                                            *)
(* File: utp_csp.thy                                                          *)
(* Authors: Samuel Canham and Simon Foster, University of York                *)
(******************************************************************************)

header {* CSP Processes *}

theory utp_csp
imports 
  "csp/utp_csp_lemmas"
  "csp/utp_csp_healths"
  "csp/utp_csp_laws"
  "csp/utp_csp_processes"
  "csp/utp_csp_process_laws"
  "csp/utp_csp_refine"
begin

definition ParallelMergeD2 :: 
  "'a upred =>  'a upred => 'a upred \<Rightarrow> 'a upred" (infix "\<parallel>2\<^bsub>_\<^esub>" 100) where
"P \<parallel>2\<^bsub>M\<^esub> Q =  ((add_sub 0 on {tr \<down>\<acute>,wait \<down>\<acute>,ref \<down>\<acute>,ok \<down>\<acute>} \<bullet> P) \<and>\<^sub>p (add_sub 1 on {tr \<down>\<acute>,wait \<down>\<acute>,ref \<down>\<acute>,ok \<down>\<acute>} \<bullet> Q) \<and>\<^sub>p II\<^bsub>REA \<union> OKAY\<^esub>) ;\<^sub>R M"

lemma ParallelMerge_form:
"P \<parallel>2\<^bsub>M\<^esub> Q =  `(P[$tr\<^bsub>0\<^esub>\<acute>/tr\<acute>][$wait\<^bsub>0\<^esub>\<acute>/wait\<acute>][$ref\<^bsub>0\<^esub>\<acute>/ref\<acute>][$ok\<^bsub>0\<^esub>\<acute>/ok\<acute>] \<and>
         Q[$tr\<^bsub>1\<^esub>\<acute>/tr\<acute>][$wait\<^bsub>1\<^esub>\<acute>/wait\<acute>][$ref\<^bsub>1\<^esub>\<acute>/ref\<acute>][$ok\<^bsub>1\<^esub>\<acute>/ok\<acute>] \<and> II\<^bsub>REA \<union> OKAY\<^esub>) ; M`"
sorry

definition MergeCSP2 :: 
"'a upred" where
"MergeCSP2 = `($ok\<acute> \<Leftrightarrow> ($ok\<^bsub>0\<^esub> \<and> $ok\<^bsub>1\<^esub>)) \<and> 
              ($wait\<acute> \<Leftrightarrow> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>)) \<and> 
              (($tr\<acute>-$tr)  \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> 
              ($ref\<acute> = $ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>)`"

definition InterleaveCSP2 ::
  "'a upred =>   'a upred \<Rightarrow> 'a upred" (infix "\<parallel>CSP" 100) where
"P \<parallel>CSP Q = P \<parallel>2\<^bsub>MergeCSP2 ;\<^sub>R SKIP\<^esub> Q"

lemma MergeCSP2_rel_closure: 
  "MergeCSP2 \<in> WF_RELATION"
apply(simp add:WF_RELATION_def MergeCSP2_def)
apply(rule unrest)
apply(rule unrest)
apply(simp add:typing closure defined unrest)
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(simp_all)
sorry

lemma aid:   "`($tr\<acute> - $tr \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> $tr\<^bsub>Suc 0\<^esub> - $tr)` \<in> WF_RELATION" 
apply(simp add:WF_RELATION_def)
apply(rule unrest)
apply(rule unrest)
apply(simp add:typing closure defined unrest)
apply(rule unrest)
apply(simp add:typing closure defined unrest)
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
apply(rule unrest)+ defer
sorry
(*
lemma pvaux_sub[simp]:
  fixes x :: "('a :: DEFINED, 'm :: VALUE) PVAR" 
  assumes "TYPEUSOUND('a,'m)"
  shows "pvaux (x\<^bsub>n\<^esub>) = pvaux x "
by (metis MkPVAR_def pvaux_MkPVAR pvchsub_def)
*)
lemma aid2:   "|$ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>Suc 0\<^esub>| \<rhd>\<^sub>* ref"
by(simp add:typing defined closure)

lemma MergeCSP2_form: 
"MergeCSP2 ;\<^sub>R SKIP = `((\<not>$ok\<^bsub>0\<^esub> \<or> \<not>$ok\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>)) \<or>  
                  ($ok\<^bsub>0\<^esub> \<and> $ok\<^bsub>1\<^esub> \<and> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute> = $ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>) \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
                  ($ok\<^bsub>0\<^esub> \<and> $ok\<^bsub>1\<^esub> \<and> \<not>$wait\<^bsub>0\<^esub> \<and> \<not>$wait\<^bsub>1\<^esub> \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> $ok\<acute> \<and> \<not> $wait\<acute>)`"
proof - 
have "MergeCSP2 ;\<^sub>R SKIP = `
     (\<not> ($ok\<^bsub>0\<^esub> \<and> $ok\<^bsub>1\<^esub>) \<and> ($wait\<acute> \<Leftrightarrow> $wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute> = $ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>)) ; ($tr \<le> $tr\<acute>) \<or>
     ($ok\<^bsub>0\<^esub> \<and> $ok\<^bsub>1\<^esub> \<and> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute> = $ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>) \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
     ($ok\<^bsub>0\<^esub> \<and> $ok\<^bsub>1\<^esub> \<and> \<not> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> (\<exists> ref\<acute> . ($ref\<acute> = $ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>)) \<and> $ok\<acute> \<and> \<not> $wait\<acute>)`"
apply(simp add: Skip_right MergeCSP2_rel_closure)
apply(simp add:MergeCSP2_def usubst typing defined closure)
apply(simp add:AndP_assoc)
apply(subst ExistsP_AndP_expand2[THEN sym])
apply(simp add:typing closure defined unrest)
apply(simp add:AndP_assoc[THEN sym])
done
also have "... = `(\<not> ($ok\<^bsub>0\<^esub> \<and> $ok\<^bsub>1\<^esub>) \<and> (\<exists> wait\<acute>\<acute> . $wait\<acute>\<acute> \<Leftrightarrow> $wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and> (\<exists> ref\<acute>\<acute> . ($ref\<acute>\<acute> = ($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>))) \<and> 
                      (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>)) \<or>  
                      ($ok\<^bsub>0\<^esub> \<and> $ok\<^bsub>1\<^esub> \<and> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute> = $ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>) \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
                      ($ok\<^bsub>0\<^esub> \<and> $ok\<^bsub>1\<^esub> \<and> \<not> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> $ok\<acute> \<and> \<not> $wait\<acute>)`"
apply(subst ExistsP_has_ty_value,simp_all add:typing closure defined unrest aid2)  
apply(subst SemiR_extract_variable_id[of "ref \<down>"],simp_all add:typing defined closure unrest)
apply(simp add:typing defined closure usubst erasure) 
apply(subst SemiR_extract_variable_id[of "wait \<down>"],simp_all add:typing defined closure unrest)
apply(simp add:typing defined closure usubst)
apply(subst AndP_comm) back back back
apply(simp add:AndP_assoc)
apply(simp add:SubstP_VarP_single_UNREST SubstE_VarE_single_UNREST typing closure defined unrest)
apply(subst SemiR_AndP_left_DASHED)
apply(rule unrest)
apply(rule unrest)
apply(rule unrest)
apply(rule unrest)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(rule unrest)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(rule unrest)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(rule unrest)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(subst ExistsP_AndP_expand1[THEN sym])
apply(simp add:typing closure defined unrest)
apply(subst ExistsP_AndP_expand1[THEN sym])
apply(simp add:typing closure defined unrest)
apply(subst ExistsP_AndP_expand1[THEN sym])
apply(simp add:typing closure defined unrest)
apply(subst ExistsP_AndP_expand2[THEN sym])
apply(simp add:typing closure defined unrest)
apply(subst ExistsP_AndP_expand2[THEN sym])
apply(simp add:typing closure defined unrest)
apply(simp add:AndP_OrP_distr AndP_OrP_distl AndP_assoc[THEN sym] OrP_assoc[THEN sym])
done
also have "... = `((\<not>$ok\<^bsub>0\<^esub> \<or> \<not>$ok\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>)) \<or>  
                  ($ok\<^bsub>0\<^esub> \<and> $ok\<^bsub>1\<^esub> \<and> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute> = $ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>) \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
                  ($ok\<^bsub>0\<^esub> \<and> $ok\<^bsub>1\<^esub> \<and> \<not>$wait\<^bsub>0\<^esub> \<and> \<not>$wait\<^bsub>1\<^esub> \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> $ok\<acute> \<and> \<not> $wait\<acute>)`"
proof -
  have 0 : "`\<exists> wait\<acute>\<acute> . $wait\<acute>\<acute> \<Leftrightarrow> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>)` = `true`" 
  proof -
    have "`\<exists> wait\<acute>\<acute> . $wait\<acute>\<acute> \<Leftrightarrow> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>)` = `(\<exists> wait\<acute>\<acute> . $wait\<acute>\<acute>=true \<and> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>)) \<or> (\<exists> wait\<acute>\<acute> . $wait\<acute>\<acute>=false \<and> \<not> $wait\<^bsub>0\<^esub> \<and> \<not> $wait\<^bsub>1\<^esub>) `" 
    apply(simp add:IffP_def ImpliesP_def demorgan1 AndP_OrP_distr AndP_OrP_distl AndP_assoc AndP_contra)
    apply(subst AndP_comm) back back
    apply(subst AndP_comm) back back back back
    apply(simp add:AndP_contra AndP_assoc[THEN sym] AndP_OrP_distr[THEN sym])
    apply(subst AndP_comm) back back
    apply(subst OrP_comm)
    apply(simp add:ExistsP_OrP_dist AndP_OrP_distr AndP_OrP_distl)
    apply(utp_poly_auto_tac)
      done
      also have "... = `true`"
      apply(subst ExistsP_AndP_expand1[THEN sym])
      apply(simp add:typing closure defined unrest)
      apply(subst ExistsP_has_ty_value) defer defer defer defer 
      apply(subst ExistsP_AndP_expand1[THEN sym])
      apply(simp add:typing closure defined unrest)
      apply(subst ExistsP_has_ty_value)
      apply(simp_all add:typing closure defined unrest)
      apply(simp add:demorgan1[THEN sym] OrP_excluded_middle)
      done
      finally show ?thesis ..
      qed
  show ?thesis
  apply(subst 0)
  apply(subst ExistsP_has_ty_value)
  apply(simp_all add:typing closure defined unrest aid2 demorgan1 demorgan2 AndP_assoc[THEN sym])
  done
qed
finally show ?thesis ..
qed

lemma InterleaveCSP_pre: 
assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
shows "CSP_Pre( P \<parallel>CSP Q )= \<not>\<^sub>p (((
        ((add_sub 0 on {tr \<down>\<acute>,ref \<down>\<acute>,wait \<down>\<acute>} \<bullet> \<not>\<^sub>p CSP_Pre P ) \<and>\<^sub>p (add_sub 1 on {tr \<down>\<acute>,ref \<down>\<acute>,wait \<down>\<acute>} \<bullet> CSP_Post Q)) \<or>\<^sub>p 
        ((add_sub 0 on {tr \<down>\<acute>,ref \<down>\<acute>,wait \<down>\<acute>} \<bullet> CSP_Post P ) \<and>\<^sub>p (add_sub 1 on {tr \<down>\<acute>,ref \<down>\<acute>,wait \<down>\<acute>} \<bullet> \<not>\<^sub>p CSP_Pre Q))
) \<and>\<^sub>p `(($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))` 
);\<^sub>R `($tr \<le> $tr\<acute>)`
)"
proof -
have "CSP_Pre( P \<parallel>CSP Q) = `\<not> (
        (P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and> 
        ($tr\<acute> = $tr) \<and> ($ref\<acute> = $ref)) ;
       ($ok \<and> \<not>$wait \<and> (\<not> $ok\<^bsub>0\<^esub> \<or> \<not> $ok\<^bsub>1\<^esub>) \<and> ((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr))) ; ($tr \<le> $tr\<acute>)))`"
apply(simp add:InterleaveCSP2_def CSP_Pre_def ParallelMerge_form)
apply(subst SubstP_SemiR_right)
apply(simp add:closure)
apply(simp add:unrest closure typing)
apply(subst MergeCSP2_form)
apply(subst SkipRA_unfold_aux_ty[of "ok"],simp_all add: typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "wait"],simp_all add: typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add: typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "ref"],simp_all add: typing defined closure)
apply(simp add:SubstP_SemiR_left closure unrest typing)
apply(simp add:usubst typing defined closure)
apply(simp add:SubstP_SemiR_right closure unrest typing)
apply(simp add:usubst typing defined closure)
apply(simp add:SkipRA_empty)
apply(subst SemiR_AndP_right_precond,simp_all add:typing defined closure urename) back
apply(subst SemiR_AndP_right_precond,simp_all add:typing defined closure urename) back
apply(simp add:AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back
apply(subst AndP_comm) back back back
apply(simp add:AndP_assoc[THEN sym])
sorry
also have "... = `\<not> (
        (P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and> 
        ($tr\<acute> = $tr) \<and> ($ref\<acute> = $ref) \<and> (\<not> $(ok\<^bsub>0\<^esub>\<acute>) \<or> \<not> $(ok\<^bsub>1\<^esub>\<acute>))) ;
       (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>))`"
apply(subst AndP_assoc) back back
apply(subst SemiR_remove_middle_unrest1[of _ _ "{ok \<down>,wait \<down>}"])
apply(simp_all add:typing defined closure unrest)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(simp add:assms)
apply(simp_all add:typing closure defined unrest) defer defer defer defer 
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(simp add:assms)
apply(simp_all add:typing closure defined unrest) defer defer defer defer
apply(rule closure)

apply(rule closure)
apply(rule closure)
apply(rule closure)
apply(simp add:UNDASHED_def)
apply(rule closure)
apply(rule closure)
apply(simp add:UNDASHED_def)
apply(rule closure)
apply(simp add:aid)
apply(simp add:closure) defer
apply(subst SemiR_AndP_right_precond)
apply(simp add:WF_CONDITION_def)
apply(rule conjI)
apply(simp add:WF_RELATION_def)
apply(rule unrest)
apply(rule unrest) defer
apply(rule unrest) defer 
apply(rule unrest)
apply(rule unrest)
apply(rule unrest)
apply(simp add:DASHED_def)
apply(rule unrest)
apply(rule unrest)
apply(simp add:DASHED_def)
apply(simp add:AndP_assoc[THEN sym] urename typing defined)
apply(subst ConvR_VarP_1)
apply(simp add:UNDASHED_def)
apply(subst ConvR_VarP_1)
apply(simp add:UNDASHED_def)
apply(simp)
apply(rule unrest)
apply(simp add:typing closure)
apply(rule unrest) defer
apply(rule unrest)
apply(simp add:typing closure)
apply(rule unrest) defer
apply(rule unrest)
apply(simp add:typing closure)
apply(rule unrest) defer
apply(rule unrest)
apply(simp add:typing closure)
apply(rule unrest) defer
apply(rule unrest)
apply(simp add:typing closure)
apply(rule unrest) defer
apply(rule unrest)
apply(simp add:typing closure)
apply(rule unrest) defer
apply(rule unrest)
apply(simp add:typing closure)
apply(rule unrest) defer
apply(rule unrest)
apply(simp add:typing closure)
apply(rule unrest) defer defer 
apply(rule unrest) defer
apply(rule unrest)
sorry
also have " ... = `\<not> ( \<exists> tr\<acute>\<acute> . (
        (P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and> 
        ($tr\<acute> = $tr) \<and> ($ref\<acute> = $ref) \<and> (\<not> $ok\<^bsub>0\<^esub>\<acute> \<or> \<not> $ok\<^bsub>1\<^esub>\<acute>)) ;
       ((($tr\<acute>\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> true) ; ($tr\<acute>\<acute> \<le> $tr\<acute>)))`"
proof -
have 0: "`($tr \<le> $tr\<acute>)[$tr\<acute>\<acute>/tr]` = `($tr\<acute>\<acute> \<le> $tr\<acute>)`"
by(simp add:usubst typing defined closure)
have 1: "`(($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>Suc 0\<^esub> - $tr))[$tr\<acute>\<acute>/tr\<acute>]` = `(($tr\<acute>\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>Suc 0\<^esub> - $tr))`"
by(simp add:usubst typing defined closure)
show ?thesis
apply(subst SemiR_extract_variable_id[of "tr \<down>"]) back
apply(simp_all add:typing defined closure unrest)
apply(subst ExistsP_SemiR_NON_REL_VAR_expand1)
apply(simp_all add:typing defined closure unrest assms)
apply(subst 0[THEN sym])
apply(subst 1[THEN sym])
apply(simp add:erasure typing closure defined)
done
qed
also have " ... = `\<not> ( \<exists> tr\<acute>\<acute> . (
        (P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and> 
        ($tr\<acute> = $tr) \<and> ($ref\<acute> = $ref) \<and> (\<not> $ok\<^bsub>0\<^esub>\<acute> \<or> \<not> $ok\<^bsub>1\<^esub>\<acute>) \<and> (($tr\<acute>\<acute> - $tr\<acute>) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr\<acute>) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr\<acute>))) ;
        true ; (true \<and> ($tr\<acute>\<acute> \<le> $tr\<acute>))))`"
proof -
have 0: "`(($tr\<acute>\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>Suc 0\<^esub> - $tr))\<acute>` = `(($tr\<acute>\<acute> - $tr\<acute>) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr\<acute>) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>Suc 0\<^esub>\<acute> - $tr\<acute>))`" 
sorry
show ?thesis
apply(subst SemiR_assoc)
apply(subst SemiR_AndP_right_DASHED)
apply(rule unrest)
apply(rule unrest)
apply(simp add:typing closure defined unrest)
apply(rule unrest)
apply(simp_all add:typing closure defined unrest)
apply(rule unrest)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(simp add:typing closure defined unrest)
apply(rule unrest)
apply(rule unrest)
apply(utp_poly_auto_tac)
apply(simp add:typing closure defined unrest)
apply(simp add:AndP_assoc[THEN sym] SemiR_assoc[THEN sym])
apply(simp add: 0)
done
qed
also have " ... = `\<not> ( \<exists> tr\<acute>\<acute> . (
        ((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and> 
        ($tr\<acute> = $tr) \<and> ($ref\<acute> = $ref) \<and> (\<not> $ok\<^bsub>0\<^esub>\<acute> \<or> \<not> $ok\<^bsub>1\<^esub>\<acute>) \<and> (($tr\<acute>\<acute> - $tr\<acute>) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr\<acute>) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr\<acute>))) ;
        ($tr\<acute>\<acute> \<le> $tr\<acute>))))`"
apply(subst SemiR_AndP_right_UNDASHED)
apply(simp_all add:closure typing defined unrest)
done
also have " ... = `\<not> ( \<exists> tr\<acute>\<acute> . (
        ((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and> 
        (\<not> $ok\<^bsub>0\<^esub>\<acute> \<or> \<not> $ok\<^bsub>1\<^esub>\<acute>) \<and> (($tr\<acute>\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))) ;
        ($tr\<acute>\<acute> \<le> $tr\<acute>))))`"

sorry


also have " ... = `\<not>  (
        ((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and> 
        (\<not> $ok\<^bsub>0\<^esub>\<acute> \<or> \<not> $ok\<^bsub>1\<^esub>\<acute>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))) ;
        ($tr \<le> $tr\<acute>)))`"
proof -
have 0: "`($tr \<le> $tr\<acute>)[$tr\<acute>\<acute>/tr]` = `($tr\<acute>\<acute> \<le> $tr\<acute>)`"
by(simp add:usubst typing defined closure)
have 1: "`(($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>Suc 0\<^esub>\<acute> - $tr))[$tr\<acute>\<acute>/tr\<acute>]` = `(($tr\<acute>\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>Suc 0\<^esub>\<acute> - $tr))`"
by(simp add:usubst typing defined closure)
show ?thesis
apply(subst SemiR_extract_variable_id[of "tr \<down>"]) back
apply(simp_all add:typing closure defined unrest assms)
apply(simp add:usubst typing defined closure)
apply(subst SubstP_twice_3) back back back back back back back back back back back back back back back
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_3) back back back back back back back back back back back back back back
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_3) back back back back back back back back back back back back back
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_3) back back back back back back back back back back back back
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_3) back back back back back back back back back back back
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_1)
apply(simp add:typing closure defined unrest SubstE_VarE_single_UNREST)
apply(subst SubstP_twice_3) back back back back back back back back back back back back back back back back back back back back
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_3) back back back back back back back back back back back back back back back back back back back
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_3) back back back back back back back back back back back back back back back back back back
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_3) back back back back back back back back back back back back back back back back back
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_3) back back back back back back back back back back back back back back back back 
apply(simp_all add:typing closure defined unrest)
apply(subst SubstP_twice_1)
apply(simp add:typing closure defined unrest SubstE_VarE_single_UNREST)
apply(subst 0[THEN sym])
apply(subst 1[THEN sym])
apply(simp add:typing defined closure erasure)
done
qed
also have " ... = `\<not>  (((
        ((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][false/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait]) \<or>
        (P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][false/ok\<acute>][true/ok][false/wait])) \<and> 
        (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))) ;
        ($tr \<le> $tr\<acute>)))`"
sorry
also have " ... = `\<not>  (((
        ((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][false/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>][true/ok][false/wait]) \<or>
        (P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>][true/ok][false/wait] \<and>
        Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][false/ok\<acute>][true/ok][false/wait])) \<and> 
        (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))) ;
        ($tr \<le> $tr\<acute>)))`"
sorry
also have " ... = `\<not>  (((
        ((\<not>CSP_Pre(P)[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>] \<and> CSP_Post(Q)[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>]) \<or>
        (CSP_Post(P)[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>] \<and> \<not>CSP_Pre(Q)[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>])) \<and> 
        (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))) ;
        ($tr \<le> $tr\<acute>)))`"
sorry
also have " ... = `\<not>  (((
        ((\<not>CSP_Pre(P)[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>] \<and> CSP_Post(Q)[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>]) \<or>
        (CSP_Post(P)[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>] \<and> \<not>CSP_Pre(Q)[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>])) \<and> 
        (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))) ;
        ($tr \<le> $tr\<acute>)))`"
sorry
finally show ?thesis 
sorry
qed

lemma Inter_form: 
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION" "P is CSP" "Q is CSP"
  shows "P \<parallel>CSP Q = `RHc(
  \<not>(
    (P \<^sub>f[($tr\<^bsub>0\<^esub>)/tr\<acute>][($wait\<^bsub>0\<^esub>)/wait\<acute>][($ref\<^bsub>0\<^esub>)/ref\<acute>][($ok\<^bsub>0\<^esub>)/ok\<acute>] \<and>
      Q \<^sub>f[($tr\<^bsub>1\<^esub>)/tr\<acute>][($wait\<^bsub>1\<^esub>)/wait\<acute>][($ref\<^bsub>1\<^esub>)/ref\<acute>][($ok\<^bsub>1\<^esub>)/ok\<acute>] \<and>
     (\<not> $ok\<^bsub>0\<^esub> \<or> \<not> $ok\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)))
     ; ($tr \<le> $tr\<acute>))
                                    \<turnstile>
      ((P \<^sub>f[($tr\<^bsub>0\<^esub>)/tr\<acute>][($wait\<^bsub>0\<^esub>)/wait\<acute>][($ref\<^bsub>0\<^esub>)/ref\<acute>][true/ok\<acute>] \<and>
     Q \<^sub>f[($tr\<^bsub>1\<^esub>)/tr\<acute>][($wait\<^bsub>1\<^esub>)/wait\<acute>][($ref\<^bsub>1\<^esub>)/ref\<acute>][true/ok\<acute>]
     \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr))) \<and>
     ((($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and> ($ref\<acute> = ($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>)))
      \<lhd> $wait\<acute> \<rhd>
        (\<not>$wait\<^bsub>0\<^esub> \<and> \<not>$wait\<^bsub>1\<^esub> )))   ; II\<^bsub>REA \<union> OKAY\<^esub>
                                                                                            )`"
proof - 
have 1: "`(P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>] \<and>
      Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>] \<and>
      II\<^bsub>{ok\<down>, ok\<down>\<acute>, wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>) ;
     ((\<not> $ok\<^bsub>0\<^esub> \<or> \<not> $ok\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>))`=
     `(P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>] \<and>
      Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>] \<and>
     (\<not> $ok\<^bsub>0\<^esub>\<acute> \<or> \<not> $ok\<^bsub>1\<^esub>\<acute>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))) ; ($tr \<le> $tr\<acute>)`"
sorry
have 2:
"`(P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
      Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
      II\<^bsub>{ok\<down>, ok\<down>\<acute>, wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>) ;
     ($ok\<^bsub>0\<^esub> \<and> $ok\<^bsub>1\<^esub> \<and> ($wait\<^bsub>0\<^esub> \<or> $wait\<^bsub>1\<^esub>) \<and>
      (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute> = ($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>)) \<and> $ok\<acute> \<and> $wait\<acute>)` = 
      `(P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
     Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
     ($wait\<^bsub>0\<^esub>\<acute> \<or> $wait\<^bsub>1\<^esub>\<acute>) \<and>
      (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr)) \<and> ($ref\<acute> = ($ref\<^bsub>0\<^esub>\<acute> \<union> $ref\<^bsub>1\<^esub>\<acute>)) 
      \<and> $ok\<acute> \<and> $wait\<acute>); II\<^bsub>REA \<union> OKAY\<^esub>`"
sorry
have 3: "`(P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>] \<and>
      Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>] \<and>
      II\<^bsub>{ok\<down>, ok\<down>\<acute>, wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>}\<^esub>) ;
     ($ok\<^bsub>0\<^esub> \<and> $ok\<^bsub>1\<^esub> \<and> \<not> $wait\<^bsub>0\<^esub> \<and> \<not> $wait\<^bsub>1\<^esub> \<and> 
     (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> $ok\<acute> \<and> \<not> $wait\<acute>)` = 
     `(P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][false/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
      Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][false/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
     (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute>  - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))
     \<and> $ok\<acute> \<and> \<not> $wait\<acute>); II\<^bsub>REA \<union> OKAY\<^esub>`"
sorry
have "P \<parallel>CSP Q = `
((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>] \<and>
      Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>] \<and>
     (\<not> $ok\<^bsub>0\<^esub>\<acute> \<or> \<not> $ok\<^bsub>1\<^esub>\<acute>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))) ; ($tr \<le> $tr\<acute>)
   ) \<or>((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
     Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
     ($wait\<^bsub>0\<^esub>\<acute> \<or> $wait\<^bsub>1\<^esub>\<acute>) \<and>
      (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr)) \<and> ($ref\<acute> = ($ref\<^bsub>0\<^esub>\<acute> \<union> $ref\<^bsub>1\<^esub>\<acute>)) 
      \<and> $ok\<acute> \<and> $wait\<acute>); II\<^bsub>REA \<union> OKAY\<^esub>
    )\<or>((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][false/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
      Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][false/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and>
     (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub>\<acute>  - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub>\<acute> - $tr))
     \<and> $ok\<acute> \<and> \<not> $wait\<acute>); II\<^bsub>REA \<union> OKAY\<^esub>
    )`"
apply(simp add: InterleaveCSP2_def)
apply(simp add: ParallelMerge_form)
apply(simp add: MergeCSP2_form)
apply(simp add:SemiR_OrP_distl)
sorry
show ?thesis 
sorry
qed

lemma hand: "P ;\<^sub>R MergeCSP2 ;\<^sub>R SKIP =  `(
      (((P[false/(ok\<^bsub>0\<^esub>)\<acute>]) \<or> (P[false/(ok\<^bsub>1\<^esub>)\<acute>])) ; 
              (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>)) \<or> 
     (((P[true/(ok\<^bsub>0\<^esub>)\<acute>][true/(ok\<^bsub>1\<^esub>)\<acute>][true/(wait\<^bsub>0\<^esub>)\<acute>] \<or> (P[true/(ok\<^bsub>0\<^esub>)\<acute>][true/(ok\<^bsub>1\<^esub>)\<acute>][true/(wait\<^bsub>1\<^esub>)\<acute>])) ; 
              ((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute>=($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>)))) \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
      ((P[true/(ok\<^bsub>0\<^esub>)\<acute>][true/(ok\<^bsub>1\<^esub>)\<acute>][false/(wait\<^bsub>0\<^esub>)\<acute>][false/(wait\<^bsub>1\<^esub>)\<acute>] ; 
              (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr))) \<and> $ok\<acute> \<and> \<not> $wait\<acute>))`"

proof -
have "P ;\<^sub>R MergeCSP2 ;\<^sub>R SKIP = `(
      (P \<and> \<not> ($ok\<^bsub>0\<^esub>)\<acute>) ; (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>) \<or> 
      (P \<and> \<not> ($ok\<^bsub>1\<^esub>)\<acute>) ; (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>) \<or>
     ((P \<and> ($ok\<^bsub>0\<^esub>)\<acute> \<and> ($ok\<^bsub>1\<^esub>)\<acute> \<and> ($wait\<^bsub>0\<^esub>)\<acute>) ; ((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute>=($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>))) \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
     ((P \<and> ($ok\<^bsub>0\<^esub>)\<acute> \<and> ($ok\<^bsub>1\<^esub>)\<acute> \<and> ($wait\<^bsub>1\<^esub>)\<acute>) ; ((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute>=($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>))) \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
     ((P \<and> ($ok\<^bsub>0\<^esub>)\<acute> \<and> ($ok\<^bsub>1\<^esub>)\<acute> \<and> \<not> ($wait\<^bsub>0\<^esub>)\<acute> \<and> \<not> ($wait\<^bsub>1\<^esub>)\<acute>) ; (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> $ok\<acute> \<and> \<not> $wait\<acute>))`"
apply(simp add:MergeCSP2_form SemiR_OrP_distl)
apply(subst SemiR_AndP_right_DASHED) defer 
apply(subst SemiR_AndP_right_DASHED) defer 
apply(subst SemiR_AndP_right_DASHED) defer 
apply(subst SemiR_AndP_right_DASHED) defer 
apply(subst SemiR_AndP_right_DASHED) back defer 
apply(subst SemiR_AndP_right_DASHED) back defer 
apply(subst SemiR_AndP_right_DASHED) back defer 
apply(subst SemiR_AndP_right_DASHED) back defer defer 
apply(simp_all add:typing defined closure unrest DASHED_def)
apply(simp add:typing defined closure urename AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back
apply(subst SemiR_AndP_right_UNDASHED) defer 
apply(subst SemiR_AndP_right_UNDASHED) back defer 
apply(simp_all add:typing defined closure unrest UNDASHED_def) 
apply(simp add:AndP_OrP_distl SemiR_OrP_distr AndP_OrP_distr AndP_assoc[THEN sym] OrP_assoc[THEN sym])
done
also have "... = `(
      (P[false/ok\<^bsub>0\<^esub>\<acute>] \<and> \<not> ($ok\<^bsub>0\<^esub>)\<acute>) ; (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>) \<or> 
      (P[false/ok\<^bsub>1\<^esub>\<acute>] \<and> \<not> ($ok\<^bsub>1\<^esub>)\<acute>) ; (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>) \<or>
     ((P[true/ok\<^bsub>0\<^esub>\<acute>][true/ok\<^bsub>1\<^esub>\<acute>][true/wait\<^bsub>0\<^esub>\<acute>] \<and> ($ok\<^bsub>0\<^esub>)\<acute> \<and> ($ok\<^bsub>1\<^esub>)\<acute> \<and> ($wait\<^bsub>0\<^esub>)\<acute>) ; ((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute>=($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>))) \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
     ((P[true/ok\<^bsub>0\<^esub>\<acute>][true/ok\<^bsub>1\<^esub>\<acute>][true/wait\<^bsub>1\<^esub>\<acute>] \<and> ($ok\<^bsub>0\<^esub>)\<acute> \<and> ($ok\<^bsub>1\<^esub>)\<acute> \<and> ($wait\<^bsub>1\<^esub>)\<acute>) ; ((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute>=($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>))) \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
     ((P[true/ok\<^bsub>0\<^esub>\<acute>][true/ok\<^bsub>1\<^esub>\<acute>][false/wait\<^bsub>0\<^esub>\<acute>][false/wait\<^bsub>1\<^esub>\<acute>] \<and> ($ok\<^bsub>0\<^esub>)\<acute> \<and> ($ok\<^bsub>1\<^esub>)\<acute> \<and> \<not> ($wait\<^bsub>0\<^esub>)\<acute> \<and> \<not> ($wait\<^bsub>1\<^esub>)\<acute>) ; (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> $ok\<acute> \<and> \<not> $wait\<acute>))`"
sorry
also have "... = `(
      P[false/ok\<^bsub>0\<^esub>\<acute>] ; (\<not> ($ok\<^bsub>0\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr))) ; ($tr \<le> $tr\<acute>) \<or> 
      P[false/ok\<^bsub>1\<^esub>\<acute>] ; (\<not> ($ok\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr))) ; ($tr \<le> $tr\<acute>) \<or>
     (P[true/ok\<^bsub>0\<^esub>\<acute>][true/ok\<^bsub>1\<^esub>\<acute>][true/wait\<^bsub>0\<^esub>\<acute>] ; (($ok\<^bsub>0\<^esub>) \<and> ($ok\<^bsub>1\<^esub>) \<and> ($wait\<^bsub>0\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute>=($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>))) \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
     (P[true/ok\<^bsub>0\<^esub>\<acute>][true/ok\<^bsub>1\<^esub>\<acute>][true/wait\<^bsub>1\<^esub>\<acute>] ; (($ok\<^bsub>0\<^esub>) \<and> ($ok\<^bsub>1\<^esub>) \<and> ($wait\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute>=($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>))) \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
     (P[true/ok\<^bsub>0\<^esub>\<acute>][true/ok\<^bsub>1\<^esub>\<acute>][false/wait\<^bsub>0\<^esub>\<acute>][false/wait\<^bsub>1\<^esub>\<acute>] ; (($ok\<^bsub>0\<^esub>) \<and> ($ok\<^bsub>1\<^esub>) \<and> \<not> ($wait\<^bsub>0\<^esub>) \<and> \<not> ($wait\<^bsub>1\<^esub>) \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr))) \<and> $ok\<acute> \<and> \<not> $wait\<acute>))`"
sorry
also have "... = `(
      P[false/ok\<^bsub>0\<^esub>\<acute>] ; (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>) \<or> 
      P[false/ok\<^bsub>1\<^esub>\<acute>] ; (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) ; ($tr \<le> $tr\<acute>) \<or>
     (P[true/ok\<^bsub>0\<^esub>\<acute>][true/ok\<^bsub>1\<^esub>\<acute>][true/wait\<^bsub>0\<^esub>\<acute>] ; ((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute>=($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>))) \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
     (P[true/ok\<^bsub>0\<^esub>\<acute>][true/ok\<^bsub>1\<^esub>\<acute>][true/wait\<^bsub>1\<^esub>\<acute>] ; ((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute>=($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>))) \<and> $ok\<acute> \<and> $wait\<acute>) \<or>
     (P[true/ok\<^bsub>0\<^esub>\<acute>][true/ok\<^bsub>1\<^esub>\<acute>][false/wait\<^bsub>0\<^esub>\<acute>][false/wait\<^bsub>1\<^esub>\<acute>] ; (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> $ok\<acute> \<and> \<not> $wait\<acute>))`"
sorry
finally show ?thesis sorry
qed


lemma Interleave_R1: 
  assumes "P is R1" "Q is R1"
  shows "P \<parallel>CSP Q is R1"
proof -
have " P \<parallel>CSP Q =`
((
    ((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][false/ok\<acute>] \<and> Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>1\<^esub>\<acute>)/ok\<acute>]) \<or>
     (P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>] \<and> Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][false/ok\<acute>]))
 \<and> (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr))) ; ($tr \<le> $tr\<acute>)) \<or>
(((((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][true/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and> Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>1\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>]) \<or> 
    (P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and> Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][true/wait\<acute>][($ref\<^bsub>1\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>])) \<and> ($tr\<acute>=$tr)) ;
      ((($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr)) \<and> ($ref\<acute> = ($ref\<^bsub>0\<^esub> \<union> $ref\<^bsub>1\<^esub>)))) \<and>
      $ok\<acute> \<and> $wait\<acute>) \<or>
(((P[($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][false/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][true/ok\<acute>] \<and> Q[($tr\<^bsub>1\<^esub>\<acute>)/tr\<acute>][false/wait\<acute>][($ref\<^bsub>1\<^esub>)\<acute>/ref\<acute>][true/ok\<acute>] \<and> ($tr\<acute>=$tr)) ;
     (($tr\<acute> - $tr) \<in> ($tr\<^bsub>0\<^esub> - $tr) \<parallel>\<^bsub>{}\<^esub> ($tr\<^bsub>1\<^esub> - $tr))) \<and>
     $ok\<acute> \<and> \<not> $wait\<acute>)`"
apply(simp add:is_healthy_def R1_def InterleaveCSP2_def ParallelMerge_form hand)
sorry
show ?thesis sorry qed

lemma Interleave_R2: 
  assumes "P is R2" "Q is R2" "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "P \<parallel>CSP Q is R2"
sorry

lemma Interleave_R3c: 
  assumes "P is R3c" "Q is R3c"
  shows "P \<parallel>CSP Q is R3c"
proof-
from assms have "P \<parallel>CSP Q = (R3c P) \<parallel>CSP (R3c Q)" sorry
also have "... = ` ((
      (\<not> $ok \<and> $wait \<and> ($tr \<le> $tr\<^bsub>0\<^esub>\<acute>) \<and> ($tr \<le> $tr\<^bsub>1\<^esub>\<acute>)) \<or>
      ($ok \<and> $wait \<and> ($wait\<^bsub>0\<^esub>\<acute>=$wait) \<and> ($ref\<^bsub>0\<^esub>\<acute>=$ref) \<and> ($tr\<^bsub>0\<^esub>\<acute>=$tr) \<and> ($ok\<^bsub>0\<^esub>\<acute>=$ok) \<and> ($wait\<^bsub>Suc 0\<^esub>\<acute>=$wait) \<and> ($ref\<^bsub>Suc 0\<^esub>\<acute>=$ref) \<and> ($tr\<^bsub>Suc 0\<^esub>\<acute>=$tr) \<and> ($ok\<^bsub>Suc 0\<^esub>\<acute>=$ok) \<and> II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>} - {ref\<down>, ref\<down>\<acute>} - {tr\<down>, tr\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub>) \<or>
      (\<not> $wait \<and> P[false/wait][($tr\<^bsub>0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>0\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>0\<^esub>\<acute>)/ok\<acute>] \<and> Q[false/wait][($tr\<^bsub>Suc 0\<^esub>\<acute>)/tr\<acute>][($wait\<^bsub>Suc 0\<^esub>\<acute>)/wait\<acute>][($ref\<^bsub>Suc 0\<^esub>\<acute>)/ref\<acute>][($ok\<^bsub>Suc 0\<^esub>\<acute>)/ok\<acute>]) 
     ) \<and> II\<^bsub>REA \<union> OKAY\<^esub>) ;
    MergeCSP2 ; SKIP`" 
apply(simp add:InterleaveCSP2_def ParallelMerge_form)
apply(simp add:R3c_form SkipR_as_SkipRA)
apply(subst SkipRA_unfold_aux_ty[of "wait"])
apply(simp_all add:typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "ref"])
apply(simp_all add:typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "tr"])
apply(simp_all add:typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "ok"])
apply(simp_all add:typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "wait"]) back
apply(simp_all add:typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "ref"]) back
apply(simp_all add:typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "tr"]) back
apply(simp_all add:typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "ok"]) back
apply(simp_all add:typing defined closure)
apply(simp add:usubst typing defined closure)

sorry
also have "... = undefined"
apply(simp add:MergeCSP2_form SemiR_OrP_distl)
apply(subst SemiR_AndP_right_DASHED) defer 
apply(subst SemiR_AndP_right_DASHED) defer 
apply(subst SemiR_AndP_right_DASHED) defer 
apply(subst SemiR_AndP_right_DASHED) defer 
apply(subst SemiR_AndP_right_DASHED) back defer 
apply(subst SemiR_AndP_right_DASHED) back defer 
apply(subst SemiR_AndP_right_DASHED) back defer 
apply(subst SemiR_AndP_right_DASHED) back defer defer 
apply(simp_all add:typing defined closure unrest DASHED_def)
apply(simp add:typing defined closure urename)
sorry
show ?thesis sorry
qed

lemma Interleave_CSP1: 
  assumes "P is CSP1" "Q is CSP1"
shows "P \<parallel>CSP Q is CSP1"
sorry

lemma Interleave_CSP2: 
  assumes "P is CSP2" "Q is CSP2"
  shows "P \<parallel>CSP Q is CSP2"
apply(simp add:is_healthy_def H2_def InterleaveCSP2_def ParallelMerge_form SemiR_assoc[THEN sym])
apply(simp add:H2_def[THEN sym])
apply(metis Skip_CSP2 is_healthy_def)
done

lemma Interleave_CSP: 
  assumes "P is CSP" "Q is CSP"
  shows "`P ||| Q` is CSP"
sorry

lemma Interleave_closure[closure]: 
  assumes "P \<in> WF_RELATION" "Q \<in> WF_RELATION"
  shows "`P ||| Q` \<in> WF_RELATION"
sorry

end