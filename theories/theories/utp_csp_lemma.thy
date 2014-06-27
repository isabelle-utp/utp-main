(******************************************************************************)
(* Project: Mechanation of the UTP                                            *)
(* File: utp_csp.thy                                                          *)
(* Authors: Samuel Canham and Simon Foster, University of York                *)
(******************************************************************************)

header {* CSP Processes *}

theory utp_csp_lemma
  imports utp_csp
begin


lemma Parallel_Design: "`P \<parallel>\<^bsub>A\<^esub> Q` = 
  `RHc( ( \<forall>tr\<^bsub>0\<^esub>\<acute> . ( \<forall>tr\<^bsub>1\<^esub>\<acute> . 
          (($tr \<le> $tr\<^bsub>0\<^esub>\<acute>) \<and> ($tr \<le> $tr\<^bsub>1\<^esub>\<acute>) \<and> 
          (($tr\<acute>-$tr) \<in> (($tr\<^bsub>0\<^esub>\<acute>-$tr)\<parallel>\<^bsub>A\<^esub>($tr\<^bsub>1\<^esub>\<acute>-$tr))))
                            \<Rightarrow>
          ( CSP_Pre(P)[$tr\<^bsub>0\<^esub>\<acute>/tr\<acute>] \<and> CSP_Pre(Q)[$tr\<^bsub>1\<^esub>\<acute>/tr\<acute>]))) 
                                        \<turnstile> 
        (\<exists>tr\<^bsub>0\<^esub>\<acute> . (\<exists>wait\<^bsub>0\<^esub>\<acute> . (\<exists>ref\<^bsub>0\<^esub>\<acute>. 
        (\<exists>tr\<^bsub>1\<^esub>\<acute> . (\<exists>wait\<^bsub>1\<^esub>\<acute> . (\<exists>ref\<^bsub>1\<^esub>\<acute>.
                ($tr \<le> $tr\<^bsub>0\<^esub>\<acute>) \<and> ($tr \<le> $tr\<^bsub>1\<^esub>\<acute>) \<and> 
                (($tr\<acute>-$tr) \<in> (($tr\<^bsub>0\<^esub>\<acute>-$tr)\<parallel>\<^bsub>A\<^esub>($tr\<^bsub>1\<^esub>\<acute>-$tr))) \<and>
                          ($wait\<acute> \<Rightarrow> ($wait\<^bsub>0\<^esub>\<acute> \<or> $wait\<^bsub>1\<^esub>\<acute>)) \<and>
                          (($wait\<^bsub>0\<^esub>\<acute> \<or> $wait\<^bsub>1\<^esub>\<acute>) \<Rightarrow> $wait\<acute>) \<and>
                                    ($ref\<acute> = ($ref\<^bsub>0\<^esub>\<acute> \<inter> $ref\<^bsub>1\<^esub>\<acute>)) \<and>
       CSP_Post(P)[$tr\<^bsub>0\<^esub>\<acute>/tr\<acute>][$wait\<^bsub>0\<^esub>\<acute>/wait\<acute>][$ref\<^bsub>0\<^esub>\<acute>/ref\<acute>] \<and>
       CSP_Post(Q)[$tr\<^bsub>1\<^esub>\<acute>/tr\<acute>][$wait\<^bsub>1\<^esub>\<acute>/wait\<acute>][$ref\<^bsub>1\<^esub>\<acute>/ref\<acute>]                 )))))))`"
sorry

lemma Skip_par_stop: "`SKIP \<parallel>\<^bsub>A\<^esub> STOP` = `STOP`" 
proof -
have a: "`((($wait\<acute> \<Rightarrow> $wait\<^bsub>0\<^esub>\<acute> \<or> $wait\<^bsub>1\<^esub>\<acute>) \<and>
             ($wait\<^bsub>0\<^esub>\<acute> \<or> $wait\<^bsub>1\<^esub>\<acute> \<Rightarrow> $wait\<acute>)) \<and>
            \<not> ($wait\<^bsub>0\<^esub>\<acute>)) \<and>
           ($wait\<^bsub>1\<^esub>\<acute>)`= `$wait\<acute> \<and> \<not>($wait\<^bsub>0\<^esub>\<acute>) \<and> ($wait\<^bsub>1\<^esub>\<acute>)`"
sorry
have b: "`(\<exists> ref\<^bsub>0\<^esub>\<acute>.
              (\<exists> ref\<^bsub>1\<^esub>\<acute>.
                 ($ref\<acute> = ($ref\<^bsub>0\<^esub>\<acute> \<inter> $ref\<^bsub>1\<^esub>\<acute>))))` = `true`"
sorry
have c:  "`(\<exists> wait\<^bsub>0\<^esub>\<acute>. \<not> $wait\<^bsub>0\<^esub>\<acute>)` = `true`" sorry
have d:  "`(\<exists> wait\<^bsub>1\<^esub>\<acute>. $wait\<^bsub>1\<^esub>\<acute>)` = `true`" sorry
have "`SKIP \<parallel>\<^bsub>A\<^esub> STOP` =
` RHc (true \<turnstile>
         (\<exists> ref\<^bsub>0\<^esub>\<acute> .
          (\<exists> ref\<^bsub>1\<^esub>\<acute> .
          ($ref\<acute> = ($ref\<^bsub>0\<^esub>\<acute> \<inter> $ref\<^bsub>1\<^esub>\<acute>)) \<and>
          (\<exists> wait\<^bsub>0\<^esub>\<acute> .
           (\<exists> wait\<^bsub>1\<^esub>\<acute> .
           (((($wait\<acute> \<Rightarrow> $wait\<^bsub>0\<^esub>\<acute> \<or> $wait\<^bsub>1\<^esub>\<acute>) \<and>
              ($wait\<^bsub>0\<^esub>\<acute> \<or> $wait\<^bsub>1\<^esub>\<acute> \<Rightarrow> $wait\<acute>)) \<and>
             \<not> ($wait\<^bsub>0\<^esub>\<acute>)) \<and>
            ($wait\<^bsub>1\<^esub>\<acute>)) \<and>
           (\<exists> tr\<^bsub>0\<^esub>\<acute> .
            (\<exists> tr\<^bsub>1\<^esub>\<acute> .
            ((((($tr \<le> $tr\<^bsub>0\<^esub>\<acute>) \<and> ($tr \<le> $tr\<^bsub>1\<^esub>\<acute>)) \<and>
               ($tr\<acute> - $tr \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>A\<^esub> $tr\<^bsub>1\<^esub>\<acute> - $tr)) \<and>
              ($tr\<^bsub>0\<^esub>\<acute> = $tr)) \<and>
             ($tr\<^bsub>1\<^esub>\<acute> = $tr)) \<and>
            II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub>)))))))`"
apply(subst Parallel_Design)
apply(simp add:Skip_pre Skip_post Stop_pre Stop_post)
apply(simp add:usubst typing defined closure ExprP_as_PExprP)
apply(subst ForallP_ident,simp add:typing defined closure unrest)
apply(subst ForallP_ident,simp add:typing defined closure unrest)
apply(subst ExistsP_commute)
apply(subst ExistsP_commute) back
apply(subst ExistsP_commute) back back back
apply(subst ExistsP_commute) back back
apply(subst ExistsP_commute) back back back back
apply(subst ExistsP_commute) back back back
apply(subst ExistsP_commute)
apply(subst ExistsP_commute) back back
apply(subst ExistsP_commute) back
apply(simp add:AndP_assoc,subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back back back
apply(subst ExistsP_AndP_expand2[THEN sym]) defer
apply(subst ExistsP_AndP_expand2[THEN sym]) defer
apply(subst ExistsP_AndP_expand2[THEN sym]) defer
apply(subst ExistsP_AndP_expand2[THEN sym]) defer
apply(simp add:AndP_assoc,subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back back 
apply(subst ExistsP_AndP_expand2[THEN sym]) back defer
apply(subst ExistsP_AndP_expand2[THEN sym]) back defer
apply(simp add:AndP_assoc,subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back back back
apply(subst ExistsP_AndP_expand2[THEN sym]) back back defer
apply(subst ExistsP_AndP_expand2[THEN sym]) back back defer
apply(simp add:AndP_assoc,subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back back back back back
apply(subst ExistsP_AndP_expand2[THEN sym]) back back defer
apply(subst ExistsP_AndP_expand2[THEN sym]) back back defer
apply(simp add:AndP_assoc,subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back back back back back back back back
apply(subst ExistsP_AndP_expand2[THEN sym]) back back defer
apply(subst ExistsP_AndP_expand2[THEN sym]) back back defer
apply(subst AndP_comm) back back back back back back back back back
apply(simp add:AndP_assoc)
sorry
also have "... =
` RHc (true \<turnstile>
         (\<exists> ref\<^bsub>0\<^esub>\<acute> .
          (\<exists> ref\<^bsub>1\<^esub>\<acute> .
          ($ref\<acute> = ($ref\<^bsub>0\<^esub>\<acute> \<inter> $ref\<^bsub>1\<^esub>\<acute>)) \<and>
          (\<exists> wait\<^bsub>0\<^esub>\<acute> .
           (\<exists> wait\<^bsub>1\<^esub>\<acute> .
           ($wait\<acute> \<and> \<not> ($wait\<^bsub>0\<^esub>\<acute>) \<and> ($wait\<^bsub>1\<^esub>\<acute>)) \<and>
           (\<exists> tr\<^bsub>0\<^esub>\<acute> .
            (\<exists> tr\<^bsub>1\<^esub>\<acute> .
            ((((($tr \<le> $tr\<^bsub>0\<^esub>\<acute>) \<and> ($tr \<le> $tr\<^bsub>1\<^esub>\<acute>)) \<and>
               ($tr\<acute> - $tr \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>A\<^esub> $tr\<^bsub>1\<^esub>\<acute> - $tr)) \<and>
              ($tr\<^bsub>0\<^esub>\<acute> = $tr)) \<and>
             ($tr\<^bsub>1\<^esub>\<acute> = $tr)) \<and>
            II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub>)))))))`"
by (metis a)
also have "... = ` RHc (true \<turnstile> (
         $wait\<acute> \<and>
         (\<exists> tr\<^bsub>0\<^esub>\<acute> .
          (\<exists> tr\<^bsub>1\<^esub>\<acute> .
          ((((($tr \<le> $tr\<^bsub>0\<^esub>\<acute>) \<and> ($tr \<le> $tr\<^bsub>1\<^esub>\<acute>)) \<and>
             ($tr\<acute> - $tr \<in> ($tr\<^bsub>0\<^esub>\<acute> - $tr) \<parallel>\<^bsub>A\<^esub> $tr\<^bsub>1\<^esub>\<acute> - $tr)) \<and>
            ($tr\<^bsub>0\<^esub>\<acute> = $tr)) \<and>
           ($tr\<^bsub>1\<^esub>\<acute> = $tr)) \<and>
          II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub>))))`"
apply(subst ExistsP_AndP_expand1[THEN sym]) defer 
apply(subst ExistsP_AndP_expand1[THEN sym]) defer 
apply(subst ExistsP_AndP_expand1[THEN sym]) defer 
apply(subst ExistsP_AndP_expand1[THEN sym]) defer
apply(subst ExistsP_AndP_expand2[THEN sym]) defer 
apply(subst ExistsP_AndP_expand2[THEN sym]) defer 
apply(subst ExistsP_AndP_expand2[THEN sym]) defer 
apply(subst ExistsP_AndP_expand1[THEN sym]) defer 
apply(subst b)
apply(subst c)
apply(subst d)
apply(simp)
sorry
also have "... =  `RHc (true \<turnstile> ($wait\<acute> \<and>
         (II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub> \<and>
         ($tr\<acute> = $tr))))` "
apply(subst AndP_comm) back back back back back
apply(simp add:AndP_assoc[THEN sym])
apply(simp add:AndP_assoc)
apply(simp add:typing defined closure erasure)
apply(subst ExistsP_one_point)
apply(simp add:typing closure defined)
apply(simp add:typing closure defined unrest)
apply(simp add:typing closure defined usubst)
apply(subst ExistsP_one_point)
apply(simp add:typing closure defined)
apply(simp add:typing closure defined unrest)
apply(simp add:typing closure defined usubst)
apply(subst SubstP_VarP_single_UNREST) defer
apply(subst SubstP_VarP_single_UNREST) defer
apply(subst SubstP_VarP_single_UNREST) defer
apply(subst SubstP_VarP_single_UNREST) back back defer
sorry
also have "... = `STOP`"
apply(subst Stop_design)
sorry
finally show ?thesis .
qed

lemma Skip_choice_a_skip: "`((a \<rightarrow> SKIP)\<box>SKIP)` = `SKIP \<or> ((a \<rightarrow> SKIP)\<box>RHc(($tr \<le> $tr\<acute>) \<turnstile> false))`" sorry
lemma OrP_Parallel_distl: "`(P \<or> Q) \<parallel>\<^bsub>A\<^esub> R` = `(P \<parallel>\<^bsub>A\<^esub> R) \<or> (Q \<parallel>\<^bsub>A\<^esub> R)`" sorry
lemma DesignREA_pre:
  assumes "A is R2" "{ok\<down>,wait\<down>,ok\<down>\<acute>} \<sharp> A"
  shows "`CSP_Pre(RHc(A \<turnstile> B))` = `A`"
sorry
lemma DesignREA_post:
  assumes "A is R2" "B is R2" "{ok\<down>,wait\<down>,ok\<down>\<acute>} \<sharp> A" "{ok\<down>,wait\<down>,ok\<down>\<acute>} \<sharp> B"
  shows "`CSP_Post(RHc(A \<turnstile> B))` = `A \<Rightarrow> B`"
sorry
lemma DesignREA_CSP: 
  shows "`RHc( A \<turnstile> B )` is CSP"
sorry
lemma Miracle_post: 
  "`CSP_Post(RHc(($tr \<le> $tr\<acute>) \<turnstile> false))` = `false`"
sorry
lemma Miracle_pre:
  "`CSP_Pre(RHc(($tr \<le> $tr\<acute>) \<turnstile> false))` = `($tr \<le> $tr\<acute>)`"
sorry
lemma OrP_external: 
  "`(A \<or> B)\<box> C` = `(A \<box> C) \<or> (B \<box> C)`"
sorry
lemma Stop_external_unit:
  "`STOP \<box> P` = `P`"
sorry
lemma Stop_par:
  assumes "P is CSP"
  shows "`P \<parallel>\<^bsub>A\<^esub> STOP` = `RHc( CSP_Pre(P) \<turnstile> (\<exists> wait\<acute>\<acute> . (\<exists> ref\<acute>\<acute> . (CSP_Post(P)[$wait\<acute>\<acute>/wait\<acute>][$ref\<acute>\<acute>/ref\<acute>] \<and> ($ref\<acute>\<subseteq>$ref\<acute>\<acute>) \<and> $wait\<acute>))))`"
sorry
lemma CSP_expansion: 
  "`CSP(P)` = `(\<not>$ok \<and> ($tr\<le>$tr\<acute>)) \<or> ($ok \<and> $wait \<and> II\<^bsub>REL_VAR\<^esub>) \<or> ($ok \<and> \<not>$wait \<and> R2(P\<^sup>f)) \<or> ($ok \<and> \<not>$wait \<and> $ok\<acute> \<and> R2(P\<^sup>t))`"
sorry
lemma NotP_Stop:
  "`\<not>STOP` = `\<not>(\<not> $ok \<and> ($tr \<le> $tr\<acute>)) \<and>
             \<not> ($ok \<and> $wait \<and> II) \<and> 
             \<not> ($ok \<and> \<not> $wait \<and> ($tr\<acute> = $tr) \<and> $wait\<acute> \<and> $ok\<acute>)`"
apply(simp add:Stop_design DesignREA_form R2_def R2s_def usubst typing defined closure R1_extend_AndP[THEN sym])
apply(simp add:R1_def tr_prefix_as_nil AndP_assoc[THEN sym] demorgan1)
done
lemma CSP2_NotP_Stop_AndP:
  assumes "P is CSP"  
  shows "`CSP2(\<not>STOP \<and> P)` = `$ok \<and> \<not> $wait \<and> (CSP_Pre (P) \<Rightarrow> (CSP_Post (P) \<and> \<not> (($tr\<acute> = $tr) \<and> $wait\<acute>) \<and> $ok\<acute>))`"
proof-
  have "`CSP2(\<not>STOP \<and> P)` = `CSP2 ($ok \<and> \<not> $wait \<and>
           ( R2 (\<not> CSP_Pre (P)) \<or> ($ok\<acute> \<and> R2 (CSP_Post(P)))) \<and>
       \<not> (($tr\<acute> = $tr) \<and> $wait\<acute> \<and> $ok\<acute>)) `"
  apply(subst AndP_comm)
  apply(simp add: NotP_Stop)
  apply(subst CSP_form[of "P"],simp add:assms)
  apply(utp_poly_auto_tac)
done
  also have "... = `$ok \<and> \<not> $wait \<and> (R2 (\<not> CSP_Pre(P)) \<or> (R2 (CSP_Post(P)) \<and> \<not> (($tr\<acute> = $tr) \<and> $wait\<acute>) \<and> $ok\<acute>))`"
  apply(simp add:H2_split usubst typing defined closure AndP_assoc[THEN sym] AndP_OrP_distl[THEN sym])
  apply(subst SubstP_VarP_single_UNREST) defer 
  apply(subst SubstP_VarP_single_UNREST) defer  
  apply(subst SubstP_VarP_single_UNREST) defer 
  apply(utp_poly_auto_tac) defer 
  apply(simp_all add:CSP_Pre_def CSP_Post_def R2_def R2s_def R1_def usubst typing defined closure)
  apply(simp_all add:typing defined closure unrest)
done
  finally show ?thesis
    apply(simp add:CSP_Pre_R2_commute[THEN sym] CSP_Post_R2_commute[THEN sym] ImpliesP_def[THEN sym])
    apply(metis assms is_healthy_def CSP_is_RHc RHc_is_R2)
    done
qed

lemma 
  assumes "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>, wait\<down>\<acute>,ref\<down>\<acute>} \<sharp> a" "NON_REL_VAR \<sharp> a"
  shows "`((a \<rightarrow> SKIP)\<box>SKIP) \<parallel>\<^bsub>A\<^esub> STOP` \<noteq> `(((a \<rightarrow> SKIP)\<box>SKIP) \<parallel>\<^bsub>A\<^esub> STOP) \<box> (a \<rightarrow> (SKIP \<parallel>\<^bsub>A\<^esub> STOP))`"
proof -
have 0: "{tr\<down>, tr\<down>\<acute>, ok\<down>\<acute>} \<sharp> a" sorry
have 1: "`($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, tr\<down>, tr\<down>\<acute>, ref\<down>, ref\<down>\<acute>} - {ok\<down>, ok\<down>\<acute>}\<^esub>` = 
`II\<^bsub>REL_VAR - {wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>,ok\<down>, ok\<down>\<acute>}\<^esub>`"sorry
have 2: "{tr\<down>} \<sharp> a" sorry
have 3: "{tr\<down>\<acute>} \<sharp> a" sorry
have 4: "`RHc (($tr \<le> $tr\<acute>) \<turnstile> ($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> \<not> $wait\<acute>)` = 
         `CSP($ok\<acute> \<and> ($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> \<not>$wait\<acute>)`"sorry
have 5: "D\<^sub>1 - out (REL_VAR - {wait\<down>, wait\<down>\<acute>, ref\<down>, ref\<down>\<acute>, ok\<down>, ok\<down>\<acute>}) = {wait\<down>\<acute>,ref\<down>\<acute>,ok\<down>\<acute>}" sorry
have 6: "{tr\<down>, tr\<down>\<acute>, ok\<down>, ok\<down>\<acute>, wait\<down>, wait\<down>\<acute>} \<sharp> a"sorry
have 7: "{wait\<down>\<acute>, ref\<down>\<acute>, ok\<down>\<acute>} \<sharp> a" sorry
have 8: "`a \<rightarrow> STOP` = `CSP2(a \<rightarrow> STOP)`" sorry
have 9: "`\<langle>a[true/ok\<acute>][\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>]\<rangle> = ($tr\<acute>-$tr)` = `\<langle>a\<rangle> = ($tr\<acute>-$tr)`"sorry
have 10: "{ok\<down>\<acute>} \<sharp> a" sorry
have 11: "`\<langle>a[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>]\<rangle> = ($tr\<acute>-$tr)` = `\<langle>a\<rangle> = ($tr\<acute>-$tr)`"sorry
have 12: "{ok\<down>,wait\<down>, ok\<down>\<acute>} \<sharp> a" sorry
have 13: "`($tr ^ \<langle>a[$wait\<acute>\<acute>/wait\<acute>][$ref\<acute>\<acute>/ref\<acute>]\<rangle> = $tr\<acute>)` = `($tr ^ \<langle>a\<rangle> = $tr\<acute>)`"sorry
have 14: " (\<exists>\<^sub>p {ref\<down>\<acute>\<acute>} . `($ref\<acute> \<subseteq> $ref\<acute>\<acute>)`) = `true`"sorry
have 15: "`(\<langle>a[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>][true/ok\<acute>][true/ok][false/wait]\<rangle> = $tr\<acute> - $tr)` = `(\<langle>a\<rangle> = $tr\<acute> - $tr)`"sorry
have 16: "`(a[\<langle>\<rangle>/tr][($tr\<acute> - $tr)/tr\<acute>] \<notin> $ref\<acute>)` = `(a \<notin> $ref\<acute>)`"sorry
have A: "`((a \<rightarrow> SKIP)\<box>SKIP) \<parallel>\<^bsub>A\<^esub> STOP` = 
      `STOP \<or> (CSP($ok\<acute> \<and> ($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> \<not> $wait\<acute>) \<parallel>\<^bsub>A\<^esub> STOP)`"
apply(simp add:Skip_choice_a_skip OrP_Parallel_distl Skip_par_stop)
apply(subst External_design) defer
apply(simp add:RHc_def)
apply(subst R1_rel_closure)
apply(subst R2_rel_closure)
apply(subst R3c_rel_closure)
apply(rule closure)
apply(simp_all add:typing defined closure)
apply(simp add:PrefixCSP_def)
apply(subst CSP_SemiR_closure)
apply(subst Prefix_CSP)
apply(simp_all add:assms Skip_CSP Skip_rel_closure Prefix_rel_closure assms DesignREA_CSP Miracle_pre Miracle_post 0)
apply(subst Prefixed_pre,simp_all add:typing defined closure unrest assms Skip_CSP Skip_pre CondR_def 6)
apply(subst Prefixed_post,simp_all add:typing defined closure unrest assms Skip_CSP Skip_pre Skip_post 6)
apply(subst AndP_comm) back back back back back
apply(simp add:AndP_assoc)
apply(subst SemiR_AndP_right_postcond)
apply(simp_all add:typing closure defined urename 1)
apply(subst SemiR_SkipRA_right,simp_all add:typing defined closure)defer
apply(simp add:AndP_OrP_distr AndP_OrP_distl demorgan1 demorgan2)
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym] AndP_contra)
apply(subst AndP_assoc,subst AndP_comm,simp add:AndP_contra)
apply(subst AndP_comm, simp add:AndP_assoc[THEN sym]) back
apply(subst OrP_comm) back
apply(subst AndP_comm) back
apply(subst OrP_AndP_absorb)
apply (metis (lifting, no_types) "4" PVAR_VAR_pvdash)
apply(simp add:PrefixCSP_def)
apply(rule closure)
apply(subst Prefix_rel_closure)
apply(simp_all add:assms Skip_rel_closure)
apply(subst 5)
apply(rule unrest)
apply(rule unrest)
apply(rule unrest) defer 
apply(rule unrest)
apply(simp_all add:typing closure defined unrest assms 7)
done
have "`(((a \<rightarrow> SKIP)\<box>SKIP) \<parallel>\<^bsub>A\<^esub> STOP) \<box> (a \<rightarrow> (SKIP \<parallel>\<^bsub>A\<^esub> STOP))` =
          `CSP2(a \<rightarrow> STOP) \<or> ((CSP ($ok\<acute> \<and> ($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> \<not>$wait\<acute>) \<parallel>\<^bsub>A\<^esub> STOP) \<box> a \<rightarrow> STOP)`"
apply(simp add:A Skip_par_stop OrP_external Stop_external_unit)
apply(subst 8,simp)
done
also have "... = `(a \<rightarrow> STOP) \<or> CSP2 (\<not> STOP \<and> (CSP ($ok\<acute> \<and> ($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> \<not> $wait\<acute>) \<parallel>\<^bsub>A\<^esub> STOP))`"
apply(simp add:ExternalChoiceCSP_def H2_OrP[THEN sym] CondR_def AndP_OrP_distl)
apply(subst AndP_comm) back back back
apply(subst AndP_assoc,subst AndP_comm,simp add:AndP_assoc[THEN sym])
apply(subst OrP_assoc,subst OrP_AndP_absorb,subst OrP_comm) back
apply(subst AndP_comm,subst OrP_assoc,subst OrP_AndP_absorb,simp add:H2_OrP)
apply(subst 8[THEN sym],simp)
done
finally have B: "`(((a \<rightarrow> SKIP)\<box>SKIP) \<parallel>\<^bsub>A\<^esub> STOP) \<box> (a \<rightarrow> (SKIP \<parallel>\<^bsub>A\<^esub> STOP))` =
    `(a \<rightarrow> STOP) \<or> CSP2 (\<not> STOP \<and> (CSP ($ok\<acute> \<and> ($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> \<not> $wait\<acute>) \<parallel>\<^bsub>A\<^esub> STOP))`" .
have C: "`(((a \<rightarrow> SKIP)\<box>SKIP) \<parallel>\<^bsub>A\<^esub> STOP)` = `STOP \<or> RHc(true \<turnstile> (($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> $wait\<acute> \<and> $ok\<acute>))`"
apply(subst A)
apply(subst 4[THEN sym])
apply(subst Stop_par)
apply (metis DesignREA_CSP)
apply(subst DesignREA_pre)
apply(simp add:R2_def R2s_def is_healthy_def R1_def usubst typing defined closure)
apply(simp add:typing defined closure unrest)
apply(subst DesignREA_post)
apply(simp add:is_healthy_def R2_def R2s_def R1_def usubst typing defined closure unrest 11 12 AndP_assoc[THEN sym])
apply(simp add:is_healthy_def R2_def R2s_def R1_def usubst typing defined closure unrest 11 12 AndP_assoc[THEN sym])
apply(subst AndP_comm) back
apply(subst AndP_assoc)
apply(simp add:tr_prefix_as_a)
apply(simp add:is_healthy_def R2_def R2s_def R1_def usubst typing defined closure unrest 11 12 AndP_assoc[THEN sym])
apply(simp add:is_healthy_def R2_def R2s_def R1_def usubst typing defined closure unrest 11 12 AndP_assoc[THEN sym])
apply(simp add: ImpliesP_def SubstP_OrP SubstP_AndP SubstP_NotP)
apply(subst SubstP_twice_2) back back
apply(simp add:typing defined closure unrest) (* 6,11 *)
apply(subst usubst(6),simp_all add:typing defined closure)
apply(subst usubst(8),simp_all add:typing defined closure)
apply(subst usubst(38),simp_all add:typing defined closure)
apply(simp add: usubst typing defined closure unrest 11 12 AndP_assoc[THEN sym])
apply(subst 13)
apply(simp add:DesignD_def ImpliesP_def AndP_OrP_distr AndP_OrP_distl ExistsP_OrP_dist demorgan1 demorgan2 OrP_assoc[THEN sym] AndP_assoc[THEN sym])
apply(subst AndP_comm[of "` ($tr ^ \<langle>a\<rangle> = $tr\<acute>)`"],simp add:AndP_assoc[THEN sym])
apply(subst AndP_comm[of _ "` ($tr ^ \<langle>a\<rangle> = $tr\<acute>)`"])
apply(simp add:ExistsP_AndP_expand1[THEN sym] ExistsP_AndP_expand2[THEN sym] typing closure defined unrest)
apply(subst ExistsP_ident,simp_all add:typing defined closure unrest 14)
apply(simp add:RHc_def R1_R2_commute R1_R3c_commute R1_OrP)
apply(simp add:R1_def AndP_assoc[THEN sym])
apply(subst AndP_comm,simp add:AndP_contra)
apply(subst AndP_assoc) back
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back
apply(subst AndP_comm,simp add:AndP_contra)
apply(subst OrP_comm,simp add:CSP1_def[THEN sym],simp add:R1_def[THEN sym])
apply(subst AndP_comm,simp add:R1_extend_AndP)
apply(subst AndP_assoc)
apply(subst ExistsP_AndP_expand1[THEN sym])
apply(simp add:typing defined closure unrest assms(2))
apply(subst ExistsP_AndP_expand1[THEN sym])
apply(simp add:typing defined closure unrest assms(2))
apply(subst ExistsP_AndP_expand1[THEN sym])
apply(simp add:typing defined closure unrest assms(2))
apply(simp add:R1_def)
apply(subst OrP_comm) back back
apply(simp add:CSP1_def[THEN sym])
apply(simp add:AndP_assoc)
apply(simp add:R1_def[THEN sym] AndP_assoc[THEN sym])
apply(subst AndP_comm) back back back back
apply(simp add:AndP_assoc[THEN sym] 14)
sorry
have D: "`(((a \<rightarrow> SKIP)\<box>SKIP) \<parallel>\<^bsub>A\<^esub> STOP) \<box> (a \<rightarrow> (SKIP \<parallel>\<^bsub>A\<^esub> STOP))` = 
    `(a \<rightarrow> STOP) \<or> ($ok \<and> \<not> $wait \<and> ($tr ^ \<langle>a\<rangle> = $tr\<acute>) \<and> $wait\<acute> \<and> $ok\<acute>)`"
apply(subst B)
apply(subst 4[THEN sym])
apply(subst Stop_par)
apply (metis DesignREA_CSP)
apply(subst DesignREA_pre)
apply(simp add:R2_def R2s_def is_healthy_def R1_def usubst typing defined closure)
apply(simp add:typing defined closure unrest)
apply(subst DesignREA_post)
apply(simp add:is_healthy_def R2_def R2s_def R1_def usubst typing defined closure unrest 11 12 AndP_assoc[THEN sym])
apply(simp add:is_healthy_def R2_def R2s_def R1_def usubst typing defined closure unrest 11 12 AndP_assoc[THEN sym])
apply(subst AndP_comm) back
apply(subst AndP_assoc)
apply(simp add:tr_prefix_as_a)
apply(simp add:is_healthy_def R2_def R2s_def R1_def usubst typing defined closure unrest 11 12 AndP_assoc[THEN sym])
apply(simp add:is_healthy_def R2_def R2s_def R1_def usubst typing defined closure unrest 11 12 AndP_assoc[THEN sym])
apply(simp add: ImpliesP_def SubstP_OrP SubstP_AndP SubstP_NotP)
apply(subst SubstP_twice_2) back back
apply(simp add:typing defined closure unrest) (* 6,11 *)
apply(subst usubst(6),simp_all add:typing defined closure)
apply(subst usubst(8),simp_all add:typing defined closure)
apply(subst usubst(38),simp_all add:typing defined closure)
apply(simp add: usubst typing defined closure unrest 11 12 AndP_assoc[THEN sym])
apply(subst 13)
apply(simp add:DesignD_def ImpliesP_def AndP_OrP_distr AndP_OrP_distl ExistsP_OrP_dist demorgan1 demorgan2 OrP_assoc[THEN sym] AndP_assoc[THEN sym])
apply(subst AndP_comm[of "` ($tr ^ \<langle>a\<rangle> = $tr\<acute>)`"],simp add:AndP_assoc[THEN sym])
apply(subst AndP_comm[of _ "` ($tr ^ \<langle>a\<rangle> = $tr\<acute>)`"])
apply(simp add:ExistsP_AndP_expand1[THEN sym] ExistsP_AndP_expand2[THEN sym] typing closure defined unrest)
apply(subst ExistsP_ident,simp_all add:typing defined closure unrest 14)
apply(simp add:RHc_def R1_R2_commute R1_R3c_commute R1_OrP)
apply(simp add:R1_def AndP_assoc[THEN sym])
apply(subst AndP_comm,simp add:AndP_contra)
apply(subst AndP_assoc) back
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back
apply(subst AndP_comm) back back back
apply(simp add:AndP_assoc[THEN sym])
apply(subst AndP_assoc)
apply(subst AndP_comm) back back
apply(simp add:AndP_contra)
apply(subst OrP_comm,simp add:CSP1_def[THEN sym],simp add:R1_def[THEN sym])
apply(subst AndP_comm,simp add:R1_extend_AndP)
apply(subst AndP_assoc)
apply(subst ExistsP_AndP_expand1[THEN sym])
apply(simp add:typing defined closure unrest assms(2))
apply(subst ExistsP_AndP_expand1[THEN sym])
apply(simp add:typing defined closure unrest assms(2))
apply(subst ExistsP_AndP_expand1[THEN sym])
apply(simp add:typing defined closure unrest assms(2))
apply(simp add: 14)
apply(subst CSP2_NotP_Stop_AndP) defer 
apply(simp add:CSP1_R1_commute R1_R3c_commute[THEN sym] R1_R2_commute[THEN sym])
apply(simp add:R2_def R1_idempotent R3c_def CSP1_def)
apply(simp add:CSP_Pre_def CSP_Post_def R1_def R2s_def usubst typing defined closure 15 AndP_assoc[THEN sym])
apply(subst AndP_assoc) back back back back
apply(subst AndP_comm,simp add:AndP_assoc[THEN sym]) back back back back
apply(subst AndP_assoc,simp add:tr_prefix_as_a)
apply(simp add:demorgan2 AndP_OrP_distl AndP_OrP_distr)
sorry
have E: "`(((a \<rightarrow> SKIP)\<box>SKIP) \<parallel>\<^bsub>A\<^esub> STOP) \<and> (($tr\<acute>=$tr) \<and> a \<in> $ref\<acute>)` =
      `(\<not> $ok \<and> ($tr = $tr\<acute>) \<and> a \<in>$ref\<acute>) \<or>
       ($ok \<and> $wait \<and> ($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - {tr\<down>, tr\<down>\<acute>}\<^esub> \<and> a \<in> $ref\<acute>) \<or>
       ($ok \<and> \<not> $wait \<and> ($tr\<acute> = $tr) \<and> $wait\<acute> \<and> $ok\<acute> \<and> a \<in> $ref\<acute>)`" 
apply(simp add:C)
apply(simp add:Stop_design DesignREA_form SkipR_as_SkipRA R2_def R2s_def R1_def 11 usubst typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing defined closure)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing defined closure)back
sorry
have F: "`((((a \<rightarrow> SKIP)\<box>SKIP) \<parallel>\<^bsub>A\<^esub> STOP) \<box> (a \<rightarrow> (SKIP \<parallel>\<^bsub>A\<^esub> STOP))) \<and> (($tr\<acute>=$tr) \<and> a \<in> $ref\<acute>)` =
      `(\<not> $ok \<and> ($tr = $tr\<acute>) \<and> a \<in>$ref\<acute>) \<or>
       ($ok \<and> $wait \<and> ($tr\<acute> = $tr) \<and> II\<^bsub>REL_VAR - {tr\<down>, tr\<down>\<acute>}\<^esub> \<and> a \<in> $ref\<acute>)`"
apply(simp add:D)
apply(subst Prefixed_design,simp_all add:typing closure defined assms Stop_CSP) defer 
apply(simp add:Stop_pre Stop_post DesignREA_form SkipR_as_SkipRA R2_def R2s_def R1_def usubst typing defined closure 11 16)
apply(subst SkipRA_unfold_aux_ty[of "tr"],simp_all add:typing defined closure)
apply(subst SemiR_AndP_right_postcond,simp add:typing closure defined)
sorry
show ?thesis
sorry
qed

lemma External_Internal:
  assumes "`A` is CSP" 
  shows "`(A \<box> B) \<or> A` = `A \<or> CSP2(\<not>STOP \<and> B)`"
proof -
have "`(A \<box> B) \<or> A` = `(A \<box> B) \<or> CSP2(A)`"
by(metis assms is_healthy_def CSP_is_CSP2)
hence "`(A \<box> B) \<or> A` = `CSP2(A \<or> (\<not>STOP \<and> B))`"
apply(simp add:ExternalChoiceCSP_def CondR_def H2_OrP[THEN sym])
apply(simp add:OrP_assoc[THEN sym] AndP_OrP_distl)
apply(subst OrP_comm) back back
apply(subst OrP_assoc) back
apply(subst OrP_comm) back
apply(subst AndP_comm) back back
apply(subst OrP_AndP_absorb)
apply(subst AndP_comm)
apply(subst OrP_assoc)
apply(subst OrP_comm,simp add:AndP_assoc[THEN sym])
apply(subst OrP_AndP_absorb,simp)
done
also have "... = `A \<or> CSP2(\<not>STOP \<and> B)`"
apply(simp add:H2_OrP)
apply(metis is_healthy_def assms CSP_is_CSP2)
done
finally show ?thesis .
qed

lemma 
assumes "`P` \<sqsubseteq> `A`" "`P` \<sqsubseteq> `B`"
shows "`P` \<sqsubseteq> `A \<or> B`"
by (metis OrP_refine assms(1) assms(2))

lemma Choice_ref_1: 
  assumes "A \<in> REL" "B \<in> REL" "A is CSP" "B is CSP"
  "`A` \<sqsubseteq> `($ok \<and> \<not> $wait \<and> \<not> ($tr\<acute> = $tr) \<and> CSP_Post(B) \<and> $ok\<acute>)`"
  "`A` \<sqsubseteq> `($ok \<and> \<not> $wait \<and> \<not> $wait\<acute> \<and> CSP_Post(B) \<and> $ok\<acute>)`"
  "`A` \<sqsubseteq> `($ok \<and> \<not> $wait \<and> \<not> CSP_Pre(B))`"
  shows "`A` \<sqsubseteq> `A \<box> B`"
proof -
have "`A \<or> (A \<box> B)` = `(A \<or> CSP2 (
                 $ok \<and> \<not>$wait \<and> \<not>(($tr\<acute> = $tr) \<and> $wait\<acute> \<and> $ok\<acute>) \<and>
                (\<not> CSP_Pre (R2 (B)) \<or> ($ok\<acute> \<and> CSP_Post (R2 (B))))))`"
apply(subst OrP_comm)
apply(subst External_Internal,simp add: assms(3))
apply(subst CSP_form[of "B"],simp add:assms(4))
apply(simp add:NotP_Stop CSP_Pre_R2_commute[THEN sym] CSP_Post_R2_commute[THEN sym])
apply(utp_poly_auto_tac)
done
also have "... = `(A \<or> CSP2 (
                 $ok \<and> \<not>$wait \<and> \<not>(($tr\<acute> = $tr) \<and> $wait\<acute> \<and> $ok\<acute>) \<and>
                (\<not> CSP_Pre (B) \<or> ($ok\<acute> \<and> CSP_Post (B)))))`"
by(metis assms is_healthy_def CSP_is_RHc RHc_is_R2)
also have "... = `A \<or> ($ok \<and> \<not> $wait \<and> \<not>CSP_Pre(B)) \<or>
          ($ok \<and> \<not> $wait \<and> \<not> (($tr\<acute> = $tr) \<and> $wait\<acute>) \<and> \<not>CSP_Pre(B) \<and> $ok\<acute>) \<or> 
          ($ok \<and> \<not> $wait \<and> \<not> (($tr\<acute> = $tr) \<and> $wait\<acute>) \<and> CSP_Post(B) \<and> $ok\<acute>)`"
apply(simp add:H2_split usubst typing defined closure CSP_Pre_def CSP_Post_def)
apply(subst SubstP_twice_3,simp_all add:typing defined closure unrest) back back
apply(subst SubstP_twice_3,simp_all add:typing defined closure unrest) back
apply(subst SubstP_twice_1,simp add:usubst typing defined closure)
apply(subst SubstP_twice_3,simp_all add:typing defined closure unrest) back back back back
apply(subst SubstP_twice_3,simp_all add:typing defined closure unrest) back back back
apply(subst SubstP_twice_1,simp add:usubst typing defined closure)
apply(subst SubstP_twice_3,simp_all add:typing defined closure unrest) back back back back back back
apply(subst SubstP_twice_3,simp_all add:typing defined closure unrest) back back back back back
apply(subst SubstP_twice_1,simp add:usubst typing defined closure)
apply(simp add:AndP_OrP_distl AndP_OrP_distr AndP_assoc[THEN sym])
done
also have "... = `A \<or> (($ok \<and> \<not> $wait \<and> \<not>CSP_Pre(B)) \<or>
          (($ok \<and> \<not> $wait \<and> \<not>CSP_Pre(B)) \<and> \<not> (($tr\<acute> = $tr) \<and> $wait\<acute>) \<and> $ok\<acute>)) \<or> 
          ($ok \<and> \<not> $wait \<and> \<not> (($tr\<acute> = $tr) \<and> $wait\<acute>) \<and> CSP_Post(B) \<and> $ok\<acute>)`"
apply(simp add:AndP_assoc[THEN sym] OrP_assoc[THEN sym])
apply(subst AndP_assoc)back back back
apply(subst AndP_comm,simp add: AndP_assoc[THEN sym]) back back back back back
done
also have "... = `A \<or> ($ok \<and> \<not> $wait \<and> (CSP_Pre(B) \<Rightarrow> \<not> (($tr\<acute> = $tr) \<and> $wait\<acute>) \<and> CSP_Post(B) \<and> $ok\<acute>))`"
by(subst OrP_AndP_absorb, simp add: AndP_OrP_distl[THEN sym] ImpliesP_def[THEN sym])
finally have P: "`A \<or> (A \<box> B)` = `A \<or> ($ok \<and> \<not> $wait \<and> (CSP_Pre(B) \<Rightarrow> \<not> (($tr\<acute> = $tr) \<and> $wait\<acute>) \<and> CSP_Post(B) \<and> $ok\<acute>))`" .
show ?thesis
apply(subst RefP_OrP)
apply(subst P)
apply(subst RefP_OrP[THEN sym],simp add:ImpliesP_def AndP_OrP_distl demorgan2 AndP_OrP_distr OrP_assoc[THEN sym])
apply(subst OrP_refine) defer
apply(subst OrP_refine,simp_all add:assms)
apply(metis assms PVAR_VAR_pvdash)
apply(metis assms PVAR_VAR_pvdash)
done
qed

lemma Choice_ref_2: 
  assumes "A \<in> REL" "B \<in> REL" "A is CSP" "B is CSP" "`A` \<sqsubseteq> `A \<box> B`"
  shows 
  "`A` \<sqsubseteq> `($ok \<and> \<not> $wait \<and> \<not> ($tr\<acute> = $tr) \<and> CSP_Post(B) \<and> $ok\<acute>)`"
  "`A` \<sqsubseteq> `($ok \<and> \<not> $wait \<and> \<not> $wait\<acute> \<and> CSP_Post(B) \<and> $ok\<acute>)`"
  "`A` \<sqsubseteq> `($ok \<and> \<not> $wait \<and> \<not> CSP_Pre(B))`"
 proof-
have 0:"`(A \<box> B) \<and> ($ok \<and> \<not>$wait \<and> \<not>($tr\<acute> = $tr) \<and> $ok\<acute>)` =
                `(\<not> CSP_Pre(A) \<and> ($ok \<and> \<not>$wait \<and> \<not>($tr\<acute>=$tr) \<and> $ok\<acute>)) \<or>
                 (\<not>CSP_Pre(B) \<and> ($ok \<and> \<not>$wait \<and> \<not>($tr\<acute>=$tr) \<and> $ok\<acute>)) \<or> 
                 (CSP_Post(A) \<and> ($ok \<and> \<not>$wait \<and> \<not>($tr\<acute>=$tr) \<and> $ok\<acute>)) \<or> 
                 (CSP_Post(B) \<and> ($ok \<and> \<not>$wait \<and> \<not>($tr\<acute>=$tr) \<and> $ok\<acute>))`"
sorry
have 1: "`A` \<sqsubseteq>  `(\<not> CSP_Pre(A) \<and> ($ok \<and> \<not>$wait \<and> \<not>($tr\<acute>=$tr) \<and> $ok\<acute>)) \<or>
                 (\<not>CSP_Pre(B) \<and> ($ok \<and> \<not>$wait \<and> \<not>($tr\<acute>=$tr) \<and> $ok\<acute>)) \<or> 
                 (CSP_Post(A) \<and> ($ok \<and> \<not>$wait \<and> \<not>($tr\<acute>=$tr) \<and> $ok\<acute>)) \<or> 
                 (CSP_Post(B) \<and> ($ok \<and> \<not>$wait \<and> \<not>($tr\<acute>=$tr) \<and> $ok\<acute>))`"
by (metis "0" AndP_refines_1 assms(5))
show "`A` \<sqsubseteq> `($ok \<and> \<not> $wait \<and> \<not> ($tr\<acute> = $tr) \<and>  CSP_Post(B) \<and> $ok\<acute>)`"
sorry
have 2:"`(A \<box> B) \<and> ($ok \<and> \<not>$wait \<and> \<not>$wait\<acute> \<and> $ok\<acute>)` =
                `(\<not> CSP_Pre(A) \<and> ($ok \<and> \<not>$wait \<and> \<not>$wait\<acute>  \<and> $ok\<acute>)) \<or>
                 (\<not>CSP_Pre(B) \<and> ($ok \<and> \<not>$wait \<and> \<not>$wait\<acute> \<and> $ok\<acute>)) \<or> 
                 (CSP_Post(A) \<and> ($ok \<and> \<not>$wait \<and> \<not>$wait\<acute> \<and> $ok\<acute>)) \<or> 
                 (CSP_Post(B) \<and> ($ok \<and> \<not>$wait \<and> \<not>$wait\<acute> \<and> $ok\<acute>))`"
sorry
have 3: "`A` \<sqsubseteq>  `(\<not> CSP_Pre(A) \<and> ($ok \<and> \<not>$wait \<and> \<not>$wait\<acute> \<and> $ok\<acute>)) \<or>
                 (\<not>CSP_Pre(B) \<and> ($ok \<and> \<not>$wait \<and> \<not>$wait\<acute> \<and> $ok\<acute>)) \<or> 
                 (CSP_Post(A) \<and> ($ok \<and> \<not>$wait \<and> \<not>$wait\<acute> \<and> $ok\<acute>)) \<or> 
                 (CSP_Post(B) \<and> ($ok \<and> \<not>$wait \<and> \<not>$wait\<acute> \<and> $ok\<acute>))`"
by (metis "2" AndP_refines_1 assms(5))
show "`A` \<sqsubseteq> `($ok \<and> \<not> $wait \<and> \<not>$wait\<acute> \<and> CSP_Post(B) \<and> $ok\<acute>)`"
sorry
have 4:"`(A \<box> B) \<and> ($ok \<and> \<not>$wait)` =
    `(\<not> CSP_Pre (A) \<and> ($ok \<and> \<not> $wait)) \<or>
     (\<not> CSP_Pre (B) \<and> ($ok \<and> \<not> $wait)) \<or>
     ( (R2 ((CSP_Post(A) \<and> CSP_Post (B)) \<lhd> ($tr\<acute> = $tr) \<and> $wait\<acute> \<rhd> (CSP_Post(A) \<or> CSP_Post(B))) \<and> $ok\<acute>)
                        \<and> ($ok \<and> \<not> $wait))`"
apply(subst AndP_comm)
apply(simp add:assms External_design DesignREA_form AndP_OrP_distl)
apply(subst AndP_comm,subst AndP_assoc[THEN sym])
apply(subst AndP_assoc,simp add:AndP_contra)
apply(subst AndP_assoc[THEN sym])
apply(subst AndP_assoc) back
apply(subst AndP_assoc) back
apply(subst AndP_comm) back back
apply(subst AndP_assoc,simp add:AndP_contra)
apply(subst AndP_assoc) back
apply(subst AndP_assoc,simp)
apply(subst AndP_assoc) back
apply(subst AndP_assoc,simp)
apply(simp add:AndP_OrP_distl demorgan2 R2_OrP CSP_Pre_R2_commute[THEN sym] OrP_assoc[THEN sym])
apply(simp add:AndP_OrP_distl[THEN sym],subst AndP_comm,simp add:AndP_OrP_distr)
apply(metis assms is_healthy_def CSP_is_RHc RHc_is_R2)
done
have 5: "`A` \<sqsubseteq>  
    `(\<not> CSP_Pre (A) \<and> ($ok \<and> \<not> $wait)) \<or>
     ((\<not> CSP_Pre (B)) \<and> ($ok \<and> \<not> $wait)) \<or>
     ( (R2 ((CSP_Post(A) \<and> CSP_Post (B)) \<lhd> ($tr\<acute> = $tr) \<and> $wait\<acute> \<rhd> (CSP_Post(A) \<or> CSP_Post(B))) \<and> $ok\<acute>)
                        \<and> ($ok \<and> \<not> $wait))`"
by (metis "4" AndP_refines_1 assms(5))
show "`A` \<sqsubseteq>   `($ok \<and> \<not>$wait \<and> \<not>CSP_Pre(B))`"
sorry
qed

lemma Choice_ref: 
  assumes "A \<in> REL" "B \<in> REL" "A is CSP" "B is CSP" 
  shows "(`A` \<sqsubseteq> `A \<box> B`) \<longleftrightarrow>
  (`A` \<sqsubseteq> `($ok \<and> \<not> $wait \<and> \<not> ($tr\<acute> = $tr) \<and> CSP_Post(B) \<and> $ok\<acute>)`)
  (`A` \<sqsubseteq> `($ok \<and> \<not> $wait \<and> \<not> $wait\<acute> \<and> CSP_Post(B) \<and> $ok\<acute>)`)
  (`A` \<sqsubseteq> `($ok \<and> \<not> $wait \<and> \<not> CSP_Pre(B))`)
end
