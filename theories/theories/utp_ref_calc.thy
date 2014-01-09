(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_ref_calc.thy                                                     *)
(* Authors: Simon Foster, University of York                                  *)
(******************************************************************************)

header {* UTP Designs-based Refinement Calculus *}

theory utp_ref_calc
imports utp_designs
begin

definition SpecD :: 
  "'a VAR set \<Rightarrow>
   'a WF_PREDICATE \<Rightarrow>
   'a WF_PREDICATE \<Rightarrow>
   'a WF_PREDICATE" ("_:[_, _]" [999,999,999] 1000) where
"w:[P, Q] = `P \<turnstile> (Q\<acute> \<and> II\<^bsub>REL_VAR - OKAY - w\<^esub>)`"

declare SpecD_def [eval, evalp, evalr]

syntax
  "_upred_spec" :: "'a VAR set \<Rightarrow> upred \<Rightarrow> upred \<Rightarrow> upred" ("_:[_, _]" [999] 1000)

translations
  "_upred_spec w p q" == "CONST SpecD w p q"

theorem SpecD_abort:
  "`w:[false,true]` = `true`"
  by (utp_pred_tac)

theorem SpecD_miracle:
  "`w:[true,false]` = `\<not> ok`"
  by (utp_pred_tac)

theorem SpecD_refine:
  assumes frees: "OKAY \<sharp> pre" "OKAY \<sharp> pre'" "OKAY \<sharp> post" "OKAY \<sharp> post'"
      and pre_pre': "`pre \<Rightarrow> pre'`" and post'_post: "`post' \<Rightarrow> post`"
  shows "`w:[pre, post]` \<sqsubseteq> `w:[pre', post']`"
proof -
  from frees have "OKAY \<sharp> `post\<acute> \<and> II\<^bsub>REL_VAR - OKAY - w\<^esub>`"
    apply (rule_tac UNREST_AndP)
    apply (force intro:UNREST_RenameP UNREST_AndP UNREST_subset UNREST_SkipRA UNREST_ConvR simp add:urename closure)+
  done

  moreover from frees have "OKAY \<sharp> `post'\<acute> \<and> II\<^bsub>REL_VAR - OKAY - w\<^esub>`"
    apply (rule_tac UNREST_AndP)
    apply (force intro:UNREST_RenameP UNREST_AndP UNREST_subset UNREST_SkipRA UNREST_ConvR simp add:urename closure)+
  done

  moreover from pre_pre'
  have "pre' \<sqsubseteq> pre"
    by (utp_pred_tac)

  moreover from post'_post
  have "`post\<acute> \<and> II\<^bsub>REL_VAR - OKAY - w\<^esub>` \<sqsubseteq> `pre \<and> post'\<acute> \<and> II\<^bsub>REL_VAR - OKAY - w\<^esub>`"
    by (utp_pred_tac)

  ultimately show ?thesis
    by (auto intro:DesignD_refine simp add:SpecD_def frees)
qed

theorem SpecD_strengthen_post:
  assumes frees: "OKAY \<sharp> pre" "OKAY \<sharp> post" "OKAY \<sharp> post'"
      and post'_post: "`post' \<Rightarrow> post`"
  shows "`w:[pre, post]` \<sqsubseteq> `w:[pre, post']`"
  apply (rule SpecD_refine)
  apply (simp_all add:assms)
  apply (utp_pred_tac)
done

theorem SpecD_weaken_pre:
  assumes frees: "OKAY \<sharp> pre" "OKAY \<sharp> pre'" "OKAY \<sharp> post"
      and pre_pre': "`pre \<Rightarrow> pre'`"
  shows "`w:[pre, post]` \<sqsubseteq> `w:[pre', post]`"
  apply (rule SpecD_refine)
  apply (simp_all add:assms)
  apply (utp_pred_tac)
done


lemma 
  fixes x :: "(int, 'm :: {BOOL_SORT, INT_SORT}) PVAR"
  assumes "x \<in> PUNDASHED" "x\<down> \<noteq> okay\<down>"
  shows "`{x\<down>}:[true, $x \<ge> \<guillemotleft>0\<guillemotright>]` \<sqsubseteq> `{x\<down>}:[true, $x = \<guillemotleft>0\<guillemotright>]`"
  using assms
  apply (rule_tac SpecD_refine)
  apply (force intro:unrest typing closure)
  apply (force intro:unrest typing closure)
  apply (force intro:unrest typing closure)
  apply (force intro:unrest typing closure)
  apply (utp_poly_tac)
  apply (utp_poly_tac)
done

done
(*
theorem SpecD_AssignD:
  fixes x :: "('a :: DEFINED, 'm) PVAR"
  assumes typesound: "TYPEUSOUND('a, 'm)"
      and frees: "OKAY \<sharp> pre" "OKAY \<sharp> post" "OKAY \<sharp> e" 
                 "NON_REL_VAR \<sharp> e" "DASHED \<sharp> e" "x \<in> PUNDASHED"
      and pre_post: "`pre \<Rightarrow> post[e/x]`"
  shows "`({x\<down>} \<union> w):[pre, post]` \<sqsubseteq> `x :=\<^sub>D e`"
  apply (unfold AssignD_def SpecD_def)
  apply (rule DesignD_refine)
  apply (simp_all add:unrest frees)
  apply (force intro:frees UNREST_AndP UNREST_subset UNREST_SkipRA frees)
  apply (rule unrest)
  apply (metis PVAR_VAR_PUNDASHED_UNDASHED frees)
  apply (simp)
  apply (rule UNREST_EXPR_subset[of "OKAY \<union> NON_REL_VAR"])
  apply (rule UNREST_EXPR_union)
  apply (metis UNREST_PExprE frees(3) typesound)
  apply (rule UNREST_PExprE)
  apply (simp_all add:assms)
  apply (utp_pred_tac)
  apply (utp_prel_tac)
apply (metis (hide_lams, no_types) UNREST_PExprE frees(3) typesound)
  apply (rule unrest)
  apply (simp add:unrest frees)
  apply (rule frees)
  apply (auto)[1]
  apply (force simp add:frees)
  apply (simp add:frees)
*)

end
