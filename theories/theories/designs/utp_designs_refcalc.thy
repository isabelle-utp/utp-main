(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_designs_laws.thy                                                 *)
(* Authors: Simon Foster, University of York                                  *)
(******************************************************************************)

header {* Designs Refinement Calculus *}

theory utp_designs_refcalc
imports utp_designs_healths
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
  "`w:[true,false]` = `\<not> $ok`"
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
done

theorem SpecD_weaken_pre:
  assumes frees: "OKAY \<sharp> pre" "OKAY \<sharp> pre'" "OKAY \<sharp> post"
      and pre_pre': "`pre \<Rightarrow> pre'`"
  shows "`w:[pre, post]` \<sqsubseteq> `w:[pre', post]`"
  apply (rule SpecD_refine)
  apply (simp_all add:assms)
done

theorem SpecD_left_unit:
  "`II\<^sub>D ; w:[pre, post]` = `w:[pre, post]`"
  apply (subst H1_left_unit)
  apply (simp add:SpecD_def)
  apply (rule closure)
  apply (simp)
done

theorem SkipR_pred_prime:
  "`p \<and> II` = `p \<and> p\<acute> \<and> II`"
  by (utp_rel_auto_tac)

lemma ExistsP_refine:
  "vs2 \<subseteq> vs1 \<Longrightarrow> (\<exists>\<^sub>p vs1. p) \<sqsubseteq> (\<exists>\<^sub>p vs2. p)" 
  apply (utp_pred_auto_tac)
  apply (metis binding_override_simps(6) inf_absorb1)
done

lemma SkipRA_closure' [closure]: "II\<^bsub>vs\<^esub> \<in> WF_RELATION"
  by (simp add:SkipRA_def WF_RELATION_def unrest)

lemma SkipRA_refine:
  "vs1 \<subseteq> vs2 \<Longrightarrow> II\<^bsub>vs1\<^esub> \<sqsubseteq> II\<^bsub>vs2\<^esub>"
  apply (simp add:SkipRA_def)
  apply (rule ExistsP_refine)
  apply (auto)
done

lemma SkipRA_SkipR_refine: "II\<^bsub>vs\<^esub> \<sqsubseteq> II"
  apply (simp add: SkipR_as_SkipRA)
  apply (simp add:SkipRA_def)
  apply (rule ExistsP_refine)
  apply (simp)
done

theorem SpecD_skip:
  assumes "`pre \<Rightarrow> post`"
  shows "`w:[pre, post]` \<sqsubseteq> `II\<^sub>D`"
proof -
  have "`pre \<and> II` = `pre \<and> post\<acute> \<and> II`"
    by (metis (hide_lams, no_types) AndP_assoc AndP_comm AndP_idem ConvR_invol IffP_eq_intro ImpliesP_eq_intro ImpliesP_export SkipR_pred_prime assms utp_pred_simps(16) utp_pred_simps(18))

  moreover hence "`post\<acute> \<and> II\<^bsub>REL_VAR - OKAY - w\<^esub>` \<sqsubseteq> `pre \<and> post\<acute> \<and> II`"
    by (smt AndP_assoc AndP_comm AndP_refines_1 RefP_AndP_intro RefineP_seperation SkipRA_SkipR_refine)

  ultimately show ?thesis
    apply (simp add: SpecD_def SkipD_def)
    apply (rule DesignD_refine)
    apply (rule RefineP_TrueP_refine)
    apply (simp)
  done
qed

theorem SpecD_sequential:
  assumes "pre \<in> WF_CONDITION" "post \<in> WF_CONDITION" "mid \<in> WF_CONDITION"
    "{ok\<down>} \<sharp> pre" "{ok\<down>} \<sharp> mid" "{ok\<down>} \<sharp> post"
    "ok\<down> \<notin> w" "ok\<down>\<acute> \<notin> w"
  shows "`w:[pre, post]` \<sqsubseteq> `w:[pre, mid] ; w:[mid, post]`"
  apply (simp add:SpecD_def)
  apply (subst DesignD_composition_cond)
  apply (simp_all add:assms closure unrest)
  defer defer defer
  apply (rule DesignD_refine)
  apply (smt AndP_comm AndP_contra SemiR_AndP_right_DASHED SemiR_FalseP_right SemiR_TrueP_precond TrueP_right_UNREST_DASHED assms(3) order_refl utp_pred_simps(15) utp_pred_simps(16) utp_pred_simps(6))
oops

end
