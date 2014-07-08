(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_designs_hoare.thy                                                *)
(* Authors: Simon Foster, University of York                                  *)
(******************************************************************************)

header {* Total Correctness Hoare Logic *}

theory utp_designs_hoare
imports utp_designs_healths
begin

definition HoareD :: 
  "'a upred \<Rightarrow> 'a upred \<Rightarrow> 'a upred \<Rightarrow> 'a upred" ("{_}_{_}\<^sub>D" [200,0,201] 200) where
"{p}Q{r}\<^sub>D = `((p \<turnstile> r\<acute>) \<sqsubseteq> Q)`"

declare HoareD_def [eval,evalr,evalrx,evalpp,evalpr]

syntax
  "_n_upred_hoared" :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" ("{_}_{_}\<^sub>D" [0,20,0] 100)

translations
  "_n_upred_hoared p Q r"  == "CONST HoareD p Q r"


lemma HoareD_as_HoareP: "`{p}Q{r}\<^sub>D` = `{$ok \<and> p}Q{$ok \<and> r}`"
  by (simp add:HoareP_def HoareD_def DesignD_def urename typing defined closure)

theorem HoareD_SkipD [hoare]:
  assumes "p \<in> COND"
  shows "`{p}II\<^sub>D{p}\<^sub>D`"
  using assms
  apply (simp add: HoareD_def SkipD_def)
  apply (rule DesignD_refine)
  apply (metis RefineP_TrueP_refine)
  apply (metis SemiR_TrueP_precond SkipR_transport_refine TrueP_right_UNREST_DASHED dual_order.refl)
done

theorem HoareD_CondR [hoare]:
  assumes "`{b \<and> p}S{q}\<^sub>D`" "`{\<not>b \<and> p}T{q}\<^sub>D`"
  shows "`{p}S \<lhd> b \<rhd> T{q}\<^sub>D`"
  using assms by (utp_pred_auto_tac)

lemma RefImp: "`q \<Rightarrow> p` \<sqsubseteq> r \<Longrightarrow> p \<sqsubseteq> `q \<and> r`"
  by (utp_pred_tac)

theorem HoareD_AssignD [hoare]:
  fixes x :: "('a :: DEFINED, 'm) pvar"
  assumes "TYPEUSOUND('a, 'm)" 
          "x \<in> PUNDASHED" "x\<down> \<noteq> ok\<down>" "{ok\<down>} \<sharp> v"
          "D\<^sub>1 \<sharp> v" "NON_REL_VAR \<sharp> v" "q \<in> COND"
          "`p \<Rightarrow> q[v/x]`"
  shows "`{p}x :=\<^sub>D v{q}\<^sub>D`"
  using assms
  apply (simp add: HoareD_def AssignD_alt_def)
  apply (rule DesignD_refine)
  apply (metis RefineP_TrueP_refine)
  apply (rule RefImp)
  apply (simp add:PAssignF_upd_def)
  apply (rule AssignR_refinement_alt)
  apply (simp_all add:closure)
done

theorem HoareD_SemiR [hoare]:
  assumes 
    "`{p}Q1{s}\<^sub>D`" "`{s}Q2{r}\<^sub>D`" 
    "p \<in> COND" "r \<in> COND" "s \<in> COND"
    "Q1 \<in> REL" "Q2 \<in> REL"
  shows "`{p}Q1 ; Q2{r}\<^sub>D`"
  using assms
  apply (simp add:HoareD_as_HoareP)
  apply (rule HoareP_SemiR)
  apply (simp)
  apply (simp)
  apply (simp_all add:closure)
done

end


