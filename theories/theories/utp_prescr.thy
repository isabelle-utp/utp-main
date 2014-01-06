(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_prescr.thy                                                       *)
(* Authors: Simon Foster, University of York                                  *)
(******************************************************************************)

header {* UTP Prescriptions *}

theory utp_prescr
imports utp_designs

definition "HP(P) = `P \<lhd> ok \<rhd> \<not> ok'`"

declare HP_def [eval, evalp]

lemma HP_form_equiv1:
  assumes "p is HP"
  shows "`p[false/okay]` = `\<not> ok'`"
proof -
  have "`p[false/okay]` = `(p \<lhd> ok \<rhd> \<not> ok')[false/okay]`"
    by (metis HP_def Healthy_simp assms)

  also have "... = `\<not> ok'`"
    by (utp_poly_tac)

  finally show ?thesis .
qed

lemma HP_form_equiv2:
  assumes "`p[false/okay]` = `\<not> ok'`"
  shows "p is HP"
using assms
apply (utp_poly_tac)
apply (safe, simp_all)
apply (drule_tac x="b" in spec)
apply (simp)
apply (subgoal_tac "b(okay :=\<^sub>* False) = b")
apply (simp)
defer
apply (drule_tac x="b" in spec, simp)
apply (rule ccontr)
apply (subgoal_tac "b = b(okay :=\<^sub>* False)")
apply (simp)
apply (metis (full_types) TypeUSound_bool binding_upd_drop_ty pvaux_MkPVAR)
by (metis (full_types) TypeUSound_bool binding_upd_drop_ty pvaux_MkPVAR)
  
theorem HP_form_equiv:
  "`P[false/okay]` = `\<not> ok'` \<longleftrightarrow> P is HP"
  by (metis HP_form_equiv1 HP_form_equiv2)

end
