(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_prescr.thy                                                       *)
(* Authors: Simon Foster, University of York                                  *)
(******************************************************************************)

header {* UTP Prescriptions *}

theory utp_prescr
imports utp_designs
begin

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
  apply (metis (full_types) TypeUSound_bool binding_upd_drop_ty pvaux_MkPVAR)+
done
  
theorem HP_form_equiv:
  "`P[false/okay]` = `\<not> ok'` \<longleftrightarrow> P is HP"
  by (metis HP_form_equiv1 HP_form_equiv2)

definition PrescrP :: 
  "'a WF_PREDICATE \<Rightarrow> 
   'a WF_PREDICATE \<Rightarrow> 
   'a WF_PREDICATE" (infixr "\<parallel>-" 60) where
"P \<parallel>- Q = `(ok \<and> P \<Rightarrow> ok') \<and> (ok' \<Rightarrow> Q \<and> ok)`"

syntax
  "_upred_prescr" :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<parallel>-" 30)

translations
  "_upred_prescr p q" == "CONST PrescrP p q"

declare PrescrP_def [eval, evalp]

theorem PrescrP_HP:
  "P \<parallel>- Q is HP"
  apply (unfold HP_form_equiv[THEN sym])
  apply (simp add:PrescrP_def usubst typing defined)
done

lemma binding_value_ccontr:
  fixes x :: "('a :: DEFINED, 'm ::VALUE) PVAR"
  assumes "\<lbrakk>P\<rbrakk>b" "TYPEUSOUND('a, 'm)" "pvaux x"
           "\<not> \<lbrakk>P\<rbrakk>(b(x :=\<^sub>* v))"
  shows "\<langle>b\<rangle>\<^sub>* x \<noteq> v"
  using assms by (auto)

lemma binding_ty_true:
  fixes x :: "(bool, 'm :: BOOL_SORT) PVAR"
  assumes "\<lbrakk>P\<rbrakk>b" "\<not> \<lbrakk>P\<rbrakk>(b(x :=\<^sub>* True))" "pvaux x"
  shows "\<not> \<langle>b\<rangle>\<^sub>* x"
  using assms 
  apply (auto)
  apply (metis (full_types) TypeUSound_bool binding_upd_drop_ty)
done

lemma binding_ty_false:
  fixes x :: "(bool, 'm :: BOOL_SORT) PVAR"
  assumes "\<lbrakk>P\<rbrakk>b" "\<not> \<lbrakk>P\<rbrakk>(b(x :=\<^sub>* False))" "pvaux x"
  shows "\<langle>b\<rangle>\<^sub>* x"
  using assms
  apply (drule_tac binding_value_ccontr[of _ _ "x" "False"])
  apply (simp_all add:typing)
done

theorem HP_as_PrescrP:
  assumes "P is HP"
  shows "P = `\<not> P\<^bsup>tf\<^esup> \<parallel>- P\<^bsup>tt\<^esup>`"
proof -
  have "`(\<not> P\<^bsup>tf\<^esup> \<parallel>- P\<^bsup>tt\<^esup>)[true/okay]` = `P[true/okay]`"
    apply (simp add:PrescrP_def usubst typing defined)
    apply (utp_poly_auto_tac)
    apply (drule binding_ty_false)
    apply (auto simp add:typing defined closure)
  done

  moreover from assms have "`(\<not> P\<^bsup>tf\<^esup> \<parallel>- P\<^bsup>tt\<^esup>)[false/okay]` = `P[false/okay]`"
    by (simp add:PrescrP_def usubst typing defined HP_form_equiv[THEN sym])

  ultimately show ?thesis
    apply (subst BoolType_pvaux_cases[of okay])
    apply (simp_all add:closure typing)
  done
qed

theorem HP_iff_PrescrP:
  "P is HP \<longleftrightarrow> P = `\<not> P\<^bsup>tf\<^esup> \<parallel>- P\<^bsup>tt\<^esup>`"
  by (metis HP_as_PrescrP PrescrP_HP)

end
