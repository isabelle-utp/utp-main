section \<open> Reactive Specifications \<close>

theory ReactiveSpec
  imports "UTP-Circus.utp_circus"
begin

consts
  seq_comp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr ";" 71)

typedef ('s, 'e) rrel = "{P :: ('s, 'e) action. P is CRR}"
  by (rule_tac x="false" in exI, simp add: closure)

setup_lifting type_definition_rrel

notation Rep_rrel ("\<lbrakk>_\<rbrakk>\<^sub>R")

instantiation rrel :: (type, type) refine
begin
  lift_definition less_eq_rrel :: "('a, 'b) rrel \<Rightarrow> ('a, 'b) rrel \<Rightarrow> bool" is "less_eq" .
  lift_definition less_rrel :: "('a, 'b) rrel \<Rightarrow> ('a, 'b) rrel \<Rightarrow> bool" is "less" .
instance by (intro_classes; transfer, simp add: less_uexpr_def)
end

lift_definition rconj :: "('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel" is "op \<and>\<^sub>p"
  by (simp add: closure)

adhoc_overloading uconj rconj

lift_definition rdisj :: "('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel" is "op \<or>\<^sub>p"
  by (simp add: closure)

adhoc_overloading udisj rdisj

lift_definition rnot :: "('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel" is rea_not
  by (simp add: closure)

adhoc_overloading unot rnot

definition rdiff :: "('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel" where
"rdiff P Q = (rconj P (rnot Q))"

lift_definition rimplies :: "('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel" is "op \<Rightarrow>\<^sub>r"
  by (simp add: closure)

adhoc_overloading uimpl rimplies

lift_definition rfalse :: "('s, 'e) rrel" is false by (simp add: closure)

adhoc_overloading ufalse rfalse

lift_definition rtrue :: "('s, 'e) rrel" is true\<^sub>r by (simp add: closure)

adhoc_overloading utrue rtrue

interpretation boolean_algebra rdiff rnot rconj "op \<le>" "op <" rdisj rfalse rtrue
  apply (unfold_locales)
  apply (transfer, rel_auto)
            apply (transfer, rel_auto)
           apply (transfer, rel_auto)
          apply (transfer, rel_auto)
         apply (transfer, rel_auto)
        apply (transfer, rel_auto)
       apply (transfer, rel_auto)
      apply (transfer)
      apply (simp add: CRR_implies_RR truer_bottom_rpred)
     apply (transfer)
     apply (simp add: utp_pred_laws.sup_inf_distrib1)
    apply (transfer, simp)
  apply (transfer)
   apply (simp add: CRR_implies_RR RR_implies_R1 rea_not_or)
  apply (simp add: rdiff_def)
  done

lift_definition rwp ::
  "('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel" is "op wp\<^sub>r"
  by (simp add: CRR_implies_RR rea_not_CRR_closed seq_CRR_closed wp_rea_def)

adhoc_overloading
  uwp rwp

lift_definition rseq :: 
  "('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel"  is "op ;;"
  by (simp add: closure)

adhoc_overloading
  seq_comp rseq

lift_definition rcondition :: "('s, 'e) rrel \<Rightarrow> bool" is "\<lambda> P. P is RC" .

lemma rcondition_true: "rcondition true"
  by (transfer, simp add: closure)

lemma st_subst_CRR_closed [closure]:
  assumes "P is CRR"
  shows "(\<sigma> \<dagger>\<^sub>S P) is CRR"
  by (rule CRR_intro, simp_all add: unrest closure assms)

lift_definition rsubst :: "'s usubst \<Rightarrow> ('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel" is "st_subst"
  by (simp add: closure)

adhoc_overloading subst rsubst

lift_definition rcsp_do :: "'s upred \<Rightarrow> 's usubst \<Rightarrow> ('e list, 's) uexpr \<Rightarrow> ('s, 'e) rrel" ("\<^bold>\<Phi>'(_,_,_')") is csp_do
  by (simp add: closure)

lift_definition rcsp_enable :: "'s upred \<Rightarrow> ('e list, 's) uexpr \<Rightarrow> ('e set, 's) uexpr \<Rightarrow> ('s, 'e) rrel" ("\<^bold>\<E>'(_,_,_')") is csp_enable
  by (simp add: closure)


lemmas rrel_rep_eq = rtrue.rep_eq rfalse.rep_eq rcsp_do.rep_eq rcsp_enable.rep_eq

lemma [simp]: "P ; rfalse = rfalse"
  by (transfer, simp)
(*
thm wp

lemma wp_rcsp_do [wp]:
  "\<^bold>\<Phi>(s,\<sigma>,t) wp P = (\<I>(s,t) \<Rightarrow> (\<sigma> \<dagger> ?P)\<lbrakk>?t\<rbrakk>\<^sub>t)"

lemma
  fixes P :: "('s, 'e) rrel"
  shows "P wp false = "
*)

end