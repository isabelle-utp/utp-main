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


lift_definition rseq :: 
  "('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel"  is "op ;;"
  by (simp add: closure)

adhoc_overloading
  seq_comp rseq

lift_definition rcondition :: "('s, 'e) rrel \<Rightarrow> bool" is "\<lambda> P. P is RC" .

lemma rcondition_true: "rcondition true"
  by (transfer, simp add: closure)

end