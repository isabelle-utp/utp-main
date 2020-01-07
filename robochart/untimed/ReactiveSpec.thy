section \<open> Reactive Specifications \<close>

theory ReactiveSpec
  imports "UTP-Circus.utp_circus"
begin

consts
  seq_comp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr ";" 61)

typedef ('s, 'e) rrel = "{P :: ('s, 'e) action. (P is CDC) \<and> (P is CRR)}"
  by (rule_tac x="false" in exI, simp add: closure)

setup_lifting type_definition_rrel

notation Rep_rrel ("\<lbrakk>_\<rbrakk>\<^sub>R")

lemma rrel_eq_transfer: "P = Q \<longleftrightarrow> \<lbrakk>P\<rbrakk>\<^sub>R = \<lbrakk>Q\<rbrakk>\<^sub>R"
  by (auto, metis Rep_rrel_inverse)

instantiation rrel :: (type, type) refine
begin
  lift_definition less_eq_rrel :: "('a, 'b) rrel \<Rightarrow> ('a, 'b) rrel \<Rightarrow> bool" is "less_eq" .
  lift_definition less_rrel :: "('a, 'b) rrel \<Rightarrow> ('a, 'b) rrel \<Rightarrow> bool" is "less" .
instance by (intro_classes; transfer, simp add: less_uexpr_def)
end

lift_definition rconj :: "('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel" is "(\<and>\<^sub>p)"
  by (simp add: closure)

adhoc_overloading uconj rconj

lift_definition rdisj :: "('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel" is "(\<or>\<^sub>p)"
  by (simp add: closure)

adhoc_overloading udisj rdisj

(*
lift_definition rnot :: "('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel" is rea_not
  by (simp add: closure)

adhoc_overloading unot rnot

definition rdiff :: "('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel" where
"rdiff P Q = (rconj P (rnot Q))"

lift_definition rimplies :: "('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel" is "op \<Rightarrow>\<^sub>r"
  by (simp add: closure)

adhoc_overloading uimpl rimplies
*)

lift_definition rfalse :: "('s, 'e) rrel" is false by (simp add: closure)

adhoc_overloading ufalse rfalse

lift_definition rtrue :: "('s, 'e) rrel" is true\<^sub>r by (simp add: closure)

adhoc_overloading utrue rtrue

(*
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
*)

lemma wp_rea_CRR_closed [closure]:
  assumes "P is CRR" "Q is CRR"
  shows "P wp\<^sub>r Q is CRR"
  by (simp add: CRR_implies_RR rea_not_CRR_closed seq_CRR_closed wp_rea_def assms)

lemma wp_rea_CDC_closed [closure]:
  assumes "Q is CDC"
  shows "P wp\<^sub>r Q is CDC"
proof -
  have "P wp\<^sub>r (CDC Q) is CDC"
    by (rel_blast)
  thus ?thesis
    by (simp add: assms Healthy_if)
qed

lift_definition rwp ::
  "('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel" is "(wp\<^sub>r)"
  by (simp add: closure)

adhoc_overloading
  uwp rwp

lift_definition rseq :: 
  "('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel"  is "(;;)"
  by (simp add: closure)

adhoc_overloading
  seq_comp rseq

lift_definition rcondition :: "('s, 'e) rrel \<Rightarrow> bool" is "\<lambda> P. P is RC" .

lemma rcondition_true: "rcondition true"
  by (transfer, simp add: closure)

lift_definition rsubst :: "'s usubst \<Rightarrow> ('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel" is "st_subst"
  by (simp add: closure)

adhoc_overloading usubst rsubst

lift_definition rR4 :: "('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel" ("[_]\<^sub>\<rhd>") is "R4" by (simp add: closure)

lift_definition rR5 :: "('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel" ("[_]\<^sub>\<box>") is "R5" by (simp add: closure)

lift_definition rcsp_do :: "'s upred \<Rightarrow> 's usubst \<Rightarrow> ('e list, 's) uexpr \<Rightarrow> ('s, 'e) rrel" ("\<^bold>\<Phi>'(_,_,_')") is csp_do
  by (simp add: closure)

lift_definition rcsp_enable :: "'s upred \<Rightarrow> ('e list, 's) uexpr \<Rightarrow> ('e set, 's) uexpr \<Rightarrow> ('s, 'e) rrel" ("\<^bold>\<E>'(_,_,_')") is csp_enable
  by (simp add: closure)

lift_definition runrest :: "('a \<Longrightarrow> ('s,'e) sfrd \<times> ('s,'e) sfrd) \<Rightarrow> ('s, 'e) rrel \<Rightarrow> bool" is "unrest_uexpr" .

adhoc_overloading unrest runrest

lemmas rrel_rep_eq = rtrue.rep_eq rfalse.rep_eq rconj.rep_eq rdisj.rep_eq rcsp_do.rep_eq rcsp_enable.rep_eq rrel_eq_transfer

lemma rfalse_right_anhil [simp]: "P ; rfalse = rfalse"
  by (transfer, simp)

end