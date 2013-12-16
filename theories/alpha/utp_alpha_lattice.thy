(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alpha_lattice.thy                                                *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Alphabetised Lattice *}

theory utp_alpha_lattice
imports 
  "../core/utp_lattice" 
  "../laws/utp_alpha_laws"
begin

instantiation WF_ALPHA_PREDICATE :: (VALUE) order
begin

instance
  apply (intro_classes)
  apply (utp_alpha_tac, utp_pred_auto_tac)+
done
end

definition OrderA :: "'a ALPHABET \<Rightarrow> 'a WF_ALPHA_PREDICATE gorder" where
"OrderA a = \<lparr> partial_object.carrier = WF_ALPHA_PREDICATE_OVER a, eq = op =, le = op \<sqsubseteq> \<rparr>"

lemma OrderA_carrier [simp]:
  "partial_object.carrier (OrderA a) = WF_ALPHA_PREDICATE_OVER a"
  by (simp add:OrderA_def)

lemma OrderA_eq [simp]:
  "eq (OrderA a) = op ="
  by (simp add:OrderA_def)

lemma OrderA_le [simp]:
  "le (OrderA a) = op \<sqsubseteq>"
  by (simp add:OrderA_def)

interpretation alpha_partial_order: partial_order "(OrderA a)"
  where "partial_object.carrier (OrderA a) = WF_ALPHA_PREDICATE_OVER a"
    and "eq (OrderA a) = op ="
    and "le (OrderA a) = op \<sqsubseteq>"
  apply (unfold_locales)
  apply (simp_all add:OrderA_def)
done

lemma OrA_glb:
  assumes 
    "\<alpha> P = a" "\<alpha> Q = a"
  shows "greatest (OrderA a) (P \<or>\<^sub>\<alpha> Q) (Lower (OrderA a) {P, Q})"
  using assms
  apply (rule_tac greatest_LowerI)
  apply (simp_all add:OrderA_def)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (simp add:Lower_def)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (simp_all add:WF_ALPHA_PREDICATE_OVER_def)
  apply (simp add:alphabet)
done

lemma AndA_lub:
  assumes 
    "\<alpha> P = a" "\<alpha> Q = a"
  shows "least (OrderA a) (P \<and>\<^sub>\<alpha> Q) (Upper (OrderA a) {P, Q})"
  using assms
  apply (rule_tac least_UpperI)
  apply (simp_all add:OrderA_def)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (simp add:Upper_def)
  apply (utp_alpha_tac)
  apply (erule conjE, simp add:alphabet)
  apply (frule_tac x="P" in spec)
  apply (drule_tac x="Q" in spec)
  apply (simp add:alphabet)
  apply (utp_pred_auto_tac)
  apply (simp_all add:WF_ALPHA_PREDICATE_OVER_def)
  apply (simp add:alphabet)
done

interpretation alpha_lattice: lattice "(OrderA a)"
  where "partial_object.carrier (OrderA a) = WF_ALPHA_PREDICATE_OVER a"
    and "eq (OrderA a) = op ="
    and "le (OrderA a) = op \<sqsubseteq>"
  apply (unfold_locales)
  apply (rule_tac x="x \<and>\<^sub>\<alpha> y" in exI)
  apply (simp_all add:WF_ALPHA_PREDICATE_OVER_def AndA_lub)
  apply (rule_tac x="x \<or>\<^sub>\<alpha> y" in exI)  
  apply (simp_all add:WF_ALPHA_PREDICATE_OVER_def OrA_glb)
done

definition InfA ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE set \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" ("\<Or>\<^bsub>_ \<^esub>_" [900,900] 900) where
"InfA a ps = (if ps = {} then false\<^bsub>a\<^esub> else MkPredA (a, \<Sqinter> {\<lbrakk>p\<rbrakk>\<pi> | p. p \<in> ps}))"

theorem InfA_rep_eq:
  "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a \<Longrightarrow>
   DestPredA (\<Or>\<^bsub>a \<^esub>ps) = (a, \<Sqinter> {\<lbrakk>p\<rbrakk>\<pi> | p. p \<in> ps})"
  apply (subgoal_tac "(a, \<Sqinter> {\<lbrakk>p\<rbrakk>\<pi> | p. p \<in> ps}) \<in> WF_ALPHA_PREDICATE")
  apply (simp add:InfA_def)
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (auto simp add:bot_WF_PREDICATE_def FalseA_rep_eq)
  apply (auto simp add:WF_ALPHA_PREDICATE_OVER_def WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (auto intro: unrest)
done

lemma InfA_alphabet [alphabet]:
  "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a \<Longrightarrow> \<alpha> (\<Or>\<^bsub>a\<^esub> ps) = a"
  by (simp add:pred_alphabet_def InfA_rep_eq)

lemma EvalA_InfA [evala]:
  "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a \<Longrightarrow> \<lbrakk>\<Or>\<^bsub>a\<^esub> ps\<rbrakk>\<pi> = \<Sqinter> {\<lbrakk>p\<rbrakk>\<pi> | p. p \<in> ps}"
  by (auto simp add: EvalA_def InfA_rep_eq)

lemma WF_ALPHA_PREDICATE_OVER_member [alphabet]:
  "\<lbrakk> ps \<subseteq> WF_ALPHA_PREDICATE_OVER a; p \<in> ps \<rbrakk> \<Longrightarrow> \<alpha> p = a"
  by (auto simp add:WF_ALPHA_PREDICATE_OVER_def)

lemma InfA_glb:
  assumes 
    "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a"
  shows "greatest (OrderA a) (\<Or>\<^bsub>a\<^esub> ps) (Lower (OrderA a) ps)"
  using assms
  apply (rule_tac greatest_LowerI)
  apply (simp_all)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (auto simp add:Lower_def)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (metis InfA_alphabet WF_ALPHA_PREDICATE_OVER_intro)
done

definition SupA ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE set \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" ("\<And>\<^bsub>_ \<^esub>_" [900,900] 900) where
"SupA a ps = (if ps = {} then true\<^bsub>a\<^esub> else MkPredA (a, \<Squnion> {\<lbrakk>p\<rbrakk>\<pi> | p. p \<in> ps}))"

theorem SupA_rep_eq:
  "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a \<Longrightarrow>
   DestPredA (\<And>\<^bsub>a\<^esub> ps) = (a, \<Squnion> {\<lbrakk>p\<rbrakk>\<pi> | p. p \<in> ps})"
  apply (subgoal_tac "(a, \<Squnion> {\<lbrakk>p\<rbrakk>\<pi> | p. p \<in> ps}) \<in> WF_ALPHA_PREDICATE")
  apply (simp add:SupA_def)
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (auto simp add:top_WF_PREDICATE_def TrueA_rep_eq)
  apply (auto simp add:WF_ALPHA_PREDICATE_OVER_def WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (auto intro: unrest)
done

lemma SupA_alphabet [alphabet]:
  "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a \<Longrightarrow> \<alpha> (\<And>\<^bsub>a\<^esub> ps) = a"
  by (simp add:pred_alphabet_def SupA_rep_eq)

lemma EvalA_SupA [evala]:
  "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a \<Longrightarrow> \<lbrakk>\<And>\<^bsub>a\<^esub> ps\<rbrakk>\<pi> = \<Squnion> {\<lbrakk>p\<rbrakk>\<pi> | p. p \<in> ps}"
  by (auto simp add: EvalA_def SupA_rep_eq)

lemma SupA_lub:
  assumes 
    "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a"
  shows "least (OrderA a) (\<And>\<^bsub>a\<^esub> ps) (Upper (OrderA a) ps)"
  using assms
  apply (rule_tac least_UpperI)
  apply (simp_all)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (auto simp add:Upper_def)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (metis SupA_alphabet WF_ALPHA_PREDICATE_OVER_intro)
done

interpretation alpha_complete_lattice: complete_lattice "(OrderA a)"
  where "partial_object.carrier (OrderA a) = WF_ALPHA_PREDICATE_OVER a"
    and "eq (OrderA a) = op ="
    and "le (OrderA a) = op \<sqsubseteq>"
  apply (unfold_locales, simp_all)
  apply (rule_tac x="\<And>\<^bsub>a\<^esub> A" in exI)
  apply (metis SupA_lub)
  apply (rule_tac x="\<Or>\<^bsub>a\<^esub> A" in exI)
  apply (metis InfA_glb)
done

lemma InfA_is_inf:
  assumes "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a"
  shows "inf (OrderA a) ps = \<Or>\<^bsub>a\<^esub> ps"
  by (metis InfA_glb alpha_complete_lattice.inf_glb alpha_partial_order.weak_greatest_unique assms)

lemma SupA_is_sup:
  assumes "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a"
  shows "sup (OrderA a) ps = \<And>\<^bsub>a\<^esub> ps"
  by (metis SupA_lub alpha_complete_lattice.sup_lub alpha_partial_order.weak_least_unique assms)

lemma TrueA_least:
  "\<alpha> p = a \<Longrightarrow> true\<^bsub>a\<^esub> \<sqsubseteq> p"
  by (utp_alpha_tac, utp_pred_tac)

lemma FalseA_greatest:
  "\<alpha> p = a \<Longrightarrow> p \<sqsubseteq> false\<^bsub>a\<^esub>"
  by (utp_alpha_tac, utp_pred_tac)

sublocale complete_lattice \<subseteq> bounded_lattice ..

lemma TrueA_is_bottom:
  "bottom (OrderA a) = true\<^bsub>a\<^esub>"
  apply (rule sym)
  apply (rule alpha_complete_lattice.bottom_eq)
  apply (metis TrueA_alphabet WF_ALPHA_PREDICATE_OVER_intro)
  apply (metis TrueA_least WF_ALPHA_PREDICATE_OVER_alphabet)
done

lemma FalseA_is_top:
  "top (OrderA a) = false\<^bsub>a\<^esub>"
  apply (rule sym)
  apply (rule alpha_complete_lattice.top_eq)
  apply (metis FalseA_alphabet WF_ALPHA_PREDICATE_OVER_intro)
  apply (metis FalseA_greatest WF_ALPHA_PREDICATE_OVER_alphabet)
done

abbreviation "LfpA a \<equiv> LFP (OrderA a)"

abbreviation "GfpA a \<equiv> GFP (OrderA a)"

end
