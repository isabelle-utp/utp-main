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

default_sort TYPED_MODEL

instantiation uapred :: (TYPED_MODEL) order
begin

instance
  apply (intro_classes)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (utp_alpha_tac)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (utp_alpha_tac)
done
end

definition OrderA :: "'a alpha \<Rightarrow> 'a uapred gorder" where
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
  apply (utp_alpha_tac)
  apply (metis (mono_tags) OrP_refine WF_ALPHA_PREDICATE_OVER_def mem_Collect_eq)
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
  apply (metis (mono_tags) RefineP_seperation_refine WF_ALPHA_PREDICATE_OVER_def mem_Collect_eq)
  apply (metis (mono_tags) WF_ALPHA_PREDICATE_OVER_def mem_Collect_eq)
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
  "'a alpha \<Rightarrow>
   'a uapred set \<Rightarrow>
   'a uapred" ("\<Sqinter>\<^bsub>_\<^esub> _" [900] 900) where
"\<Sqinter>\<^bsub>a\<^esub> ps = (if (ps \<subseteq> WF_ALPHA_PREDICATE_OVER a) then (\<Or>\<^bsub>a\<^esub> ps) else FalseA a)"

definition InfiA ::
  "'a alpha \<Rightarrow>
   'b set \<Rightarrow> ('b::type \<Rightarrow> 'a uapred) \<Rightarrow>
   'a uapred" where
"InfiA a A f = \<Sqinter>\<^bsub>a\<^esub> (f ` A)"

definition SupA ::
  "'a alpha \<Rightarrow>
   'a uapred set \<Rightarrow>
   'a uapred" ("\<Squnion>\<^bsub>_\<^esub> _" [900] 900) where
"\<Squnion>\<^bsub>a\<^esub> ps = (if (ps \<subseteq> WF_ALPHA_PREDICATE_OVER a) then (\<And>\<^bsub>a\<^esub> ps) else TrueA a)"

definition SuprA ::
  "'a alpha \<Rightarrow>
   'b set \<Rightarrow> ('b::type \<Rightarrow> 'a uapred) \<Rightarrow>
   'a uapred" where
"SuprA a A f = \<Squnion>\<^bsub>a\<^esub> (f ` A)"

declare InfA_def [evala]
declare SupA_def [evala]

lemma InfA_alphabet [alphabet]:
  "\<alpha> (\<Sqinter>\<^bsub>a\<^esub> ps) = a"
  by (simp add:InfA_def alphabet)

lemma SupA_alphabet [alphabet]:
  "\<alpha> (\<Squnion>\<^bsub>a\<^esub> ps) = a"
  by (simp add:SupA_def alphabet)

lemma InfiA_alphabet [alphabet]:
  "\<alpha> (InfiA a A f) = a"
  by (simp add:InfiA_def alphabet)

lemma SuprA_alphabet [alphabet]:
  "\<alpha> (SuprA a A f) = a"
  by (simp add:SuprA_def alphabet)

lemma InfA_glb:
  assumes 
    "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a"
  shows "greatest (OrderA a) (\<Sqinter>\<^bsub>a\<^esub> ps) (Lower (OrderA a) ps)"
  using assms
  apply (rule_tac greatest_LowerI)
  apply (simp_all)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (auto simp add:Lower_def)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (metis WF_ALPHA_PREDICATE_OVER_member order_refl)
  apply (metis WF_ALPHA_PREDICATE_OVER_member order_refl)
  apply (metis (lifting, full_types) InfA_alphabet WF_ALPHA_PREDICATE_OVER_def mem_Collect_eq)
done

lemma SupA_lub:
  assumes 
    "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a"
  shows "least (OrderA a) (\<Squnion>\<^bsub>a\<^esub> ps) (Upper (OrderA a) ps)"
  using assms
  apply (rule_tac least_UpperI)
  apply (simp_all)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (auto simp add:Upper_def)
  apply (utp_alpha_tac, utp_pred_auto_tac)
  apply (metis WF_ALPHA_PREDICATE_OVER_member order_refl)
  apply (metis WF_ALPHA_PREDICATE_OVER_member order_refl)
  apply (metis (mono_tags) SupA_alphabet WF_ALPHA_PREDICATE_OVER_def mem_Collect_eq)
done


text {* Alphabetised predicates for a complete lattice over any alphabet *}

interpretation alpha_complete_lattice: complete_lattice "(OrderA a)"
  where "partial_object.carrier (OrderA a) = WF_ALPHA_PREDICATE_OVER a"
    and "eq (OrderA a) = op ="
    and "le (OrderA a) = op \<sqsubseteq>"
  apply (unfold_locales, simp_all)
  apply (rule_tac x="\<Squnion>\<^bsub>a\<^esub> A" in exI)
  apply (metis SupA_lub)
  apply (rule_tac x="\<Sqinter>\<^bsub>a\<^esub> A" in exI)
  apply (metis InfA_glb)
done

lemma InfA_is_inf:
  assumes "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a"
  shows "inf (OrderA a) ps = \<Sqinter>\<^bsub>a\<^esub> ps"
  by (metis InfA_glb alpha_complete_lattice.inf_glb alpha_partial_order.greatest_unique assms)

lemma SupA_is_sup:
  assumes "ps \<subseteq> WF_ALPHA_PREDICATE_OVER a"
  shows "sup (OrderA a) ps = \<Squnion>\<^bsub>a\<^esub> ps"
  by (metis SupA_lub alpha_complete_lattice.sup_lub alpha_partial_order.least_unique assms)

lemma InfiA_is_infi:
  assumes "f`ps \<subseteq> WF_ALPHA_PREDICATE_OVER a"
  shows "infi (OrderA a) ps f = InfiA a ps f"
  using assms by (simp add:InfiA_def InfA_is_inf[THEN sym] infi_def)

lemma SuprA_is_supr:
  assumes "f`ps \<subseteq> WF_ALPHA_PREDICATE_OVER a"
  shows "supr (OrderA a) ps f = SuprA a ps f"
  using assms by (simp add:SuprA_def SupA_is_sup[THEN sym] supr_def)

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
  apply (metis (mono_tags) TrueA_alphabet WF_ALPHA_PREDICATE_OVER_def mem_Collect_eq)
  apply (metis TrueA_least WF_ALPHA_PREDICATE_OVER_member subset_refl)
done

lemma FalseA_is_top:
  "top (OrderA a) = false\<^bsub>a\<^esub>"
  apply (rule sym)
  apply (rule alpha_complete_lattice.top_eq)
  apply (metis (mono_tags) FalseA_alphabet WF_ALPHA_PREDICATE_OVER_def mem_Collect_eq)
  apply (metis FalseA_greatest WF_ALPHA_PREDICATE_OVER_member order_refl)
done

abbreviation "LfpA a \<equiv> LFP (OrderA a)"

abbreviation "GfpA a \<equiv> GFP (OrderA a)"


end
