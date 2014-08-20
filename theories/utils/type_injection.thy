(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: type_injection.thy                                                   *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)
(* LAST REVIEWED: 30 January 2014 *)

header {* Type Injections *}

theory type_injection
imports Main
begin

subsection {* Locale Definition *}

locale type_injection =
  fixes Abs and Rep and A and B
  assumes
   Abs_inverse : "x \<in> A \<Longrightarrow> Rep (Abs x) = x" and
   Abs_image : "Abs ` A = B"
begin

theorem Rep_inverse : "y \<in> B \<Longrightarrow> Abs (Rep y) = y"
apply (subgoal_tac "\<exists> x . x \<in> A \<and> y = Abs x")
apply (clarify)
apply (simp add: Abs_inverse)
apply (insert Abs_image)
apply (unfold image_def)
apply (safe)
apply (rule_tac x = "x" in exI)
apply (simp)
done

theorem Rep_image : "Rep ` B = A"
apply (insert Abs_image)
apply (unfold image_def)
apply (safe)
apply (simp add: Abs_inverse)
apply (rule_tac x = "Abs x" in bexI)
apply (simp add: Abs_inverse)
apply (simp)
apply (rule_tac x = "x" in bexI)
apply (simp)
apply (assumption)
done

theorem Rep_inject :
  assumes "x \<in> B" and "y \<in> B"
  shows "(Rep x = Rep y) = (x = y)"
apply (safe)
apply (drule_tac f = "Abs" in arg_cong)
apply (simp add: Rep_inverse assms)
done

theorem Abs_inject :
  assumes "x \<in> A" and "y \<in> A"
  shows "(Abs x = Abs y) = (x = y)"
apply (safe)
apply (drule_tac f = "Rep" in arg_cong)
apply (simp add: Abs_inverse assms)
done

theorems Rep_inject_sym = sym [OF Rep_inject]
theorems Abs_inject_sym = sym [OF Abs_inject]

theorem Rep_cases [cases set] :
  assumes "x \<in> A" and "\<And> y . x = Rep y \<Longrightarrow> P"
  shows P
apply (insert assms)
apply (drule_tac x = "Abs x" in meta_spec)
apply (simp add: Abs_inverse)
done

theorem Abs_cases [cases set (* type *)] :
  assumes "y \<in> B" and "\<And> x . y = Abs x \<Longrightarrow> P"
  shows P
apply (insert assms)
apply (drule_tac x = "Rep y" in meta_spec)
apply (simp add: Rep_inverse)
done

theorem Rep_induct [induct set] :
  assumes "x \<in> A" and "\<And> y . P (Rep y)"
  shows "P x"
apply (insert assms)
apply (drule_tac x = "Abs x" in meta_spec)
apply (simp add: Abs_inverse)
done

theorem Abs_induct [induct set (* type *)] :
  assumes "y \<in> B" and "\<And> x . P (Abs x)"
  shows "P y"
apply (insert assms)
apply (drule_tac x = "Rep y" in meta_spec)
apply (simp add: Rep_inverse)
done

theorem Rep_inj_on :
"inj_on Rep B"
apply (rule inj_onI)
apply (simp only: Rep_inject)
done

theorem Abs_inj_on :
"inj_on Abs A"
apply (rule inj_onI)
apply (simp only: Abs_inject)
done

theorem Rep_bij_betw :
"bij_betw Rep B A"
apply (unfold bij_betw_def)
apply (simp add: Rep_inj_on Rep_image)
done

theorem Abs_bij_betw :
"bij_betw Abs A B"
apply (unfold bij_betw_def)
apply (simp add: Abs_inj_on Abs_image)
done
end

subsection {* Instantiation Support *}

paragraph {* Instantiation Lemmas *}

lemma type_injection_inv_into_Abs :
"inj_on Abs A \<Longrightarrow> type_injection Abs (inv_into A Abs) A (Abs ` A)"
apply (simp add: type_injection_def)
done

lemma type_injection_inv_into_Rep :
"inj_on Rep B \<Longrightarrow> type_injection (inv_into B Rep) Rep (Rep ` B) B"
apply (simp add: type_injection_def)
apply (safe)
apply (rule f_inv_into_f)
apply (simp)
done

lemma type_injection_the_inv_into_Abs :
"inj_on Abs A \<Longrightarrow> type_injection Abs (the_inv_into A Abs) A (Abs ` A)"
apply (simp add: type_injection_def)
apply (safe)
apply (rule the_inv_into_f_f)
apply (simp_all)
done

lemma type_injection_the_inv_into_Rep :
"inj_on Rep B \<Longrightarrow> type_injection (the_inv_into B Rep) Rep (Rep ` B) B"
apply (simp add: type_injection_def)
apply (safe)
apply (rule f_the_inv_into_f)
apply (simp_all)
done

paragraph {* Existence Theorems *}

theorem inj_on_Abs_imp_type_injection :
"inj_on Abs A \<Longrightarrow> \<exists> Rep . type_injection Abs Rep A (Abs ` A)"
apply (rule_tac x = "inv_into A Abs" in exI)
apply (erule type_injection_inv_into_Abs)
done

theorem inj_on_Rep_imp_type_injection :
"inj_on Rep B \<Longrightarrow> \<exists> Abs . type_injection Abs Rep (Rep ` B) B"
apply (rule_tac x = "inv_into B Rep" in exI)
apply (erule type_injection_inv_into_Rep)
done

theorem bij_betw_Abs_imp_type_injection :
"bij_betw Abs A B \<Longrightarrow> \<exists> Rep . type_injection Abs Rep A B"
apply (unfold bij_betw_def)
apply (clarify)
apply (erule inj_on_Abs_imp_type_injection)
done

theorem bij_betw_Rep_imp_type_injection :
"bij_betw Rep B A \<Longrightarrow> \<exists> Abs . type_injection Abs Rep A B"
apply (unfold bij_betw_def)
apply (clarify)
apply (erule inj_on_Rep_imp_type_injection)
done

paragraph {* Type Injection vs Definition *}

theorem type_injection_iff_type_definition :
"type_injection Abs Rep A UNIV \<longleftrightarrow> type_definition Rep Abs A"
apply (unfold type_injection_def)
apply (unfold type_definition_def)
apply (safe)
apply (simp_all)
-- {* Subgoal 1 *}
apply (metis image_iff rangeI)
-- {* Subgoal 2 *}
apply (metis image_iff rangeI)
-- {* Subgoal 3 *}
apply (metis image_iff)
done
end
