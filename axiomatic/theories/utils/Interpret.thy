(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Interpret.thy                                                        *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk frank.zeyda@york.ac.uk                     *)
(******************************************************************************)
(* LAST REVIEWED: 15 Feb 2017 *)

section {* Interpretation Tools *}

theory Interpret
imports Main
begin

subsection {* Preliminaries *}

definition surj_on :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool" where
"surj_on f A \<longleftrightarrow> f ` A = UNIV"

lemma surj_onI [intro]:
"f ` A = UNIV \<Longrightarrow> surj_on f A"
apply (unfold surj_on_def)
apply (assumption)
done

lemma surj_onD [dest]:
"surj_on f A \<Longrightarrow> \<exists>x\<in>A. f x = y"
apply (unfold surj_on_def)
apply (simp add: image_def)
apply (simp add: set_eq_iff)
apply (drule_tac x = "y" in spec)
apply (clarsimp)
apply (rule_tac x = "x" in bexI)
apply (rule refl)
apply (assumption)
done

lemma surj_comp_funct:
"inj f \<Longrightarrow> surj (\<lambda>g. g o f)"
apply (rule_tac f = "\<lambda>g. g o (inv f)" in surjI)
apply (simp)
done

subsection {* Locale @{text interp} *}

text {*
  Interestingly, surjectivity of the interpretation function @{term f} turns
  out to be sufficient. Compare this, for instance, to the assumptions used in
  the theory @{text Transfer_extra} where we effectively exploit the fact that
  the abstraction and representation functions are indeed mutual inverses.
*}

locale interp =
fixes f :: "'a \<Rightarrow> 'b"
fixes A :: "'a set"
assumes f_surj_on_A: "surj_on f A"
begin
lemma forall_transfer:
"(\<forall>y::'b. P y) = (\<forall>(x::'a)\<in>A. P (f x))"
apply (safe)
-- {* Subgoal 1 *}
apply (drule_tac x = "f x" in spec)
apply (assumption)
-- {* Subgoal 2 *}
apply (insert surj_onD [OF f_surj_on_A])
apply (drule_tac x = "y" in meta_spec)
apply (clarsimp)
done

lemma exists_transfer:
"(\<exists>y::'b. P y) = (\<exists>(x::'a)\<in>A. P (f x))"
apply (safe)
-- {* Subgoal 1 *}
apply (insert surj_onD [OF f_surj_on_A]) [1]
apply (drule_tac x = "y" in meta_spec)
apply (clarsimp)
apply (rule_tac x = "x" in bexI)
apply (assumption)
apply (assumption)
-- {* Subgoal 2 *}
apply (rule_tac x = "f x" in exI)
apply (assumption)
done

lemma meta_transfer:
"(\<And>y::'b. PROP P y) \<equiv> (\<And>x::'a. x \<in> A \<Longrightarrow> PROP P (f x))"
apply (rule)
-- {* Subgoal 1 *}
apply (drule_tac x = "f x" in meta_spec)
apply (assumption)
-- {* Subgoal 2 *}
apply (insert surj_onD [OF f_surj_on_A])
apply (drule_tac x = "y" in meta_spec)
(* apply (clarsimp) *)
(* The following is clumsy but clarsimp seems not to work?! *)
apply (drule_tac x = "SOME x. x \<in> A \<and> f x = y" in meta_spec)
apply (subgoal_tac "(SOME x. x \<in> A \<and> f x = y) \<in> A")
-- {* Subgoal 2.1 *}
apply (clarsimp)
apply (subgoal_tac "f (SOME x. x \<in> A \<and> f x = y) = y")
-- {* Subgoal 2.1.1 *}
apply (clarsimp)
-- {* Subgoal 2.1.2 *}
apply (erule someI2_bex; clarsimp)
-- {* Subgoal 2.2 *}
apply (erule someI2_bex; clarsimp)
done

lemmas transfer =
  meta_transfer
  forall_transfer
  exists_transfer
end
end