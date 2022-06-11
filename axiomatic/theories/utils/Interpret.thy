(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Interpret.thy                                                        *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Interpretation Tools\<close>

theory Interpret
imports Main
begin

subsection \<open>Preliminaries\<close>

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

subsection \<open>Locale @{text interp}\<close>

text \<open>
  Interestingly, surjectivity of the interpretation function @{term f} turns
  out to be sufficient. Compare this, for instance, to the assumptions used in
  the theory @{text Transfer_extra} where we effectively exploit the fact that
  the abstraction and representation functions are indeed mutual inverses.
\<close>

locale interp =
fixes f :: "'a \<Rightarrow> 'b"
fixes A :: "'a set"
assumes f_surj_on_A: "surj_on f A"
begin
lemma forall_transfer:
"(\<forall>y::'b. P y) = (\<forall>(x::'a)\<in>A. P (f x))"
apply (safe)
\<comment> \<open>Subgoal 1\<close>
apply (drule_tac x = "f x" in spec)
apply (assumption)
\<comment> \<open>Subgoal 2\<close>
apply (insert surj_onD [OF f_surj_on_A])
apply (drule_tac x = "y" in meta_spec)
apply (clarsimp)
done

lemma exists_transfer:
"(\<exists>y::'b. P y) = (\<exists>(x::'a)\<in>A. P (f x))"
apply (safe)
\<comment> \<open>Subgoal 1\<close>
apply (insert surj_onD [OF f_surj_on_A]) [1]
apply (drule_tac x = "y" in meta_spec)
apply (clarsimp)
apply (rule_tac x = "x" in bexI)
apply (assumption)
apply (assumption)
\<comment> \<open>Subgoal 2\<close>
apply (rule_tac x = "f x" in exI)
apply (assumption)
done

lemma meta_transfer:
"(\<And>y::'b. PROP P y) \<equiv> (\<And>x::'a. x \<in> A \<Longrightarrow> PROP P (f x))"
apply (rule)
\<comment> \<open>Subgoal 1\<close>
apply (drule_tac x = "f x" in meta_spec)
apply (assumption)
\<comment> \<open>Subgoal 2\<close>
apply (insert surj_onD [OF f_surj_on_A])
apply (drule_tac x = "y" in meta_spec)
(* apply (clarsimp) *)
(* The following is clumsy but clarsimp seems not to work?! *)
apply (drule_tac x = "SOME x. x \<in> A \<and> f x = y" in meta_spec)
apply (subgoal_tac "(SOME x. x \<in> A \<and> f x = y) \<in> A")
\<comment> \<open>Subgoal 2.1\<close>
apply (clarsimp)
apply (subgoal_tac "f (SOME x. x \<in> A \<and> f x = y) = y")
\<comment> \<open>Subgoal 2.1.1\<close>
apply (clarsimp)
\<comment> \<open>Subgoal 2.1.2\<close>
apply (erule someI2_bex; clarsimp)
\<comment> \<open>Subgoal 2.2\<close>
apply (erule someI2_bex; clarsimp)
done

lemmas transfer =
  meta_transfer
  forall_transfer
  exists_transfer
end
end