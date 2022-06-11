(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Transfer_extra.thy                                                   *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Typedef Extras\<close>

theory Typedef_extra
imports Main
begin

subsection \<open>Transfer Laws\<close>

text \<open>
  We extend Isabelle's @{text type_definition} locale here with transfer laws
  for existential, universal and meta quantifiers. These laws can be used with
  plain rewriting via @{method simp}, hence do not require the full-blown use
  of the transfer package. Note that we have to instantiate them manually for
  particular type definitions, an example is at the bottom of the theory.
\<close>

context type_definition
begin
lemma meta_transfer:
"(\<And>y::'b. PROP P y) \<equiv> (\<And>x::'a. x \<in> A \<Longrightarrow> PROP P (Abs x))"
apply (rule)
\<comment> \<open>Subgoal 1\<close>
apply (drule_tac x = "Abs x" in meta_spec)
apply (assumption)
\<comment> \<open>Subgoal 2\<close>
apply (drule_tac x = "Rep y" in meta_spec)
apply (simp add: Rep)
apply (simp add: Rep_inverse)
done

lemma forall_transfer:
"(\<forall>y::'b. P y) = (\<forall>(x::'a)\<in>A. P (Abs x))"
apply (safe)
\<comment> \<open>Subgoal 1\<close>
apply (drule_tac x = "Abs x" in spec)
apply (assumption)
\<comment> \<open>Subgoal 2\<close>
apply (drule_tac x = "Rep y" in bspec)
apply (simp add: Rep)
apply (simp add: Rep_inverse)
done

lemma exists_transfer:
"(\<exists>y::'b. P y) = (\<exists>(x::'a)\<in>A. P (Abs x))"
apply (safe)
\<comment> \<open>Subgoal 1\<close>
apply (rule_tac x = "Rep y" in bexI)
apply (simp add: Rep_inverse)
apply (simp add: Rep)
\<comment> \<open>Subgoal 2\<close>
apply (rule_tac x = "Abs x" in exI)
apply (assumption)
done

lemmas transfer =
  meta_transfer
  forall_transfer
  exists_transfer
end

text \<open>An example of an instantiation i.e.~for the product type would be.\<close>

lemmas list_transfer =
  type_definition.transfer [OF Product_Type.type_definition_prod]

hide_fact list_transfer
end