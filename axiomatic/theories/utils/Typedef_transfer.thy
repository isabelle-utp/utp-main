(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: Typedef_transfer.thy                                                 *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 10 Feb 2017 *)

section {* Light-weight Transfer *}

theory Typedef_transfer
imports Main
begin

text {*
  We extend Isabelle's @{text type_definition} locale with transfer laws for
  existential, universal and meta quantification. These laws can be used with
  plain rewriting via @{method simp}, hence do not require the full-blown use
  of the transfer package. Note that we have to instantiate them manually for
  particular type definitions, and example is at the bottom of the theory.
*}

context type_definition
begin
lemma meta_all_typedef_transfer:
"(\<And>(y::'b). PROP P y) \<equiv> (\<And>(x::'a). PROP P (Abs x))"
apply (rule)
-- {* Subgoal 1 *}
apply (drule_tac x = "Abs x" in meta_spec)
apply (assumption)
-- {* Subgoal 2 *}
apply (drule_tac x = "Rep y" in meta_spec)
apply (simp add: Rep_inverse)
done

lemma all_typedef_transfer:
"(\<forall>(y::'b). P y) = (\<forall>(x::'a). P (Abs x))"
apply (safe)
-- {* Subgoal 1 *}
apply (drule_tac x = "Abs x" in spec)
apply (assumption)
-- {* Subgoal 2 *}
apply (drule_tac x = "Rep y" in spec)
apply (simp add: Rep_inverse)
done

lemma exists_typedef_transfer:
"(\<exists>(y::'b). P y) = (\<exists>(x::'a). P (Abs x))"
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "Rep y" in exI)
apply (simp add: Rep_inverse)
-- {* Subgoal 2 *}
apply (rule_tac x = "Abs x" in exI)
apply (simp add: Rep_inverse)
done

lemmas typedef_transfer =
  meta_all_typedef_transfer
  all_typedef_transfer
  exists_typedef_transfer
end

text {* An example of an instantiation i.e.~for the product type would be. *}

lemmas list_transfer = 
  type_definition.typedef_transfer [OF Product_Type.type_definition_prod]

hide_fact list_transfer
end