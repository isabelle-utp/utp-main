(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Interp.thy                                                           *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk frank.zeyda@york.ac.uk                     *)
(******************************************************************************)
(* LAST REVIEWED: 7/12/2016 *)

section {* Interpretation Tools *}

theory Interp
imports Main
begin

subsection {* Interpretation Locale *}

locale interp =
fixes f :: "'a \<Rightarrow> 'b"
assumes f_inj : "inj f"
begin
lemma meta_interp_law:
"(\<And>P. PROP Q P) \<equiv> (\<And>P. PROP Q (P o f))"
  apply (rule equal_intr_rule)
    -- {* Subgoal 1 *}
   apply (drule_tac x = "P o f" in meta_spec)
   apply (assumption)
    -- {* Subgoal 2 *}
  apply (drule_tac x = "P o inv f" in meta_spec)
  apply (simp add: f_inj)
done

lemma all_interp_law:
"(\<forall>P. Q P) = (\<forall>P. Q (P o f))"
  apply (safe)
    -- {* Subgoal 1 *}
   apply (drule_tac x = "P o f" in spec)
   apply (assumption)
    -- {* Subgoal 2 *}
  apply (drule_tac x = "P o inv f" in spec)
  apply (simp add: f_inj)
done

lemma exists_interp_law:
"(\<exists>P. Q P) = (\<exists>P. Q (P o f))"
  apply (safe)
    -- {* Subgoal 1 *}
   apply (rule_tac x = "P o inv f" in exI)
   apply (simp add: f_inj)
    -- {* Subgoal 2 *}
  apply (rule_tac x = "P o f" in exI)
  apply (assumption)
done
end
end