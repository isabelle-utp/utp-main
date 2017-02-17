(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: unrest_sf.thy                                                        *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)

section {* Unrestriction *}

theory unrest_sf
imports uvar ustate
begin

default_sort type

subsection {* Definition of Unrestriction *}

definition unrest_sf :: "uvar set \<Rightarrow> (ustate \<Rightarrow> 'a) \<Rightarrow> bool" where
"unrest_sf vs f = (\<forall>v\<in>vs. \<forall>s x. f s(v :=\<^sub>u x)\<^sub>s = f s)"

subsection {* Theorems *}

theorem unrest_sf_empty:
"unrest_sf {} f"
apply (unfold unrest_sf_def)
apply (clarsimp)
done

theorem unrest_sf_subset:
"vs1 \<subseteq> vs2 \<Longrightarrow> unrest_sf vs2 f \<Longrightarrow> unrest_sf vs1 f"
apply (unfold unrest_sf_def)
apply (blast)
done

theorem unrest_sf_const:
"unrest_sf vs (\<lambda>_. c)"
apply (unfold unrest_sf_def)
apply (clarsimp)
done

theorem unrest_sf_uvar:
"unrest_sf (vs - {v}) (\<lambda>s. f s\<cdot>v)"
apply (unfold unrest_sf_def)
apply (transfer)
apply (clarsimp)
done

theorem unrest_sf_var:
"unrest_sf (vs - {v\<down>}) (\<lambda>s. f s\<star>v)"
apply (unfold unrest_sf_def)
apply (transfer)
apply (clarsimp)
done
end