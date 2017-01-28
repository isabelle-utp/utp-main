(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: designs.thy                                                          *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 26 Jan 2016 *)

section {* Theory of Designs *}

theory designs
imports utheory
begin

subsection {* Type Injections *}

inject_type bool

subsection {* Theory Variables *}

declare_uvar ok :: "bool"

subsection {* Operators *}

definition design :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infix "\<turnstile>\<^sub>p" 90) where
"P \<turnstile>\<^sub>p Q = `ok \<and> {P} \<Rightarrow> ok' \<and> {Q}`"

declare design_def [evalp]

subsection {* Parser Extensions *}

syntax "_udesign" :: "uterm \<Rightarrow> uterm \<Rightarrow> uterm" (infix "\<turnstile>" 90)

translations "_udesign P Q" \<rightharpoonup> "P \<turnstile>\<^sub>p Q"

subsection {* Healthiness Conditions *}

definition H1 :: "hcond" where
"H1 P = `ok \<Rightarrow> {P}`"

declare H1_def [evalp]

subsection {* Theorems *}

theorem design_H1 :
"P \<turnstile>\<^sub>p Q is H1"
apply (unfold evalp)
apply (auto)
done
end