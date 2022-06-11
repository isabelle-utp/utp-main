(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: designs.thy                                                          *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Theory of Designs\<close>

theory designs
imports utheory
begin

subsection \<open>Type Injections\<close>

inject_type bool

subsection \<open>Theory Variables\<close>

declare_uvar ok :: "bool"

subsection \<open>Operators\<close>

definition design :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infix "\<turnstile>\<^sub>p" 90) where
"P \<turnstile>\<^sub>p Q = `ok \<and> {P} \<Rightarrow> ok' \<and> {Q}`"

declare design_def [evalp]

subsection \<open>Parser Extensions\<close>

syntax "_udesign" :: "uterm \<Rightarrow> uterm \<Rightarrow> uterm" (infix "\<turnstile>" 90)

translations "_udesign P Q" \<rightharpoonup> "P \<turnstile>\<^sub>p Q"

subsection \<open>Healthiness Conditions\<close>

definition H1 :: "hcond" where
"H1 P = `ok \<Rightarrow> {P}`"

declare H1_def [evalp]

subsection \<open>Theorems\<close>

theorem design_H1 :
"P \<turnstile>\<^sub>p Q is H1"
apply (unfold evalp)
apply (auto)
done
end