(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: urel.thy                                                             *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Relational Predicates\<close>

theory urel
imports upred ulift
begin

subsection \<open>Operators\<close>

subsubsection \<open>Skip\<close>

definition SkipP :: "upred" where
"SkipP = LiftP (\<lambda>b. \<forall>v\<in>UNDASHED. b\<cdot>v = b\<cdot>(v\<acute>))"

notation SkipP ("II\<^sub>p")

subsubsection \<open>Composition\<close>

text \<open>\fixme{Give an algebraic definition once substitution is mechanised.}\<close>

lift_definition SemiP :: "upred \<Rightarrow> upred \<Rightarrow> upred"
is "(\<lambda>bs1 bs2.
  {b::ustate. \<exists>b1\<in>bs1. \<exists>b2\<in>bs2.
    (b \<cong>\<^sub>b b1 on UNDASHED \<union> NON_REL_VAR) \<and>
    (b \<cong>\<^sub>b b2 on DASHED \<union> NON_REL_VAR) \<and>
    (\<forall>v\<in>UNDASHED. b1\<cdot>(v\<acute>) = b2\<cdot>v)})"
done

notation SemiP (infixl ";\<^sub>p" 100)

subsection \<open>Proof Support\<close>

declare SkipP_def [evalp]

subsection \<open>Experiments\<close>

text \<open>\todo{Automate imposing @{class injectable} on free types!}\<close>

theorem "II\<^sub>p \<and>\<^sub>p (x = @(c::nat))\<^sub>p \<Rightarrow>\<^sub>p (x' = @(c))\<^sub>p"
apply (upred_tac)
apply (unfold ustate_app_poly_def)
apply (simp add: vars)
done
end