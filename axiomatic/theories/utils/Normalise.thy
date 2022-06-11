(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: Normalise.thy                                                        *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Normalisation\<close>

theory Normalise
imports Main
 "HOL-Eisbach.Eisbach"
begin

subsection \<open>Theorem Attribute\<close>

text \<open>Theorems and tactic used for normalisation.\<close>

named_theorems normalise "normalisation theorems"

subsection \<open>Normalisation Tactic\<close>

method normalise = (simp add: normalise)

subsection \<open>Type Class @{text normalise}\<close>

text \<open>
  Instantiation of the class @{text normalise} signals that normalisation can
  be performed on constructions that involve the underlying type. For now, we
  only consider chains of function updates. Importantly, the type must provide
  a linear order to ensure that normalisation does not loop.
\<close>

class normalise = linorder
begin
theorem fun_upd_normalise [normalise]:
fixes x :: "'a"
fixes y :: "'a"
shows "x < y \<Longrightarrow> f(y := a, x := b) = f(x := b, y := a)"
by (simp add: fun_upd_twist)
end

text \<open>
  The tactic below is not very efficient as using backtracking. In practice,
  it is slightly quicker to use plain simplification instead of substitution.
  Both approaches, however, suffer from the same drawback that dead ends may
  need to be explored. A better solution would implement some form of guarded
  rewriting.
\<close>

method fun_upd_normalise_tac =
  (subst fun_upd_normalise, (simp; fail))+

end