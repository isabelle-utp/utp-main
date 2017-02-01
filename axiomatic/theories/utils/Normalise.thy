(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: Normalise.thy                                                        *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 16 Jan 2016 *)

section {* Normalisation *}

theory Normalise
imports Main
 "~~/src/HOL/Eisbach/Eisbach"
begin

subsection {* Theorem Attribute *}

text {* Theorems and tactic used for normalisation. *}

named_theorems normalise "normalisation theorems"

subsection {* Normalisation Tactic *}

method normalise = (simp add: normalise)

subsection {* Type Class @{text normalise} *}

text {*
  Instantiation of the class @{text normalise} signals that normalisation can
  be performed on constructions that involve the underlying type. For now, we
  only consider chains of function updates. Importantly, the type must provide
  a linear order to ensure that normalisation does not loop.
*}

class normalise = linorder
begin
theorem fun_upd_normalise [normalise]:
fixes x :: "'a"
fixes y :: "'a"
shows "x < y \<Longrightarrow> f(y := a, x := b) = f(x := b, y := a)"
by (simp add: fun_upd_twist)
end

text {*
  The tactic below is not very efficient as using backtracking. In practice,
  it is slightly quicker to use plain simplification instead of substitution.
  Both approaches, however, suffer from the same drawback that dead ends may
  need to be explored. A better solution would implement some form of guarded
  rewriting.
*}

method fun_upd_normalise_tac =
  (subst fun_upd_normalise, (simp; fail))+
end