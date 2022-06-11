(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_avar.thy                                                         *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@gmail.com                  *)
(******************************************************************************)
(* LAST REVIEWED: 11 Jun 2022 *)

section \<open>Axiomatic Variables\<close>

theory utp_avar
  imports
  "UTP1.utp_var"
  "../../../axiomatic/Axiomatic"
begin recall_syntax

default_sort type

text \<open>
  Note that theory @{text ulens} already includes key definitions and laws
  for defining the required lenses for axiomatic variables. Our concern here
  is merely to integrate them smoothly into Isabelle/UTP.
\<close>

subsection \<open>Compatibility with Isabelle/UTP\<close>

subsubsection \<open>Late-Inclusion Side-effects\<close>

text \<open>
  A problem in Isabelle/HOL is that depending on the order in which imported
  theories are processed, undeclaration of syntax and notations may be lost
  after the inclusion; in particular, if a theory is imported that does not
  depend on the theory that undeclares the respective notation or syntax. We
  use the @{text TotalRecall} utility and @{command purge_notation} command
  to solve this problem here.
\<close>

\<comment> \<open>From @{text utype}.\<close>

purge_notation (ASCII)
  Set.member  ("'(:')") and
  Set.member  ("(_/ : _)" [51, 51] 50)

subsubsection \<open>Syntactic Adjustments\<close>

text \<open>
  We undeclare several notations here to avoid inherent ambiguities with those
  used in Isabelle/UTP. We note that it is sufficient to remove them as input
  notations, namely to be still able to take advantage of them being printed.
\<close>

purge_notation (input)
  dash ("_\<acute>" [1000] 1000) and
  undash ("_\<inverse>" [1000] 1000) and
  subscr ("_\<^bsub>_\<^esub>" [1000, 0] 1000)

text \<open>The prefix @{text "uvar."} is important to avoid errors by the tool.\<close>

purge_syntax (input)
  "_MkPVar1" :: "id \<Rightarrow>         'a uvar.var" ("$_" [1000] 1000)
  "_MkPVar2" :: "id \<Rightarrow> type \<Rightarrow> 'a uvar.var" ("$_:{_}"  [1000, 0] 1000)
  "_MkPVar3" :: "id \<Rightarrow> type \<Rightarrow> 'a uvar.var" ("$_:{_}-" [1000, 0] 1000)

purge_syntax (input)
  "_MkAxVar1" :: "id \<Rightarrow>         ('a, 'b) lens" ("@_" [1000] 1000)
  "_MkAxVar2" :: "id \<Rightarrow> type \<Rightarrow> ('a, 'b) lens" ("@_:{_}"  [1000, 0] 1000)
  "_MkAxVar3" :: "id \<Rightarrow> type \<Rightarrow> ('a, 'b) lens" ("@_:{_}-" [1000, 0] 1000)

purge_notation (input)
  ustate_app_mono ("_\<cdot>_" [1000, 1000] 1000) and
  ustate_app_poly ("_\<star>_" [1000, 1000] 1000)

subsubsection \<open>Hiding Constants and Types\<close>

hide_type (open) uvar.uvar

subsubsection \<open>Forgetting Liftings\<close>

text \<open>The liftings below can interfere with the automatic proof tactics.\<close>

lifting_forget String.literal.lifting
lifting_forget uvar.var.lifting
lifting_forget ustate.ustate.lifting

subsection \<open>Variable Constructors\<close>

definition in_avar :: "'a::injectable var \<Rightarrow> ('a \<Longrightarrow> '\<alpha>::ust \<times> '\<beta>)" where
[simp]: "in_avar x = in_var (avar_ust\<^sub>L x)"

definition out_avar :: "'a::injectable var \<Rightarrow> ('a \<Longrightarrow> '\<alpha> \<times> '\<beta>::ust)" where
[simp]: "out_avar x = out_var (avar_ust\<^sub>L x)"

subsection \<open> Variable Syntax \<close>

syntax "_MkAxVar1" :: "id \<Rightarrow>         svid" ("{_}" [1000] 1000)
syntax "_MkAxVar2" :: "id \<Rightarrow> type \<Rightarrow> svid" ("{_::_}"  [1000, 0] 1000)
syntax "_MkAxVar3" :: "id \<Rightarrow> type \<Rightarrow> svid" ("{_::_}-" [1000, 0] 1000)

syntax "_MkAxVar1_logic" :: "id \<Rightarrow>         logic" ("{_}\<^sub>x" [1000] 1000)
syntax "_MkAxVar2_logic" :: "id \<Rightarrow> type \<Rightarrow> logic" ("{_::_}\<^sub>x"  [1000, 0] 1000)
syntax "_MkAxVar3_logic" :: "id \<Rightarrow> type \<Rightarrow> logic" ("{_::_}\<^sub>x-" [1000, 0] 1000)

translations "_MkAxVar1 n"   \<rightleftharpoons> "_MkPVar1 n"
translations "_MkAxVar2 n a" \<rightleftharpoons> "_MkPVar2 n a"
translations "_MkAxVar3 n a" \<rightleftharpoons> "_MkPVar3 n a"

translations "_MkAxVar1_logic n"   \<rightharpoonup> "_MkPVar1 n"
translations "_MkAxVar2_logic n a" \<rightharpoonup> "_MkPVar2 n a"
translations "_MkAxVar3_logic n a" \<rightharpoonup> "_MkPVar3 n a"
end
