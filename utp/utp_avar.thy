(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: utp_avar.thy                                                         *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 27 Jan 2017 *)

section {* Axiomatic Variables *}

theory utp_avar
imports utp_var ulens
begin

default_sort type

subsection {* Compatibility with Isabelle/UTP *}

subsubsection {* Hiding Constants and Types *}

hide_type (open) uvar.uvar

subsubsection {* Syntax Adjustments *}

text {* We undeclare several notations to avoid ambiguities in Isabelle/UTP. *}

no_notation (input) dash ("_\<acute>" [1000] 1000)
no_notation (input) undash ("_\<inverse>" [1000] 1000)
no_notation (input) subscr ("_\<^bsub>_\<^esub>" [1000, 0] 1000)

no_syntax (input) "_MkPVar1" :: "id \<Rightarrow>         'a var" ("$_" [1000] 1000)
no_syntax (input) "_MkPVar2" :: "id \<Rightarrow> type \<Rightarrow> 'a var" ("$_:{_}"  [1000, 0] 1000)
no_syntax (input) "_MkPVar3" :: "id \<Rightarrow> type \<Rightarrow> 'a var" ("$_:{_}-" [1000, 0] 1000)

no_syntax "_MkAxVar1" :: "id \<Rightarrow>         ('a, 'b) lens" ("@_" [1000] 1000)
no_syntax "_MkAxVar2" :: "id \<Rightarrow> type \<Rightarrow> ('a, 'b) lens" ("@_:{_}"  [1000, 0] 1000)
no_syntax "_MkAxVar3" :: "id \<Rightarrow> type \<Rightarrow> ('a, 'b) lens" ("@_:{_}-" [1000, 0] 1000)

no_notation (input) ustate_app_mono ("_\<cdot>_" [1000, 1000] 1000)
no_notation (input) ustate_app_poly ("_\<star>_" [1000, 1000] 1000)

subsubsection {* Forgetting Liftings *}

text {* This can interfere with transfer e.g.~in automatic tactics. *}

lifting_forget Strings.literal.lifting
lifting_forget uvar.var.lifting
lifting_forget ustate.ustate.lifting

subsection {* Variable Constructors *}

definition in_avar :: "'a::injectable var \<Rightarrow> ('a \<Longrightarrow> '\<alpha>::ust \<times> '\<beta>)" where
[simp]: "in_avar x = in_var (avar\<^sub>L x)"

definition out_avar :: "'a::injectable var \<Rightarrow> ('a \<Longrightarrow> '\<alpha> \<times> '\<beta>::ust)" where
[simp]: "out_avar x = out_var (avar\<^sub>L x)"

adhoc_overloading
  ivar in_avar and
  ovar out_avar and
  svar avar_lens

subsection {* Parsing and Pretty-Printing *}

syntax "_check_var" :: "svar \<Rightarrow> logic" ("CHECK'(_')")

translations "_check_var v" \<rightharpoonup> "v"

syntax "_MkAxVar1" :: "id \<Rightarrow>         svid" ("{_}\<^sub>x" [1000] 1000)
syntax "_MkAxVar2" :: "id \<Rightarrow> type \<Rightarrow> svid" ("{_::_}\<^sub>x"  [1000, 0] 1000)
syntax "_MkAxVar3" :: "id \<Rightarrow> type \<Rightarrow> svid" ("{_::_}\<^sub>x-" [1000, 0] 1000)

translations "_MkAxVar1 n"   \<rightleftharpoons> "_MkPVar1 n"
translations "_MkAxVar2 n a" \<rightleftharpoons> "_MkPVar2 n a"
translations "_MkAxVar3 n a" \<rightleftharpoons> "_MkPVar3 n a"

declare [[show_types]]
declare [[show_sorts]]

term "CHECK(${x::nat}\<^sub>x\<acute>)"

declare [[show_types=false]]
declare [[show_sorts=false]]
end