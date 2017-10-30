(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_avar.thy                                                         *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 16 Feb 2017 *)

section {* Axiomatic Variables *}

theory utp_avar
  imports
  "../utp_var"
  "../../axiomatic/Axiomatic"
begin recall_syntax

default_sort type

text {*
  Note that theory @{theory ulens} already includes key definitions and laws
  for defining the required lenses for axiomatic variables. Our concern here
  is merely to integrate them smoothly into Isabelle/UTP.
*}

subsection {* Compatibility with Isabelle/UTP *}

subsubsection {* Late-Inclusion Side-effects *}

text {*
  A problem in Isabelle/HOL is that depending on the order in which imported
  theories are processed, undeclaration of syntax and notations may be lost
  after the inclusion; in particular, if a theory is imported that does not
  depend on the theory that undeclares the respective notation or syntax. We
  use the @{theory TotalRecall} utility and @{command purge_notation} command
  to solve this problem here.
*}

-- {* From @{theory utype}. *}

purge_notation
  Set.member  ("op :") and
  Set.member  ("(_/ : _)" [51, 51] 50)

subsubsection {* Syntactic Adjustments *}

text {*
  We undeclare several notations here to avoid inherent ambiguities with those
  used in Isabelle/UTP. We note that it is sufficient to remove them as input
  notations, namely to be still able to take advantage of them being printed.
*}

purge_notation (input)
  dash ("_\<acute>" [1000] 1000) and
  undash ("_\<inverse>" [1000] 1000) and
  subscr ("_\<^bsub>_\<^esub>" [1000, 0] 1000)

text {* The prefix @{text "uvar."} is important to avoid errors by the tool. *}

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

subsubsection {* Hiding Constants and Types *}

hide_type (open) uvar.uvar

subsubsection {* Forgetting Liftings *}

text {* The liftings below can interfere with the automatic proof tactics. *}

lifting_forget Strings.literal.lifting
lifting_forget uvar.var.lifting
lifting_forget ustate.ustate.lifting

subsection {* Variable Constructors *}

definition in_avar :: "'a::injectable var \<Rightarrow> ('a \<Longrightarrow> '\<alpha>::ust \<times> '\<beta>)" where
[simp]: "in_avar x = in_var (avar_ust\<^sub>L x)"

definition out_avar :: "'a::injectable var \<Rightarrow> ('a \<Longrightarrow> '\<alpha> \<times> '\<beta>::ust)" where
[simp]: "out_avar x = out_var (avar_ust\<^sub>L x)"

adhoc_overloading
  ivar in_avar and
  ovar out_avar and
  svar avar_lens

subsection {* Variable Syntax *}

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