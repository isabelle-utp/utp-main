(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: ulens.thy                                                            *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 14 Feb 2017 *)

section \<open> Axiomatic Lenses \<close>

theory ulens
imports ustate ustore
begin

text \<open> This is a source of ambiguity in the presence of structure variables. \<close>

no_notation subscr ("_\<^bsub>_\<^esub>" [1000] 1000)

default_sort type

subsection \<open> Lens Types \<close>

type_synonym 'a ulens = "'a \<Longrightarrow> ustate"

subsection \<open> Constructors \<close>

definition avar_lens :: "'a::injectable var \<Rightarrow> 'a ulens" where
"avar_lens v = \<lparr>lens_get = (\<lambda>s. s\<star>v), lens_put = (\<lambda>s x. s(v := x)\<^sub>s)\<rparr>"

notation avar_lens ("avar\<^sub>L")

definition avar_ust_lens :: "'a::injectable var \<Rightarrow> ('a \<Longrightarrow> 'b::ust)" where
"avar_ust_lens v = avar\<^sub>L v ;\<^sub>L ust\<^sub>L"

notation avar_ust_lens ("avar'_ust\<^sub>L")

subsection \<open> Lens Laws \<close>

theorem avar_vwb_lens [simp]:
"vwb_lens (avar\<^sub>L v)"
apply (unfold_locales)
apply (unfold avar_lens_def)
apply (simp_all)
\<comment> \<open> Subgoal 1 \<close>
apply (transfer)
apply (rule ext)
apply (clarsimp)
apply (metis ProjU_inverse)
done

theorem avar_ust_vwb_lens [simp]:
"vwb_lens (avar_ust\<^sub>L v)"
apply (unfold avar_ust_lens_def)
apply (simp add: comp_vwb_lens)
done

theorem avar_indepI [simp]:
fixes x :: "'a::injectable var"
fixes y :: "'b::injectable var"
shows "v\<down> \<noteq> w\<down> \<Longrightarrow> avar\<^sub>L v \<bowtie> avar\<^sub>L w"
apply (unfold lens_indep_def avar_lens_def)
apply (clarsimp)
apply (transfer')
apply (clarsimp)
apply (rule ext)
apply (clarsimp)
done

theorem avar_indep_iff [iff]:
fixes v :: "'a::{injectable, two} var"
fixes w :: "'b::{injectable, two} var"
shows "avar\<^sub>L v \<bowtie> avar\<^sub>L w \<longleftrightarrow> v\<down> \<noteq> w\<down>"
apply (rule iffI)
\<comment> \<open> Subgoal 1 \<close>
apply (unfold lens_indep_def) [1]
apply (unfold avar_lens_def) [1]
apply (clarsimp)
apply (erule contrapos_pp)
apply (clarsimp)
apply (subgoal_tac "\<exists>(a\<^sub>1::'a) (a\<^sub>2::'a). a\<^sub>1 \<noteq> a\<^sub>2")
prefer 2 apply (rule two_diff)
apply (subgoal_tac "\<exists>(b\<^sub>1::'b) (b\<^sub>2::'b). b\<^sub>1 \<noteq> b\<^sub>2")
prefer 2 apply (rule two_diff)
apply (clarsimp)
apply (rule_tac x = "\<sigma>\<^sub>0" in exI)
apply (rule_tac x = "if \<sigma>\<^sub>0\<star>w = b\<^sub>1 then b\<^sub>2 else b\<^sub>1" in exI)
apply (rule_tac x = "if \<sigma>\<^sub>0\<star>v = a\<^sub>1 then a\<^sub>2 else a\<^sub>1" in exI)
apply (clarsimp)
apply ((*smt*)metis ustate_upd_poly_app1)
\<comment> \<open> Subgoal 2 \<close>
apply (erule avar_indepI)
done

theorem avar_ust_indepI [simp]:
fixes v :: "'a::injectable var"
fixes w :: "'b::injectable var"
shows "v\<down> \<noteq> w\<down> \<Longrightarrow> avar_ust\<^sub>L v \<bowtie> avar_ust\<^sub>L w"
apply (unfold avar_ust_lens_def)
apply (simp)
done

theorem avar_ust_indep_iff [iff]:
fixes v :: "'a::{injectable, two} var"
fixes w :: "'b::{injectable, two} var"
shows "avar_ust\<^sub>L v \<bowtie> avar_ust\<^sub>L w \<longleftrightarrow> v\<down> \<noteq> w\<down>"
apply (unfold sym [OF avar_indep_iff])
apply (unfold avar_ust_lens_def)
apply (simp add: lens_comp_indep_cong)
done

lemma avar_indep_iff' (*[iff]*):
fixes x :: "'a::{injectable, two} var"
fixes y :: "'a::{injectable, two} var"
shows "avar\<^sub>L x \<bowtie> avar\<^sub>L y \<longleftrightarrow> x \<noteq> y"
using Rep_var_inject avar_indep_iff
apply (blast)
done

lemma avar_ustindep_iff' (*[iff]*):
fixes x :: "'a::{injectable, two} var"
fixes y :: "'a::{injectable, two} var"
shows "avar_ust\<^sub>L x \<bowtie> avar_ust\<^sub>L y \<longleftrightarrow> x \<noteq> y"
using avar_ust_indep_iff by (auto)

subsection \<open> Lens Syntax \<close>

\<comment> \<open> Syntax is now also configured in @{text utp_avar} within Isabelle/UTP. \<close>

text \<open> We use the prefix @{text "@"} for axiomatic (lens) variables. \<close>

syntax "_MkAxVar1" :: "id \<Rightarrow>         ('a, 'b) lens" ("@_" [1000] 1000)
syntax "_MkAxVar2" :: "id \<Rightarrow> type \<Rightarrow> ('a, 'b) lens" ("@_:{_}"  [1000, 0] 1000)
syntax "_MkAxVar3" :: "id \<Rightarrow> type \<Rightarrow> ('a, 'b) lens" ("@_:{_}-" [1000, 0] 1000)

translations "@n"       \<rightleftharpoons> "avar_ust\<^sub>L $n"
translations "@n:{'a}"  \<rightleftharpoons> "avar_ust\<^sub>L $n:{'a}"
translations "@n:{'a}-" \<rightleftharpoons> "avar_ust\<^sub>L $n:{'a}-"

subsection \<open> Experiments \<close>

declare [[show_sorts]]

term "avar_ust\<^sub>L $x"
term "avar_ust\<^sub>L $x:{nat}"
term "avar_ust\<^sub>L $x:{bool}-"

text \<open> We deal with relational state spaces through lens composition. \<close>

term "@x:{nat} ;\<^sub>L fst\<^sub>L"
term "@x':{bool} ;\<^sub>L snd\<^sub>L"

declare [[show_sorts=false]]
end