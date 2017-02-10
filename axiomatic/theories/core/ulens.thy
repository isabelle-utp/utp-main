(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: ulens.thy                                                            *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 26 Jan 2017 *)

section {* Variable Lenses *}

theory ulens
imports ustate usort
begin

text {* Perhaps this file should be part of Isabelle/UTP. *}

default_sort type

subsection {* Lens Types *}

type_synonym 'a ulens = "'a \<Longrightarrow> ustate"

subsection {* Constructors *}

definition uvar_lens :: "'a::injectable var \<Rightarrow> 'a ulens" where
"uvar_lens x = \<lparr>lens_get = (\<lambda>s. s\<star>x), lens_put = (\<lambda>s v. s(x := v)\<^sub>s)\<rparr>"

notation uvar_lens ("uvar\<^sub>L")

definition avar_lens :: "'a::injectable var \<Rightarrow> ('a \<Longrightarrow> 'b::ust)" where
"avar_lens x = uvar\<^sub>L x ;\<^sub>L ust\<^sub>L"

notation avar_lens ("avar\<^sub>L")

subsection {* Lens Laws *}

theorem uvar_vwb_lens [simp]:
"vwb_lens (uvar\<^sub>L x)"
apply (unfold_locales)
apply (unfold uvar_lens_def)
apply (simp_all)
-- {* Subgoal 1 *}
apply (transfer)
apply (rule ext)
apply (clarsimp)
apply (metis ProjU_inverse)
done

theorem uvar_indepI [simp, intro]:
fixes x :: "'a::injectable var"
fixes y :: "'b::injectable var"
shows "x\<down> \<noteq> y\<down> \<Longrightarrow> uvar\<^sub>L x \<bowtie> uvar\<^sub>L y"
apply (unfold lens_indep_def uvar_lens_def)
apply (clarsimp)
apply (transfer')
apply (clarsimp)
apply (rule ext)
apply (clarsimp)
done

theorem uvar_indep_iff (*[iff]*):
fixes x :: "'a::{injectable, two} var"
fixes y :: "'b::{injectable, two} var"
shows "uvar\<^sub>L x \<bowtie> uvar\<^sub>L y \<longleftrightarrow> x\<down> \<noteq> y\<down>"
apply (rule iffI)
-- {* Subgoal 1 *}
apply (unfold lens_indep_def) [1]
apply (unfold uvar_lens_def) [1]
apply (clarsimp)
apply (erule contrapos_pp)
apply (clarsimp)
apply (subgoal_tac "\<exists>(a\<^sub>1::'a) (a\<^sub>2::'a). a\<^sub>1 \<noteq> a\<^sub>2")
apply (clarsimp)
apply (subgoal_tac "\<exists>(b\<^sub>1::'b) (b\<^sub>2::'b). b\<^sub>1 \<noteq> b\<^sub>2")
apply (clarsimp)
-- {* Subgoal 1.1 *}
apply (rule_tac x = "\<sigma>\<^sub>0" in exI)
apply (rule_tac x = "if \<sigma>\<^sub>0\<star>y = b\<^sub>1 then b\<^sub>2 else b\<^sub>1" in exI)
apply (rule_tac x = "if \<sigma>\<^sub>0\<star>x = a\<^sub>1 then a\<^sub>2 else a\<^sub>1" in exI)
apply (clarsimp)
apply ((*smt*)metis ustate_upd_poly_app1)
-- {* Subgoal 1.2 *}
apply (rule two_diff)
-- {* Subgoal 1.3 *}
apply (rule two_diff)
-- {* Subgoal 2 *}
apply (erule uvar_indepI)
done

theorem avar_mwb_lens [simp]:
"mwb_lens (avar\<^sub>L x)"
apply (unfold avar_lens_def)
apply (simp add: comp_mwb_lens vwb_lens_ust)
done

theorem avar_indepI [simp, intro]:
fixes x :: "'a::injectable var"
fixes y :: "'b::injectable var"
shows "x\<down> \<noteq> y\<down> \<Longrightarrow> avar\<^sub>L x \<bowtie> avar\<^sub>L y"
apply (unfold avar_lens_def)
apply (simp add: lens_indep_left_comp vwb_lens_ust)
done

theorem avar_indep_iff (*[iff]*):
fixes x :: "'a::{injectable, two} var"
fixes y :: "'b::{injectable, two} var"
shows "avar\<^sub>L x \<bowtie> avar\<^sub>L y \<longleftrightarrow> x\<down> \<noteq> y\<down>"
apply (unfold sym [OF uvar_indep_iff])
apply (unfold avar_lens_def)
apply (simp add: lens_comp_indep_cong vwb_lens_ust)
done

lemma uvar_indep_iff' (*[iff]*):
fixes x :: "'a::{injectable, two} var"
fixes y :: "'a::{injectable, two} var"
shows "uvar\<^sub>L x \<bowtie> uvar\<^sub>L y \<longleftrightarrow> x \<noteq> y"
using Rep_var_inject uvar_indep_iff
apply (blast)
done

lemma avar_indep_iff' (*[iff]*):
fixes x :: "'a::{injectable, two} var"
fixes y :: "'a::{injectable, two} var"
shows "avar\<^sub>L x \<bowtie> avar\<^sub>L y \<longleftrightarrow> x \<noteq> y"
using avar_indep_iff by (auto)

subsection {* Lens Syntax *}

-- {* Syntax is now also configured in @{text utp_avar} within Isabelle/UTP. *}

text {* We use the prefix @{text "@"} for axiomatic (lens) variables. *}

syntax "_MkAxVar1" :: "id \<Rightarrow>         ('a, 'b) lens" ("@_" [1000] 1000)
syntax "_MkAxVar2" :: "id \<Rightarrow> type \<Rightarrow> ('a, 'b) lens" ("@_:{_}"  [1000, 0] 1000)
syntax "_MkAxVar3" :: "id \<Rightarrow> type \<Rightarrow> ('a, 'b) lens" ("@_:{_}-" [1000, 0] 1000)

translations "@n"       \<rightleftharpoons> "avar\<^sub>L $n"
translations "@n:{'a}"  \<rightleftharpoons> "avar\<^sub>L $n:{'a}"
translations "@n:{'a}-" \<rightleftharpoons> "avar\<^sub>L $n:{'a}-"

subsection {* Experiments *}

declare [[show_sorts]]

term "avar\<^sub>L $x"
term "avar\<^sub>L $x:{nat}"
term "avar\<^sub>L $x:{bool}-"

text {* We deal with relational state spaces through lens composition. *}

term "@x:{nat} ;\<^sub>L fst\<^sub>L"
term "@x':{bool} ;\<^sub>L snd\<^sub>L"

declare [[show_sorts=false]]
end