(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: upred.thy                                                            *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Core Predicates\<close>

theory upred
imports ustate
begin

text \<open>This theory needs rework for integration with @{text uexpr}.\<close>

subsection \<open>Predicate Type\<close>

typedef upred = "UNIV :: ustate set set"
apply (rule UNIV_witness)
done

notation Rep_upred ("\<beta>")

setup_lifting type_definition_upred

subsection \<open>Literal Predicates\<close>

lift_definition TrueP :: "upred"
is "UNIV"
done

notation TrueP ("true\<^sub>p")

lift_definition FalseP :: "upred"
is "{}"
done

notation FalseP ("false\<^sub>p")

subsection \<open>Logical Connectives\<close>

lift_definition NotP :: "upred \<Rightarrow> upred"
is "uminus"
done

notation NotP ("\<not>\<^sub>p _" [190] 190)

lift_definition AndP :: "upred \<Rightarrow> upred \<Rightarrow> upred"
is "(\<inter>)"
done

notation AndP (infixr "\<and>\<^sub>p" 180)

lift_definition OrP :: "upred \<Rightarrow> upred \<Rightarrow> upred"
is "(\<union>)"
done

notation OrP (infixr "\<or>\<^sub>p" 170)

definition ImpliesP :: "upred \<Rightarrow> upred \<Rightarrow> upred" where
"ImpliesP p1 p2 = \<not>\<^sub>p p1 \<or>\<^sub>p p2"

notation ImpliesP (infixr "\<Rightarrow>\<^sub>p" 160)

definition IffP :: "upred \<Rightarrow> upred \<Rightarrow> upred" where
"IffP p1 p2 = (p1 \<Rightarrow>\<^sub>p p2) \<and>\<^sub>p (p2 \<Rightarrow>\<^sub>p p1)"

notation IffP (infixr "\<Leftrightarrow>\<^sub>p" 150)

syntax "_RevIffP" :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<Leftarrow>\<^sub>p" 160)

translations "p1 \<Leftarrow>\<^sub>p p2" \<rightharpoonup> "p2 \<Rightarrow>\<^sub>p p1"

subsection \<open>Quantifiers\<close>

lift_definition ExistsP :: "uvar set \<Rightarrow> upred \<Rightarrow> upred" is
"\<lambda>vs p. {b1 \<oplus>\<^sub>s b2 on vs| b1 b2. b1 \<in> p}"
done

notation ExistsP ("(\<exists>\<^sub>p _./ _)" [0, 100] 100)

definition ForallP :: "uvar set \<Rightarrow> upred \<Rightarrow> upred" where
"ForallP vs p = \<not>\<^sub>p (\<exists>\<^sub>p vs. \<not>\<^sub>p p)"

notation ForallP ("(\<forall>\<^sub>p _./ _)" [0, 100] 100)

definition ClosureP :: "upred \<Rightarrow> upred" where
"ClosureP p = \<forall>\<^sub>p UVAR. p"

notation ClosureP ("[_]\<^sub>p")

subsection \<open>Meta-logical Operators\<close>

definition TautP :: "upred \<Rightarrow> bool" ("taut _" 10) where
"(taut p) = (p = true\<^sub>p)"

definition ContraP :: "upred \<Rightarrow> bool" ("contra _" 10) where
"(contra p) = (p = false\<^sub>p)"

definition RefineP :: "upred \<Rightarrow> upred \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
"p1 \<sqsubseteq> p2 = (taut p1 \<Leftarrow>\<^sub>p p2)"

text \<open>\fixme{I am slightly unsure about the coercion below.}\<close>

declare [[coercion TautP]]

subsection \<open>Proof Support\<close>

named_theorems evalp "evalp theorems"

method upred_tac = (unfold evalp, (auto)?)

text \<open>Evaluation Function\<close>

lift_definition EvalP :: "upred \<Rightarrow> ustate \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>_" [0, 1000] 51)
is "\<lambda> (p::ustate set) b. b \<in> p"
done

text \<open>Interpretation Laws\<close>

theorem EvalP_eq [evalp]:
"p1 = p2 \<longleftrightarrow> (\<forall>b. \<lbrakk>p1\<rbrakk>b \<longleftrightarrow> \<lbrakk>p2\<rbrakk>b)"
apply (transfer)
apply (auto)
done

theorem EvalP_eqI:
"(\<And>b. \<lbrakk>p1\<rbrakk>b \<longleftrightarrow> \<lbrakk>p2\<rbrakk>b) \<Longrightarrow> p1 = p2"
apply (transfer)
apply (auto)
done

theorem EvalP_TrueP [evalp]:
"\<lbrakk>true\<^sub>p\<rbrakk>b = True"
apply (transfer)
apply (simp)
done

theorem EvalP_FalseP [evalp]:
"\<lbrakk>false\<^sub>p\<rbrakk>b = False"
apply (transfer)
apply (simp)
done

theorem EvalP_NotP [evalp]:
"\<lbrakk>\<not>\<^sub>p p\<rbrakk>b = (\<not>\<lbrakk>p\<rbrakk>b)"
apply (transfer)
apply (simp)
done

theorem EvalP_AndP [evalp]:
"\<lbrakk>p1 \<and>\<^sub>p p2\<rbrakk>b = (\<lbrakk>p1\<rbrakk>b \<and> \<lbrakk>p2\<rbrakk>b)"
apply (transfer)
apply (simp)
done

theorem EvalP_OrP [evalp]:
"\<lbrakk>p1 \<or>\<^sub>p p2\<rbrakk>b = (\<lbrakk>p1\<rbrakk>b \<or> \<lbrakk>p2\<rbrakk>b)"
apply (transfer)
apply (simp)
done

theorem EvalP_ImpliesP [evalp]:
"\<lbrakk>p1 \<Rightarrow>\<^sub>p p2\<rbrakk>b = (\<lbrakk>p1\<rbrakk>b \<longrightarrow> \<lbrakk>p2\<rbrakk>b)"
apply (unfold ImpliesP_def)
apply (auto simp: evalp)
done

theorem EvalP_IffP [evalp]:
"\<lbrakk>p1 \<Leftrightarrow>\<^sub>p p2\<rbrakk>b = (\<lbrakk>p1\<rbrakk>b \<longleftrightarrow> \<lbrakk>p2\<rbrakk>b)"
apply (unfold IffP_def)
apply (auto simp: evalp)
done

theorem EvalP_ExistsP [evalp]:
"\<lbrakk>\<exists>\<^sub>p vs. p\<rbrakk>b = (\<exists>b'. \<lbrakk>p\<rbrakk>(b \<oplus>\<^sub>s b' on vs))"
apply (transfer')
apply (clarsimp)
apply (safe, simp)
\<comment> \<open>Subgoal 1\<close>
apply (rule_tac x = "b1" in exI)
apply (simp)
\<comment> \<open>Subgoal 2\<close>
apply (rule_tac x = "b \<oplus>\<^sub>s b' on vs" in exI)
apply (simp)
apply (rule_tac x = "b" in exI)
apply (simp)
done

theorem EvalP_ForallP [evalp]:
"\<lbrakk>\<forall>\<^sub>p vs . p\<rbrakk>b = (\<forall>b'. \<lbrakk>p\<rbrakk>(b \<oplus>\<^sub>s b' on vs))"
apply (unfold ForallP_def)
apply (auto simp: evalp)
done

theorem EvalP_ClosureP [evalp]:
"\<lbrakk>[p]\<^sub>p\<rbrakk>b = (\<forall>b. \<lbrakk>p\<rbrakk>b)"
apply (unfold ClosureP_def)
apply (auto simp: evalp)
done

declare TautP_def [evalp]
declare ContraP_def [evalp]
declare RefineP_def [evalp]
end