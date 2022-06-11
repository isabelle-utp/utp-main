(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: ulift.thy                                                            *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Predicate Lifting\<close>

theory ulift
imports upred unrest
keywords "declare_uvar" :: thy_decl
begin

text \<open>A parser that lifts HOL predicates into @{type upred} objects.\<close>

subsection \<open>Tool Options\<close>

text \<open>Option that enables implicit typing in lifted predicates.\<close>

ML \<open>
  val (ulift_typing, ulift_typing_setup) =
    Attrib.config_bool @{binding ulift_typing} (K true);
\<close>

setup ulift_typing_setup

text \<open>Option that disables the pretty-printer to facilitate debugging.\<close>

ML \<open>
  val (disable_ulift_pp, disable_ulift_pp_setup) =
    Attrib.config_bool @{binding disable_ulift_pp} (K false);
\<close>

setup disable_ulift_pp_setup

subsection \<open>Lifting Operator\<close>

lift_definition LiftP :: "(ustate \<Rightarrow> bool) \<Rightarrow> upred"
is "\<lambda>f::ustate \<Rightarrow> bool. {b .f b}"
done

(* declare ustate_app_poly_def [evalp] *)

subsection \<open>Lifting Syntax\<close>

text \<open>We define a constant to tag terms to be processed by the parser.\<close>

consts ulift :: "bool \<Rightarrow> upred" ("'(_')\<^sub>p")

text \<open>The following allows us to protect inner terms from processing.\<close>

consts uprotect :: "'a \<Rightarrow> 'a" ("@'(_')")

subsection \<open>Parser and Printer\<close>

ML_file "ulift.ML"

setup \<open>
  Context.theory_map (
    (Syntax_Phases.term_check 2 "ulift parser" Ulift_Parser.ulift_tr) o
    (Syntax_Phases.term_uncheck 2 "ulift printer" Ulift_Printer.ulift_tr'))
\<close>

subsection \<open>Implicit Typing\<close>

parse_translation \<open>
  [(@{const_syntax "ulift"}, Ulift_Typing.implicit_typing)]
\<close>

text \<open>The following configures a command to declare an auxiliary variable.\<close>

ML \<open>
  Outer_Syntax.local_theory @{command_keyword "declare_uvar"} "declare uvar"
    (Parse.const_decl >>
      (fn (uvar, typ, _) => Ulift_Typing.mk_uvar_type_synonym uvar typ));
\<close>

subsection \<open>Proof Support\<close>

theorem EvalP_LiftP [evalp]:
"\<lbrakk>LiftP f\<rbrakk>b = (f b)"
apply (transfer)
apply (simp)
done

subsection \<open>Theorems\<close>

paragraph \<open>Unrestriction of Lifting\<close>

theorem LiftP_unrest_zero:
"vs \<sharp> (LiftP (\<lambda>b. P0))"
apply (transfer)
apply (simp)
done

theorem LiftP_unrest:
"vs \<inter> {v} = {} \<Longrightarrow>
 vs \<sharp> (LiftP (\<lambda>b. P1 b\<cdot>v))"
"vs \<inter> {v1, v2} = {} \<Longrightarrow>
 vs \<sharp> (LiftP (\<lambda>b. P2 b\<cdot>v1 b\<cdot>v2))"
"vs \<inter> {v1, v2, v3} = {} \<Longrightarrow>
 vs \<sharp> (LiftP (\<lambda>b. P3 b\<cdot>v1 b\<cdot>v2 b\<cdot>v3))"
"vs \<inter> {v1, v2, v3, v4} = {} \<Longrightarrow>
 vs \<sharp> (LiftP (\<lambda>b. P4 b\<cdot>v1 b\<cdot>v2 b\<cdot>v3 b\<cdot>v4))"
"vs \<inter> {v1, v2, v3, v4, v5} = {} \<Longrightarrow>
 vs \<sharp> (LiftP (\<lambda>b. P5 b\<cdot>v1 b\<cdot>v2 b\<cdot>v3 b\<cdot>v4 b\<cdot>v5))"
"vs \<inter> {v1, v2, v3, v4, v5, v6} = {} \<Longrightarrow>
 vs \<sharp> (LiftP (\<lambda>b. P6 b\<cdot>v1 b\<cdot>v2 b\<cdot>v3 b\<cdot>v4 b\<cdot>v5 b\<cdot>v6))"
"vs \<inter> {v1, v2, v3, v4, v5, v6, v7} = {} \<Longrightarrow>
 vs \<sharp> (LiftP (\<lambda>b. P7 b\<cdot>v1 b\<cdot>v2 b\<cdot>v3 b\<cdot>v4 b\<cdot>v5 b\<cdot>v6 b\<cdot>v7))"
"vs \<inter> {v1, v2, v3, v4, v5, v6, v7, v8} = {} \<Longrightarrow>
 vs \<sharp> (LiftP (\<lambda>b. P8 b\<cdot>v1 b\<cdot>v2 b\<cdot>v3 b\<cdot>v4 b\<cdot>v5 b\<cdot>v6 b\<cdot>v7 b\<cdot>v8))"
apply (transfer', clarsimp, transfer', simp)+
done

theorem "{$z\<down>} \<sharp> (x = y + (1::nat))\<^sub>p"
apply (unfold ustate_app_poly_def)
apply (rule LiftP_unrest)
apply (code_simp)
done

theorem "{$x\<down>} \<sharp> (x = y + (1::nat))\<^sub>p"
apply (unfold ustate_app_poly_def)
apply (rule LiftP_unrest)
apply (code_simp)
oops

subsection \<open>Experiments\<close>

text \<open>Types propagate through predicate connectives.\<close>

theorem "taut (x = y + 1)\<^sub>p \<and>\<^sub>p (y = 2)\<^sub>p \<Rightarrow>\<^sub>p (x = (3::nat))\<^sub>p"
apply (unfold evalp)
apply (clarify)
apply (simp)
done

text \<open>HOL quantifies can be used in lifted predicates too.\<close>

theorem "taut (\<exists> y . x = y + 1)\<^sub>p \<Rightarrow>\<^sub>p (x > (0::nat))\<^sub>p"
apply (unfold evalp simp_thms)
apply (clarify)
apply (simp)
done

text \<open>Note that the following holds for arbitrary HOL sets!\<close>

inject_type set

theorem "taut (x < 3)\<^sub>p \<and>\<^sub>p (s = {0::nat, 1, 2})\<^sub>p \<Rightarrow>\<^sub>p (x \<in> s)\<^sub>p"
apply (unfold evalp)
apply (safe)
apply (clarsimp)
done

text \<open>Lifting implies that HOL connectives are naturally supported.\<close>

theorem "taut (x < 3 \<and> s = {0, 1, 2::nat} \<longrightarrow> x \<in> s)\<^sub>p"
apply (unfold evalp)
apply (safe)
apply (clarsimp)
done
end