(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: ucommon.thy                                                          *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jan 2022 *)

section \<open>Common Definitions\<close>

theory ucommon
imports uimports document
  "core/uattrib"
  "utils/flat_orders"
(* "utils/Interpret" *)
  "utils/Normalise"
  "utils/Sum_Order"
  "utils/Transfer_Plus"
  "utils/Typedef_extra"
(* "utils/Typedep" *)
  "utils/Typerep_ind"
(* Provided by UTP-Toolkit *)
  "Optics.Lenses"
  "Z_Toolkit.Infinity"
begin

text \<open>ML Utility Functions\<close>

ML_file "utils/Pure_Utils.ML"

subsection \<open>Configuration\<close>

default_sort type

declare [[ML_print_depth = 100]]

text \<open>The following prevents the simplifier from splitting pairs by default.\<close>

declare split_paired_All [simp del]
declare split_paired_Ex [simp del]

setup \<open>map_theory_claset (fn ctx => ctx delSWrapper "split_all_tac")\<close>

subsection \<open>Notation and Syntax\<close>

text \<open>We are going to use the colon for model typing.\<close>

no_notation (ASCII)
  Set.member  ("'(:')") and
  Set.member  ("(_/ : _)" [51, 51] 50)

text \<open>We are going to use the floor brackets for names.\<close>

no_notation floor ("\<lfloor>_\<rfloor>")

text \<open>We are going to use the converse symbol for undashing.\<close>

no_notation
  converse  ("(_\<inverse>)" [1000] 999)

subsection \<open>Types from Terms\<close>

text \<open>
  The following function constructs an element of type (@{typ "'a itself"})
  from a term of type @{typ "'a"}. It mirrors the @{term "TYPE('a)"} syntax
  albeit applying to a term rather than a type. For example, we can write
  @{text "TYPE_TERM(1::nat)"} with the same meaning as @{term "TYPE(nat)"}.
\<close>

definition type_of_term :: "'a \<Rightarrow> 'a itself" where
"type_of_term (x::'a) = TYPE('a)"

notation type_of_term ("TERM'_TYPE'(_')")

subsection \<open>Uncurrying\<close>

text \<open>Isabelle provides a currying operator but none for uncurrying.\<close>

definition uncurry :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b \<Rightarrow> 'c)" where
"uncurry = (\<lambda>f p. f (fst p) (snd p))"

lemma uncurry_app [simp]:
"uncurry f (x, y) = f x y"
apply (simp add: uncurry_def)
done

theorem uncurry_inverse [simp]:
"curry (uncurry f) = f"
apply (fastforce)
done

theorem curry_inverse [simp]:
"uncurry (curry f) = f"
apply (metis case_prod_curry uncurry_inverse)
done

subsection \<open>Function Override\<close>

text \<open>We first introduce a neater syntax for function override.\<close>

notation override_on ("_ \<oplus> _ on _" [56, 56, 51] 55)

paragraph \<open>Override Tactic\<close>

method override_on_tac =
  (unfold override_on_def fun_eq_iff, auto) [1]

paragraph \<open>Override Theorems\<close>

text_raw \<open>\label{sec:override_laws}\<close>

lemma override_on_eq:
"f\<^sub>1 \<oplus> g\<^sub>1 on a\<^sub>1 = f\<^sub>2 \<oplus> g\<^sub>2 on a\<^sub>2 \<longleftrightarrow>
 (\<forall>x. x \<notin> a\<^sub>1 \<and> x \<notin> a\<^sub>2 \<longrightarrow> f\<^sub>1 x = f\<^sub>2 x) \<and>
 (\<forall>x. x \<notin> a\<^sub>1 \<and> x \<in> a\<^sub>2 \<longrightarrow> f\<^sub>1 x = g\<^sub>2 x) \<and>
 (\<forall>x. x \<in> a\<^sub>1 \<and> x \<notin> a\<^sub>2 \<longrightarrow> g\<^sub>1 x = f\<^sub>2 x) \<and>
 (\<forall>x. x \<in> a\<^sub>1 \<and> x \<in> a\<^sub>2 \<longrightarrow> g\<^sub>1 x = g\<^sub>2 x)"
apply (override_on_tac)
done

text \<open>
  A similar theorem @{thm [source] override_on_emptyset} is already a default
  simplification.
\<close>

theorem override_on_empty (*[simp]*):
"f \<oplus> g on {} = f"
apply (rule ext)
apply (simp)
done

theorem override_on_UNIV [simp]:
"f \<oplus> g on UNIV = g"
apply (rule ext)
apply (simp)
done

theorem override_on_idem [simp]:
"f \<oplus> f on a = f"
apply (rule ext)
apply (case_tac "x \<in> a")
apply (simp_all)
done

theorem override_on_comm:
"(f \<oplus> g on a) = (g \<oplus> f on -a)"
apply (rule ext)
apply (case_tac "x \<in> a")
apply (simp_all)
done

theorem override_on_assoc:
"(f \<oplus> g on a) \<oplus> h on b = f \<oplus> (g \<oplus> h on b) on (a \<union> b)"
apply (rule ext)
apply (case_tac "x \<in> a"; case_tac "x \<in> b")
apply (simp_all)
done

theorem override_on_cancel [simp]:
"f \<oplus> (g \<oplus> h on a) on a = f \<oplus> h on a"
"(f \<oplus> g on a) \<oplus> h on a = f \<oplus> h on a"
"f \<oplus> (f \<oplus> g on a) on b = f \<oplus> g on a \<inter> b"
"(f \<oplus> g on a) \<oplus> g on b = f \<oplus> g on a \<union> b"
"f \<oplus> (g \<oplus> f on b) on a = f \<oplus> g on a - b"
"(f \<oplus> g on a) \<oplus> f on b = f \<oplus> g on a - b"
apply (rule ext;
  case_tac "x \<in> a";
  case_tac "x \<in> b"; simp)+
done

theorem override_on_singleton [simp]:
"f \<oplus> g on {x} = f(x := g x)"
apply (rule ext)
apply (simp)
done

theorem override_on_reorder:
"a \<inter> b = {} \<Longrightarrow>
 (f \<oplus> g on a) \<oplus> h on b = (f \<oplus> h on b) \<oplus> g on a"
apply (rule ext)
apply (case_tac "x \<in> a"; case_tac "x \<in> b")
apply (simp_all)
apply (auto)
done

subsection \<open>Involutions\<close>

locale invol =
  fixes f :: "'a \<Rightarrow> 'a"
  assumes invol_f: "f o f = id"
begin
lemma invol_app [simp]:
"f (f x) = x"
apply (insert invol_f)
apply (erule pointfree_idE)
done

lemma invol_inj [simp]:
"inj f"
apply (rule injI)
apply (metis invol_app)
done

lemma invol_surj [simp]:
"surj f"
apply (rule surjI)
apply (rule invol_app)
done

lemma invol_bij [simp]:
"bij f"
apply (rule bijI)
apply (rule invol_inj)
apply (rule invol_surj)
done
end

subsection \<open>Generic Transfer\<close>

theorem inj_on_transfer_eq:
"inj_on f S \<Longrightarrow>
 \<lbrakk>x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> x = y \<longleftrightarrow> f x = f y"
apply (simp add: inj_on_def)
apply (auto)
done

theorem inj_on_transfer_eqI:
"inj_on f S \<Longrightarrow>
 \<lbrakk>x \<in> S; y \<in> S; f x = f y\<rbrakk> \<Longrightarrow> x = y"
apply (simp add: inj_on_transfer_eq)
done

subsection \<open>Miscellaneous\<close>

lemmas asmE = rev_mp
end