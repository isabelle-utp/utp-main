(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: ustate.thy                                                           *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Universal State\<close>

theory ustate
imports utype uval uvar
begin

text \<open>
  In this theory, we define a notion of state space (binding) for universal
  values. This is through a new type @{text uspace}. We consider states as
  total bindings so that there is no notion of frame and all variables are
  assigned a value. An important property of state bindings is that they are
  well-typed by construction; this is the main reason why we need the axiom
  @{thm [source] utypes_non_empty} in our @{text axiomatization}.
\<close>

no_notation
  converse  ("(_\<inverse>)" [1000] 999)

default_sort injectable

subsection \<open>State Type\<close>

text \<open>
  As before, total functions are used to encode states. This is possible due
  to the axiom @{thm [source] utypes_non_empty} which enforces non-emptiness
  of all model types, irrespective of them being injectable into @{type uval}
  or not. It guarantees the existence of a well-typed binding and this here is
  needed to discharge the non-emptiness assumption of the type definition.
\<close>

typedef ustate = "{b::uvar \<Rightarrow> uval. \<forall>v. (b v) :\<^sub>u (type v)}"
apply (rule_tac x = "\<lambda>v. some_uval (type v)" in exI)
apply (clarsimp)
apply (rule some_uval_typed)
done

text \<open>\fixme{Is there a way to fix the warning about relators below?}\<close>

setup_lifting type_definition_ustate

subsection \<open>Constants\<close>

subsubsection \<open>Some State\<close>

text \<open>Constant that yields some arbitrary (albeit well-typed) state.\<close>

lift_definition some_ustate :: "ustate" ("\<sigma>\<^sub>0")
is "\<lambda>v. some_uval (type v)"
apply (rule some_uval_typed)
done

subsection \<open>Operators\<close>

text \<open>
  The operators we introduce are application, state updated, state override,
  and congruence. For application and update, we provide both a monomorphic
  and polymorphic versions of the operator. Strictly, state update could be
  expressed in terms of override with a singleton binding i.e.~if we added a
  construct to create such bindings.
\<close>

subsubsection \<open>Application\<close>

text \<open>Both a monomorphic and polymorphic version is provided.\<close>

lift_definition ustate_app_mono :: "ustate \<Rightarrow> uvar \<Rightarrow> uval"
is "\<lambda>s v. s v"
done

notation ustate_app_mono ("_\<cdot>_" [1000, 1000] 1000)

definition ustate_app_poly :: "ustate \<Rightarrow> 'a var \<Rightarrow> 'a" where
[transfer_unfold]: "ustate_app_poly s v = ProjU s\<cdot>(v\<down>)"

notation ustate_app_poly ("_\<star>_" [1000, 1000] 1000)

subsubsection \<open>State Update\<close>

text \<open>Both a monomorphic and polymorphic version is provided.\<close>

lift_definition ustate_upd_mono :: "ustate \<Rightarrow> uvar \<Rightarrow> uval \<Rightarrow> ustate"
is "\<lambda>s v x. if x :\<^sub>u (type v) then s(v := x) else s"
apply (transfer')
apply (simp add: typing)
done

definition ustate_upd_poly :: "ustate \<Rightarrow>  'a var \<Rightarrow> 'a \<Rightarrow> ustate" where
[transfer_unfold]: "ustate_upd_poly s v x = ustate_upd_mono s v\<down> (InjU x)"

text \<open>Syntax for State Update\<close>

nonterminal ubinds and ubind

text \<open>The below is inspired by Isabelle's syntax for function update.\<close>

syntax
  "_ubind_mono" :: "uvar \<Rightarrow> uval \<Rightarrow> ubind"      ("(2_ :=\<^sub>u/ _)")
  "_ubind_poly" :: "'a var \<Rightarrow> 'a \<Rightarrow> ubind"      ("(2_ :=/ _)")
  ""            :: "ubind \<Rightarrow> ubinds"            ("_")
  "_ubinds"     :: "ubind \<Rightarrow> ubinds \<Rightarrow> ubinds"  ("_,/ _")
  "_update"     :: "ustate \<Rightarrow> ubinds \<Rightarrow> ustate" ("_/'((_)')\<^sub>s" [1000, 0] 1000)

translations
  "_update s (_ubinds b bs)" \<rightleftharpoons> "_update (_update s b) bs"
  "_update s (_ubind_mono x y)" \<rightleftharpoons> "(CONST ustate_upd_mono) s x y"
  "_update s (_ubind_poly x y)" \<rightleftharpoons> "(CONST ustate_upd_poly) s x y"

subsubsection \<open>Override\<close>

lift_definition ustate_override :: "ustate \<Rightarrow> ustate \<Rightarrow> uvar set \<Rightarrow> ustate"
is "override_on"
apply (rename_tac s\<^sub>1 s\<^sub>2 vs v)
apply (case_tac "v \<in> vs")
apply (simp_all)
done

notation ustate_override ("_ \<oplus>\<^sub>s _ on _" [55, 56, 56] 55)

subsubsection \<open>Congruence\<close>

text \<open>Two states are congruent if they agree over a given set of variables.\<close>

lift_definition ustate_cong_on :: "ustate \<Rightarrow> ustate \<Rightarrow> uvar set \<Rightarrow> bool"
is "\<lambda>b1 b2 vs. \<forall>v\<in>vs. (b1 v) = (b2 v)"
done

notation ustate_cong_on ("_ \<cong>\<^sub>b _ on _" [51, 51, 0] 50)

subsection \<open>Theorems\<close>

theorem ustate_eq:
"b1 = b2 \<longleftrightarrow> (\<forall>v. b1\<cdot>v = b2\<cdot>v)"
apply (transfer')
apply (fold fun_eq_iff)
apply (rule refl)
done

theorem ustate_eqI [rule_format]:
"(\<forall>v. b1\<cdot>v = b2\<cdot>v) \<Longrightarrow> b1 = b2"
apply (subst ustate_eq)
apply (assumption)
done

paragraph \<open>Application Laws\<close>

theorem ustate_upd_mono_app [simp]:
"x :\<^sub>u (type v) \<Longrightarrow> s(v :=\<^sub>u x)\<^sub>s\<cdot>w = (if v = w then x else s\<cdot>w)"
apply (transfer')
apply (clarsimp)
done

theorem ustate_upd_poly_app1 [simp]:
"s(v := x)\<^sub>s\<star>w = (if v = w then x else s\<star>w)"
apply (unfold ustate_app_poly_def)
apply (unfold ustate_upd_poly_def)
apply (clarsimp)
done

text \<open>
  Note that the following theorem is not subsumed by the one above. This is
  because the types of the polymorphic types of the variables @{text v} and
  @{text w} may be different whereas above the have to be the same.
\<close>

theorem ustate_upd_poly_app2 [simp]:
"v\<down> \<noteq> w\<down> \<Longrightarrow> s(v := x)\<^sub>s\<star>w = s\<star>w"
apply (unfold ustate_app_poly_def)
apply (unfold ustate_upd_poly_def)
apply (clarsimp)+
done

lemma ustate_upd_mono_override [simp]:
"v = w \<Longrightarrow> y :\<^sub>u (type w) \<Longrightarrow> \<sigma>(v :=\<^sub>u x, w :=\<^sub>u y)\<^sub>s = \<sigma>(w :=\<^sub>u y)\<^sub>s"
apply (transfer)
apply (rule ext)
apply (clarsimp)
done

lemma ustate_upd_poly_override [simp]:
"v\<down> = w\<down> \<Longrightarrow> \<sigma>(v := x, w := y)\<^sub>s = \<sigma>(w := y)\<^sub>s"
apply (transfer)
apply (rule ext)
apply (clarsimp)
apply (simp add: p_type_rel_def)
done

theorem ustate_override_mono_app [simp]:
"(s\<^sub>1 \<oplus>\<^sub>s s\<^sub>2 on vs)\<cdot>v = (if v \<in> vs then s\<^sub>2\<cdot>v else s\<^sub>1\<cdot>v)"
apply (transfer')
apply (clarsimp)
done

theorem ustate_override_poly_app [simp]:
"(s\<^sub>1 \<oplus>\<^sub>s s\<^sub>2 on vs)\<star>v = (if v\<down> \<in> vs then s\<^sub>2\<star>v else s\<^sub>1\<star>v)"
apply (transfer')
apply (clarsimp)
done

paragraph \<open>Override Laws\<close>

text \<open>
  Many of the theorems here mirror those for @{term "f \<oplus> g on a"} in theory
  @{text ucommon} (see Section \ref{sec:override_laws}).
\<close>

theorem ustate_override_empty [simp]:
"s\<^sub>1 \<oplus>\<^sub>s s\<^sub>2 on {} = s\<^sub>1"
apply (transfer')
apply (rule override_on_empty)
done

theorem ustate_override_UVAR [simp]:
"s\<^sub>1 \<oplus>\<^sub>s s\<^sub>2 on UVAR = s\<^sub>2"
apply (transfer')
apply (rule override_on_UNIV)
done

theorem ustate_override_idem [simp]:
"s \<oplus>\<^sub>s s on vs = s"
apply (transfer')
apply (rule override_on_idem)
done

theorem ustate_override_comm:
"(s\<^sub>1 \<oplus>\<^sub>s s\<^sub>2 on vs) = (s\<^sub>2 \<oplus>\<^sub>s s\<^sub>1 on -vs)"
apply (transfer')
apply (rule override_on_comm)
done

theorem ustate_override_assoc:
"(s\<^sub>1 \<oplus> s\<^sub>2 on vs\<^sub>1) \<oplus> s\<^sub>3 on vs\<^sub>2 = s\<^sub>1 \<oplus> (s\<^sub>2 \<oplus> s\<^sub>3 on vs\<^sub>2) on (vs\<^sub>1 \<union> vs\<^sub>2)"
apply (transfer')
apply (rule override_on_assoc)
done

theorem ustate_override_cancel [simp]:
"s\<^sub>1 \<oplus>\<^sub>s (s\<^sub>2 \<oplus>\<^sub>s s\<^sub>3 on vs) on vs = s\<^sub>1 \<oplus>\<^sub>s s\<^sub>3 on vs"
"(s\<^sub>1 \<oplus>\<^sub>s s\<^sub>2 on vs) \<oplus>\<^sub>s s\<^sub>3 on vs = s\<^sub>1 \<oplus>\<^sub>s s\<^sub>3 on vs"
"s\<^sub>1 \<oplus>\<^sub>s (s\<^sub>1 \<oplus>\<^sub>s s\<^sub>2 on vs\<^sub>1) on vs\<^sub>2 = s\<^sub>1 \<oplus>\<^sub>s s\<^sub>2 on (vs\<^sub>1 \<inter> vs\<^sub>2)"
"(s\<^sub>1 \<oplus>\<^sub>s s\<^sub>2 on vs\<^sub>1) \<oplus>\<^sub>s s\<^sub>2 on vs\<^sub>2 = s\<^sub>1 \<oplus>\<^sub>s s\<^sub>2 on (vs\<^sub>1 \<union> vs\<^sub>2)"
"s\<^sub>1 \<oplus>\<^sub>s (s\<^sub>2 \<oplus>\<^sub>s s\<^sub>1 on vs\<^sub>2) on vs\<^sub>1 = s\<^sub>1 \<oplus>\<^sub>s s\<^sub>2 on (vs\<^sub>1 - vs\<^sub>2)"
"(s\<^sub>1 \<oplus>\<^sub>s s\<^sub>2 on vs\<^sub>1) \<oplus>\<^sub>s s\<^sub>1 on vs\<^sub>2 = s\<^sub>1 \<oplus>\<^sub>s s\<^sub>2 on (vs\<^sub>1 - vs\<^sub>2)"
apply (transfer', rule override_on_cancel(1))
apply (transfer', rule override_on_cancel(2))
apply (transfer', rule override_on_cancel(3))
apply (transfer', rule override_on_cancel(4))
apply (transfer', rule override_on_cancel(5))
apply (transfer', rule override_on_cancel(6))
done

text \<open>\todo{How about a polymorphic version of the following law?}\<close>

theorem ustate_override_singleton [simp]:
"s\<^sub>1 \<oplus>\<^sub>s s\<^sub>2 on {v} = s\<^sub>1(v :=\<^sub>u s\<^sub>2\<cdot>v)\<^sub>s"
apply (transfer)
apply (subst override_on_singleton)
apply (clarsimp)
done

theorem ustate_override_reorder:
"vs\<^sub>1 \<inter> vs\<^sub>2 = {} \<Longrightarrow>
 (s\<^sub>1 \<oplus>\<^sub>s s\<^sub>2 on vs\<^sub>1) \<oplus>\<^sub>s s\<^sub>3 on vs\<^sub>2 = (s\<^sub>1 \<oplus>\<^sub>s s\<^sub>3 on vs\<^sub>2) \<oplus>\<^sub>s s\<^sub>2 on vs\<^sub>1"
apply (transfer')
apply (rule override_on_reorder)
apply (auto)
done

subsection \<open>Transfer\<close>

theorem ex_ustate_transfer_0:
"(\<exists>s::ustate. P) \<longleftrightarrow> P"
apply (clarsimp)
done

theorem ex_ustate_transfer_1:
"(\<exists>s::ustate. P s\<star>v) \<longleftrightarrow> (\<exists>v. P v)"
apply (rule iffI)
apply (safe)
\<comment> \<open>Subgoal 1\<close>
apply (rule_tac x = "s\<star>v" in exI)
apply (assumption)
\<comment> \<open>Subgoal 2\<close>
apply (rename_tac x)
apply (rule_tac x = "\<sigma>(v := x)\<^sub>s" in exI)
apply (clarsimp)
done

theorem ex_ustate_transfer_2:
"distinct [v1\<down>, v2\<down>] \<Longrightarrow>
(\<exists>s::ustate. P s\<star>v1 s\<star>v2) \<longleftrightarrow> (\<exists>v1 v2. P v1 v2)"
apply (rule iffI)
apply (safe)
\<comment> \<open>Subgoal 1\<close>
apply (rule_tac x = "s\<star>v1" in exI)
apply (rule_tac x = "s\<star>v2" in exI)
apply (assumption)
\<comment> \<open>Subgoal 2\<close>
apply (rename_tac x1 x2)
apply (rule_tac x = "\<sigma>(v1 := x1, v2 := x2)\<^sub>s" in exI)
apply (clarsimp)
done

theorem ex_ustate_transfer_3:
"distinct [v1\<down>, v2\<down>, v3\<down>] \<Longrightarrow>
 (\<exists>s::ustate. P s\<star>v1 s\<star>v2 s\<star>v3) \<longleftrightarrow> (\<exists>v1 v2 v3. P v1 v2 v3)"
apply (rule iffI)
apply (safe)
\<comment> \<open>Subgoal 1\<close>
apply (rule_tac x = "s\<star>v1" in exI)
apply (rule_tac x = "s\<star>v2" in exI)
apply (rule_tac x = "s\<star>v3" in exI)
apply (assumption)
\<comment> \<open>Subgoal 2\<close>
apply (rename_tac x1 x2 x3)
apply (rule_tac x = "\<sigma>(v1 := x1, v2 := x2, v3 := x3)\<^sub>s" in exI)
apply (clarsimp)
done

theorem ex_ustate_transfer_4:
"distinct [v1\<down>, v2\<down>, v3\<down>, v4\<down>] \<Longrightarrow>
 (\<exists>s::ustate. P s\<star>v1 s\<star>v2 s\<star>v3 s\<star>v4) \<longleftrightarrow> (\<exists>v1 v2 v3 v4. P v1 v2 v3 v4)"
apply (rule iffI)
apply (safe)
\<comment> \<open>Subgoal 1\<close>
apply (rule_tac x = "s\<star>v1" in exI)
apply (rule_tac x = "s\<star>v2" in exI)
apply (rule_tac x = "s\<star>v3" in exI)
apply (rule_tac x = "s\<star>v4" in exI)
apply (assumption)
\<comment> \<open>Subgoal 2\<close>
apply (rename_tac x1 x2 x3 x4)
apply (rule_tac x = "\<sigma>(v1 := x1, v2 := x2, v3 := x3, v4 := x4)\<^sub>s" in exI)
apply (clarsimp)
done

theorem ex_ustate_transfer_5:
"distinct [v1\<down>, v2\<down>, v3\<down>, v4\<down>, v5\<down>] \<Longrightarrow>
 (\<exists>s::ustate. P s\<star>v1 s\<star>v2 s\<star>v3 s\<star>v4 s\<star>v5) \<longleftrightarrow> (\<exists>v1 v2 v3 v4 v5. P v1 v2 v3 v4 v5)"
apply (rule iffI)
apply (safe)
\<comment> \<open>Subgoal 1\<close>
apply (rule_tac x = "s\<star>v1" in exI)
apply (rule_tac x = "s\<star>v2" in exI)
apply (rule_tac x = "s\<star>v3" in exI)
apply (rule_tac x = "s\<star>v4" in exI)
apply (rule_tac x = "s\<star>v5" in exI)
apply (assumption)
\<comment> \<open>Subgoal 2\<close>
apply (rename_tac x1 x2 x3 x4 x5)
apply (rule_tac x = "\<sigma>(v1 := x1, v2 := x2, v3 := x3, v4 := x4, v5 := x5)\<^sub>s" in exI)
apply (clarsimp)
done

lemmas ex_ustate_transfer =
  ex_ustate_transfer_0
  ex_ustate_transfer_1
  ex_ustate_transfer_2
  ex_ustate_transfer_3
  ex_ustate_transfer_4
  ex_ustate_transfer_5

theorem all_ustate_transfer_0:
"(\<forall>s::ustate. P) \<longleftrightarrow> P"
apply (clarsimp)
done

theorem all_ustate_transfer_1:
"(\<forall>s::ustate. P s\<star>v) \<longleftrightarrow> (\<forall>v. P v)"
apply (rule iffI)
apply (simp_all)
apply (clarsimp)
apply (rename_tac x)
apply (drule_tac x = "\<sigma>(v := x)\<^sub>s" in spec)
apply (clarsimp)
done

theorem all_ustate_transfer_2:
"distinct [v1\<down>, v2\<down>] \<Longrightarrow>
 (\<forall>s::ustate. P s\<star>v1 s\<star>v2) \<longleftrightarrow> (\<forall>v1 v2. P v1 v2)"
apply (rule iffI)
apply (simp_all)
apply (clarsimp)
apply (rename_tac x1 x2)
apply (drule_tac x = "\<sigma>(v1 := x1, v2 := x2)\<^sub>s" in spec)
apply (clarsimp)
done

theorem all_ustate_transfer_3:
"distinct [v1\<down>, v2\<down>, v3\<down>] \<Longrightarrow>
 (\<forall>s::ustate. P s\<star>v1 s\<star>v2 s\<star>v3) \<longleftrightarrow> (\<forall>v1 v2 v3. P v1 v2 v3)"
apply (rule iffI)
apply (simp_all)
apply (clarsimp)
apply (rename_tac x1 x2 x3)
apply (drule_tac x = "\<sigma>(v1 := x1, v2 := x2, v3 := x3)\<^sub>s" in spec)
apply (clarsimp)
done

theorem all_ustate_transfer_4:
"distinct [v1\<down>, v2\<down>, v3\<down>, v4\<down>] \<Longrightarrow>
 (\<forall>s::ustate. P s\<star>v1 s\<star>v2 s\<star>v3 s\<star>v4) \<longleftrightarrow> (\<forall>v1 v2 v3 v4. P v1 v2 v3 v4)"
apply (rule iffI)
apply (simp_all)
apply (clarsimp)
apply (rename_tac x1 x2 x3 x4)
apply (drule_tac x = "\<sigma>(v1 := x1, v2 := x2, v3 := x3, v4 := x4)\<^sub>s" in spec)
apply (clarsimp)
done

theorem all_ustate_transfer_5:
"distinct [v1\<down>, v2\<down>, v3\<down>, v4\<down>, v5\<down>] \<Longrightarrow>
 (\<forall>s::ustate. P s\<star>v1 s\<star>v2 s\<star>v3 s\<star>v4 s\<star>v5) \<longleftrightarrow> (\<forall>v1 v2 v3 v4 v5. P v1 v2 v3 v4 v5)"
apply (rule iffI)
apply (simp_all)
apply (clarsimp)
apply (rename_tac x1 x2 x3 x4 x5)
apply (drule_tac x = "\<sigma>(v1 := x1, v2 := x2, v3 := x3, v4 := x4, v5 := x5)\<^sub>s" in spec)
apply (clarsimp)
done

lemmas all_ustate_transfer =
  all_ustate_transfer_0
  all_ustate_transfer_1
  all_ustate_transfer_2
  all_ustate_transfer_3
  all_ustate_transfer_4
  all_ustate_transfer_5

theorem meta_ustate_transfer_0:
"(\<And>s::ustate. PROP P) \<equiv> P"
apply (clarsimp)
done

theorem meta_ustate_transfer_1:
"(\<And>s::ustate. P s\<star>v) \<equiv> (\<And>v. P v)"
apply (atomize (full))
apply (simp add: all_ustate_transfer_1)
done

theorem meta_ustate_transfer_2:
"distinct [v1\<down>, v2\<down>] \<Longrightarrow>
 (\<And>s::ustate. P s\<star>v1 s\<star>v2) \<equiv> (\<And>v1 v2. P v1 v2)"
apply (atomize (full))
apply (simp add: all_ustate_transfer_2)
done

theorem meta_ustate_transfer_3:
"distinct [v1\<down>, v2\<down>, v3\<down>] \<Longrightarrow>
 (\<And>s::ustate. P s\<star>v1 s\<star>v2 s\<star>v3) \<equiv> (\<And>v1 v2 v3. P v1 v2 v3)"
apply (atomize (full))
apply (simp add: all_ustate_transfer_3)
done

theorem meta_ustate_transfer_4:
"distinct [v1\<down>, v2\<down>, v3\<down>, v4\<down>] \<Longrightarrow>
 (\<And>s::ustate. P s\<star>v1 s\<star>v2 s\<star>v3 s\<star>v4) \<equiv> (\<And>v1 v2 v3 v4. P v1 v2 v3 v4)"
apply (atomize (full))
apply (simp add: all_ustate_transfer_4)
done

theorem meta_ustate_transfer_5:
"distinct [v1\<down>, v2\<down>, v3\<down>, v4\<down>, v5\<down>] \<Longrightarrow>
 (\<And>s::ustate. P s\<star>v1 s\<star>v2 s\<star>v3 s\<star>v4 s\<star>v5) \<equiv> (\<And>v1 v2 v3 v4 v5. P v1 v2 v3 v4 v5)"
apply (atomize (full))
apply (simp add:all_ustate_transfer_5)
done

lemmas meta_ustate_transfer =
  meta_ustate_transfer_0
  meta_ustate_transfer_1
  meta_ustate_transfer_2
  meta_ustate_transfer_3
  meta_ustate_transfer_4
  meta_ustate_transfer_5

named_theorems ustate_transfer "ustate transfer rules"

declare meta_ustate_transfer [ustate_transfer]
declare all_ustate_transfer [ustate_transfer]
declare ex_ustate_transfer [ustate_transfer]

text \<open>@{text simp} alone is not sufficient as we require HO unification.\<close>

method ustate_transfer =
  (subst ustate_transfer)+
end