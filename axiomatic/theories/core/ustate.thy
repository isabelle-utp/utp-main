(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: ustate.thy                                                           *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 25 Jan 2017 *)

section {* State Space *}

theory ustate
imports utype uval uvar
begin

text {*
  In this theory, we define a notion of state space (binding) for universal
  values. This is through a new type @{text uspace}. We consider states as
  total bindings so that there is no notion of frame and all variables are
  assigned a value. A property of state bindings is that they are well-typed
  by construction.
*}

default_sort injectable

subsection {* State Type *}

text {*
  As before, total functions are used to encode states. This is possible due
  to the axiom @{thm [source] utypes_non_empty} which enforces non-emptiness
  of all model types, irrespective of them being injectable into @{type uval}
  or not. Such guarantees the existence of a well-typed binding here and this
  is needed to discharge the non-emptiness assumption of the type definition.
*}

typedef ustate = "{b::uvar \<Rightarrow> uval. \<forall>v. (b v) :\<^sub>u (type v)}"
apply (rule_tac x = "\<lambda>v. some_uval (type v)" in exI)
apply (clarsimp)
apply (rule some_uval_typed)
done

text {* \fixme{Is there a way to fix the warning about relators below?} *}

setup_lifting type_definition_ustate

subsection {* State Class  *}

text {*
  This type class enables us to locate a universal state type inside a larger
  type into which @{type ustate} may be embedded. Access to the embedded state
  is via a lens @{text "ust\<^sub>L"}. That lens is typically composed with the lens
  for axiomatic variables (theory @{text ulens}. We thus obtain a model which
  is agnostic to the particular structure of the state type. This is in line
  with Isabelle/UTP's solution to integrating deep variables and lends itself
  nicely for combination of our model with the existing variable model(s) in
  Isabelle/UTP, meaning we potentially can potentially use different kinds of
  variables alongside. This unifying aspect of lenses is very interesting in
  its own right, and maybe deserves more investigation and possibly a paper.
*}

text {* An open issue is perhaps how we deal with relational state spaces. *}

class ust =
  fixes ust_lens :: "ustate \<Longrightarrow> 'a::type" ("ust\<^sub>L")
  assumes vwb_lens_ust: "vwb_lens ust_lens"

text {* Clearly type @{type ustate} instantiates @{class ust}. *}

instantiation ustate :: ust
begin
definition ust_lens_ustate :: "ustate \<Longrightarrow> ustate" where
[simp]: "ust_lens_ustate = 1\<^sub>L"
instance
apply (intro_classes)
apply (unfold ust_lens_ustate_def)
apply (rule id_vwb_lens)
done
end

text {*
  We should be able to instantiate the product type as class @{class ust}
  too. The idea is to combine two plain states into a relational one. This
  is taking the undashed variables of each of the states and merging them
  via state override while dashing the variables of the second one. We then
  should be able to treat relational states uniformly within our model: we
  ought to be able to instantiate @{text "'a uexpr"} with either a flat or
  relational type while still being able to define all concepts, including
  the unrestriction caveat of the type and expression parser. This suggests
  that a relational expression model does not need any `special treatment'.
*}

lift_definition dash_ustate :: "ustate \<Rightarrow> ustate"
is "\<lambda>s. \<lambda>v::uvar. s v\<inverse>"
apply (rename_tac \<sigma> v)
apply (atomize (full))
apply (clarsimp)
apply (unfold vars)
apply (metis uvar.select_convs(2) uvar.surjective uvar.update_convs(1))
done

consts ustate_comb_lens :: "ustate \<Longrightarrow> ustate \<times> ustate" ("ust\<^sub>>\<^sub><")

-- {* TODO *}

(*
lemma ustate_comb_vwb_lens:
"vwb_lens ust\<^sub>>\<^sub><"
sorry
*)

(*
instantiation prod :: (ust, ust) ust
begin
definition ust_lens_prod :: "ustate \<Longrightarrow> 'a \<times> 'b" where
"ust_lens_prod = ust\<^sub>>\<^sub>< ;\<^sub>L (ust\<^sub>L::ustate \<Longrightarrow> 'a) \<times>\<^sub>L (ust\<^sub>L::ustate \<Longrightarrow> 'b)"
instance
apply (intro_classes)
apply (unfold ust_lens_prod_def)
apply (simp add: ustate_comb_vwb_lens comp_vwb_lens prod_vwb_lens vwb_lens_ust)
done
end
*)

subsection {* Constants *}

subsubsection {* Some State *}

text {* Constant that yields some arbitrary (albeit well-typed) state. *}

lift_definition some_ustate :: "ustate" ("\<sigma>\<^sub>0")
is "\<lambda>v. some_uval (type v)"
apply (rule some_uval_typed)
done

subsection {* Operators *}

text {*
  The operators we introduce are application, state updated, state override,
  and congruence. For application and update, we provide both a monomorphic
  and polymorphic versions of the operator. Strictly, state update could be
  expressed in terms of override with a singleton binding i.e.~if we added a
  construct to create such bindings.
*}

subsubsection {* Application *}

text {* Both a monomorphic and polymorphic version is provided. *}

lift_definition ustate_app_mono :: "ustate \<Rightarrow> uvar \<Rightarrow> uval"
is "\<lambda>s v. s v"
done

notation ustate_app_mono ("_\<cdot>_" [1000, 1000] 1000)

definition ustate_app_poly :: "ustate \<Rightarrow> 'a var \<Rightarrow> 'a" where
[transfer_unfold]: "ustate_app_poly s v = ProjU s\<cdot>(v\<down>)"

notation ustate_app_poly ("_\<star>_" [1000, 1000] 1000)

subsubsection {* State Update *}

text {* Both a monomorphic and polymorphic version is provided. *}

lift_definition ustate_upd_mono :: "ustate \<Rightarrow> uvar \<Rightarrow> uval \<Rightarrow> ustate"
is "\<lambda>s v x. if x :\<^sub>u (type v) then s(v := x) else s"
apply (transfer')
apply (simp add: typing)
done

definition ustate_upd_poly :: "ustate \<Rightarrow>  'a var \<Rightarrow> 'a \<Rightarrow> ustate" where
[transfer_unfold]: "ustate_upd_poly s v x = ustate_upd_mono s v\<down> (InjU x)"

text {* Syntax for State Update*}

nonterminal ubinds and ubind

text {* The below is inspired by Isabelle's syntax for function update. *}

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

subsubsection {* Override *}

lift_definition ustate_override :: "ustate \<Rightarrow> ustate \<Rightarrow> uvar set \<Rightarrow> ustate"
is "override_on"
apply (rename_tac s\<^sub>1 s\<^sub>2 vs v)
apply (case_tac "v \<in> vs")
apply (simp_all)
done

notation ustate_override ("_ \<oplus>\<^sub>s _ on _" [55, 56, 56] 55)

subsubsection {* Congruence *}

text {* Two states are congruent if they agree over a given set of variables. *}

lift_definition ustate_cong_on :: "ustate \<Rightarrow> ustate \<Rightarrow> uvar set \<Rightarrow> bool"
is "\<lambda>b1 b2 vs. \<forall>v\<in>vs. (b1 v) = (b2 v)"
done

notation ustate_cong_on ("_ \<cong>\<^sub>b _ on _" [51, 51, 0] 50)

subsection {* Theorems *}

paragraph {* Transfer Laws *}

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

paragraph {* Application Laws *}

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

text {*
  Note that the following theorem is not subsumed by the one above. This is
  because the types of the polymorphic types of the variables @{text v} and
  @{text w} may be different whereas above the have to be the same.
*}

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

paragraph {* Override Laws *}

text {*
  Many of the theorems here mirror those for @{term "f \<oplus> g on a"} in theory
  @{theory ucommon} (see Section \ref{sec:override_laws}).
*}

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

text {* \todo{How about a polymorphic version of the following law?} *}

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

paragraph {* Undashed State Laws *}

theorem dash_ustate_app_mono [simp]:
"v \<in> UNDASHED \<Longrightarrow> (dash_ustate s)\<cdot>(v\<acute>) = s\<cdot>v"
apply (transfer')
apply (erule rev_mp)
apply (induct_tac v)
apply (rename_tac n t)
apply (induct_tac n)
apply (simp add: vars)
done

theorem dash_ustate_app_poly [simp]:
"v \<in> UNDASHED \<Longrightarrow>(dash_ustate s)\<star>(v\<acute>) = s\<star>v"
apply (unfold ustate_app_poly_def)
apply (subst dash_erasure_commutes)
apply (rule arg_cong) back
apply (simp add: UNDASHED_uvar_def UNDASHED_var_def)
done

subsection {* Transfer *}

theorem ex_ustate_transfer_0:
"(\<exists>s::ustate. P) \<longleftrightarrow> P"
apply (clarsimp)
done

theorem ex_ustate_transfer_1:
"(\<exists>s::ustate. P s\<star>v) \<longleftrightarrow> (\<exists>v. P v)"
apply (rule iffI)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "s\<star>v" in exI)
apply (assumption)
-- {* Subgoal 2 *}
apply (rename_tac x)
apply (rule_tac x = "\<sigma>(v := x)\<^sub>s" in exI)
apply (clarsimp)
done

theorem ex_ustate_transfer_2:
"distinct [v1\<down>, v2\<down>] \<Longrightarrow>
(\<exists>s::ustate. P s\<star>v1 s\<star>v2) \<longleftrightarrow> (\<exists>v1 v2. P v1 v2)"
apply (rule iffI)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "s\<star>v1" in exI)
apply (rule_tac x = "s\<star>v2" in exI)
apply (assumption)
-- {* Subgoal 2 *}
apply (rename_tac x1 x2)
apply (rule_tac x = "\<sigma>(v1 := x1, v2 := x2)\<^sub>s" in exI)
apply (clarsimp)
done

theorem ex_ustate_transfer_3:
"distinct [v1\<down>, v2\<down>, v3\<down>] \<Longrightarrow>
 (\<exists>s::ustate. P s\<star>v1 s\<star>v2 s\<star>v3) \<longleftrightarrow> (\<exists>v1 v2 v3. P v1 v2 v3)"
apply (rule iffI)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "s\<star>v1" in exI)
apply (rule_tac x = "s\<star>v2" in exI)
apply (rule_tac x = "s\<star>v3" in exI)
apply (assumption)
-- {* Subgoal 2 *}
apply (rename_tac x1 x2 x3)
apply (rule_tac x = "\<sigma>(v1 := x1, v2 := x2, v3 := x3)\<^sub>s" in exI)
apply (clarsimp)
done

theorem ex_ustate_transfer_4:
"distinct [v1\<down>, v2\<down>, v3\<down>, v4\<down>] \<Longrightarrow>
 (\<exists>s::ustate. P s\<star>v1 s\<star>v2 s\<star>v3 s\<star>v4) \<longleftrightarrow> (\<exists>v1 v2 v3 v4. P v1 v2 v3 v4)"
apply (rule iffI)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "s\<star>v1" in exI)
apply (rule_tac x = "s\<star>v2" in exI)
apply (rule_tac x = "s\<star>v3" in exI)
apply (rule_tac x = "s\<star>v4" in exI)
apply (assumption)
-- {* Subgoal 2 *}
apply (rename_tac x1 x2 x3 x4)
apply (rule_tac x = "\<sigma>(v1 := x1, v2 := x2, v3 := x3, v4 := x4)\<^sub>s" in exI)
apply (clarsimp)
done

theorem ex_ustate_transfer_5:
"distinct [v1\<down>, v2\<down>, v3\<down>, v4\<down>, v5\<down>] \<Longrightarrow>
 (\<exists>s::ustate. P s\<star>v1 s\<star>v2 s\<star>v3 s\<star>v4 s\<star>v5) \<longleftrightarrow> (\<exists>v1 v2 v3 v4 v5. P v1 v2 v3 v4 v5)"
apply (rule iffI)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "s\<star>v1" in exI)
apply (rule_tac x = "s\<star>v2" in exI)
apply (rule_tac x = "s\<star>v3" in exI)
apply (rule_tac x = "s\<star>v4" in exI)
apply (rule_tac x = "s\<star>v5" in exI)
apply (assumption)
-- {* Subgoal 2 *}
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
apply (simp add: all_ustate_transfer_5)
done

lemmas meta_ustate_transfer =
  meta_ustate_transfer_0
  meta_ustate_transfer_1
  meta_ustate_transfer_2
  meta_ustate_transfer_3
  meta_ustate_transfer_4
  meta_ustate_transfer_5

named_theorems ustate_transfer "ustate transfer rules"

declare ex_ustate_transfer [ustate_transfer]
declare all_ustate_transfer [ustate_transfer]
declare meta_ustate_transfer [ustate_transfer]

text {* @{text simp} alone is not sufficient as we require HO unification. *}

method ustate_transfer =
  (subst ustate_transfer)+
end