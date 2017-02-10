(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: usort.thy                                                            *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 10 Jan 2017 *)

section {* State Sort *}

theory usort
imports ustate
begin

default_sort type

subsection {* Type Class *}

text {*
  We define a type class here to locate the universal state type @{type ustate}
  within some larger type into which it may be embedded. Access to the embedded
  state is via the lens @{text "ust\<^sub>L"} provided by the class. That lens can be
  composed with the lens for axiomatic variables to obtain variable lenses into
  some arbitrary state space @{text "'\<alpha>::ust"}. We thus obtain a model that is
  agnostic to the particular structure of the state type. This is in line with
  Isabelle/UTP's solution to integrating deep variables and lends itself nicely
  for combination of our model with its preexisting variable model(s), meaning
  that we can freely use different kinds of variables alongside. This unifying
  aspect of lenses is very interesting in its own right and may deserves more
  exploration.
*}

class ust =
  fixes ust_lens :: "ustate \<Longrightarrow> 'a" ("ust\<^sub>L")
  assumes vwb_lens_ust: "vwb_lens ust_lens"

subsection {* Instantiations *}

subsubsection {* @{type ustate} Type *}

text {* Clearly type @{type ustate} itself instantiates @{class ust}. *}

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

subsubsection {* Product Type *}

text {*
  Before we proceed, we define two utility functions that enable us to dash and
  undash states of type @{type ustate}. Both are effectively substitutions that
  turn all undashed (resp.~dashed) variables into dashed (resp.~undashed) ones.
*}

lift_definition undash_ustate :: "ustate \<Rightarrow> ustate"
is "\<lambda>s. \<lambda>v::uvar. s v\<acute>"
apply (var_tac)
done

adhoc_overloading undash undash_ustate

lift_definition dash_ustate :: "ustate \<Rightarrow> ustate"
is "\<lambda>s. \<lambda>v::uvar. s v\<inverse>"
apply (var_tac)
done

adhoc_overloading dash dash_ustate

text {*
  We next instantiate class @{class ust} for product state spaces. This creates
  a link to state models that uses HOL relations to represent UTP relations. To
  turn a state product into a single state (of type @{type ustate}), we have to
  dash the undashed variables of the second state and override the first state
  (on the dashed variable) with the result. We start by defining two utility
  functions to combine and split relational state spaces; they are effectively
  the get and put functions of the lens for the @{type prod}uct instantiation.
*}

definition comb_ustate :: "ustate \<times> ustate \<Rightarrow> ustate" where [transfer_unfold]:
"comb_ustate = (\<lambda>(s1, s2). s1 \<oplus>\<^sub>s s2\<acute> on DASHED)"

definition split_ustate ::
  "(ustate \<times> ustate) \<Rightarrow> ustate \<Rightarrow> (ustate \<times> ustate)" where [transfer_unfold]:
"split_ustate = (\<lambda>(s1, s2). \<lambda>s. (s1 \<oplus>\<^sub>s s on UNDASHED, s2 \<oplus>\<^sub>s s\<inverse> on UNDASHED))"

definition split_ustate_lens :: "ustate \<Longrightarrow> ustate \<times> ustate" ("ust\<^sub>>\<^sub><") where
"split_ustate_lens = \<lparr>lens_get = comb_ustate, lens_put = split_ustate\<rparr>"

text {* We next prove lemmas for @{term "ust\<^sub>>\<^sub><"} being a very well-behaved lens. *}

theorem split_ustate_inv:
"comb_ustate (split_ustate ss s) = s"
apply (transfer')
apply (clarsimp)
apply (rule ext)
apply (rename_tac v)
apply (case_tac "v \<in> DASHED")
apply (simp_all)
-- {* Subgoal 1 *}
apply (var_tac)
-- {* Subgoal 2 *}
apply (var_tac)
done

theorem comb_ustate_inv:
"split_ustate ss (comb_ustate ss) = ss"
apply (transfer')
apply (clarsimp)
apply (rule conjI)
-- {* Subgoal 1 *}
apply (var_tac)
-- {* Subgoal 2 *}
apply (rule ext)
apply (rename_tac v)
apply (case_tac "v \<in> UNDASHED")
-- {* Subgoal 2.1 *}
apply (var_tac)
-- {* Subgoal 2.2 *}
apply (var_tac)
done

theorem split_ustate_idem:
"split_ustate (split_ustate ss t) s = split_ustate ss s"
apply (transfer')
apply (clarsimp)
done

theorem ustate_split_vwb_lens:
"vwb_lens ust\<^sub>>\<^sub><"
apply (unfold_locales)
apply (unfold split_ustate_lens_def)
apply (simp_all)
apply (rule split_ustate_inv)
apply (rule comb_ustate_inv)
apply (rule split_ustate_idem)
done

text {*
  We are finally ready to carry out the instantiation of the @{type prod} type
  as class @{class ust}. It makes use of the compression lens @{term "ust\<^sub>>\<^sub><"}.
*}

instantiation prod :: (ust, ust) ust
begin
definition ust_lens_prod :: "ustate \<Longrightarrow> 'a \<times> 'b" where
"ust_lens_prod = ust\<^sub>>\<^sub>< ;\<^sub>L (ust\<^sub>L \<times>\<^sub>L ust\<^sub>L)"
instance
apply (intro_classes)
apply (unfold ust_lens_prod_def)
apply (simp add: comp_vwb_lens prod_vwb_lens ustate_split_vwb_lens vwb_lens_ust)
done
end

subsection {* Store Type *}

text {* We provide a concrete extensible store for @{type ustate} instances. *}

record ust_store =
  ust_store :: "ustate"

definition ust_store_lens :: "ustate \<Longrightarrow> 'a ust_store_ext" where
"ust_store_lens = \<lparr>lens_get = ust_store, lens_put = (\<lambda>\<sigma> v. \<sigma>\<lparr>ust_store := v\<rparr>)\<rparr>"

notation ust_store_lens ("ust'_store\<^sub>L")

definition ust_ext_lens :: "'a \<Longrightarrow> 'a ust_store_ext" where
"ust_ext_lens = \<lparr>lens_get = more, lens_put = (\<lambda>\<sigma> v. \<sigma>\<lparr>more := v\<rparr>)\<rparr>"

notation ust_ext_lens ("ust'_store'_ext\<^sub>L")

instantiation ust_store_ext :: (type) ust
begin
definition ust_lens_ust_store_ext :: "ustate \<Longrightarrow> 'a ust_store_ext" where
"ust_lens_ust_store_ext = ust_store\<^sub>L"
instance
apply (intro_classes)
apply (unfold ust_lens_ust_store_ext_def ust_store_lens_def)
apply (unfold_locales)
apply (simp_all)
done
end

subsection {* Laws *}

subsubsection {* Independence Laws *}

text {* \todo{Prove the relevant lens independence laws here!} *}

subsubsection {* State Space Laws *}

theorem dash_ustate_app_mono [simp]:
"v \<in> UNDASHED \<Longrightarrow> (dash_ustate s)\<cdot>(v\<acute>) = s\<cdot>v"
apply (transfer')
apply (var_tac)
done

theorem dash_ustate_app_poly [simp]:
"v \<in> UNDASHED \<Longrightarrow>(dash_ustate s)\<star>(v\<acute>) = s\<star>v"
apply (unfold ustate_app_poly_def)
apply (subst dash_erasure_commutes)
apply (rule arg_cong) back
apply (simp add: UNDASHED_uvar_def UNDASHED_var_def)
done
end