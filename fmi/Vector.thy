(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Vector.thy                                                           *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 8 Sep 2017 *)

section {* Vectors *}

text \<open>Encoding of fixed-size vectors (arrays).\<close>

theory Vector
imports Main "../utp/utp"
begin recall_syntax

hide_fact Congruence.set_eqI

lemma dom_lambda_pfun:
"dom (\<lambda>i. if i \<in> S then Some (f i) else None) = S"
apply (rule set_eqI)
apply (safe; clarsimp?)
apply (case_tac "x \<in> S")
apply (simp_all)
done

subsection {* Vector Type *}

definition vector :: "(nat \<rightharpoonup> 'a) set" where
"vector = {f. \<exists>n. dom f = {1..n}}"

typedef 'a vector = "vector :: (nat \<rightharpoonup> 'a) set"
apply (unfold vector_def)
apply (rule_tac x = "Map.empty" in exI)
apply (clarify)
apply (rule_tac x = "0" in exI)
apply (clarsimp)
done

setup_lifting type_definition_vector

subsection {* Constructors *}

lift_definition mk_vector :: "nat \<Rightarrow> 'a \<Rightarrow> 'a vector"
is "\<lambda>n default. \<lambda>i. if i \<in> {1..n} then (Some default) else None"
apply (rename_tac n default)
apply (unfold vector_def)
apply (clarify)
apply (subst dom_lambda_pfun)
apply (rule_tac x = "n" in exI)
apply (rule refl)
done

lift_definition vector_from_list :: "'a list \<Rightarrow> 'a vector"
is "\<lambda>l. \<lambda>i. if i \<in> {1..length l} then Some (l ! (i-1)) else None"
apply (rename_tac l)
apply (unfold vector_def)
apply (clarify)
apply (subst dom_lambda_pfun)
apply (rule_tac x = "length l" in exI)
apply (rule refl)
done

subsection {* Operators *}

instantiation vector :: (type) size
begin
lift_definition size_vector :: "'a vector \<Rightarrow> nat"
is "\<lambda>f. THE n. dom f = {1..n}" .
instance ..
end

lift_definition at_vector :: "'a vector \<Rightarrow> nat \<Rightarrow> 'a"
is "\<lambda>f i. if i \<in> dom f then the (f i) else undefined" .

notation at_vector ("_\<^bold>[_\<^bold>]" [1000, 0] 1000)

lift_definition vector_upd :: "'a vector \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a vector"
is "\<lambda>f i x. if i \<in> dom f then f(i \<mapsto> x) else f"
apply (rename_tac f i x)
apply (unfold vector_def)
apply (clarify)
apply (rule_tac x = "n" in exI)
apply (erule subst)
apply (simp add: insert_absorb)
done

text \<open>What should be the precedence of the operator below?\<close>

notation vector_upd ("(_\<^bold>[_\<^bold>] \<hookleftarrow>/ _)" [101, 0, 101] 100)

subsection {* Isabelle/UTP Integration *}

syntax "umk_vector" ::
  "nat \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('a vector, '\<alpha>) uexpr" ("mk'_vector\<^sub>u")

translations
  "mk_vector\<^sub>u n default" \<rightleftharpoons> "(CONST bop) (CONST mk_vector) \<guillemotleft>n\<guillemotright> default"

syntax "uvector_from_list" ::
  "'a list \<Rightarrow> ('a vector, '\<alpha>) uexpr" ("vector'_from'_list\<^sub>u")

translations
  "vector_from_list\<^sub>u l" \<rightleftharpoons> "(CONST uop) (CONST vector_from_list) \<guillemotleft>l\<guillemotright>"

definition ucard_vector :: "'a vector \<Rightarrow> nat" where
[simp]: "ucard_vector = size"

adhoc_overloading ucard ucard_vector

purge_notation
  utp_pred.closure ("[_]\<^sub>u")

syntax "uat_vector" ::
  "('a vector, '\<alpha>) uexpr \<Rightarrow> nat \<Rightarrow> ('a, '\<alpha>) uexpr" ("_[_]\<^sub>u" [1000, 0] 1000)

translations "v[i]\<^sub>u" \<rightleftharpoons> "(CONST bop) (CONST at_vector) v \<guillemotleft>i\<guillemotright>"

text \<open>Indexed assignment and application for the @{type vector} type.\<close>

adhoc_overloading uupd vector_upd and uapply at_vector

text \<open>TODO: Pretty-printing of indexed assignment. See theory @{theory utp_rel}.\<close>

(* translations "x [k] := v" \<leftharpoondown> "x := &x(k \<mapsto> v)\<^sub>u" *)

subsection {* Theorems *}

lemma atLeastOneAtMost_eq:
fixes n :: "nat"
fixes m :: "nat"
shows "{1..n} = {1..m} \<longleftrightarrow> (n = m)"
apply (safe)
apply (metis One_nat_def card_atLeastAtMost diff_Suc_Suc diff_zero)
done

theorem mk_vector_size [simp]:
"size (mk_vector n x) = n"
apply (transfer)
apply (subst dom_lambda_pfun)
apply (rule the_equality)
apply (rule refl)
apply (simp only: atLeastOneAtMost_eq)
done

theorem vector_from_list_size [simp]:
"size (vector_from_list l) = length l"
apply (transfer)
apply (subst dom_lambda_pfun)
apply (rule the_equality)
apply (rule refl)
apply (simp only: atLeastOneAtMost_eq)
done

theorem mk_vector_at [simp]:
"i \<in> {1..n} \<Longrightarrow> (mk_vector n x)\<^bold>[i\<^bold>] = x"
apply (transfer)
apply (clarsimp)
done

theorem vector_from_list_at [simp]:
"i \<in> {1..length l} \<Longrightarrow> (vector_from_list l)\<^bold>[i\<^bold>] = l ! (i - 1)"
apply (transfer)
apply (clarsimp)
done

theorem vector_from_list_upd [simp]:
"i \<in> {1..length l} \<Longrightarrow>
  (vector_from_list l)\<^bold>[i\<^bold>] \<hookleftarrow> x = (vector_from_list (list_update l (i-1) x))"
apply (transfer)
apply (subst dom_lambda_pfun)
apply (clarsimp)
apply (rule ext)
apply (simp add: eq_diff_iff)
done

lemma vector_app_eq_None:
"v \<in> vector \<Longrightarrow> v i = None \<longleftrightarrow> i \<notin> {1..(THE n. dom v = {1..n})}"
apply (unfold vector_def)
apply (clarify)
apply (rule the1I2)
-- {* Subgoal 1 *}
apply (rule_tac a = "n" in ex1I)
apply (clarsimp)
apply (clarsimp)
-- {* Subgoal 2 *}
apply (blast)
done

lemma vector_upd_size [simp]:
"size (v\<^bold>[i\<^bold>] \<hookleftarrow> x) = size v"
apply (transfer)
apply (case_tac "i \<in> dom v")
apply (simp_all del: One_nat_def)
apply (subgoal_tac "insert i (dom v) = dom v")
apply (erule ssubst)
apply (rule refl)
apply (auto)
done

theorem vector_upd_at [simp]:
"i \<in> {1..size v} \<Longrightarrow> (v\<^bold>[i\<^bold>] \<hookleftarrow> x)\<^bold>[j\<^bold>] = (if i = j then x else v\<^bold>[j\<^bold>])"
apply (transfer)
apply (clarsimp simp del: One_nat_def)
apply (simp add: vector_app_eq_None)
done

theorem vector_upd_ident [simp]:
"(v\<^bold>[i\<^bold>] \<hookleftarrow> v\<^bold>[i\<^bold>]) = v"
apply (transfer')
apply (clarsimp)
apply (simp add: fun_upd_idem_iff)
done

text \<open>Ordered rewriting is performed automatically, so the below is safe.\<close>

theorem vector_upd_commute [simp]:
"i \<noteq> j \<Longrightarrow> ((v\<^bold>[i\<^bold>] \<hookleftarrow> x)\<^bold>[j\<^bold>] \<hookleftarrow> y) = ((v\<^bold>[j\<^bold>] \<hookleftarrow> y)\<^bold>[i\<^bold>] \<hookleftarrow> x)"
apply (transfer')
apply (clarsimp)
apply (simp add: fun_upd_twist)
done

theorem vector_upd_cancel [simp]:
"((v\<^bold>[i\<^bold>] \<hookleftarrow> x)\<^bold>[i\<^bold>] \<hookleftarrow> y) = (v\<^bold>[i\<^bold>] \<hookleftarrow> y)"
apply (transfer')
apply (clarsimp)
done

(* TODO: Revise the proof below! *)

lemma eq_vector_from_list:
"v = vector_from_list l \<longleftrightarrow>
  size v = (length l) \<and> (\<forall>i\<in>{1..length l}. v\<^bold>[i\<^bold>] = l ! (i - 1))"
apply (transfer)
apply (simp add: fun_eq_iff)
apply (rule the1I2)
apply (unfold vector_def)
apply (force)
apply (safe; clarsimp?)
apply (smt Icc_eq_Icc atLeastAtMost_iff atLeastAtMost_insertL domIff le_0_eq not_less_eq_eq option.simps(3) order_refl)
apply (metis atLeastAtMost_iff domIff option.exhaust_sel)
using atLeastAtMost_iff apply (blast)
apply (metis atLeastAtMost_iff domIff le0 le_SucE not_less_eq_eq)
done

hide_fact dom_lambda_pfun vector_app_eq_None

lifting_forget vector.lifting
end