(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: cardinals.thy                                                        *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)
(* LAST REVIEWED: 27 March 2014 *)

header {* Lightweight Cardinals *}

theory cardinals
imports Main Real Countable_Set Cardinals infinity UNIV_TYPE
begin

subsection {* Cardinal Order *}

definition leq_card :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool" (infix "\<preceq>\<^sub>c" 50) where
"(A \<preceq>\<^sub>c B) \<longleftrightarrow> (\<exists> f . (inj_on f A) \<and> (f ` A) \<subseteq> B)"

definition equal_card :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool" (infix "\<equiv>\<^sub>c" 50) where
"(A \<equiv>\<^sub>c B) \<longleftrightarrow> (A \<preceq>\<^sub>c B) \<and> (B \<preceq>\<^sub>c A)"

definition less_card :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool" (infix "\<prec>\<^sub>c" 50) where
"(A \<prec>\<^sub>c B) \<longleftrightarrow> (A \<preceq>\<^sub>c B) \<and> \<not> (A \<equiv>\<^sub>c B)"

theorems card_ord_defs =
  leq_card_def
  equal_card_def
  less_card_def

subsection {*  Constructors *}

definition fin_card :: "nat \<Rightarrow> nat set" ("c\<^sub>f") where
"c\<^sub>f n = {1..n}"

definition type_card :: "'a itself \<Rightarrow> 'a set" ("c\<^sub>\<T>") where
"c\<^sub>\<T> (t :: 'a itself) = UNIV_T('a)"

definition bool_card :: "bool set" ("c\<^sub>\<bool>") where
"c\<^sub>\<bool> = c\<^sub>\<T> TYPE(bool)"

definition nat_card :: "nat set" ("c\<^sub>\<nat>") where
"c\<^sub>\<nat> = c\<^sub>\<T> TYPE(nat)"

definition real_card :: "real set" ("c\<^sub>\<real>") where
"c\<^sub>\<real> = c\<^sub>\<T> TYPE(real)"

theorems card_defs =
  fin_card_def
  type_card_def
  bool_card_def
  nat_card_def
  real_card_def

subsection {* Theorems *}

subsubsection {* Library Link *}

theorem ordLess_lemma :
"(A <o B) \<longleftrightarrow> (A \<le>o B) \<and> \<not> (A =o B)"
apply (metis not_ordLess_ordIso ordLeq_iff_ordLess_or_ordIso)
done

paragraph {* Transfer Rules *}

theorem leq_card_iff_ordLeq :
"c1 \<preceq>\<^sub>c c2 \<longleftrightarrow> |c1| \<le>o |c2|"
apply (fold card_of_ordLeq)
apply (unfold leq_card_def)
apply (simp)
done

theorem equal_card_iff_ordIso :
"c1 \<equiv>\<^sub>c c2 \<longleftrightarrow> |c1| =o |c2|"
apply (unfold equal_card_def)
apply (unfold leq_card_iff_ordLeq)
apply (unfold ordIso_iff_ordLeq)
apply (rule refl)
done

theorem less_card_iff_ordLess :
"c1 \<prec>\<^sub>c c2 \<longleftrightarrow> |c1| <o |c2|"
apply (unfold less_card_def equal_card_def)
apply (unfold leq_card_iff_ordLeq)
apply (unfold ordLess_lemma ordIso_iff_ordLeq)
apply (rule refl)
done

theorems card_transfer =
  leq_card_iff_ordLeq
  equal_card_iff_ordIso
  less_card_iff_ordLess

paragraph {* Introduction Rules *}

theorem leq_card_intro [intro] :
"|c1| \<le>o |c2| \<Longrightarrow> c1 \<preceq>\<^sub>c c2"
apply (simp add: leq_card_iff_ordLeq)
done

theorem equal_card_intro [intro] :
"|c1| =o |c2| \<Longrightarrow> c1 \<equiv>\<^sub>c c2"
apply (simp add: equal_card_iff_ordIso)
done

theorem less_card_intro [intro] :
"|c1| <o |c2| \<Longrightarrow> c1 \<prec>\<^sub>c c2"
apply (simp add: less_card_iff_ordLess)
done

paragraph {* Destruction Rules *}

theorem leq_card_dest [dest] :
"c1 \<preceq>\<^sub>c c2 \<Longrightarrow> |c1| \<le>o |c2|"
apply (simp add: leq_card_iff_ordLeq)
done

theorem equal_card_dest [dest] :
"c1 \<equiv>\<^sub>c c2 \<Longrightarrow> |c1| =o |c2|"
apply (simp add: equal_card_iff_ordIso)
done

theorem less_card_dest [dest] :
"c1 \<prec>\<^sub>c c2 \<Longrightarrow> |c1| <o |c2|"
apply (simp add: less_card_iff_ordLess)
done

subsubsection {* Theorems for @{term "op \<preceq>\<^sub>c"} *}

theorem leq_card_refl :
"(A \<preceq>\<^sub>c A)"
apply (unfold leq_card_def)
apply (rule_tac x = "id" in exI)
apply (simp)
done

theorem leq_card_antisym :
"\<lbrakk>(A \<preceq>\<^sub>c B); (B \<preceq>\<^sub>c A)\<rbrakk> \<Longrightarrow> (A \<equiv>\<^sub>c B)"
apply (unfold equal_card_def)
apply (simp)
done

theorem leq_card_trans :
"\<lbrakk>(A \<preceq>\<^sub>c B); (B \<preceq>\<^sub>c C)\<rbrakk> \<Longrightarrow> (A \<preceq>\<^sub>c C)"
apply (unfold leq_card_def)
apply (clarify)
apply (rename_tac f g)
apply (rule_tac x = "g \<circ> f" in exI)
apply (rule conjI)
-- {* Subgoal 1 *}
apply (rule comp_inj_on)
apply (assumption)
apply (erule subset_inj_on)
apply (assumption)
-- {* Subgoal 2 *}
apply (simp add: image_compose)
apply (metis image_mono order.trans)
done

theorem leq_card_linear :
"(A \<preceq>\<^sub>c B) \<or> (B \<preceq>\<^sub>c A)"
apply (unfold leq_card_def)
apply (metis one_set_greater)
done

theorem not_leq_card_dest :
"\<not> (A \<preceq>\<^sub>c B) \<Longrightarrow> (B \<preceq>\<^sub>c A)"
apply (metis leq_card_linear)
done

theorem leq_card_empty :
"{} \<preceq>\<^sub>c C"
apply (unfold leq_card_def)
apply (simp)
done

theorem leq_card_subset :
"A \<subseteq> B \<Longrightarrow> A \<preceq>\<^sub>c B"
apply (unfold leq_card_def)
apply (rule_tac x = "id" in exI)
apply (simp)
done

theorem leq_image_mono :
"A \<preceq>\<^sub>c C \<Longrightarrow> (f ` A) \<preceq>\<^sub>c C"
apply (unfold leq_card_def)
apply (clarify)
apply (rename_tac g)
apply (rule_tac x = "g o (inv_into A f)" in exI)
apply (rule conjI)
-- {* Subgoal 1 *}
apply (rule comp_inj_on)
apply (rule inj_on_inv_into)
apply (simp)
apply (erule subset_inj_on)
apply (rule image_subsetI)
apply (erule inv_into_into)
-- {* Subgoal 2 *}
apply (rule image_subsetI)
apply (unfold comp_def)
apply (metis image_eqI in_mono inv_into_into)
done

subsubsection {* Theorems for @{term "op \<equiv>\<^sub>c"} *}

theorem equal_card_bij_betw :
"(A \<equiv>\<^sub>c B) \<longleftrightarrow> (\<exists> f . bij_betw f A B)"
apply (unfold equal_card_def leq_card_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rename_tac f g)
apply (rule Cantor_Bernstein)
apply (assumption)+
-- {* Subgoal 2 *}
apply (unfold bij_betw_def)
apply (rule_tac x = "f" in exI)
apply (clarsimp)
-- {* Subgoal 3 *}
apply (rule_tac x = "inv_into A f" in exI)
apply (clarsimp)
apply (rule inj_on_inv_into)
apply (simp)
done

theorem equal_card_refl :
"(A \<equiv>\<^sub>c A)"
apply (unfold equal_card_def)
apply (simp add: leq_card_refl)
done

theorem equal_card_sym :
"(A \<equiv>\<^sub>c B) \<longleftrightarrow> (B \<equiv>\<^sub>c A)"
apply (unfold equal_card_def)
apply (safe)
done

theorem equal_card_trans :
"\<lbrakk>(A \<equiv>\<^sub>c B); (B \<equiv>\<^sub>c C)\<rbrakk> \<Longrightarrow> (A \<equiv>\<^sub>c C)"
apply (unfold equal_card_def)
apply (clarsimp)
apply (rule conjI)
apply (erule leq_card_trans)
apply (assumption)
apply (erule leq_card_trans)
apply (assumption)
done

subsubsection {* Theorems for @{term "op \<prec>\<^sub>c"} *}

theorem le_imp_leq_card :
"(A \<prec>\<^sub>c B) \<Longrightarrow> (A \<preceq>\<^sub>c B)"
apply (unfold less_card_def)
apply (clarify)
done

theorem le_card_iff :
"(A \<prec>\<^sub>c B) \<longleftrightarrow> \<not> (B \<preceq>\<^sub>c A)"
apply (unfold less_card_def equal_card_def)
apply (metis leq_card_linear)
done

theorem le_card_cases :
"(A \<prec>\<^sub>c B) \<or> (B \<prec>\<^sub>c A) \<or> (A \<equiv>\<^sub>c B)"
apply (simp add: le_card_iff)
apply (simp add: equal_card_def)
done

theorem le_card_trans :
"\<lbrakk>(A \<prec>\<^sub>c B); (B \<prec>\<^sub>c C)\<rbrakk> \<Longrightarrow> (A \<prec>\<^sub>c C)"
apply (simp add: le_card_iff)
apply (metis leq_card_linear leq_card_trans)
done

subsubsection {* Theorems for @{term "c\<^sub>f"} *}

theorem fin_card_mono :
"n \<le> m \<Longrightarrow> c\<^sub>f n \<preceq>\<^sub>c c\<^sub>f m"
apply (unfold fin_card_def)
apply (unfold leq_card_def)
apply (rule_tac x = "id" in exI)
apply (clarsimp)
done

theorem fin_le_nat_card :
"c\<^sub>f n \<prec>\<^sub>c c\<^sub>\<nat>"
apply (subst le_card_iff)
apply (unfold card_defs)
apply (unfold leq_card_def)
apply (simp add: UNIV_TYPE_def)
apply (clarify)
apply (drule range_inj_infinite)
apply (drule infinite_super)
apply (assumption)
apply (simp)
done

theorem fin_leq_nat_card :
"c\<^sub>f n \<preceq>\<^sub>c c\<^sub>\<nat>"
apply (rule le_imp_leq_card)
apply (rule fin_le_nat_card)
done

subsubsection {* Theorems for @{term "c\<^sub>\<bool>"} *}

theorem bool_eq_fin_card :
"c\<^sub>\<bool> \<equiv>\<^sub>c c\<^sub>f 2"
apply (unfold equal_card_def leq_card_def)
apply (unfold card_defs)
apply (simp add: UNIV_TYPE_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "(\<lambda> b . if b then 1 else 2)" in exI)
apply (rule conjI)
-- {* Subgoal 1.1 *}
apply (rule injI)
apply (simp only: atomize_imp)
apply (induct_tac x)
apply (induct_tac y)
apply (simp_all)
-- {* Subgoal 1.2 *}
apply (auto) [1]
-- {* Subgoal 2 *}
apply (rule_tac x = "(\<lambda> n . n = 1)" in exI)
apply (rule inj_onI)
apply (clarsimp)
apply (case_tac "x = 1")
apply (simp_all)
done

subsubsection {* Theorems for @{term "c\<^sub>\<nat>"} *}

theorem countable_leq_nat_card :
"countable c \<Longrightarrow> c \<preceq>\<^sub>c c\<^sub>\<nat>"
apply (unfold nat_card_def type_card_def)
apply (unfold UNIV_TYPE_def)
apply (unfold leq_card_def)
apply (simp add: countable_def)
done

theorem infinite_nat_card_leq :
"infinite c \<Longrightarrow> c\<^sub>\<nat> \<preceq>\<^sub>c c"
apply (unfold nat_card_def type_card_def)
apply (unfold UNIV_TYPE_def)
apply (unfold leq_card_def)
apply (erule infinite_countable_subset)
done

theorem countable_infinite_eq_nat_card :
"countable c \<Longrightarrow> infinite c \<Longrightarrow> c \<equiv>\<^sub>c c\<^sub>\<nat>"
apply (drule countable_leq_nat_card)
apply (drule infinite_nat_card_leq)
apply (simp add: equal_card_def)
done

theorem leq_type_card_inj :
"c\<^sub>\<T> TYPE('a) \<preceq>\<^sub>c c\<^sub>\<T> TYPE('b) \<longleftrightarrow> (\<exists> f :: 'a \<Rightarrow> 'b . inj f)"
apply (unfold type_card_def)
apply (unfold UNIV_TYPE_def)
apply (simp add: leq_card_def)
done

theorem eq_type_card_bij :
"c\<^sub>\<T> TYPE('a) \<equiv>\<^sub>c c\<^sub>\<T> TYPE('b) \<longleftrightarrow> (\<exists> f :: 'a \<Rightarrow> 'b . bij f)"
apply (unfold type_card_def)
apply (unfold UNIV_TYPE_def)
apply (simp add: equal_card_bij_betw)
done

theorem countable_infinite_inj_ex :
"countable (c\<^sub>\<T> TYPE('a)) \<Longrightarrow>
 infinite (c\<^sub>\<T> TYPE('b)) \<Longrightarrow>
 (\<exists> f :: 'a \<Rightarrow> 'b . inj f)"
apply (fold leq_type_card_inj)
apply (drule countable_leq_nat_card)
apply (drule infinite_nat_card_leq)
apply (metis leq_card_trans)
done

theorem countable_infinite_bij_ex :
"countable (c\<^sub>\<T> TYPE('a)) \<Longrightarrow> infinite (c\<^sub>\<T> TYPE('a)) \<Longrightarrow>
 countable (c\<^sub>\<T> TYPE('b)) \<Longrightarrow> infinite (c\<^sub>\<T> TYPE('b)) \<Longrightarrow>
 (\<exists> f :: 'a \<Rightarrow> 'b . bij f)"
apply (fold eq_type_card_bij)
apply (drule countable_infinite_eq_nat_card)
apply (assumption)
apply (drule countable_infinite_eq_nat_card)
apply (assumption)
apply (metis equal_card_sym equal_card_trans)
done

theorem countable_type_leq_nat_card [simp] :
"(c :: 'a::countable set) \<preceq>\<^sub>c c\<^sub>\<nat>"
apply (rule countable_leq_nat_card)
apply (rule countableI_type)
done

theorem countable_infinite_type_inj_ex :
"(\<exists> f :: 'a::countable \<Rightarrow> 'b::infinite . inj f)"
apply (rule countable_infinite_inj_ex)
apply (unfold type_card_def)
apply (unfold UNIV_TYPE_def)
apply (simp_all)
done

theorem countable_infinite_type_bij_ex :
"(\<exists> f :: 'a::{countable,infinite} \<Rightarrow> 'b::{countable,infinite} . bij f)"
apply (rule countable_infinite_bij_ex)
apply (unfold type_card_def)
apply (unfold UNIV_TYPE_def)
apply (simp_all)
done
end
