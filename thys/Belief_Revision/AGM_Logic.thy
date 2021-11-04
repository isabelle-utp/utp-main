(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : AGM Theory
 * Version         : 1.0
 *
 * Authors         : Valentin Fouillard, Safouan Taha, Frederic Boulanger
                     and Nicolas Sabouret
 *
 * This file       : AGM logics
 *
 * Copyright (c) 2021 Université Paris Saclay, France
 *
 ******************************************************************************\<close>

theory AGM_Logic

imports Main

begin
(*>*)

section \<open>Introduction\<close>

text\<open>
The 1985 paper by Carlos Alchourrón, Peter Gärdenfors,
and David Makinson (AGM), “On the Logic of Theory Change: Partial Meet
Contraction and Revision Functions” @{cite "alchourron1985logic"} launches a large and
rapidly growing literature that employs formal models and logics to handle changing beliefs of a rational agent
and to take into account new piece of information observed by this agent. 
In 2011, a review book titled "AGM 25 Years: Twenty-Five Years of Research in Belief Change"
was edited to summarize the first twenty five years of works based on AGM 
@{cite "Ferme2011"}.

According to Google Scholar, the original AGM paper was cited 4000 times! 
This AFP entry is HOL-based and it is a faithful formalization of the logic operators (e.g. contraction, revision, remainder \dots )
axiomatized in the AGM paper. It also contains the proofs of all the theorems stated in the paper that show how these operators combine.
Both proofs of Harper and Levi identities are established.
\<close>

text\<open>A belief state can be considered as a consistent set of beliefs (logical propositions) closed under logical reasoning.
Belief changes represent the operations that apply on a belief state to remove some of it and/or to add new beliefs (propositions). 
In the latter case, it is possible that other beliefs are affected by these changes (to preserve consistency for example). 
AGM define several postulates to guarantee that such operations preserve consistency meaning that the agent keeps rational. 
Three kinds of operators are defined :
\<^item> The contraction @{text \<open>\<div>\<close>} : where a proposition is removed from a belief set
\<^item> The expansion @{text \<open>\<oplus>\<close>} : where a proposition is added to a belief set
\<^item> The revision @{text \<open>\<^bold>*\<close>} : where a proposition is added to a belief set such that the belief set remains consistent
\<close>

text\<open>In this AFP entry, there are three theory files: 
\<^enum> The AGM Logic file contains a classification of logics used in the AGM framework.
\<^enum> The AGM Remainder defines a important operator used in the AGM framework.
\<^enum> The AGM Contraction file contains the postulates of the AGM contraction and its relation with the meet contraction.
\<^enum> The AGM Revision file contains the postulates of the AGM revision and its relation with the meet revision.  
\<close>

section \<open>Logics\<close>

text\<open>The AGM framework depends on the underlying logic used to express beliefs. AGM requires at least a Tarskian propositional calculus. 
If this logic is also supra-classical and/or compact, new properties are established and the main theorems of AGM are strengthened. 
To model AGM it is therefore important to start by formalizing this underlying logic and its various extensions. 
We opted for a deep embedding in HOL which required the redefinition of all the logical operators and an axiomatization of their rules. 
This is certainly not efficient in terms of proof but it gives a total control of our formalization and an assurance 
that the logic used has no hidden properties depending on the Isabelle/HOL implementation. 
We use the Isabelle \<^emph>\<open>locales\<close> feature and we take advantage of the inheritance/extension mechanisms between locales.\<close>


subsection \<open>Tarskian Logic\<close>

text \<open>
The first locale formalizes a Tarskian logic based on the famous Tarski's consequence operator: @{term \<open>Cn(A)\<close>} 
which gives the set of all propositions (\<^bold>\<open>closure\<close>) that can be inferred from the set of propositions @{term \<open>A\<close>}, 
Exactly as it is classically axiomatized in the literature, three assumptions of the locale define the consequence operator.
\<close>
locale Tarskian_logic =
fixes Cn::\<open>'a set \<Rightarrow> 'a set\<close>
assumes monotonicity_L:     \<open>A \<subseteq> B \<Longrightarrow> Cn(A) \<subseteq> Cn(B)\<close>
    and inclusion_L:        \<open>A \<subseteq> Cn(A)\<close> 
    and transitivity_L:     \<open>Cn(Cn(A)) \<subseteq> Cn(A)\<close>

\<comment> \<open>
  Short notation for ``@{term \<open>\<phi>\<close>} can be inferred from the propositions in @{term \<open>A\<close>}''.
\<close>
fixes infer::\<open>'a set \<Rightarrow> 'a \<Rightarrow> bool\<close>  (infix \<open>\<turnstile>\<close> 50)
defines \<open>A \<turnstile> \<phi> \<equiv> \<phi> \<in> Cn(A)\<close>

\<comment> \<open>
  @{term \<open>\<phi>\<close>} is valid (a tautology) if it can be inferred from nothing.
\<close>
fixes valid::\<open>'a \<Rightarrow> bool\<close>            (\<open>\<tturnstile>\<close>)
defines \<open>\<tturnstile> \<phi> \<equiv> {} \<turnstile> \<phi>\<close>

\<comment> \<open>
  @{term \<open>A \<oplus> \<phi>\<close>} is all that can be infered from  @{term \<open>A\<close>} and  @{term \<open>\<phi>\<close>}.
\<close>
fixes expansion::\<open>'a set \<Rightarrow> 'a \<Rightarrow> 'a set\<close> (infix \<open>\<oplus>\<close> 57)
defines \<open>A \<oplus> \<phi> \<equiv> Cn(A \<union> {\<phi>})\<close>

begin 

lemma idempotency_L: \<open>Cn(Cn(A)) = Cn(A)\<close>
  by (simp add: inclusion_L transitivity_L subset_antisym)

lemma assumption_L: \<open>\<phi> \<in> A \<Longrightarrow> A \<turnstile> \<phi>\<close>
  using inclusion_L infer_def by blast 

lemma validD_L: \<open>\<tturnstile> \<phi> \<Longrightarrow> \<phi> \<in> Cn(A)\<close>
  using monotonicity_L valid_def infer_def by fastforce

lemma valid_expansion: \<open>K = Cn(A) \<Longrightarrow> \<tturnstile> \<phi> \<Longrightarrow> K \<oplus> \<phi> = K\<close>
  by (simp add: idempotency_L insert_absorb validD_L valid_def expansion_def)

lemma transitivity2_L:
  assumes \<open>\<forall>\<phi> \<in> B. A \<turnstile> \<phi>\<close>
      and \<open>B \<turnstile> \<psi>\<close>
    shows \<open>A \<turnstile> \<psi>\<close>
proof -
  from assms(1) have \<open>B \<subseteq> Cn(A)\<close> by (simp add: infer_def subsetI)
  hence \<open>Cn(B) \<subseteq> Cn(A)\<close>  using idempotency_L monotonicity_L by blast
  moreover from assms(2) have \<open>\<psi> \<in> Cn(B)\<close> by (simp add: infer_def)
  ultimately show ?thesis using infer_def by blast
qed

lemma Cn_same: \<open>(Cn(A) = Cn(B)) \<longleftrightarrow> (\<forall>C. A \<subseteq> Cn(C) \<longleftrightarrow> B \<subseteq> Cn(C))\<close>
proof
  { assume h:\<open>Cn(A) = Cn(B)\<close>
    from h have \<open>\<forall>\<phi> \<in> B. A \<turnstile> \<phi>\<close> 
      by (simp add: Tarskian_logic.assumption_L Tarskian_logic_axioms infer_def)
    moreover from h[symmetric] have \<open>\<forall>\<phi> \<in> A. B \<turnstile> \<phi>\<close>
      by (simp add: Tarskian_logic.assumption_L Tarskian_logic_axioms infer_def)
    ultimately have \<open>\<forall>C. A \<subseteq> Cn(C) \<longleftrightarrow> B \<subseteq> Cn(C)\<close>
      using h idempotency_L inclusion_L monotonicity_L by blast
  } thus \<open>Cn(A) = Cn(B) \<Longrightarrow> \<forall>C. (A \<subseteq> Cn(C)) = (B \<subseteq> Cn(C))\<close> .
next
  { assume h:\<open>\<forall>C. (A \<subseteq> Cn(C)) = (B \<subseteq> Cn(C))\<close>
    from h have \<open>(A \<subseteq> Cn(A)) = (B \<subseteq> Cn(A))\<close> and \<open>(A \<subseteq> Cn(B)) = (B \<subseteq> Cn(B))\<close> by simp+
    hence \<open>B \<subseteq> Cn(A)\<close> and \<open>A \<subseteq> Cn(B)\<close> by (simp add: inclusion_L)+
    hence \<open>Cn(A) = Cn(B)\<close>
      using idempotency_L monotonicity_L by blast
  } thus \<open>(\<forall>C. (A \<subseteq> Cn(C)) = (B \<subseteq> Cn(C))) \<Longrightarrow> Cn(A) = Cn(B)\<close> .
qed

\<comment> \<open>
The closure of the union of two consequence closures.
\<close>
lemma Cn_union: \<open>Cn(Cn(A) \<union> Cn(B)) = Cn(A \<union> B)\<close>
proof
  have \<open>Cn(Cn(A) \<union> Cn(B)) \<subseteq> Cn(Cn (A \<union> B))\<close> by (simp add: monotonicity_L)
  thus \<open>Cn(Cn(A) \<union> Cn(B)) \<subseteq> Cn(A \<union> B)\<close> by (simp add: idempotency_L)
next
  have \<open>(A \<union> B) \<subseteq> (Cn(A) \<union> Cn(B))\<close> using inclusion_L by blast
  thus \<open>Cn(A \<union> B) \<subseteq> Cn(Cn(A) \<union> Cn(B))\<close> by (simp add: monotonicity_L)
qed

\<comment> \<open>
The closure of an infinite union of consequence closures.
\<close>
lemma Cn_Union: \<open>Cn(\<Union>{Cn(B)|B. P B}) = Cn(\<Union>{B. P B})\<close> (is \<open>?A = ?B\<close>)
proof
  have \<open>?A \<subseteq> Cn ?B\<close>
    apply(rule monotonicity_L, rule Union_least, auto) 
    by (metis Sup_upper in_mono mem_Collect_eq monotonicity_L)
  then show \<open>?A \<subseteq> ?B\<close>
    by (simp add: idempotency_L)
next
  show \<open>?B \<subseteq> ?A\<close> 
    by (metis (mono_tags, lifting) Union_subsetI inclusion_L mem_Collect_eq monotonicity_L)
qed

\<comment> \<open>
The intersection of two closures is closed.
\<close>
lemma Cn_inter: \<open>K = Cn(A) \<inter> Cn(B) \<Longrightarrow> K = Cn(K)\<close>
proof -
  { fix K assume h:\<open>K = Cn(A) \<inter> Cn(B)\<close>
    from h have \<open>K \<subseteq> Cn(A)\<close> and \<open>K \<subseteq> Cn(B)\<close> by simp+
    hence \<open>Cn(K) \<subseteq> Cn(A)\<close> and \<open>Cn(K) \<subseteq> Cn(B)\<close> using idempotency_L monotonicity_L by blast+
    hence \<open>Cn(K) \<subseteq> Cn(A) \<inter> Cn(B)\<close> by simp
    with h have \<open>K = Cn(K)\<close> by (simp add: inclusion_L subset_antisym)
  } thus \<open>K = Cn(A) \<inter> Cn(B) \<Longrightarrow> K = Cn(K)\<close> .
qed

\<comment> \<open>
An infinite intersection of closures is closed.
\<close>
lemma Cn_Inter: \<open>K = \<Inter>{Cn(B)|B. P B} \<Longrightarrow> K = Cn(K)\<close>
proof -
  { fix K assume h:\<open>K = \<Inter>{Cn(B)|B. P B}\<close>
    from h have \<open>\<forall>B. P B \<longrightarrow> K \<subseteq> Cn(B)\<close> by blast
    hence \<open>\<forall>B. P B \<longrightarrow> Cn(K) \<subseteq> Cn(B)\<close> using idempotency_L monotonicity_L by blast
    hence \<open>Cn(K) \<subseteq> \<Inter>{Cn(B)|B. P B}\<close> by blast
    with h have \<open>K = Cn(K)\<close> by (simp add: inclusion_L subset_antisym)
  } thus \<open>K = \<Inter>{Cn(B)|B. P B} \<Longrightarrow> K = Cn(K)\<close> .
qed

end

subsection \<open>Supraclassical Logic\<close>

text \<open>
A Tarskian logic has only one abstract operator catching the notion of consequence. A basic case of such a logic is a \<^bold>\<open>Supraclassical\<close> logic that 
is a logic with all classical propositional operators (e.g. conjunction (\<open>\<and>\<close>), implication(\<open>\<longrightarrow>\<close>), negation (\<open>\<not>\<close>) \dots ) together with their classical semantics.

We define a new locale. In order to distinguish the propositional operators of our supraclassical logic from those of Isabelle/HOL, we use dots (e.g. \<open>.\<and>.\<close> stands for conjunction). 
We axiomatize the introduction and elimination rules of each operator as it is commonly established in the classical literature. As explained before, 
we give priority to a complete control of our logic instead of an efficient shallow embedding in Isabelle/HOL.
\<close>

locale Supraclassical_logic = Tarskian_logic +

fixes true_PL::   \<open>'a\<close>             (\<open>\<top>\<close>)
  and false_PL::  \<open>'a\<close>             (\<open>\<bottom>\<close>)
  and imp_PL::    \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infix \<open>.\<longrightarrow>.\<close> 55)
  and not_PL::    \<open>'a \<Rightarrow> 'a\<close>       (\<open>.\<not>\<close>)  
  and conj_PL::   \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infix \<open>.\<and>.\<close> 55)
  and disj_PL::   \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infix \<open>.\<or>.\<close> 55)
  and equiv_PL::  \<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> (infix \<open>.\<longleftrightarrow>.\<close> 55)

assumes true_PL:     \<open>A \<turnstile> \<top>\<close>

    and false_PL:    \<open>{\<bottom>} \<turnstile> p\<close>

    and impI_PL:     \<open>A \<union> {p} \<turnstile> q \<Longrightarrow> A \<turnstile> (p .\<longrightarrow>. q)\<close>
    and mp_PL:       \<open>A \<turnstile> p .\<longrightarrow>. q \<Longrightarrow> A \<turnstile> p \<Longrightarrow> A \<turnstile> q\<close>

    and notI_PL:     \<open>A \<turnstile> p .\<longrightarrow>. \<bottom> \<Longrightarrow> A \<turnstile> .\<not> p\<close>
    and notE_PL:     \<open>A \<turnstile> .\<not> p \<Longrightarrow> A \<turnstile> (p .\<longrightarrow>. \<bottom>)\<close>

    and conjI_PL:    \<open>A \<turnstile> p \<Longrightarrow> A \<turnstile> q \<Longrightarrow> A \<turnstile> (p .\<and>. q)\<close>
    and conjE1_PL:   \<open>A \<turnstile> p .\<and>. q \<Longrightarrow> A \<turnstile> p\<close>
    and conjE2_PL:   \<open>A \<turnstile> p .\<and>. q \<Longrightarrow> A \<turnstile> q\<close>

    and disjI1_PL:   \<open>A \<turnstile> p \<Longrightarrow> A \<turnstile> (p .\<or>. q)\<close>
    and disjI2_PL:   \<open>A \<turnstile> q \<Longrightarrow> A \<turnstile> (p .\<or>. q)\<close>
    and disjE_PL:    \<open>A \<turnstile> p .\<or>. q \<Longrightarrow> A \<turnstile> p .\<longrightarrow>. r \<Longrightarrow> A \<turnstile> q.\<longrightarrow>. r \<Longrightarrow> A \<turnstile> r\<close>

    and equivI_PL:   \<open>A \<turnstile> p .\<longrightarrow>. q \<Longrightarrow> A \<turnstile> q .\<longrightarrow>. p \<Longrightarrow> A \<turnstile> (p .\<longleftrightarrow>. q)\<close>
    and equivE1_PL:  \<open>A \<turnstile> p .\<longleftrightarrow>. q \<Longrightarrow> A \<turnstile> p .\<longrightarrow>. q\<close>
    and equivE2_PL:  \<open>A \<turnstile> p .\<longleftrightarrow>. q \<Longrightarrow> A \<turnstile> q .\<longrightarrow>. p\<close>

\<comment> \<open>non intuitionistic rules\<close>
    and absurd_PL:   \<open>A \<turnstile> .\<not> (.\<not> p) \<Longrightarrow> A \<turnstile> p\<close>
    and ex_mid_PL:   \<open>A \<turnstile> p .\<or>. (.\<not> p)\<close>

begin 

text \<open>In the following, we will first retrieve the classical logic operators semantics coming from previous introduction and elimination rules\<close>

lemma non_consistency:
  assumes \<open>A \<turnstile> .\<not> p\<close>
      and \<open>A \<turnstile> p\<close>
    shows \<open>A \<turnstile> q\<close>
  by (metis assms(1) assms(2) false_PL mp_PL notE_PL singleton_iff transitivity2_L)

\<comment> \<open>this direct result brings directly many remarkable properties of implication (i.e. transitivity)\<close>
lemma imp_PL: \<open>A \<turnstile> p .\<longrightarrow>. q \<longleftrightarrow> A \<union> {p} \<turnstile> q\<close>
  apply (intro iffI impI_PL)
   apply(rule mp_PL[where p=p], meson UnI1 assumption_L transitivity2_L)
  using assumption_L by auto

lemma not_PL: \<open>A \<turnstile> .\<not> p \<longleftrightarrow> A \<union> {p} \<turnstile> \<bottom>\<close>
  using notE_PL notI_PL imp_PL by blast

\<comment> \<open>Classical logic result\<close>
lemma notnot_PL: \<open>A \<turnstile> .\<not> (.\<not> p) \<longleftrightarrow> A \<turnstile> p\<close>
  apply(rule iffI, simp add:absurd_PL) 
  by (meson mp_PL notE_PL Un_upper1 Un_upper2 assumption_L infer_def monotonicity_L not_PL singletonI subsetD)

lemma conj_PL: \<open>A \<turnstile> p .\<and>. q \<longleftrightarrow> (A \<turnstile> p \<and> A \<turnstile> q)\<close>
  using conjE1_PL conjE2_PL conjI_PL by blast 

lemma disj_PL: \<open>A \<turnstile> p .\<or>. q \<longleftrightarrow> A \<union> {.\<not> p} \<turnstile> q\<close>
proof
  assume a:\<open>A \<turnstile> p .\<or>. q\<close>
  have b:\<open>A \<turnstile> p .\<longrightarrow>. (.\<not> p .\<longrightarrow>. q)\<close> 
    by (intro impI_PL) (meson Un_iff assumption_L insertI1 non_consistency)
  have c:\<open>A \<turnstile> q .\<longrightarrow>. (.\<not> p .\<longrightarrow>. q)\<close> 
    by (simp add: assumption_L impI_PL)
  from a b c have \<open>A \<turnstile> .\<not> p .\<longrightarrow>. q\<close>
    by (erule_tac disjE_PL) simp_all
  then show \<open>A \<union> {.\<not> p} \<turnstile> q\<close> 
    using imp_PL by blast
next 
  assume a:\<open>A \<union> {.\<not> p} \<turnstile> q\<close>
  hence b:\<open>A \<turnstile> .\<not> p .\<longrightarrow>. q\<close> by (simp add: impI_PL)
  then show \<open>A \<turnstile> p .\<or>. q\<close> 
    apply(rule_tac disjE_PL[OF ex_mid_PL, of A p \<open>p .\<or>. q\<close>]) 
    by (auto simp add: assumption_L disjI2_PL disjI1_PL impI_PL imp_PL) 
qed

lemma equiv_PL:\<open>A \<turnstile> p .\<longleftrightarrow>. q \<longleftrightarrow> (A \<union> {p} \<turnstile> q \<and> A \<union> {q} \<turnstile> p)\<close>
  using imp_PL equivE1_PL equivE2_PL equivI_PL by blast

corollary valid_imp_PL:  \<open>\<tturnstile> (p .\<longrightarrow>. q) = ({p} \<turnstile> q)\<close>
      and valid_not_PL:  \<open>\<tturnstile> (.\<not> p) = ({p} \<turnstile> \<bottom>)\<close>
      and valid_conj_PL: \<open>\<tturnstile> (p .\<and>. q) = (\<tturnstile> p \<and> \<tturnstile> q)\<close>
      and valid_disj_PL: \<open>\<tturnstile> (p .\<or>. q) = ({.\<not> p} \<turnstile> q)\<close>
      and valid_equiv_PL:\<open>\<tturnstile> (p .\<longleftrightarrow>. q) = ({p} \<turnstile> q \<and> {q} \<turnstile> p)\<close>
  using imp_PL not_PL conj_PL disj_PL equiv_PL valid_def by auto

text\<open>Second, we will combine each logical operator with the consequence operator \<open>Cn\<close>: it is a trick to profit from set theory to get many essential 
lemmas without complex inferences\<close>
declare infer_def[simp]

lemma nonemptyCn: \<open>Cn(A) \<noteq> {}\<close>
  using true_PL by auto

lemma Cn_true: \<open>Cn({\<top>}) = Cn({})\<close>
  using Cn_same true_PL by auto

lemma Cn_false: \<open>Cn({\<bottom>}) = UNIV\<close> 
  using false_PL by auto

lemma Cn_imp:     \<open>A \<turnstile> (p .\<longrightarrow>. q) \<longleftrightarrow> Cn({q}) \<subseteq> Cn(A \<union> {p})\<close> 
  and Cn_imp_bis: \<open>A \<turnstile> (p .\<longrightarrow>. q) \<longleftrightarrow> Cn(A \<union> {q}) \<subseteq> Cn(A \<union> {p})\<close> 
  using Cn_same imp_PL idempotency_L inclusion_L infer_def subset_insertI by force+

lemma Cn_not: \<open>A \<turnstile> .\<not> p \<longleftrightarrow> Cn(A \<union> {p}) = UNIV\<close>
  using Cn_false Cn_imp notE_PL not_PL by fastforce

lemma Cn_conj: \<open>A \<turnstile> (p .\<and>. q) \<longleftrightarrow> Cn({p}) \<union> Cn({q}) \<subseteq> Cn(A)\<close>
  apply(intro iffI conjI_PL, frule conjE1_PL, frule conjE2_PL) 
  using Cn_same Un_insert_right bot.extremum idempotency_L inclusion_L by auto

lemma Cn_conj_bis: \<open>Cn({p .\<and>. q}) = Cn({p, q})\<close> 
  by (unfold Cn_same)
     (meson Supraclassical_logic.conj_PL Supraclassical_logic_axioms insert_subset)

lemma Cn_disj:     \<open>A \<turnstile> (p .\<or>. q) \<longleftrightarrow> Cn({q}) \<subseteq> Cn(A \<union> {.\<not> p})\<close>
  and Cn_disj_bis: \<open>A \<turnstile> (p .\<or>. q) \<longleftrightarrow> Cn(A \<union> {q}) \<subseteq> Cn(A \<union> {.\<not> p})\<close>
  using disj_PL Cn_same imp_PL idempotency_L inclusion_L infer_def subset_insertI by force+

lemma Cn_equiv: \<open>A \<turnstile> (p .\<longleftrightarrow>. q) \<longleftrightarrow> Cn(A \<union> {p}) = Cn(A \<union> {q})\<close>
  by (metis Cn_imp_bis equivE1_PL equivE2_PL equivI_PL set_eq_subset)

corollary valid_nonemptyCn: \<open>Cn({}) \<noteq> {}\<close>
      and valid_Cn_imp:     \<open>\<tturnstile> (p .\<longrightarrow>. q) \<longleftrightarrow> Cn({q}) \<subseteq> Cn({p})\<close> 
      and valid_Cn_not:     \<open>\<tturnstile> (.\<not> p) \<longleftrightarrow> Cn({p}) = UNIV\<close>
      and valid_Cn_conj:    \<open>\<tturnstile> (p .\<and>. q) \<longleftrightarrow> Cn({p}) \<union> Cn({q}) \<subseteq> Cn({})\<close>
      and valid_Cn_disj:    \<open>\<tturnstile> (p .\<or>. q) \<longleftrightarrow> Cn({q}) \<subseteq> Cn({.\<not> p})\<close>
      and valid_Cn_equiv:   \<open>\<tturnstile> (p .\<longleftrightarrow>. q) \<longleftrightarrow> Cn({p}) = Cn({q})\<close>
  using nonemptyCn Cn_imp Cn_not Cn_conj Cn_disj Cn_equiv valid_def by auto

\<comment> \<open>Finally, we group additional lemmas that were essential in further proofs\<close>
lemma consistency: \<open>Cn({p}) \<inter> Cn({.\<not> p}) = Cn({})\<close>
proof
  { fix q
    assume \<open>{p} \<turnstile> q\<close> and \<open>{.\<not> p} \<turnstile> q\<close>
    hence "{} \<turnstile> p .\<longrightarrow>. q" and "{} \<turnstile> (.\<not> p) .\<longrightarrow>. q" 
      using impI_PL by auto
    hence \<open>{} \<turnstile> q\<close> 
      using ex_mid_PL by (rule_tac disjE_PL[where p=p and q=\<open>.\<not> p\<close>]) blast   
  }
  then show \<open>Cn({p}) \<inter> Cn({.\<not> p}) \<subseteq> Cn({})\<close> by (simp add: subset_iff)
next
  show \<open>Cn({}) \<subseteq> Cn({p}) \<inter> Cn({.\<not> p})\<close> by (simp add: monotonicity_L)
qed

lemma Cn_notnot: \<open>Cn({.\<not> (.\<not> \<phi>)}) = Cn({\<phi>})\<close> 
  by (metis (no_types, hide_lams) notnot_PL valid_Cn_equiv valid_equiv_PL) 

lemma conj_com: \<open>A \<turnstile> p .\<and>. q \<longleftrightarrow> A \<turnstile> q .\<and>. p\<close>
  using conj_PL by auto

lemma conj_com_Cn: \<open>Cn({p .\<and>. q}) = Cn({q .\<and>. p})\<close>
  by (simp add: Cn_conj_bis insert_commute) 

lemma disj_com: \<open>A \<turnstile> p .\<or>. q \<longleftrightarrow> A \<turnstile> q .\<or>. p\<close>
proof -
  { fix p q
    have \<open>A \<turnstile> p .\<or>. q \<Longrightarrow> A \<turnstile> q .\<or>. p\<close>
      apply(erule disjE_PL) 
      using assumption_L disjI2_PL disjI1_PL impI_PL by auto 
  }
  then show ?thesis by auto
qed

lemma disj_com_Cn: \<open>Cn({p .\<or>. q}) = Cn({q .\<or>. p})\<close>
  unfolding Cn_same using disj_com by simp

lemma imp_contrapos: \<open>A \<turnstile> p .\<longrightarrow>. q \<longleftrightarrow> A \<turnstile> .\<not> q .\<longrightarrow>. .\<not> p\<close>
  by (metis Cn_not Un_insert_left Un_insert_right imp_PL notnot_PL)

lemma equiv_negation: \<open>A \<turnstile> p .\<longleftrightarrow>. q \<longleftrightarrow> A \<turnstile> .\<not> p .\<longleftrightarrow>. .\<not> q\<close>
  using equivE1_PL equivE2_PL equivI_PL imp_contrapos by blast

lemma imp_trans: \<open>A \<turnstile> p .\<longrightarrow>.q \<Longrightarrow> A \<turnstile> q .\<longrightarrow>.r \<Longrightarrow> A \<turnstile> p .\<longrightarrow>.r\<close>
  using Cn_imp_bis by auto

lemma imp_recovery0: \<open>A \<turnstile> p .\<or>. (p .\<longrightarrow>. q)\<close>
  apply(subst disj_PL, subst imp_contrapos)
  using assumption_L impI_PL by auto

lemma imp_recovery1: \<open>A \<union> {p .\<longrightarrow>. q} \<turnstile> p \<Longrightarrow> A \<turnstile> p\<close>
  using disjE_PL[OF imp_recovery0, of A p p q] assumption_L imp_PL by auto

lemma imp_recovery2: \<open>A \<turnstile> p .\<longrightarrow>. q \<Longrightarrow> A \<turnstile> (q .\<longrightarrow>. p) .\<longrightarrow>. p \<Longrightarrow> A \<turnstile> q\<close>
  using imp_PL imp_recovery1 imp_trans by blast

lemma impI2: \<open>A \<turnstile> q \<Longrightarrow> A \<turnstile> p .\<longrightarrow>. q\<close> 
  by (meson assumption_L impI_PL in_mono sup_ge1 transitivity2_L)

lemma conj_equiv: \<open>A \<turnstile> p \<Longrightarrow> A \<turnstile> ((p .\<and>. q) .\<longleftrightarrow>. q)\<close>
  by (metis Un_insert_right assumption_L conjE2_PL conjI_PL equiv_PL impI2 imp_PL insertI1 sup_bot.right_neutral)

lemma conj_imp: \<open>A \<turnstile> (p .\<and>. q) .\<longrightarrow>. r \<longleftrightarrow> A \<turnstile> p .\<longrightarrow>. (q .\<longrightarrow>. r)\<close>
proof
  assume "A \<turnstile> (p .\<and>. q) .\<longrightarrow>. r"
  then have "Cn (A \<union> {r}) \<subseteq> Cn (A \<union> {p, q})"
    by (metis (no_types) Cn_conj_bis Cn_imp_bis Cn_union Un_insert_right sup_bot.right_neutral)
  then show \<open>A \<turnstile> p .\<longrightarrow>. (q .\<longrightarrow>. r)\<close>
    by (metis Un_insert_right impI_PL inclusion_L infer_def insert_commute insert_subset subset_eq sup_bot.right_neutral)
next
   assume "A \<turnstile> p .\<longrightarrow>. (q .\<longrightarrow>. r)"
  then have "A \<union> {p} \<union> {q} \<turnstile> r"
    using imp_PL by auto
  then show "A \<turnstile> (p .\<and>. q) .\<longrightarrow>. r"
    by (metis (full_types) Cn_conj_bis Cn_union impI_PL infer_def insert_is_Un sup_assoc)
qed

lemma conj_not_impE_PL: \<open>A \<turnstile> (p .\<and>. q) .\<longrightarrow>. r \<Longrightarrow> A \<turnstile> (p .\<and>. .\<not> q) .\<longrightarrow>. r \<Longrightarrow> A \<turnstile> p .\<longrightarrow>. r\<close> 
  by (meson conj_imp disjE_PL ex_mid_PL imp_PL)

lemma disj_notE_PL: \<open>A \<turnstile> q \<Longrightarrow> A \<turnstile> p .\<or>. .\<not> q \<Longrightarrow> A \<turnstile> p\<close>
  using Cn_imp Cn_imp_bis Cn_not disjE_PL notnot_PL by blast

lemma disj_not_impE_PL: \<open>A \<turnstile> (p .\<or>. q) .\<longrightarrow>. r \<Longrightarrow> A \<turnstile> (p .\<or>. .\<not> q) .\<longrightarrow>. r \<Longrightarrow> A \<turnstile> r\<close> 
  by (metis Un_insert_right disjE_PL disj_PL disj_com ex_mid_PL insert_commute sup_bot.right_neutral)

lemma imp_conj: \<open>A \<turnstile> p .\<longrightarrow>. q \<Longrightarrow> A \<turnstile> r .\<longrightarrow>. s \<Longrightarrow> A \<turnstile> (p .\<and>. r) .\<longrightarrow>. (q .\<and>. s)\<close>
  apply(intro impI_PL conjI_PL, unfold imp_PL[symmetric])
  by (meson assumption_L conjE1_PL conjE2_PL imp_trans infer_def insertI1 validD_L valid_imp_PL)+

lemma conj_overlap: \<open>A \<turnstile> (p .\<and>. q) \<longleftrightarrow> A \<turnstile> (p .\<and>. ((.\<not> p) .\<or>. q))\<close>
  by (meson conj_PL disjI2_PL disj_com disj_notE_PL)

lemma morgan: \<open>A \<turnstile> .\<not> (p .\<and>. q) \<longleftrightarrow> A \<turnstile> (.\<not> p) .\<or>. (.\<not> q)\<close>
  by (meson conj_imp disj_PL disj_com imp_PL imp_contrapos notE_PL notI_PL)

lemma conj_superexpansion1: \<open>A \<turnstile> .\<not> (p .\<and>. q) .\<and>. .\<not> p \<longleftrightarrow> A \<turnstile> .\<not> p\<close>
  using conj_PL disjI1_PL morgan by auto

lemma conj_superexpansion2: \<open>A \<turnstile> (p .\<or>. q) .\<and>. p \<longleftrightarrow> A \<turnstile> p\<close>
  using conj_PL disjI1_PL by auto

end

subsection \<open>Compact Logic\<close>
text\<open>If the logic is compact, which means that any result is based on a finite set of hypothesis\<close>
locale Compact_logic = Tarskian_logic +
  assumes compactness_L: \<open>A \<turnstile> \<phi> \<Longrightarrow> (\<exists>A'. A'\<subseteq> A \<and> finite A' \<and> A'\<turnstile> \<phi>)\<close>

begin

text \<open>Very important lemma preparing the application of the Zorn's lemma. It states that in a compact logic, we can not deduce \<open>\<phi>\<close>
if we accumulate an infinity of hypothesis groups which locally do not deduce phi\<close>
lemma chain_closure: \<open>\<not> \<tturnstile> \<phi> \<Longrightarrow> subset.chain {B. \<not> B \<turnstile> \<phi>} C \<Longrightarrow> \<not> \<Union>C \<turnstile> \<phi>\<close> 
proof                                    
  assume a:\<open>subset.chain {B. \<not> B \<turnstile> \<phi>} C\<close> and b:\<open>\<not> \<tturnstile> \<phi>\<close> and \<open>\<Union> C \<turnstile> \<phi>\<close>
  then obtain A' where c:\<open>A'\<subseteq> \<Union> C\<close> and d:\<open>finite A'\<close>  and e:\<open>A' \<turnstile> \<phi>\<close> using compactness_L by blast
  define f where f:\<open>f \<equiv> \<lambda>a. SOME B. B \<in> C \<and> a \<in> B\<close>
  have g:\<open>finite (f ` A')\<close> using f d by simp
  have h:\<open>(f ` A') \<subseteq> C\<close> 
    unfolding f by auto (metis (mono_tags, lifting) Union_iff c someI_ex subset_eq)
  have i:\<open>subset.chain {B. \<not> B \<turnstile> \<phi>} (f ` A')\<close> using a h
    using a h by (meson subsetD subset_chain_def subset_trans)
  have \<open>A' \<noteq> {} \<Longrightarrow> \<Union> (f ` A') \<in> {B. \<not> B \<turnstile> \<phi>}\<close> using g i 
    by (meson Union_in_chain image_is_empty subset_chain_def subset_eq)
  hence j:\<open>A' \<noteq> {} \<Longrightarrow> \<not> \<Union>(f ` A') \<turnstile> \<phi>\<close> by simp
  have \<open>A' \<subseteq> \<Union>(f ` A')\<close> 
    unfolding f by auto (metis (no_types, lifting) Union_iff c someI_ex subset_iff)
  with j e b show False
    by (metis infer_def monotonicity_L subsetD valid_def)
qed

end

end


