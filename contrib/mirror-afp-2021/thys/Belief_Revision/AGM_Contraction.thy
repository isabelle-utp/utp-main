(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : AGM Theory
 * Version         : 1.0
 *
 * Authors         : Valentin Fouillard, Safouan Taha, Frederic Boulanger
                     and Nicolas Sabouret
 *
 * This file       : AGM contraction
 *
 * Copyright (c) 2021 Université Paris Saclay, France
 *
 * All rights reserved.
 *
 ******************************************************************************\<close>

theory AGM_Contraction

imports AGM_Logic AGM_Remainder

begin
(*>*)

section \<open>Contractions\<close>
text\<open>The first operator of belief change of the AGM framework is contraction. This operator consist to remove 
a sentence @{term \<open>\<phi>\<close>} from a belief set @{term \<open>K\<close>} in such a way that @{term \<open>K\<close>} no longer imply @{term \<open>\<phi>\<close>}.

In the following we will first axiomatize such operators at different levels of logics (Tarskian, supraclassical and compact) 
and then we will give constructions satisfying these axioms. The following graph summarizes all equivalences we established:

\includegraphics[width=\textwidth]{"graph_locales.pdf"}

We will use the extension feature of locales in Isabelle/HOL to incrementally define the contraction 
operator as shown by blue arrows in the previous figure. Then, using the interpretation feature of locales, we will prove the equivalence between
descriptive and constructive approaches at each level depending on the adopted logics (black arrows).    
\<close>

subsection\<open>AGM contraction postulates\<close>
text\<open>
The operator of contraction is denoted by the symbol @{text \<open>\<div>\<close>} and respects the six following conditions :
\<^item> @{text \<open>contract_closure\<close>} : a belief set @{term \<open>K\<close>} contracted by @{term \<open>\<phi>\<close>} should be logically closed
\<^item> @{text \<open>contract_inclusion\<close>} : a contracted set @{term \<open>K\<close>} should be a subset of the original one
\<^item> @{text \<open>contract_vacuity\<close>} : if @{term \<open>\<phi>\<close>} is not included in a set @{term \<open>K\<close>} then the contraction of @{term \<open>K\<close>} by @{term \<open>\<phi>\<close>} involves no change at all
\<^item> @{text \<open>contract_success\<close>} : if a set @{term \<open>K\<close>} is contracted by @{term \<open>\<phi>\<close>} then @{term \<open>K\<close>} does not imply @{term \<open>\<phi>\<close>}
\<^item> @{text \<open>contract_recovery\<close>}: all propositions removed in a set @{term \<open>K\<close>} by contraction of @{term \<open>\<phi>\<close>} will be recovered by expansion of @{term \<open>\<phi>\<close>}
\<^item> @{text \<open>contract_extensionality\<close>} : Extensionality guarantees that the logic of contraction is extensional in the sense of allowing logically 
quivalent sentences to be freely substituted for each other\<close>
locale AGM_Contraction = Tarskian_logic +
fixes contraction::\<open>'a set \<Rightarrow> 'a \<Rightarrow> 'a set\<close> (infix \<open>\<div>\<close> 55)
assumes contract_closure:        \<open>K = Cn(A) \<Longrightarrow> K \<div> \<phi> = Cn(K \<div> \<phi>)\<close> 
    and contract_inclusion:      \<open>K = Cn(A) \<Longrightarrow> K \<div> \<phi> \<subseteq> K\<close>
    and contract_vacuity:        \<open>K = Cn(A) \<Longrightarrow> \<phi> \<notin> K \<Longrightarrow> K \<div> \<phi> = K\<close>
    and contract_success:        \<open>K = Cn(A) \<Longrightarrow> \<phi> \<notin> Cn({}) \<Longrightarrow> \<phi> \<notin> K \<div> \<phi>\<close>
    and contract_recovery:       \<open>K = Cn(A) \<Longrightarrow> K \<subseteq> ((K \<div> \<phi>) \<oplus> \<phi>)\<close>
    and contract_extensionality: \<open>K = Cn(A) \<Longrightarrow> Cn({\<phi>}) = Cn({\<psi>}) \<Longrightarrow> K \<div> \<phi> = K \<div> \<psi>\<close>


text\<open>
A full contraction is defined by two more postulates to rule the conjunction. We base on a supraclassical logic.
\<^item> @{text \<open>contract_conj_overlap\<close>} : An element in both @{text \<open>K \<div> \<phi>\<close>}  and  @{text \<open>K \<div> \<psi>\<close>}  is also an element of  @{text \<open>K \<div> (\<phi> \<and> \<psi>)\<close>}
\<^item> @{text \<open>contract_conj_inclusion\<close>} : If @{term \<open>\<phi>\<close>} not in @{text \<open>K \<div> (\<phi> \<and> \<psi>)\<close>}  then all elements removed by this contraction are also removed from @{text \<open>K \<div> \<phi>\<close>}\<close>
locale AGM_FullContraction = AGM_Contraction + Supraclassical_logic +
  assumes contract_conj_overlap:   \<open>K = Cn(A) \<Longrightarrow> (K \<div> \<phi>) \<inter> (K \<div> \<psi>) \<subseteq> (K \<div> (\<phi> .\<and>. \<psi>))\<close>
      and contract_conj_inclusion: \<open>K = Cn(A) \<Longrightarrow> \<phi> \<notin> (K \<div> (\<phi> .\<and>. \<psi>)) \<Longrightarrow> ((K \<div> (\<phi> .\<and>. \<psi>) \<subseteq> (K \<div> \<phi>)))\<close>

begin 
\<comment> \<open>two important lemmas/corollaries that can replace the two assumptions @{text \<open>contract_conj_overlap\<close>} and @{text \<open>contract_conj_inclusion\<close>}\<close>
text\<open>@{text \<open>contract_conj_overlap_variant\<close>} does not need \<open>\<psi>\<close> to occur in the left side! \<close>
corollary contract_conj_overlap_variant:  \<open>K = Cn(A) \<Longrightarrow> (K \<div> \<phi>) \<inter> Cn({\<phi>}) \<subseteq> (K \<div> (\<phi> .\<and>. \<psi>))\<close>
proof -
  assume a:\<open>K = Cn(A)\<close>
  { assume b:\<open>K \<turnstile> \<phi>\<close> and c:\<open>K \<turnstile> \<psi>\<close> 
    hence d:\<open>K \<div> (\<phi> .\<and>. \<psi>) = K \<div> (\<phi> .\<and>. ((.\<not> \<phi>) .\<or>. \<psi>))\<close> 
      apply(rule_tac contract_extensionality[OF a]) 
      using conj_overlap[of _ \<phi> \<psi>] by (simp add: Cn_same)
    have e:\<open>K \<inter> Cn {\<phi>} \<subseteq> K \<div> (.\<not> \<phi> .\<or>. \<psi>)\<close> 
    proof(safe)
      fix \<chi>
      assume f:\<open>\<chi> \<in> K\<close> and g:\<open>\<chi> \<in> Cn {\<phi>}\<close>
      have \<open>K \<div> (.\<not> \<phi> .\<or>. \<psi>) \<turnstile> (.\<not> \<phi> .\<or>. \<psi>) .\<longrightarrow>. \<chi>\<close>
        by (metis a contract_recovery expansion_def f impI_PL infer_def subset_eq)
      hence \<open>K \<div> (.\<not> \<phi> .\<or>. \<psi>) \<turnstile> .\<not> \<phi> .\<longrightarrow>. \<chi>\<close>
        by (meson disjI1_PL imp_trans inclusion_L infer_def insert_subset validD_L valid_imp_PL)
      with g show \<open>\<chi> \<in> K \<div> (.\<not> \<phi> .\<or>. \<psi>)\<close>
        by (metis a contract_closure disjE_PL ex_mid_PL infer_def validD_L valid_imp_PL)
    qed
    have ?thesis 
      unfolding d using e contract_conj_overlap[OF a, of \<phi> \<open>(.\<not> \<phi> .\<or>. \<psi>)\<close>] a contract_inclusion by force 
  }
  then show ?thesis
    apply (cases \<open>\<not> K \<turnstile> \<phi> \<or> \<not> K \<turnstile> \<psi>\<close>)  
    by (metis IntE a assumption_L conjE1_PL conjE2_PL contract_inclusion contract_vacuity subsetD subsetI) blast
qed 

text\<open>@{text \<open>contract_conj_inclusion_variant\<close>}: Everything retained in @{text \<open>K \<div> (\<phi> \<and> \<psi>)\<close>} is retained in @{text \<open>K \<div> \<psi>\<close>}\<close>
corollary contract_conj_inclusion_variant : \<open>K = Cn(A) \<Longrightarrow> (K \<div> (\<phi> .\<and>. \<psi>) \<subseteq> (K \<div> \<phi>)) \<or> (K \<div> (\<phi> .\<and>. \<psi>) \<subseteq> (K \<div> \<psi>))\<close>
proof -
  assume a:\<open>K = Cn(A)\<close>
  { assume d:\<open>\<phi> \<in> (K \<div> (\<phi> .\<and>. \<psi>)) \<and> \<psi> \<in> (K \<div> (\<phi> .\<and>. \<psi>))\<close> 
    hence \<open>\<phi> .\<and>. \<psi> \<in> (K \<div> (\<phi> .\<and>. \<psi>))\<close> 
      using Supraclassical_logic.conjI_PL Supraclassical_logic_axioms a contract_closure by fastforce
    with d have ?thesis
      by (metis (no_types, lifting) Supraclassical_logic.valid_conj_PL Supraclassical_logic_axioms 
                Tarskian_logic.valid_expansion Tarskian_logic_axioms a contract_closure contract_inclusion 
                contract_recovery contract_success dual_order.trans expansion_def)     
  }
  then show ?thesis 
    by (metis a conj_com_Cn contract_conj_inclusion contract_extensionality)
qed

end

subsection \<open>Partial meet contraction definition\<close>

text\<open>A partial meet contraction of @{term \<open>K\<close>} by @{term \<open>\<phi>\<close>} is the intersection of some sets that not imply @{term \<open>\<phi>\<close>}.
We define these sets as the "remainders" @{text \<open>(K .\<bottom>. \<phi>\<close>}.
The function of selection @{term \<open>\<gamma>\<close>} select the best set of the remainders that do not imply @{term \<open>\<phi>\<close>}.
This function respect these postulates :
\<^item> @{text \<open>is_selection\<close>} : if there exist some set that do not imply @{term \<open>\<phi>\<close>} then the function selection @{term \<open>\<gamma>\<close>} is a subset of these sets
\<^item> @{text \<open>tautology_selection\<close>} : if there is no set that do not imply @{term \<open>\<phi>\<close>} then the result of the selection function is @{term \<open>K\<close>}
\<^item> @{text nonempty_selection} : An empty selection function do not exist
\<^item> @{text extensional_selection} : Two proposition with the same closure have the same selection function\<close>
locale PartialMeetContraction = Tarskian_logic +

fixes selection::\<open>'a set \<Rightarrow> 'a  \<Rightarrow> 'a set set\<close> (\<open>\<gamma>\<close>)
assumes is_selection:          \<open>K = Cn(A) \<Longrightarrow> (K .\<bottom>. \<phi>) \<noteq> {} \<Longrightarrow> \<gamma> K \<phi> \<subseteq> (K .\<bottom>. \<phi>)\<close>
assumes tautology_selection:   \<open>K = Cn(A) \<Longrightarrow> (K .\<bottom>. \<phi>) = {} \<Longrightarrow> \<gamma> K \<phi> = {K}\<close>
assumes nonempty_selection:    \<open>K = Cn(A) \<Longrightarrow> \<gamma> K \<phi> \<noteq> {}\<close>
assumes extensional_selection: \<open>K = Cn(A) \<Longrightarrow> Cn({\<phi>}) = Cn({\<psi>}) \<Longrightarrow> \<gamma> K \<phi> = \<gamma> K \<psi>\<close>

\<comment> \<open>extensionality seems very hard to implement for a constructive approach, 
one basic implementation will be to ignore @{term \<open>A\<close>} and @{term \<open>\<phi>\<close>} 
and only base on @{text \<open>A .\<bottom>. \<phi>\<close>} that 
is already proved as extensional (lemma @{text \<open>remainder_extensionality\<close>})\<close> 

begin

text \<open>A partial meet is the intersection of set of selected element.\<close>
definition (in Tarskian_logic) meet_contraction::\<open>'a set \<Rightarrow> ('a set \<Rightarrow> 'a  \<Rightarrow> 'a set set) \<Rightarrow> 'a \<Rightarrow> 'a set\<close> (\<open>_ \<div>\<^bsub>_\<^esub> _\<close> [60,50,60]55)
  where mc: \<open>(A \<div>\<^bsub>\<gamma>\<^esub> \<phi>) \<equiv> \<Inter>(\<gamma> A \<phi>)\<close>

text \<open>Following this definition 4 postulates of AGM can be proved on a partial meet contraction:
\<^item> @{text \<open>contract_inclusion\<close>}
\<^item> @{text \<open> contract_vacuity\<close>}
\<^item> @{text \<open> contract_closure\<close>}
\<^item> @{text \<open> contract_extensionality\<close>}\<close>

text \<open>@{text \<open>pmc_inclusion\<close> } :a partial meet contraction is a subset of the contracted set\<close>
lemma pmc_inclusion: \<open>K = Cn(A) \<Longrightarrow> K \<div>\<^bsub>\<gamma>\<^esub> \<phi> \<subseteq> K\<close>
  apply (cases \<open>(K .\<bottom>. \<phi>) = {}\<close>, simp_all add: mc tautology_selection) 
  by (meson Inf_less_eq in_mono is_selection nonempty_selection rem_inclusion)

text\<open>@{text \<open>pmc_vacuity\<close>} :  if @{term \<open>\<phi>\<close>} is not included in a set @{term \<open>K\<close>} then the partial meet contraction of @{term \<open>K\<close>} by @{term \<open>\<phi>\<close>} involves not change at all\<close>
lemma pmc_vacuity: \<open>K = Cn(A) \<Longrightarrow> \<not> K \<turnstile> \<phi> \<Longrightarrow> K \<div>\<^bsub>\<gamma>\<^esub> \<phi> = K\<close> 
  unfolding mc nonconsequence_remainder
  by (metis Inf_superset_mono Un_absorb1 cInf_singleton insert_not_empty is_selection mc nonconsequence_remainder pmc_inclusion sup_commute)

text\<open>@{text \<open>pmc_closure\<close>} : a partial meet contraction is logically closed\<close>
lemma pmc_closure: \<open>K = Cn(A) \<Longrightarrow> (K \<div>\<^bsub>\<gamma>\<^esub> \<phi>) = Cn(K \<div>\<^bsub>\<gamma>\<^esub> \<phi>)\<close> 
proof (rule subset_antisym, simp_all add:inclusion_L mc transitivity_L, goal_cases)
  case 1
  have \<open>\<Inter>(\<gamma> (Cn A) \<phi>) = \<Inter>{Cn(B)|B. B \<in> \<gamma> (Cn A) \<phi>}\<close> 
    by auto (metis idempotency_L insert_absorb insert_iff insert_subset is_selection rem_closure tautology_selection)+
  from Cn_Inter[OF this] show ?case by blast
qed

text \<open>@{text \<open>pmc_extensionality\<close>} : Extensionality guarantees that the logic of contraction is extensional in the sense of allowing logically equivalent sentences to be freely substituted for each other\<close>
lemma pmc_extensionality: \<open>K = Cn(A) \<Longrightarrow> Cn({\<phi>}) = Cn({\<psi>}) \<Longrightarrow> K \<div>\<^bsub>\<gamma>\<^esub> \<phi> = K \<div>\<^bsub>\<gamma>\<^esub> \<psi>\<close>
  by (metis extensional_selection mc)

text \<open>@{text \<open>pmc_tautology\<close>} : if @{term \<open>\<phi>\<close>} is a tautology then the partial meet contraction of @{term \<open>K\<close>} by @{term \<open>\<phi>\<close>} is @{term \<open>K\<close>}\<close>
lemma pmc_tautology: \<open>K = Cn(A) \<Longrightarrow> \<tturnstile> \<phi> \<Longrightarrow>  K \<div>\<^bsub>\<gamma>\<^esub> \<phi> = K\<close> 
  by (simp add: mc taut2emptyrem tautology_selection)

text\<open>@{text \<open>completion\<close>} is a an operator that can build an equivalent selection from an existing one\<close>
definition (in Tarskian_logic) completion::\<open>('a set \<Rightarrow> 'a  \<Rightarrow> 'a set set) \<Rightarrow> 'a set \<Rightarrow> 'a  \<Rightarrow> 'a set set\<close> (\<open>*\<close>)
  where \<open>* \<gamma> A \<phi> \<equiv> if (A .\<bottom>. \<phi>) = {} then {A} else {B. B \<in> A .\<bottom>. \<phi> \<and> \<Inter> (\<gamma> A \<phi>) \<subseteq> B}\<close>


lemma selection_completion: "K = Cn(A) \<Longrightarrow> \<gamma> K \<phi> \<subseteq> * \<gamma> K \<phi>" 
  using completion_def is_selection tautology_selection by fastforce

lemma (in Tarskian_logic) completion_completion: "K = Cn(A) \<Longrightarrow> * (* \<gamma>) K \<phi> = * \<gamma> K \<phi>"
  by (auto simp add:completion_def)

lemma pmc_completion: \<open>K = Cn(A) \<Longrightarrow> K \<div>\<^bsub>*\<gamma>\<^esub> \<phi> = K \<div>\<^bsub>\<gamma>\<^esub> \<phi>\<close>
  apply(auto simp add: mc completion_def tautology_selection)
  by (metis Inter_lower equals0D in_mono is_selection)

end

text\<open>A transitively relational meet contraction is a partial meet contraction using a binary relation between the elements of the selection function\<close>
text\<open>A relation is : 
\<^item> transitive (@{text \<open>trans_rel\<close>})
\<^item> non empty (there is always an element  preferred to the others (@{text \<open>nonempty_rel\<close>}))\<close>

text\<open>A selection function @{term \<open>\<gamma>\<^sub>T\<^sub>R\<close>} is transitively relational @{text \<open>rel_sel\<close>} with the following condition :
\<^item> If the the remainders @{text \<open>K .\<bottom>. \<phi>\<close>} is empty then the selection function return @{term \<open>K\<close>}
\<^item> Else the selection function return a non empty transitive relation on the remainders\<close>
locale TransitivelyRelationalMeetContraction =  Tarskian_logic +

fixes relation::\<open>'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool\<close> (\<open>_ \<preceq>\<^bsub>_\<^esub> _\<close> [60,50,60]55)
assumes trans_rel: \<open>K = Cn(A) \<Longrightarrow> B \<preceq>\<^bsub>K\<^esub> C \<Longrightarrow> C \<preceq>\<^bsub>K\<^esub> D \<Longrightarrow> B \<preceq>\<^bsub>K\<^esub> D\<close>
assumes nonempty_rel: \<open>K = Cn(A) \<Longrightarrow> (K .\<bottom>. \<phi>) \<noteq> {} \<Longrightarrow> \<exists>B\<in>(K .\<bottom>. \<phi>). (\<forall>C\<in>(K .\<bottom>. \<phi>). C \<preceq>\<^bsub>K\<^esub> B)\<close> \<comment> \<open>pas clair dans la litterrature\<close>

fixes rel_sel::\<open>'a set \<Rightarrow> 'a  \<Rightarrow> 'a set set\<close> (\<open>\<gamma>\<^sub>T\<^sub>R\<close>) 
defines rel_sel: \<open>\<gamma>\<^sub>T\<^sub>R K \<phi> \<equiv> if (K .\<bottom>. \<phi>) = {} then {K} 
                                              else {B. B\<in>(K .\<bottom>. \<phi>) \<and> (\<forall>C\<in>(K .\<bottom>. \<phi>). C \<preceq>\<^bsub>K\<^esub> B)}\<close>

begin

text\<open>A transitively relational selection function respect the partial meet contraction postulates.\<close>
sublocale PartialMeetContraction where selection = \<gamma>\<^sub>T\<^sub>R
  apply(unfold_locales)
     apply(simp_all add: rel_sel) 
   using nonempty_rel apply blast
  using remainder_extensionality by blast

end

text\<open>A full meet contraction is a limiting case of the partial meet contraction where if the remainders are not empty then
the selection function return all the remainders (as defined by @{text \<open>full_sel\<close>}\<close>
locale FullMeetContraction = Tarskian_logic +

fixes full_sel::\<open>'a set \<Rightarrow> 'a  \<Rightarrow> 'a set set\<close> (\<open>\<gamma>\<^sub>F\<^sub>C\<close>) 
defines full_sel: \<open>\<gamma>\<^sub>F\<^sub>C K \<phi> \<equiv> if K .\<bottom>. \<phi> = {} then {K} else K .\<bottom>. \<phi>\<close>

begin


text\<open>A full selection and a relation ? is a transitively relational meet contraction postulates.\<close>
sublocale TransitivelyRelationalMeetContraction where relation = \<open>\<lambda> K A B. True\<close> and rel_sel=\<gamma>\<^sub>F\<^sub>C
  by (unfold_locales, auto simp add:full_sel, rule eq_reflection, simp) 

end

subsection\<open>Equivalence of partial meet contraction and AGM contraction\<close>


locale PMC_SC = PartialMeetContraction + Supraclassical_logic + Compact_logic 

begin

text \<open>In a context of a supraclassical and a compact logic the two remaining postulates of AGM contraction :
\<^item> @{text \<open>contract_recovery\<close>}
\<^item> @{text \<open>contract_success\<close>}
can be proved on a partial meet contraction.\<close>

text\<open>@{text \<open>pmc_recovery\<close>} : all proposition removed by a partial meet contraction of @{term \<open>\<phi>\<close>} will be recovered by the expansion of @{term \<open>\<phi>\<close>}\<close>

\<comment> \<open>recovery requires supraclassicality\<close>
lemma pmc_recovery: \<open>K = Cn(A) \<Longrightarrow> K \<subseteq> ((K \<div>\<^bsub>\<gamma>\<^esub> \<phi>) \<oplus> \<phi>)\<close>  
  apply(cases \<open>(K .\<bottom>. \<phi>) = {}\<close>, simp_all (no_asm) add:mc expansion_def) 
  using inclusion_L tautology_selection apply fastforce
  proof -
    assume a:\<open>K = Cn(A)\<close> and b:\<open>K .\<bottom>. \<phi> \<noteq> {}\<close>
    { fix \<psi>
      assume d:\<open>K \<turnstile> \<psi>\<close>
      have \<open>\<phi> .\<longrightarrow>. \<psi> \<in> \<Inter>(\<gamma> K \<phi>)\<close> 
        using is_selection[OF a b] 
        by auto (metis a d infer_def rem_closure remainder_recovery subsetD)
    }
    with a b show \<open>K \<subseteq> Cn (insert \<phi> (\<Inter> (\<gamma> K \<phi>)))\<close>
      by (metis (no_types, lifting) Un_commute assumption_L imp_PL infer_def insert_is_Un subsetI)
  qed

text \<open>@{text \<open>pmc_success\<close>} : a partial meet contraction of @{term \<open>K\<close>} by @{term \<open>\<phi>\<close>} not imply @{term \<open>\<phi>\<close>}\<close>
\<comment> \<open>success requires compacteness\<close>
lemma pmc_success: \<open>K = Cn(A) \<Longrightarrow> \<phi> \<notin> Cn({}) \<Longrightarrow> \<phi> \<notin> K \<div>\<^bsub>\<gamma>\<^esub> \<phi>\<close>
proof
  assume a:\<open>K = Cn(A)\<close> and b:\<open>\<phi> \<notin> Cn({})\<close> and c:\<open>\<phi> \<in> K \<div>\<^bsub>\<gamma>\<^esub> \<phi>\<close>
  from c show False unfolding mc
  proof(cases \<open>K .\<bottom>. \<phi> = {K}\<close>)
    case True
    then show ?thesis
      by (meson assumption_L c nonconsequence_remainder pmc_inclusion[OF a] subsetD)
  next
    case False
    hence \<open>\<forall>B\<in>K .\<bottom>. \<phi>. \<phi> \<notin> B\<close> using assumption_L rem by auto
    moreover have \<open>K .\<bottom>. \<phi> \<noteq> {}\<close> using b emptyrem2taut validD_L by blast
    ultimately show ?thesis 
      using b c mc nonempty_selection[OF a] validD_L emptyrem2taut is_selection[OF a]
      by (metis Inter_iff bot.extremum_uniqueI subset_iff)
  qed
qed

text\<open>As a partial meet contraction has been proven to respect all postulates of AGM contraction 
the equivalence between the both are straightforward\<close>
sublocale AGM_Contraction where contraction = \<open>\<lambda>A \<phi>. A \<div>\<^bsub>\<gamma>\<^esub> \<phi>\<close>
  using pmc_closure pmc_inclusion pmc_vacuity 
        pmc_success pmc_recovery pmc_extensionality
        expansion_def idempotency_L infer_def
  by (unfold_locales) metis+

end


locale AGMC_SC = AGM_Contraction + Supraclassical_logic + Compact_logic

begin

text \<open>obs 2.5 page 514\<close>
definition AGM_selection::\<open>'a set \<Rightarrow> 'a  \<Rightarrow> 'a set set\<close> (\<open>\<gamma>\<^sub>A\<^sub>G\<^sub>M\<close>)
  where AGM_sel: \<open>\<gamma>\<^sub>A\<^sub>G\<^sub>M A \<phi> \<equiv> if A .\<bottom>. \<phi> = {} then {A} else {B. B \<in> A .\<bottom>. \<phi> \<and> A \<div> \<phi> \<subseteq> B}\<close> 

text\<open>The selection function @{term \<open>\<gamma>\<^sub>A\<^sub>G\<^sub>M\<close>} respect the partial meet contraction postulates\<close>
sublocale PartialMeetContraction where selection = \<gamma>\<^sub>A\<^sub>G\<^sub>M
proof(unfold_locales, unfold AGM_sel, simp_all, goal_cases)
  case (1 K A \<phi>) \<comment> \<open>@{text \<open>non_emptiness\<close>} of selection requires a compact logic\<close>
  then show ?case  using upper_remainder[of \<open>K \<div> \<phi>\<close> K \<phi>] contract_success[OF 1(1)]
    by (metis contract_closure contract_inclusion infer_def taut2emptyrem valid_def)
next
  case (2 K A \<phi> \<psi>)
  then show ?case
    by (metis (mono_tags, lifting) contract_extensionality Collect_cong remainder_extensionality)
qed 

text \<open>@{text \<open>contraction_is_pmc\<close>} : an AGM contraction is equivalent to a partial met contraction using the selection function \<open>\<gamma>\<^sub>A\<^sub>G\<^sub>M\<close>\<close>
lemma contraction_is_pmc: \<open>K = Cn(A) \<Longrightarrow> K \<div> \<phi> = K \<div>\<^bsub>\<gamma>\<^sub>A\<^sub>G\<^sub>M\<^esub> \<phi>\<close> \<comment> \<open>requires a supraclassical logic\<close>
proof
  assume a:\<open>K = Cn(A)\<close>
  show \<open>K \<div> \<phi> \<subseteq> K \<div>\<^bsub>\<gamma>\<^sub>A\<^sub>G\<^sub>M\<^esub> \<phi>\<close> 
    using contract_inclusion[OF a] by (auto simp add:mc AGM_sel) 
next
  assume a:\<open>K = Cn(A)\<close>
  show \<open>K \<div>\<^bsub>\<gamma>\<^sub>A\<^sub>G\<^sub>M\<^esub> \<phi> \<subseteq> K \<div> \<phi>\<close>
  proof (cases \<open>\<tturnstile> \<phi>\<close>)
    case True
    hence \<open>K .\<bottom>. \<phi> = {}\<close>
      using nonconsequence_remainder taut2emptyrem by auto
    then show ?thesis 
      apply(simp_all add:mc AGM_sel) 
      by (metis a emptyrem2taut contract_closure contract_recovery valid_expansion)
  next  
    case validFalse:False
    then show ?thesis 
    proof (cases \<open>K \<turnstile> \<phi>\<close>)
      case True
      hence b:\<open>K .\<bottom>. \<phi> \<noteq> {}\<close>
        using emptyrem2taut validFalse by blast
      have d:\<open>\<psi> \<in> K \<Longrightarrow> \<phi> .\<longrightarrow>. \<psi> \<in> K \<div> \<phi>\<close> for \<psi> 
        using Supraclassical_logic.impI_PL Supraclassical_logic_axioms a contract_closure contract_recovery expansion_def by fastforce
      { fix \<psi>
        assume e:\<open>\<psi> \<in> K \<close> and f:\<open>\<psi> \<notin> K \<div> \<phi>\<close>
        have \<open>(\<psi> .\<longrightarrow>. \<phi>) .\<longrightarrow>. \<phi> \<notin> K \<div> \<phi>\<close> 
          using imp_recovery2[of \<open>K \<div> \<phi>\<close> \<phi> \<psi>] a contract_closure d e f by auto
        hence g:\<open>\<not> (K \<div> \<phi>) \<union> {\<psi> .\<longrightarrow>. \<phi>} \<turnstile> \<phi>\<close> 
          using a contract_closure impI_PL by fastforce
        then obtain B where h:\<open>(K \<div> \<phi>) \<union> {\<psi> .\<longrightarrow>. \<phi>} \<subseteq> B\<close> and i:\<open>B \<in> K .\<bottom>. \<phi>\<close>  
          using upper_remainder[of \<open>(K \<div> \<phi>) \<union> {\<psi> .\<longrightarrow>. \<phi>}\<close> K \<phi>] a True contract_inclusion idempotency_L impI2 by auto
        hence j:\<open>\<psi> \<notin> Cn(B)\<close>
          by (metis (no_types, lifting) CollectD mp_PL Un_insert_right a infer_def insert_subset rem rem_closure)
        have \<open>\<psi> \<notin>  K \<div>\<^bsub>\<gamma>\<^sub>A\<^sub>G\<^sub>M\<^esub> \<phi>\<close> 
          apply(simp add:mc AGM_sel b, rule_tac x=B in exI)
          by (meson Tarskian_logic.assumption_L Tarskian_logic_axioms h i j le_sup_iff)
      }
      then show ?thesis 
        using a pmc_inclusion by fastforce
    next
      case False
      hence \<open>K .\<bottom>. \<phi> = {K}\<close>
        using nonconsequence_remainder taut2emptyrem by auto
      then show ?thesis 
        using False a contract_vacuity idempotency_L pmc_vacuity by auto
    qed
  qed
qed

lemma contraction_with_completion: \<open>K = Cn(A) \<Longrightarrow> K \<div> \<phi> = K \<div>\<^bsub>* \<gamma>\<^sub>A\<^sub>G\<^sub>M\<^esub> \<phi>\<close>
  by (simp add: contraction_is_pmc pmc_completion)

end

(* in case of doubt uncomment one of these\<in>
sublocale AGMC_SC \<subseteq> PMC_SC where selection = \<gamma>\<^sub>A\<^sub>G\<^sub>M\<^sub>C 
  by (unfold_locales)

sublocale PMC_SC \<subseteq> AGMC_SC where contraction = \<open>\<lambda>A \<phi>. A \<div>\<^bsub>\<gamma>\<^esub> \<phi>\<close>
  by (unfold_locales)
*)

locale TRMC_SC = TransitivelyRelationalMeetContraction + PMC_SC where selection = \<gamma>\<^sub>T\<^sub>R

begin
text \<open>A transitively relational selection function respect conjuctive overlap.\<close>
lemma rel_sel_conj_overlap: \<open>K = Cn(A) \<Longrightarrow> \<gamma>\<^sub>T\<^sub>R K (\<phi> .\<and>. \<psi>) \<subseteq> \<gamma>\<^sub>T\<^sub>R K \<phi> \<union> \<gamma>\<^sub>T\<^sub>R K \<psi>\<close>
proof(intro subsetI) 
  fix B
  assume a:\<open>K = Cn(A)\<close> and b:\<open>B \<in> \<gamma>\<^sub>T\<^sub>R K (\<phi> .\<and>. \<psi>)\<close>
  show \<open>B \<in> \<gamma>\<^sub>T\<^sub>R K \<phi> \<union> \<gamma>\<^sub>T\<^sub>R K \<psi>\<close> (is ?A)
  proof(cases \<open>\<tturnstile> \<phi> \<or> \<tturnstile> \<psi> \<or> \<not> K \<turnstile> \<phi> \<or> \<not> K \<turnstile> \<psi>\<close>, elim disjE)
    assume \<open>\<tturnstile> \<phi>\<close>
    hence c:\<open>Cn({\<phi> .\<and>. \<psi>}) = Cn({\<psi>})\<close> 
      using conj_equiv valid_Cn_equiv valid_def by blast
    from b show ?A 
      by (metis Un_iff a c extensional_selection)
  next
    assume \<open>\<tturnstile> \<psi>\<close>
    hence c:\<open>Cn({\<phi> .\<and>. \<psi>}) = Cn({\<phi>})\<close> 
      by (simp add: Cn_conj_bis Cn_same validD_L)
    from b show ?A 
      by (metis Un_iff a c extensional_selection)
  next
    assume \<open>\<not> K \<turnstile> \<phi>\<close>
    then show ?A
      by (metis UnI1 a b conjE1_PL is_selection nonconsequence_remainder nonempty_selection tautology_selection subset_singletonD)
  next
    assume \<open>\<not> K \<turnstile> \<psi>\<close>
    then show ?A
      by (metis UnI2 a b conjE2_PL is_selection nonconsequence_remainder nonempty_selection tautology_selection subset_singletonD)
  next
    assume d:\<open>\<not> (\<tturnstile> \<phi> \<or> \<tturnstile> \<psi> \<or> \<not> K \<turnstile> \<phi> \<or> \<not> K \<turnstile> \<psi>)\<close>
    hence h:\<open>K .\<bottom>. \<phi>  \<noteq> {}\<close> and i:\<open>K .\<bottom>. \<psi> \<noteq> {}\<close> and j:\<open>K .\<bottom>. (\<phi> .\<and>. \<psi>) \<noteq> {}\<close> and k:"K \<turnstile> \<phi> .\<and>. \<psi>"
      using d emptyrem2taut valid_conj_PL apply auto
      by (meson Supraclassical_logic.conjI_PL Supraclassical_logic_axioms d)
    show ?A 
      using remainder_conj[OF a k] b h i j rel_sel by auto
  qed
qed

text\<open>A transitively relational meet contraction respect conjuctive overlap.\<close>
lemma trmc_conj_overlap: \<open>K = Cn(A) \<Longrightarrow> (K \<div>\<^bsub>\<gamma>\<^sub>T\<^sub>R\<^esub> \<phi>) \<inter> (K \<div>\<^bsub>\<gamma>\<^sub>T\<^sub>R\<^esub> \<psi>) \<subseteq> (K \<div>\<^bsub>\<gamma>\<^sub>T\<^sub>R\<^esub> (\<phi> .\<and>. \<psi>))\<close>
  unfolding mc using rel_sel_conj_overlap by blast

text\<open>A transitively relational selection function respect conjuctive inclusion\<close>
lemma rel_sel_conj_inclusion: \<open>K = Cn(A) \<Longrightarrow> \<gamma>\<^sub>T\<^sub>R K (\<phi> .\<and>. \<psi>) \<inter> (K .\<bottom>. \<phi>) \<noteq> {} \<Longrightarrow> \<gamma>\<^sub>T\<^sub>R K \<phi> \<subseteq> \<gamma>\<^sub>T\<^sub>R K (\<phi> .\<and>. \<psi>)\<close>
proof(intro subsetI) 
  fix B
  assume a:\<open>K = Cn(A)\<close> and b:\<open>\<gamma>\<^sub>T\<^sub>R K (\<phi> .\<and>. \<psi>) \<inter> (K .\<bottom>. \<phi>) \<noteq> {}\<close> and c:\<open>B \<in> \<gamma>\<^sub>T\<^sub>R K \<phi>\<close>
  show \<open>B \<in> \<gamma>\<^sub>T\<^sub>R K (\<phi> .\<and>. \<psi>)\<close> (is ?A)
  proof(cases \<open>\<tturnstile> \<phi> \<or> \<tturnstile> \<psi> \<or> \<not> K \<turnstile> \<phi> \<or> \<not> K \<turnstile> \<psi>\<close>, auto)
    assume \<open>\<tturnstile> \<phi>\<close>
    then show ?A 
      using b taut2emptyrem by auto
  next
    assume \<open>\<tturnstile> \<psi>\<close>
    hence \<open>Cn({\<phi> .\<and>. \<psi>}) = Cn({\<phi>})\<close>
      by (simp add: Cn_conj_bis Cn_same validD_L)
    then show ?A 
      using a c extensional_selection by blast  
  next
    assume d:\<open>\<phi> \<notin> Cn K\<close>
    with d show ?A
      by (metis Int_emptyI Tarskian_logic.nonconsequence_remainder Tarskian_logic_axioms a b c idempotency_L 
                inf_bot_right is_selection nonempty_selection singletonD subset_singletonD)
  next
    assume d:\<open>\<psi> \<notin> Cn K\<close>
    hence e:\<open>(\<phi> .\<and>. \<psi>) \<notin> Cn K\<close> 
      by (meson Supraclassical_logic.conjE2_PL Supraclassical_logic_axioms)
    hence f:\<open>\<gamma>\<^sub>T\<^sub>R K (\<phi> .\<and>. \<psi>) = {K}\<close>
      by (metis Tarskian_logic.nonconsequence_remainder Tarskian_logic_axioms a insert_not_empty is_selection 
                nonempty_selection subset_singletonD)
    with b have g:\<open>(K .\<bottom>. \<phi>) = {K}\<close> 
      unfolding nonconsequence_remainder[symmetric] using rem by auto
    with d f show ?A
      using a c is_selection by fastforce
  next
    assume d:\<open>\<not> \<tturnstile> \<phi>\<close> and e:\<open>\<not> \<tturnstile> \<psi>\<close> and f:\<open>\<phi> \<in> Cn K\<close> and g:\<open>\<psi> \<in> Cn K\<close>
    hence h:\<open>K .\<bottom>. \<phi>  \<noteq> {}\<close> and i:\<open>K .\<bottom>. \<psi> \<noteq> {}\<close> and j:\<open>K .\<bottom>. (\<phi> .\<and>. \<psi>) \<noteq> {}\<close> and k:"K \<turnstile> \<phi> .\<and>. \<psi>"
      using e d emptyrem2taut valid_conj_PL apply auto
      by (meson Supraclassical_logic.conjI_PL Supraclassical_logic_axioms f g)
    have o:\<open>B \<in> K .\<bottom>. \<phi> \<Longrightarrow> B \<in> K .\<bottom>. (\<phi> .\<and>. \<psi>)\<close> for B
      using a k remainder_conj by auto
    from b obtain B' where l:\<open>B' \<in> K .\<bottom>. (\<phi> .\<and>. \<psi>)\<close> and m:\<open>\<forall>C\<in>K .\<bottom>. (\<phi> .\<and>. \<psi>). C \<preceq>\<^bsub>K\<^esub> B'\<close> and n:\<open>\<phi> \<notin> B'\<close>
      apply (auto simp add:mc rel_sel j)
      using assumption_L rem by force
    have p:\<open>B' \<in> K .\<bottom>. \<phi>\<close> 
      apply(simp add: rem)
      by (metis (no_types, lifting) Supraclassical_logic.conjE1_PL Supraclassical_logic_axioms 
                Tarskian_logic.rem Tarskian_logic_axioms a l mem_Collect_eq n rem_closure)
    from c show ?A 
      apply (simp add:rel_sel o j h)
      using m p trans_rel a by blast
  qed
qed

text\<open>A transitively relational meet contraction respect conjuctive inclusion\<close>
lemma trmc_conj_inclusion: \<open>K = Cn(A) \<Longrightarrow> \<phi> \<notin> (K \<div>\<^bsub>\<gamma>\<^sub>T\<^sub>R\<^esub> (\<phi> .\<and>. \<psi>)) \<Longrightarrow> ((K \<div>\<^bsub>\<gamma>\<^sub>T\<^sub>R\<^esub> (\<phi> .\<and>. \<psi>) \<subseteq> (K \<div>\<^bsub>\<gamma>\<^sub>T\<^sub>R\<^esub> \<phi>)))\<close>
proof -
  assume a:\<open>K = Cn(A)\<close> and b:\<open>\<phi> \<notin> (K \<div>\<^bsub>\<gamma>\<^sub>T\<^sub>R\<^esub> (\<phi> .\<and>. \<psi>))\<close>
  then obtain B where c:\<open>B \<in> \<gamma>\<^sub>T\<^sub>R K (\<phi> .\<and>. \<psi>)\<close> and d:\<open>\<not> B \<turnstile> \<phi>\<close> apply(simp add:mc) 
    by (metis b emptyrem2taut is_selection pmc_tautology rem_closure subset_iff validD_L valid_conj_PL)
  hence \<open>B \<in> (K .\<bottom>. \<phi>)\<close>
    using remainder_recovery_bis[OF a _ d, of \<open>\<phi> .\<and>. \<psi>\<close>]
    by (metis (no_types, hide_lams) a conj_PL emptyrem2taut insert_not_empty is_selection 
                                    nonconsequence_remainder subsetD taut2emptyrem)
  with c have e:\<open>\<gamma>\<^sub>T\<^sub>R K (\<phi> .\<and>. \<psi>) \<inter> (K .\<bottom>. \<phi>) \<noteq> {}\<close> by blast
  then show \<open>((K \<div>\<^bsub>\<gamma>\<^sub>T\<^sub>R\<^esub> (\<phi> .\<and>. \<psi>) \<subseteq> (K \<div>\<^bsub>\<gamma>\<^sub>T\<^sub>R\<^esub> \<phi>)))\<close> 
    unfolding mc using rel_sel_conj_inclusion[OF a e] by blast
qed

text\<open>As a transitively relational meet contraction has been proven to respect all postulates of AGM full contraction 
the equivalence between the both are straightforward\<close>
sublocale AGM_FullContraction where contraction = \<open>\<lambda>A \<phi>. A  \<div>\<^bsub>\<gamma>\<^sub>T\<^sub>R\<^esub> \<phi>\<close>
  using trmc_conj_inclusion trmc_conj_overlap
  by (unfold_locales, simp_all)

end

                                    
locale AGMFC_SC = AGM_FullContraction + AGMC_SC 

begin

text\<open>An AGM relation is defined as ?\<close>
definition AGM_relation::\<open>'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool\<close> 
  where AGM_rel: \<open>AGM_relation C K B  \<equiv> (C = K \<and> B = K) \<or> (  (\<exists>\<phi>. K \<turnstile> \<phi> \<and> C \<in> K .\<bottom>. \<phi>)
                                                            \<and> (\<exists>\<phi>. K \<turnstile> \<phi> \<and> B \<in> K .\<bottom>. \<phi> \<and>  K \<div> \<phi> \<subseteq> B)
                                                            \<and> (\<forall>\<phi>. (K \<turnstile> \<phi> \<and> C \<in> K .\<bottom>. \<phi> \<and> B \<in> K .\<bottom>. \<phi> \<and> K \<div> \<phi> \<subseteq> C) \<longrightarrow> K \<div> \<phi> \<subseteq> B))\<close>
text\<open>An AGM relational selection is defined as a function that return @{term \<open>K\<close>} if the remainders of @{text \<open>K .\<bottom>. \<phi>\<close>} is empty and
the best element of the remainders according to an AGM relation\<close>
definition AGM_relational_selection::\<open>'a set \<Rightarrow> 'a  \<Rightarrow> 'a set set\<close> (\<open>\<gamma>\<^sub>A\<^sub>G\<^sub>M\<^sub>T\<^sub>R\<close>)
  where AGM_rel_sel: \<open>\<gamma>\<^sub>A\<^sub>G\<^sub>M\<^sub>T\<^sub>R  K \<phi> \<equiv> if (K .\<bottom>. \<phi>) = {} 
                                   then {K} 
                                   else {B. B\<in>(K .\<bottom>. \<phi>) \<and> (\<forall>C\<in>(K .\<bottom>. \<phi>). AGM_relation C K B)}\<close>

lemma AGM_rel_sel_completion: \<open>K = Cn(A) \<Longrightarrow> \<gamma>\<^sub>A\<^sub>G\<^sub>M\<^sub>T\<^sub>R K \<phi> = * \<gamma>\<^sub>A\<^sub>G\<^sub>M K \<phi>\<close> 
  apply (unfold AGM_rel_sel, simp add:completion_def split: if_splits)
proof(auto simp add:AGM_sel)
  fix S B C
  assume a:\<open>S \<in> Cn(A) .\<bottom>. \<phi>\<close> and b:\<open>B \<in> Cn(A) .\<bottom>. \<phi>\<close> and c:\<open>\<Inter> {B \<in> Cn(A) .\<bottom>. \<phi>. Cn(A) \<div> \<phi> \<subseteq> B} \<subseteq> B\<close> 
     and d:\<open>C \<in> Cn(A) .\<bottom>. \<phi>\<close>
  hence e:\<open>\<phi> \<notin>  Cn(A) \<div> \<phi>\<close> 
    using Tarskian_logic.taut2emptyrem Tarskian_logic_axioms contract_success by fastforce
  show \<open>AGM_relation C (Cn(A)) B\<close>
  proof(cases \<open>\<phi> \<in> Cn(A)\<close>)
    case True
    { fix \<psi>
      assume \<open>Cn A \<div> \<psi> \<subseteq> C\<close> 
      hence \<open>Cn A \<div> (\<phi> .\<and>. \<psi>) \<subseteq> Cn A \<div> \<phi>\<close> 
        using contract_conj_inclusion_variant[of \<open>Cn(A)\<close> A \<phi> \<psi>]
        by (metis (mono_tags, lifting) assumption_L contract_conj_inclusion d mem_Collect_eq rem subset_iff)
    } note f = this
    { fix \<psi> \<phi>'
      assume g:\<open>\<psi> \<in> Cn A \<div> \<phi>'\<close> and h:\<open>B \<in> Cn A .\<bottom>. \<phi>'\<close> and j:\<open>Cn A \<div> \<phi>' \<subseteq> C\<close> and i:\<open>\<psi> \<notin> B\<close> 
      hence \<open>\<phi>' .\<or>. \<psi> \<in> Cn A \<div> \<phi>'\<close>
        using Supraclassical_logic.disjI2_PL Supraclassical_logic_axioms contract_closure by fastforce
      hence k:\<open>\<phi>' .\<or>. \<psi> \<in> Cn A \<div> \<phi>\<close> 
        using contract_conj_overlap_variant[of \<open>Cn(A)\<close> A \<phi>' \<phi>] f[OF j]
        by (metis IntI Supraclassical_logic.disjI1_PL Supraclassical_logic_axioms conj_com_Cn 
                  contract_extensionality inclusion_L singletonI subsetD) 
      hence l:\<open>Cn A \<div> \<phi> \<subseteq> B\<close> using c by auto
      from k l have m:\<open>\<phi>' .\<or>. \<psi> \<in> B\<close> and n:\<open>B =Cn(B)\<close> 
        using b rem_closure by blast+
      have \<open>B \<union> {\<psi>} \<turnstile> \<phi>'\<close> using g h i
        by (simp add:rem) (metis contract_inclusion insertI1 insert_subsetI psubsetI subsetD subset_insertI)
      with n m have  \<open>B \<turnstile> \<phi>'\<close>
        by (metis Cn_equiv assumption_L disjE_PL disj_com equiv_PL imp_PL)
      with h have False 
        using assumption_L rem by auto
    } note g = this
    with True show ?thesis 
      apply(unfold AGM_rel, rule_tac disjI2)
      using d b c by (auto simp add:AGM_rel idempotency_L del:subsetI) blast+
  next
    case False
    then show ?thesis
      by (metis AGM_rel b d idempotency_L infer_def nonconsequence_remainder singletonD)
    qed
next
  fix S B \<psi>
  assume a:\<open>S \<in> Cn(A) .\<bottom>. \<phi>\<close> and b:\<open>B \<in> Cn(A) .\<bottom>. \<phi>\<close> and c:\<open>\<forall>C\<in>Cn A .\<bottom>. \<phi>. AGM_relation C (Cn A) B\<close> 
     and d:\<open>\<forall>C'. C' \<in> Cn A .\<bottom>. \<phi> \<and> Cn A \<div> \<phi> \<subseteq> C' \<longrightarrow> \<psi> \<in> C'\<close>
  then show \<open>\<psi> \<in> B\<close>
    unfolding AGM_rel
    by (metis (no_types, lifting) AGM_sel empty_Collect_eq insert_Diff insert_not_empty 
              nonconsequence_remainder nonempty_selection singletonD)
qed

text\<open>A transitively relational selection and an AGM relation is a transitively relational meet contraction\<close>
sublocale TransitivelyRelationalMeetContraction where relation = AGM_relation and rel_sel = \<open>\<gamma>\<^sub>A\<^sub>G\<^sub>M\<^sub>T\<^sub>R\<close>
proof(unfold_locales, simp_all (no_asm) only:atomize_eq, goal_cases)
  case a:(1 K A C B' B) \<comment> \<open>Very difficult proof requires litterature and high automation of isabelle!\<close>
  from a(2,3) show ?case 
    unfolding AGM_rel apply(elim disjE conjE, simp_all) 
  proof(intro disjI2 allI impI, elim exE conjE, goal_cases)
    case (1 \<psi> _ _ \<phi>)
    have b:\<open>B \<in> K .\<bottom>. (\<phi> .\<and>. \<psi>)\<close> and c:\<open>B' \<in> K .\<bottom>. (\<phi> .\<and>. \<psi>)\<close> and d:\<open>C \<in> K .\<bottom>. (\<phi> .\<and>. \<psi>)\<close>
      using remainder_conj[OF a(1)] 1 conjI_PL by auto
    hence e:\<open>K \<div> (\<phi> .\<and>. \<psi>) \<subseteq> B\<close> 
      using contract_conj_inclusion_variant[OF a(1), of \<phi>  \<psi>] 
      by (meson "1"(1) "1"(12) "1"(16) "1"(2) "1"(3) "1"(8) Supraclassical_logic.conj_PL 
                Supraclassical_logic_axioms dual_order.trans)
    { fix \<chi>
      assume f:\<open>\<chi> \<in> K \<div> \<psi>\<close>
      have \<open>\<psi> .\<or>. \<chi> \<in> (K \<div> \<psi>) \<inter> Cn {\<psi>}\<close> 
        by (metis Int_iff Supraclassical_logic.disjI1_PL Supraclassical_logic.disjI2_PL Supraclassical_logic_axioms 
                  f a(1) contract_closure in_mono inclusion_L singletonI)
      hence g:\<open>\<psi> .\<or>. \<chi> \<in> B\<close> 
        using contract_conj_overlap_variant[OF a(1), of \<psi>] 
        by (metis AGM_Contraction.contract_extensionality AGM_Contraction_axioms a(1) conj_com_Cn e in_mono)
      have \<open>\<psi> .\<longrightarrow>. \<chi> \<in> B\<close>
        by (metis a(1) "1"(10) "1"(15) "1"(16) assumption_L f in_mono infer_def rem_closure rem_inclusion remainder_recovery)
      with g have \<open>\<chi> \<in> B\<close>
        by (metis 1(15) a(1) disjE_PL infer_def order_refl rem_closure validD_L valid_Cn_imp)
    }
    then show ?case by blast
  qed
next
  case (2 K A \<phi>) 
  hence \<open>* \<gamma>\<^sub>A\<^sub>G\<^sub>M  K \<phi> \<noteq> {}\<close> 
    using nonempty_selection[OF 2(1), of \<phi>] selection_completion[OF 2(1), of \<phi>] by blast
  then show ?case
    using AGM_rel_sel_completion[OF 2(1), of \<phi>] AGM_rel_sel 2(1,2) by force
next
  case (3 K \<phi>)
  then show ?case using AGM_rel_sel_completion AGM_rel_sel by simp
qed 

\<comment> \<open>ça marche tout seul! ==> Je ne vois pas où sont utilisés ces lemmas\<close>
lemmas fullcontraction_is_pmc = contraction_is_pmc
lemmas fullcontraction_is_trmc = contraction_with_completion

end


locale FMC_SC = FullMeetContraction + TRMC_SC

begin

lemma full_meet_weak1: \<open>K = Cn(A) \<Longrightarrow> K \<turnstile> \<phi> \<Longrightarrow> (K \<div>\<^bsub>\<gamma>\<^sub>F\<^sub>C\<^esub> \<phi>) = K \<inter> Cn({.\<not> \<phi>})\<close>
proof(intro subset_antisym Int_greatest)
  assume a:\<open>K = Cn(A)\<close> and b:\<open>K \<turnstile> \<phi>\<close> 
  then show \<open> (K \<div>\<^bsub>\<gamma>\<^sub>F\<^sub>C\<^esub> \<phi>) \<subseteq> K\<close> 
    by (simp add: Inf_less_eq full_sel mc rem_inclusion)
next 
  assume a:\<open>K = Cn(A)\<close> and b:\<open>K \<turnstile> \<phi>\<close>   
  show \<open>(K \<div>\<^bsub>\<gamma>\<^sub>F\<^sub>C\<^esub> \<phi>) \<subseteq> Cn({.\<not> \<phi>})\<close>
  proof
    fix \<psi>
    assume c:\<open>\<psi> \<in> (K \<div>\<^bsub>\<gamma>\<^sub>F\<^sub>C\<^esub> \<phi>)\<close>
    { assume \<open>\<not> {.\<not> \<phi>} \<turnstile> \<psi>\<close>
      hence \<open>\<not> {.\<not> \<psi>} \<turnstile> \<phi>\<close>
        by (metis Un_insert_right insert_is_Un not_PL notnot_PL)
      hence \<open>\<not> {\<phi> .\<or>. .\<not> \<psi>} \<turnstile> \<phi>\<close>
        by (metis assumption_L disjI2_PL singleton_iff transitivity2_L)
      then obtain B where d:\<open>{\<phi> .\<or>. .\<not> \<psi>} \<subseteq> B\<close> and e:\<open>B \<in> K .\<bottom>. \<phi>\<close>
        by (metis a b disjI1_PL empty_subsetI idempotency_L infer_def insert_subset upper_remainder)
      hence f:\<open>\<not> \<psi> \<in> B\<close> 
        by (metis (no_types, lifting) CollectD assumption_L insert_subset disj_notE_PL rem)
      hence \<open>\<not> \<psi> \<in> (K \<div>\<^bsub>\<gamma>\<^sub>F\<^sub>C\<^esub> \<phi>)\<close>
        using e mc full_sel by auto
    }
    then show \<open>\<psi> \<in> Cn({.\<not> \<phi>})\<close>
      using c infer_def by blast
  qed 
next 
  assume a:\<open>K = Cn(A)\<close> and b:\<open>K \<turnstile> \<phi>\<close>   
  show \<open>K \<inter> Cn({.\<not> \<phi>}) \<subseteq> (K \<div>\<^bsub>\<gamma>\<^sub>F\<^sub>C\<^esub> \<phi>)\<close>
  proof(safe)
    fix \<psi>
    assume c:\<open>\<psi> \<in> K\<close> and d: \<open>\<psi> \<in> Cn {.\<not> \<phi>}\<close>
    have e:\<open>B \<turnstile> .\<not> \<phi> .\<longrightarrow>. \<psi>\<close> for B
      by (simp add: d validD_L valid_imp_PL)
    { fix B
      assume f:\<open>B \<in> K .\<bottom>. \<phi>\<close>
      hence \<open>B \<turnstile> \<phi> .\<longrightarrow>. \<psi>\<close>
        using a assumption_L c remainder_recovery by auto
      then have f:\<open>B \<turnstile> \<psi>\<close> using d e
        using disjE_PL ex_mid_PL by blast 
    }
    then show \<open>\<psi> \<in> (K \<div>\<^bsub>\<gamma>\<^sub>F\<^sub>C\<^esub> \<phi>)\<close>
      apply(simp_all add:mc c full_sel)
      using a rem_closure by blast
  qed
qed

lemma full_meet_weak2:\<open>K = Cn(A) \<Longrightarrow> K \<turnstile> \<phi> \<Longrightarrow> Cn((K \<div>\<^bsub>\<gamma>\<^sub>F\<^sub>C\<^esub> \<phi>) \<union> {.\<not> \<phi>}) = Cn({.\<not> \<phi>})\<close>
  unfolding full_meet_weak1 
  by (metis Cn_union idempotency_L inf.cobounded2 sup.absorb_iff2 sup_commute)

end

end
