(*
  Author: Fred Kurz
*)
theory CNF_Semantics_Supplement
  imports "Propositional_Proof_Systems.CNF_Formulas_Sema" "CNF_Supplement"
begin

lemma not_model_if_exists_unmodeled_singleton_clause:
  assumes "is_cnf F"
    and "{L} \<in> cnf F"
    and "\<not>lit_semantics \<nu> L" 
  shows "\<not>\<nu> \<Turnstile> F" 
proof (rule ccontr)
  assume "\<not>\<not>\<nu> \<Turnstile> F"  
  then have a: "\<nu> \<Turnstile> F"
    by blast
  moreover have "is_nnf F" 
    using is_nnf_cnf[OF assms(1)]
    by simp 
  moreover {
    let ?C = "{L}" 
    have "\<not>(\<exists>L'. L' \<in> ?C \<and> lit_semantics \<nu> L')" 
      using assms(3)
      by fast
    then have "\<not>(\<forall>C \<in> cnf F. \<exists>L. L \<in> C \<and> lit_semantics \<nu> L)"
      using assms(2)
      by blast
    hence "\<not>cnf_semantics \<nu> (cnf F)" 
      unfolding cnf_semantics_def clause_semantics_def
      by fast
  }
  ultimately have "\<not> \<nu> \<Turnstile> F" 
    using cnf_semantics
    by blast
  thus False 
    using a 
    by blast
qed

\<comment> \<open> NOTE This follows by contraposition from the previous lemma 
\<open>not_model_if_exists_unmodeled_singleton_clause\<close>. \<close>
corollary model_then_all_singleton_clauses_modelled:
  assumes "is_cnf F"
    and "{L} \<in> cnf F"
    and "\<nu> \<Turnstile> F" 
  shows "lit_semantics \<nu> L" 
  using not_model_if_exists_unmodeled_singleton_clause[OF assms(1, 2)] assms(3)
  by blast

\<comment> \<open> NOTE This is essentially the \<open>\<Rightarrow>\<close> direction of the compactness theorem when treating CNFs as sets
of formulas (sets of disjunctions in this case). \<close>
lemma model_for_cnf_is_model_of_all_subsets:
  assumes "cnf_semantics \<nu> \<F>"
    and "\<F>' \<subseteq> \<F>" 
  shows "cnf_semantics \<nu> \<F>'" 
proof -
  {
    fix C
    assume "C \<in> \<F>'"
    then have "C \<in> \<F>" 
      using assms(2)
      by blast
    then have "clause_semantics \<nu> C" 
      using assms(1)
      unfolding cnf_semantics_def
      by blast
  }
  thus ?thesis 
    unfolding cnf_semantics_def
    by blast
qed

lemma cnf_semantics_monotonous_in_cnf_subsets_if:
  assumes "\<A> \<Turnstile> \<Phi>" 
    and "is_cnf \<Phi>" 
    and "cnf \<Phi>' \<subseteq> cnf \<Phi>" 
  shows "cnf_semantics \<A> (cnf \<Phi>')"
proof -
  {
    have "is_nnf \<Phi>"
      using is_nnf_cnf[OF assms(2)].
    hence "cnf_semantics \<A> (cnf \<Phi>)" 
      using cnf_semantics assms(1)
      by blast
  }
  thus ?thesis 
    using model_for_cnf_is_model_of_all_subsets[OF _ assms(3)]
    by simp
qed

corollary modelling_relation_monotonous_in_cnf_subsets_if:
  assumes "\<A> \<Turnstile> \<Phi>" 
    and "is_cnf \<Phi>" 
    and "is_cnf \<Phi>'"
    and "cnf \<Phi>' \<subseteq> cnf \<Phi>" 
  shows "\<A> \<Turnstile> \<Phi>'"
proof -
  have "cnf_semantics \<A> (cnf \<Phi>')" 
    using cnf_semantics_monotonous_in_cnf_subsets_if[OF assms(1, 2, 4)].
  thus ?thesis
    using cnf_semantics is_nnf_cnf[OF assms(3)]
    by blast  
qed

\<comment> \<open> NOTE Show that any clause \<open>C\<close> containing a subset \<open>C\<close> for which all literals
  \<open>L\<close> evaluate to \<open>False\<close> for the given valuation \<open>\<A>\<close>, then the clause
  semantics evaluation can be reduced to the set \<open>C - C'\<close> where all literals of 
  \<open>C'\<close> have been removed. \<close>
lemma lit_semantics_reducible_to_subset_if:
  assumes "C' \<subseteq> C"
    and "\<forall>L \<in> C'. \<not>lit_semantics \<A> L"
  shows "clause_semantics \<A> C = clause_semantics \<A> (C - C')"
  unfolding clause_semantics_def
  using assms
  by fast

end
