(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : AGM Theory
 * Version         : 1.0
 *
 * Authors         : Valentin Fouillard, Safouan Taha, Frederic Boulanger
                     and Nicolas Sabouret
 *
 * This file       : AGM Remainders
 *
 * Copyright (c) 2021 Université Paris Saclay, France
 *
 ******************************************************************************\<close>

theory AGM_Remainder

imports AGM_Logic

begin

(*>*)



section \<open>Remainders\<close>

text\<open>In AGM, one important feature is to eliminate some proposition from a set of propositions by ensuring 
that the set of retained clauses is maximal and that nothing among these clauses allows to retrieve the eliminated proposition\<close>

subsection \<open>Remainders in a Tarskian logic\<close>
text \<open>In a general context of a Tarskian logic, we consider a descriptive definition (by comprehension)\<close>
context Tarskian_logic

begin
definition remainder::\<open>'a set \<Rightarrow> 'a \<Rightarrow> 'a set set\<close> (infix \<open>.\<bottom>.\<close> 55)
  where rem: \<open>A .\<bottom>. \<phi> \<equiv> {B. B \<subseteq> A \<and> \<not> B \<turnstile> \<phi> \<and> (\<forall>B'\<subseteq> A. B \<subset> B' \<longrightarrow> B' \<turnstile> \<phi>)}\<close> 

lemma rem_inclusion: \<open>B \<in> A .\<bottom>. \<phi> \<Longrightarrow> B \<subseteq> A\<close> 
  by (auto simp add:rem split:if_splits) 

lemma rem_closure: "K = Cn(A) \<Longrightarrow> B \<in> K .\<bottom>. \<phi> \<Longrightarrow> B = Cn(B)"
  apply(cases \<open>K .\<bottom>. \<phi> = {}\<close>, simp)
  by (simp add:rem infer_def) (metis idempotency_L inclusion_L monotonicity_L psubsetI)

lemma remainder_extensionality: \<open>Cn({\<phi>}) = Cn({\<psi>}) \<Longrightarrow> A .\<bottom>. \<phi> = A .\<bottom>. \<psi>\<close> 
  unfolding rem infer_def apply safe 
  by (simp_all add: Cn_same) blast+

lemma nonconsequence_remainder: \<open>A .\<bottom>. \<phi> = {A} \<longleftrightarrow> \<not> A \<turnstile> \<phi>\<close>
  unfolding rem by auto                           

\<comment> \<open>As we will see further, the other direction requires compactness!\<close>
lemma taut2emptyrem: \<open>\<tturnstile> \<phi> \<Longrightarrow> A .\<bottom>. \<phi> = {}\<close>
  unfolding rem by (simp add: infer_def validD_L)

end

subsection \<open>Remainders in a supraclassical logic\<close>
text\<open>In case of a supraclassical logic, remainders get impressive properties\<close>
context Supraclassical_logic

begin

\<comment> \<open>As an effect of being maximal, a remainder keeps the eliminated proposition in its propositions hypothesis\<close>
lemma remainder_recovery: \<open>K = Cn(A) \<Longrightarrow> K \<turnstile> \<psi> \<Longrightarrow> B \<in> K .\<bottom>. \<phi> \<Longrightarrow> B \<turnstile> \<phi> .\<longrightarrow>. \<psi>\<close> 
proof -
  { fix \<psi> and B
    assume  a:\<open>K = Cn(A)\<close> and c:\<open>\<psi> \<in> K\<close> and d:\<open>B \<in> K .\<bottom>. \<phi>\<close> and e:\<open>\<phi> .\<longrightarrow>. \<psi> \<notin> Cn(B)\<close>
    with a have f:\<open>\<phi> .\<longrightarrow>. \<psi> \<in> K\<close> using impI2 infer_def by blast
    with d e have \<open>\<phi> \<in> Cn(B \<union> {\<phi> .\<longrightarrow>. \<psi>})\<close> 
      apply (simp add:rem, elim conjE)
      by (metis dual_order.order_iff_strict inclusion_L insert_subset)
    with d have False using rem imp_recovery1 
      by (metis (no_types, lifting) CollectD infer_def)
  }
  thus \<open>K = Cn(A) \<Longrightarrow> K \<turnstile> \<psi> \<Longrightarrow> B \<in> K .\<bottom>. \<phi> \<Longrightarrow> B \<turnstile> \<phi> .\<longrightarrow>. \<psi>\<close>
    using idempotency_L by auto
qed

\<comment> \<open>When you remove some proposition \<open>\<phi>\<close> several other propositions can be lost. 
An important lemma states that the resulting remainder is also a remainder of any lost proposition\<close>
lemma remainder_recovery_bis: \<open>K = Cn(A) \<Longrightarrow> K \<turnstile> \<psi> \<Longrightarrow> \<not> B \<turnstile> \<psi> \<Longrightarrow> B \<in> K .\<bottom>. \<phi> \<Longrightarrow> B \<in> K .\<bottom>. \<psi>\<close>
proof-
  assume a:\<open>K = Cn(A)\<close> and b:\<open>\<not> B \<turnstile> \<psi>\<close> and c:\<open>B \<in> K .\<bottom>. \<phi>\<close> and d:\<open>K \<turnstile> \<psi>\<close>
  hence d:\<open>B \<turnstile> \<phi> .\<longrightarrow>. \<psi>\<close> using remainder_recovery by simp
  with c show \<open>B \<in> K .\<bottom>. \<psi>\<close>
    by (simp add:rem) (meson b dual_order.trans infer_def insert_subset monotonicity_L mp_PL order_refl psubset_imp_subset)
qed

corollary remainder_recovery_imp: \<open>K = Cn(A) \<Longrightarrow> K \<turnstile> \<psi> \<Longrightarrow> \<tturnstile> (\<psi> .\<longrightarrow>. \<phi>) \<Longrightarrow> B \<in> K .\<bottom>. \<phi> \<Longrightarrow> B \<in> K .\<bottom>. \<psi>\<close>
  apply(rule remainder_recovery_bis, simp_all)
  by (simp add:rem) (meson infer_def mp_PL validD_L)

\<comment> \<open>If we integrate back the eliminated proposition into the remainder, we retrieve the original set!\<close>
lemma remainder_expansion: \<open>K = Cn(A) \<Longrightarrow> K \<turnstile> \<psi> \<Longrightarrow> \<not> B \<turnstile> \<psi> \<Longrightarrow> B \<in> K .\<bottom>. \<phi> \<Longrightarrow> B \<oplus> \<psi> = K\<close>
proof 
  assume a:\<open>K = Cn(A)\<close> and b:\<open>K \<turnstile> \<psi>\<close> and c:\<open>\<not> B \<turnstile> \<psi>\<close> and d:\<open>B \<in> K .\<bottom>. \<phi>\<close>
  then show \<open>B \<oplus> \<psi> \<subseteq> K\<close>
    by (metis Un_insert_right expansion_def idempotency_L infer_def insert_subset 
              monotonicity_L rem_inclusion sup_bot.right_neutral)
next
  assume a:\<open>K = Cn(A)\<close> and b:\<open>K \<turnstile> \<psi>\<close> and c:\<open>\<not> B \<turnstile> \<psi>\<close> and d:\<open>B \<in> K .\<bottom>. \<phi>\<close>
  { fix \<chi>
    assume \<open>\<chi> \<in> K\<close>
    hence e:\<open>B \<turnstile> \<phi> .\<longrightarrow>.\<chi>\<close> using remainder_recovery[OF a _ d, of \<chi>] assumption_L by blast 
    have \<open>\<psi> \<in> K\<close> using a b idempotency_L infer_def by blast
    hence f:\<open>B \<union> {\<psi>} \<turnstile> \<phi>\<close> using b c d apply(simp add:rem)
      by (meson inclusion_L insert_iff insert_subsetI less_le_not_le subset_iff) 
    from e f have \<open>B \<union> {\<psi>} \<turnstile> \<chi>\<close> using imp_PL imp_trans by blast
  }
  then show \<open>K \<subseteq> B \<oplus> \<psi>\<close> 
    by (simp add: expansion_def subsetI)
qed

text\<open>To eliminate a conjunction, we only need to remove one side\<close>
lemma remainder_conj: \<open>K = Cn(A) \<Longrightarrow> K \<turnstile> \<phi> .\<and>. \<psi> \<Longrightarrow> K .\<bottom>. (\<phi> .\<and>. \<psi>) = (K .\<bottom>. \<phi>) \<union> (K .\<bottom>. \<psi>)\<close>
  apply(intro subset_antisym Un_least subsetI, simp add:rem)
    apply (meson conj_PL infer_def)
   using remainder_recovery_imp[of K A \<open>\<phi> .\<and>. \<psi>\<close> \<phi>] 
   apply (meson assumption_L conjE1_PL singletonI subsetI valid_imp_PL)
  using remainder_recovery_imp[of K A \<open>\<phi> .\<and>. \<psi>\<close> \<psi>]
  by (meson assumption_L conjE2_PL singletonI subsetI valid_imp_PL)

end

subsection \<open>Remainders in a compact logic\<close>
text\<open>In case of a supraclassical logic, remainders get impressive properties\<close>
context Compact_logic
begin

text \<open>The following lemma is the Lindembaum's lemma requiring the Zorn's lemma (already available in standard Isabelle/HOL). 
  For more details, please refer to the book "Theory of logical calculi" @{cite wojcicki2013theory}. 
This very important lemma states that we can get a maximal set (remainder \<open>B'\<close>) starting from any set 
\<open>B\<close> if this latter does not infer the proposition \<open>\<phi>\<close> we want to eliminate\<close>
lemma upper_remainder: \<open>B \<subseteq> A \<Longrightarrow> \<not> B \<turnstile> \<phi> \<Longrightarrow> \<exists>B'. B \<subseteq> B' \<and>  B' \<in> A .\<bottom>. \<phi>\<close> 
proof -
  assume a:\<open>B \<subseteq> A\<close> and b:\<open>\<not> B \<turnstile> \<phi>\<close>
  have c:\<open>\<not> \<tturnstile> \<phi>\<close>
    using b infer_def validD_L by blast
  define \<B> where "\<B> \<equiv> {B'. B \<subseteq> B' \<and> B' \<subseteq> A \<and> \<not> B' \<turnstile> \<phi>}"
  have d:\<open>subset.chain \<B> C \<Longrightarrow> subset.chain {B. \<not> B \<turnstile> \<phi>} C\<close> for C
    unfolding \<B>_def
    by (simp add: le_fun_def less_eq_set_def subset_chain_def)
  have e:\<open>C \<noteq> {} \<Longrightarrow> subset.chain \<B> C \<Longrightarrow> B \<subseteq> \<Union> C\<close> for C 
    by (metis (no_types, lifting) \<B>_def subset_chain_def less_eq_Sup mem_Collect_eq subset_iff)
  { fix C
    assume f:\<open>C \<noteq> {}\<close> and g:\<open>subset.chain \<B> C\<close> 
    have \<open>\<Union> C \<in> \<B>\<close>
      using \<B>_def  e[OF f g] chain_closure[OF c d[OF g]] 
      by simp (metis (no_types, lifting) CollectD Sup_least Sup_subset_mono g subset.chain_def subset_trans)
  } note f=this 
  have \<open>subset.chain \<B> C \<Longrightarrow> \<exists>U\<in>\<B>. \<forall>X\<in>C. X \<subseteq> U\<close> for C
    apply (cases \<open>C \<noteq> {}\<close>) 
     apply (meson Union_upper f) 
    using \<B>_def a b by blast
  with subset_Zorn[OF this, simplified] obtain B' where f:\<open>B'\<in> \<B> \<and> (\<forall>X\<in>\<B>. B' \<subseteq> X \<longrightarrow> X = B')\<close> by auto
  then show ?thesis 
    by (simp add:rem \<B>_def, rule_tac x=B' in exI) (metis psubsetE subset_trans)
qed

\<comment> \<open>An immediate corollary ruling tautologies\<close>
corollary emptyrem2taut: \<open>A .\<bottom>. \<phi> = {} \<Longrightarrow> \<tturnstile> \<phi>\<close>
  by (metis bot.extremum empty_iff upper_remainder valid_def)

end

end
