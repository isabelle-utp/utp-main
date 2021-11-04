(* Title: Examples/SML_Relativization/Topology/SML_Topological_Space_Countability.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>
Relativization of the results related to the countability properties of 
topological spaces
\<close>
theory SML_Topological_Space_Countability
  imports SML_Topological_Space
begin



subsection\<open>First countable topological space\<close>


subsubsection\<open>Definitions and common properties\<close>

locale first_countable_topology_ow = 
  topological_space_ow U \<tau> for U :: "'at set" and \<tau> +
  assumes first_countable_basis:
    "(
      \<forall>x\<in>U. 
      (
        \<exists>B::nat \<Rightarrow> 'at set. 
          (\<forall>i. B i \<subseteq> U \<and> x \<in> B i \<and> \<tau> (B i)) \<and> 
          (\<forall>S. S \<subseteq> U \<and> \<tau> S \<and> x \<in> S \<longrightarrow> (\<exists>i. B i \<subseteq> S))
      )
    )"

locale ts_fct_ow = 
  ts: topological_space_ow U\<^sub>1 \<tau>\<^sub>1 + fct: first_countable_topology_ow U\<^sub>2 \<tau>\<^sub>2
  for U\<^sub>1 :: "'at set" and \<tau>\<^sub>1 and U\<^sub>2 :: "'bt set" and \<tau>\<^sub>2
begin

sublocale topological_space_pair_ow U\<^sub>1 \<tau>\<^sub>1 U\<^sub>2 \<tau>\<^sub>2 ..

end

locale first_countable_topology_pair_ow = 
  fct\<^sub>1: first_countable_topology_ow U\<^sub>1 \<tau>\<^sub>1 + 
  fct\<^sub>2: first_countable_topology_ow U\<^sub>2 \<tau>\<^sub>2
  for U\<^sub>1 :: "'at set" and \<tau>\<^sub>1 and U\<^sub>2 :: "'bt set" and \<tau>\<^sub>2
begin

sublocale ts_fct_ow U\<^sub>1 \<tau>\<^sub>1 U\<^sub>2 \<tau>\<^sub>2 ..

end


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

private lemma first_countable_topology_transfer_h: 
  "(\<forall>i. B i \<subseteq> Collect (Domainp A) \<and> x \<in> B i \<and> \<tau> (B i)) =
    (B ` Collect top \<subseteq> {Aa. Aa \<subseteq> Collect (Domainp A)} \<and> 
    (\<forall>i. x \<in> B i \<and> \<tau> (B i)))"
  by auto

lemma first_countable_topology_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A"
  shows 
    "((rel_set A ===> (=)) ===> (=)) 
      (first_countable_topology_ow (Collect (Domainp A))) 
      class.first_countable_topology"
  unfolding 
    first_countable_topology_ow_def 
    class.first_countable_topology_def
    first_countable_topology_ow_axioms_def 
    class.first_countable_topology_axioms_def
  apply transfer_prover_start
  apply transfer_step+  
  by 
    (
      simp,
      unfold Ball_Collect, 
      intro ext, 
      unfold first_countable_topology_transfer_h
    ) 
    (metis top_set_def)

end


subsubsection\<open>Relativization\<close>

context first_countable_topology_ow 
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting first_countable_topology_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> through simp
begin

tts_lemma countable_basis_at_decseq:
  assumes "x \<in> U"
    and "\<And>A. 
      \<lbrakk>
        range A \<subseteq> Pow U; 
        \<And>i. \<tau> (A i); 
        \<And>i. x \<in> A i; 
        \<And>S. \<lbrakk>S \<subseteq> U; \<tau> S; x \<in> S\<rbrakk> \<Longrightarrow> \<forall>\<^sub>F i in sequentially. A i \<subseteq> S
      \<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is first_countable_topology_class.countable_basis_at_decseq.

tts_lemma first_countable_basisE:
  assumes "x \<in> U"
    and "\<And>\<A>. 
      \<lbrakk>
        \<A> \<subseteq> Pow U; 
        countable \<A>; 
        \<And>A. \<lbrakk>A \<subseteq> U; A \<in> \<A>\<rbrakk> \<Longrightarrow> x \<in> A; 
        \<And>A. \<lbrakk>A \<subseteq> U; A \<in> \<A>\<rbrakk> \<Longrightarrow> \<tau> A; 
        \<And>S. \<lbrakk>S \<subseteq> U; \<tau> S; x \<in> S\<rbrakk> \<Longrightarrow> \<exists>A\<in>\<A>. A \<subseteq> S\<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is first_countable_topology_class.first_countable_basisE.

tts_lemma first_countable_basis_Int_stableE:
  assumes "x \<in> U"
    and "\<And>\<A>. 
      \<lbrakk>
        \<A> \<subseteq> Pow U; 
        countable \<A>; 
        \<And>A. \<lbrakk>A \<subseteq> U; A \<in> \<A>\<rbrakk> \<Longrightarrow> x \<in> A; 
        \<And>A. \<lbrakk>A \<subseteq> U; A \<in> \<A>\<rbrakk> \<Longrightarrow> \<tau> A; 
        \<And>S. \<lbrakk>S \<subseteq> U; \<tau> S; x \<in> S\<rbrakk> \<Longrightarrow> \<exists>A\<in>\<A>. A \<subseteq> S; 
        \<And>A B. \<lbrakk>A \<subseteq> U; B \<subseteq> U; A \<in> \<A>; B \<in> \<A>\<rbrakk> \<Longrightarrow> A \<inter> B \<in> \<A>
      \<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is first_countable_topology_class.first_countable_basis_Int_stableE.

end

end



subsection\<open>Topological space with a countable basis\<close>


subsubsection\<open>Definitions and common properties\<close>

locale countable_basis_ow = 
  topological_space_ow U \<tau> for U :: "'at set" and \<tau> +
  fixes B :: "'at set set"
  assumes is_basis: "topological_basis_ow U \<tau> B"
    and countable_basis: "countable B"
begin

lemma B_ss_PowU[simp]: "B \<subseteq> Pow U" 
  by (simp add: is_basis topological_basis_closed)

end


subsubsection\<open>Transfer rules\<close>

context 
  includes lifting_syntax
begin

lemma countable_basis_transfer[transfer_rule]: 
  assumes [transfer_rule]: "bi_unique A" "right_total A"
  shows 
    "((rel_set A ===> (=)) ===> rel_set (rel_set A) ===> (=)) 
      (countable_basis_ow (Collect (Domainp A))) countable_basis"
proof(intro rel_funI)
  fix \<tau> :: "'a set \<Rightarrow> bool" and \<tau>' :: "'b set \<Rightarrow> bool" and B B'
  assume \<tau>\<tau>'[transfer_rule]: "(rel_set A ===> (=)) \<tau> \<tau>'" 
    and BB'[transfer_rule]: "rel_set (rel_set A) B B'"
  show "countable_basis_ow (Collect (Domainp A)) \<tau> B = countable_basis \<tau>' B'"
  proof
    assume cbow: "countable_basis_ow (Collect (Domainp A)) \<tau> B"
    interpret cbow: countable_basis_ow "Collect (Domainp A)" \<tau> B by (rule cbow)
    interpret ts: topological_space \<tau>' 
      by transfer (simp add: cbow.topological_space_ow_axioms)
    show "countable_basis \<tau>' B'"
      apply unfold_locales
      subgoal
        using cbow.is_basis unfolding ts.topological_basis_with by transfer
      subgoal using cbow.countable_basis by transfer
      done
  next
    assume cb: "countable_basis \<tau>' B'"
    interpret cb: countable_basis \<tau>' B' by (rule cb)
    interpret tsow: topological_space_ow "Collect (Domainp A)" \<tau> 
      using cb.topological_space_axioms by transfer
    show "countable_basis_ow (Collect (Domainp A)) \<tau> B"
      apply unfold_locales
      subgoal using cb.is_basis unfolding cb.topological_basis_with by transfer
      subgoal using cb.countable_basis by transfer
      done
  qed
qed

end


subsubsection\<open>Relativization\<close>

context countable_basis_ow 
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting countable_basis_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> through auto
  applying [OF B_ss_PowU]
begin

tts_lemma open_countable_basis_ex:
  assumes "X \<subseteq> U" and "\<tau> X"
  shows "\<exists>B'\<in>Pow (Pow U). B' \<subseteq> B \<and> X = \<Union> B'"
    is countable_basis.open_countable_basis_ex.

tts_lemma countable_dense_exists:
  "\<exists>D\<in>Pow U. 
    countable D \<and> 
    (\<forall>X\<in>Pow U. \<tau> X \<longrightarrow> X \<noteq> {} \<longrightarrow> (\<exists>d\<in>D. d \<in> X))"
    is countable_basis.countable_dense_exists.

tts_lemma open_countable_basisE:
  assumes "X \<subseteq> U"
    and "\<tau> X"
    and "\<And>B'. \<lbrakk>B' \<subseteq> Pow U; B' \<subseteq> B; X = \<Union> B'\<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is countable_basis.open_countable_basisE.

tts_lemma countable_dense_setE:
  assumes "\<And>D. 
    \<lbrakk>D \<subseteq> U; countable D; \<And>X. \<lbrakk>X \<subseteq> U; \<tau> X; X \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>x\<in>D. x \<in> X\<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is countable_basis.countable_dense_setE.

end

end



subsection\<open>Second countable topological space\<close>


subsubsection\<open>Definitions and common properties\<close>

locale second_countable_topology_ow = 
  topological_space_ow U \<tau> for U :: "'at set" and \<tau> +
  assumes second_countable_basis:
    "\<exists>B\<subseteq>Pow U. countable B \<and> (\<forall>S\<subseteq>U. \<tau> S = generate_topology_on B U S)"


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma second_countable_topology_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((rel_set A ===> (=)) ===> (=)) 
      (second_countable_topology_ow (Collect (Domainp A))) 
      class.second_countable_topology"
  unfolding 
    second_countable_topology_ow_def 
    class.second_countable_topology_def
    second_countable_topology_ow_axioms_def 
    class.second_countable_topology_axioms_def
  apply transfer_prover_start
  apply transfer_step+
  unfolding Ball_Collect ctr_simps_subset_pow_iff''[symmetric] 
  by simp

end


subsubsection\<open>Relativization\<close>

context second_countable_topology_ow 
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting second_countable_topology_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> through (unfold topological_basis_ow_def, auto)
begin

tts_lemma ex_countable_basis:
  "\<exists>B\<in>Pow (Pow U). countable B \<and> (on U with \<tau> : \<guillemotleft>topological_basis\<guillemotright> B)"
    is Elementary_Topology.ex_countable_basis.

end

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting second_countable_topology_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> through (auto simp: countable_subset)
begin

tts_lemma countable_dense_exists:
  "\<exists>D\<in>Pow U. countable D \<and> (\<forall>X\<in>Pow U. \<tau> X \<longrightarrow> X \<noteq> {} \<longrightarrow> (\<exists>d\<in>D. d \<in> X))"
    is Elementary_Topology.countable_dense_exists.

tts_lemma countable_dense_setE:
  assumes "\<And>D. 
    \<lbrakk>
      D \<subseteq> U; 
      countable D; 
      \<And>X. \<lbrakk>X \<subseteq> U; \<tau> X; X \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>d\<in>D. d \<in> X
    \<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is Elementary_Topology.countable_dense_setE.

tts_lemma univ_second_countable:
  assumes "\<And>\<B>. 
    \<lbrakk>
      \<B> \<subseteq> Pow U; 
      countable \<B>; 
      \<And>C. \<lbrakk>C \<subseteq> U; C \<in> \<B>\<rbrakk> \<Longrightarrow> \<tau> C; 
      \<And>S. \<lbrakk>S \<subseteq> U; \<tau> S\<rbrakk> \<Longrightarrow> \<exists>U\<in>Pow (Pow U). U \<subseteq> \<B> \<and> S = \<Union> U
    \<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is Elementary_Topology.univ_second_countable.

tts_lemma Lindelof:
  assumes "\<F> \<subseteq> Pow U"
    and "\<And>S. \<lbrakk>S \<subseteq> U; S \<in> \<F>\<rbrakk> \<Longrightarrow> \<tau> S"
    and "\<And>\<F>'. \<lbrakk>\<F>' \<subseteq> Pow U; \<F>' \<subseteq> \<F>; countable \<F>'; \<Union> \<F>' = \<Union> \<F>\<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is Elementary_Topology.Lindelof.

tts_lemma countable_disjoint_open_subsets:
  assumes "\<F> \<subseteq> Pow U" and "\<And>S. \<lbrakk>S \<subseteq> U; S \<in> \<F>\<rbrakk> \<Longrightarrow> \<tau> S" and "disjoint \<F>"
  shows "countable \<F>"
    is Elementary_Topology.countable_disjoint_open_subsets.

end

end

text\<open>\newpage\<close>

end