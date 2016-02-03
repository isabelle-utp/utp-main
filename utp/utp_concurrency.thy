section {* Concurrent programming *}

theory utp_concurrency
  imports utp_designs
begin

no_notation
  Sublist.parallel (infixl "\<parallel>" 50)

text {* We describe the partition of a state space into a left and right part for parallel composition. If
        we want n-ary partitions this could alternatively use a list. But then the type-system would not
        record the number of state-spaces present, but perhaps we don't want that ... *}

record 'a partition =
  left_alpha :: "'a"
  right_alpha :: "'a"

definition design_par :: "('\<alpha>, '\<beta>) relation_d \<Rightarrow> ('\<alpha>, '\<beta>) relation_d \<Rightarrow> ('\<alpha>, '\<beta>) relation_d" (infixr "\<parallel>" 85) where
"P \<parallel> Q = ((pre\<^sub>D(P) \<and> pre\<^sub>D(Q)) \<turnstile>\<^sub>r (post\<^sub>D(P) \<and> post\<^sub>D(Q)))"

declare design_par_def [upred_defs]

lemma parallel_zero: "P \<parallel> true = true"
proof -
  have "P \<parallel> true = (pre\<^sub>D(P) \<and> pre\<^sub>D(true)) \<turnstile>\<^sub>r (post\<^sub>D(P) \<and> post\<^sub>D(true))"
    by (simp add: design_par_def)
  also have "... = (pre\<^sub>D(P) \<and> false) \<turnstile>\<^sub>r (post\<^sub>D(P) \<and> true)"
    by rel_tac
  also have "... = true"
    by rel_tac
  finally show ?thesis .
qed

lemma parallel_assoc: "P \<parallel> Q \<parallel> R = (P \<parallel> Q) \<parallel> R"
  by rel_tac

lemma parallel_comm: "P \<parallel> Q = Q \<parallel> P"
  by pred_tac
  
lemma parallel_idem: 
  assumes "P is H1" "P is H2"
  shows "P \<parallel> P = P"
  by (metis H1_H2_is_rdesign assms conj_idem design_par_def)

text {* A merge relation is a design that describes how a partitioned state-space should be
        merged into a third state-space. For now the state-spaces for two merged processes
        should have the same type. This could potentially be generalised, but that might
        have an effect on our reasoning capabilities. *}

type_synonym ('\<alpha>, '\<beta>) merge_d = "('\<alpha> partition, '\<beta>) relation_d"

lift_definition U0 :: "('\<alpha>, '\<alpha> partition) relation_d" is
"\<lambda> (A, A'). des_ok A' = des_ok A \<and> left_alpha (alpha_d.more A') = alpha_d.more A" .

lift_definition U1 :: "('\<alpha>, '\<alpha> partition) relation_d" is
"\<lambda> (A, A'). des_ok A' = des_ok A \<and> right_alpha (alpha_d.more A') = alpha_d.more A" .

text {* Parallel by merge *}

definition design_par_by_merge :: 
  "('\<alpha>, '\<beta>) relation_d \<Rightarrow> ('\<beta>, '\<gamma>) merge_d \<Rightarrow> ('\<alpha>, '\<beta>) relation_d \<Rightarrow> ('\<alpha>, '\<gamma>) relation_d" (infixr "\<parallel>\<^bsub>_\<^esub>" 85) 
where "P \<parallel>\<^bsub>M\<^esub> Q = (((P ;; U0) \<parallel> (Q ;; U1)) ;; M)"

end