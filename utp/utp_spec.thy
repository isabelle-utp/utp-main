section {* Weakest Pre- and Postspecification *}

theory utp_spec
imports utp_rel_laws
begin

subsection {* Weakest Prespecification *}
  
definition wpre :: "'a hrel \<Rightarrow> 'a hrel \<Rightarrow> 'a hrel" (infixl "\\" 70) where
  [upred_defs]: "Q \\ R = \<Sqinter> { Y. R \<sqsubseteq> Y ;; Q}"
  
lemma wpre_sol1: "R \<sqsubseteq> (Q \\ R) ;; Q"
  by (rel_auto)
 
lemma wpre_sol2: "Q \\ (P ;; Q) \<sqsubseteq> P"
  by (rel_auto)
  
lemma wpre_id: "(P \\ P) \<sqsubseteq> II"
  by (metis seqr_left_unit wpre_sol2)
    
lemma wpre_skip: "P = II \\ P"
  by (rel_auto)
  
lemma wpre_galois: "R \<sqsubseteq> P ;; Q \<longleftrightarrow> Q \\ R \<sqsubseteq> P"
  by (rel_blast)

lemma wpre_seq: "(P ;; Q) \\ R = P \\ (Q \\ R)"
  by (rule antisym, (metis (no_types, lifting) seqr_assoc wpre_galois wpre_sol1)+)

lemma wpre_choice: "(P \<sqinter> Q) \\ R = (P \\ R \<and> Q \\ R)"
  apply (rule antisym)
  apply (metis (no_types, lifting) semilattice_sup_class.le_sup_iff upred_semiring.distrib_left utp_pred_laws.le_inf_iff wpre_galois wpre_sol1)
  apply (metis conj_comm semilattice_sup_class.le_supI upred_semiring.distrib_left utp_pred_laws.inf_le2 wpre_galois)
done

text {* We cannot write the weakest prespecification as a weakest precondition construction *}
  
lemma "Q \\ R = (\<not> (Q ;; (\<not> R)))"
  apply (rel_auto)
  nitpick
oops
    
lemma "R \<sqsubseteq> P ;; Q \<longleftrightarrow> (\<not> Q ;; (\<not> R)) \<sqsubseteq> P"
  apply (rel_auto)
  nitpick
oops
  
subsection {* Weakest Postspecification *}
    
definition wpost :: "'a hrel \<Rightarrow> 'a hrel \<Rightarrow> 'a hrel" (infixl "\<^bold>'/" 70) where
  [upred_defs]: "Q \<^bold>/ R = \<Sqinter> { Y. R \<sqsubseteq> Q ;; Y}"

lemma wpost_galois: "R \<sqsubseteq> P ;; Q \<longleftrightarrow> P \<^bold>/ R \<sqsubseteq> Q"
  by (rel_blast)
    
end