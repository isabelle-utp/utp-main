section {* Concurrent programming *}

theory utp_concurrency
  imports utp_rel
begin

no_notation
  Sublist.parallel (infixl "\<parallel>" 50)

subsection {* Design parallel composition *}

definition design_par :: "('\<alpha>, '\<beta>) relation_d \<Rightarrow> ('\<alpha>, '\<beta>) relation_d \<Rightarrow> ('\<alpha>, '\<beta>) relation_d" (infixr "\<parallel>" 85) where
"P \<parallel> Q = ((pre\<^sub>D(P) \<and> pre\<^sub>D(Q)) \<turnstile>\<^sub>r (post\<^sub>D(P) \<and> post\<^sub>D(Q)))"

declare design_par_def [upred_defs]

lemma design_par_is_H1_H2: "(P \<parallel> Q) is H1_H2"
  by (simp add: design_par_def rdesign_is_H1_H2)
  
lemma design_par_skip_d_distl:
  assumes "P is H1_H2" "Q is H1_H2"
  shows "((P ;; II\<^sub>D) \<parallel> (Q ;; II\<^sub>D)) = ((P \<parallel> Q) ;; II\<^sub>D)"
proof -
  obtain P\<^sub>1 P\<^sub>2 where P: "P = P\<^sub>1 \<turnstile>\<^sub>r P\<^sub>2"
    by (metis H1_H2_commute H1_H2_is_rdesign H2_idem Healthy_def assms(1))
  moreover obtain Q\<^sub>1 Q\<^sub>2 where Q: "Q = Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2"
   by (metis H1_H2_commute H1_H2_is_rdesign H2_idem Healthy_def assms(2))
  moreover have "(((P\<^sub>1 \<turnstile>\<^sub>r P\<^sub>2) ;; II\<^sub>D) \<parallel> ((Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2) ;; II\<^sub>D)) = (((P\<^sub>1 \<turnstile>\<^sub>r P\<^sub>2) \<parallel> (Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2)) ;; II\<^sub>D)"
    by (simp add: design_par_def skip_d_def rdesign_composition, rel_auto)
  ultimately show ?thesis
    by simp
qed

lemma design_par_H3_closure:
  assumes "P is H1_H3" "Q is H1_H3"
  shows "(P \<parallel> Q) is H3"
  using assms
  by (simp add: H3_unrest_out_alpha design_par_def precond_right_unit rdesign_H3_iff_pre seqr_pre_out)

lemma parallel_zero: "P \<parallel> true = true"
proof -
  have "P \<parallel> true = (pre\<^sub>D(P) \<and> pre\<^sub>D(true)) \<turnstile>\<^sub>r (post\<^sub>D(P) \<and> post\<^sub>D(true))"
    by (simp add: design_par_def)
  also have "... = (pre\<^sub>D(P) \<and> false) \<turnstile>\<^sub>r (post\<^sub>D(P) \<and> true)"
    by rel_auto
  also have "... = true"
    by rel_auto
  finally show ?thesis .
qed

lemma parallel_assoc: "P \<parallel> Q \<parallel> R = (P \<parallel> Q) \<parallel> R"
  by rel_auto

lemma parallel_comm: "P \<parallel> Q = Q \<parallel> P"
  by pred_auto
  
lemma parallel_idem: 
  assumes "P is H1" "P is H2"
  shows "P \<parallel> P = P"
  by (metis H1_H2_is_rdesign assms conj_idem design_par_def)

lemma parallel_mono_1:
  assumes "P\<^sub>1 \<sqsubseteq> P\<^sub>2" "P\<^sub>1 is H1_H2" "P\<^sub>2 is H1_H2"
  shows "P\<^sub>1 \<parallel> Q \<sqsubseteq> P\<^sub>2 \<parallel> Q"
proof -
  have "pre\<^sub>D(P\<^sub>1) \<turnstile>\<^sub>r post\<^sub>D(P\<^sub>1) \<sqsubseteq> pre\<^sub>D(P\<^sub>2) \<turnstile>\<^sub>r post\<^sub>D(P\<^sub>2)"
    by (metis H1_H2_commute H1_H2_is_rdesign H1_idem Healthy_def' assms)
  hence "(pre\<^sub>D(P\<^sub>1) \<turnstile>\<^sub>r post\<^sub>D(P\<^sub>1)) \<parallel> Q \<sqsubseteq> (pre\<^sub>D(P\<^sub>2) \<turnstile>\<^sub>r post\<^sub>D(P\<^sub>2)) \<parallel> Q" 
    by (auto simp add: rdesign_refinement design_par_def) (pred_auto+)
  thus ?thesis
    by (metis H1_H2_commute H1_H2_is_rdesign H1_idem Healthy_def' assms)
qed

lemma parallel_mono_2:
  assumes "Q\<^sub>1 \<sqsubseteq> Q\<^sub>2" "Q\<^sub>1 is H1_H2" "Q\<^sub>2 is H1_H2"
  shows "P \<parallel> Q\<^sub>1 \<sqsubseteq> P \<parallel> Q\<^sub>2"
  by (metis assms parallel_comm parallel_mono_1)

lemma parallel_choice_distr:
  "(P \<sqinter> Q) \<parallel> R = ((P \<parallel> R) \<sqinter> (Q \<parallel> R))"
  by (simp add: design_par_def rdesign_choice conj_assoc inf_left_commute inf_sup_distrib2)

lemma parallel_condr_distr:
  "(P \<triangleleft> \<lceil>b\<rceil>\<^sub>D \<triangleright> Q) \<parallel> R = ((P \<parallel> R) \<triangleleft> \<lceil>b\<rceil>\<^sub>D \<triangleright> (Q \<parallel> R))"
  by (simp add: design_par_def rdesign_def alpha cond_conj_distr conj_comm design_condr)

subsection {* Parallel by merge *}

text {* We describe the partition of a state space into two pieces. *}

type_synonym '\<alpha> partition = "'\<alpha> \<times> '\<alpha>"

definition "left_uvar x = x ;\<^sub>L fst\<^sub>L ;\<^sub>L snd\<^sub>L"

definition "right_uvar x = x ;\<^sub>L snd\<^sub>L ;\<^sub>L snd\<^sub>L"

declare left_uvar_def [upred_defs]

declare right_uvar_def [upred_defs]

text {* Extract the ith element of the second part *}

definition "pre_uvar x = x ;\<^sub>L fst\<^sub>L"

definition "in_pre_uvar x = in_var (pre_uvar x)"

definition "out_pre_uvar x = out_var (pre_uvar x)"

definition "in_pre_uexpr x = var (in_pre_uvar x)"

definition "out_pre_uexpr x = var (out_pre_uvar x)"

declare pre_uvar_def [upred_defs]

declare in_pre_uexpr_def [upred_defs]
declare out_pre_uexpr_def [upred_defs]

lemma left_uvar_indep_right_uvar [simp]:
  "left_uvar x \<bowtie> right_uvar y"
  apply (simp add: left_uvar_def right_uvar_def lens_comp_assoc[THEN sym])
  apply (simp add: alpha_in_var alpha_out_var)
done

lemma right_uvar_indep_left_uvar [simp]:
  "right_uvar x \<bowtie> left_uvar y"
  by (simp add: lens_indep_sym)

lemma left_uvar [simp]: "vwb_lens x \<Longrightarrow> vwb_lens (left_uvar x)"
  by (simp add: left_uvar_def comp_vwb_lens fst_vwb_lens snd_vwb_lens)

lemma right_uvar [simp]: "vwb_lens x \<Longrightarrow> vwb_lens (right_uvar x)"
  by (simp add: right_uvar_def comp_vwb_lens fst_vwb_lens snd_vwb_lens)

syntax
  "_svarpre"   :: "svid \<Rightarrow> svid" ("_\<^sub><" [999] 999)
  "_svarleft"  :: "svid \<Rightarrow> svid" ("0-_" [999] 999)
  "_svarright" :: "svid \<Rightarrow> svid" ("1-_" [999] 999)

translations
  "_svarpre x" == "CONST pre_uvar x"
  "_svarleft x" == "CONST left_uvar x"
  "_svarright x" == "CONST right_uvar x"

type_synonym '\<alpha> merge = "('\<alpha> \<times> ('\<alpha> \<times> '\<alpha>), '\<alpha>) relation"

record ('\<alpha>, '\<beta>, '\<gamma>) amerge =
  mrel   :: "('\<alpha> \<times> ('\<beta> \<times> '\<gamma>), '\<alpha>) relation"
  mleft  :: "'\<beta> \<Longrightarrow> '\<alpha>"
  mright :: "'\<gamma> \<Longrightarrow> '\<alpha>"

text {* Separating simulations. I assume that the value of ok' should track the value
  of n.ok'. *}

definition "U0 = ($0-\<Sigma>\<acute> =\<^sub>u $\<Sigma>)"

definition "U1 = ($1-\<Sigma>\<acute> =\<^sub>u $\<Sigma>)"

declare U0_def [upred_defs]
declare U1_def [upred_defs]
  
text {* The following implementation of parallel by merge is less general than the book version, in
  that it does not properly partition the alphabet into two disjoint segments. We could actually
  achieve this specifying lenses into the larger alphabet, but this would complicate the definition
  of programs. May reconsider later. *}

definition par_by_merge  ("_ \<parallel>\<^bsub>_\<^esub> _" [85,0,86] 85) 
where [upred_defs]: "P \<parallel>\<^bsub>M\<^esub> Q = ((((P ;; U0) \<and> (Q ;; U1) \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>)) ;; M)"

text {* swap is a predicate that the swaps the left and right indices; it is used to specify commutativity of the parallel operator *}

definition "swap\<^sub>m = (0-\<Sigma>,1-\<Sigma> := &1-\<Sigma>,&0-\<Sigma>)"

declare swap\<^sub>m_def [upred_defs]

lemma U0_swap: "(U0 ;; swap\<^sub>m) = U1"
  by (rel_auto)

lemma U1_swap: "(U1 ;; swap\<^sub>m) = U0"
  by (rel_auto)

lemma swap_merge_par_distl:
  assumes "P is H1_H2" "Q is H1_H2"
  shows "((P \<parallel> Q) ;; swap\<^sub>m) = (P ;; swap\<^sub>m) \<parallel> (Q ;; swap\<^sub>m)"
proof -
  obtain P\<^sub>1 P\<^sub>2 where P: "P = P\<^sub>1 \<turnstile>\<^sub>r P\<^sub>2"
    by (metis H1_H2_commute H1_H2_is_rdesign H2_idem Healthy_def assms(1))
  obtain Q\<^sub>1 Q\<^sub>2 where Q: "Q = Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2"
   by (metis H1_H2_commute H1_H2_is_rdesign H2_idem Healthy_def assms(2))
  have "(((P\<^sub>1 \<turnstile>\<^sub>r P\<^sub>2) \<parallel> (Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2)) ;; swap\<^sub>m) = 
        (\<not> (\<not> P\<^sub>1 \<or> \<not> Q\<^sub>1 ;; true)) \<turnstile>\<^sub>r ((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<and> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2) ;; \<langle>[&0-\<Sigma> \<mapsto>\<^sub>s &1-\<Sigma>, &1-\<Sigma> \<mapsto>\<^sub>s &0-\<Sigma>]\<rangle>\<^sub>a)"
    by (simp add: design_par_def swap\<^sub>m_def assigns_d_def rdesign_composition)
  also have "... =  (\<not> (\<not> P\<^sub>1 \<or> \<not> Q\<^sub>1 ;; true)) \<turnstile>\<^sub>r (((P\<^sub>1 \<Rightarrow> P\<^sub>2) ;; \<langle>[&0-\<Sigma> \<mapsto>\<^sub>s &1-\<Sigma>, &1-\<Sigma> \<mapsto>\<^sub>s &0-\<Sigma>]\<rangle>\<^sub>a) \<and> ((Q\<^sub>1 \<Rightarrow> Q\<^sub>2) ;; \<langle>[&0-\<Sigma> \<mapsto>\<^sub>s &1-\<Sigma>, &1-\<Sigma> \<mapsto>\<^sub>s &0-\<Sigma>]\<rangle>\<^sub>a))"
    by (rel_auto)
  also have "... = ((P\<^sub>1 \<turnstile>\<^sub>r P\<^sub>2) ;; swap\<^sub>m) \<parallel> ((Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2) ;; swap\<^sub>m)"
    by (simp add: design_par_def swap\<^sub>m_def assigns_d_def rdesign_composition, rel_auto)
  finally show ?thesis
    using P Q by blast
qed

lemma par_by_merge_left_zero:
  assumes "M is H1"
  shows "true \<parallel>\<^bsub>M\<^esub> P = true"
proof -
  have "true \<parallel>\<^bsub>M\<^esub> P = ((true ;; U0) \<parallel> (P ;; U1) ;; M)" (is "_ = ((?P \<parallel> ?Q) ;; ?M)")
    by (simp add: par_by_merge_def)
  moreover have "?P = true"
    by (rel_auto)
  ultimately show ?thesis
    by (metis H1_left_zero assms parallel_comm parallel_zero)
qed

lemma par_by_merge_right_zero:
  assumes "M is H1"
  shows "P \<parallel>\<^bsub>M\<^esub> true = true"
proof -
  have "P \<parallel>\<^bsub>M\<^esub> true = ((P ;; U0) \<parallel> (true ;; U1) ;; M)" (is "_ = ((?P \<parallel> ?Q) ;; ?M)")
    by (simp add: par_by_merge_def)
  moreover have "?Q = true"
    by (rel_auto)
  ultimately show ?thesis
    by (metis H1_left_zero assms parallel_comm parallel_zero)
qed

lemma par_by_merge_commute:
  assumes "(swap\<^sub>m ;; M) = M"
  shows "P \<parallel>\<^bsub>M\<^esub> Q = Q \<parallel>\<^bsub>M\<^esub> P"
proof -
  have "P \<parallel>\<^bsub>M\<^esub> Q = (((P ;; U0) \<and> (Q ;; U1) \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) ;; M)"
    by (simp add: par_by_merge_def)
  also have "... = ((((P ;; U0) \<and> (Q ;; U1) \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) ;; swap\<^sub>m) ;; M)"
    by (metis assms seqr_assoc)
  also have "... = (((P ;; U0 ;; swap\<^sub>m) \<and> (Q ;; U1 ;; swap\<^sub>m) \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) ;; M)"
    by rel_tac
  also have "... = (((P ;; U1) \<and> (Q ;; U0) \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) ;; M)"
    by (simp add: U0_swap U1_swap)
  also have "... = Q \<parallel>\<^bsub>M\<^esub> P"
    by (simp add: par_by_merge_def utp_pred.inf.left_commute)
  finally show ?thesis .
qed

lemma par_by_merge_mono_1:
  assumes "P\<^sub>1 \<sqsubseteq> P\<^sub>2"
  shows "P\<^sub>1 \<parallel>\<^bsub>M\<^esub> Q \<sqsubseteq> P\<^sub>2 \<parallel>\<^bsub>M\<^esub> Q"
  using assms by (rel_tac)

lemma par_by_merge_mono_2:
  assumes "Q\<^sub>1 \<sqsubseteq> Q\<^sub>2"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q\<^sub>1) \<sqsubseteq> (P \<parallel>\<^bsub>M\<^esub> Q\<^sub>2)"
  using assms by rel_blast
end