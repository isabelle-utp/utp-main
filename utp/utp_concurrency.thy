section {* Concurrent programming *}

theory utp_concurrency
  imports utp_designs
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
    by (simp add: design_par_def skip_d_def rdesign_composition, rel_tac)
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

lemma parallel_mono_1:
  assumes "P\<^sub>1 \<sqsubseteq> P\<^sub>2" "P\<^sub>1 is H1_H2" "P\<^sub>2 is H1_H2"
  shows "P\<^sub>1 \<parallel> Q \<sqsubseteq> P\<^sub>2 \<parallel> Q"
proof -
  have "pre\<^sub>D(P\<^sub>1) \<turnstile>\<^sub>r post\<^sub>D(P\<^sub>1) \<sqsubseteq> pre\<^sub>D(P\<^sub>2) \<turnstile>\<^sub>r post\<^sub>D(P\<^sub>2)"
    by (metis H1_H2_commute H1_H2_is_rdesign H1_idem Healthy_def' assms)
  hence "(pre\<^sub>D(P\<^sub>1) \<turnstile>\<^sub>r post\<^sub>D(P\<^sub>1)) \<parallel> Q \<sqsubseteq> (pre\<^sub>D(P\<^sub>2) \<turnstile>\<^sub>r post\<^sub>D(P\<^sub>2)) \<parallel> Q" 
    by (auto simp add: rdesign_refinement design_par_def) (pred_tac+)
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

definition "ind_uvar i x = x ;\<^sub>L list_lens i ;\<^sub>L snd\<^sub>L ;\<^sub>L des_lens"

definition "pre_uvar x = x ;\<^sub>L fst\<^sub>L"

definition "in_ind_uvar i x = in_var (ind_uvar i x)"

definition "out_ind_uvar i x = out_var (ind_uvar i x)"

definition "in_pre_uvar x = in_var (pre_uvar x)"

definition "out_pre_uvar x = out_var (pre_uvar x)"

definition "in_ind_uexpr i x = var (in_ind_uvar i x)"

definition "out_ind_uexpr i x = var (out_ind_uvar i x)"

definition "in_pre_uexpr x = var (in_pre_uvar x)"

definition "out_pre_uexpr x = var (out_pre_uvar x)"

declare ind_uvar_def [upred_defs]
declare pre_uvar_def [upred_defs]

declare in_ind_uvar_def [upred_defs]
declare out_ind_uvar_def [upred_defs]

declare in_ind_uexpr_def [upred_defs]
declare out_ind_uexpr_def [upred_defs]

declare in_pre_uexpr_def [upred_defs]
declare out_pre_uexpr_def [upred_defs]

lemma left_uvar_indep_right_uvar [simp]:
  "left_uvar x \<bowtie> right_uvar y"
  apply (simp add: left_uvar_def right_uvar_def lens_comp_assoc[THEN sym])
  apply (metis in_out_indep in_var_def lens_indep_left_comp out_var_def out_var_indep vwb_des_lens vwb_lens_mwb)
done

lemma right_uvar_indep_left_uvar [simp]:
  "right_uvar x \<bowtie> left_uvar y"
  by (simp add: lens_indep_sym)

lemma left_uvar [simp]: "vwb_lens x \<Longrightarrow> vwb_lens (left_uvar x)"
  by (simp add: left_uvar_def comp_vwb_lens fst_vwb_lens snd_vwb_lens)

lemma right_uvar [simp]: "vwb_lens x \<Longrightarrow> vwb_lens (right_uvar x)"
  by (simp add: right_uvar_def comp_vwb_lens fst_vwb_lens snd_vwb_lens)

lemma ind_uvar_indep [simp]:
  "\<lbrakk>mwb_lens x; i \<noteq> j\<rbrakk> \<Longrightarrow> ind_uvar i x \<bowtie> ind_uvar j x"
  apply (simp add: ind_uvar_def lens_comp_assoc[THEN sym])
  apply (metis lens_indep_left_comp lens_indep_right_comp list_lens_indep out_var_def out_var_indep vwb_des_lens vwb_lens_mwb)
done

lemma ind_uvar_mwb_lens [simp]:
  "mwb_lens x \<Longrightarrow> mwb_lens (ind_uvar i x)"
  by (auto intro!: comp_mwb_lens list_mwb_lens simp add: ind_uvar_def snd_vwb_lens)

lemma in_ind_uvar_mwb_lens [simp]:
  "mwb_lens x \<Longrightarrow> mwb_lens (in_ind_uvar i x)"
  by (simp add: in_ind_uvar_def)

lemma out_ind_uvar_mwb_lens [simp]:
  "mwb_lens x \<Longrightarrow> mwb_lens (out_ind_uvar i x)"
  by (simp add: out_ind_uvar_def)

declare id_vwb_lens [simp]  

syntax
  "_svarpre"   :: "svid \<Rightarrow> svid" ("_\<^sub><" [999] 999)
  "_svarleft"  :: "svid \<Rightarrow> svid" ("0-_" [999] 999)
  "_svarright" :: "svid \<Rightarrow> svid" ("1-_" [999] 999)

translations
  "_svarpre x" == "CONST pre_uvar x"
  "_svarleft x" == "CONST left_uvar x"
  "_svarright x" == "CONST right_uvar x"

type_synonym '\<alpha> merge = "('\<alpha> \<times> '\<alpha> partition, '\<alpha>) relation_d"

text {* Separating simulations. I assume that the value of ok' should track the value
  of n.ok'. *}

definition "U0 = (true \<turnstile>\<^sub>r ($0-\<Sigma>\<acute> =\<^sub>u $\<Sigma> \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>))"

definition "U1 = (true \<turnstile>\<^sub>r ($1-\<Sigma>\<acute> =\<^sub>u $\<Sigma> \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>))"

declare U0_def [upred_defs]
declare U1_def [upred_defs]
  
text {* The following implementation of parallel by merge is less general than the book version, in
  that it does not properly partition the alphabet into two disjoint segments. We could actually
  achieve this specifying lenses into the larger alphabet, but this would complicate the definition
  of programs. May reconsider later. *}

definition par_by_merge :: 
  "'\<alpha> hrelation_d \<Rightarrow> '\<alpha> merge \<Rightarrow> '\<alpha> hrelation_d \<Rightarrow> '\<alpha> hrelation_d" (infixr "\<parallel>\<^bsub>_\<^esub>" 85) 
where "P \<parallel>\<^bsub>M\<^esub> Q = ((((P ;; U0) \<parallel> (Q ;; U1))) ;; M)"

definition "swap\<^sub>m = true \<turnstile>\<^sub>r (0-\<Sigma>,1-\<Sigma> := &1-\<Sigma>, &0-\<Sigma>)"

declare One_nat_def [simp del]

declare swap\<^sub>m_def [upred_defs]

lemma U0_H1_H2: "U0 is H1_H2"
  by (simp add: U0_def rdesign_is_H1_H2)

lemma U0_swap: "(U0 ;; swap\<^sub>m) = U1"
  apply (simp add: U0_def swap\<^sub>m_def rdesign_composition)
  apply (subst seqr_and_distl_uinj)
  using assigns_r_swap_uinj id_vwb_lens left_uvar right_uvar apply fastforce
  apply (rel_tac)
done

lemma U1_H1_H2: "U1 is H1_H2"
  by (simp add: U1_def rdesign_is_H1_H2)

lemma U1_swap: "(U1 ;; swap\<^sub>m) = U0"
  apply (simp add: U1_def swap\<^sub>m_def rdesign_composition)
  apply (subst seqr_and_distl_uinj)
  using assigns_r_swap_uinj id_vwb_lens left_uvar right_uvar apply fastforce
  apply (rel_tac)
done

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
    by (simp add: design_par_def swap\<^sub>m_def rdesign_composition)
  also have "... =  (\<not> (\<not> P\<^sub>1 \<or> \<not> Q\<^sub>1 ;; true)) \<turnstile>\<^sub>r (((P\<^sub>1 \<Rightarrow> P\<^sub>2) ;; \<langle>[&0-\<Sigma> \<mapsto>\<^sub>s &1-\<Sigma>, &1-\<Sigma> \<mapsto>\<^sub>s &0-\<Sigma>]\<rangle>\<^sub>a) \<and> ((Q\<^sub>1 \<Rightarrow> Q\<^sub>2) ;; \<langle>[&0-\<Sigma> \<mapsto>\<^sub>s &1-\<Sigma>, &1-\<Sigma> \<mapsto>\<^sub>s &0-\<Sigma>]\<rangle>\<^sub>a))"
    apply (subst seqr_and_distl_uinj)
    using assigns_r_swap_uinj id_vwb_lens left_uvar right_uvar apply fastforce
    apply (simp)
  done

  also have "... = ((P\<^sub>1 \<turnstile>\<^sub>r P\<^sub>2) ;; swap\<^sub>m) \<parallel> ((Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2) ;; swap\<^sub>m)"
    by (simp add: design_par_def swap\<^sub>m_def rdesign_composition, rel_tac)

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
    by (rel_tac)
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
    by (rel_tac)
  ultimately show ?thesis
    by (metis H1_left_zero assms parallel_comm parallel_zero)
qed
  
lemma par_by_merge_commute:
  assumes "P is H1_H2" "Q is H1_H2" "M = (swap\<^sub>m ;; M)"
  shows "P \<parallel>\<^bsub>M\<^esub> Q = Q \<parallel>\<^bsub>M\<^esub> P"
proof -
  have "P \<parallel>\<^bsub>M\<^esub> Q = (((P ;; U0) \<parallel> (Q ;; U1)) ;; M)"
    by (simp add: par_by_merge_def)
  also have "... = ((((P ;; U0) \<parallel> (Q ;; U1)) ;; swap\<^sub>m) ;; M)"
    by (metis assms(3) seqr_assoc)
  also have "... = (((P ;; U0 ;; swap\<^sub>m) \<parallel> (Q ;; U1 ;; swap\<^sub>m)) ;; M)"
    by (simp add: U0_def U1_def assms(1) assms(2) rdesign_is_H1_H2 seq_r_H1_H2_closed seqr_assoc swap_merge_par_distl)
  also have "... = (((P ;; U1) \<parallel> (Q ;; U0)) ;; M)"
    by (simp add: U0_swap U1_swap)
  also have "... = Q \<parallel>\<^bsub>M\<^esub> P"
    by (simp add: par_by_merge_def parallel_comm)
  finally show ?thesis .
qed

lemma par_by_merge_mono_1:
  assumes "P\<^sub>1 \<sqsubseteq> P\<^sub>2" "P\<^sub>1 is H1_H2" "P\<^sub>2 is H1_H2"
  shows "P\<^sub>1 \<parallel>\<^bsub>M\<^esub> Q \<sqsubseteq> P\<^sub>2 \<parallel>\<^bsub>M\<^esub> Q"
  using assms
  by (auto intro:seqr_mono parallel_mono_1 seq_r_H1_H2_closed U0_H1_H2 U1_H1_H2 simp add: par_by_merge_def)

lemma par_by_merge_mono_2:
  assumes "Q\<^sub>1 \<sqsubseteq> Q\<^sub>2" "Q\<^sub>1 is H1_H2" "Q\<^sub>2 is H1_H2"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q\<^sub>1) \<sqsubseteq> (P \<parallel>\<^bsub>M\<^esub> Q\<^sub>2)"
  using assms
  by (auto intro:seqr_mono parallel_mono_2 seq_r_H1_H2_closed U0_H1_H2 U1_H1_H2 simp add: par_by_merge_def)

end