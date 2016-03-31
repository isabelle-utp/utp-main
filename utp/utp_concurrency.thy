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

subsection {* Parallel by merge *}

text {* We describe the partition of a state space into two pieces. *}

type_synonym '\<alpha> partition = "'\<alpha> \<times> '\<alpha>"

definition "left_uvar x = x ;\<^sub>L fst\<^sub>L ;\<^sub>L snd\<^sub>L ;\<^sub>L des_lens"

definition "right_uvar x = x ;\<^sub>L snd\<^sub>L ;\<^sub>L snd\<^sub>L ;\<^sub>L des_lens"

declare left_uvar_def [upred_defs]

declare right_uvar_def [upred_defs]

text {* Extract the ith element of the second part *}

definition "ind_uvar i x = x ;\<^sub>L list_lens i ;\<^sub>L snd\<^sub>L ;\<^sub>L des_lens"

definition "pre_uvar x = x ;\<^sub>L fst\<^sub>L ;\<^sub>L des_lens"

definition "in_ind_uvar i x = in_var (ind_uvar i x)"

definition "out_ind_uvar i x = out_var (ind_uvar i x)"

definition "in_pre_uvar x = in_var (pre_uvar x)"

definition "out_pre_uvar x = out_var (pre_uvar x)"

definition "in_ind_uexpr i x = var (in_ind_uvar i x)"

definition "out_ind_uexpr i x = var (out_ind_uvar i x)"

definition "in_pre_uexpr x = var (in_pre_uvar x)"

definition "out_pre_uexpr x = var (out_pre_uvar x)"


declare ind_uvar_def [urel_defs]
declare ind_uvar_def [upred_defs]

declare in_ind_uvar_def [upred_defs]
declare out_ind_uvar_def [upred_defs]

declare in_ind_uexpr_def [upred_defs]
declare out_ind_uexpr_def [upred_defs]

declare in_pre_uexpr_def [upred_defs]
declare out_pre_uexpr_def [upred_defs]

lemma left_uvar_indep_right_uvar [simp]:
  "left_uvar x \<bowtie> right_uvar y"
  apply (simp add: left_uvar_def right_uvar_def lens_comp_assoc[THEN sym])
  apply (metis in_out_indep in_var_def lens_indep_left_comp out_var_def out_var_indep uvar_des_lens vwb_lens_mwb)
done

lemma right_uvar_indep_left_uvar [simp]:
  "right_uvar x \<bowtie> left_uvar y"
  by (simp add: lens_indep_sym)

lemma left_uvar [simp]: "uvar x \<Longrightarrow> uvar (left_uvar x)"
  by (simp add: left_uvar_def comp_vwb_lens fst_vwb_lens snd_vwb_lens)

lemma right_uvar [simp]: "uvar x \<Longrightarrow> uvar (right_uvar x)"
  by (simp add: right_uvar_def comp_vwb_lens fst_vwb_lens snd_vwb_lens)

lemma ind_uvar_indep [simp]:
  "\<lbrakk>mwb_lens x; i \<noteq> j\<rbrakk> \<Longrightarrow> ind_uvar i x \<bowtie> ind_uvar j x"
  apply (simp add: ind_uvar_def lens_comp_assoc[THEN sym])
  apply (metis lens_indep_left_comp lens_indep_right_comp list_lens_indep out_var_def out_var_indep uvar_des_lens vwb_lens_mwb)
done

lemma ind_uvar_semi_uvar [simp]:
  "semi_uvar x \<Longrightarrow> semi_uvar (ind_uvar i x)"
  by (auto intro!: comp_mwb_lens list_mwb_lens simp add: ind_uvar_def snd_vwb_lens)

lemma in_ind_uvar_semi_uvar [simp]:
  "semi_uvar x \<Longrightarrow> semi_uvar (in_ind_uvar i x)"
  by (simp add: in_ind_uvar_def)

lemma out_ind_uvar_semi_uvar [simp]:
  "semi_uvar x \<Longrightarrow> semi_uvar (out_ind_uvar i x)"
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

type_synonym '\<alpha> merge = "('\<alpha> alphabet_d \<times> '\<alpha> alphabet_d partition, '\<alpha>) relation_d"

text {* Separating simulations. I assume that the value of ok' should track the value
  of n.ok'. *}


definition "U0 = (($0-\<Sigma>\<acute> =\<^sub>u $\<Sigma>) \<and> ($ok\<acute> =\<^sub>u $ok))"

definition "U1 = (($1-\<Sigma>\<acute> =\<^sub>u $\<Sigma>) \<and> ($ok\<acute> =\<^sub>u $ok))"

declare U0_def [upred_defs]
declare U1_def [upred_defs]

text {* The following implementation of parallel by merge is less general than the book version, in
  that it does not properly partition the alphabet into two disjoint segments. We could actually
  achieve this specifying lenses into the larger alphabet, but this would complicate the definition
  of programs. May reconsider later. *}

definition par_by_merge :: 
  "'\<alpha> hrelation_d \<Rightarrow> '\<alpha> merge \<Rightarrow> '\<alpha> hrelation_d \<Rightarrow> '\<alpha> hrelation_d" (infixr "\<parallel>\<^bsub>_\<^esub>" 85) 
where "P \<parallel>\<^bsub>M\<^esub> Q = ((((P ;; U0) \<parallel> (Q ;; U1)) \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) ;; M)"

term "$0-\<Sigma>"

definition "swap\<^sub>m = 0-\<Sigma>,1-\<Sigma> :=\<^sub>D &1-\<Sigma>, &0-\<Sigma>"

declare One_nat_def [simp del]

declare swap\<^sub>m_def [upred_defs]

(*
lemma merge_swap_swap: "(swap\<^sub>m ;; swap\<^sub>m) = II\<^sub>D"
  apply (simp add: swap\<^sub>m_def in_ind_uexpr_def in_ind_uvar_def assigns_comp usubst unrest)
  apply (subst usubst_upd_comm)
  apply (simp_all add: usubst_upd_idem)
  apply (subst usubst_upd_comm)
  apply (simp_all add: usubst_upd_idem)
  apply (subst usubst_upd_var_id)
  apply (simp)
  apply (simp add: usubst)
  apply (simp add: skip_r_def)
done
*)  

end