section {* Concurrent programming *}

theory utp_concurrency
  imports utp_rel
begin

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

lemma par_by_merge_commute:
  assumes "(swap\<^sub>m ;; M) = M"
  shows "P \<parallel>\<^bsub>M\<^esub> Q = Q \<parallel>\<^bsub>M\<^esub> P"
proof -
  have "P \<parallel>\<^bsub>M\<^esub> Q = (((P ;; U0) \<and> (Q ;; U1) \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) ;; M)"
    by (simp add: par_by_merge_def)
  also have "... = ((((P ;; U0) \<and> (Q ;; U1) \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) ;; swap\<^sub>m) ;; M)"
    by (metis assms seqr_assoc)
  also have "... = (((P ;; U0 ;; swap\<^sub>m) \<and> (Q ;; U1 ;; swap\<^sub>m) \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) ;; M)"
    by rel_auto
  also have "... = (((P ;; U1) \<and> (Q ;; U0) \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) ;; M)"
    by (simp add: U0_swap U1_swap)
  also have "... = Q \<parallel>\<^bsub>M\<^esub> P"
    by (simp add: par_by_merge_def utp_pred.inf.left_commute)
  finally show ?thesis .
qed

lemma par_by_merge_mono_1:
  assumes "P\<^sub>1 \<sqsubseteq> P\<^sub>2"
  shows "P\<^sub>1 \<parallel>\<^bsub>M\<^esub> Q \<sqsubseteq> P\<^sub>2 \<parallel>\<^bsub>M\<^esub> Q"
  using assms by (rel_auto)

lemma par_by_merge_mono_2:
  assumes "Q\<^sub>1 \<sqsubseteq> Q\<^sub>2"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q\<^sub>1) \<sqsubseteq> (P \<parallel>\<^bsub>M\<^esub> Q\<^sub>2)"
  using assms by rel_blast
end