section {* Concurrent programming *}

theory utp_concurrency
  imports utp_rel
begin

text {* In parallel-by-merge constructions, a merge predicate defines the behaviour following execution of
        of parallel processes, P || Q, as a relation that merges the output of P and Q. In order to achieve
        this we need to separate the variable values output from P and Q, and in addition the variable values 
        before execution. The following three constructs do these separations. *}

definition [upred_defs]: "left_uvar x = x ;\<^sub>L fst\<^sub>L ;\<^sub>L snd\<^sub>L"

definition [upred_defs]: "right_uvar x = x ;\<^sub>L snd\<^sub>L ;\<^sub>L snd\<^sub>L"

definition [upred_defs]: "pre_uvar x = x ;\<^sub>L fst\<^sub>L"

lemma left_uvar_indep_right_uvar [simp]:
  "left_uvar x \<bowtie> right_uvar y"
  apply (simp add: left_uvar_def right_uvar_def lens_comp_assoc[THEN sym])
  apply (simp add: alpha_in_var alpha_out_var)
done

lemma right_uvar_indep_left_uvar [simp]:
  "right_uvar x \<bowtie> left_uvar y"
  by (simp add: lens_indep_sym)

lemma left_uvar [simp]: "vwb_lens x \<Longrightarrow> vwb_lens (left_uvar x)"
  by (simp add: left_uvar_def )

lemma right_uvar [simp]: "vwb_lens x \<Longrightarrow> vwb_lens (right_uvar x)"
  by (simp add: right_uvar_def)

syntax
  "_svarpre"   :: "svid \<Rightarrow> svid" ("_\<^sub><" [999] 999)
  "_svarleft"  :: "svid \<Rightarrow> svid" ("0-_" [999] 999)
  "_svarright" :: "svid \<Rightarrow> svid" ("1-_" [999] 999)

translations
  "_svarpre x" == "CONST pre_uvar x"
  "_svarleft x" == "CONST left_uvar x"
  "_svarright x" == "CONST right_uvar x"

type_synonym '\<alpha> merge = "('\<alpha> \<times> ('\<alpha> \<times> '\<alpha>), '\<alpha>) relation"

text {* U0 and U1 are relations that index all input variables x to 0-x and 1-x, respectively. *}

definition [upred_defs]: "U0 = ($0-\<Sigma>\<acute> =\<^sub>u $\<Sigma>)"

definition [upred_defs]: "U1 = ($1-\<Sigma>\<acute> =\<^sub>u $\<Sigma>)"

text {* As shown below, separating simulations can also be expressed using the following two alphabet extrusions *}

definition U0_alpha ("\<lceil>_\<rceil>\<^sub>0") where [upred_defs]: "\<lceil>P\<rceil>\<^sub>0 = P \<oplus>\<^sub>p (1\<^sub>L \<times>\<^sub>L out_var fst\<^sub>L)"

definition U1_alpha ("\<lceil>_\<rceil>\<^sub>1") where [upred_defs]: "\<lceil>P\<rceil>\<^sub>1 \<equiv> P \<oplus>\<^sub>p (1\<^sub>L \<times>\<^sub>L out_var snd\<^sub>L)"
  
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
  by rel_auto

lemma U1_swap: "(U1 ;; swap\<^sub>m) = U0"
  by rel_auto

text {* We can equivalently express separating simulations using alphabet extrusion *}

lemma U0_as_alpha: "(P ;; U0) = \<lceil>P\<rceil>\<^sub>0"
  by rel_auto

lemma U1_as_alpha: "(P ;; U1) = \<lceil>P\<rceil>\<^sub>1"
  by rel_auto

lemma U0_alpha_out_var [alpha]: "\<lceil>$x\<acute>\<rceil>\<^sub>0 = $0-x\<acute>"
  by (rel_auto)

lemma U1_alpha_out_var [alpha]: "\<lceil>$x\<acute>\<rceil>\<^sub>1 = $1-x\<acute>"
  by (rel_auto)

lemma U0_seq_subst: "(P ;; U0)\<lbrakk>\<guillemotleft>v\<guillemotright>/$0-x\<acute>\<rbrakk> = (P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> ;; U0)" 
  by rel_auto

lemma U1_seq_subst: "(P ;; U1)\<lbrakk>\<guillemotleft>v\<guillemotright>/$1-x\<acute>\<rbrakk> = (P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> ;; U1)"
  by rel_auto

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