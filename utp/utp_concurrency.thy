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

definition U0\<alpha> where [upred_defs]: "U0\<alpha> = (1\<^sub>L \<times>\<^sub>L out_var fst\<^sub>L)"

definition U1\<alpha> where [upred_defs]: "U1\<alpha> = (1\<^sub>L \<times>\<^sub>L out_var snd\<^sub>L)"

abbreviation U0_alpha_lift ("\<lceil>_\<rceil>\<^sub>0") where "\<lceil>P\<rceil>\<^sub>0 \<equiv> P \<oplus>\<^sub>p U0\<alpha>"

abbreviation U1_alpha_lift ("\<lceil>_\<rceil>\<^sub>1") where "\<lceil>P\<rceil>\<^sub>1 \<equiv> P \<oplus>\<^sub>p U1\<alpha>"

text {* We implement the following useful abbreviation for separating of two parallel processes and
  copying of the before variables, all to act as input to the merge predicate. *}
  
abbreviation par_sep (infixl "\<parallel>\<^sub>s" 85) where
"P \<parallel>\<^sub>s Q \<equiv> (P ;; U0) \<and> (Q ;; U1) \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>"

text {* The following implementation of parallel by merge is less general than the book version, in
  that it does not properly partition the alphabet into two disjoint segments. We could actually
  achieve this specifying lenses into the larger alphabet, but this would complicate the definition
  of programs. May reconsider later. *}

definition par_by_merge  ("_ \<parallel>\<^bsub>_\<^esub> _" [85,0,86] 85) 
where [upred_defs]: "P \<parallel>\<^bsub>M\<^esub> Q = (P \<parallel>\<^sub>s Q ;; M)"

text {* nil is the merge predicate which ignores the output of both parallel predicates *}

definition [upred_defs]: "nil\<^sub>m = ($\<Sigma>\<acute> =\<^sub>u $\<Sigma>\<^sub><)"

text {* swap is a predicate that the swaps the left and right indices; it is used to specify commutativity of the parallel operator *}

definition [upred_defs]: "swap\<^sub>m = (0-\<Sigma>,1-\<Sigma> := &1-\<Sigma>,&0-\<Sigma>)"

lemma U0_swap: "(U0 ;; swap\<^sub>m) = U1"
  by rel_auto

lemma U1_swap: "(U1 ;; swap\<^sub>m) = U0"
  by rel_auto

text {* We can equivalently express separating simulations using alphabet extrusion *}

lemma U0_as_alpha: "(P ;; U0) = \<lceil>P\<rceil>\<^sub>0"
  by rel_auto

lemma U1_as_alpha: "(P ;; U1) = \<lceil>P\<rceil>\<^sub>1"
  by rel_auto

lemma U0\<alpha>_vwb_lens [simp]: "vwb_lens U0\<alpha>"
  by (simp add: U0\<alpha>_def id_vwb_lens prod_vwb_lens)

lemma U1\<alpha>_vwb_lens [simp]: "vwb_lens U1\<alpha>"
  by (simp add: U1\<alpha>_def id_vwb_lens prod_vwb_lens)

lemma U0_alpha_out_var [alpha]: "\<lceil>$x\<acute>\<rceil>\<^sub>0 = $0-x\<acute>"
  by (rel_auto)

lemma U1_alpha_out_var [alpha]: "\<lceil>$x\<acute>\<rceil>\<^sub>1 = $1-x\<acute>"
  by (rel_auto)

lemma U0\<alpha>_comp_in_var [alpha]: "(in_var x) ;\<^sub>L U0\<alpha> = in_var x"
  by (simp add: U0\<alpha>_def alpha_in_var in_var_prod_lens pre_uvar_def)

lemma U0\<alpha>_comp_out_var [alpha]: "(out_var x) ;\<^sub>L U0\<alpha> = out_var (left_uvar x)"
  by (simp add: U0\<alpha>_def alpha_out_var id_wb_lens left_uvar_def out_var_prod_lens)

lemma U1\<alpha>_comp_in_var [alpha]: "(in_var x) ;\<^sub>L U1\<alpha> = in_var x"
  by (simp add: U1\<alpha>_def alpha_in_var in_var_prod_lens pre_uvar_def)

lemma U1\<alpha>_comp_out_var [alpha]: "(out_var x) ;\<^sub>L U1\<alpha> = out_var (right_uvar x)"
  by (simp add: U1\<alpha>_def alpha_out_var id_wb_lens right_uvar_def out_var_prod_lens)

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

lemma shEx_pbm_left: "((\<^bold>\<exists> x \<bullet> P x) \<parallel>\<^bsub>M\<^esub> Q) = (\<^bold>\<exists> x \<bullet> (P x \<parallel>\<^bsub>M\<^esub> Q))"
  by (rel_auto)

lemma shEx_pbm_right: "(P \<parallel>\<^bsub>M\<^esub> (\<^bold>\<exists> x \<bullet> Q x)) = (\<^bold>\<exists> x \<bullet> (P \<parallel>\<^bsub>M\<^esub> Q x))"
  by (rel_auto)

lemma par_by_merge_mono_1:
  assumes "P\<^sub>1 \<sqsubseteq> P\<^sub>2"
  shows "P\<^sub>1 \<parallel>\<^bsub>M\<^esub> Q \<sqsubseteq> P\<^sub>2 \<parallel>\<^bsub>M\<^esub> Q"
  using assms by (rel_auto)

lemma par_by_merge_mono_2:
  assumes "Q\<^sub>1 \<sqsubseteq> Q\<^sub>2"
  shows "(P \<parallel>\<^bsub>M\<^esub> Q\<^sub>1) \<sqsubseteq> (P \<parallel>\<^bsub>M\<^esub> Q\<^sub>2)"
  using assms by rel_blast

end