section {* Concurrent programming *}

theory utp_concurrency
  imports utp_rel utp_tactics
begin

subsection {* Variable renamings *}
  
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

lemma left_uvar_indep_pre_uvar [simp]:
  "left_uvar x \<bowtie> pre_uvar y"
  apply (simp add: left_uvar_def pre_uvar_def)
  using fst_snd_lens_indep lens_indep_sym apply blast
done
  
lemma left_uvar_indep_left_uvar [simp]:
  "x \<bowtie> y \<Longrightarrow> left_uvar x \<bowtie> left_uvar y"
  by (simp add: left_uvar_def)
  
lemma right_uvar_indep_left_uvar [simp]:
  "right_uvar x \<bowtie> left_uvar y"
  by (simp add: lens_indep_sym)
    
lemma right_uvar_indep_pre_uvar [simp]:
  "right_uvar x \<bowtie> pre_uvar y"
  apply (simp add: right_uvar_def pre_uvar_def)
  using fst_snd_lens_indep lens_indep_sym apply blast
done
    
lemma right_uvar_indep_right_uvar [simp]:
  "x \<bowtie> y \<Longrightarrow> right_uvar x \<bowtie> right_uvar y"
  by (simp add: right_uvar_def)

lemma pre_uvar_indep_left_uvar [simp]:
  "pre_uvar x \<bowtie> left_uvar y"
  by (simp add: lens_indep_sym)

lemma pre_uvar_indep_right_uvar [simp]:
  "pre_uvar x \<bowtie> right_uvar y"
  by (simp add: lens_indep_sym)

lemma pre_uvar_indep_pre_uvar [simp]:
  "x \<bowtie> y \<Longrightarrow> pre_uvar x \<bowtie> pre_uvar y"
  by (simp add: pre_uvar_def)
    
lemma left_uvar [simp]: "vwb_lens x \<Longrightarrow> vwb_lens (left_uvar x)"
  by (simp add: left_uvar_def )

lemma right_uvar [simp]: "vwb_lens x \<Longrightarrow> vwb_lens (right_uvar x)"
  by (simp add: right_uvar_def)

lemma left_uvar_mwb [simp]: "mwb_lens x \<Longrightarrow> mwb_lens (left_uvar x)"
  by (simp add: left_uvar_def )

lemma right_uvar_mwb [simp]: "mwb_lens x \<Longrightarrow> mwb_lens (right_uvar x)"
  by (simp add: right_uvar_def)

lemma pre_uvar_mwb [simp]: "mwb_lens x \<Longrightarrow> mwb_lens (pre_uvar x)"
  by (simp add: pre_uvar_def)
    
syntax
  "_svarpre"   :: "svid \<Rightarrow> svid" ("_\<^sub><" [999] 999)
  "_svarleft"  :: "svid \<Rightarrow> svid" ("0-_" [999] 999)
  "_svarright" :: "svid \<Rightarrow> svid" ("1-_" [999] 999)

translations
  "_svarpre x" == "CONST pre_uvar x"
  "_svarleft x" == "CONST left_uvar x"
  "_svarright x" == "CONST right_uvar x"

subsection {* Merge predicates *}
  
text {* A merge is then a relation whose input has three parts: the prior variables, the output
  variables of the left predicate, and the output of the right predicate. *}

type_synonym '\<alpha> merge = "('\<alpha> \<times> ('\<alpha> \<times> '\<alpha>), '\<alpha>) rel"
  
text {* nil is the merge predicate which ignores the output of both parallel predicates *}

definition nil\<^sub>m :: "'\<alpha> merge" where
[upred_defs]: "nil\<^sub>m = ($\<Sigma>\<acute> =\<^sub>u $\<Sigma>\<^sub><)"

text {* swap is a predicate that the swaps the left and right indices; it is used to specify 
        commutativity of the parallel operator *}

-- {* TODO: There is an ambiguity below due to list assignment and tuples. *}

definition swap\<^sub>m :: "('\<alpha> \<times> '\<beta> \<times> '\<beta>, '\<alpha> \<times> '\<beta> \<times> '\<beta>) rel" where
[upred_defs]: "swap\<^sub>m = (0-\<Sigma>,1-\<Sigma> := &1-\<Sigma>,&0-\<Sigma>)"
  
subsection {* Separating simulations *}

text {* U0 and U1 are relations that index all input variables x to 0-x and 1-x, respectively. *}

definition [upred_defs]: "U0 = ($0-\<Sigma>\<acute> =\<^sub>u $\<Sigma>)"

definition [upred_defs]: "U1 = ($1-\<Sigma>\<acute> =\<^sub>u $\<Sigma>)"

text {* As shown below, separating simulations can also be expressed using the following two alphabet extrusions *}

definition U0\<alpha> where [upred_defs]: "U0\<alpha> = (1\<^sub>L \<times>\<^sub>L out_var fst\<^sub>L)"

definition U1\<alpha> where [upred_defs]: "U1\<alpha> = (1\<^sub>L \<times>\<^sub>L out_var snd\<^sub>L)"

abbreviation U0_alpha_lift ("\<lceil>_\<rceil>\<^sub>0") where "\<lceil>P\<rceil>\<^sub>0 \<equiv> P \<oplus>\<^sub>p U0\<alpha>"

abbreviation U1_alpha_lift ("\<lceil>_\<rceil>\<^sub>1") where "\<lceil>P\<rceil>\<^sub>1 \<equiv> P \<oplus>\<^sub>p U1\<alpha>"

lemma U0_swap: "(U0 ;; swap\<^sub>m) = U1"
  by (rel_auto)+

lemma U1_swap: "(U1 ;; swap\<^sub>m) = U0"
  by (rel_auto)

text {* We can equivalently express separating simulations using alphabet extrusion *}

lemma U0_as_alpha: "(P ;; U0) = \<lceil>P\<rceil>\<^sub>0"
  by (rel_auto)

lemma U1_as_alpha: "(P ;; U1) = \<lceil>P\<rceil>\<^sub>1"
  by (rel_auto)

lemma U0\<alpha>_vwb_lens [simp]: "vwb_lens U0\<alpha>"
  by (simp add: U0\<alpha>_def id_vwb_lens prod_vwb_lens)

lemma U1\<alpha>_vwb_lens [simp]: "vwb_lens U1\<alpha>"
  by (simp add: U1\<alpha>_def id_vwb_lens prod_vwb_lens)

lemma U0_alpha_out_var [alpha]: "\<lceil>$x\<acute>\<rceil>\<^sub>0 = $0-x\<acute>"
  by (rel_auto)

lemma U1_alpha_out_var [alpha]: "\<lceil>$x\<acute>\<rceil>\<^sub>1 = $1-x\<acute>"
  by (rel_auto)

lemma U0_skip [alpha]: "\<lceil>II\<rceil>\<^sub>0 = ($0-\<Sigma>\<acute> =\<^sub>u $\<Sigma>)"
  by (rel_auto)

lemma U1_skip [alpha]: "\<lceil>II\<rceil>\<^sub>1 = ($1-\<Sigma>\<acute> =\<^sub>u $\<Sigma>)"
  by (rel_auto)
    
lemma U0\<alpha>_comp_in_var [alpha]: "(in_var x) ;\<^sub>L U0\<alpha> = in_var x"
  by (simp add: U0\<alpha>_def alpha_in_var in_var_prod_lens pre_uvar_def)

lemma U0\<alpha>_comp_out_var [alpha]: "(out_var x) ;\<^sub>L U0\<alpha> = out_var (left_uvar x)"
  by (simp add: U0\<alpha>_def alpha_out_var id_wb_lens left_uvar_def out_var_prod_lens)

lemma U1\<alpha>_comp_in_var [alpha]: "(in_var x) ;\<^sub>L U1\<alpha> = in_var x"
  by (simp add: U1\<alpha>_def alpha_in_var in_var_prod_lens pre_uvar_def)

lemma U1\<alpha>_comp_out_var [alpha]: "(out_var x) ;\<^sub>L U1\<alpha> = out_var (right_uvar x)"
  by (simp add: U1\<alpha>_def alpha_out_var id_wb_lens right_uvar_def out_var_prod_lens)

subsection {* Parallel operators *}
    
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

lemma shEx_pbm_left: "((\<^bold>\<exists> x \<bullet> P x) \<parallel>\<^bsub>M\<^esub> Q) = (\<^bold>\<exists> x \<bullet> (P x \<parallel>\<^bsub>M\<^esub> Q))"
  by (rel_auto)

lemma shEx_pbm_right: "(P \<parallel>\<^bsub>M\<^esub> (\<^bold>\<exists> x \<bullet> Q x)) = (\<^bold>\<exists> x \<bullet> (P \<parallel>\<^bsub>M\<^esub> Q x))"
  by (rel_auto)
 
subsection {* Substitution laws *}

text {* Substitution is a little tricky because when we push the expression through the composition
  operator the alphabet of the expression must also change. Consequently for now we only support
  literal substitution, though this could be generalised with suitable alphabet coercsions. We
  need quite a number of variants to support this which are below. *}
    
lemma U0_seq_subst: "(P ;; U0)\<lbrakk>\<guillemotleft>v\<guillemotright>/$0-x\<acute>\<rbrakk> = (P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> ;; U0)"
  by (rel_auto)

lemma U1_seq_subst: "(P ;; U1)\<lbrakk>\<guillemotleft>v\<guillemotright>/$1-x\<acute>\<rbrakk> = (P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> ;; U1)"
  by (rel_auto)
    
lemma lit_pbm_subst [usubst]:
  fixes x :: "(_ \<Longrightarrow> '\<alpha>)"
  shows 
    "\<And> P Q M \<sigma>. \<sigma>($x \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> ((P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>) \<parallel>\<^bsub>M\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<^sub><\<rbrakk>\<^esub> (Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>))"
    "\<And> P Q M \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> (P \<parallel>\<^bsub>M\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk>\<^esub> Q)"    
  by (rel_auto)+

lemma bool_pbm_subst [usubst]:
  fixes x :: "(_ \<Longrightarrow> '\<alpha>)"
  shows
    "\<And> P Q M \<sigma>. \<sigma>($x \<mapsto>\<^sub>s false) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> ((P\<lbrakk>false/$x\<rbrakk>) \<parallel>\<^bsub>M\<lbrakk>false/$x\<^sub><\<rbrakk>\<^esub> (Q\<lbrakk>false/$x\<rbrakk>))"
    "\<And> P Q M \<sigma>. \<sigma>($x \<mapsto>\<^sub>s true) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> ((P\<lbrakk>true/$x\<rbrakk>) \<parallel>\<^bsub>M\<lbrakk>true/$x\<^sub><\<rbrakk>\<^esub> (Q\<lbrakk>true/$x\<rbrakk>))"
    "\<And> P Q M \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s false) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> (P \<parallel>\<^bsub>M\<lbrakk>false/$x\<acute>\<rbrakk>\<^esub> Q)"
    "\<And> P Q M \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s true) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> (P \<parallel>\<^bsub>M\<lbrakk>true/$x\<acute>\<rbrakk>\<^esub> Q)"
  by (rel_auto)+
    
lemma zero_one_pbm_subst [usubst]:
  fixes x :: "(_ \<Longrightarrow> '\<alpha>)"
  shows
    "\<And> P Q M \<sigma>. \<sigma>($x \<mapsto>\<^sub>s 0) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> ((P\<lbrakk>0/$x\<rbrakk>) \<parallel>\<^bsub>M\<lbrakk>0/$x\<^sub><\<rbrakk>\<^esub> (Q\<lbrakk>0/$x\<rbrakk>))"
    "\<And> P Q M \<sigma>. \<sigma>($x \<mapsto>\<^sub>s 1) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> ((P\<lbrakk>1/$x\<rbrakk>) \<parallel>\<^bsub>M\<lbrakk>1/$x\<^sub><\<rbrakk>\<^esub> (Q\<lbrakk>1/$x\<rbrakk>))"
    "\<And> P Q M \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s 0) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> (P \<parallel>\<^bsub>M\<lbrakk>0/$x\<acute>\<rbrakk>\<^esub> Q)"
    "\<And> P Q M \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s 1) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> (P \<parallel>\<^bsub>M\<lbrakk>1/$x\<acute>\<rbrakk>\<^esub> Q)"
  by (rel_auto)+

lemma numeral_pbm_subst [usubst]:
  fixes x :: "(_ \<Longrightarrow> '\<alpha>)"
  shows
    "\<And> P Q M \<sigma>. \<sigma>($x \<mapsto>\<^sub>s numeral n) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> ((P\<lbrakk>numeral n/$x\<rbrakk>) \<parallel>\<^bsub>M\<lbrakk>numeral n/$x\<^sub><\<rbrakk>\<^esub> (Q\<lbrakk>numeral n/$x\<rbrakk>))"
    "\<And> P Q M \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s numeral n) \<dagger> (P \<parallel>\<^bsub>M\<^esub> Q) = \<sigma> \<dagger> (P \<parallel>\<^bsub>M\<lbrakk>numeral n/$x\<acute>\<rbrakk>\<^esub> Q)"
  by (rel_auto)+
    
subsection {* Parallel-by-merge laws *}
    
lemma par_by_merge_false [simp]:
  "P \<parallel>\<^bsub>false\<^esub> Q = false"
  by (rel_auto)

lemma par_by_merge_left_false [simp]:
  "false \<parallel>\<^bsub>M\<^esub> Q = false"
  by (rel_auto)

lemma par_by_merge_right_false [simp]:
  "P \<parallel>\<^bsub>M\<^esub> false = false"
  by (rel_auto)

text {* A nil parallel-by-merge yields a skip whenever the parallel predicates are both feasible. *}
    
lemma par_by_merge_nil:
  assumes "P ;; true = true" "Q ;; true = true"
  shows "P \<parallel>\<^bsub>nil\<^sub>m\<^esub> Q = II"
  using assms by (rel_auto)
    
lemma nil_swap: "swap\<^sub>m ;; nil\<^sub>m = nil\<^sub>m"
  by (rel_auto)
    
text {* Parallel-by-merge commutes when the merge predicate is unchanged by swap *}
    
lemma par_by_merge_commute:
  assumes "(swap\<^sub>m ;; M) = M"
  shows "P \<parallel>\<^bsub>M\<^esub> Q = Q \<parallel>\<^bsub>M\<^esub> P"
proof -
  have "P \<parallel>\<^bsub>M\<^esub> Q = (((P ;; U0) \<and> (Q ;; U1) \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) ;; M)"
    by (simp add: par_by_merge_def)
  also have "... = ((((P ;; U0) \<and> (Q ;; U1) \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) ;; swap\<^sub>m) ;; M)"
    by (metis assms seqr_assoc)
  also have "... = (((P ;; U0 ;; swap\<^sub>m) \<and> (Q ;; U1 ;; swap\<^sub>m) \<and> $\<Sigma>\<^sub><\<acute> =\<^sub>u $\<Sigma>) ;; M)"
    by (rel_auto)
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
  using assms by (rel_blast)

end