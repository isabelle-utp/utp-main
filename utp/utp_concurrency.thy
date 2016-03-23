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

text {* We describe the partition of a state space into a n pieces through the use of a list. *}

type_synonym '\<alpha> partition = "'\<alpha> list"

text {* A merge relation is a design that describes how a partitioned state-space should be
        merged into a third state-space. For now the state-spaces for two merged processes
        should have the same type. This could potentially be generalised, but that might
        have an effect on our reasoning capabilities. *}

(*
definition ind_uvar_0 :: "('a, '\<alpha> alphabet_d) uvar \<Rightarrow> ('a, ('\<alpha> \<times> '\<alpha> partition) alphabet_d) uvar" where
"ind_uvar_0 x = 
  \<lparr> var_lookup = var_lookup x \<circ> (\<lambda> A. \<lparr> des_ok = des_ok A, \<dots> = fst (snd (more A)) \<rparr>)
  , var_update = (\<lambda> f A. let A' = var_update x f \<lparr> des_ok = des_ok A, \<dots> = fst (snd (more A)) \<rparr>
                          in \<lparr> des_ok = des_ok A, \<dots> = (fst (more A), (more A', snd (snd (more A)))) \<rparr>) \<rparr>"

definition ind_uvar_1 :: "('a, '\<alpha> alphabet_d) uvar \<Rightarrow> ('a, ('\<alpha> \<times> '\<alpha> partition) alphabet_d) uvar" where
"ind_uvar_1 x = 
  \<lparr> var_lookup = var_lookup x \<circ> (\<lambda> A. \<lparr> des_ok = des_ok A, \<dots> = snd (snd (more A)) \<rparr>)
  , var_update = (\<lambda> f A. let A' = var_update x f \<lparr> des_ok = des_ok A, \<dots> = snd (snd (more A)) \<rparr>
                          in \<lparr> des_ok = des_ok A, \<dots> = (fst (more A), (fst (snd (more A)), more A')) \<rparr>) \<rparr>"
*)

text {* Extract the ith element of the second part *}

definition "ind_uvar i x = x ;\<^sub>l list_lens i ;\<^sub>l snd\<^sub>l ;\<^sub>l des_lens"

definition "pre_uvar x = x ;\<^sub>l fst\<^sub>l ;\<^sub>l des_lens"

definition "in_ind_uvar i x = in_var (ind_uvar i x)"

definition "out_ind_uvar i x = out_var (ind_uvar i x)"

definition "in_ind_uexpr i x = var (in_ind_uvar i x)"

definition "out_ind_uexpr i x = var (out_ind_uvar i x)"

declare in_ind_uvar_def [upred_defs]
declare out_ind_uvar_def [upred_defs]

declare in_ind_uexpr_def [upred_defs]
declare out_ind_uexpr_def [upred_defs]

thm lens_comp_assoc[THEN sym]

lemma ind_uvar_indep:
  "\<lbrakk>mwb_lens x; i \<noteq> j\<rbrakk> \<Longrightarrow> ind_uvar i x \<bowtie> ind_uvar j x"
  apply (simp add: ind_uvar_def lens_comp_assoc[THEN sym])
  apply (metis lens_indep_left_comp lens_indep_right_comp list_lens_indep out_var_def out_var_indep uvar_des_lens vwb_lens_mwb)
done

lemma ind_uvar_semi_uvar:
  "semi_uvar x \<Longrightarrow> semi_uvar (ind_uvar i x)"
  apply (unfold_locales)
  apply (simp_all add:ind_uvar_def)
oops

syntax
  "_uprevar"  :: "('t, '\<alpha>) uvar \<Rightarrow> logic" ("$\<^sub><_" [999] 999)
  "_upostvar"  :: "('t, '\<alpha>) uvar \<Rightarrow> logic" ("$\<^sub>>_" [999] 999)
  "_udotvar"  :: "nat \<Rightarrow> ('t, '\<alpha>) uvar \<Rightarrow> logic" ("&_._" [0,999] 999)
  "_uidotvar" :: "nat \<Rightarrow> ('t, '\<alpha>) uvar \<Rightarrow> logic" ("$_._" [0,999] 999)
  "_uodotvar" :: "nat \<Rightarrow> ('t, '\<alpha>) uvar \<Rightarrow> logic" ("$_._\<acute>" [999] 999)
  "_sdotvar"     :: "nat \<Rightarrow> logic \<Rightarrow> svar" ("&_._" [0,999] 999)
  "_sin_dotvar"  :: "nat \<Rightarrow> logic \<Rightarrow> svar" ("$_._")
  "_sout_dotvar" :: "nat \<Rightarrow> logic \<Rightarrow> svar" ("$_._\<acute>")

translations
  "_uprevar x" == "CONST var (CONST in_var (CONST pre_uvar x))"
  "_upostvar x" == "CONST var (CONST out_var (CONST pre_uvar x))"
  "_udotvar n x" == "CONST var (CONST ind_uvar n x)"
  "_uidotvar n x" == "CONST in_ind_uexpr n x"
  "_uodotvar n x" == "CONST out_ind_uexpr n x"
  "_sdotvar n x" == "CONST ind_uvar n x"
  "_sin_dotvar n x" == "CONST in_var (CONST ind_uvar n x)"
  "_sout_dotvar n x" == "CONST out_var (CONST ind_uvar n x)"
  "_psubst m (_sdotvar n x) v" => "CONST subst_upd m (CONST ind_uvar n x) v"

type_synonym '\<alpha> merge = "('\<alpha> alphabet_d \<times> '\<alpha> alphabet_d partition, '\<alpha>) relation_d"

text {* Separating simulations. I assume that the value of ok' should track the value
  of n.ok'. *}

definition sep_sim :: "_ \<Rightarrow> _" ("U'(_')")
where "U(n) = (($(n).\<Sigma>\<acute> =\<^sub>u $\<Sigma>) \<and> ($ok\<acute> =\<^sub>u $ok))"

declare sep_sim_def [upred_defs]

lemma var_lookup_univ_alpha [simp]:
  "var_lookup \<Sigma> = id"
  by (simp add: univ_alpha_def id_lens_def)

text {* The following implementation of parallel by merge is less general than the book version, in
  that it does not properly partition the alphabet into two disjoint segments. We could actually
  achieve this specifying lenses into the larger alphabet, but this would complicate the definition
  of programs. May reconsider later. *}

definition par_by_merge :: 
  "'\<alpha> hrelation_d \<Rightarrow> '\<alpha> merge \<Rightarrow> '\<alpha> hrelation_d \<Rightarrow> '\<alpha> hrelation_d" (infixr "\<parallel>\<^bsub>_\<^esub>" 85) 
where "P \<parallel>\<^bsub>M\<^esub> Q = ((((P ;; U(0)) \<parallel> (Q ;; U(1))) \<and> $\<^sub>>\<Sigma> =\<^sub>u $\<Sigma>) ;; M)"

definition "swap\<^sub>m = (($0.\<Sigma>\<acute> =\<^sub>u $1.\<Sigma>) \<and> ($1.\<Sigma>\<acute> =\<^sub>u $0.\<Sigma>) \<and> ($\<^sub><\<Sigma> =\<^sub>u $\<^sub>>\<Sigma>))"

declare swap\<^sub>m_def [upred_defs]

end