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

type_synonym 'a partition = "'a list"

text {* A merge relation is a design that describes how a partitioned state-space should be
        merged into a third state-space. For now the state-spaces for two merged processes
        should have the same type. This could potentially be generalised, but that might
        have an effect on our reasoning capabilities. *}

definition ind_uvar :: "nat \<Rightarrow> ('a, '\<alpha> alphabet_d) uvar \<Rightarrow> ('a, ('\<alpha> \<times> '\<alpha> partition) alphabet_d) uvar" where
"ind_uvar i x = \<lparr> var_lookup = var_lookup x \<circ> (\<lambda> A. \<lparr> des_ok = des_ok A, \<dots> = snd (more A) ! i \<rparr>)
                , var_update = undefined
                     \<rparr>"

definition pre_uvar :: "('a, '\<alpha> alphabet_d) uvar \<Rightarrow> ('a, ('\<alpha> \<times> '\<alpha> partition) alphabet_d) uvar" where
"pre_uvar x = \<lparr> var_lookup = var_lookup x \<circ> (\<lambda> A. \<lparr> des_ok = des_ok A, \<dots> = fst (more A) \<rparr>)
              , var_update = undefined \<rparr>"

(*
(\<lambda> f A. let A' = var_update x f \<lparr> des_ok = des_ok A, \<dots> = more A ! i \<rparr>
                            in \<lparr> des_ok = des_ok A, \<dots> = more A[i := more A'] \<rparr>)
*)

lemma ind_uvar_semi_uvar:
  "semi_uvar x \<Longrightarrow> semi_uvar (ind_uvar i x)"
  apply (unfold_locales)
  apply (simp_all add:ind_uvar_def)
oops

syntax
  "_uprevar"  :: "('t, '\<alpha>) uvar \<Rightarrow> logic" ("$\<^sub><_" [999] 999)
  "_udotvar"  :: "nat \<Rightarrow> ('t, '\<alpha>) uvar \<Rightarrow> logic" ("&_._" [0,999] 999)
  "_uidotvar" :: "nat \<Rightarrow> ('t, '\<alpha>) uvar \<Rightarrow> logic" ("$_._" [0,999] 999)
  "_uodotvar" :: "nat \<Rightarrow> ('t, '\<alpha>) uvar \<Rightarrow> logic" ("$_._\<acute>" [999] 999)
  "_sdotvar"     :: "nat \<Rightarrow> id \<Rightarrow> svar" ("&_._" [0,999] 999)
  "_sin_dotvar"  :: "nat \<Rightarrow> id \<Rightarrow> svar" ("$_._")
  "_sout_dotvar" :: "nat \<Rightarrow> id \<Rightarrow> svar" ("$_._\<acute>")

translations
  "_uprevar x" == "CONST var (CONST in_var (CONST pre_uvar x))"
  "_udotvar n x" == "CONST var (CONST ind_uvar n x)"
  "_uidotvar n x" == "CONST var (CONST in_var (CONST ind_uvar n x))"
  "_uidotvar n x" == "CONST var (CONST out_var (CONST ind_uvar n x))"
  "_sdotvar n x" == "CONST ind_uvar n x"
  "_sin_dotvar n x" == "CONST in_var (CONST ind_uvar n x)"
  "_sout_dotvar n x" == "CONST out_var (CONST ind_uvar n x)"
  "_psubst m (_sdotvar n x) v" => "CONST subst_upd m (CONST ind_uvar n x) v"

type_synonym '\<alpha> merge = "('\<alpha> \<times> '\<alpha> partition, '\<alpha>) relation_d"

text {* Separating simulations *}

lift_definition sep_sim :: "nat \<Rightarrow> ('\<alpha>, '\<alpha> partition) relation_d" ("U'(_')") is
"\<lambda> n (A, A'). des_ok A' = des_ok A \<and> length (alpha_d.more A') > n \<and> alpha_d.more A' ! n = alpha_d.more A" .

lift_definition alpha_ext :: "('\<alpha>, '\<beta>) relation_d \<Rightarrow> ('\<alpha>, '\<alpha> \<times> '\<beta>) relation_d" ("_\<^sub>+" [999] 999) is
"\<lambda> P (A, A'). P (A, \<lparr> des_ok = des_ok A', \<dots> = snd (more A')\<rparr>) \<and> des_ok A' = des_ok A \<and> fst (more A') = more A" .

text {* Parallel by merge *}

definition design_par_by_merge :: 
  "'\<alpha> hrelation_d \<Rightarrow> '\<alpha> merge \<Rightarrow> '\<alpha> hrelation_d \<Rightarrow> '\<alpha> hrelation_d" (infixr "\<parallel>\<^bsub>_\<^esub>" 85) 
where "P \<parallel>\<^bsub>M\<^esub> Q = (((P ;; U(0)) \<parallel> (Q ;; U(1)))\<^sub>+ ;; M)"

end