section {* Fixed-points and Recursion *}

theory utp_recursion
  imports utp_pred_laws
begin

subsection {* Fixed-point Laws *}
  
lemma mu_id: "(\<mu> X \<bullet> X) = true"
  by (simp add: antisym gfp_upperbound)

lemma mu_const: "(\<mu> X \<bullet> P) = P"
  by (simp add: gfp_const)

lemma nu_id: "(\<nu> X \<bullet> X) = false"
  by (meson lfp_lowerbound utp_pred_laws.bot.extremum_unique)

lemma nu_const: "(\<nu> X \<bullet> P) = P"
  by (simp add: lfp_const)

lemma mu_refine_intro:
  assumes "(C \<Rightarrow> S) \<sqsubseteq> F(C \<Rightarrow> S)" "`C \<Rightarrow> (\<mu> F \<Leftrightarrow> \<nu> F)`"
  shows "(C \<Rightarrow> S) \<sqsubseteq> \<mu> F"
proof -
  from assms have "(C \<Rightarrow> S) \<sqsubseteq> \<nu> F"
    by (simp add: lfp_lowerbound)
  with assms show ?thesis
    by (pred_auto)
qed

subsection {* Obtaining Unique Fixed-points *}
    
text {* Obtaining termination proofs via approximation chains. Theorems and proofs adapted
  from Chapter 2, page 63 of the UTP book~\cite{Hoare&98}.  *}

type_synonym 'a chain = "nat \<Rightarrow> 'a upred"

definition chain :: "'a chain \<Rightarrow> bool" where
  "chain Y = ((Y 0 = false) \<and> (\<forall> i. Y (Suc i) \<sqsubseteq> Y i))"

lemma chain0 [simp]: "chain Y \<Longrightarrow> Y 0 = false"
  by (simp add:chain_def)

lemma chainI:
  assumes "Y 0 = false" "\<And> i. Y (Suc i) \<sqsubseteq> Y i"
  shows "chain Y"
  using assms by (auto simp add: chain_def)

lemma chainE:
  assumes "chain Y" "\<And> i. \<lbrakk> Y 0 = false; Y (Suc i) \<sqsubseteq> Y i \<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms by (simp add: chain_def)

lemma L274:
  assumes "\<forall> n. ((E n \<and>\<^sub>p X) = (E n \<and> Y))"
  shows "(\<Sqinter> (range E) \<and> X) = (\<Sqinter> (range E) \<and> Y)"
  using assms by (pred_auto)

text {* Constructive chains *}

definition constr ::
  "('a upred \<Rightarrow> 'a upred) \<Rightarrow> 'a chain \<Rightarrow> bool" where
"constr F E \<longleftrightarrow> chain E \<and> (\<forall> X n. ((F(X) \<and> E(n + 1)) = (F(X \<and> E(n)) \<and> E (n + 1))))"

text {* This lemma gives a way of showing that there is a unique fixed-point when
        the predicate function can be built using a constructive function F
        over an approximation chain E *}

lemma chain_pred_terminates:
  assumes "constr F E" "mono F"
  shows "(\<Sqinter> (range E) \<and> \<mu> F) = (\<Sqinter> (range E) \<and> \<nu> F)"
proof -
  from assms have "\<forall> n. (E n \<and> \<mu> F) = (E n \<and> \<nu> F)"
  proof (rule_tac allI)
    fix n
    from assms show "(E n \<and> \<mu> F) = (E n \<and> \<nu> F)"
    proof (induct n)
      case 0 thus ?case by (simp add: constr_def)
    next
      case (Suc n)
      note hyp = this
      thus ?case
      proof -
        have "(E (n + 1) \<and> \<mu> F) = (E (n + 1) \<and> F (\<mu> F))"
          using gfp_unfold[OF hyp(3), THEN sym] by (simp add: constr_def)
        also from hyp have "... = (E (n + 1) \<and> F (E n \<and> \<mu> F))"
          by (metis conj_comm constr_def)
        also from hyp have "... = (E (n + 1) \<and> F (E n \<and> \<nu> F))"
          by simp
        also from hyp have "... = (E (n + 1) \<and> \<nu> F)"
          by (metis (no_types, lifting) conj_comm constr_def lfp_unfold)
        ultimately show ?thesis
          by simp
      qed
    qed
  qed
  thus ?thesis
    by (auto intro: L274)
qed

theorem constr_fp_uniq:
  assumes "constr F E" "mono F" "\<Sqinter> (range E) = C"
  shows "(C \<and> \<mu> F) = (C \<and> \<nu> F)"
  using assms(1) assms(2) assms(3) chain_pred_terminates by blast

end