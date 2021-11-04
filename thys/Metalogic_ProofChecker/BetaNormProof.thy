
text\<open>Facts about beta normalization involving theories\<close>

theory BetaNormProof
  imports BetaNorm Theory
begin

lemma beta_preserves_term_ok': "term_ok' \<Sigma> r \<Longrightarrow> r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> term_ok' \<Sigma> s"
proof (induction r arbitrary: s)
  case (Ct n T)
  then show ?case 
    apply (simp add: tinstT_def split: option.splits)
    (* Seems like I miss a simp rule for Ct*)
    using beta_reducible.simps(7) beta_step_imp_beta_reducible by blast
next
  case (Fv n T)
  then show ?case 
    by auto
next
  case (Bv n)
  then show ?case 
    by auto
next
  case (Abs R r)
  then show ?case 
    by auto
next
  case (App f u)
  then show ?case 
    apply -
    apply (ind_cases "f $ u \<rightarrow>\<^sub>\<beta> s" for f u s)
    using term_ok'_subst_bv2 term_ok'.simps(4) term_ok'.simps(5) apply blast
    using term_ok'.simps(4) apply blast
    using term_ok'.simps(4) apply blast
    done
qed

lemma beta_preserves_term_ok: "term_ok \<Theta> r \<Longrightarrow> r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> term_ok \<Theta> s"
proof -
  assume a1: "term_ok \<Theta> r"
  assume a2: "r \<rightarrow>\<^sub>\<beta> s"
  then have "None \<noteq> typ_of1 [] s"
    using a1 beta_preserves_typ_of1
    by (metis has_typ1_imp_typ_of1 has_typ_def option.distinct(1) term_ok_def wt_term_def)
  then show ?thesis
    using a2 a1 beta_preserves_term_ok' has_typ_iff_typ_of wt_term_def typ_of_def
    by (meson beta_preserves_typ_of term_ok_def wf_term_iff_term_ok')
qed

lemma beta_star_preserves_term_ok': "r \<rightarrow>\<^sub>\<beta>\<^sup>* s \<Longrightarrow> term_ok' \<Sigma> r  \<Longrightarrow> term_ok' \<Sigma> s"
  by (induction rule: rtranclp.induct) (auto simp add: beta_preserves_term_ok')

corollary beta_star_preserves_term_ok: "r \<rightarrow>\<^sub>\<beta>\<^sup>* s \<Longrightarrow> term_ok thy r  \<Longrightarrow> term_ok thy s"
  using beta_star_preserves_term_ok' beta_star_preserves_typ_of1 wt_term_def typ_of_def by auto
                     
corollary term_ok_beta_norm: "term_ok thy t \<Longrightarrow> beta_norm t = Some t'\<Longrightarrow> term_ok thy t'"
  using beta_norm_imp_beta_reds beta_star_preserves_term_ok by blast

end
