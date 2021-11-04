
text\<open>Facts about eta normalization involving theories\<close>

theory EtaNormProof
  imports EtaNorm Theory
  (* This means I need to restructure *)
  BetaNormProof
begin

lemma term_ok'_decr: "term_ok' \<Sigma> t \<Longrightarrow> term_ok' \<Sigma> (decr i t)"
  by (induction i t rule: decr.induct) auto

lemma eta_preserves_term_ok': "term_ok' \<Sigma> r \<Longrightarrow> r \<rightarrow>\<^sub>\<eta> s \<Longrightarrow> term_ok' \<Sigma> s"
proof (induction r arbitrary: s)
  case (Ct n T)
  then show ?case 
    apply (simp add: tinstT_def split: option.splits)
    (* Seems like I miss a simp rule for Ct*)
    using eta_reducible.simps(12) eta_step_imp_eta_reducible by blast
next
  case (Fv n T)
  then show ?case
    using eta.cases 
    by blast
next
  case (Bv n)
  then show ?case 
    by auto
next
  case (Abs R r)
  then show ?case 
    using eta.cases 
    by (fastforce simp add: term_ok'_decr)
next
  case (App f u)
  then show ?case 
    apply - 
    apply (erule eta_cases(2)) 
    using term_ok'.simps(4) by blast+
qed

lemma eta_preserves_term_ok: "term_ok \<Theta> r \<Longrightarrow> r \<rightarrow>\<^sub>\<eta> s \<Longrightarrow> term_ok \<Theta> s"
proof -
  assume a1: "term_ok \<Theta> r"
  assume a2: "r \<rightarrow>\<^sub>\<eta> s"
  then have "None \<noteq> typ_of1 [] s"
    using a1 eta_preserves_typ_of1 option.collapse wt_term_def typ_of_def 
    by auto
  then show ?thesis
    using a2 a1 eta_preserves_term_ok' wt_term_def typ_of_def wf_term_iff_term_ok' term_ok_def
    by (meson eta_preserves_typ_of has_typ_iff_typ_of)
qed

lemma eta_star_preserves_term_ok': "r \<rightarrow>\<^sub>\<eta>\<^sup>* s \<Longrightarrow> term_ok' \<Sigma> r  \<Longrightarrow> term_ok' \<Sigma> s"
  by (induction rule: rtranclp.induct) (auto simp add: eta_preserves_term_ok')

corollary eta_star_preserves_term_ok: "r \<rightarrow>\<^sub>\<eta>\<^sup>* s \<Longrightarrow> term_ok thy r  \<Longrightarrow> term_ok thy s"
  using eta_star_preserves_term_ok' eta_star_preserves_typ_of1 wt_term_def typ_of_def by auto
                     
corollary term_ok_eta_norm: "term_ok thy t \<Longrightarrow> eta_norm t = t'\<Longrightarrow> term_ok thy t'"
  using eta_norm_imp_eta_reds eta_star_preserves_term_ok by blast

end