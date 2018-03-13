section {* Kleene Algebra and KAT Laws *}

theory utp_kleene
  imports
    "KAT_and_DRA.KAT"
    "../utp/utp"
begin

subsection \<open> Syntax setup \<close>

text \<open> It is necessary to replace parts of the KA/KAT syntax to ensure compatibility with UTP\<close>

purge_notation star ("_\<^sup>\<star>" [101] 100)

recall_syntax

purge_notation n_op ("n _" [90] 91)
purge_notation ts_ord (infix "\<sqsubseteq>" 50)

notation n_op ("\<^bold>n[_]")
notation t ("\<^bold>n\<^sup>2[_]")
notation ts_ord (infix "\<sqsubseteq>\<^sub>t" 50)

hide_const t

text \<open> Kleene Algebra Instantiations \<close>

text {* In this theory we import the laws of Kleene Algebra into UTP relational calculus. We show
  that relations form a dioid and Kleene algebra via two locales, the interpretation of which
  exports a large library of algebraic laws. *}

interpretation urel_dioid: dioid
  where plus = "op \<sqinter>" and times = "op ;;\<^sub>h" and less_eq = less_eq and less = less
proof
  fix P Q R :: "'\<alpha> hrel"
  show "(P \<sqinter> Q) ;; R = P ;; R \<sqinter> Q ;; R"
    by (simp add: upred_semiring.distrib_right)
  show "(Q \<sqsubseteq> P) = (P \<sqinter> Q = Q)"
    by (simp add: semilattice_sup_class.le_iff_sup)
  show "(P < Q) = (Q \<sqsubseteq> P \<and> \<not> P = Q)"
    by (simp add: less_le)
  show "P \<sqinter> P = P"
    by simp
qed

interpretation urel_ka: kleene_algebra
  where plus = "op \<sqinter>" and times = "op ;;\<^sub>h" and one = skip_r and zero = false\<^sub>h and less_eq = less_eq and less = less and star = ustar
proof
  fix P Q R :: "'\<alpha> hrel"
  show "II ;; P = P" by simp
  show "P ;; II = P" by simp
  show "false \<sqinter> P = P" by simp
  show "false ;; P = false" by simp
  show "P ;; false = false" by simp
  show "P\<^sup>\<star> \<sqsubseteq> II \<sqinter> P ;; P\<^sup>\<star>"
    using ustar_sub_unfoldl by blast
  show "Q \<sqsubseteq> R \<sqinter> P ;; Q \<Longrightarrow> Q \<sqsubseteq> P\<^sup>\<star> ;; R"
    by (simp add: ustar_inductl)
  show "Q \<sqsubseteq> R \<sqinter> Q ;; P \<Longrightarrow> Q \<sqsubseteq> R ;; P\<^sup>\<star>"
    by (simp add: ustar_inductr)
qed

interpretation urel_kat: kat
  where plus = "op \<sqinter>" and times = "op ;;\<^sub>h" and one = skip_r and zero = false\<^sub>h and less_eq = less_eq and less = less and star = ustar and n_op = "\<lambda>x. II \<and> (\<not> x)"
  by (unfold_locales, rel_auto+)

text {* We can now access the laws of KA and KAT for UTP relations as below. *}

thm urel_ka.star_inductr_var
thm urel_ka.star_trans
thm urel_ka.star_square
thm urel_ka.independence1

subsection \<open> Derived Laws \<close>

text \<open> We prove that UTP assumptions are tests \<close>

lemma test_rassume [simp]: "urel_kat.test [b]\<^sup>\<top>"
  by (simp add: urel_kat.test_def, rel_auto)

text \<open> The KAT laws can be used to prove results like the one below \<close>

lemma while_kat_form:
  "while b do P od = ([b]\<^sup>\<top> ;; P)\<^sup>\<star> ;; [\<not> b]\<^sup>\<top>" (is "?lhs = ?rhs")
proof -
  have 1:"(II::'a hrel) \<sqinter> (II::'a hrel) ;; [\<not> b]\<^sup>\<top> = II"
    by (metis assume_true test_rassume urel_kat.test_absorb1)
  have "?lhs = ([b]\<^sup>\<top> ;; P \<sqinter> [\<not> b]\<^sup>\<top> ;; II)\<^sup>\<star> ;; [\<not> b]\<^sup>\<top>"
    by (simp add: while_star_form rcond_rassume_expand)
  also have "... = (([b]\<^sup>\<top> ;; P)\<^sup>\<star> ;; [\<not> b]\<^sup>\<top>\<^sup>\<star>)\<^sup>\<star> ;; [\<not> b]\<^sup>\<top>"
    by (metis seqr_right_unit urel_ka.star_denest)
  also have "... = (([b]\<^sup>\<top> ;; P)\<^sup>\<star> ;; (II \<sqinter> [\<not> b]\<^sup>\<top>)\<^sup>\<star>)\<^sup>\<star> ;; [\<not> b]\<^sup>\<top>"
    by (metis urel_ka.star2)
  also have "... = (([b]\<^sup>\<top> ;; P)\<^sup>\<star> ;; (II)\<^sup>\<star>)\<^sup>\<star> ;; [\<not> b]\<^sup>\<top>"
    by (metis 1 seqr_left_unit)
  also have "... = (([b]\<^sup>\<top> ;; P)\<^sup>\<star>)\<^sup>\<star> ;; [\<not> b]\<^sup>\<top>"
    by (metis urel_ka.mult_oner urel_ka.star_one)
  also have "... = ?rhs"
    by (metis urel_ka.star_invol)
  finally show ?thesis .
qed

lemma uplus_invol [simp]: "(P\<^sup>+)\<^sup>+ = P\<^sup>+"
  by (metis RA1 uplus_def urel_ka.conway.dagger_trans_eq urel_ka.star_denest_var_2 urel_ka.star_invol)

lemma uplus_alt_def: "P\<^sup>+ = P\<^sup>\<star> ;; P"
  by (simp add: uplus_def urel_ka.star_slide_var)

subsection \<open> UTP Theories with Kleene Algebra \<close>

locale utp_theory_kleene = utp_theory_cont_unital_zerol
begin

lemma Star_def: "P\<^bold>\<star> = P\<^sup>\<star> ;; \<I>\<I>"
  by (simp add: utp_star_def)
  
lemma Star_alt_def:
  assumes "P is \<H>"
  shows "P\<^bold>\<star> = \<I>\<I> \<sqinter> P\<^sup>+"
proof -
  from assms have "P\<^sup>+ = P\<^sup>\<star> ;; P ;; \<I>\<I>"
    by (simp add: Unit_Right uplus_alt_def)
  then show ?thesis
    by (simp add: RA1 utp_star_def)
qed

lemma Star_Healthy [closure]:
  assumes "P is \<H>"
  shows "P\<^bold>\<star> is \<H>"
  by (simp add: assms closure Star_alt_def)

lemma Star_unfoldl:
  "P\<^bold>\<star> \<sqsubseteq> \<I>\<I> \<sqinter> P ;; P\<^bold>\<star>"
  by (simp add: RA1 utp_star_def)

lemma Star_inductl:
  assumes "R is \<H>" "Q \<sqsubseteq> P ;; Q \<sqinter> R"
  shows "Q \<sqsubseteq> P\<^bold>\<star>;;R"
proof -
  from assms(2) have "Q \<sqsubseteq> R" "Q \<sqsubseteq> P ;; Q"
    by auto
  thus ?thesis
    by (simp add: Unit_Left assms(1) upred_semiring.mult_assoc urel_ka.star_inductl utp_star_def)
qed

lemma Star_invol:
  assumes "P is \<H>"
  shows "P\<^bold>\<star>\<^bold>\<star> = P\<^bold>\<star>"
  by (metis (no_types) RA1 Unit_Left Unit_self assms urel_ka.star_invol urel_ka.star_sim3 utp_star_def)

lemma Star_test: 
  assumes "P is \<H>" "utest \<T> P"
  shows "P\<^bold>\<star> = \<I>\<I>"
  by (metis utp_star_def Star_alt_def Unit_Right Unit_self assms semilattice_sup_class.sup.absorb1 semilattice_sup_class.sup_left_idem urel_ka.star_inductr_var_eq2 urel_ka.star_sim1 utest_def)

lemma Star_lemma_1:
  "P is \<H> \<Longrightarrow> \<I>\<I> ;; P\<^sup>\<star> ;; \<I>\<I> = P\<^sup>\<star> ;; \<I>\<I>"
  by (metis utp_star_def Star_Healthy Unit_Left)
  
lemma Star_lemma_2:
  assumes "P is \<H>" "Q is \<H>"
  shows "(P\<^sup>\<star> ;; Q\<^sup>\<star> ;; \<I>\<I>)\<^sup>\<star> ;; \<I>\<I> = (P\<^sup>\<star> ;; Q\<^sup>\<star>)\<^sup>\<star> ;; \<I>\<I>"
  by (metis (no_types) assms RA1 Star_lemma_1 Unit_self urel_ka.star_sim3)

lemma Star_denest:
  assumes "P is \<H>" "Q is \<H>"
  shows "(P \<sqinter> Q)\<^bold>\<star> = (P\<^bold>\<star> ;; Q\<^bold>\<star>)\<^bold>\<star>"
  by (metis (no_types, lifting) RA1 utp_star_def Star_lemma_1 Star_lemma_2 assms urel_ka.star_denest)  

lemma Star_unfoldl_eq: 
  assumes "P is \<H>"
  shows "\<I>\<I> \<sqinter> P ;; P\<^bold>\<star> = P\<^bold>\<star>"
  by (simp add: RA1 utp_star_def)

lemma uplus_Star_def:
  assumes "P is \<H>"
  shows "P\<^sup>+ = (P ;; P\<^bold>\<star>)"
  by (metis (full_types) RA1 utp_star_def Unit_Left Unit_Right assms uplus_def urel_ka.conway.dagger_slide)

lemma Star_trade_skip:
  "P is \<H> \<Longrightarrow> \<I>\<I> ;; P\<^sup>\<star> = P\<^sup>\<star> ;; \<I>\<I>"
  by (simp add: Unit_Left Unit_Right urel_ka.star_sim3)

lemma Star_slide:
  assumes "P is \<H>"
  shows "(P ;; P\<^bold>\<star>) = (P\<^bold>\<star> ;; P)" (is "?lhs = ?rhs")
proof -
  have "?lhs = P ;; P\<^sup>\<star> ;; \<I>\<I>"
    by (simp add: utp_star_def)
  also have "... = P ;; \<I>\<I> ;; P\<^sup>\<star>"
    by (simp add: Star_trade_skip assms)
  also have "... = P ;; P\<^sup>\<star>"
    by (simp add: RA1 Unit_Right assms)
  also have "... = P\<^sup>\<star> ;; P"
    by (simp add: urel_ka.star_slide_var)
  also have "... = ?rhs"
    by (metis RA1 utp_star_def Unit_Left assms)
  finally show ?thesis .
qed

lemma Star_unfoldr_eq:
  assumes "P is \<H>"
  shows "\<I>\<I> \<sqinter> P\<^bold>\<star> ;; P = P\<^bold>\<star>"
  using Star_slide Star_unfoldl_eq assms by auto

lemma Star_inductr:
  assumes "P is \<H>" "R is \<H>" "Q \<sqsubseteq> P \<sqinter> Q ;; R"
  shows "Q \<sqsubseteq> P;;R\<^bold>\<star>"
  by (metis (full_types) RA1 Star_def Star_trade_skip Unit_Right assms urel_ka.star_inductr')

lemma Star_Top: "\<^bold>\<top>\<^bold>\<star> = \<I>\<I>"
  by (simp add: Star_test top_healthy utest_Top)

end

end