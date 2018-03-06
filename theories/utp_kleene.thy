section {* Kleene Algebra and KAT Laws *}

theory utp_kleene
  imports
    "KAT_and_DRA.KAT"
    "../utp/utp"
begin

text \<open> It is necessary to replace parts of the KA/KAT syntax to ensure compatibility with UTP\<close>

purge_notation star ("_\<^sup>\<star>" [101] 100)

recall_syntax

purge_notation n_op ("n _" [90] 91)
purge_notation ts_ord (infix "\<sqsubseteq>" 50)

notation n_op ("\<^bold>n[_]")
notation t ("\<^bold>n\<^sup>2[_]")
notation ts_ord (infix "\<sqsubseteq>\<^sub>t" 50)

hide_const t

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

end