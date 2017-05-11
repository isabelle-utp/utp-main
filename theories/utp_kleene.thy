section {* Kleene Algebra Laws *}

theory utp_kleene
  imports 
    "../contrib/Kleene_Algebra/Kleene_Algebra"
    "../utp/utp"
begin 

text {* In this theory we import the laws of Kleene Algebra into UTP relational calculus. We show
  that relations form a dioid and Kleene algebra via two locales, the interpretation of which
  exports a large library of algebraic laws. *}
  
no_notation star ("_\<^sup>\<star>" [101] 100)
recall_syntax
  
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
    using ustar_unfoldl by blast
  show "Q \<sqsubseteq> R \<sqinter> P ;; Q \<Longrightarrow> Q \<sqsubseteq> P\<^sup>\<star> ;; R"
    by (simp add: ustar_inductl)
  show "Q \<sqsubseteq> R \<sqinter> Q ;; P \<Longrightarrow> Q \<sqsubseteq> R ;; P\<^sup>\<star>"
    by (simp add: ustar_inductr)
qed
      
text {* We can now access the laws of KA for UTP relations as below. *}
  
thm urel_ka.star_trans
thm urel_ka.star_square
thm urel_ka.independence1
  
end