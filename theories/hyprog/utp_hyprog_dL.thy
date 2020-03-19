section \<open> Differential Dynamic Logic \<close>

theory utp_hyprog_dL
  imports utp_hyprog_ode
begin

subsection \<open> dL Rules \<close>

theorem dWeakening: \<comment> \<open> Differential Weakening \<close>
  "`B \<Rightarrow> C` \<Longrightarrow> \<^bold>[ode F' B\<^bold>]C = true"
  by (rel_simp, simp add: lit.rep_eq uexpr_appl.rep_eq)

lemma hoare_ode_meaning:
  "\<lbrace>P\<rbrace>ode F' B\<lbrace>Q\<rbrace>\<^sub>u = (\<forall> s F l. \<lbrakk>P\<rbrakk>\<^sub>e \<lparr> cvec\<^sub>v = F 0, \<dots> = s \<rparr> \<and> l \<ge> 0 \<and> solves F \<lbrakk>F'\<rbrakk>\<^sub>e B s l \<longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F l, \<dots> = s\<rparr>))"
  by (rel_auto', blast)

theorem dCut:
  fixes B :: "('c::executable_euclidean_space, 's) hypred"
  assumes "\<lbrace>P\<rbrace>ode F' B\<lbrace>C\<rbrace>\<^sub>u" "\<lbrace>P\<rbrace>ode F' (B \<and> C)\<lbrace>Q\<rbrace>\<^sub>u"
  shows "\<lbrace>P\<rbrace>ode F' B\<lbrace>Q\<rbrace>\<^sub>u"
proof (simp add: hoare_ode_meaning, clarsimp)
  fix s :: "'s" and F :: "real \<Rightarrow> 'c" and l :: "real"
  assume a: "0 \<le> l" "solves F \<lbrakk>F'\<rbrakk>\<^sub>e B s l" "\<lbrakk>P\<rbrakk>\<^sub>e \<lparr> cvec\<^sub>v = F 0, \<dots> = s \<rparr>"
  have "\<forall> t\<in>{0..l}. \<lbrakk>C\<rbrakk>\<^sub>e \<lparr>cvec\<^sub>v = F t, \<dots> = s\<rparr>"
  proof (clarsimp)
    fix t
    assume b: "0 \<le> t" "t \<le> l"
    from a(1,2) b assms(1) show "\<lbrakk>C\<rbrakk>\<^sub>e (\<lparr>cvec\<^sub>v = F t, \<dots> = s\<rparr>)"
      apply (simp add: hoare_ode_meaning)
      apply (drule_tac x="s" in spec)
      apply (drule_tac x="F" in spec)
      apply (drule_tac x="t" in spec)
      apply (simp)
      using a(2) a(3) has_vector_derivative_within_subset apply fastforce
      done
  qed
  with a(1,2,3) assms(2) show "\<lbrakk>Q\<rbrakk>\<^sub>e \<lparr>cvec\<^sub>v = F l, \<dots> = s\<rparr>"
    apply (simp add: hoare_ode_meaning)
    apply (drule_tac x="s" in spec)
    apply (drule_tac x="F" in spec)
    apply (drule_tac x="l" in spec)
    apply (rel_auto')
    using a(2) apply auto
    done
qed

end