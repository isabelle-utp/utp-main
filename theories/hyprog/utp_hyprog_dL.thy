section \<open> Differential Dynamic Logic \<close>

theory utp_hyprog_dL
  imports utp_hyprog_ode
begin

subsection \<open> dL Rules \<close>

theorem dWeakening: \<comment> \<open> Differential Weakening \<close>
  "`B \<Rightarrow> C` \<Longrightarrow> \<^bold>[ode F' B\<^bold>]C = true"
  by (rel_simp, simp add: bop_ueval lit.rep_eq)

lemma hoare_meaning:
  "\<lbrace>P\<rbrace>S\<lbrace>Q\<rbrace>\<^sub>u = (\<forall> s s'. \<lbrakk>P\<rbrakk>\<^sub>e s \<and> \<lbrakk>S\<rbrakk>\<^sub>e (s, s') \<longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e s')"
  by (rel_auto)

lemma hoare_ode_meaning:
  "\<lbrace>P\<rbrace>ode F' B\<lbrace>Q\<rbrace>\<^sub>u = (\<forall> s F l. \<lbrakk>P\<rbrakk>\<^sub>e s \<and> l \<ge> 0 \<and> solves F F' B s l \<and> cvec\<^sub>v s = F 0 \<longrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F l\<rparr>))"
  by (rel_auto', metis (no_types) hybs.simps(1) hybs.simps(3) hybs.surjective)

lemma solves_le: 
  "\<lbrakk> solves F F' B s l; l' \<le> l \<rbrakk> \<Longrightarrow> solves F F' B s l'"
  by (meson atLeastatMost_subset_iff has_vector_derivative_within_subset order_refl order_trans)

theorem dCut:
  fixes B :: "('c::executable_euclidean_space, 's) hypred"
  assumes "\<lbrace>P\<rbrace>ode F' B\<lbrace>C\<rbrace>\<^sub>u" "\<lbrace>P\<rbrace>ode F' (B \<and> C)\<lbrace>Q\<rbrace>\<^sub>u"
  shows "\<lbrace>P\<rbrace>ode F' B\<lbrace>Q\<rbrace>\<^sub>u"
proof (simp add: hoare_ode_meaning, clarsimp)
  fix s :: "('c, 's) hybs_scheme" and F :: "real \<Rightarrow> 'c" and l :: "real"
  assume a: "0 \<le> l" "solves F F' B s l" "cvec\<^sub>v s = F 0" "\<lbrakk>P\<rbrakk>\<^sub>e s"
  have "\<forall> t\<in>{0..l}. \<lbrakk>C\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>)"
  proof (clarsimp)
    fix t
    assume b: "0 \<le> t" "t \<le> l"
    from a(1,3,4) b assms(1) show "\<lbrakk>C\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F t\<rparr>)"
      apply (simp add: hoare_ode_meaning)
      apply (drule_tac x="s" in spec)
      apply (drule_tac x="F" in spec)
      apply (drule_tac x="t" in spec)
      apply (simp)
      apply (metis a(2) atLeastatMost_subset_iff has_vector_derivative_within_subset order_refl order_trans)
      done
  qed
  with a(1,2,3,4) assms(2) show "\<lbrakk>Q\<rbrakk>\<^sub>e (s\<lparr>cvec\<^sub>v := F l\<rparr>)"
    apply (simp add: hoare_ode_meaning)
    apply (drule_tac x="s" in spec)
    apply (drule_tac x="F" in spec)
    apply (drule_tac x="l" in spec)
    apply (rel_auto')
    using a(2) apply auto
    done
qed

end