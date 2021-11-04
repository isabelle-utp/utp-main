subsection \<open>Local versions of relations\<close>

theory Relations
  imports
    "HOL-Library.Multiset"
    "Abstract-Rewriting.Abstract_Rewriting"
begin

text\<open>Common predicates on relations\<close>

definition compatible_l :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "compatible_l R1 R2 \<equiv> R1 O R2 \<subseteq> R2"

definition compatible_r :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "compatible_r R1 R2 \<equiv> R2 O R1 \<subseteq> R2"

text\<open>Local reflexivity\<close>

definition locally_refl :: "'a rel \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "locally_refl R A \<equiv> (\<forall> a. a \<in># A \<longrightarrow> (a,a) \<in> R)"

definition locally_irrefl :: "'a rel \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "locally_irrefl R A \<equiv> (\<forall>t. t \<in># A \<longrightarrow> (t,t) \<notin> R)"

text\<open>Local symmetry\<close>

definition locally_sym :: "'a rel \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "locally_sym R A \<equiv> (\<forall>t u. t \<in># A \<longrightarrow> u \<in># A \<longrightarrow>
               (t,u) \<in> R \<longrightarrow> (u,t) \<in> R)"

definition locally_antisym :: "'a rel \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "locally_antisym R A \<equiv> (\<forall>t u. t \<in># A \<longrightarrow> u \<in># A \<longrightarrow>
               (t,u) \<in> R \<longrightarrow> (u,t) \<in> R \<longrightarrow> t = u)"

text\<open>Local transitivity\<close>

definition locally_trans :: "'a rel \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "locally_trans R A B C \<equiv> (\<forall>t u v.
               t \<in># A \<longrightarrow> u \<in># B \<longrightarrow> v \<in># C \<longrightarrow>
               (t,u) \<in> R \<longrightarrow> (u,v) \<in> R \<longrightarrow> (t,v) \<in> R)"

text\<open>Local inclusion\<close>

definition locally_included :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "locally_included R1 R2 A B \<equiv> (\<forall>t u. t \<in># A \<longrightarrow> u \<in># B \<longrightarrow>
               (t,u) \<in> R1 \<longrightarrow>  (t,u) \<in> R2)"

text\<open>Local transitivity compatibility\<close>

definition locally_compatible_l :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "locally_compatible_l R1 R2 A B C \<equiv> (\<forall>t u v. t \<in># A \<longrightarrow> u \<in># B \<longrightarrow> v \<in># C \<longrightarrow>
               (t,u) \<in> R1 \<longrightarrow> (u,v) \<in> R2 \<longrightarrow> (t,v) \<in> R2)"

definition locally_compatible_r :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "locally_compatible_r R1 R2 A B C \<equiv> (\<forall>t u v. t \<in># A \<longrightarrow> u \<in># B \<longrightarrow> v \<in># C \<longrightarrow>
               (t,u) \<in> R2 \<longrightarrow> (u,v) \<in> R1 \<longrightarrow> (t,v) \<in> R2)" 

text\<open>included + compatible $\longrightarrow$  transitive\<close>

lemma in_cl_tr:
  assumes "R1 \<subseteq> R2"
    and "compatible_l R2 R1"
  shows "trans R1"
proof-
  {
    fix x y z
    assume s_x_y: "(x,y) \<in> R1" and s_y_z: "(y,z) \<in> R1"
    from assms s_x_y have "(x,y) \<in> R2" by auto
    with s_y_z assms(2)[unfolded compatible_l_def]  have "(x,z) \<in> R1" by blast
  }
  then show ?thesis unfolding trans_def by fast
qed

lemma in_cr_tr:
  assumes "R1 \<subseteq> R2"
    and "compatible_r R2 R1"
  shows "trans R1"
proof-
  {
    fix x y z
    assume s_x_y: "(x,y) \<in> R1" and s_y_z: "(y,z) \<in> R1"
    with assms have "(y,z) \<in> R2" by auto
    with s_x_y assms(2)[unfolded compatible_r_def] have "(x,z) \<in> R1" by blast
  }
  then show ?thesis unfolding trans_def by fast
qed

text\<open>If a property holds globally, it also holds locally. Obviously.\<close>

lemma r_lr:
  assumes "refl R"
  shows "locally_refl R A"
  using assms unfolding refl_on_def locally_refl_def by blast

lemma tr_ltr:
  assumes "trans R"
  shows "locally_trans R A B C"
  using assms unfolding trans_def and locally_trans_def by fast

lemma in_lin:
  assumes "R1 \<subseteq> R2"
  shows "locally_included R1 R2 A B"
  using assms unfolding locally_included_def by auto

lemma cl_lcl:
  assumes "compatible_l R1 R2"
  shows "locally_compatible_l R1 R2 A B C"
  using assms unfolding compatible_l_def and locally_compatible_l_def by auto

lemma cr_lcr:
  assumes "compatible_r R1 R2"
  shows "locally_compatible_r R1 R2 A B C"
  using assms unfolding compatible_r_def and locally_compatible_r_def by auto

text\<open>If a predicate holds on a set then it holds on
  all the subsets:\<close>

lemma lr_trans_l:
  assumes "locally_refl R (A + B)"
  shows "locally_refl R A"
  using assms unfolding locally_refl_def
  by auto

lemma li_trans_l:
  assumes "locally_irrefl R (A + B)"
  shows "locally_irrefl R A"
  using assms unfolding locally_irrefl_def
  by auto

lemma ls_trans_l:
  assumes "locally_sym R (A + B)"
  shows "locally_sym R A"
  using assms unfolding locally_sym_def
  by auto

lemma las_trans_l:
  assumes "locally_antisym R (A + B)"
  shows "locally_antisym R A"
  using assms unfolding locally_antisym_def
  by auto

lemma lt_trans_l:
  assumes "locally_trans R (A + B) (C + D) (E + F)"
  shows "locally_trans R A C E"
  using assms[unfolded locally_trans_def, rule_format]
  unfolding locally_trans_def by auto

lemma lin_trans_l: 
  assumes "locally_included R1 R2 (A + B) (C + D)"
  shows "locally_included R1 R2 A C"
  using assms unfolding locally_included_def by auto

lemma lcl_trans_l: 
  assumes "locally_compatible_l R1 R2 (A + B) (C + D) (E + F)"
  shows "locally_compatible_l R1 R2 A C E"
  using assms[unfolded locally_compatible_l_def, rule_format]
  unfolding locally_compatible_l_def by auto

lemma lcr_trans_l: 
  assumes "locally_compatible_r R1 R2 (A + B) (C + D) (E + F)"
  shows "locally_compatible_r R1 R2 A C E"
  using assms[unfolded locally_compatible_r_def, rule_format]
  unfolding locally_compatible_r_def by auto

lemma lr_trans_r:
  assumes "locally_refl R (A + B)"
  shows "locally_refl R B"
  using assms unfolding locally_refl_def
  by auto

lemma li_trans_r:
  assumes "locally_irrefl R (A + B)"
  shows "locally_irrefl R B"
  using assms unfolding locally_irrefl_def
  by auto

lemma ls_trans_r:
  assumes "locally_sym R (A + B)"
  shows "locally_sym R B"
  using assms unfolding locally_sym_def
  by auto

lemma las_trans_r:
  assumes "locally_antisym R (A + B)"
  shows "locally_antisym R B"
  using assms unfolding locally_antisym_def
  by auto

lemma lt_trans_r:
  assumes "locally_trans R (A + B) (C + D) (E + F)"
  shows "locally_trans R B D F"
  using assms[unfolded locally_trans_def, rule_format]
  unfolding locally_trans_def
  by auto

lemma lin_trans_r: 
  assumes "locally_included R1 R2 (A + B) (C + D)"
  shows "locally_included R1 R2 B D"
  using assms unfolding locally_included_def by auto

lemma lcl_trans_r:
  assumes "locally_compatible_l R1 R2 (A + B) (C + D) (E + F)"
  shows "locally_compatible_l R1 R2 B D F"
  using assms[unfolded locally_compatible_l_def, rule_format]
  unfolding locally_compatible_l_def by auto

lemma lcr_trans_r: 
  assumes "locally_compatible_r R1 R2 (A + B) (C + D) (E + F)"
  shows "locally_compatible_r R1 R2 B D F"
  using assms[unfolded locally_compatible_r_def, rule_format]
  unfolding locally_compatible_r_def by auto

lemma lr_minus:
  assumes "locally_refl R A"
  shows "locally_refl R (A - B)"
  using assms unfolding locally_refl_def by (meson in_diffD)

lemma li_minus:
  assumes "locally_irrefl R A"
  shows "locally_irrefl R (A - B)"
  using assms unfolding locally_irrefl_def by (meson in_diffD)

lemma ls_minus:
  assumes "locally_sym R A"
  shows "locally_sym R (A - B)"
  using assms unfolding locally_sym_def by (meson in_diffD)


lemma las_minus:
  assumes "locally_antisym R A"
  shows "locally_antisym R (A - B)"
  using assms unfolding locally_antisym_def by (meson in_diffD)

lemma lt_minus:
  assumes "locally_trans R A C E"
  shows "locally_trans R (A - B) (C - D) (E - F)"
  using assms[unfolded locally_trans_def, rule_format]
  unfolding locally_trans_def by (meson in_diffD)


lemma lin_minus: 
  assumes "locally_included R1 R2 A C"
  shows "locally_included R1 R2 (A - B) (C - D)"
  using assms unfolding locally_included_def by (meson in_diffD)

lemma lcl_minus:
  assumes "locally_compatible_l R1 R2 A C E"
  shows "locally_compatible_l R1 R2 (A - B) (C - D) (E - F)"
  using assms[unfolded locally_compatible_l_def, rule_format]
  unfolding locally_compatible_l_def by (meson in_diffD)

lemma lcr_minus: 
  assumes "locally_compatible_r R1 R2 A C E"
  shows "locally_compatible_r R1 R2 (A - B) (C - D) (E - F)"
  using assms[unfolded locally_compatible_r_def, rule_format]
  unfolding locally_compatible_r_def by (meson in_diffD)


text \<open>Notations\<close>

notation restrict (infixl "\<restriction>" 80)

lemma mem_restrictI[intro!]: assumes "x \<in> X" "y \<in> X" "(x,y) \<in> R" shows "(x,y) \<in> R \<restriction> X"
  using assms unfolding restrict_def by auto

lemma mem_restrictD[dest]: assumes "(x,y) \<in> R \<restriction> X" shows "x \<in> X" "y \<in> X" "(x,y) \<in> R"
  using assms unfolding restrict_def by auto


end
