(*
    File:     DirProds.thy
    Author:   Joseph Thommes, TU München
*)
section \<open>Direct group product\<close>

theory DirProds
  imports Finite_Product_Extend Group_Hom Finite_And_Cyclic_Groups
begin

notation integer_mod_group ("Z")

text \<open>The direct group product is defined component-wise and provided in an indexed way.\<close>

definition DirProds :: "('a \<Rightarrow> ('b, 'c) monoid_scheme) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) monoid" where
  "DirProds G I = \<lparr> carrier = Pi\<^sub>E I (carrier \<circ> G),
                   monoid.mult = (\<lambda>x y. restrict (\<lambda>i. x i \<otimes>\<^bsub>G i\<^esub> y i) I),
                   one = restrict (\<lambda>i. \<one>\<^bsub>G i\<^esub>) I \<rparr>"

text \<open>Basic lemmas about \<open>DirProds\<close>.\<close>

lemma DirProds_empty:
  "carrier (DirProds f {}) = {\<one>\<^bsub>DirProds f {}\<^esub>}"
  unfolding DirProds_def by auto

lemma DirProds_order:
  assumes "finite I"
  shows "order (DirProds G I) = prod (order \<circ> G) I"
  unfolding order_def DirProds_def using assms by (simp add: card_PiE)

lemma DirProds_in_carrI:
  assumes "\<And>i. i \<in> I \<Longrightarrow> x i \<in> carrier (G i)" "\<And>i. i \<notin> I \<Longrightarrow> x i = undefined"
  shows "x \<in> carrier (DirProds G I)"
  unfolding DirProds_def using assms by auto

lemma comp_in_carr:
  assumes "x \<in> carrier (DirProds G I)" "i \<in> I"
  shows "x i \<in> carrier (G i)"
  using assms unfolding DirProds_def by auto

lemma comp_mult:
  assumes "i \<in> I"
  shows "(x \<otimes>\<^bsub>DirProds G I\<^esub> y) i = (x i \<otimes>\<^bsub>G i\<^esub> y i)"
  using assms unfolding DirProds_def by simp

lemma comp_exp_nat:
  fixes k::nat
  assumes "i \<in> I"
  shows "(x [^]\<^bsub>DirProds G I\<^esub> k) i = x i [^]\<^bsub>G i\<^esub> k"
proof (induction k)
  case 0
  then show ?case using assms unfolding DirProds_def by simp
next
  case i: (Suc k)
  have "(x [^]\<^bsub>DirProds G I\<^esub> k \<otimes>\<^bsub>DirProds G I\<^esub> x) i = (x [^]\<^bsub>DirProds G I\<^esub> k) i \<otimes>\<^bsub>G i\<^esub> x i"
    by(rule comp_mult[OF assms])
  also from i have "\<dots> = x i [^]\<^bsub>G i\<^esub> k \<otimes>\<^bsub>G i\<^esub> x i" by simp
  also have "\<dots> = x i [^]\<^bsub>G i\<^esub> Suc k" by simp
  finally show ?case by simp
qed

lemma DirProds_m_closed:
  assumes "x \<in> carrier (DirProds G I)" "y \<in> carrier (DirProds G I)" "\<And>i. i \<in> I \<Longrightarrow> group (G i)"
  shows "x \<otimes>\<^bsub>DirProds G I\<^esub> y \<in> carrier (DirProds G I)"
  using assms monoid.m_closed[OF group.is_monoid[OF assms(3)]] unfolding DirProds_def by fastforce

lemma partial_restr:
  assumes "a \<in> carrier (DirProds G I)" "J \<subseteq> I"
  shows "restrict a J \<in> carrier (DirProds G J)"
  using assms unfolding DirProds_def by auto 

lemma eq_parts_imp_eq:
  assumes "a \<in> carrier (DirProds G I)" "b \<in> carrier (DirProds G I)" "\<And>i. i \<in> I \<Longrightarrow> a i = b i"
  shows "a = b"
  using assms unfolding DirProds_def by fastforce

lemma mult_restr:
  assumes "a \<in> carrier (DirProds G I)" "b \<in> carrier (DirProds G I)" "J \<subseteq> I"
  shows "a \<otimes>\<^bsub>DirProds G J\<^esub> b = restrict (a \<otimes>\<^bsub>DirProds G I\<^esub> b) J"
  using assms unfolding DirProds_def by force

lemma DirProds_one:
  assumes "x \<in> carrier (DirProds G I)"
  shows "(\<forall>i \<in> I. x i = \<one>\<^bsub>G i\<^esub>) \<longleftrightarrow> x = \<one>\<^bsub>DirProds G I\<^esub>"
  using assms unfolding DirProds_def by fastforce

lemma DirProds_one':
  "i\<in>I \<Longrightarrow> \<one>\<^bsub>DirProds G I\<^esub> i = \<one>\<^bsub>G i\<^esub>"
  unfolding DirProds_def by simp

lemma DirProds_one'':
  "\<one>\<^bsub>DirProds G I\<^esub> = restrict (\<lambda>i. \<one>\<^bsub>G i\<^esub>) I"
  by (unfold DirProds_def, simp)

lemma DirProds_mult:
  "(\<otimes>\<^bsub>DirProds G I\<^esub>) = (\<lambda>x y. restrict (\<lambda>i. x i \<otimes>\<^bsub>G i\<^esub> y i) I)"
  unfolding DirProds_def by simp

lemma DirProds_one_iso: "(\<lambda>x. x G) \<in> iso (DirProds f {G}) (f G)"
proof (intro isoI homI)
  show "bij_betw (\<lambda>x. x G) (carrier (DirProds f {G})) (carrier (f G))"
  proof (unfold bij_betw_def, rule)
    show "inj_on (\<lambda>x. x G) (carrier (DirProds f {G}))"
      by (intro inj_onI, unfold DirProds_def PiE_def Pi_def extensional_def, fastforce)
    show "(\<lambda>x. x G) ` carrier (DirProds f {G}) = carrier (f G)"
    proof(intro equalityI subsetI)
      show "x \<in> carrier (f G)" if "x \<in> (\<lambda>x. x G) ` carrier (DirProds f {G})" for x
        using that unfolding DirProds_def by auto
      show "x \<in> (\<lambda>x. x G) ` carrier (DirProds f {G})" if xc: "x \<in> carrier (f G)" for x
      proof
        show "(\<lambda>k\<in>{G}. x) \<in> carrier (DirProds f {G})" unfolding DirProds_def using xc by auto
        moreover show "x = (\<lambda>k\<in>{G}. x) G" by simp
      qed
    qed
  qed
qed (unfold DirProds_def PiE_def Pi_def extensional_def, auto)

lemma DirProds_one_cong: "(DirProds f {G}) \<cong> (f G)"
  using DirProds_one_iso is_isoI by fast

lemma DirProds_one_iso_sym: "(\<lambda>x. (\<lambda>_\<in>{G}. x)) \<in> iso (f G) (DirProds f {G})"
proof (intro isoI homI)
  show "bij_betw (\<lambda>x. \<lambda>_\<in>{G}. x) (carrier (f G)) (carrier (DirProds f {G}))"
  proof (unfold bij_betw_def, rule)
    show "inj_on (\<lambda>x. (\<lambda>_\<in>{G}. x)) (carrier (f G))"
      by (intro inj_onI, metis imageI image_constant image_restrict_eq member_remove remove_def)
    show "(\<lambda>x. (\<lambda>_\<in>{G}. x)) ` carrier (f G) = carrier (DirProds f {G})"
      unfolding DirProds_def by fastforce
  qed
qed (unfold DirProds_def, auto)

lemma DirProds_one_cong_sym: "(f G) \<cong> (DirProds f {G})"
  using DirProds_one_iso_sym is_isoI by fast

text \<open>The direct product is a group iff all factors are groups.\<close>

lemma DirProds_is_group:
  assumes "\<And>i. i \<in> I \<Longrightarrow> group (G i)"
  shows "group (DirProds G I)"
proof(rule groupI)
  show one_closed: "\<one>\<^bsub>DirProds G I\<^esub> \<in> carrier (DirProds G I)" unfolding DirProds_def
    by (simp add: assms group.is_monoid)
  fix x
  assume x: "x \<in> carrier (DirProds G I)"
  have one_: "\<And>i. i \<in> I \<Longrightarrow> \<one>\<^bsub>G i\<^esub> = \<one>\<^bsub>DirProds G I\<^esub> i" unfolding DirProds_def by simp
  have "\<And>i. i \<in> I \<Longrightarrow> \<one>\<^bsub>DirProds G I\<^esub> i \<otimes>\<^bsub>G i\<^esub> x i = x i"
  proof -
    fix i
    assume i: "i \<in> I"
    interpret group "G i" using assms[OF i] .
    have "x i \<in> carrier (G i)" using x i comp_in_carr by fast
    thus "\<one>\<^bsub>DirProds G I\<^esub> i \<otimes>\<^bsub>G i\<^esub> x i = x i" by(subst one_[OF i, symmetric]; simp)
  qed
  with one_ x show "\<one>\<^bsub>DirProds G I\<^esub> \<otimes>\<^bsub>DirProds G I\<^esub> x = x" unfolding DirProds_def by force
  have "restrict (\<lambda>i. inv\<^bsub>G i\<^esub> (x i)) I \<in> carrier (DirProds G I)" using x group.inv_closed[OF assms]
    unfolding DirProds_def by fastforce 
  moreover have "restrict (\<lambda>i. inv\<^bsub>G i\<^esub> (x i)) I \<otimes>\<^bsub>DirProds G I\<^esub> x = \<one>\<^bsub>DirProds G I\<^esub>"
    using x group.l_inv[OF assms] unfolding DirProds_def by fastforce
  ultimately show "\<exists>y\<in>carrier (DirProds G I). y \<otimes>\<^bsub>DirProds G I\<^esub> x = \<one>\<^bsub>DirProds G I\<^esub>" by blast
  fix y
  assume y: "y \<in> carrier (DirProds G I)"
  from DirProds_m_closed[OF x y assms] show m_closed: "x \<otimes>\<^bsub>DirProds G I\<^esub> y \<in> carrier (DirProds G I)"
    by blast
  fix z
  assume z: "z \<in> carrier (DirProds G I)"
  have "\<And>i. i \<in> I \<Longrightarrow> (x \<otimes>\<^bsub>DirProds G I\<^esub> y \<otimes>\<^bsub>DirProds G I\<^esub> z) i
                    = (x \<otimes>\<^bsub>DirProds G I\<^esub> (y \<otimes>\<^bsub>DirProds G I\<^esub> z)) i"
  proof -
    fix i
    assume i: "i \<in> I"
    have "(x \<otimes>\<^bsub>DirProds G I\<^esub> y \<otimes>\<^bsub>DirProds G I\<^esub> z) i = (x \<otimes>\<^bsub>DirProds G I\<^esub> y) i \<otimes>\<^bsub>G i\<^esub> z i"
      using assms by (simp add: comp_mult i m_closed z)
    also have "\<dots> = x i \<otimes>\<^bsub>G i\<^esub> y i \<otimes>\<^bsub>G i\<^esub> z i" by (simp add: assms comp_mult i x y)
    also have "\<dots> = x i \<otimes>\<^bsub>G i\<^esub> (y i \<otimes>\<^bsub>G i\<^esub> z i)" using i assms x y z
      by (meson Group.group_def comp_in_carr monoid.m_assoc)
    also have "\<dots> = (x \<otimes>\<^bsub>DirProds G I\<^esub> (y \<otimes>\<^bsub>DirProds G I\<^esub> z)) i" by (simp add: DirProds_def i)
    finally show "(x \<otimes>\<^bsub>DirProds G I\<^esub> y \<otimes>\<^bsub>DirProds G I\<^esub> z) i
                = (x \<otimes>\<^bsub>DirProds G I\<^esub> (y \<otimes>\<^bsub>DirProds G I\<^esub> z)) i" .
  qed
  thus "x \<otimes>\<^bsub>DirProds G I\<^esub> y \<otimes>\<^bsub>DirProds G I\<^esub> z = x \<otimes>\<^bsub>DirProds G I\<^esub> (y \<otimes>\<^bsub>DirProds G I\<^esub> z)"
    unfolding DirProds_def by auto
qed

lemma DirProds_obtain_elem_carr:
  assumes "group (DirProds G I)" "i \<in> I" "x \<in> carrier (G i)"
  obtains k where "k \<in> carrier (DirProds G I)" "k i = x"
proof -
  interpret DP: group "DirProds G I" by fact
  from comp_in_carr[OF DP.one_closed] DirProds_one' have ao: "\<forall>j\<in>I. \<one>\<^bsub>G j\<^esub> \<in> carrier (G j)" by metis
  let ?r = "restrict ((\<lambda>j. \<one>\<^bsub>G j\<^esub>)(i := x)) I"
  have "?r \<in> carrier (DirProds G I)"
    unfolding DirProds_def PiE_def Pi_def using assms(2, 3) ao by auto
  moreover have "?r i = x" using assms(2) by simp
  ultimately show "(\<And>k. \<lbrakk>k \<in> carrier (DirProds G I); k i = x\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis" by blast
qed

lemma DirProds_group_imp_groups:
  assumes "group (DirProds G I)" and i: "i \<in> I"
  shows "group (G i)"
proof (intro groupI)
  let ?DP = "DirProds G I"
  interpret DP: group ?DP by fact
  show "\<one>\<^bsub>G i\<^esub> \<in> carrier (G i)" using DirProds_one' comp_in_carr[OF DP.one_closed i] i by metis
  show "x \<otimes>\<^bsub>G i\<^esub> y \<in> carrier (G i)" if "x \<in> carrier (G i)" "y \<in> carrier (G i)" for x y
  proof -
    from DirProds_obtain_elem_carr[OF assms that(1)] obtain k where k: "k \<in> carrier ?DP" "k i = x" .
    from DirProds_obtain_elem_carr[OF assms that(2)] obtain l where l: "l \<in> carrier ?DP" "l i = y" .
    have "k \<otimes>\<^bsub>?DP\<^esub> l \<in> carrier ?DP" using k l by fast
    from comp_in_carr[OF this i] comp_mult[OF i] show ?thesis using k l by metis
  qed
  show "x \<otimes>\<^bsub>G i\<^esub> y \<otimes>\<^bsub>G i\<^esub> z = x \<otimes>\<^bsub>G i\<^esub> (y \<otimes>\<^bsub>G i\<^esub> z)"
    if x: "x \<in> carrier (G i)" and y: "y \<in> carrier (G i)" and z: "z \<in> carrier (G i)" for x y z
  proof -
    from DirProds_obtain_elem_carr[OF assms x] obtain k where k: "k \<in> carrier ?DP" "k i = x" .
    from DirProds_obtain_elem_carr[OF assms y] obtain l where l: "l \<in> carrier ?DP" "l i = y" .
    from DirProds_obtain_elem_carr[OF assms z] obtain m where m: "m \<in> carrier ?DP" "m i = z" .
    have "x \<otimes>\<^bsub>G i\<^esub> y \<otimes>\<^bsub>G i\<^esub> z = (k i) \<otimes>\<^bsub>G i\<^esub> (l i) \<otimes>\<^bsub>G i\<^esub> (m i)" using k l m by argo
    also have "\<dots> = (k \<otimes>\<^bsub>?DP\<^esub> l \<otimes>\<^bsub>?DP\<^esub> m) i" using comp_mult[OF i] k l m by metis
    also have "\<dots> = (k \<otimes>\<^bsub>?DP\<^esub> (l \<otimes>\<^bsub>?DP\<^esub> m)) i"
    proof -
      have "k \<otimes>\<^bsub>?DP\<^esub> l \<otimes>\<^bsub>?DP\<^esub> m = k \<otimes>\<^bsub>?DP\<^esub> (l \<otimes>\<^bsub>?DP\<^esub> m)" using DP.m_assoc[OF k(1) l(1) m(1)] .
      thus ?thesis by simp
    qed
    also have "\<dots> = (k i) \<otimes>\<^bsub>G i\<^esub> ((l i) \<otimes>\<^bsub>G i\<^esub> (m i))" using comp_mult[OF i] k l m by metis
    finally show ?thesis using k l m by blast
  qed
  show "\<one>\<^bsub>G i\<^esub> \<otimes>\<^bsub>G i\<^esub> x = x" if "x \<in> carrier (G i)" for x
  proof -
    from DirProds_obtain_elem_carr[OF assms that(1)] obtain k where k: "k \<in> carrier ?DP" "k i = x" .
    hence "\<one>\<^bsub>?DP\<^esub> \<otimes>\<^bsub>?DP\<^esub> k = k" by simp
    with comp_mult k DirProds_one[OF DP.one_closed] that i show ?thesis by metis
  qed
  show "\<exists>y\<in>carrier (G i). y \<otimes>\<^bsub>G i\<^esub> x = \<one>\<^bsub>G i\<^esub>" if "x \<in> carrier (G i)" for x
  proof -
    from DirProds_obtain_elem_carr[OF assms that(1)] obtain k where k: "k \<in> carrier ?DP" "k i = x" .
    hence ic: "inv\<^bsub>?DP\<^esub> k \<in> carrier ?DP" by simp
    have "inv\<^bsub>?DP\<^esub> k \<otimes>\<^bsub>?DP\<^esub> k = \<one>\<^bsub>?DP\<^esub>" using k by simp
    hence "(inv\<^bsub>?DP\<^esub> k) i \<otimes>\<^bsub>G i\<^esub> k i= \<one>\<^bsub>G i\<^esub>" using comp_mult[OF i] DirProds_one'[OF i] by metis
    with k(2) comp_in_carr[OF ic i] show ?thesis by blast
  qed
qed

lemma DirProds_group_iff: "group (DirProds G I) \<longleftrightarrow> (\<forall>i\<in>I. group (G i))"
  using DirProds_is_group DirProds_group_imp_groups by metis

lemma comp_inv:
  assumes "group (DirProds G I)" and x: "x \<in> carrier (DirProds G I)" and i: "i \<in> I"
  shows "(inv\<^bsub>(DirProds G I)\<^esub> x) i = inv\<^bsub>(G i)\<^esub> (x i)"
proof -
  interpret DP: group "DirProds G I" by fact
  interpret Gi: group "G i" using DirProds_group_imp_groups[OF DP.is_group i] .
  have ixc: "inv\<^bsub>(DirProds G I)\<^esub> x \<in> carrier (DirProds G I)" using x by blast
  hence "inv\<^bsub>(DirProds G I)\<^esub> x \<otimes>\<^bsub>DirProds G I\<^esub> x = \<one>\<^bsub>DirProds G I\<^esub>" using x by simp
  hence "(inv\<^bsub>(DirProds G I)\<^esub> x \<otimes>\<^bsub>DirProds G I\<^esub> x) i = \<one>\<^bsub>G i\<^esub>" by (simp add: DirProds_one' i)
  moreover from comp_mult[OF i]
  have "(inv\<^bsub>(DirProds G I)\<^esub> x \<otimes>\<^bsub>DirProds G I\<^esub> x) i = ((inv\<^bsub>(DirProds G I)\<^esub> x) i) \<otimes>\<^bsub>G i\<^esub> (x i)"
    by blast
  ultimately show ?thesis using x ixc by (simp add: comp_in_carr[OF _ i] group.inv_equality)
qed

text \<open>The same is true for abelian groups.\<close>

lemma DirProds_is_comm_group:
  assumes "\<And>i. i \<in> I \<Longrightarrow> comm_group (G i)"
  shows "comm_group (DirProds G I)" (is "comm_group ?DP")
proof
  interpret group ?DP using assms DirProds_is_group unfolding comm_group_def by metis
  show "carrier ?DP \<subseteq> Units ?DP" "\<one>\<^bsub>?DP\<^esub> \<in> carrier ?DP" by simp_all
  fix x
  assume x[simp]: "x \<in> carrier ?DP"
  show "\<one>\<^bsub>?DP\<^esub> \<otimes>\<^bsub>?DP\<^esub> x = x" "x \<otimes>\<^bsub>?DP\<^esub> \<one>\<^bsub>?DP\<^esub> = x" by simp_all
  fix y
  assume y[simp]: "y \<in> carrier ?DP"
  show "x \<otimes>\<^bsub>?DP\<^esub> y \<in> carrier ?DP" by simp
  show "x \<otimes>\<^bsub>DirProds G I\<^esub> y = y \<otimes>\<^bsub>DirProds G I\<^esub> x"
  proof (rule eq_parts_imp_eq[of _ G I])
    show "x \<otimes>\<^bsub>?DP\<^esub> y \<in> carrier ?DP" by simp
    show "y \<otimes>\<^bsub>?DP\<^esub> x \<in> carrier ?DP" by simp
    show "\<And>i. i\<in>I \<Longrightarrow> (x \<otimes>\<^bsub>DirProds G I\<^esub> y) i = (y \<otimes>\<^bsub>DirProds G I\<^esub> x) i"
    proof -
      fix i
      assume i: "i \<in> I"
      interpret gi: comm_group "(G i)" using assms(1)[OF i] .
      have "(x \<otimes>\<^bsub>?DP\<^esub> y) i = x i \<otimes>\<^bsub>G i\<^esub> y i"
        by (intro comp_mult[OF i])
      also have "\<dots> = y i \<otimes>\<^bsub>G i\<^esub> x i" using comp_in_carr[OF _ i] x y gi.m_comm by metis
      also have "\<dots> = (y \<otimes>\<^bsub>?DP\<^esub> x) i" by (intro comp_mult[symmetric, OF i])
      finally show "(x \<otimes>\<^bsub>DirProds G I\<^esub> y) i = (y \<otimes>\<^bsub>DirProds G I\<^esub> x) i" .
    qed
  qed
  fix z
  assume z[simp]: "z \<in> carrier ?DP"
  show "x \<otimes>\<^bsub>?DP\<^esub> y \<otimes>\<^bsub>?DP\<^esub> z = x \<otimes>\<^bsub>?DP\<^esub> (y \<otimes>\<^bsub>?DP\<^esub> z)" using m_assoc by simp
qed

lemma DirProds_comm_group_imp_comm_groups:
  assumes "comm_group (DirProds G I)" and i: "i \<in> I"
  shows "comm_group (G i)"
proof -
  interpret DP: comm_group "DirProds G I" by fact
  interpret Gi: group "G i" using DirProds_group_imp_groups[OF DP.is_group i] .
  show "comm_group (G i)"
  proof
    show "x \<otimes>\<^bsub>G i\<^esub> y = y \<otimes>\<^bsub>G i\<^esub> x" if x: "x \<in> carrier (G i)" and y: "y \<in> carrier (G i)" for x y
    proof -
      obtain a where a[simp]: "a \<in> carrier (DirProds G I)" "a i = x"
        using DirProds_obtain_elem_carr[OF DP.is_group i x] .
      obtain b where b[simp]: "b \<in> carrier (DirProds G I)" "b i = y"
        using DirProds_obtain_elem_carr[OF DP.is_group i y] .
      have "a \<otimes>\<^bsub>DirProds G I\<^esub> b = b \<otimes>\<^bsub>DirProds G I\<^esub> a" using DP.m_comm by simp
      hence "(a \<otimes>\<^bsub>DirProds G I\<^esub> b) i = (b \<otimes>\<^bsub>DirProds G I\<^esub> a) i" by argo
      with comp_mult[OF i] have "a i \<otimes>\<^bsub>G i\<^esub> b i = b i \<otimes>\<^bsub>G i\<^esub> a i" by metis
      with a b show "x \<otimes>\<^bsub>G i\<^esub> y = y \<otimes>\<^bsub>G i\<^esub> x" by blast
    qed
  qed
qed

lemma DirProds_comm_group_iff: "comm_group (DirProds G I) \<longleftrightarrow> (\<forall>i\<in>I. comm_group (G i))"
  using DirProds_is_comm_group DirProds_comm_group_imp_comm_groups by metis

text \<open>And also for finite groups.\<close>

lemma DirProds_is_finite_group:
  assumes "\<And>i. i\<in>I \<Longrightarrow> finite_group (G i)" "finite I"
  shows "finite_group (DirProds G I)"
proof -
  have "group (G i)" if "i\<in>I" for i using assms(1)[OF that] unfolding finite_group_def by blast
  from DirProds_is_group[OF this] interpret DP: group "DirProds G I" by fast
  show ?thesis
  proof(unfold_locales)
    have "order (DirProds G I) \<noteq> 0"
    proof(unfold DirProds_order[OF assms(2)])
      have "(order \<circ> G) i \<noteq> 0" if "i\<in>I" for i
        using assms(1)[OF that] by (simp add: finite_group.order_gt_0)
      thus "prod (order \<circ> G) I \<noteq> 0" by (simp add: assms(2))
    qed
    thus "finite (carrier (DirProds G I))" unfolding order_def by (meson card.infinite)
  qed
qed

lemma DirProds_finite_imp_finite_groups:
  assumes "finite_group (DirProds G I)" "finite I"
  shows "\<And>i. i\<in>I \<Longrightarrow> finite_group (G i)"
proof -
  fix i assume i: "i \<in> I"
  interpret DP: finite_group "DirProds G I" by fact
  interpret group "G i" by (rule DirProds_group_imp_groups[OF DP.is_group i])
  show "finite_group (G i)"
  proof(unfold_locales)
    have oDP: "order (DirProds G I) \<noteq> 0" by blast
    with DirProds_order[OF assms(2), of G] have "order (G i) \<noteq> 0" using i assms(2) by force
    thus "finite (carrier (G i))" unfolding order_def by (meson card_eq_0_iff)
  qed
qed

lemma DirProds_finite_group_iff:
  assumes "finite I"
  shows "finite_group (DirProds G I) \<longleftrightarrow> (\<forall>i\<in>I. finite_group (G i))"
  using DirProds_is_finite_group DirProds_finite_imp_finite_groups assms by metis

lemma DirProds_finite_comm_group_iff:
  assumes "finite I"
  shows "finite_comm_group (DirProds G I) \<longleftrightarrow> (\<forall>i\<in>I. finite_comm_group (G i))"
  using DirProds_finite_group_iff[OF assms] DirProds_comm_group_iff unfolding finite_comm_group_def by fast

text \<open>If a group is an internal direct product of a family of subgroups, it is isomorphic to the
direct product of these subgroups.\<close>

lemma (in comm_group) subgroup_iso_DirProds_IDirProds:
  assumes "subgroup J G" "is_idirprod J S I" "finite I"
  shows "(\<lambda>x. \<Otimes>\<^bsub>G\<^esub>i\<in>I. x i) \<in> iso (DirProds (\<lambda>i. G\<lparr>carrier := (S i)\<rparr>) I) (G\<lparr>carrier := J\<rparr>)"
(is "?fp \<in> iso ?DP ?J")
proof -
  from assms(2) have assm: "J = IDirProds G S I"
                           "compl_fam S I"
    unfolding is_idirprod_def by auto
  from assms(1, 2) have assm': "\<And>i. i \<in> I \<Longrightarrow> subgroup (S i) (G\<lparr>carrier := J\<rparr>)"
    using normal_imp_subgroup subgroup_incl by (metis IDirProds_incl assms(2) is_idirprod_def)
  interpret J: comm_group ?J using subgroup_is_comm_group[OF assms(1)] .
  interpret DP: comm_group ?DP
    by (intro DirProds_is_comm_group; use J.subgroup_is_comm_group[OF assm'] in simp)
  have inJ: "S i \<subseteq> J" if "i \<in> I" for i using subgroup.subset[OF assm'[OF that]] by simp
  have hom: "?fp \<in> hom ?DP ?J"
  proof (rule homI)
    fix x
    assume x[simp]: "x \<in> carrier ?DP"
    show "finprod G x I \<in> carrier ?J"
    proof (subst finprod_subgroup[OF _ assms(1)])
      show "x \<in> I \<rightarrow> J" using inJ comp_in_carr[OF x] by auto
      thus "finprod ?J x I \<in> carrier ?J" by (intro J.finprod_closed; simp)
    qed
    fix y
    assume y[simp]: "y \<in> carrier ?DP"
    show "finprod G (x \<otimes>\<^bsub>?DP\<^esub> y) I = finprod G x I \<otimes>\<^bsub>?J\<^esub> finprod G y I"
    proof(subst (1 2 3) finprod_subgroup[of _ _ J])
      show xyJ: "x \<in> I \<rightarrow> J" "y \<in> I \<rightarrow> J" using x y inJ comp_in_carr[OF x] comp_in_carr[OF y]
        by auto
      show xyJ1: "x \<otimes>\<^bsub>?DP\<^esub> y \<in> I \<rightarrow> J" using inJ x y comp_in_carr[of "x \<otimes>\<^bsub>?DP\<^esub> y"] by fastforce
      show "subgroup J G" using assms(1) .
      show "finprod ?J (x \<otimes>\<^bsub>?DP\<^esub> y) I = finprod ?J x I \<otimes>\<^bsub>?J\<^esub> finprod ?J y I"
      proof (rule J.finprod_cong_split)
        show "x \<in> I \<rightarrow> carrier ?J" "y \<in> I \<rightarrow> carrier ?J" using xyJ by simp_all
        show "x \<otimes>\<^bsub>?DP\<^esub> y \<in> I \<rightarrow> carrier ?J" using xyJ1 by simp
        fix i
        assume i: "i \<in> I"
        then have "x i \<otimes>\<^bsub>G\<lparr>carrier := (S i) \<rparr>\<^esub> y i = (x \<otimes>\<^bsub>?DP\<^esub> y) i"
          by (intro comp_mult[symmetric])
        thus "x i \<otimes>\<^bsub>?J\<^esub> y i = (x \<otimes>\<^bsub>?DP\<^esub> y) i" by simp
      qed
    qed
  qed
  then interpret fp: group_hom ?DP ?J ?fp unfolding group_hom_def group_hom_axioms_def by blast
  have s: "subgroup (S i) G" if "i \<in> I" for i using incl_subgroup[OF assms(1) assm'[OF that]] .
  have "kernel ?DP ?J ?fp = {\<one>\<^bsub>?DP\<^esub>}"
  proof -
    have "a = \<one>\<^bsub>?DP\<^esub>" if "a \<in> kernel ?DP ?J ?fp" for a
    proof -
      from that have a: "finprod G a I = \<one>" "a \<in> carrier ?DP" unfolding kernel_def by simp_all
      from compl_fam_imp_triv_finprod[OF assm(2) assms(3) s a(1)] comp_in_carr[OF a(2)]
      have "\<forall>i\<in>I. a i = \<one>" by simp
      then show ?thesis using DirProds_one[OF a(2)] by fastforce
    qed
    thus ?thesis using fp.one_in_kernel by blast
  qed
  moreover have "J \<subseteq> ?fp ` carrier ?DP"
    using assm(1) IDirProds_eq_finprod_PiE[OF assms(3) incl_subgroup[OF assms(1) assm']]
    unfolding DirProds_def PiE_def Pi_def by simp
  ultimately show ?thesis using hom fp.iso_iff unfolding kernel_def by auto
qed

lemma (in comm_group) iso_DirProds_IDirProds:
  assumes "is_idirprod (carrier G) S I" "finite I"
  shows "(\<lambda>x. \<Otimes>\<^bsub>G\<^esub>i\<in>I. x i) \<in> iso (DirProds (\<lambda>i. G\<lparr>carrier := (S i)\<rparr>) I) G"
  using subgroup_iso_DirProds_IDirProds[OF subgroup_self assms(1, 2)] by auto

lemma (in comm_group) cong_DirProds_IDirProds:
  assumes "is_idirprod (carrier G) S I" "finite I"
  shows "DirProds (\<lambda>i. G\<lparr>carrier := (S i)\<rparr>) I \<cong> G"
  by (intro is_isoI, use iso_DirProds_IDirProds[OF assms] in blast)

text \<open>In order to prove the isomorphism between two direct products, the following lemmas provide
some criterias.\<close>

lemma DirProds_iso:
  assumes "bij_betw f I J" "\<And>i. i\<in>I \<Longrightarrow> Gs i \<cong> Hs (f i)"
          "\<And>i. i\<in>I \<Longrightarrow> group (Gs i)" "\<And>j. j\<in>J \<Longrightarrow> group (Hs j)"
  shows "DirProds Gs I \<cong> DirProds Hs J"
proof -
  interpret DG: group "DirProds Gs I" using DirProds_is_group assms(3) by blast
  interpret DH: group "DirProds Hs J" using DirProds_is_group assms(4) by blast
  from assms(1) obtain g where g: "g = inv_into I f" "bij_betw g J I" by (meson bij_betw_inv_into)
  hence fgi: "\<And>i. i \<in> I \<Longrightarrow> g (f i) = i" "\<And>j. j \<in> J \<Longrightarrow> f (g j) = j"
    using assms(1) bij_betw_inv_into_left[OF assms(1)] bij_betw_inv_into_right[OF assms(1)] by auto
  from assms(2) have "\<And>i. i \<in> I \<Longrightarrow> (\<exists>h. h \<in> iso (Gs i) (Hs (f i)))" unfolding is_iso_def by blast
  then obtain h where h: "\<And>i. i \<in> I \<Longrightarrow> h i \<in> iso (Gs i) (Hs (f i))" by metis
  let ?h = "(\<lambda>x. (\<lambda>j. if j\<in>J then (h (g j)) (x (g j)) else undefined))"
  have hc: "?h x \<in> carrier (DirProds Hs J)" if "x \<in> carrier (DirProds Gs I)" for x
  proof -
    have xc: "x \<in> carrier (DirProds Gs I)" by fact
    have "h (g j) (x (g j)) \<in> carrier (Hs j)" if "j \<in> J" for j
    proof(intro iso_in_carr[OF _ comp_in_carr[OF xc], of "h (g j)" "g j" "Hs j"])
      show "g j \<in> I" using g(2)[unfolded bij_betw_def] that by blast
      from h[OF this] show "h (g j) \<in> Group.iso (Gs (g j)) (Hs j)" using fgi(2)[OF that] by simp
    qed
    thus ?thesis using xc unfolding DirProds_def PiE_def extensional_def by auto
  qed
  moreover have "?h (x \<otimes>\<^bsub>DirProds Gs I\<^esub> y)= ?h x \<otimes>\<^bsub>DirProds Hs J\<^esub> ?h y"
    if "x \<in> carrier (DirProds Gs I)" "y \<in> carrier (DirProds Gs I)" for x y
  proof(intro eq_parts_imp_eq[OF hc[OF DG.m_closed[OF that]] DH.m_closed[OF hc[OF that(1)] hc[OF that(2)]]])
    fix j
    assume j: "j \<in> J"
    hence gj: "g j \<in> I" using g unfolding bij_betw_def by blast
    from assms(3)[OF gj] assms(4)[OF j] have g: "group (Gs (g j))" "Group.group (Hs j)" .
    from iso_imp_homomorphism[OF h[OF gj]] fgi(2)[OF j] g
    interpret hjh: group_hom "Gs (g j)" "Hs j" "h (g j)"
      unfolding group_hom_def group_hom_axioms_def by simp
    show "(?h (x \<otimes>\<^bsub>DirProds Gs I\<^esub> y)) j = (?h x \<otimes>\<^bsub>DirProds Hs J\<^esub> ?h y) j"
    proof(subst comp_mult)
      show "(if j \<in> J then h (g j) (x (g j) \<otimes>\<^bsub>Gs (g j)\<^esub> y (g j)) else undefined)
          = (?h x \<otimes>\<^bsub>DirProds Hs J\<^esub> ?h y) j"
      proof(subst comp_mult)
        have "h (g j) (x (g j) \<otimes>\<^bsub>Gs (g j)\<^esub> y (g j)) = h (g j) (x (g j)) \<otimes>\<^bsub>Hs j\<^esub> h (g j) (y (g j))"
          using comp_in_carr[OF that(1) gj] comp_in_carr[OF that(2) gj] by simp
        thus "(if j \<in> J then h (g j) (x (g j) \<otimes>\<^bsub>Gs (g j)\<^esub> y (g j)) else undefined) =
              (if j \<in> J then h (g j) (x (g j)) else undefined)
      \<otimes>\<^bsub>Hs j\<^esub> (if j \<in> J then h (g j) (y (g j)) else undefined)"
          using j by simp
      qed (use j g that hc in auto)
    qed (use gj g that in auto)
  qed
  ultimately interpret hgh: group_hom "DirProds Gs I" "DirProds Hs J" ?h
    unfolding group_hom_def group_hom_axioms_def by (auto intro: homI)
  have "carrier (DirProds Hs J) \<subseteq> ?h ` carrier (DirProds Gs I)"
  proof
    show "x \<in> ?h ` carrier (DirProds Gs I)" if xc: "x \<in> carrier (DirProds Hs J)" for x
    proof -
      from h obtain k where k: "\<And>i. i\<in>I \<Longrightarrow> k i = inv_into (carrier (Gs i)) (h i)" by fast
      hence kiso: "\<And>i. i\<in>I \<Longrightarrow> k i \<in> iso (Hs (f i)) (Gs i)"
        using h by (simp add: assms(3) group.iso_set_sym)
      hence hk: "y = (h (g j) \<circ> (k (g j))) y" if "j \<in> J" "y \<in> carrier (Hs j)" for j y
      proof -
        have gj: "g j \<in> I" using that g[unfolded bij_betw_def] by blast
        thus ?thesis
          using h[OF gj, unfolded iso_def] k[OF gj] that fgi(2)[OF that(1)] bij_betw_inv_into_right
          unfolding comp_def by fastforce
      qed
      let ?k = "(\<lambda>i. if i\<in>I then k i else (\<lambda>_. undefined))"
      let ?y = "(\<lambda>i. (?k i) (x (f i)))"
      have "x j = (\<lambda>j. if j \<in> J then h (g j) (?y (g j)) else undefined) j" for j
      proof (cases "j \<in> J")
        case True
        thus ?thesis using hk[OF True comp_in_carr[OF that True]]
                           fgi(2)[OF True] g[unfolded bij_betw_def] by auto
      next
        case False
        thus ?thesis using that[unfolded DirProds_def] by auto
      qed
      moreover have "?y \<in> carrier (DirProds Gs I)"
      proof -
        have "?y i \<in> carrier (Gs i)" if i: "i \<in> I" for i
          using k[OF i] h[OF i] comp_in_carr[OF xc] assms(1) bij_betwE iso_in_carr kiso that
          by fastforce
        moreover have "?y i = undefined" if i: "i \<notin> I" for i using i by simp
        ultimately show ?thesis unfolding DirProds_def PiE_def Pi_def extensional_def by simp
      qed
      ultimately show ?thesis by fast
    qed
  qed
  moreover have "x = \<one>\<^bsub>DirProds Gs I\<^esub>"
    if "x \<in> carrier (DirProds Gs I)" "?h x = \<one>\<^bsub>DirProds Hs J\<^esub>" for x
  proof -
    have "\<forall>i\<in>I. x i = \<one>\<^bsub>Gs i\<^esub>"
    proof
      fix i
      assume i: "i \<in> I"
      interpret gi: group "Gs i" using assms(3)[OF i] .
      interpret hfi: group "Hs (f i)" using assms(4) i assms(1)[unfolded bij_betw_def] by blast
      from h[OF i] interpret hi: group_hom "(Gs i)" "Hs (f i)" "h i"
        unfolding group_hom_def group_hom_axioms_def iso_def by blast
      from that have hx: "?h x \<in> carrier (DirProds Hs J)" by simp
      from DirProds_one[OF this] that(2)
      have "(if j \<in> J then h (g j) (x (g j)) else undefined) = \<one>\<^bsub>Hs j\<^esub>" if "j \<in> J" for j
        using that by blast
      hence "h (g (f i)) (x (g (f i))) = \<one>\<^bsub>Hs (f i)\<^esub>" using i assms(1)[unfolded bij_betw_def] by auto
      hence "h i (x i) = \<one>\<^bsub>Hs (f i)\<^esub>" using fgi(1)[OF i] by simp
      with hi.iso_iff h[OF i] comp_in_carr[OF that(1) i] show "x i = \<one>\<^bsub>Gs i\<^esub>" by fast
    qed
    with DirProds_one that show ?thesis using assms(3) by blast
  qed
  ultimately show ?thesis unfolding is_iso_def using hgh.iso_iff by blast
qed

lemma DirProds_iso1:
  assumes "\<And>i. i\<in>I \<Longrightarrow> Gs i \<cong> (f \<circ> Gs) i" "\<And>i. i\<in>I \<Longrightarrow> group (Gs i)" "\<And>i. i\<in>I \<Longrightarrow> group ((f \<circ> Gs) i)"
  shows "DirProds Gs I \<cong> DirProds (f \<circ> Gs) I"
proof -
  interpret DP: group "DirProds Gs I" using DirProds_is_group assms by metis
  interpret fDP: group "DirProds (f \<circ> Gs) I" using DirProds_is_group assms by metis
  from assms have "\<forall>i\<in>I. (\<exists>g. g \<in> iso (Gs i) ((f \<circ> Gs) i))" unfolding is_iso_def by blast
  then obtain J where J: "\<forall>i\<in>I. J i \<in> iso (Gs i) ((f \<circ> Gs) i)" by metis
  let ?J = "(\<lambda>i. if i\<in>I then J i else (\<lambda>_. undefined))"
  from J obtain K where K: "\<forall>i\<in>I. K i = inv_into (carrier (Gs i)) (J i)" by fast
  hence K_iso: "\<forall>i\<in>I. K i \<in> iso ((f \<circ> Gs) i) (Gs i)" using group.iso_set_sym assms J by metis
  let ?K = "(\<lambda>i. if i\<in>I then K i else (\<lambda>_. undefined))"
  have JKi: "(?J i) ((?K i) (x i)) = x i" if "x \<in> carrier (DirProds (f \<circ> Gs) I)" for i x
  proof -
    have "(J i) ((K i) (x i)) = x i" if "x \<in> carrier (DirProds (f \<circ> Gs) I)" "i \<in> I" for i x
    proof -
      from J that have "(J i) ` (carrier (Gs i)) = carrier ((f \<circ> Gs) i)"
        unfolding iso_def bij_betw_def by blast
      hence "\<exists>y. y \<in> carrier (Gs i) \<and> (J i) y = x i" using that by (metis comp_in_carr imageE)
      with someI_ex[OF this] that show "(J i) ((K i) (x i)) = x i"
        using K J K_iso unfolding inv_into_def by auto
    qed
    moreover have "(?J i) ((K i) (x i)) = x i" if "x \<in> carrier (DirProds (f \<circ> Gs) I)" "i \<notin> I" for i x
      using that unfolding DirProds_def PiE_def extensional_def by force
    ultimately show ?thesis using that by simp
  qed
  let ?r = "(\<lambda>e. restrict (\<lambda>i. ?J i (e i)) I)"
  have hom: "?r \<in> hom (DirProds Gs I) (DirProds (f \<circ> Gs) I)"
  proof (intro homI)
    show "?r x \<in> carrier (DirProds (f \<circ> Gs) I)" if "x \<in> carrier (DirProds Gs I)" for x
      using that J comp_in_carr[OF that] unfolding DirProds_def iso_def bij_betw_def by fastforce
    show "?r (x \<otimes>\<^bsub>DirProds Gs I\<^esub> y) = ?r x \<otimes>\<^bsub>DirProds (f \<circ> Gs) I\<^esub> ?r y"
      if "x \<in> carrier (DirProds Gs I)" "y \<in> carrier (DirProds Gs I)" for x y
      using that J comp_in_carr[OF that(1)] comp_in_carr[OF that(2)]
      unfolding DirProds_def iso_def hom_def by force
  qed
  then interpret r: group_hom "(DirProds Gs I)" "(DirProds (f \<circ> Gs) I)" ?r
    unfolding group_hom_def group_hom_axioms_def by blast
  have "carrier (DirProds (f \<circ> Gs) I) \<subseteq> ?r ` carrier (DirProds Gs I)"
  proof
    show "x \<in> ?r ` carrier (DirProds Gs I)" if "x \<in> carrier (DirProds (f \<circ> Gs) I)" for x
    proof
      show "x = (\<lambda>i\<in>I. ?J i ((?K i) (x i)))"
        using JKi[OF that] that unfolding DirProds_def PiE_def by (simp add: extensional_restrict)
      show "(\<lambda>i. ?K i (x i)) \<in> carrier (DirProds Gs I)" using K_iso iso_in_carr that
        unfolding DirProds_def PiE_def Pi_def extensional_def by fastforce
    qed
  qed
  moreover have "x = \<one>\<^bsub>DirProds Gs I\<^esub>"
    if "x \<in> carrier (DirProds Gs I)" "?r x = \<one>\<^bsub>DirProds (f \<circ> Gs) I\<^esub>" for x
  proof -
    have "\<forall>i\<in>I. x i = \<one>\<^bsub>Gs i\<^esub>"
    proof
      fix i
      assume i: "i \<in> I"
      with J assms interpret Ji: group_hom "(Gs i)" "(f \<circ> Gs) i" "J i"
        unfolding group_hom_def group_hom_axioms_def iso_def by blast
      from that have rx: "?r x \<in> carrier (DirProds (f \<circ> Gs) I)" by simp
      from i DirProds_one[OF this] that
      have "(\<lambda>i\<in>I. (if i \<in> I then J i else (\<lambda>_. undefined)) (x i)) i = \<one>\<^bsub>(f \<circ> Gs) i\<^esub>" by blast
      hence "(J i) (x i) = \<one>\<^bsub>(f \<circ> Gs) i\<^esub>" using i by simp
      with Ji.iso_iff mp[OF spec[OF J[unfolded Ball_def]] i] comp_in_carr[OF that(1) i]
      show "x i = \<one>\<^bsub>Gs i\<^esub>" by fast
    qed
    with DirProds_one[OF that(1)] show ?thesis by blast
  qed
  ultimately show ?thesis unfolding is_iso_def using r.iso_iff by blast
qed

lemma DirProds_iso2:
  assumes "inj_on f A" "group (DirProds g (f ` A))"
  shows "DirProds (g \<circ> f) A \<cong> DirProds g (f ` A)"
proof (intro DirProds_iso[of f])
  show "bij_betw f A (f ` A)" using assms(1) unfolding bij_betw_def by blast
  show "\<And>i. i \<in> A \<Longrightarrow> (g \<circ> f) i \<cong> g (f i)" unfolding comp_def using iso_refl by simp
  from assms(2) show "\<And>i. i \<in> (f ` A) \<Longrightarrow> group (g i)" using DirProds_group_imp_groups by fast
  with assms(1) show "\<And>i. i \<in> A \<Longrightarrow> group ((g \<circ> f) i)" by auto
qed

text \<open>The direct group product distributes when nested.\<close>

lemma DirProds_Sigma:
  "DirProds (\<lambda>i. DirProds (G i) (J i)) I \<cong> DirProds (\<lambda>(i,j). G i j) (Sigma I J)" (is "?L \<cong> ?R")
proof (intro is_isoI isoI)
  let ?f = "\<lambda>x. restrict (case_prod x) (Sigma I J)"
  show hom: "?f \<in> hom ?L ?R"
  proof(intro homI)
    show "?f a \<in> carrier ?R" if "a \<in> carrier ?L" for a
      using that unfolding DirProds_def PiE_def Pi_def extensional_def by auto
    show "?f (a \<otimes>\<^bsub>?L\<^esub> b) = ?f a \<otimes>\<^bsub>?R\<^esub> ?f b" if "a \<in> carrier ?L" and "b \<in> carrier ?L" for a b
      using that unfolding DirProds_def PiE_def Pi_def extensional_def by auto
  qed
  show "bij_betw ?f (carrier ?L) (carrier ?R)"
  proof (intro bij_betwI)
    let ?g = "\<lambda>x. (\<lambda>i. if i\<in>I then (\<lambda>j. if j\<in>(J i) then x(i, j) else undefined) else undefined)"
    show "?f \<in> carrier ?L \<rightarrow> carrier ?R" unfolding DirProds_def by fastforce
    show "?g \<in> carrier ?R \<rightarrow> carrier ?L" unfolding DirProds_def by fastforce
    show "?f (?g x) = x" if "x \<in> carrier ?R" for x
      using that unfolding DirProds_def PiE_def Pi_def extensional_def by auto
    show "?g (?f x) = x" if "x \<in> carrier ?L" for x
      using that unfolding DirProds_def PiE_def Pi_def extensional_def by force
  qed
qed

no_notation integer_mod_group ("Z")

end
