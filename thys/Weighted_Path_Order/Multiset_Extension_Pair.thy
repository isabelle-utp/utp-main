section \<open>Multiset extension of an order pair\<close>

text \<open>Given a well-founded order $\prec$ and a compatible non-strict order $\precsim$,
  we define the corresponding multiset-extension of these orders.\<close>

theory Multiset_Extension_Pair
  imports 
    "HOL-Library.Multiset" 
    "Regular-Sets.Regexp_Method"
    "Abstract-Rewriting.Abstract_Rewriting" 
    Relations
begin

(* Possible to generalize by assuming trans locally *)

lemma mult_locally_cancel:
  assumes "trans s " and "locally_irrefl s (X + Z)" and "locally_irrefl s (Y + Z)"
  shows "(X + Z, Y + Z) \<in> mult s \<longleftrightarrow> (X, Y) \<in> mult s" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L thus ?R using assms(2, 3)
  proof (induct Z arbitrary: X Y)
    case (add z Z)
    obtain X' Y' Z' where *: "add_mset z X + Z = Z' + X'" "add_mset z Y + Z = Z' + Y'" "Y' \<noteq> {#}"
      "\<forall>x \<in> set_mset X'. \<exists>y \<in> set_mset Y'. (x, y) \<in> s"
      using mult_implies_one_step[OF \<open>trans s\<close> add(2)] by auto
    consider Z2 where "Z' = add_mset z Z2" | X2 Y2 where "X' = add_mset z X2" "Y' = add_mset z Y2"
      using *(1,2) by (metis add_mset_remove_trivial_If insert_iff set_mset_add_mset_insert union_iff)
    thus ?case
    proof (cases)
      case 1 thus ?thesis using * one_step_implies_mult[of Y' X' s Z2] 
        by (auto simp: add.commute[of _ "{#_#}"] add.assoc intro: add(1))
          (metis add.hyps add.prems(2) add.prems(3) add_mset_add_single li_trans_l union_mset_add_mset_right) 
    next
      case 2 then obtain y where "y \<in> set_mset Y2" "(z, y) \<in> s" using *(4) add(3, 4)
        by (auto simp: locally_irrefl_def)
      moreover from this transD[OF \<open>trans s\<close> _ this(2)]
      have "x' \<in> set_mset X2 \<Longrightarrow> \<exists>y \<in> set_mset Y2. (x', y) \<in> s" for x'
        using 2 *(4)[rule_format, of x'] by auto
      ultimately show ?thesis using  * one_step_implies_mult[of Y2 X2 s Z'] 2 add(3, 4)
        by (force simp: locally_irrefl_def add.commute[of "{#_#}"] add.assoc[symmetric] intro: add(1))
    qed
  qed auto
next
  assume ?R then obtain I J K
    where "Y = I + J" "X = I + K" "J \<noteq> {#}" "\<forall>k \<in> set_mset K. \<exists>j \<in> set_mset J. (k, j) \<in> s"
    using mult_implies_one_step[OF \<open>trans s\<close>] by blast
  thus ?L using one_step_implies_mult[of J K s "I + Z"] by (auto simp: ac_simps)
qed

lemma mult_locally_cancelL:
  assumes "trans s" "locally_irrefl s (X + Z)" "locally_irrefl s (Y + Z)"
  shows "(Z + X, Z + Y) \<in> mult s \<longleftrightarrow> (X, Y) \<in> mult s"
  using mult_locally_cancel[OF assms] by (simp only: union_commute)

lemma mult_cancelL:
  assumes "trans s" "irrefl s" shows "(Z + X, Z + Y) \<in> mult s \<longleftrightarrow> (X, Y) \<in> mult s"
  using assms mult_locally_cancelL by (simp add: mult_cancel union_commute) 

lemma wf_trancl_conv:
  shows "wf (r\<^sup>+) \<longleftrightarrow> wf r"
  using wf_subset[of "r\<^sup>+" r] by (force simp: wf_trancl)

subsection \<open>Pointwise multiset order\<close>

inductive_set multpw :: "'a rel \<Rightarrow> 'a multiset rel" for ns :: "'a rel" where
  empty: "({#}, {#}) \<in> multpw ns"
| add: "(x, y) \<in> ns \<Longrightarrow> (X, Y) \<in> multpw ns \<Longrightarrow> (add_mset x X, add_mset y Y) \<in> multpw ns"

lemma multpw_emptyL [simp]:
  "({#}, X) \<in> multpw ns \<longleftrightarrow> X = {#}"
  by (cases X) (auto elim: multpw.cases intro: multpw.intros)

lemma multpw_emptyR [simp]:
  "(X, {#}) \<in> multpw ns \<longleftrightarrow> X = {#}"
  by (cases X) (auto elim: multpw.cases intro: multpw.intros)

lemma refl_multpw:
  assumes "refl ns" shows "refl (multpw ns)"
proof -
  have "(X, X) \<in> multpw ns" for X using assms
    by (induct X) (auto intro: multpw.intros simp: refl_on_def)
  then show ?thesis by (auto simp: refl_on_def)
qed

lemma multpw_Id_Id [simp]:
  "multpw Id = Id"
proof -
  have "(X, Y) \<in> multpw (Id :: 'a rel) \<Longrightarrow> X = Y" for X Y by (induct X Y rule: multpw.induct) auto
  then show ?thesis using refl_multpw[of Id] by (auto simp: refl_on_def)
qed

lemma mono_multpw:
  assumes "ns \<subseteq> ns'" shows "multpw ns \<subseteq> multpw ns'"
proof -
  have "(X, Y) \<in> multpw ns \<Longrightarrow> (X, Y) \<in> multpw ns'" for X Y
    by (induct X Y rule: multpw.induct) (insert assms, auto intro: multpw.intros)
  then show ?thesis by auto
qed

lemma multpw_converse:
  "multpw (ns\<inverse>) = (multpw ns)\<inverse>"
proof -
  have "(X, Y) \<in> multpw (ns\<inverse>) \<Longrightarrow> (X, Y) \<in> (multpw ns)\<inverse>" for X Y and ns :: "'a rel"
    by (induct X Y rule: multpw.induct) (auto intro: multpw.intros)
  then show ?thesis by auto
qed

lemma multpw_local:
  "(X, Y) \<in> multpw ns \<Longrightarrow> (X, Y) \<in> multpw (ns \<inter> set_mset X \<times> set_mset Y)"
proof (induct X Y rule: multpw.induct)
  case (add x y X Y) then show ?case
    using mono_multpw[of "ns \<inter> set_mset X \<times> set_mset Y" "ns \<inter> insert x (set_mset X) \<times> insert y (set_mset Y)"]
    by (auto intro: multpw.intros)
qed auto

lemma multpw_split1R:
  assumes "(add_mset x X, Y) \<in> multpw ns"
  obtains z Z where "Y = add_mset z Z" and "(x, z) \<in> ns" and "(X, Z) \<in> multpw ns"
  using assms
proof (induct  "add_mset x X" Y arbitrary: X thesis rule: multpw.induct)
  case (add x' y' X' Y') then show ?case
  proof (cases "x = x'")
    case False
    obtain X'' where [simp]: "X = add_mset x' X''"
      using add(4) False
      by (metis add_eq_conv_diff)
    have "X' = add_mset x X''" using add(4) by (auto simp: add_eq_conv_ex)
    with add(2) obtain Y'' y where "Y' = add_mset y Y''" "(x,y) \<in> ns" "(X'', Y'') \<in> multpw ns"
      by (auto intro: add(3))
    then show ?thesis using add(1) add(5)[of y "add_mset y' Y''"]
      by (auto simp: ac_simps intro: multpw.intros)
  qed auto
qed auto

lemma multpw_splitR:
  assumes "(X1 + X2, Y) \<in> multpw ns"
  obtains Y1 Y2 where "Y = Y1 + Y2" and "(X1, Y1) \<in> multpw ns" and "(X2, Y2) \<in> multpw ns"
  using assms
proof (induct X2 arbitrary: Y thesis)
  case (add x2 X2)
  from add(3) obtain Y' y2 where "(X1 + X2, Y') \<in> multpw ns" "(x2, y2) \<in> ns" "Y = add_mset y2 Y'"
    by (auto elim: multpw_split1R simp: union_assoc[symmetric])
  moreover then obtain Y1 Y2 where "(X1, Y1) \<in> multpw ns" "(X2, Y2) \<in> multpw ns" "Y' = Y1 + Y2"
    by (auto elim: add(1)[rotated])
  ultimately show ?case by (intro add(2)) (auto simp: union_assoc intro: multpw.intros)
qed auto

lemma multpw_split1L:
  assumes "(X, add_mset y Y) \<in> multpw ns"
  obtains z Z where "X = add_mset z Z" and "(z, y) \<in> ns" and "(Z, Y) \<in> multpw ns"
  using assms multpw_split1R[of y Y X "ns\<inverse>" thesis] by (auto simp: multpw_converse)

lemma multpw_splitL:
  assumes "(X, Y1 + Y2) \<in> multpw ns"
  obtains X1 X2 where "X = X1 + X2" and "(X1, Y1) \<in> multpw ns" and "(X2, Y2) \<in> multpw ns"
  using assms multpw_splitR[of Y1 Y2 X "ns\<inverse>" thesis] by (auto simp: multpw_converse)

lemma locally_trans_multpw:
  assumes "locally_trans ns S T U"
    and "(S, T) \<in> multpw ns"
    and "(T, U) \<in> multpw ns"
  shows "(S, U) \<in> multpw ns"
  using assms(2,3,1)
proof (induct S T arbitrary: U rule: multpw.induct)
  case (add x y X Y)
  then show ?case unfolding locally_trans_def
    by (auto 0 3 intro: multpw.intros elim: multpw_split1R)
qed blast

lemma trans_multpw:
  assumes "trans ns" shows "trans (multpw ns)"
  using locally_trans_multpw unfolding locally_trans_def trans_def
  by (meson assms locally_trans_multpw tr_ltr)

lemma multpw_add:
  assumes "(X1, Y1) \<in> multpw ns" "(X2, Y2) \<in> multpw ns" shows "(X1 + X2, Y1 + Y2) \<in> multpw ns"
  using assms(2,1)
  by (induct X2 Y2 rule: multpw.induct) (auto intro: multpw.intros simp: add.assoc[symmetric])

lemma multpw_single:
  "(x, y) \<in> ns \<Longrightarrow> ({#x#}, {#y#}) \<in> multpw ns"
  using multpw.intros(2)[OF _ multpw.intros(1)] .

lemma multpw_mult1_commute:
  assumes compat: "s O ns \<subseteq> s" and reflns: "refl ns"
  shows "mult1 s O multpw ns \<subseteq> multpw ns O mult1 s"
proof -
  { fix X Y Z assume 1: "(X, Y) \<in> mult1 s" "(Y, Z) \<in> multpw ns"
    then obtain X' Y' y where 2: "X = Y' + X'" "Y = add_mset y Y'" "\<forall>x. x \<in># X' \<longrightarrow> (x, y) \<in> s"
      by (auto simp: mult1_def)
    moreover obtain Z' z where 3: "Z = add_mset z Z'" "(y, z) \<in> ns" "(Y', Z') \<in> multpw ns"
      using 1(2) 2(2) by (auto elim: multpw_split1R)
    moreover have "\<forall>x. x \<in># X' \<longrightarrow> (x, z) \<in> s" using 2(3) 3(2) compat by blast
    ultimately have "\<exists>Y'. (X, Y') \<in> multpw ns \<and> (Y', Z) \<in> mult1 s" unfolding mult1_def
      using refl_multpw[OF reflns]
      by (intro exI[of _ "Z' + X'"]) (auto intro: multpw_add simp: refl_on_def)
  }
  then show ?thesis by fast
qed

lemma multpw_mult_commute:
  assumes "s O ns \<subseteq> s" "refl ns" shows "mult s O multpw ns \<subseteq> multpw ns O mult s"
proof -
  { fix X Y Z assume 1: "(X, Y) \<in> mult s" "(Y, Z) \<in> multpw ns"
    then have "\<exists>Y'. (X, Y') \<in> multpw ns \<and> (Y', Z) \<in> mult s" unfolding mult_def
      using multpw_mult1_commute[OF assms] by (induct rule: converse_trancl_induct) (auto 0 3)
  }
  then show ?thesis by fast
qed

lemma wf_mult_rel_multpw:
  assumes "wf s" "s O ns \<subseteq> s" "refl ns" shows "wf ((multpw ns)\<^sup>* O mult s O (multpw ns)\<^sup>*)"
  using assms(1) multpw_mult_commute[OF assms(2,3)] by (subst qc_wf_relto_iff) (auto simp: wf_mult)

lemma multpw_cancel1:
  assumes "trans ns" "(y, x) \<in> ns"
  shows "(add_mset x X, add_mset y Y) \<in> multpw ns \<Longrightarrow> (X, Y) \<in> multpw ns" (is "?L \<Longrightarrow> ?R")
proof -
  assume ?L then obtain x' X' where X: "(x', y) \<in> ns" "add_mset x' X' = add_mset x X" "(X', Y) \<in> multpw ns"
    by (auto elim: multpw_split1L simp: union_assoc[symmetric])
  then show ?R
  proof (cases "x = x'")
    case False then obtain X2 where X2: "X' = add_mset x X2" "X = add_mset x' X2"
      using X(2) by (auto simp: add_eq_conv_ex)
    then obtain y' Y' where Y: "(x, y') \<in> ns" "Y = add_mset y' Y'" "(X2, Y') \<in> multpw ns"
      using X(3) by (auto elim: multpw_split1R)
    have "(x', y') \<in> ns" using X(1) Y(1) \<open>trans ns\<close> assms(2) by (metis trans_def)
    then show ?thesis using Y by (auto intro: multpw.intros simp: X2)
  qed auto
qed

lemma multpw_cancel:
  assumes "refl ns" "trans ns"
  shows "(X + Z, Y + Z) \<in> multpw ns \<longleftrightarrow> (X, Y) \<in> multpw ns" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L then show ?R
  proof (induct Z)
    case (add z Z) then show ?case using multpw_cancel1[of ns z z "X + Z" "Y + Z"] assms
      by (auto simp: refl_on_def union_assoc)
  qed auto
next
  assume ?R then show ?L using assms refl_multpw by (auto intro: multpw_add simp: refl_on_def)
qed

lemma multpw_cancelL:
  assumes "refl ns" "trans ns" shows "(Z + X, Z + Y) \<in> multpw ns \<longleftrightarrow> (X, Y) \<in> multpw ns"
  using multpw_cancel[OF assms, of X Z Y] by (simp only: union_commute)

subsection \<open>Multiset extension for order pairs via the pointwise order and @{const mult}\<close>

definition "mult2_s ns s \<equiv> multpw ns O mult s"
definition "mult2_ns ns s \<equiv> multpw ns O (mult s)\<^sup>="

lemma mult2_ns_conv:
  shows "mult2_ns ns s = mult2_s ns s \<union> multpw ns"
  by (auto simp: mult2_s_def mult2_ns_def)

lemma mono_mult2_s:
  assumes "ns \<subseteq> ns'" "s \<subseteq> s'" shows "mult2_s ns s \<subseteq> mult2_s ns' s'"
  using mono_multpw[OF assms(1)] mono_mult[OF assms(2)] unfolding mult2_s_def by auto

lemma mono_mult2_ns:
  assumes "ns \<subseteq> ns'" "s \<subseteq> s'" shows "mult2_ns ns s \<subseteq> mult2_ns ns' s'"
  using mono_multpw[OF assms(1)] mono_mult[OF assms(2)] unfolding mult2_ns_def by auto

lemma wf_mult2_s:
  assumes "wf s" "s O ns \<subseteq> s" "refl ns"
  shows "wf (mult2_s ns s)"
  using wf_mult_rel_multpw[OF assms] assms by (auto simp: mult2_s_def wf_mult intro: wf_subset)

lemma refl_mult2_ns:
  assumes "refl ns" shows "refl (mult2_ns ns s)"
  using refl_multpw[OF assms] unfolding mult2_ns_def refl_on_def by fast

lemma trans_mult2_s:
  assumes "s O ns \<subseteq> s" "refl ns" "trans ns"
  shows "trans (mult2_s ns s)"
  using trans_multpw[OF assms(3)] trans_trancl[of "mult1 s", folded mult_def] multpw_mult_commute[OF assms(1,2)]
  unfolding mult2_s_def trans_O_iff by (blast 8)

lemma trans_mult2_ns:
  assumes "s O ns \<subseteq> s" "refl ns" "trans ns"
  shows "trans (mult2_ns ns s)"
  using trans_multpw[OF assms(3)] trans_trancl[of "mult1 s", folded mult_def] multpw_mult_commute[OF assms(1,2)]
  unfolding mult2_ns_def trans_O_iff by (blast 8)

lemma compat_mult2:
  assumes "s O ns \<subseteq> s" "refl ns" "trans ns"
  shows "mult2_ns ns s O mult2_s ns s \<subseteq> mult2_s ns s" "mult2_s ns s O mult2_ns ns s \<subseteq> mult2_s ns s"
  using trans_multpw[OF assms(3)] trans_trancl[of "mult1 s", folded mult_def] multpw_mult_commute[OF assms(1,2)]
  unfolding mult2_s_def mult2_ns_def trans_O_iff by (blast 8)+

text \<open>Trivial inclusions\<close>

lemma mult_implies_mult2_s:
  assumes "refl ns" "(X, Y) \<in> mult s"
  shows "(X, Y) \<in> mult2_s ns s"
  using refl_multpw[of ns] assms unfolding mult2_s_def refl_on_def by blast

lemma mult_implies_mult2_ns:
  assumes "refl ns" "(X, Y) \<in> (mult s)\<^sup>="
  shows "(X, Y) \<in> mult2_ns ns s"
  using refl_multpw[of ns] assms unfolding mult2_ns_def refl_on_def by blast

lemma multpw_implies_mult2_ns:
  assumes "(X, Y) \<in> multpw ns"
  shows "(X, Y) \<in> mult2_ns ns s"
  unfolding mult2_ns_def using assms by simp

subsection \<open>One-step versions of the multiset extensions\<close>

lemma mult2_s_one_step:
  assumes "ns O s \<subseteq> s" "refl ns" "trans s"
  shows "(X, Y) \<in> mult2_s ns s \<longleftrightarrow> (\<exists>X1 X2 Y1 Y2. X = X1 + X2 \<and> Y = Y1 + Y2 \<and>
    (X1, Y1) \<in> multpw ns \<and> Y2 \<noteq> {#} \<and> (\<forall>x. x \<in># X2 \<longrightarrow> (\<exists>y. y \<in># Y2 \<and> (x, y) \<in> s)))" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?R then obtain X1 X2 Y1 Y2 where *: "X = X1 + X2" "Y = Y1 + Y2" "(X1, Y1) \<in> multpw ns" and
    "Y2 \<noteq> {#}" "\<forall>x. x \<in># X2 \<longrightarrow> (\<exists>y. y \<in># Y2 \<and> (x, y) \<in> s)" by blast
  then have "(Y1 + X2, Y1 + Y2) \<in> mult s"
    using \<open>trans s\<close> by (auto intro: one_step_implies_mult)
  moreover have "(X1 + X2, Y1 + X2) \<in> multpw ns"
    using \<open>refl ns\<close> refl_multpw[of ns] by (auto intro: multpw_add simp: refl_on_def *)
  ultimately show ?L by (auto simp: mult2_s_def *)
next
  assume ?L then obtain X1 X2 Z1 Z2 Y2 where *: "X = X1 + X2" "Y = Z1 + Y2" "(X1, Z1) \<in> multpw ns"
    "(X2, Z2) \<in> multpw ns" "Y2 \<noteq> {#}" "\<forall>x. x \<in># Z2 \<longrightarrow> (\<exists>y. y \<in># Y2 \<and> (x, y) \<in> s)"
    by (auto 0 3 dest!: mult_implies_one_step[OF \<open>trans s\<close>] simp: mult2_s_def elim!: multpw_splitL) metis
  have "\<forall>x. x \<in># X2 \<longrightarrow> (\<exists>y. y \<in># Y2 \<and> (x,y) \<in> s)"
  proof (intro allI impI)
    fix x assume "x \<in># X2"
    then obtain X2' where "X2 = add_mset x X2'" by (metis multi_member_split)
    then obtain z Z2' where "Z2 = add_mset z Z2'" "(x, z) \<in> ns" using *(4) by (auto elim: multpw_split1R)
    then have "z \<in># Z2" "(x, z) \<in> ns" by auto
    then show "\<exists>y. y \<in># Y2 \<and> (x,y) \<in> s" using *(6) \<open>ns O s \<subseteq> s\<close> by blast
  qed
  then show ?R using * by auto
qed

lemma mult2_ns_one_step:
  assumes "ns O s \<subseteq> s" "refl ns" "trans s"
  shows "(X, Y) \<in> mult2_ns ns s \<longleftrightarrow> (\<exists>X1 X2 Y1 Y2. X = X1 + X2 \<and> Y = Y1 + Y2 \<and>
    (X1, Y1) \<in> multpw ns \<and> (\<forall>x. x \<in># X2 \<longrightarrow> (\<exists>y. y \<in># Y2 \<and> (x, y) \<in> s)))" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L then consider "(X, Y) \<in> multpw ns" | "(X, Y) \<in> mult2_s ns s"
    by (auto simp: mult2_s_def mult2_ns_def)
  then show ?R using mult2_s_one_step[OF assms]
    by (cases, intro exI[of _ "{#}", THEN exI[of _ Y, THEN exI[of _ "{#}", THEN exI[of _ X]]]]) auto
next
  assume ?R then obtain X1 X2 Y1 Y2 where "X = X1 + X2" "Y = Y1 + Y2"
    "(X1, Y1) \<in> multpw ns" "\<forall>x. x \<in># X2 \<longrightarrow> (\<exists>y. y \<in># Y2 \<and> (x, y) \<in> s)" by blast
  then show ?L using mult2_s_one_step[OF assms, of X Y] count_inject[of X2 "{#}"]
    by (cases "Y2 = {#}") (auto simp: mult2_s_def mult2_ns_def)
qed

lemma mult2_s_locally_one_step':
  assumes "ns O s \<subseteq> s" "refl ns" "locally_irrefl s X" "locally_irrefl s Y" "trans s"
  shows "(X, Y) \<in> mult2_s ns s \<longleftrightarrow> (\<exists>X1 X2 Y1 Y2. X = X1 + X2 \<and> Y = Y1 + Y2 \<and>
    (X1, Y1) \<in> multpw ns \<and> (X2, Y2) \<in> mult s)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L then show ?R unfolding mult2_s_one_step[OF assms(1,2,5)]
    using one_step_implies_mult[of _ _ s "{#}"] by auto metis
next
  assume ?R then obtain X1 X2 Y1 Y2 where x: "X = X1 + X2" and y: "Y = Y1 + Y2" and
    ns: "(X1, Y1) \<in> multpw ns" and s: "(X2, Y2) \<in> mult s" by blast
  then have l: "locally_irrefl s (X2 + Y1)" and r: "locally_irrefl s (Y2 + Y1)"
    using assms(3, 4) by (auto simp add: locally_irrefl_def)
  show ?L using ns s mult_locally_cancelL[OF assms(5) l r] multpw_add[OF ns, of X2 X2] refl_multpw[OF \<open>refl ns\<close>]
    unfolding mult2_s_def refl_on_def x y by auto
qed

lemma mult2_s_one_step':
  assumes "ns O s \<subseteq> s" "refl ns" "irrefl s" "trans s"
  shows "(X, Y) \<in> mult2_s ns s \<longleftrightarrow> (\<exists>X1 X2 Y1 Y2. X = X1 + X2 \<and> Y = Y1 + Y2 \<and>
    (X1, Y1) \<in> multpw ns \<and> (X2, Y2) \<in> mult s)" (is "?L \<longleftrightarrow> ?R")
  using assms mult2_s_locally_one_step' by (simp add: mult2_s_locally_one_step' irrefl_def locally_irrefl_def) 

lemma mult2_ns_one_step':
  assumes "ns O s \<subseteq> s" "refl ns" "irrefl s" "trans s"
  shows "(X, Y) \<in> mult2_ns ns s \<longleftrightarrow> (\<exists>X1 X2 Y1 Y2. X = X1 + X2 \<and> Y = Y1 + Y2 \<and>
    (X1, Y1) \<in> multpw ns \<and> (X2, Y2) \<in> (mult s)\<^sup>=)" (is "?L \<longleftrightarrow> ?R")
proof -
  have "(X, Y) \<in> multpw ns \<Longrightarrow> ?R"
    by (intro exI[of _ "{#}", THEN exI[of _ Y, THEN exI[of _ "{#}", THEN exI[of _ X]]]]) auto
  moreover have "X = X1 + Y2 \<and> Y = Y1 + Y2 \<and> (X1, Y1) \<in> multpw ns \<Longrightarrow> ?L" for X1 Y1 Y2
    using multpw_add[of X1 Y1 ns Y2 Y2] refl_multpw[OF \<open>refl ns\<close>] by (auto simp: mult2_ns_def refl_on_def)
  ultimately show ?thesis using mult2_s_one_step'[OF assms] unfolding mult2_ns_conv
    by auto blast
qed

subsection \<open>Cancellation\<close>

lemma mult2_s_locally_cancel1:
  assumes "s O ns \<subseteq> s" "ns O s \<subseteq> s" "refl ns" "trans ns" "locally_irrefl s (add_mset z X)" "locally_irrefl s (add_mset z Y)" "trans s"
    "(add_mset z X, add_mset z Y) \<in> mult2_s ns s"
  shows "(X, Y) \<in> mult2_s ns s"
proof -
  obtain X1 X2 Y1 Y2 where *: "add_mset z X = X1 + X2" "add_mset z Y = Y1 + Y2" "(X1, Y1) \<in> multpw ns"
    "(X2, Y2) \<in> mult s" using assms(8) unfolding mult2_s_locally_one_step'[OF assms(2,3,5,6,7)] by blast    
  from union_single_eq_member[OF this(1)] union_single_eq_member[OF this(2)] multi_member_split
  consider X1' where "X1 = add_mset z X1'" | Y1' where "Y1 = add_mset z Y1'"
    | X2' Y2' where "X2 = add_mset z X2'" "Y2 = add_mset z Y2'"
    unfolding set_mset_union Un_iff by metis
  then show ?thesis
  proof (cases)
    case 1 then obtain Y1' z' where **: "(X1', Y1') \<in> multpw ns" "Y1 = add_mset z' Y1'" "(z, z') \<in> ns"
      using * by (auto elim: multpw_split1R)
    then have "(X, Y1' + Y2) \<in> mult2_s ns s" using * 1
      by auto (metis add_mset_add_single assms(2 - 7) li_trans_l mult2_s_locally_one_step') 
    moreover
    have "(Y1' + Y2, Y) \<in> multpw ns"
      using refl_multpw[OF \<open>refl ns\<close>] * ** multpw_cancel1[OF \<open>trans ns\<close> **(3), of "Y1' + Y2" Y]
      by (auto simp: refl_on_def)
    ultimately show ?thesis using compat_mult2[OF assms(1,3,4)] unfolding mult2_ns_conv by blast
  next
    case 2 then obtain X1' z' where **: "(X1', Y1') \<in> multpw ns" "X1 = add_mset z' X1'" "(z', z) \<in> ns"
      using * by (auto elim: multpw_split1L)
    then have "(X1' + X2, Y) \<in> mult2_s ns s" using * 2
      by auto (metis add_mset_add_single assms(2 - 7) li_trans_l mult2_s_locally_one_step')
    moreover
    have "(X, X1' + X2) \<in> multpw ns"
      using refl_multpw[OF \<open>refl ns\<close>] * ** multpw_cancel1[OF \<open>trans ns\<close> **(3), of X "X1' + X2"]
      by (auto simp: refl_on_def)
    ultimately show ?thesis using compat_mult2[OF assms(1,3,4)] unfolding mult2_ns_conv by blast
  next
    case 3 then show ?thesis using assms *
      by (auto simp: mult2_s_locally_one_step' union_commute[of "{#_#}"] union_assoc[symmetric] mult_cancel mult_cancel_add_mset)
        (metis "*"(1) "*"(2) add_mset_add_single li_trans_l li_trans_r mult2_s_locally_one_step' mult_locally_cancel)
  qed
qed

lemma mult2_s_cancel1:
  assumes "s O ns \<subseteq> s" "ns O s \<subseteq> s" "refl ns" "trans ns" "irrefl s" "trans s" "(add_mset z X, add_mset z Y) \<in> mult2_s ns s"
  shows "(X, Y) \<in> mult2_s ns s"
  using assms mult2_s_locally_cancel1 by (metis irrefl_def locally_irrefl_def) 

lemma mult2_s_locally_cancel:
  assumes "s O ns \<subseteq> s" "ns O s \<subseteq> s" "refl ns" "trans ns" "locally_irrefl s (X + Z)" "locally_irrefl s (Y + Z)" "trans s"
  shows "(X + Z, Y + Z) \<in> mult2_s ns s \<Longrightarrow> (X, Y) \<in> mult2_s ns s"
  using assms(5, 6)
proof (induct Z)
  case (add z Z) then show ?case
    using mult2_s_locally_cancel1[OF assms(1-4), of z "X + Z" "Y + Z"] 
    by auto (metis add_mset_add_single assms(7) li_trans_l) 
qed auto

lemma mult2_s_cancel:
  assumes "s O ns \<subseteq> s" "ns O s \<subseteq> s" "refl ns" "trans ns" "irrefl s" "trans s"
  shows "(X + Z, Y + Z) \<in> mult2_s ns s \<Longrightarrow> (X, Y) \<in> mult2_s ns s"
  using mult2_s_locally_cancel assms by (metis irrefl_def locally_irrefl_def) 

lemma mult2_ns_cancel:
  assumes "s O ns \<subseteq> s" "ns O s \<subseteq> s" "refl ns" "trans s" "irrefl s" "trans ns"
  shows "(X + Z, Y + Z) \<in> mult2_s ns s \<Longrightarrow> (X, Y) \<in> mult2_ns ns s"
  unfolding mult2_ns_conv using assms mult2_s_cancel multpw_cancel by blast

subsection \<open>Implementation friendly versions of @{const mult2_s} and @{const mult2_ns}\<close>

definition mult2_alt :: "bool \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a multiset rel" where
  "mult2_alt b ns s = {(X, Y). (\<exists>X1 X2 Y1 Y2. X = X1 + X2 \<and> Y = Y1 + Y2 \<and>
    (X1, Y1) \<in> multpw ns \<and> (b \<or> Y2 \<noteq> {#}) \<and> (\<forall>x. x \<in># X2 \<longrightarrow> (\<exists>y. y \<in># Y2 \<and> (x, y) \<in> s)))}"

lemma mult2_altI:
  assumes "X = X1 + X2" "Y = Y1 + Y2" "(X1, Y1) \<in> multpw ns"
    "b \<or> Y2 \<noteq> {#}" "\<forall>x. x \<in># X2 \<longrightarrow> (\<exists>y. y \<in># Y2 \<and> (x, y) \<in> s)"
  shows "(X, Y) \<in> mult2_alt b ns s"
  using assms unfolding mult2_alt_def by blast

lemma mult2_altE:
  assumes "(X, Y) \<in> mult2_alt b ns s"
  obtains X1 X2 Y1 Y2 where "X = X1 + X2" "Y = Y1 + Y2" "(X1, Y1) \<in> multpw ns"
    "b \<or> Y2 \<noteq> {#}" "\<forall>x. x \<in># X2 \<longrightarrow> (\<exists>y. y \<in># Y2 \<and> (x, y) \<in> s)"
  using assms unfolding mult2_alt_def by blast

lemma mono_mult2_alt:
  assumes "ns \<subseteq> ns'" "s \<subseteq> s'" shows "mult2_alt b ns s \<subseteq> mult2_alt b ns' s'"
  unfolding mult2_alt_def using mono_multpw[OF assms(1)] assms by (blast 19)

abbreviation "mult2_alt_s \<equiv> mult2_alt False"
abbreviation "mult2_alt_ns \<equiv> mult2_alt True"

lemmas mult2_alt_s_def = mult2_alt_def[where b = False, unfolded simp_thms]
lemmas mult2_alt_ns_def = mult2_alt_def[where b = True, unfolded simp_thms]
lemmas mult2_alt_sI = mult2_altI[where b = False, unfolded simp_thms]
lemmas mult2_alt_nsI = mult2_altI[where b = True, unfolded simp_thms True_implies_equals]
lemmas mult2_alt_sE = mult2_altE[where b = False, unfolded simp_thms]
lemmas mult2_alt_nsE = mult2_altE[where b = True, unfolded simp_thms True_implies_equals]

paragraph \<open>Equivalence to @{const mult2_s} and @{const mult2_ns}\<close>

lemma mult2_s_eq_mult2_s_alt:
  assumes "ns O s \<subseteq> s" "refl ns" "trans s"
  shows "mult2_alt_s ns s = mult2_s ns s"
  using mult2_s_one_step[OF assms] unfolding mult2_alt_s_def by blast

lemma mult2_ns_eq_mult2_ns_alt:
  assumes "ns O s \<subseteq> s" "refl ns" "trans s"
  shows "mult2_alt_ns ns s = mult2_ns ns s"
  using mult2_ns_one_step[OF assms] unfolding mult2_alt_ns_def by blast

lemma mult2_alt_local:
  assumes "(X, Y) \<in> mult2_alt b ns s"
  shows "(X, Y) \<in> mult2_alt b (ns \<inter> set_mset X \<times> set_mset Y) (s \<inter> set_mset X \<times> set_mset Y)"
proof -
  from assms obtain X1 X2 Y1 Y2 where *: "X = X1 + X2" "Y = Y1 + Y2" and
    "(X1, Y1) \<in> multpw ns" "(b \<or> Y2 \<noteq> {#})" "(\<forall>x. x \<in># X2 \<longrightarrow> (\<exists>y. y \<in># Y2 \<and> (x, y) \<in> s))"
    unfolding mult2_alt_def by blast
  then have "X = X1 + X2 \<and> Y = Y1 + Y2 \<and>
    (X1, Y1) \<in> multpw (ns \<inter> set_mset X \<times> set_mset Y) \<and> (b \<or> Y2 \<noteq> {#}) \<and>
    (\<forall>x. x \<in># X2 \<longrightarrow> (\<exists>y. y \<in># Y2 \<and> (x, y) \<in> s \<inter> set_mset X \<times> set_mset Y))"
    using multpw_local[of X1 Y1 ns]
      mono_multpw[of "ns \<inter> set_mset X1 \<times> set_mset Y1" "ns \<inter> set_mset X \<times> set_mset Y"] assms
    unfolding * set_mset_union unfolding set_mset_def by blast
  then show ?thesis unfolding mult2_alt_def by blast
qed

subsection \<open>Local well-foundedness: restriction to downward closure of a set\<close>

definition wf_below :: "'a rel \<Rightarrow> 'a set \<Rightarrow> bool" where
  "wf_below r A = wf (Restr r ((r\<^sup>*)\<inverse> `` A))"

lemma wf_below_UNIV[simp]:
  shows "wf_below r UNIV \<longleftrightarrow> wf r"
  by (auto simp: wf_below_def rtrancl_converse[symmetric] Image_closed_trancl[OF subset_UNIV])

lemma wf_below_mono1:
  assumes "r \<subseteq> r'" "wf_below r' A" shows "wf_below r A"
  using assms unfolding wf_below_def
  by (intro wf_subset[OF assms(2)[unfolded wf_below_def]] Int_mono Sigma_mono Image_mono
      iffD2[OF converse_mono] rtrancl_mono subset_refl)

lemma wf_below_mono2:
  assumes "A \<subseteq> A'" "wf_below r A'" shows "wf_below r A"
  using assms unfolding wf_below_def
  by (intro wf_subset[OF assms(2)[unfolded wf_below_def]]) blast

lemma wf_below_pointwise:
  "wf_below r A \<longleftrightarrow> (\<forall>a. a \<in> A \<longrightarrow> wf_below r {a})" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L then show ?R using wf_below_mono2[of "{_}" A r] by blast
next
  have *: "(r\<^sup>*)\<inverse> `` A = \<Union>{(r\<^sup>*)\<inverse> `` {a} |a. a \<in> A}" unfolding Image_def by blast
  assume ?R
  { fix x X assume *: "X \<subseteq> Restr r ((r\<^sup>*)\<inverse> `` A) `` X" "x \<in> X"
    then obtain a where **: "a \<in> A" "(x, a) \<in> r\<^sup>*" unfolding Image_def by blast
    from * have "X \<inter> ((r\<^sup>*)\<inverse> `` {a}) \<subseteq> (Restr r ((r\<^sup>*)\<inverse> `` A) `` X) \<inter> ((r\<^sup>*)\<inverse> `` {a})" by auto
    also have "... \<subseteq> Restr r ((r\<^sup>*)\<inverse> `` {a}) `` (X  \<inter> ((r\<^sup>*)\<inverse> `` {a}))" unfolding Image_def by fastforce
    finally have "X \<inter> ((r\<^sup>*)\<inverse> `` {a}) = {}" using \<open>?R\<close> **(1) unfolding wf_below_def
      by (intro wfE_pf[of "Restr r ((r\<^sup>*)\<inverse> `` {a})"]) (auto simp: Image_def)
    then have False using *(2) ** unfolding Image_def by blast
  }
  then show ?L unfolding wf_below_def by (intro wfI_pf) auto
qed

lemma SN_on_Image_rtrancl_conv:
  "SN_on r A \<longleftrightarrow> SN_on r (r\<^sup>* `` A)" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L then show ?R by (auto simp: SN_on_Image_rtrancl)
next
  assume ?R then show ?L by (auto simp: SN_on_def)
qed

lemma SN_on_iff_wf_below:
  "SN_on r A \<longleftrightarrow> wf_below (r\<inverse>) A"
proof -
  { fix f
    assume "f 0 \<in> r\<^sup>* `` A" and **: "(f i, f (Suc i)) \<in> r" for i
    then have "f i \<in> r\<^sup>* `` A" for i
      by (induct i) (auto simp: Image_def, metis UnCI relcomp.relcompI rtrancl_unfold)
    then have "(f i, f (Suc i)) \<in> Restr r (r\<^sup>* `` A)" for i using ** by auto
  }
  moreover then have "SN_on r (r\<^sup>* `` A) \<longleftrightarrow> SN_on (Restr r (r\<^sup>* `` A)) (r\<^sup>* `` A)"
    unfolding SN_on_def by auto blast
  moreover have "(\<And>i. (f i, f (Suc i)) \<in> Restr r (r\<^sup>* `` A)) \<Longrightarrow> f 0 \<in> r\<^sup>* `` A" for f by auto
  then have "SN_on (Restr r (r\<^sup>* `` A)) (r\<^sup>* `` A) \<longleftrightarrow> SN_on (Restr r (r\<^sup>* `` A)) UNIV"
    unfolding SN_on_def by auto
  ultimately show ?thesis  unfolding SN_on_Image_rtrancl_conv [of _ A]
    by (simp add: wf_below_def SN_iff_wf rtrancl_converse converse_Int converse_Times)
qed


lemma restr_trancl_under:
  shows "Restr (r\<^sup>+) ((r\<^sup>*)\<inverse> `` A) = (Restr r ((r\<^sup>*)\<inverse> `` A))\<^sup>+"
proof (intro equalityI subrelI, elim IntE conjE[OF iffD1[OF mem_Sigma_iff]])
  fix a b assume *: "(a, b) \<in> r\<^sup>+" "b \<in> (r\<^sup>*)\<inverse> `` A"
  then have "(a, b) \<in> (Restr r ((r\<^sup>*)\<inverse> `` A))\<^sup>+ \<and> a \<in> (r\<^sup>*)\<inverse> `` A"
  proof (induct rule: trancl_trans_induct[consumes 1])
    case 1 then show ?case by (auto simp: Image_def intro: converse_rtrancl_into_rtrancl)
  next
    case 2 then show ?case by (auto simp del: Int_iff del: ImageE)
  qed
  then show "(a, b) \<in> (Restr r ((r\<^sup>*)\<inverse> `` A))\<^sup>+" by simp
next
  fix a b assume "(a, b) \<in> (Restr r ((r\<^sup>*)\<inverse> `` A))\<^sup>+"
  then show "(a, b) : Restr (r\<^sup>+) ((r\<^sup>*)\<inverse> `` A)" by induct auto
qed

lemma wf_below_trancl:
  shows "wf_below (r\<^sup>+) A \<longleftrightarrow> wf_below r A"
  using restr_trancl_under[of r A] by (simp add: wf_below_def wf_trancl_conv)

lemma wf_below_mult_local:
  assumes "wf_below r (set_mset X)" shows "wf_below (mult r) {X}"
    (* this is actually an equivalence; is the other direction useful as well? *)
proof -
  have foo: "mult r \<subseteq> mult (r\<^sup>+)" using mono_mult[of r "r\<^sup>+"] by force
  have "(Y, X) \<in> (mult (r\<^sup>+))\<^sup>* \<Longrightarrow> set_mset Y \<subseteq> ((r\<^sup>+)\<^sup>*)\<inverse> `` set_mset X" for Y
  proof (induct rule: converse_rtrancl_induct)
    case (step Z Y)
    obtain I J K where *: "Y = I + J" "Z = I + K" "(\<forall>k \<in> set_mset K. \<exists>j \<in> set_mset J. (k, j) \<in> r\<^sup>+)"
      using mult_implies_one_step[OF _ step(1)] by auto
    { fix k assume "k \<in># K"
      then obtain j where "j \<in># J" "(k, j) \<in> r\<^sup>+" using *(3) by auto
      moreover then obtain x where "x \<in># X" "(j, x) \<in> r\<^sup>*" using step(3) by (auto simp: *)
      ultimately have "\<exists>x. x \<in># X \<and> (k, x) \<in> r\<^sup>*" by auto
    }
    then show ?case using * step(3) by (auto simp: Image_def) metis
  qed auto
  then have q: "(Y, X) \<in> (mult (r\<^sup>+))\<^sup>* \<Longrightarrow> y \<in># Y  \<Longrightarrow> y \<in> ((r\<^sup>+)\<^sup>*)\<inverse> `` set_mset X" for Y y by force
  have "Restr (mult (r\<^sup>+)) (((mult (r\<^sup>+))\<^sup>*)\<inverse> `` {X}) \<subseteq> mult (Restr (r\<^sup>+) (((r\<^sup>+)\<^sup>*)\<inverse> `` set_mset X))"
  proof (intro subrelI)
    fix N M assume "(N, M) \<in> Restr (mult (r\<^sup>+)) (((mult (r\<^sup>+))\<^sup>*)\<inverse> `` {X})"
    then have **:  "(N, X) \<in> (mult (r\<^sup>+))\<^sup>*" "(M, X) \<in> (mult (r\<^sup>+))\<^sup>*" "(N, M) \<in> mult (r\<^sup>+)" by auto
    obtain I J K where *: "M = I + J" "N = I + K" "J \<noteq> {#}" "\<forall>k \<in> set_mset K. \<exists>j \<in> set_mset J. (k, j) \<in> r\<^sup>+"
      using mult_implies_one_step[OF _ \<open>(N, M) \<in> mult (r\<^sup>+)\<close>] by auto
    then show "(N, M) \<in> mult (Restr (r\<^sup>+) (((r\<^sup>+)\<^sup>*)\<inverse> `` set_mset X))"
      using q[OF **(1)] q[OF **(2)] unfolding * by (auto intro: one_step_implies_mult)
  qed
  note bar = subset_trans[OF Int_mono[OF foo Sigma_mono] this]
  have "((mult r)\<^sup>*)\<inverse> `` {X} \<subseteq> ((mult (r\<^sup>+))\<^sup>*)\<inverse> `` {X}" using foo by (simp add: Image_mono rtrancl_mono)
  then have "Restr (mult r) (((mult r)\<^sup>*)\<inverse> `` {X}) \<subseteq> mult (Restr (r\<^sup>+) (((r\<^sup>+)\<^sup>*)\<inverse> `` set_mset X))"
    by (intro bar) auto
  then show ?thesis using wf_mult assms wf_subset
    unfolding wf_below_trancl[of r, symmetric] unfolding wf_below_def by blast
qed

lemma qc_wf_below:
  assumes "s O ns \<subseteq> (s \<union> ns)\<^sup>* O s" "wf_below s A"
  shows "wf_below (ns\<^sup>* O s O ns\<^sup>*) A"
  unfolding wf_below_def
proof (intro wfI_pf)
  let ?A' = "((ns\<^sup>* O s O ns\<^sup>*)\<^sup>*)\<inverse> `` A"
  fix X assume X: "X \<subseteq> Restr (ns\<^sup>* O s O ns\<^sup>*) ?A' `` X"
  let ?X' = "((s \<union> ns)\<^sup>* \<inter> UNIV \<times> ((s\<^sup>*)\<inverse> `` A)) `` X"
  have *: "s O (s \<union> ns)\<^sup>* \<subseteq> (s \<union> ns)\<^sup>* O s"
  proof - (* taken from the proof of qc_wf_relto_iff *)
    { fix x y z assume "(y, z) \<in> (s \<union> ns)\<^sup>*" and "(x, y) \<in> s"
      then have "(x, z) \<in> (s \<union> ns)\<^sup>* O s"
      proof (induct y z)
        case rtrancl_refl then show ?case by auto
      next
        case (rtrancl_into_rtrancl a b c)
        then have "(x, c) \<in> ((s \<union> ns)\<^sup>* O (s \<union> ns)\<^sup>*) O s" using assms by blast
        then show ?case by simp
      qed }
    then show ?thesis by auto
  qed
  { fix x assume "x \<in> Restr (ns\<^sup>* O s O ns\<^sup>*) ?A' `` X"
    then obtain y z where **: "y \<in> X" "z \<in> A" "(y, x) \<in> ns\<^sup>* O s O ns\<^sup>*" "(x, z) \<in> (ns\<^sup>* O s O ns\<^sup>*)\<^sup>*" by blast
    have "(ns\<^sup>* O s O ns\<^sup>*) O (ns\<^sup>* O s O ns\<^sup>*)\<^sup>* \<subseteq> (s \<union> ns)\<^sup>*" by regexp 
    then have "(y, z) \<in> (s \<union> ns)\<^sup>*" using **(3,4) by blast
    moreover have "?X' = {}"
    proof (intro wfE_pf[OF assms(2)[unfolded wf_below_def]] subsetI)
      fix x assume "x \<in> ?X'"
      then have "x \<in> ((s \<union> ns)\<^sup>* \<inter> UNIV \<times> ((s\<^sup>*)\<inverse> `` A)) `` Restr (ns\<^sup>* O s O ns\<^sup>*) ?A' `` X" using X by auto
      then obtain x0 y z where **: "z \<in> X" "x0 \<in> A" "(z, y) \<in> ns\<^sup>* O s O ns\<^sup>*" "(y, x) \<in> (s \<union> ns)\<^sup>*" "(x, x0) \<in> s\<^sup>*"
        unfolding Image_def by blast
      have "(ns\<^sup>* O s O ns\<^sup>*) O (s \<union> ns)\<^sup>* \<subseteq> ns\<^sup>* O (s O (s \<union> ns)\<^sup>*)" by regexp
      with **(3,4) have "(z, x) \<in> ns\<^sup>* O (s O (s \<union> ns)\<^sup>*)" by blast
      moreover have "ns\<^sup>* O ((s \<union> ns)\<^sup>* O s) \<subseteq> (s \<union> ns)\<^sup>* O s" by regexp
      ultimately have "(z, x) \<in> (s \<union> ns)\<^sup>* O s" using * by blast
      then obtain x' where "z \<in> X" "(z, x') \<in> (s \<union> ns)\<^sup>*"  "(x', x) \<in> s" "(x', x0) \<in> s\<^sup>*" "(x, x0) \<in> s\<^sup>*" "x0 \<in> A"
        using **(1,2,5) converse_rtrancl_into_rtrancl[OF _ **(5)] by blast
      then show "x \<in> Restr s ((s\<^sup>*)\<inverse> `` A) `` ?X'"
        unfolding Image_def by blast
    qed
    ultimately have False using **(1,2) unfolding Image_def by blast 
  }
  then show "X = {}" using X by blast
qed

lemma wf_below_mult2_s_local:
  assumes "wf_below s (set_mset X)" "s O ns \<subseteq> s" "refl ns" "trans ns"
  shows "wf_below (mult2_s ns s) {X}"
  using wf_below_mult_local[of s X] assms multpw_mult_commute[of s ns]
    wf_below_mono1[of "multpw ns O mult s" "(multpw ns)\<^sup>* O mult s O (multpw ns)\<^sup>*" "{X}"]
    qc_wf_below[of "mult s" "multpw ns" "{X}"]
  unfolding mult2_s_def by blast


subsection \<open>Trivial cases\<close>

lemma mult2_alt_emptyL:
  "({#}, Y) \<in> mult2_alt b ns s \<longleftrightarrow> b \<or> Y \<noteq> {#}"
  unfolding mult2_alt_def by auto

lemma mult2_alt_emptyR:
  "(X, {#}) \<in> mult2_alt b ns s \<longleftrightarrow> b \<and> X = {#}"
  unfolding mult2_alt_def by (auto intro: multiset_eqI)

lemma mult2_alt_s_single:
  "(a, b) \<in> s \<Longrightarrow> ({#a#}, {#b#}) \<in> mult2_alt_s ns s"
  using mult2_altI[of _ "{#}" _ _ "{#}" _ ns False s] by auto

lemma multpw_implies_mult2_alt_ns:
  assumes "(X, Y) \<in> multpw ns"
  shows "(X, Y) \<in> mult2_alt_ns ns s"
  using assms by (intro mult2_alt_nsI[of X X "{#}" Y Y "{#}"]) auto

lemma mult2_alt_ns_conv:
  "mult2_alt_ns ns s = mult2_alt_s ns s \<union> multpw ns" (is "?l = ?r")
proof (intro equalityI subrelI)
  fix X Y assume "(X, Y) \<in> ?l"
  thm mult2_alt_nsE
  then obtain X1 X2 Y1 Y2 where "X = X1 + X2" "Y = Y1 + Y2" "(X1, Y1) \<in> multpw ns"
    "\<forall>x. x \<in># X2 \<longrightarrow> (\<exists>y. y \<in># Y2 \<and> (x, y) \<in> s)" by (auto elim: mult2_alt_nsE)
  then show "(X, Y) \<in> ?r" using count_inject[of X2 "{#}"]
    by (cases "Y2 = {#}") (auto intro: mult2_alt_sI elim: mult2_alt_nsE mult2_alt_sE)
next
  fix X Y assume "(X, Y) \<in> ?r" then show "(X, Y) \<in> ?l"
    by (auto intro: mult2_alt_nsI multpw_implies_mult2_alt_ns elim: mult2_alt_sE)
qed

lemma mult2_alt_s_implies_mult2_alt_ns:
  assumes "(X, Y) \<in> mult2_alt_s ns s"
  shows "(X, Y) \<in> mult2_alt_ns ns s"
  using assms by (auto intro: mult2_alt_nsI elim: mult2_alt_sE)

lemma mult2_alt_add:
  assumes "(X1, Y1) \<in> mult2_alt b1 ns s" and "(X2, Y2) \<in> mult2_alt b2 ns s"
  shows "(X1 + X2, Y1 + Y2) \<in> mult2_alt (b1 \<and> b2) ns s"
proof -
  from assms obtain X11 X12 Y11 Y12 X21 X22 Y21 Y22 where
    "X1 = X11 + X12" "Y1 = Y11 + Y12"
    "(X11, Y11) \<in> multpw ns" "(b1 \<or> Y12 \<noteq> {#})" "(\<forall>x. x \<in># X12 \<longrightarrow> (\<exists>y. y \<in># Y12 \<and> (x, y) \<in> s))"
    "X2 = X21 + X22" "Y2 = Y21 + Y22"
    "(X21, Y21) \<in> multpw ns" "(b2 \<or> Y22 \<noteq> {#})" "(\<forall>x. x \<in># X22 \<longrightarrow> (\<exists>y. y \<in># Y22 \<and> (x, y) \<in> s))"
    unfolding mult2_alt_def by (blast 9)
  then show ?thesis
    by (intro mult2_altI[of _ "X11 + X21" "X12 + X22" _ "Y11 + Y21" "Y12 + Y22"])
      (auto intro: multpw_add simp: ac_simps)
qed

lemmas mult2_alt_s_s_add = mult2_alt_add[of _ _ False _ _ _ _ False, unfolded simp_thms]
lemmas mult2_alt_ns_s_add = mult2_alt_add[of _ _ True _ _ _ _ False, unfolded simp_thms]
lemmas mult2_alt_s_ns_add = mult2_alt_add[of _ _ False _ _ _ _ True, unfolded simp_thms]
lemmas mult2_alt_ns_ns_add = mult2_alt_add[of _ _ True _ _ _ _ True, unfolded simp_thms]


lemma multpw_map:
  assumes "\<And>x y. x \<in># X \<Longrightarrow> y \<in># Y \<Longrightarrow> (x, y) \<in> ns \<Longrightarrow> (f x, g y) \<in> ns'"
    and "(X, Y) \<in> multpw ns"
  shows "(image_mset f X, image_mset g Y) \<in> multpw ns'"
  using assms(2,1) by (induct X Y rule: multpw.induct) (auto intro: multpw.intros)

lemma mult2_alt_map:
  assumes "\<And>x y. x \<in># X \<Longrightarrow> y \<in># Y \<Longrightarrow> (x, y) \<in> ns \<Longrightarrow> (f x, g y) \<in> ns'"
    and "\<And>x y. x \<in># X \<Longrightarrow> y \<in># Y \<Longrightarrow> (x, y) \<in> s \<Longrightarrow> (f x, g y) \<in> s'"
    and "(X, Y) \<in> mult2_alt b ns s"
  shows "(image_mset f X, image_mset g Y) \<in> mult2_alt b ns' s'"
proof -
  from assms(3) obtain X1 X2 Y1 Y2 where "X = X1 + X2" "Y = Y1 + Y2" "(X1, Y1) \<in> multpw ns"
    "b \<or> Y2 \<noteq> {#}" "\<forall>x. x \<in># X2 \<longrightarrow> (\<exists>y. y \<in># Y2 \<and> (x, y) \<in> s)" by (auto elim: mult2_altE)
  moreover from this(1,2,5) have "\<forall>x. x \<in># image_mset f X2 \<longrightarrow> (\<exists>y. y \<in># image_mset g Y2 \<and> (x, y) \<in> s')"
    using assms(2) by (simp add: in_image_mset image_iff) blast
  ultimately show ?thesis using assms multpw_map[of X1 Y1 ns f g]
    by (intro mult2_altI[of _ "image_mset f X1" "image_mset f X2" _ "image_mset g Y1" "image_mset g Y2"]) auto
qed

text \<open>Local transitivity of @{const mult2_alt}\<close>

lemma trans_mult2_alt_local:
  assumes ss: "\<And>x y z. x \<in># X \<Longrightarrow> y \<in># Y \<Longrightarrow> z \<in># Z \<Longrightarrow> (x, y) \<in> s \<Longrightarrow> (y, z) \<in> s \<Longrightarrow> (x, z) \<in> s"
    and ns: "\<And>x y z. x \<in># X \<Longrightarrow> y \<in># Y \<Longrightarrow> z \<in># Z \<Longrightarrow> (x, y) \<in> ns \<Longrightarrow> (y, z) \<in> s \<Longrightarrow> (x, z) \<in> s"
    and sn: "\<And>x y z. x \<in># X \<Longrightarrow> y \<in># Y \<Longrightarrow> z \<in># Z \<Longrightarrow> (x, y) \<in> s \<Longrightarrow> (y, z) \<in> ns \<Longrightarrow> (x, z) \<in> s"
    and nn: "\<And>x y z. x \<in># X \<Longrightarrow> y \<in># Y \<Longrightarrow> z \<in># Z \<Longrightarrow> (x, y) \<in> ns \<Longrightarrow> (y, z) \<in> ns \<Longrightarrow> (x, z) \<in> ns"
    and xyz: "(X, Y) \<in> mult2_alt b1 ns s" "(Y, Z) \<in> mult2_alt b2 ns s"
  shows "(X, Z) \<in> mult2_alt (b1 \<and> b2) ns s"
proof -
  let ?a1 = Enum.finite_3.a\<^sub>1 and ?a2 = Enum.finite_3.a\<^sub>2 and ?a3 = Enum.finite_3.a\<^sub>3
  let ?t = "{(?a1, ?a2), (?a1, ?a3), (?a2, ?a3)}"
  let ?A = "{(?a1, x) |x. x \<in># X} \<union> {(?a2, y) |y. y \<in># Y} \<union> {(?a3, z) |z. z \<in># Z}"
  define s' where "s' = Restr {((a, x), (b, y)) |a x b y. (a, b) \<in> ?t \<and> (x, y) \<in> s} ?A"
  define ns' where "ns' = (Restr {((a, x), (b, y)) |a x b y. (a, b) \<in> ?t \<and> (x, y) \<in> ns} ?A)\<^sup>="
  have *: "refl ns'" "trans ns'" "trans s'" "s' O ns' \<subseteq> s'" "ns' O s' \<subseteq> s'"
    by (force simp: trans_def ss ns sn nn s'_def ns'_def)+
  have "({#(?a1, x). x \<in># X#}, {#(?a2, y). y \<in># Y#}) \<in> mult2_alt b1 ns' s'"
    by (auto intro: mult2_alt_map[OF _ _ xyz(1)] simp: s'_def ns'_def)
  moreover have "({#(?a2, y). y \<in># Y#}, {#(?a3, z). z \<in># Z#}) \<in> mult2_alt b2 ns' s'"
    by (auto intro: mult2_alt_map[OF _ _ xyz(2)] simp: s'_def ns'_def)
  ultimately have "({#(?a1, x). x \<in># X#}, {#(?a3, z). z \<in># Z#}) \<in> mult2_alt (b1 \<and> b2) ns' s'"
    using mult2_s_eq_mult2_s_alt[OF *(5,1,3)] mult2_ns_eq_mult2_ns_alt[OF *(5,1,3)]
      trans_mult2_s[OF *(4,1,2)] trans_mult2_ns[OF *(4,1,2)] compat_mult2[OF *(4,1,2)]
    by (cases b1; cases b2) (auto simp: trans_O_iff)
  from mult2_alt_map[OF _ _ this, of snd snd ns s]
  show ?thesis by (auto simp: s'_def ns'_def image_mset.compositionality comp_def in_image_mset image_iff)
qed

lemmas trans_mult2_alt_s_s_local = trans_mult2_alt_local[of _ _ _ _ _ False False, unfolded simp_thms]
lemmas trans_mult2_alt_ns_s_local = trans_mult2_alt_local[of _ _ _ _ _ True False, unfolded simp_thms]
lemmas trans_mult2_alt_s_ns_local = trans_mult2_alt_local[of _ _ _ _ _ False True, unfolded simp_thms]
lemmas trans_mult2_alt_ns_ns_local = trans_mult2_alt_local[of _ _ _ _ _ True True, unfolded simp_thms]

end
