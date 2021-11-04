(* Title: Examples/SML_Relativization/Foundations/Transfer_Ext.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Extension of the theory \<^text>\<open>Transfer\<close>\<close>
theory Transfer_Ext
  imports Main
begin

lemma bi_unique_intersect_r:
  assumes "bi_unique T" 
    and "rel_set T a a'" 
    and "rel_set T b b'" 
    and "rel_set T (a \<inter> b) xr" 
  shows "a' \<inter> b' = xr"
proof -
  {
    fix x assume "x \<in> a \<inter> b"
    then have "x \<in> a" and "x \<in> b" by simp+
    from assms(2) \<open>x \<in> a\<close> have "\<exists>y \<in> a'. T x y" by (rule rel_setD1)
    moreover from assms(3) \<open>x \<in> b\<close> have "\<exists>y \<in> b'. T x y" by (rule rel_setD1)
    ultimately have "\<exists>y \<in> a' \<inter> b'. T x y" 
      using assms(1) by (auto dest: bi_uniqueDr)
  }
  note unique_r = this
  {
    fix x assume "x \<in> a' \<inter> b'"
    then have "x \<in> a'" and "x \<in> b'" by simp+
    from assms(2) \<open>x \<in> a'\<close> have "\<exists>y \<in> a. T y x" by (rule rel_setD2)
    moreover from assms(3) \<open>x \<in> b'\<close> have "\<exists>y \<in> b. T y x" by (rule rel_setD2)
    ultimately have "\<exists>y \<in> a \<inter> b. T y x" 
      using assms(1) by (auto dest: bi_uniqueDl)
  }
  with unique_r have "rel_set T (a \<inter> b) (a' \<inter> b')" using rel_setI by blast 
  with assms(1,4) show ?thesis by (auto dest: bi_uniqueDr bi_unique_rel_set)
qed

lemma bi_unique_intersect_l:
  assumes "bi_unique T" 
    and "rel_set T a a'" 
    and "rel_set T b b'" 
    and "rel_set T xl (a' \<inter> b')" 
  shows "a \<inter> b = xl"
proof -
  let ?T' = "\<lambda> y x. T x y"
  from assms(1) have "bi_unique ?T'" unfolding bi_unique_def by simp
  moreover from assms(2) have "rel_set ?T' a' a" unfolding rel_set_def by simp
  moreover from assms(3) have "rel_set ?T' b' b" unfolding rel_set_def by simp
  moreover from assms(4) have "rel_set ?T' (a' \<inter> b') xl" 
    unfolding rel_set_def by simp
  ultimately show ?thesis by (rule bi_unique_intersect_r)
qed

lemma bi_unique_intersect:
  assumes "bi_unique T" and "rel_set T a a'" and "rel_set T b b'" 
  shows "rel_set T (a \<inter> b) (a' \<inter> b')" 
proof -
  {
    fix xl assume "xl \<in> a \<inter> b"
    then have "xl \<in> a" and "xl \<in> b" by simp+
    with assms(3) obtain xr where "T xl xr" unfolding rel_set_def by auto
    with assms(1,2) \<open>xl \<in> a\<close> have "xr \<in> a'"
      by (auto dest: bi_uniqueDr rel_setD1)
    moreover with assms(1,3) \<open>xl \<in> b\<close> \<open>T xl xr\<close> have "xr \<in> b'" 
      by (auto dest: bi_uniqueDr rel_setD1)
    ultimately have "xr \<in> a' \<inter> b'" by simp
    with \<open>T xl xr\<close> have "\<exists>xr. xr \<in> a' \<inter> b' \<and> T xl xr" by auto
  }
  then have prem_lhs: "\<forall>xl \<in> a \<inter> b. \<exists>xr. xr \<in> a' \<inter> b' \<and> T xl xr" by simp  
  {
    fix xr
    assume "xr \<in> a' \<inter> b'"
    then have "xr \<in> a'" and "xr \<in> b'" by simp+
    with assms(3) obtain xl where "T xl xr" unfolding rel_set_def by auto
    with assms(1,2) \<open>xr \<in> a'\<close> have "xl \<in> a" 
      by (auto dest: bi_uniqueDl rel_setD2)
    moreover with assms(1,3) \<open>xr \<in> b'\<close> \<open>T xl xr\<close> have "xl \<in> b" 
      by (auto dest: bi_uniqueDl rel_setD2)
    ultimately have "xl \<in> a \<inter> b" by simp
    with \<open>T xl xr\<close> have "\<exists>xl. xl \<in> a \<inter> b \<and> T xl xr" by auto
  }
  then have prem_rhs: "\<forall>xr \<in> a' \<inter> b'. \<exists>xl. xl \<in> a \<inter> b \<and> T xl xr" by simp
  from prem_lhs prem_rhs show ?thesis unfolding rel_set_def by auto
qed

lemma bi_unique_union_r:
  assumes "bi_unique T" 
    and "rel_set T a a'" 
    and "rel_set T b b'" 
    and "rel_set T (a \<union> b) xr" 
  shows "a' \<union> b' = xr"
proof -
  {
    fix x assume "x \<in> a \<union> b"
    then have "x \<in> a \<or> x \<in> b" by simp
    from assms(2) have "\<exists>y \<in> a'. T x y" if "x \<in> a" 
      using that by (rule rel_setD1)
    moreover from assms(3) have "\<exists>y \<in> b'. T x y" if "x \<in> b" 
      using that by (rule rel_setD1)
    ultimately have "\<exists>y \<in> a' \<union> b'. T x y" using \<open>x \<in> a \<or> x \<in> b\<close> by auto
  }
  note unique_r = this
  {
    fix x assume "x \<in> a' \<union> b'"
    then have "x \<in> a' \<or> x \<in> b'" by simp
    from assms(2) have "\<exists>y \<in> a. T y x" if "x \<in> a'" 
      using that by (rule rel_setD2)
    moreover from assms(3) have "\<exists>y \<in> b. T y x" if "x \<in> b'" 
      using that by (rule rel_setD2)
    ultimately have "\<exists>y \<in> a \<union> b. T y x" using \<open>x \<in> a' \<or> x \<in> b'\<close> by auto
  }
  with unique_r have "rel_set T (a \<union> b) (a' \<union> b')" by (auto intro: rel_setI) 
  with assms(1,4) show ?thesis by (auto dest: bi_uniqueDr bi_unique_rel_set)
qed

lemma bi_unique_union_l:
  assumes "bi_unique T" 
    and "rel_set T a a'" 
    and "rel_set T b b'" 
    and "rel_set T xl (a' \<union> b')" 
  shows "a \<union> b = xl"
proof -
  let ?T' = "\<lambda>y x. T x y"
  from assms(1) have "bi_unique ?T'" unfolding bi_unique_def by simp
  moreover from assms(2) have "rel_set ?T' a' a" unfolding rel_set_def by simp
  moreover from assms(3) have "rel_set ?T' b' b" unfolding rel_set_def by simp
  moreover from assms(4) have "rel_set ?T' (a' \<union> b') xl" 
    unfolding rel_set_def by simp
  ultimately show ?thesis by (rule bi_unique_union_r)
qed

lemma bi_unique_union:
  assumes "bi_unique T" and "rel_set T a a'" and "rel_set T b b'" 
  shows "rel_set T (a \<union> b) (a' \<union> b')" 
proof -
  {
    fix xl assume "xl \<in> a \<union> b"
    with assms(2,3) obtain xr where "T xl xr" unfolding rel_set_def by auto
    with assms \<open>xl \<in> a \<union> b\<close> have "xr \<in> a' \<union> b'"
      unfolding bi_unique_def using Un_iff by (metis Un_iff rel_setD1)
    with \<open>T xl xr\<close> have "\<exists>xr. xr \<in> a' \<union> b' \<and> T xl xr" by auto
  }
  then have prem_lhs: "\<forall>xl \<in> a \<union> b. \<exists>xr. xr \<in> a' \<union> b' \<and> T xl xr" by simp  
  {
    fix xr assume "xr \<in> a' \<union> b'"
    with assms(2,3) obtain xl where "T xl xr" unfolding rel_set_def by auto
    with assms \<open>xr \<in> a' \<union> b'\<close> have "xl \<in> a \<union> b"
      unfolding bi_unique_def by (metis Un_iff rel_setD2)
    with \<open>T xl xr\<close> have "\<exists>xl. xl \<in> a \<union> b \<and> T xl xr" by auto
  }
  then have prem_rhs: "\<forall>xr \<in> a' \<union> b'. \<exists>xl. xl \<in> a \<union> b \<and> T xl xr" by simp
  from prem_lhs prem_rhs show ?thesis unfolding rel_set_def by auto
qed

lemma bi_unique_Union_r:
  fixes T :: "['a, 'b] \<Rightarrow> bool" and K
  defines K':  "K' \<equiv> {(x, y). rel_set T x y} `` K"
  assumes "bi_unique T" 
    and "\<Union>K \<subseteq> Collect (Domainp T)" 
    and "rel_set T (\<Union>K) xr" 
  shows "\<Union>K' = xr"
proof -
  {
    fix x assume "x \<in> \<Union>K"
    then obtain k where "x \<in> k" and "k \<in> K" by clarsimp
    from assms have ex_k'_prem: "\<forall>k \<in> K. \<forall>x \<in> k. \<exists>x'. T x x'" by auto
    define k' where k': "k' = {x'. \<exists>x \<in> k. T x x'}" 
    have "rel_set T k k'" 
      unfolding rel_set_def Bex_def k' 
      using \<open>k \<in> K\<close> by (blast dest: ex_k'_prem[rule_format])
    with \<open>k \<in> K\<close> have "k' \<in> K'" unfolding K' by auto
    from \<open>rel_set T k k'\<close> \<open>x \<in> k\<close> obtain y where "y \<in> k' \<and> T x y" 
      by (auto dest: rel_setD1)
    then have "\<exists>y \<in> \<Union>K'. T x y" using \<open>k' \<in> K'\<close> by auto
  }
  note unique_r = this
  {
    fix x' assume "x' \<in> \<Union>K'"
    then obtain k' where "x' \<in> k'" and "k' \<in> K'" by clarsimp
    then have ex_k_prem: "\<forall>k' \<in> K'. \<forall>x \<in> k'. \<exists>x. T x x'" 
      unfolding K' by (auto dest: rel_setD2)
    define k where k: "k = {x. \<exists>x' \<in> k'. T x x'}"
    have "rel_set T k k'" 
      unfolding rel_set_def Bex_def k 
      using \<open>k' \<in> K'\<close> K' by (blast dest: rel_setD2)
    from assms(2) have "bi_unique (rel_set T)" by (rule bi_unique_rel_set)
    with \<open>rel_set T k k'\<close> have "\<exists>!k. rel_set T k k'" by (auto dest: bi_uniqueDl)
    with \<open>rel_set T k k'\<close> K' \<open>k' \<in> K'\<close> have "k \<in> K" by auto
    from \<open>rel_set T k k'\<close> \<open>x' \<in> k'\<close> obtain y where "y \<in> k \<and> T y x'" 
      by (auto dest: rel_setD2)
    then have "\<exists>y \<in> \<Union>K. T y x'" using \<open>k \<in> K\<close> by auto
  }
  with unique_r have "rel_set T (\<Union>K) (\<Union>K')" by (intro rel_setI) 
  with assms(2,4) show ?thesis by (auto dest: bi_uniqueDr bi_unique_rel_set)
qed

lemma bi_unique_Union_l:
  fixes T :: "['a, 'b] \<Rightarrow> bool" and K'
  defines K: "K \<equiv> {(x, y). rel_set (\<lambda> y x. T x y) x y} `` K'"
  assumes "bi_unique T" 
    and "\<Union>K' \<subseteq> Collect (Rangep T)" 
    and "rel_set T xl (\<Union>K')" 
  shows "\<Union>K = xl"
proof -
  let ?T' = "\<lambda> y x. T x y"
  from assms(2) have "bi_unique ?T'" unfolding bi_unique_def by simp
  moreover from assms(3) have "\<Union>K' \<subseteq> Collect (Domainp ?T')" by blast
  moreover from assms(4) have "rel_set ?T' (\<Union>K') xl" 
    unfolding rel_set_def by simp
  ultimately have "\<Union>({(x, y). rel_set ?T' x y} `` K') = xl" 
    by (rule bi_unique_Union_r)
  thus ?thesis using K by simp
qed

context
  includes lifting_syntax
begin

text\<open>
The lemma \<^text>\<open>Domainp_applyI\<close> was adopted from the lemma with the 
identical name in the theory \<^text>\<open>Types_To_Sets/Group_on_With.thy\<close>.
\<close>
lemma Domainp_applyI:
  includes lifting_syntax
  shows "(A ===> B) f g \<Longrightarrow> A x y \<Longrightarrow> Domainp B (f x)"
  by (auto simp: rel_fun_def)

lemma Domainp_fun:
  assumes "left_unique A" 
  shows 
    "Domainp (rel_fun A B) = 
      (\<lambda>f. f ` (Collect (Domainp A)) \<subseteq> (Collect (Domainp B)))"
proof-
  have 
    "pred_fun (Domainp A) (Domainp B) = 
      (\<lambda>f. f ` (Collect (Domainp A)) \<subseteq> (Collect (Domainp B)))"
    by (simp add: image_subset_iff)
  from Domainp_pred_fun_eq[OF \<open>left_unique A\<close>, of B, unfolded this]
  show ?thesis .  
qed

lemma Bex_fun_transfer[transfer_rule]:
  assumes "bi_unique A" "right_total B"
  shows 
    "(((A ===> B) ===> (=)) ===> (=)) 
      (Bex (Collect (\<lambda>f. f ` (Collect (Domainp A)) \<subseteq> (Collect (Domainp B))))) 
      Ex"
proof-
  from assms(1) have "left_unique A" by (simp add: bi_unique_alt_def)
  note right_total_BA[transfer_rule] = 
    right_total_fun[
      OF conjunct2[OF bi_unique_alt_def[THEN iffD1, OF assms(1)]] assms(2)
      ]
  show ?thesis 
    unfolding Domainp_fun[OF \<open>left_unique A\<close>, symmetric]
    by transfer_prover
qed

end

text\<open>\newpage\<close>

end