(*
  File:         Finite_Map_Multiset.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory Finite_Map_Multiset
imports "HOL-Library.Finite_Map" Duplicate_Free_Multiset
begin

notation image_mset (infixr "`#" 90)

section \<open>Finite maps and multisets\<close>

subsection \<open>Finite sets and multisets\<close>

abbreviation mset_fset :: \<open>'a fset \<Rightarrow> 'a multiset\<close> where
  \<open>mset_fset N \<equiv> mset_set (fset N)\<close>

definition fset_mset :: \<open>'a multiset \<Rightarrow> 'a fset\<close> where
  \<open>fset_mset N \<equiv> Abs_fset (set_mset N)\<close>

lemma fset_mset_mset_fset: \<open>fset_mset (mset_fset N) = N\<close>
  by (auto simp: fset.fset_inverse fset_mset_def)

lemma mset_fset_fset_mset[simp]:
  \<open>mset_fset (fset_mset N) = remdups_mset N\<close>
  by (auto simp: fset.fset_inverse fset_mset_def Abs_fset_inverse remdups_mset_def)

lemma in_mset_fset_fmember[simp]: \<open>x \<in># mset_fset N \<longleftrightarrow> x |\<in>| N\<close>
  by (auto simp: fmember.rep_eq)

lemma in_fset_mset_mset[simp]: \<open>x |\<in>| fset_mset N \<longleftrightarrow> x \<in># N\<close>
  by (auto simp: fmember.rep_eq fset_mset_def Abs_fset_inverse)


subsection \<open>Finite map and multisets\<close>

text \<open>Roughly the same as \<^term>\<open>ran\<close> and \<^term>\<open>dom\<close>, but with duplication in the content (unlike their
  finite sets counterpart) while still working on finite domains (unlike a function mapping).
  Remark that \<^term>\<open>dom_m\<close> (the keys) does not contain duplicates, but we keep for symmetry (and for
  easier use of multiset operators as in the definition of \<^term>\<open>ran_m\<close>).
\<close>
definition dom_m where
  \<open>dom_m N = mset_fset (fmdom N)\<close>

definition ran_m where
  \<open>ran_m N = the `# fmlookup N `# dom_m N\<close>

lemma dom_m_fmdrop[simp]: \<open>dom_m (fmdrop C N) = remove1_mset C (dom_m N)\<close>
  unfolding dom_m_def
  by (cases \<open>C |\<in>| fmdom N\<close>)
    (auto simp: mset_set.remove fmember.rep_eq)

lemma dom_m_fmdrop_All: \<open>dom_m (fmdrop C N) = removeAll_mset C (dom_m N)\<close>
  unfolding dom_m_def
  by (cases \<open>C |\<in>| fmdom N\<close>)
    (auto simp: mset_set.remove fmember.rep_eq)

lemma dom_m_fmupd[simp]: \<open>dom_m (fmupd k C N) = add_mset k (remove1_mset k (dom_m N))\<close>
  unfolding dom_m_def
  by (cases \<open>k |\<in>| fmdom N\<close>)
    (auto simp: mset_set.remove fmember.rep_eq mset_set.insert_remove)

lemma distinct_mset_dom: \<open>distinct_mset (dom_m N)\<close>
  by (simp add: distinct_mset_mset_set dom_m_def)

lemma in_dom_m_lookup_iff: \<open>C \<in># dom_m N' \<longleftrightarrow> fmlookup N' C \<noteq> None\<close>
  by (auto simp: dom_m_def fmdom.rep_eq fmlookup_dom'_iff)

lemma in_dom_in_ran_m[simp]: \<open>i \<in># dom_m N \<Longrightarrow> the (fmlookup N i) \<in># ran_m N\<close>
  by (auto simp: ran_m_def)

lemma fmupd_same[simp]:
  \<open>x1 \<in># dom_m x1aa \<Longrightarrow> fmupd x1 (the (fmlookup x1aa x1)) x1aa = x1aa\<close>
  by (metis fmap_ext fmupd_lookup in_dom_m_lookup_iff option.collapse)

lemma ran_m_fmempty[simp]: \<open>ran_m fmempty = {#}\<close> and
    dom_m_fmempty[simp]: \<open>dom_m fmempty = {#}\<close>
  by (auto simp: ran_m_def dom_m_def)

lemma fmrestrict_set_fmupd:
  \<open>a \<in> xs \<Longrightarrow> fmrestrict_set xs (fmupd a C N) = fmupd a C (fmrestrict_set xs N)\<close>
  \<open>a \<notin> xs \<Longrightarrow> fmrestrict_set xs (fmupd a C N) = fmrestrict_set xs N\<close>
  by (auto simp: fmfilter_alt_defs)

lemma fset_fmdom_fmrestrict_set:
  \<open>fset (fmdom (fmrestrict_set xs N)) = fset (fmdom N) \<inter> xs\<close>
  by (auto simp: fmfilter_alt_defs)

lemma dom_m_fmrestrict_set: \<open>dom_m (fmrestrict_set (set xs) N) = mset xs \<inter># dom_m N\<close>
  using fset_fmdom_fmrestrict_set[of \<open>set xs\<close> N] distinct_mset_dom[of N]
  distinct_mset_inter_remdups_mset[of \<open>mset_fset (fmdom N)\<close> \<open>mset xs\<close>]
  by (auto simp: dom_m_def fset_mset_mset_fset finite_mset_set_inter multiset_inter_commute
    remdups_mset_def)

lemma dom_m_fmrestrict_set': \<open>dom_m (fmrestrict_set xs N) = mset_set (xs \<inter> set_mset (dom_m N))\<close>
  using fset_fmdom_fmrestrict_set[of \<open>xs\<close> N] distinct_mset_dom[of N]
  by (auto simp: dom_m_def fset_mset_mset_fset finite_mset_set_inter multiset_inter_commute
    remdups_mset_def)

lemma indom_mI: \<open>fmlookup m x = Some y \<Longrightarrow> x \<in># dom_m m\<close>
  by (drule fmdomI)  (auto simp: dom_m_def fmember.rep_eq)

lemma fmupd_fmdrop_id:
  assumes \<open>k |\<in>| fmdom N'\<close>
  shows \<open>fmupd k (the (fmlookup N' k)) (fmdrop k N') = N'\<close>
proof -
  have [simp]: \<open>map_upd k (the (fmlookup N' k))
       (\<lambda>x. if x \<noteq> k then fmlookup N' x else None) =
     map_upd k (the (fmlookup N' k))
       (fmlookup N')\<close>
    by (auto intro!: ext simp: map_upd_def)
  have [simp]: \<open>map_upd k (the (fmlookup N' k)) (fmlookup N') = fmlookup N'\<close>
    using assms
    by (auto intro!: ext simp: map_upd_def)
  have [simp]: \<open>finite (dom (\<lambda>x. if x = k then None else fmlookup N' x))\<close>
    by (subst dom_if) auto
  show ?thesis
    apply (auto simp: fmupd_def fmupd.abs_eq[symmetric])
    unfolding fmlookup_drop
    apply (simp add: fmlookup_inverse)
    done
qed

lemma fm_member_split: \<open>k |\<in>| fmdom N' \<Longrightarrow> \<exists>N'' v. N' = fmupd k v N'' \<and> the (fmlookup N' k) = v \<and>
    k |\<notin>| fmdom N''\<close>
  by (rule exI[of _ \<open>fmdrop k N'\<close>])
    (auto simp: fmupd_fmdrop_id)

lemma \<open>fmdrop k (fmupd k va N'') = fmdrop k N''\<close>
  by (simp add: fmap_ext)

lemma fmap_ext_fmdom:
  \<open>(fmdom N = fmdom N') \<Longrightarrow> (\<And> x. x |\<in>| fmdom N \<Longrightarrow> fmlookup N x = fmlookup N' x) \<Longrightarrow>
       N = N'\<close>
  by (rule fmap_ext)
    (case_tac \<open>x |\<in>| fmdom N\<close>, auto simp: fmdom_notD)

lemma fmrestrict_set_insert_in:
  \<open>xa  \<in> fset (fmdom N) \<Longrightarrow>
    fmrestrict_set (insert xa l1) N = fmupd xa (the (fmlookup N xa)) (fmrestrict_set l1 N)\<close>
  apply (rule fmap_ext_fmdom)
   apply (auto simp: fset_fmdom_fmrestrict_set fmember.rep_eq notin_fset; fail)[]
  apply (auto simp: fmlookup_dom_iff; fail)
  done

lemma fmrestrict_set_insert_notin:
  \<open>xa  \<notin> fset (fmdom N) \<Longrightarrow>
    fmrestrict_set (insert xa l1) N = fmrestrict_set l1 N\<close>
  by (rule fmap_ext_fmdom)
     (auto simp: fset_fmdom_fmrestrict_set fmember.rep_eq notin_fset)

lemma fmrestrict_set_insert_in_dom_m[simp]:
  \<open>xa  \<in># dom_m N \<Longrightarrow>
    fmrestrict_set (insert xa l1) N = fmupd xa (the (fmlookup N xa)) (fmrestrict_set l1 N)\<close>
  by (simp add: fmrestrict_set_insert_in dom_m_def)

lemma fmrestrict_set_insert_notin_dom_m[simp]:
  \<open>xa  \<notin># dom_m N \<Longrightarrow>
    fmrestrict_set (insert xa l1) N = fmrestrict_set l1 N\<close>
  by (simp add: fmrestrict_set_insert_notin dom_m_def)

lemma fmlookup_restrict_set_id: \<open>fset (fmdom N) \<subseteq> A \<Longrightarrow> fmrestrict_set A N = N\<close>
  by (metis fmap_ext fmdom'_alt_def fmdom'_notD fmlookup_restrict_set subset_iff)

lemma fmlookup_restrict_set_id': \<open>set_mset (dom_m N) \<subseteq> A \<Longrightarrow> fmrestrict_set A N = N\<close>
  by (rule fmlookup_restrict_set_id)
    (auto simp: dom_m_def)

lemma ran_m_mapsto_upd:
  assumes
    NC: \<open>C \<in># dom_m N\<close>
  shows \<open>ran_m (fmupd C C' N) = add_mset C' (remove1_mset (the (fmlookup N C)) (ran_m N))\<close>
proof -
  define N' where
    \<open>N' = fmdrop C N\<close>
  have N_N': \<open>dom_m N = add_mset C (dom_m N')\<close>
    using NC unfolding N'_def by auto
  have \<open>C \<notin># dom_m N'\<close>
    using NC distinct_mset_dom[of N] unfolding N_N' by auto
  then show ?thesis
    by (auto simp: N_N' ran_m_def mset_set.insert_remove image_mset_remove1_mset_if
      intro!: image_mset_cong)
qed

lemma ran_m_mapsto_upd_notin:
  assumes NC: \<open>C \<notin># dom_m N\<close>
  shows \<open>ran_m (fmupd C C' N) = add_mset C' (ran_m N)\<close>
  using NC
  by (auto simp: ran_m_def mset_set.insert_remove image_mset_remove1_mset_if
      intro!: image_mset_cong split: if_splits)

lemma image_mset_If_eq_notin:
   \<open>C \<notin># A \<Longrightarrow> {#f (if x = C then a x else b x). x \<in># A#} = {# f(b x). x \<in># A #}\<close>
  by (induction A) auto

lemma filter_mset_cong2:
  "(\<And>x. x \<in># M \<Longrightarrow> f x = g x) \<Longrightarrow> M = N \<Longrightarrow> filter_mset f M = filter_mset g N"
  by (hypsubst, rule filter_mset_cong, simp)

lemma ran_m_fmdrop:
  \<open>C \<in># dom_m N \<Longrightarrow>  ran_m (fmdrop C N) = remove1_mset (the (fmlookup N C)) (ran_m N)\<close>
  using distinct_mset_dom[of N]
  by (cases \<open>fmlookup N C\<close>)
    (auto simp: ran_m_def image_mset_If_eq_notin[of C _ \<open>\<lambda>x. fst (the x)\<close>]
     dest!: multi_member_split
     intro!: filter_mset_cong2 image_mset_cong2)

lemma ran_m_fmdrop_notin:
  \<open>C \<notin># dom_m N \<Longrightarrow> ran_m (fmdrop C N) = ran_m N\<close>
  using distinct_mset_dom[of N]
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ \<open>\<lambda>x. fst (the x)\<close>]
    dest!: multi_member_split
    intro!: filter_mset_cong2 image_mset_cong2)

lemma ran_m_fmdrop_If:
  \<open>ran_m (fmdrop C N) = (if C \<in># dom_m N then remove1_mset (the (fmlookup N C)) (ran_m N) else ran_m N)\<close>
  using distinct_mset_dom[of N]
  by (auto simp: ran_m_def image_mset_If_eq_notin[of C _ \<open>\<lambda>x. fst (the x)\<close>]
    dest!: multi_member_split
    intro!: filter_mset_cong2 image_mset_cong2)

lemma dom_m_empty_iff[iff]:
  \<open>dom_m NU = {#} \<longleftrightarrow> NU = fmempty\<close>
  by (cases NU) (auto simp: dom_m_def mset_set.insert_remove)

end