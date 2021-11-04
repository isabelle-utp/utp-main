(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Elementary binary relations\<close>
theory CZH_Sets_BRelations
  imports CZH_Sets_Sets
  keywords "mk_VLambda" :: thy_defn  
    and "|app" "|vsv" "|vdomain" 
begin



subsection\<open>Background\<close>


text\<open>
This section presents a theory of binary relations internalized in the 
type \<^typ>\<open>V\<close> and exposes elementary properties of two special types of 
binary relations: single-valued binary relations and injective single-valued 
binary relations.

Many of the results that are presented in this section were carried over
(with amendments) from the theories \<^text>\<open>Set\<close> and \<^text>\<open>Relation\<close> in the main
library.
\<close>



subsection\<open>Constructors\<close>


subsubsection\<open>Identity relation\<close>

definition vid_on :: "V \<Rightarrow> V"
  where "vid_on A = set {\<langle>a, a\<rangle> | a. a \<in>\<^sub>\<circ> A}"

lemma vid_on_small[simp]: "small {\<langle>a, a\<rangle> | a. a \<in>\<^sub>\<circ> A}"
  by (rule down[of _ \<open>A \<times>\<^sub>\<circ> A\<close>]) blast


text\<open>Rules.\<close>

lemma vid_on_eqI: 
  assumes "a = b" and "a \<in>\<^sub>\<circ> A"
  shows "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> vid_on A"
  using assms by (simp add: vid_on_def)

lemma vid_onI[intro!]: 
  assumes "a \<in>\<^sub>\<circ> A"
  shows "\<langle>a, a\<rangle> \<in>\<^sub>\<circ> vid_on A"
  by (rule vid_on_eqI) (simp_all add: assms)

lemma vid_onD[dest!]: 
  assumes "\<langle>a, a\<rangle> \<in>\<^sub>\<circ> vid_on A"
  shows "a \<in>\<^sub>\<circ> A"
  using assms unfolding vid_on_def by auto

lemma vid_onE[elim!]: 
  assumes "x \<in>\<^sub>\<circ> vid_on A" and "\<exists>a\<in>\<^sub>\<circ>A. x = \<langle>a, a\<rangle> \<Longrightarrow> P" 
  shows P
  using assms unfolding vid_on_def by auto

lemma vid_on_iff: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> vid_on A \<longleftrightarrow> a = b \<and> a \<in>\<^sub>\<circ> A" by auto


text\<open>Set operations.\<close>

lemma vid_on_vempty[simp]: "vid_on 0 = 0" by auto

lemma vid_on_vsingleton[simp]: "vid_on (set {a}) = set {\<langle>a, a\<rangle>}" by auto

lemma vid_on_vdoubleton[simp]: "vid_on (set {a, b}) = set {\<langle>a, a\<rangle>, \<langle>b, b\<rangle>}" 
  by (auto simp: vinsert_set_insert_eq)

lemma vid_on_mono: 
  assumes "A \<subseteq>\<^sub>\<circ> B"
  shows "vid_on A \<subseteq>\<^sub>\<circ> vid_on B"
  using assms by auto

lemma vid_on_vinsert: "(vinsert \<langle>a, a\<rangle> (vid_on A)) = (vid_on (vinsert a A))" 
  by auto

lemma vid_on_vintersection: "vid_on (A \<inter>\<^sub>\<circ> B) = vid_on A \<inter>\<^sub>\<circ> vid_on B" by auto

lemma vid_on_vunion: "vid_on (A \<union>\<^sub>\<circ> B) = vid_on A \<union>\<^sub>\<circ> vid_on B" by auto

lemma vid_on_vdiff: "vid_on (A -\<^sub>\<circ> B) = vid_on A -\<^sub>\<circ> vid_on B" by auto


text\<open>Special properties.\<close>

lemma vid_on_vsubset_vtimes: "vid_on A \<subseteq>\<^sub>\<circ> A \<times>\<^sub>\<circ> A" by clarsimp


subsubsection\<open>Constant function\<close>

definition vconst_on :: "V \<Rightarrow> V \<Rightarrow> V"
  where "vconst_on A c = set {\<langle>a, c\<rangle> | a. a \<in>\<^sub>\<circ> A}"

lemma small_vconst_on[simp]: "small {\<langle>a, c\<rangle> | a. a \<in>\<^sub>\<circ> A}"
  by (rule down[of _ \<open>A \<times>\<^sub>\<circ> set {c}\<close>]) auto


text\<open>Rules.\<close>

lemma vconst_onI[intro!]: 
  assumes "a \<in>\<^sub>\<circ> A"
  shows "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> vconst_on A c"
  using assms unfolding vconst_on_def by simp

lemma vconst_onD[dest!]: 
  assumes "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> vconst_on A c"
  shows "a \<in>\<^sub>\<circ> A" 
  using assms unfolding vconst_on_def by simp

lemma vconst_onE[elim!]: 
  assumes "x \<in>\<^sub>\<circ> vconst_on A c"
  obtains a where "a \<in>\<^sub>\<circ> A" and "x = \<langle>a, c\<rangle>"
  using assms unfolding vconst_on_def by auto

lemma vconst_on_iff: "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> vconst_on A c \<longleftrightarrow> a \<in>\<^sub>\<circ> A" by auto


text\<open>Set operations.\<close>

lemma vconst_on_vempty[simp]: "vconst_on 0 c = 0"
  unfolding vconst_on_def by auto

lemma vconst_on_vsingleton[simp]: "vconst_on (set {a}) c = set {\<langle>a, c\<rangle>}" by auto

lemma vconst_on_vdoubleton[simp]: "vconst_on (set {a, b}) c = set {\<langle>a, c\<rangle>, \<langle>b, c\<rangle>}" 
  by (auto simp: vinsert_set_insert_eq)

lemma vconst_on_mono: 
  assumes "A \<subseteq>\<^sub>\<circ> B"
  shows "vconst_on A c \<subseteq>\<^sub>\<circ> vconst_on B c"
  using assms by auto

lemma vconst_on_vinsert:
  "(vinsert \<langle>a, c\<rangle> (vconst_on A c)) = (vconst_on (vinsert a A) c)" 
  by auto

lemma vconst_on_vintersection: 
  "vconst_on (A \<inter>\<^sub>\<circ> B) c = vconst_on A c \<inter>\<^sub>\<circ> vconst_on B c"
  by auto

lemma vconst_on_vunion: "vconst_on (A \<union>\<^sub>\<circ> B) c = vconst_on A c \<union>\<^sub>\<circ> vconst_on B c"
  by auto

lemma vconst_on_vdiff: "vconst_on (A -\<^sub>\<circ> B) c = vconst_on A c -\<^sub>\<circ> vconst_on B c"
  by auto


text\<open>Special properties.\<close>

lemma vconst_on_eq_vtimes: "vconst_on A c = A \<times>\<^sub>\<circ> set {c}" 
  by standard (auto intro!: vsubset_antisym)


subsubsection\<open>\<open>VLambda\<close>\<close>


text\<open>Rules.\<close>

lemma VLambdaI[intro!]: 
  assumes "a \<in>\<^sub>\<circ> A"
  shows "\<langle>a, f a\<rangle> \<in>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>A. f a)"
  using assms unfolding VLambda_def by auto

lemma VLambdaD[dest!]: 
  assumes "\<langle>a, f a\<rangle> \<in>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>A. f a)"
  shows "a \<in>\<^sub>\<circ> A"
  using assms unfolding VLambda_def by auto

lemma VLambdaE[elim!]:  
  assumes "x \<in>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>A. f a)"
  obtains a where "a \<in>\<^sub>\<circ> A" and "x = \<langle>a, f a\<rangle>"
  using assms unfolding VLambda_def by auto

lemma VLambda_iff1: "x \<in>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>A. f a) \<longleftrightarrow> (\<exists>a\<in>\<^sub>\<circ>A. x = \<langle>a, f a\<rangle>)" by auto

lemma VLambda_iff2: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>A. f a) \<longleftrightarrow> b = f a \<and> a \<in>\<^sub>\<circ> A" by auto

lemma small_VLambda[simp]: "small {\<langle>a, f a\<rangle> | a. a \<in>\<^sub>\<circ> A}" by auto

lemma VLambda_set_def: "(\<lambda>a\<in>\<^sub>\<circ>A. f a) = set {\<langle>a, f a\<rangle> | a. a \<in>\<^sub>\<circ> A}" by auto


text\<open>Set operations.\<close>

lemma VLambda_vempty[simp]: "(\<lambda>a\<in>\<^sub>\<circ>0. f a) = 0" by auto

lemma VLambda_vsingleton(*not simp*): "(\<lambda>a\<in>\<^sub>\<circ>set {a}. f a) = set {\<langle>a, f a\<rangle>}" 
  by auto

lemma VLambda_vdoubleton(*not simp*): 
  "(\<lambda>a\<in>\<^sub>\<circ>set {a, b}. f a) = set {\<langle>a, f a\<rangle>, \<langle>b, f b\<rangle>}"
  by (auto simp: vinsert_set_insert_eq)

lemma VLambda_mono: 
  assumes "A \<subseteq>\<^sub>\<circ> B"
  shows "(\<lambda>a\<in>\<^sub>\<circ>A. f a) \<subseteq>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>B. f a)"
  using assms by auto

lemma VLambda_vinsert: 
  "(\<lambda>a\<in>\<^sub>\<circ>vinsert a A. f a) = (\<lambda>a\<in>\<^sub>\<circ>set {a}. f a) \<union>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>A. f a)" 
  by auto

lemma VLambda_vintersection: "(\<lambda>a\<in>\<^sub>\<circ>A \<inter>\<^sub>\<circ> B. f a) = (\<lambda>a\<in>\<^sub>\<circ>A. f a) \<inter>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>B. f a)" 
  by auto

lemma VLambda_vunion: "(\<lambda>a\<in>\<^sub>\<circ>A \<union>\<^sub>\<circ> B. f a) = (\<lambda>a\<in>\<^sub>\<circ>A. f a) \<union>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>B. f a)" by auto

lemma VLambda_vdiff: "(\<lambda>a\<in>\<^sub>\<circ>A -\<^sub>\<circ> B. f a) = (\<lambda>a\<in>\<^sub>\<circ>A. f a) -\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>B. f a)" by auto


text\<open>Connections.\<close>

lemma VLambda_vid_on: "(\<lambda>a\<in>\<^sub>\<circ>A. a) = vid_on A" by auto

lemma VLambda_vconst_on: "(\<lambda>a\<in>\<^sub>\<circ>A. c) = vconst_on A c" by auto


subsubsection\<open>Composition\<close>

definition vcomp :: "V \<Rightarrow> V \<Rightarrow> V" (infixr "\<circ>\<^sub>\<circ>" 75)
  where "r \<circ>\<^sub>\<circ> s = set {\<langle>a, c\<rangle> | a c. \<exists>b. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> s \<and> \<langle>b, c\<rangle> \<in>\<^sub>\<circ> r}"
notation vcomp (infixr \<open>\<circ>\<^sub>\<circ>\<close> 75)

lemma vcomp_small[simp]: "small {\<langle>a, c\<rangle> | a c. \<exists>b. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> s \<and> \<langle>b, c\<rangle> \<in>\<^sub>\<circ> r}" 
  (is \<open>small ?s\<close>)
proof-
  define comp' where "comp' = (\<lambda>\<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>. \<langle>a, d\<rangle>)"
  have "small (elts (vpairs (s \<times>\<^sub>\<circ> r)))" by simp
  then have small_comp: "small (comp' ` elts (vpairs (s \<times>\<^sub>\<circ> r)))" by simp
  have ss: "?s \<subseteq> (comp' ` elts (vpairs (s \<times>\<^sub>\<circ> r)))" 
  proof
    fix x assume "x \<in> ?s"
    then obtain a b c where x_def: "x = \<langle>a, c\<rangle>" 
      and "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> s" 
      and "\<langle>b, c\<rangle> \<in>\<^sub>\<circ> r"
      by auto
    then have abbc: "\<langle>\<langle>a, b\<rangle>, \<langle>b, c\<rangle>\<rangle> \<in>\<^sub>\<circ> vpairs (s \<times>\<^sub>\<circ> r)"
      by (simp add: vpairs_iff_elts)
    have x_def': "x = comp' \<langle>\<langle>a, b\<rangle>, \<langle>b, c\<rangle>\<rangle>" unfolding comp'_def x_def by auto
    then show "x \<in> comp' ` elts (vpairs (s \<times>\<^sub>\<circ> r))"
      unfolding x_def' using abbc by auto
  qed
  with small_comp show ?thesis by (metis (lifting) smaller_than_small)
qed


text\<open>Rules.\<close>

lemma vcompI[intro!]: 
  assumes "\<langle>b, c\<rangle> \<in>\<^sub>\<circ> r" and "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> s" 
  shows "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> r \<circ>\<^sub>\<circ> s"
  using assms unfolding vcomp_def by auto

lemma vcompD[dest!]: 
  assumes "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> r \<circ>\<^sub>\<circ> s"
  shows "\<exists>b. \<langle>b, c\<rangle> \<in>\<^sub>\<circ> r \<and> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> s" 
  using assms unfolding vcomp_def by auto

lemma vcompE[elim!]:
  assumes "ac \<in>\<^sub>\<circ> r \<circ>\<^sub>\<circ> s" 
  obtains a b c where "ac = \<langle>a, c\<rangle>" and "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> s" and "\<langle>b, c\<rangle> \<in>\<^sub>\<circ> r"
  using assms unfolding vcomp_def by clarsimp


text\<open>Elementary properties.\<close>

lemma vcomp_assoc: "(r \<circ>\<^sub>\<circ> s) \<circ>\<^sub>\<circ> t = r \<circ>\<^sub>\<circ> (s \<circ>\<^sub>\<circ> t)" by auto


text\<open>Set operations.\<close>

lemma vcomp_vempty_left[simp]: "0 \<circ>\<^sub>\<circ> r = 0" by auto

lemma vcomp_vempty_right[simp]: "r \<circ>\<^sub>\<circ> 0 = 0" by auto

lemma vcomp_mono:
  assumes "r' \<subseteq>\<^sub>\<circ> r" and "s' \<subseteq>\<^sub>\<circ> s" 
  shows "r' \<circ>\<^sub>\<circ> s' \<subseteq>\<^sub>\<circ> r \<circ>\<^sub>\<circ> s"
  using assms by auto

lemma vcomp_vinsert_left[simp]: 
  "(vinsert \<langle>a, b\<rangle> s) \<circ>\<^sub>\<circ> r = (set {\<langle>a, b\<rangle>} \<circ>\<^sub>\<circ> r) \<union>\<^sub>\<circ> (s \<circ>\<^sub>\<circ> r)" 
  by auto

lemma vcomp_vinsert_right[simp]: 
  "r \<circ>\<^sub>\<circ> (vinsert \<langle>a, b\<rangle> s) = (r \<circ>\<^sub>\<circ> set {\<langle>a, b\<rangle>}) \<union>\<^sub>\<circ> (r \<circ>\<^sub>\<circ> s)"
  by auto

lemma vcomp_vunion_left[simp]: "(s \<union>\<^sub>\<circ> t) \<circ>\<^sub>\<circ> r = (s \<circ>\<^sub>\<circ> r) \<union>\<^sub>\<circ> (t \<circ>\<^sub>\<circ> r)" by auto

lemma vcomp_vunion_right[simp]: "r \<circ>\<^sub>\<circ> (s \<union>\<^sub>\<circ> t) = (r \<circ>\<^sub>\<circ> s) \<union>\<^sub>\<circ> (r \<circ>\<^sub>\<circ> t)" by auto


text\<open>Connections.\<close>

lemma vcomp_vid_on_idem[simp]: "vid_on A \<circ>\<^sub>\<circ> vid_on A = vid_on A" by auto

lemma vcomp_vid_on[simp]: "vid_on A \<circ>\<^sub>\<circ> vid_on B = vid_on (A \<inter>\<^sub>\<circ> B)" by auto

lemma vcomp_vconst_on_vid_on[simp]: "vconst_on A c \<circ>\<^sub>\<circ> vid_on A = vconst_on A c" 
  by auto

lemma vcomp_VLambda_vid_on[simp]: "(\<lambda>a\<in>\<^sub>\<circ>A. f a) \<circ>\<^sub>\<circ> vid_on A = (\<lambda>a\<in>\<^sub>\<circ>A. f a)" 
  by auto


text\<open>Special properties.\<close>

lemma vcomp_vsubset_vtimes:
  assumes "r \<subseteq>\<^sub>\<circ> B \<times>\<^sub>\<circ> C" and "s \<subseteq>\<^sub>\<circ> A \<times>\<^sub>\<circ> B" 
  shows "r \<circ>\<^sub>\<circ> s \<subseteq>\<^sub>\<circ> A \<times>\<^sub>\<circ> C"
  using assms by auto

lemma vcomp_obtain_middle[elim]:
  assumes "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> r \<circ>\<^sub>\<circ> s"
  obtains b where "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> s" and "\<langle>b, c\<rangle> \<in>\<^sub>\<circ> r"
  using assms by auto


subsubsection\<open>Converse relation\<close>

definition vconverse :: "V \<Rightarrow> V"
  where "vconverse A = (\<lambda>r\<in>\<^sub>\<circ>A. set {\<langle>b, a\<rangle> | a b. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r})"

abbreviation app_vconverse (\<open>(_\<inverse>\<^sub>\<circ>)\<close> [1000] 999)
  where "r\<inverse>\<^sub>\<circ> \<equiv> vconverse (set {r}) \<lparr>r\<rparr>"

lemma app_vconverse_def: "r\<inverse>\<^sub>\<circ> = set {\<langle>b, a\<rangle> | a b. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}"
  unfolding vconverse_def by simp

lemma vconverse_small[simp]: "small {\<langle>b, a\<rangle> | a b. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}"
proof-
  have eq: "{\<langle>b, a\<rangle> | a b. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r} = (\<lambda>\<langle>a, b\<rangle>. \<langle>b, a\<rangle>) ` elts (vpairs r)"
  proof(rule subset_antisym; rule subsetI, unfold mem_Collect_eq)
    fix x assume "x \<in> (\<lambda>\<langle>a, b\<rangle>. \<langle>b, a\<rangle>) ` elts (vpairs r)" 
    then obtain a b where "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> vpairs r" and "x = (\<lambda>\<langle>a, b\<rangle>. \<langle>b, a\<rangle>) \<langle>a, b\<rangle>"
      by blast
    then show "\<exists>a b. x = \<langle>b, a\<rangle> \<and> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" by auto
  qed (use image_iff vpairs_iff_elts in fastforce)
  show ?thesis unfolding eq by (rule replacement) auto
qed


text\<open>Rules.\<close>

lemma vconverseI[intro!]: 
  assumes "r \<in>\<^sub>\<circ> A"
  shows "\<langle>r, r\<inverse>\<^sub>\<circ>\<rangle> \<in>\<^sub>\<circ> vconverse A"
  using assms unfolding vconverse_def by auto

lemma vconverseD[dest]: 
  assumes "\<langle>r, s\<rangle> \<in>\<^sub>\<circ> vconverse A" 
  shows "r \<in>\<^sub>\<circ> A" and "s = r\<inverse>\<^sub>\<circ>"
  using assms unfolding vconverse_def by auto

lemma vconverseE[elim]: 
  assumes "x \<in>\<^sub>\<circ> vconverse A" 
  obtains r where "x = \<langle>r, r\<inverse>\<^sub>\<circ>\<rangle>" and "r \<in>\<^sub>\<circ> A"
  using assms unfolding vconverse_def by auto

lemma app_vconverseI[sym, intro!]: 
  assumes "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
  shows "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<circ>"
  using assms unfolding vconverse_def by auto

lemma app_vconverseD[sym, dest]: 
  assumes "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<circ>"
  shows "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> r" 
  using assms unfolding vconverse_def by simp

lemma app_vconverseE[elim!]: 
  assumes "x \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<circ>" 
  obtains a b where "x = \<langle>b, a\<rangle>" and "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
  using assms unfolding vconverse_def by auto

lemma vconverse_iff: "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<circ> \<longleftrightarrow> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" by auto


text\<open>Set operations.\<close>

lemma vconverse_vempty[simp]: "0\<inverse>\<^sub>\<circ> = 0" by auto

lemma vconverse_vsingleton: "(set {\<langle>a, b\<rangle>})\<inverse>\<^sub>\<circ> = set {\<langle>b, a\<rangle>}" by auto

lemma vconverse_vdoubleton[simp]: "(set {\<langle>a, b\<rangle>, \<langle>c, d\<rangle>})\<inverse>\<^sub>\<circ> = set {\<langle>b, a\<rangle>, \<langle>d, c\<rangle>}" 
  by (auto simp: vinsert_set_insert_eq)

lemma vconverse_vinsert: "(vinsert \<langle>a, b\<rangle> r)\<inverse>\<^sub>\<circ> = vinsert \<langle>b, a\<rangle> (r\<inverse>\<^sub>\<circ>)" by auto

lemma vconverse_vintersection: "(r \<inter>\<^sub>\<circ> s)\<inverse>\<^sub>\<circ> = r\<inverse>\<^sub>\<circ> \<inter>\<^sub>\<circ> s\<inverse>\<^sub>\<circ>" by auto

lemma vconverse_vunion: "(r \<union>\<^sub>\<circ> s)\<inverse>\<^sub>\<circ> = r\<inverse>\<^sub>\<circ> \<union>\<^sub>\<circ> s\<inverse>\<^sub>\<circ>" by auto


text\<open>Connections.\<close>

lemma vconverse_vid_on[simp]: "(vid_on A)\<inverse>\<^sub>\<circ> = vid_on A" by auto

lemma vconverse_vconst_on[simp]: "(vconst_on A c)\<inverse>\<^sub>\<circ> = set {c} \<times>\<^sub>\<circ> A" by auto

lemma vconverse_vcomp: "(r \<circ>\<^sub>\<circ> s)\<inverse>\<^sub>\<circ> = s\<inverse>\<^sub>\<circ> \<circ>\<^sub>\<circ> r\<inverse>\<^sub>\<circ>" by auto

lemma vconverse_vtimes: "(A \<times>\<^sub>\<circ> B)\<inverse>\<^sub>\<circ> = (B \<times>\<^sub>\<circ> A)" by auto


subsubsection\<open>Left restriction\<close>

definition vlrestriction :: "V \<Rightarrow> V"
  where "vlrestriction D =
    VLambda D (\<lambda>\<langle>r, A\<rangle>. set {\<langle>a, b\<rangle> | a b. a \<in>\<^sub>\<circ> A \<and> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r})"

abbreviation app_vlrestriction :: "V \<Rightarrow> V \<Rightarrow> V" (infixr \<open>\<restriction>\<^sup>l\<^sub>\<circ>\<close> 80)
  where "r \<restriction>\<^sup>l\<^sub>\<circ> A \<equiv> vlrestriction (set {\<langle>r, A\<rangle>}) \<lparr>\<langle>r, A\<rangle>\<rparr>"

lemma app_vlrestriction_def: "r \<restriction>\<^sup>l\<^sub>\<circ> A = set {\<langle>a, b\<rangle> | a b. a \<in>\<^sub>\<circ> A \<and> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}"
  unfolding vlrestriction_def by simp

lemma vlrestriction_small[simp]: "small {\<langle>a, b\<rangle> | a b. a \<in>\<^sub>\<circ> A \<and> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}"
  by (rule down[of _ r]) auto


text\<open>Rules.\<close>

lemma vlrestrictionI[intro!]: 
  assumes "\<langle>r, A\<rangle> \<in>\<^sub>\<circ> D"
  shows "\<langle>\<langle>r, A\<rangle>, r \<restriction>\<^sup>l\<^sub>\<circ> A\<rangle> \<in>\<^sub>\<circ> vlrestriction D"
  using assms unfolding vlrestriction_def by (simp add: VLambda_iff2)

lemma vlrestrictionD[dest]: 
  assumes "\<langle>\<langle>r, A\<rangle>, s\<rangle> \<in>\<^sub>\<circ> vlrestriction D" 
  shows "\<langle>r, A\<rangle> \<in>\<^sub>\<circ> D" and "s = r \<restriction>\<^sup>l\<^sub>\<circ> A"
  using assms unfolding vlrestriction_def by auto

lemma vlrestrictionE[elim]: 
  assumes "x \<in>\<^sub>\<circ> vlrestriction D" and "D \<subseteq>\<^sub>\<circ> R \<times>\<^sub>\<circ> X"
  obtains r A where "x = \<langle>\<langle>r, A\<rangle>, r \<restriction>\<^sup>l\<^sub>\<circ> A\<rangle>" and "r \<in>\<^sub>\<circ> R" and "A \<in>\<^sub>\<circ> X"
  using assms unfolding vlrestriction_def by auto

lemma app_vlrestrictionI[intro!]: 
  assumes "a \<in>\<^sub>\<circ> A" and "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" 
  shows "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r \<restriction>\<^sup>l\<^sub>\<circ> A" 
  using assms unfolding vlrestriction_def by simp

lemma app_vlrestrictionD[dest]: 
  assumes "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r \<restriction>\<^sup>l\<^sub>\<circ> A"  
  shows "a \<in>\<^sub>\<circ> A" and "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
  using assms unfolding vlrestriction_def by auto

lemma app_vlrestrictionE[elim]: 
  assumes "x \<in>\<^sub>\<circ> r \<restriction>\<^sup>l\<^sub>\<circ> A"
  obtains a b where "x = \<langle>a, b\<rangle>" and "a \<in>\<^sub>\<circ> A" and "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
  using assms unfolding vlrestriction_def by auto


text\<open>Set operations.\<close>

lemma vlrestriction_on_vempty[simp]: "r \<restriction>\<^sup>l\<^sub>\<circ> 0 = 0" 
  by (auto intro!: vsubset_antisym)

lemma vlrestriction_vempty[simp]: "0 \<restriction>\<^sup>l\<^sub>\<circ> A = 0" by auto

lemma vlrestriction_vsingleton_in[simp]: 
  assumes "a \<in>\<^sub>\<circ> A"
  shows "set {\<langle>a, b\<rangle>} \<restriction>\<^sup>l\<^sub>\<circ> A = set {\<langle>a, b\<rangle>}" 
  using assms by auto

lemma vlrestriction_vsingleton_nin[simp]: 
  assumes "a \<notin>\<^sub>\<circ> A"
  shows "set {\<langle>a, b\<rangle>} \<restriction>\<^sup>l\<^sub>\<circ> A = 0" 
  using assms by auto

lemma vlrestriction_mono: 
  assumes "A \<subseteq>\<^sub>\<circ> B"
  shows "r \<restriction>\<^sup>l\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> r \<restriction>\<^sup>l\<^sub>\<circ> B"
  using assms by auto

lemma vlrestriction_vinsert_nin[simp]: 
  assumes "a \<notin>\<^sub>\<circ> A"
  shows "(vinsert \<langle>a, b\<rangle> r) \<restriction>\<^sup>l\<^sub>\<circ> A = r \<restriction>\<^sup>l\<^sub>\<circ> A" 
  using assms by auto

lemma vlrestriction_vinsert_in: 
  assumes "a \<in>\<^sub>\<circ> A"
  shows "(vinsert \<langle>a, b\<rangle> r) \<restriction>\<^sup>l\<^sub>\<circ> A = vinsert \<langle>a, b\<rangle> (r \<restriction>\<^sup>l\<^sub>\<circ> A)" 
  using assms by auto

lemma vlrestriction_vintersection: "(r \<inter>\<^sub>\<circ> s) \<restriction>\<^sup>l\<^sub>\<circ> A = r \<restriction>\<^sup>l\<^sub>\<circ> A \<inter>\<^sub>\<circ> s \<restriction>\<^sup>l\<^sub>\<circ> A" by auto

lemma vlrestriction_vunion: "(r \<union>\<^sub>\<circ> s) \<restriction>\<^sup>l\<^sub>\<circ> A = r \<restriction>\<^sup>l\<^sub>\<circ> A \<union>\<^sub>\<circ> s \<restriction>\<^sup>l\<^sub>\<circ> A" by auto

lemma vlrestriction_vdiff: "(r -\<^sub>\<circ> s) \<restriction>\<^sup>l\<^sub>\<circ> A = r \<restriction>\<^sup>l\<^sub>\<circ> A -\<^sub>\<circ> s \<restriction>\<^sup>l\<^sub>\<circ> A" by auto


text\<open>Connections.\<close>

lemma vlrestriction_vid_on[simp]: "(vid_on A) \<restriction>\<^sup>l\<^sub>\<circ> B = vid_on (A \<inter>\<^sub>\<circ> B)" by auto

lemma vlrestriction_vconst_on: "(vconst_on A c) \<restriction>\<^sup>l\<^sub>\<circ> B = (vconst_on B c) \<restriction>\<^sup>l\<^sub>\<circ> A"
  by auto

lemma vlrestriction_vconst_on_commute:
  assumes "x \<in>\<^sub>\<circ> vconst_on A c \<restriction>\<^sup>l\<^sub>\<circ> B"
  shows "x \<in>\<^sub>\<circ> vconst_on B c \<restriction>\<^sup>l\<^sub>\<circ> A"
  using assms by auto

lemma vlrestriction_vcomp[simp]: "(r \<circ>\<^sub>\<circ> s) \<restriction>\<^sup>l\<^sub>\<circ> A = r \<circ>\<^sub>\<circ> (s \<restriction>\<^sup>l\<^sub>\<circ> A)" by auto


text\<open>Previous connections.\<close>

lemma vcomp_rel_vid_on[simp]: "r \<circ>\<^sub>\<circ> vid_on A = r \<restriction>\<^sup>l\<^sub>\<circ> A" by auto

lemma vcomp_vconst_on: 
  "r \<circ>\<^sub>\<circ> (vconst_on A c) = (r \<restriction>\<^sup>l\<^sub>\<circ> set {c}) \<circ>\<^sub>\<circ> (vconst_on A c)" 
  by auto


text\<open>Special properties.\<close>

lemma vlrestriction_vsubset_vpairs: "r \<restriction>\<^sup>l\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> vpairs r"
  by (rule vsubsetI) blast

lemma vlrestriction_vsubset_rel: "r \<restriction>\<^sup>l\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> r" by auto

lemma vlrestriction_VLambda: "(\<lambda>a\<in>\<^sub>\<circ>A. f a) \<restriction>\<^sup>l\<^sub>\<circ> B = (\<lambda>a\<in>\<^sub>\<circ>A \<inter>\<^sub>\<circ> B. f a)" by auto


subsubsection\<open>Right restriction\<close>

definition vrrestriction :: "V \<Rightarrow> V"
  where "vrrestriction D = 
    VLambda D (\<lambda>\<langle>r, A\<rangle>. set {\<langle>a, b\<rangle> | a b. b \<in>\<^sub>\<circ> A \<and> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r})"

abbreviation app_vrrestriction :: "V \<Rightarrow> V \<Rightarrow> V" (infixr \<open>\<restriction>\<^sup>r\<^sub>\<circ>\<close> 80)
  where "r \<restriction>\<^sup>r\<^sub>\<circ> A \<equiv> vrrestriction (set {\<langle>r, A\<rangle>}) \<lparr>\<langle>r, A\<rangle>\<rparr>"

lemma app_vrrestriction_def: "r \<restriction>\<^sup>r\<^sub>\<circ> A = set {\<langle>a, b\<rangle> | a b. b \<in>\<^sub>\<circ> A \<and> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}"
  unfolding vrrestriction_def by simp

lemma vrrestriction_small[simp]: "small {\<langle>a, b\<rangle> | a b. b \<in>\<^sub>\<circ> A \<and> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}"
  by (rule down[of _ r]) auto


text\<open>Rules.\<close>

lemma vrrestrictionI[intro!]: 
  assumes "\<langle>r, A\<rangle> \<in>\<^sub>\<circ> D"
  shows "\<langle>\<langle>r, A\<rangle>, r \<restriction>\<^sup>r\<^sub>\<circ> A\<rangle> \<in>\<^sub>\<circ> vrrestriction D"
  using assms unfolding vrrestriction_def by (simp add: VLambda_iff2)

lemma vrrestrictionD[dest]: 
  assumes "\<langle>\<langle>r, A\<rangle>, s\<rangle> \<in>\<^sub>\<circ> vrrestriction D" 
  shows "\<langle>r, A\<rangle> \<in>\<^sub>\<circ> D" and "s = r \<restriction>\<^sup>r\<^sub>\<circ> A"
  using assms unfolding vrrestriction_def by auto

lemma vrrestrictionE[elim]: 
  assumes "x \<in>\<^sub>\<circ> vrrestriction D" and "D \<subseteq>\<^sub>\<circ> R \<times>\<^sub>\<circ> X"
  obtains r A where "x = \<langle>\<langle>r, A\<rangle>, r \<restriction>\<^sup>r\<^sub>\<circ> A\<rangle>" and "r \<in>\<^sub>\<circ> R" and "A \<in>\<^sub>\<circ> X"
  using assms unfolding vrrestriction_def by auto

lemma app_vrrestrictionI[intro!]: 
  assumes "b \<in>\<^sub>\<circ> A" and "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" 
  shows "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r \<restriction>\<^sup>r\<^sub>\<circ> A" 
  using assms unfolding vrrestriction_def by simp

lemma app_vrrestrictionD[dest]: 
  assumes "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r \<restriction>\<^sup>r\<^sub>\<circ> A"  
  shows "b \<in>\<^sub>\<circ> A" and "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
  using assms unfolding vrrestriction_def by auto

lemma app_vrrestrictionE[elim]: 
  assumes "x \<in>\<^sub>\<circ> r \<restriction>\<^sup>r\<^sub>\<circ> A"
  obtains a b where "x = \<langle>a, b\<rangle>" and "b \<in>\<^sub>\<circ> A" and "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
  using assms unfolding vrrestriction_def by auto


text\<open>Set operations.\<close>

lemma vrrestriction_on_vempty[simp]: "r \<restriction>\<^sup>r\<^sub>\<circ> 0 = 0" 
  by (auto intro!: vsubset_antisym)

lemma vrrestriction_vempty[simp]: "0 \<restriction>\<^sup>r\<^sub>\<circ> A = 0" by auto

lemma vrrestriction_vsingleton_in[simp]: 
  assumes "b \<in>\<^sub>\<circ> A"
  shows "set {\<langle>a, b\<rangle>} \<restriction>\<^sup>r\<^sub>\<circ> A = set {\<langle>a, b\<rangle>}" 
  using assms by auto

lemma vrrestriction_vsingleton_nin[simp]: 
  assumes "b \<notin>\<^sub>\<circ> A"
  shows "set {\<langle>a, b\<rangle>} \<restriction>\<^sup>r\<^sub>\<circ> A = 0" 
  using assms by auto

lemma vrrestriction_mono: 
  assumes "A \<subseteq>\<^sub>\<circ> B"
  shows "r \<restriction>\<^sup>r\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> r \<restriction>\<^sup>r\<^sub>\<circ> B"
  using assms by auto

lemma vrrestriction_vinsert_nin[simp]:
  assumes "b \<notin>\<^sub>\<circ> A"
  shows "(vinsert \<langle>a, b\<rangle> r) \<restriction>\<^sup>r\<^sub>\<circ> A = r \<restriction>\<^sup>r\<^sub>\<circ> A" 
  using assms by auto

lemma vrrestriction_vinsert_in: 
  assumes "b \<in>\<^sub>\<circ> A"
  shows "(vinsert \<langle>a, b\<rangle> r) \<restriction>\<^sup>r\<^sub>\<circ> A = vinsert \<langle>a, b\<rangle> (r \<restriction>\<^sup>r\<^sub>\<circ> A)" 
  using assms by auto

lemma vrrestriction_vintersection: "(r \<inter>\<^sub>\<circ> s) \<restriction>\<^sup>r\<^sub>\<circ> A = r \<restriction>\<^sup>r\<^sub>\<circ> A \<inter>\<^sub>\<circ> s \<restriction>\<^sup>r\<^sub>\<circ> A" by auto

lemma vrrestriction_vunion: "(r \<union>\<^sub>\<circ> s) \<restriction>\<^sup>r\<^sub>\<circ> A = r \<restriction>\<^sup>r\<^sub>\<circ> A \<union>\<^sub>\<circ> s \<restriction>\<^sup>r\<^sub>\<circ> A" by auto

lemma vrrestriction_vdiff: "(r -\<^sub>\<circ> s) \<restriction>\<^sup>r\<^sub>\<circ> A = r \<restriction>\<^sup>r\<^sub>\<circ> A -\<^sub>\<circ> s \<restriction>\<^sup>r\<^sub>\<circ> A" by auto


text\<open>Connections.\<close>

lemma vrrestriction_vid_on[simp]: "(vid_on A) \<restriction>\<^sup>r\<^sub>\<circ> B = vid_on (A \<inter>\<^sub>\<circ> B)" by auto

lemma vrrestriction_vconst_on:
  assumes "c \<in>\<^sub>\<circ> B"
  shows "(vconst_on A c) \<restriction>\<^sup>r\<^sub>\<circ> B = vconst_on A c"  
  using assms by auto

lemma vrrestriction_vcomp[simp]: "(r \<circ>\<^sub>\<circ> s) \<restriction>\<^sup>r\<^sub>\<circ> A = (r \<restriction>\<^sup>r\<^sub>\<circ> A) \<circ>\<^sub>\<circ> s" by auto


text\<open>Previous connections.\<close>

lemma vcomp_vid_on_rel[simp]: "vid_on A \<circ>\<^sub>\<circ> r = r \<restriction>\<^sup>r\<^sub>\<circ> A" 
  by (auto intro!: vsubset_antisym)

lemma vcomp_vconst_on_rel: "(vconst_on A c) \<circ>\<^sub>\<circ> r = (vconst_on A c) \<circ>\<^sub>\<circ> (r \<restriction>\<^sup>r\<^sub>\<circ> A)"
  by auto

lemma vlrestriction_vconverse: "r\<inverse>\<^sub>\<circ> \<restriction>\<^sup>l\<^sub>\<circ> A = (r \<restriction>\<^sup>r\<^sub>\<circ> A)\<inverse>\<^sub>\<circ>" by auto

lemma vrrestriction_vconverse: "r\<inverse>\<^sub>\<circ> \<restriction>\<^sup>r\<^sub>\<circ> A = (r \<restriction>\<^sup>l\<^sub>\<circ> A)\<inverse>\<^sub>\<circ>" by auto


text\<open>Special properties.\<close>

lemma vrrestriction_vsubset_rel: "r \<restriction>\<^sup>r\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> r" by auto

lemma vrrestriction_vsubset_vpairs: "r \<restriction>\<^sup>r\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> vpairs r" by auto


subsubsection\<open>Restriction\<close>

definition vrestriction :: "V \<Rightarrow> V"
  where "vrestriction D = 
    VLambda D (\<lambda>\<langle>r, A\<rangle>. set {\<langle>a, b\<rangle> | a b. a \<in>\<^sub>\<circ> A \<and> b \<in>\<^sub>\<circ> A \<and> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r})"

abbreviation app_vrestriction :: "V \<Rightarrow> V \<Rightarrow> V" (infixr \<open>\<restriction>\<^sub>\<circ>\<close> 80)
  where "r \<restriction>\<^sub>\<circ> A \<equiv> vrestriction (set {\<langle>r, A\<rangle>}) \<lparr>\<langle>r, A\<rangle>\<rparr>"

lemma app_vrestriction_def: 
  "r \<restriction>\<^sub>\<circ> A = set {\<langle>a, b\<rangle> | a b. a \<in>\<^sub>\<circ> A \<and> b \<in>\<^sub>\<circ> A \<and> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}"
  unfolding vrestriction_def by simp

lemma vrestriction_small[simp]: 
  "small {\<langle>a, b\<rangle> | a b. a \<in>\<^sub>\<circ> A \<and> b \<in>\<^sub>\<circ> A \<and> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}"
  by (rule down[of _ r]) auto


text\<open>Rules.\<close>

lemma vrestrictionI[intro!]: 
  assumes "\<langle>r, A\<rangle> \<in>\<^sub>\<circ> D"
  shows "\<langle>\<langle>r, A\<rangle>, r \<restriction>\<^sub>\<circ> A\<rangle> \<in>\<^sub>\<circ> vrestriction D"
  using assms unfolding vrestriction_def by (simp add: VLambda_iff2)

lemma vrestrictionD[dest]: 
  assumes "\<langle>\<langle>r, A\<rangle>, s\<rangle> \<in>\<^sub>\<circ> vrestriction D" 
  shows "\<langle>r, A\<rangle> \<in>\<^sub>\<circ> D" and "s = r \<restriction>\<^sub>\<circ> A"
  using assms unfolding vrestriction_def by auto

lemma vrestrictionE[elim]: 
  assumes "x \<in>\<^sub>\<circ> vrestriction D" and "D \<subseteq>\<^sub>\<circ> R \<times>\<^sub>\<circ> X"
  obtains r A where "x = \<langle>\<langle>r, A\<rangle>, r \<restriction>\<^sub>\<circ> A\<rangle>" and "r \<in>\<^sub>\<circ> R" and "A \<in>\<^sub>\<circ> X"
  using assms unfolding vrestriction_def by auto

lemma app_vrestrictionI[intro!]: 
  assumes "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A" and "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" 
  shows "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r \<restriction>\<^sub>\<circ> A" 
  using assms unfolding vrestriction_def by simp

lemma app_vrestrictionD[dest]: 
  assumes "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r \<restriction>\<^sub>\<circ> A"  
  shows "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A" and "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
  using assms unfolding vrestriction_def by auto

lemma app_vrestrictionE[elim]:
  assumes "x \<in>\<^sub>\<circ> r \<restriction>\<^sub>\<circ> A"
  obtains a b where "x = \<langle>a, b\<rangle>" and "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A" and "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
  using assms unfolding vrestriction_def by clarsimp


text\<open>Set operations.\<close>

lemma vrestriction_on_vempty[simp]: "r \<restriction>\<^sub>\<circ> 0 = 0" 
  by (auto intro!: vsubset_antisym)

lemma vrestriction_vempty[simp]: "0 \<restriction>\<^sub>\<circ> A = 0" by auto

lemma vrestriction_vsingleton_in[simp]: 
  assumes "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A"
  shows "set {\<langle>a, b\<rangle>} \<restriction>\<^sub>\<circ> A = set {\<langle>a, b\<rangle>}" 
  using assms by auto

lemma vrestriction_vsingleton_nin_left[simp]: 
  assumes "a \<notin>\<^sub>\<circ> A"
  shows "set {\<langle>a, b\<rangle>} \<restriction>\<^sub>\<circ> A = 0" 
  using assms by auto

lemma vrestriction_vsingleton_nin_right[simp]: 
  assumes "b \<notin>\<^sub>\<circ> A"
  shows "set {\<langle>a, b\<rangle>} \<restriction>\<^sub>\<circ> A = 0" 
  using assms by auto

lemma vrestriction_mono: 
  assumes "A \<subseteq>\<^sub>\<circ> B"
  shows "r \<restriction>\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> r \<restriction>\<^sub>\<circ> B"
  using assms by auto

lemma vrestriction_vinsert_nin[simp]: 
  assumes "a \<notin>\<^sub>\<circ> A" and "b \<notin>\<^sub>\<circ> A"
  shows "(vinsert \<langle>a, b\<rangle> r) \<restriction>\<^sub>\<circ> A = r \<restriction>\<^sub>\<circ> A" 
  using assms by auto

lemma vrestriction_vinsert_in: 
  assumes "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A"
  shows "(vinsert \<langle>a, b\<rangle> r) \<restriction>\<^sub>\<circ> A = vinsert \<langle>a, b\<rangle> (r \<restriction>\<^sub>\<circ> A)" 
  using assms by auto

lemma vrestriction_vintersection: "(r \<inter>\<^sub>\<circ> s) \<restriction>\<^sub>\<circ> A = r \<restriction>\<^sub>\<circ> A \<inter>\<^sub>\<circ> s \<restriction>\<^sub>\<circ> A" by auto

lemma vrestriction_vunion: "(r \<union>\<^sub>\<circ> s) \<restriction>\<^sub>\<circ> A = r \<restriction>\<^sub>\<circ> A \<union>\<^sub>\<circ> s \<restriction>\<^sub>\<circ> A" by auto

lemma vrestriction_vdiff: "(r -\<^sub>\<circ> s) \<restriction>\<^sub>\<circ> A = r \<restriction>\<^sub>\<circ> A -\<^sub>\<circ> s \<restriction>\<^sub>\<circ> A" by auto


text\<open>Connections.\<close>

lemma vrestriction_vid_on[simp]: "(vid_on A) \<restriction>\<^sub>\<circ> B = vid_on (A \<inter>\<^sub>\<circ> B)" by auto

lemma vrestriction_vconst_on_ex:
  assumes "c \<in>\<^sub>\<circ> B"
  shows "(vconst_on A c) \<restriction>\<^sub>\<circ> B = vconst_on (A \<inter>\<^sub>\<circ> B) c"  
  using assms by auto

lemma vrestriction_vconst_on_nex:
  assumes "c \<notin>\<^sub>\<circ> B"
  shows "(vconst_on A c) \<restriction>\<^sub>\<circ> B = 0"  
  using assms by auto

lemma vrestriction_vcomp[simp]: "(r \<circ>\<^sub>\<circ> s) \<restriction>\<^sub>\<circ> A = (r \<restriction>\<^sup>r\<^sub>\<circ> A) \<circ>\<^sub>\<circ> (s \<restriction>\<^sup>l\<^sub>\<circ> A)" by auto

lemma vrestriction_vconverse: "r\<inverse>\<^sub>\<circ> \<restriction>\<^sub>\<circ> A = (r \<restriction>\<^sub>\<circ> A)\<inverse>\<^sub>\<circ>" by auto


text\<open>Previous connections.\<close>

lemma vrrestriction_vlrestriction[simp]: "(r \<restriction>\<^sup>r\<^sub>\<circ> A) \<restriction>\<^sup>l\<^sub>\<circ> A = r \<restriction>\<^sub>\<circ> A" by auto

lemma vlrestriction_vrrestriction[simp]: "(r \<restriction>\<^sup>l\<^sub>\<circ> A) \<restriction>\<^sup>r\<^sub>\<circ> A = r \<restriction>\<^sub>\<circ> A" by auto

lemma vrestriction_vlrestriction[simp]: "(r \<restriction>\<^sub>\<circ> A) \<restriction>\<^sup>l\<^sub>\<circ> A = r \<restriction>\<^sub>\<circ> A" by auto

lemma vrestriction_vrrestriction[simp]: "(r \<restriction>\<^sub>\<circ> A) \<restriction>\<^sup>r\<^sub>\<circ> A = r \<restriction>\<^sub>\<circ> A" by auto


text\<open>Special properties.\<close>

lemma vrestriction_vsubset_vpairs: "r \<restriction>\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> vpairs r" by auto

lemma vrestriction_vsubset_vtimes: "r \<restriction>\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> A \<times>\<^sub>\<circ> A" by auto

lemma vrestriction_vsubset_rel: "r \<restriction>\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> r" by auto



subsection\<open>Properties\<close>


subsubsection\<open>Domain\<close>

definition vdomain :: "V \<Rightarrow> V"
  where "vdomain D = (\<lambda>r\<in>\<^sub>\<circ>D. set {a. \<exists>b. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r})"

abbreviation app_vdomain :: "V \<Rightarrow> V" (\<open>\<D>\<^sub>\<circ>\<close>)
  where "\<D>\<^sub>\<circ> r \<equiv> vdomain (set {r}) \<lparr>r\<rparr>"

lemma app_vdomain_def: "\<D>\<^sub>\<circ> r = set {a. \<exists>b. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}"
  unfolding vdomain_def by simp

lemma vdomain_small[simp]: "small {a. \<exists>b. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}"
proof-
  have ss: "{a. \<exists>b. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r} \<subseteq> vfst ` elts r" using image_iff by fastforce
  have small: "small (vfst ` elts r)" by (rule replacement) simp
  show ?thesis by (rule smaller_than_small, rule small, rule ss)
qed


text\<open>Rules.\<close>

lemma vdomainI[intro!]: 
  assumes "r \<in>\<^sub>\<circ> A"
  shows "\<langle>r, \<D>\<^sub>\<circ> r\<rangle> \<in>\<^sub>\<circ> vdomain A"
  using assms unfolding vdomain_def by auto

lemma vdomainD[dest]: 
  assumes "\<langle>r, s\<rangle> \<in>\<^sub>\<circ> vdomain A"
  shows "r \<in>\<^sub>\<circ> A" and "s = \<D>\<^sub>\<circ> r"
  using assms unfolding vdomain_def by auto

lemma vdomainE[elim]: 
  assumes "x \<in>\<^sub>\<circ> vdomain A" 
  obtains r where "x = \<langle>r, \<D>\<^sub>\<circ> r\<rangle>" and "r \<in>\<^sub>\<circ> A"
  using assms unfolding vdomain_def by auto

lemma app_vdomainI[intro]:
  assumes "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
  shows "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  using assms unfolding vdomain_def by auto

lemma app_vdomainD[dest]: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  shows "\<exists>b. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" 
  using assms unfolding vdomain_def by auto

lemma app_vdomainE[elim]:
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  obtains b where "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
  using assms unfolding vdomain_def by clarsimp

lemma vdomain_iff: "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r \<longleftrightarrow> (\<exists>y. \<langle>a, y\<rangle> \<in>\<^sub>\<circ> r)" by auto


text\<open>Set operations.\<close>

lemma vdomain_vempty[simp]: "\<D>\<^sub>\<circ> 0 = 0" by (auto intro!: vsubset_antisym)

lemma vdomain_vsingleton[simp]: "\<D>\<^sub>\<circ> (set {\<langle>a, b\<rangle>}) = set {a}" by auto

lemma vdomain_vdoubleton[simp]: "\<D>\<^sub>\<circ> (set {\<langle>a, b\<rangle>, \<langle>c, d\<rangle>}) = set {a, c}" 
  by (auto simp: vinsert_set_insert_eq)

lemma vdomain_mono:
  assumes "r \<subseteq>\<^sub>\<circ> s"
  shows "\<D>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> s"
  using assms by blast

lemma vdomain_vinsert[simp]: "\<D>\<^sub>\<circ> (vinsert \<langle>a, b\<rangle> r) = vinsert a (\<D>\<^sub>\<circ> r)" 
  by (auto intro!: vsubset_antisym)

lemma vdomain_vunion: "\<D>\<^sub>\<circ> (A \<union>\<^sub>\<circ> B) = \<D>\<^sub>\<circ> A \<union>\<^sub>\<circ> \<D>\<^sub>\<circ> B" 
  by (auto intro!: vsubset_antisym)

lemma vdomain_vintersection_vsubset: "\<D>\<^sub>\<circ> (A \<inter>\<^sub>\<circ> B) \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> A \<inter>\<^sub>\<circ> \<D>\<^sub>\<circ> B" by auto

lemma vdomain_vdiff_vsubset: "\<D>\<^sub>\<circ> A -\<^sub>\<circ> \<D>\<^sub>\<circ> B \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> (A -\<^sub>\<circ> B)" by auto


text\<open>Connections.\<close>

lemma vdomain_vid_on[simp]: "\<D>\<^sub>\<circ> (vid_on A) = A" 
  by (auto intro!: vsubset_antisym)

lemma vdomain_vconst_on[simp]: "\<D>\<^sub>\<circ> (vconst_on A c) = A" 
  by (auto intro!: vsubset_antisym)

lemma vdomain_VLambda[simp]: "\<D>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>A. f a) = A" 
  by (auto intro!: vsubset_antisym)

lemma vdomain_vlrestriction: "\<D>\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<circ> A) = \<D>\<^sub>\<circ> r \<inter>\<^sub>\<circ> A" by auto


text\<open>Special properties.\<close>

lemma vdomain_vsubset_vtimes:
  assumes "vpairs r \<subseteq>\<^sub>\<circ> x \<times>\<^sub>\<circ> y"
  shows "\<D>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> x"
  using assms by auto


subsubsection\<open>Range\<close>

definition vrange :: "V \<Rightarrow> V"
  where "vrange D = (\<lambda>r\<in>\<^sub>\<circ>D. set {b. \<exists>a. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r})"

abbreviation app_vrange :: "V \<Rightarrow> V" (\<open>\<R>\<^sub>\<circ>\<close>)
  where "\<R>\<^sub>\<circ> r \<equiv> vrange (set {r}) \<lparr>r\<rparr>"

lemma app_vrange_def: "\<R>\<^sub>\<circ> r = set {b. \<exists>a. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}"
  unfolding vrange_def by simp

lemma vrange_small[simp]: "small {b. \<exists>a. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}"
proof-
  have ss: "{b. \<exists>a. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r} \<subseteq> vsnd ` elts r" using image_iff by fastforce
  have small: "small (vsnd ` elts r)" by (rule replacement) simp
  show ?thesis by (rule smaller_than_small, rule small, rule ss)
qed


text\<open>Rules.\<close>

lemma vrangeI[intro]: 
  assumes "r \<in>\<^sub>\<circ> A"
  shows "\<langle>r, \<R>\<^sub>\<circ> r\<rangle> \<in>\<^sub>\<circ> vrange A"
  using assms unfolding vrange_def by auto

lemma vrangeD[dest]: 
  assumes "\<langle>r, s\<rangle> \<in>\<^sub>\<circ> vrange A"
  shows "r \<in>\<^sub>\<circ> A" and "s = \<R>\<^sub>\<circ> r"
  using assms unfolding vrange_def by auto

lemma vrangeE[elim]: 
  assumes "x \<in>\<^sub>\<circ> vrange A" 
  obtains r where "x = \<langle>r, \<R>\<^sub>\<circ> r\<rangle>" and "r \<in>\<^sub>\<circ> A"
  using assms unfolding vrange_def by auto

lemma app_vrangeI[intro]: 
  assumes "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
  shows "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r"
  using assms unfolding vrange_def by auto

lemma app_vrangeD[dest]: 
  assumes "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r"
  shows "\<exists>a. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" 
  using assms unfolding vrange_def by simp

lemma app_vrangeE[elim]:
  assumes "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r"
  obtains a where "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
  using assms unfolding vrange_def by clarsimp

lemma vrange_iff: "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r \<longleftrightarrow> (\<exists>a. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r)" by auto


text\<open>Set operations.\<close>

lemma vrange_vempty[simp]: "\<R>\<^sub>\<circ> 0 = 0" by (auto intro!: vsubset_antisym)

lemma vrange_vsingleton[simp]: "\<R>\<^sub>\<circ> (set {\<langle>a, b\<rangle>}) = set {b}" by auto

lemma vrange_vdoubleton[simp]: "\<R>\<^sub>\<circ> (set {\<langle>a, b\<rangle>, \<langle>c, d\<rangle>}) = set {b, d}" 
  by (auto simp: vinsert_set_insert_eq)

lemma vrange_mono: 
  assumes "r \<subseteq>\<^sub>\<circ> s"
  shows "\<R>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> s"
  using assms by force

lemma vrange_vinsert[simp]: "\<R>\<^sub>\<circ> (vinsert \<langle>a, b\<rangle> r) = vinsert b (\<R>\<^sub>\<circ> r)" 
  by (auto intro!: vsubset_antisym)

lemma vrange_vunion: "\<R>\<^sub>\<circ> (r \<union>\<^sub>\<circ> s) = \<R>\<^sub>\<circ> r \<union>\<^sub>\<circ> \<R>\<^sub>\<circ> s" 
  by (auto intro!: vsubset_antisym)

lemma vrange_vintersection_vsubset: "\<R>\<^sub>\<circ> (r \<inter>\<^sub>\<circ> s) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> r \<inter>\<^sub>\<circ> \<R>\<^sub>\<circ> s" by auto

lemma vrange_vdiff_vsubset: "\<R>\<^sub>\<circ> r -\<^sub>\<circ> \<R>\<^sub>\<circ> s \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (r -\<^sub>\<circ> s)" by auto


text\<open>Connections.\<close>

lemma vrange_vid_on[simp]: "\<R>\<^sub>\<circ> (vid_on A) = A" by (auto intro!: vsubset_antisym)

lemma vrange_vconst_on_vempty[simp]: "\<R>\<^sub>\<circ> (vconst_on 0 c) = 0" by auto

lemma vrange_vconst_on_ne[simp]: 
  assumes "A \<noteq> 0"
  shows "\<R>\<^sub>\<circ> (vconst_on A c) = set {c}"
  using assms by (auto intro!: vsubset_antisym)

lemma vrange_VLambda: "\<R>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>A. f a) = set (f ` elts A)"
  by (intro vsubset_antisym vsubsetI) auto

lemma vrange_vrrestriction: "\<R>\<^sub>\<circ> (r \<restriction>\<^sup>r\<^sub>\<circ> A) = \<R>\<^sub>\<circ> r \<inter>\<^sub>\<circ> A" by auto


text\<open>Previous connections\<close>

lemma vdomain_vconverse[simp]: "\<D>\<^sub>\<circ> (r\<inverse>\<^sub>\<circ>) = \<R>\<^sub>\<circ> r" 
  by (auto intro!: vsubset_antisym)

lemma vrange_vconverse[simp]: "\<R>\<^sub>\<circ> (r\<inverse>\<^sub>\<circ>) = \<D>\<^sub>\<circ> r" 
  by (auto intro!: vsubset_antisym)


text\<open>Special properties.\<close>

lemma vrange_iff_vdomain: "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r \<longleftrightarrow> (\<exists>a\<in>\<^sub>\<circ>\<D>\<^sub>\<circ> r. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r)" by auto

lemma vrange_vsubset_vtimes:
  assumes "vpairs r \<subseteq>\<^sub>\<circ> x \<times>\<^sub>\<circ> y"
  shows "\<R>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> y"
  using assms by auto

lemma vrange_VLambda_vsubset:
  assumes "\<And>x. x \<in>\<^sub>\<circ> A \<Longrightarrow> f x \<in>\<^sub>\<circ> B"
  shows "\<R>\<^sub>\<circ> (VLambda A f) \<subseteq>\<^sub>\<circ> B"
  using assms by auto

lemma vpairs_vsubset_vdomain_vrange[simp]: "vpairs r \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> r \<times>\<^sub>\<circ> \<R>\<^sub>\<circ> r" 
  by (rule vsubsetI) auto

lemma vrange_vsubset:
  assumes "\<And>x y. \<langle>x, y\<rangle> \<in>\<^sub>\<circ> r \<Longrightarrow> y \<in>\<^sub>\<circ> A"
  shows "\<R>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> A"
  using assms by auto


subsubsection\<open>Field\<close>

definition vfield :: "V \<Rightarrow> V"
  where "vfield D = (\<lambda>r\<in>\<^sub>\<circ>D. \<D>\<^sub>\<circ> r \<union>\<^sub>\<circ> \<R>\<^sub>\<circ> r)"

abbreviation app_vfield :: "V \<Rightarrow> V" (\<open>\<F>\<^sub>\<circ>\<close>)
  where "\<F>\<^sub>\<circ> r \<equiv> vfield (set {r}) \<lparr>r\<rparr>"

lemma app_vfield_def: "\<F>\<^sub>\<circ> r = \<D>\<^sub>\<circ> r \<union>\<^sub>\<circ> \<R>\<^sub>\<circ> r" unfolding vfield_def by simp


text\<open>Rules.\<close>

lemma vfieldI[intro!]: 
  assumes "r \<in>\<^sub>\<circ> A"
  shows "\<langle>r, \<F>\<^sub>\<circ> r\<rangle> \<in>\<^sub>\<circ> vfield A"
  using assms unfolding vfield_def by auto

lemma vfieldD[dest]: 
  assumes "\<langle>r, s\<rangle> \<in>\<^sub>\<circ> vfield A"
  shows "r \<in>\<^sub>\<circ> A" and "s = \<F>\<^sub>\<circ> r"
  using assms unfolding vfield_def by auto

lemma vfieldE[elim]: 
  assumes "x \<in>\<^sub>\<circ> vfield A" 
  obtains r where "x = \<langle>r, \<F>\<^sub>\<circ> r\<rangle>" and "r \<in>\<^sub>\<circ> A"
  using assms unfolding vfield_def by auto

lemma app_vfieldI1[intro]: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r \<union>\<^sub>\<circ> \<R>\<^sub>\<circ> r"
  shows "a \<in>\<^sub>\<circ> \<F>\<^sub>\<circ> r"
  using assms unfolding vfield_def by simp

lemma app_vfieldI2[intro]: 
  assumes "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
  shows "a \<in>\<^sub>\<circ> \<F>\<^sub>\<circ> r"
  using assms by auto

lemma app_vfieldI3[intro]: 
  assumes "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
  shows "b \<in>\<^sub>\<circ> \<F>\<^sub>\<circ> r"
  using assms by auto

lemma app_vfieldD[dest]: 
  assumes "a \<in>\<^sub>\<circ> \<F>\<^sub>\<circ> r"
  shows "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r \<union>\<^sub>\<circ> \<R>\<^sub>\<circ> r"
  using assms unfolding vfield_def by simp

lemma app_vfieldE[elim]:  
  assumes "a \<in>\<^sub>\<circ> \<F>\<^sub>\<circ> r" and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r \<union>\<^sub>\<circ> \<R>\<^sub>\<circ> r \<Longrightarrow> P"
  shows P
  using assms by auto

lemma app_vfield_vpairE[elim]:
  assumes "a \<in>\<^sub>\<circ> \<F>\<^sub>\<circ> r"
  obtains b where "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r \<or> \<langle>b, a\<rangle> \<in>\<^sub>\<circ> r "
  using assms unfolding app_vfield_def by blast

lemma vfield_iff: "a \<in>\<^sub>\<circ> \<F>\<^sub>\<circ> r \<longleftrightarrow> (\<exists>b. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r \<or> \<langle>b, a\<rangle> \<in>\<^sub>\<circ> r)" by auto


text\<open>Set operations.\<close>

lemma vfield_vempty[simp]: "\<F>\<^sub>\<circ> 0 = 0" by (auto intro!: vsubset_antisym)

lemma vfield_vsingleton[simp]: "\<F>\<^sub>\<circ> (set {\<langle>a, b\<rangle>}) = set {a, b}" 
  by (simp add: app_vfield_def vinsert_set_insert_eq)

lemma vfield_vdoubleton[simp]: "\<F>\<^sub>\<circ> (set {\<langle>a, b\<rangle>, \<langle>c, d\<rangle>}) = set {a, b, c, d}" 
  by (auto simp: vinsert_set_insert_eq)

lemma vfield_mono:
  assumes "r \<subseteq>\<^sub>\<circ> s"
  shows "\<F>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> \<F>\<^sub>\<circ> s"
  using assms by fastforce

lemma vfield_vinsert[simp]: "\<F>\<^sub>\<circ> (vinsert \<langle>a, b\<rangle> r) = set {a, b} \<union>\<^sub>\<circ> \<F>\<^sub>\<circ> r"
  by (auto intro!: vsubset_antisym)

lemma vfield_vunion[simp]: "\<F>\<^sub>\<circ> (r \<union>\<^sub>\<circ> s) = \<F>\<^sub>\<circ> r \<union>\<^sub>\<circ> \<F>\<^sub>\<circ> s" 
  by (auto intro!: vsubset_antisym)


text\<open>Connections.\<close>

lemma vid_on_vfield[simp]: "\<F>\<^sub>\<circ> (vid_on A) = A" by (auto intro!: vsubset_antisym)

lemma vconst_on_vfield_ne[intro, simp]:
  assumes "A \<noteq> 0"
  shows "\<F>\<^sub>\<circ> (vconst_on A c) = vinsert c A" 
  using assms by (auto intro!: vsubset_antisym)

lemma vconst_on_vfield_vempty[simp]: "\<F>\<^sub>\<circ> (vconst_on 0 c) = 0" by auto

lemma vfield_vconverse[simp]: "\<F>\<^sub>\<circ> (r\<inverse>\<^sub>\<circ>) = \<F>\<^sub>\<circ> r" 
  by (auto intro!: vsubset_antisym)


subsubsection\<open>Image\<close>

definition vimage :: "V \<Rightarrow> V"
  where "vimage D = VLambda D (\<lambda>\<langle>r, A\<rangle>. \<R>\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<circ> A))"

abbreviation app_vimage :: "V \<Rightarrow> V \<Rightarrow> V" (infixr \<open>`\<^sub>\<circ>\<close> 90)
  where "r `\<^sub>\<circ> A \<equiv> vimage (set {\<langle>r, A\<rangle>}) \<lparr>\<langle>r, A\<rangle>\<rparr>"

lemma app_vimage_def: "r `\<^sub>\<circ> A = \<R>\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<circ> A)" unfolding vimage_def by simp

lemma vimage_small[simp]: "small {b. \<exists>a\<in>\<^sub>\<circ>A. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}"
proof-
  have ss: "{b. \<exists>a\<in>\<^sub>\<circ>A. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r} \<subseteq> vsnd ` elts r"
    using image_iff by fastforce
  have small: "small (vsnd ` elts r)" by (rule replacement) simp
  show ?thesis by (rule smaller_than_small, rule small, rule ss)
qed

lemma app_vimage_set_def: "r `\<^sub>\<circ> A = set {b. \<exists>a\<in>\<^sub>\<circ>A. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}"
  unfolding vimage_def vrange_def by auto


text\<open>Rules.\<close>

lemma vimageI[intro!]: 
  assumes "\<langle>r, A\<rangle> \<in>\<^sub>\<circ> D"
  shows "\<langle>\<langle>r, A\<rangle>, r `\<^sub>\<circ> A\<rangle> \<in>\<^sub>\<circ> vimage D"
  using assms unfolding vimage_def by (simp add: VLambda_iff2)

lemma vimageD[dest]: 
  assumes "\<langle>\<langle>r, A\<rangle>, s\<rangle> \<in>\<^sub>\<circ> vimage D" 
  shows "\<langle>r, A\<rangle> \<in>\<^sub>\<circ> D" and "s = r `\<^sub>\<circ> A"
  using assms unfolding vimage_def by auto

lemma vimageE[elim]: 
  assumes "x \<in>\<^sub>\<circ> vimage (R \<times>\<^sub>\<circ> X)"
  obtains r A where "x = \<langle>\<langle>r, A\<rangle>, r `\<^sub>\<circ> A\<rangle>" and "r \<in>\<^sub>\<circ> R" and "A \<in>\<^sub>\<circ> X"
  using assms unfolding vimage_def by auto

lemma app_vimageI1:
  assumes "x \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<circ> A)"
  shows "x \<in>\<^sub>\<circ> r `\<^sub>\<circ> A" 
  using assms unfolding vimage_def by simp

lemma app_vimageI2[intro]:
  assumes "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" and "a \<in>\<^sub>\<circ> A" 
  shows "b \<in>\<^sub>\<circ> r `\<^sub>\<circ> A"
  using assms app_vimageI1 by auto

lemma app_vimageD[dest]: 
  assumes "x \<in>\<^sub>\<circ> r `\<^sub>\<circ> A"
  shows "x \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<circ> A)"
  using assms unfolding vimage_def by simp

lemma app_vimageE[elim]:
  assumes "b \<in>\<^sub>\<circ> r `\<^sub>\<circ> A"
  obtains a where "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" and "a \<in>\<^sub>\<circ> A"
  using assms unfolding vimage_def by auto

lemma app_vimage_iff: "b \<in>\<^sub>\<circ> r `\<^sub>\<circ> A \<longleftrightarrow> (\<exists>a\<in>\<^sub>\<circ>A. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r)" by auto


text\<open>Set operations.\<close>

lemma vimage_vempty[simp]: "0 `\<^sub>\<circ> A = 0" by (auto intro!: vsubset_antisym)

lemma vimage_of_vempty[simp]: "r `\<^sub>\<circ> 0 = 0" by (auto intro!: vsubset_antisym)

lemma vimage_vsingleton: "r `\<^sub>\<circ> set {a} = set {b. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}"
proof-
  have "{b. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r} \<subseteq> {b. \<exists>a. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}" by auto
  then have [simp]: "small {b. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}" 
    by (rule smaller_than_small[OF vrange_small[of r]])
  show ?thesis using app_vimage_set_def by auto
qed

lemma vimage_vsingleton_in[intro, simp]: 
  assumes "a \<in>\<^sub>\<circ> A"
  shows "set {\<langle>a, b\<rangle>} `\<^sub>\<circ> A = set {b}" 
  using assms by auto

lemma vimage_vsingleton_nin[intro, simp]: 
  assumes "a \<notin>\<^sub>\<circ> A"
  shows "set {\<langle>a, b\<rangle>} `\<^sub>\<circ> A = 0" 
  using assms by auto

lemma vimage_vsingleton_vinsert[simp]: "set {\<langle>a, b\<rangle>} `\<^sub>\<circ> vinsert a A = set {b}" 
  by auto

lemma vimage_mono: 
  assumes "r' \<subseteq>\<^sub>\<circ> r" and "A' \<subseteq>\<^sub>\<circ> A"
  shows "(r' `\<^sub>\<circ> A') \<subseteq>\<^sub>\<circ> (r `\<^sub>\<circ> A)" 
  using assms by fastforce

lemma vimage_vinsert: "r `\<^sub>\<circ> (vinsert a A) = r `\<^sub>\<circ> set {a} \<union>\<^sub>\<circ> r `\<^sub>\<circ> A" 
  by (auto intro!: vsubset_antisym)

lemma vimage_vunion_left: "(r \<union>\<^sub>\<circ> s) `\<^sub>\<circ> A = r `\<^sub>\<circ> A \<union>\<^sub>\<circ> s `\<^sub>\<circ> A" 
  by (auto intro!: vsubset_antisym)

lemma vimage_vunion_right: "r `\<^sub>\<circ> (A \<union>\<^sub>\<circ> B) = r `\<^sub>\<circ> A \<union>\<^sub>\<circ> r `\<^sub>\<circ> B" 
  by (auto intro!: vsubset_antisym)

lemma vimage_vintersection: "r `\<^sub>\<circ> (A \<inter>\<^sub>\<circ> B) \<subseteq>\<^sub>\<circ> r `\<^sub>\<circ> A \<inter>\<^sub>\<circ> r `\<^sub>\<circ> B" by auto

lemma vimage_vdiff: "r `\<^sub>\<circ> A -\<^sub>\<circ> r `\<^sub>\<circ> B \<subseteq>\<^sub>\<circ> r `\<^sub>\<circ> (A -\<^sub>\<circ> B)" by auto


text\<open>Previous set operations.\<close>

lemma VPow_vinsert:
  "VPow (vinsert a A) = VPow A \<union>\<^sub>\<circ> ((\<lambda>x\<in>\<^sub>\<circ>VPow A. vinsert a x) `\<^sub>\<circ> VPow A)"
proof(intro vsubset_antisym vsubsetI)
  fix x assume "x \<in>\<^sub>\<circ> VPow (vinsert a A)"
  then have "x \<subseteq>\<^sub>\<circ> vinsert a A" by simp
  then consider "x \<subseteq>\<^sub>\<circ> A" | "a \<in>\<^sub>\<circ> x" by auto
  then show "x \<in>\<^sub>\<circ> VPow A \<union>\<^sub>\<circ> (\<lambda>x\<in>\<^sub>\<circ>VPow A. vinsert a x) `\<^sub>\<circ> VPow A"
  proof cases
    case 1 then show ?thesis by simp
  next
    case 2
    define x' where "x' = x -\<^sub>\<circ> set {a}"
    with 2 have "x = vinsert a x'" and "a \<notin>\<^sub>\<circ> x'" by auto
    with \<open>x \<subseteq>\<^sub>\<circ> vinsert a A\<close> show ?thesis
      unfolding vimage_def
      by (fastforce simp: vsubset_vinsert vlrestriction_VLambda)
  qed
qed (elim vunionE, auto)


text\<open>Special properties.\<close>

lemma vimage_vsingleton_iff[iff]: "b \<in>\<^sub>\<circ> r `\<^sub>\<circ> set {a} \<longleftrightarrow> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" by auto

lemma vimage_is_vempty[iff]: "r `\<^sub>\<circ> A = 0 \<longleftrightarrow> vdisjnt (\<D>\<^sub>\<circ> r) A" by fastforce

lemma vcomp_vimage_vtimes_right: 
  assumes "r `\<^sub>\<circ> Y = Z"
  shows "r \<circ>\<^sub>\<circ> (X \<times>\<^sub>\<circ> Y) = X \<times>\<^sub>\<circ> Z"
proof(intro vsubset_antisym vsubsetI)
  fix x assume x: "x \<in>\<^sub>\<circ> r \<circ>\<^sub>\<circ> (X \<times>\<^sub>\<circ> Y)"
  then obtain a c where x_def: "x = \<langle>a, c\<rangle>" and "a \<in>\<^sub>\<circ> X" and "c \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r" by auto
  with x obtain b where "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> X \<times>\<^sub>\<circ> Y" and "\<langle>b, c\<rangle> \<in>\<^sub>\<circ> r" by clarsimp
  then show "x \<in>\<^sub>\<circ> X \<times>\<^sub>\<circ> Z" unfolding x_def using assms by auto
next
  fix x assume "x \<in>\<^sub>\<circ> X \<times>\<^sub>\<circ> Z"
  then obtain a c where x_def: "x = \<langle>a, c\<rangle>" and "a \<in>\<^sub>\<circ> X" and "c \<in>\<^sub>\<circ> Z" by auto
  then show "x \<in>\<^sub>\<circ> r \<circ>\<^sub>\<circ> X \<times>\<^sub>\<circ> Y"
    using assms unfolding x_def by (meson VSigmaI app_vimageE vcompI)
qed


text\<open>Connections.\<close>

lemma vid_on_vimage[simp]: "vid_on A `\<^sub>\<circ> B = A \<inter>\<^sub>\<circ> B" 
  by (auto intro!: vsubset_antisym)

lemma vimage_vconst_on_ne[simp]: 
  assumes "B \<inter>\<^sub>\<circ> A \<noteq> 0"
  shows "vconst_on A c `\<^sub>\<circ> B = set {c}" 
  using assms by auto

lemma vimage_vconst_on_vempty[simp]: 
  assumes "vdisjnt A B"
  shows "vconst_on A c `\<^sub>\<circ> B = 0" 
  using assms by auto

lemma vimage_vconst_on_vsubset_vconst: "vconst_on A c `\<^sub>\<circ> B \<subseteq>\<^sub>\<circ> set {c}" by auto

lemma vimage_VLambda_vrange: "(\<lambda>a\<in>\<^sub>\<circ>A. f a) `\<^sub>\<circ> B = \<R>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>A \<inter>\<^sub>\<circ> B. f a)"
  unfolding vimage_def by (simp add: vlrestriction_VLambda)

lemma vimage_VLambda_vrange_rep: "(\<lambda>a\<in>\<^sub>\<circ>A. f a) `\<^sub>\<circ> A = \<R>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>A. f a)"
  by (simp add: vimage_VLambda_vrange)

lemma vcomp_vimage: "(r \<circ>\<^sub>\<circ> s) `\<^sub>\<circ> A = r `\<^sub>\<circ> (s `\<^sub>\<circ> A)" 
  by (auto intro!: vsubset_antisym)

lemma vimage_vlrestriction[simp]: "(r \<restriction>\<^sup>l\<^sub>\<circ> A) `\<^sub>\<circ> B = r `\<^sub>\<circ> (A \<inter>\<^sub>\<circ> B)" 
  by (auto intro!: vsubset_antisym)

lemma vimage_vrrestriction[simp]: "(r \<restriction>\<^sup>r\<^sub>\<circ> A) `\<^sub>\<circ> B = A \<inter>\<^sub>\<circ> r `\<^sub>\<circ> B" by auto

lemma vimage_vrestriction[simp]: "(r \<restriction>\<^sub>\<circ> A) `\<^sub>\<circ> B = A \<inter>\<^sub>\<circ> (r `\<^sub>\<circ> (A \<inter>\<^sub>\<circ> B))" by auto

lemma vimage_vdomain: "r `\<^sub>\<circ> \<D>\<^sub>\<circ> r = \<R>\<^sub>\<circ> r" by (auto intro!: vsubset_antisym)

lemma vimage_eq_imp_vcomp: 
  assumes "r `\<^sub>\<circ> A = s `\<^sub>\<circ> B"
  shows "(t \<circ>\<^sub>\<circ> r) `\<^sub>\<circ> A = (t \<circ>\<^sub>\<circ> s) `\<^sub>\<circ> B"
  using assms by (metis vcomp_vimage)


text\<open>Previous connections.\<close>

lemma vcomp_rel_vconst: "r \<circ>\<^sub>\<circ> (vconst_on A c) = A \<times>\<^sub>\<circ> (r `\<^sub>\<circ> set {c})" 
  by auto

lemma vcomp_VLambda:
  "(\<lambda>b\<in>\<^sub>\<circ>((\<lambda>a\<in>\<^sub>\<circ>A. g a) `\<^sub>\<circ> A). f b) \<circ>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>A. g a) = (\<lambda>a\<in>\<^sub>\<circ>A. (f \<circ> g) a)" 
  using VLambda_iff1 by (auto intro!: vsubset_antisym)+


text\<open>Further special properties.\<close>

lemma vimage_vsubset: 
  assumes "r \<subseteq>\<^sub>\<circ> A \<times>\<^sub>\<circ> B"
  shows "r `\<^sub>\<circ> C \<subseteq>\<^sub>\<circ> B" 
  using assms by auto

lemma vimage_vdomain_vsubset: "r `\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> r `\<^sub>\<circ> \<D>\<^sub>\<circ> r" by auto

lemma vdomain_vsubset_VUnion2: "\<D>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>r)"
proof(intro vsubsetI)
  fix x assume "x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  then obtain y where "\<langle>x, y\<rangle> \<in>\<^sub>\<circ> r" by auto
  then have "set {set {x}, set {x, y}} \<in>\<^sub>\<circ> r" unfolding vpair_def by auto
  with insert_commute have xy_Ur: "set {x, y} \<in>\<^sub>\<circ> \<Union>\<^sub>\<circ>r" 
    unfolding VUnion_iff by auto
  define Ur where "Ur = \<Union>\<^sub>\<circ>r"
  from xy_Ur show "x \<in>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>r)"
    unfolding Ur_def[symmetric] by (auto dest: VUnionI)
qed

lemma vrange_vsubset_VUnion2: "\<R>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>r)"
proof(intro vsubsetI)
  fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r"
  then obtain x where "\<langle>x, y\<rangle> \<in>\<^sub>\<circ> r" by auto
  then have "set {set {x}, set {x, y}} \<in>\<^sub>\<circ> r" unfolding vpair_def by auto
  with insert_commute have xy_Ur: "set {x, y} \<in>\<^sub>\<circ> \<Union>\<^sub>\<circ>r" 
    unfolding VUnion_iff by auto
  define Ur where "Ur = \<Union>\<^sub>\<circ>r"
  from xy_Ur show "y \<in>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>r)"
    unfolding Ur_def[symmetric] by (auto dest: VUnionI)
qed

lemma vfield_vsubset_VUnion2: "\<F>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>r)"
  using vdomain_vsubset_VUnion2 vrange_vsubset_VUnion2 
  by (auto simp: app_vfield_def)


subsubsection\<open>Inverse image\<close>

definition invimage :: "V \<Rightarrow> V"
  where "invimage D = VLambda D (\<lambda>\<langle>r, A\<rangle>. r\<inverse>\<^sub>\<circ> `\<^sub>\<circ> A)"

abbreviation app_invimage :: "V \<Rightarrow> V \<Rightarrow> V" (infixr \<open>-`\<^sub>\<circ>\<close> 90)
  where "r -`\<^sub>\<circ> A \<equiv> invimage (set {\<langle>r, A\<rangle>}) \<lparr>\<langle>r, A\<rangle>\<rparr>"

lemma app_invimage_def: "r -`\<^sub>\<circ> A = r\<inverse>\<^sub>\<circ> `\<^sub>\<circ> A" unfolding invimage_def by simp

lemma invimage_small[simp]: "small {a. \<exists>b\<in>\<^sub>\<circ>A. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}"
proof-
  have ss: "{a. \<exists>b\<in>\<^sub>\<circ>A. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r} \<subseteq> vfst ` elts r" 
    using image_iff by fastforce
  have small: "small (vfst ` elts r)" by (rule replacement) simp
  show ?thesis by (rule smaller_than_small, rule small, rule ss)
qed


text\<open>Rules.\<close>

lemma invimageI[intro!]: 
  assumes "\<langle>r, A\<rangle> \<in>\<^sub>\<circ> D"
  shows "\<langle>\<langle>r, A\<rangle>, r -`\<^sub>\<circ> A\<rangle> \<in>\<^sub>\<circ> invimage D"
  using assms unfolding invimage_def by (simp add: VLambda_iff2)

lemma invimageD[dest]: 
  assumes "\<langle>\<langle>r, A\<rangle>, s\<rangle> \<in>\<^sub>\<circ> invimage D" 
  shows "\<langle>r, A\<rangle> \<in>\<^sub>\<circ> D" and "s = r -`\<^sub>\<circ> A"
  using assms unfolding invimage_def by auto

lemma invimageE[elim]: 
  assumes "x \<in>\<^sub>\<circ> invimage D" and "D \<subseteq>\<^sub>\<circ> R \<times>\<^sub>\<circ> X"
  obtains r A where "x = \<langle>\<langle>r, A\<rangle>, r -`\<^sub>\<circ> A\<rangle>" and "r \<in>\<^sub>\<circ> R" and "A \<in>\<^sub>\<circ> X"
  using assms unfolding invimage_def by auto

lemma app_invimageI[intro]:
  assumes "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" and "b \<in>\<^sub>\<circ> A" 
  shows "a \<in>\<^sub>\<circ> r -`\<^sub>\<circ> A"
  using assms invimage_def by auto

lemma app_invimageD[dest]: 
  assumes "a \<in>\<^sub>\<circ> r -`\<^sub>\<circ> A"
  shows "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (r \<restriction>\<^sup>r\<^sub>\<circ> A)"
  using assms using invimage_def by auto

lemma app_invimageE[elim]:
  assumes "a \<in>\<^sub>\<circ> r -`\<^sub>\<circ> A"
  obtains b where "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" and "b \<in>\<^sub>\<circ> A"
  using assms unfolding invimage_def by auto

lemma app_invimageI1: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (r \<restriction>\<^sup>r\<^sub>\<circ> A)"
  shows "a \<in>\<^sub>\<circ> r -`\<^sub>\<circ> A" 
  using assms unfolding vimage_def 
  by (simp add: invimage_def app_vimageI1 vlrestriction_vconverse)

lemma app_invimageD1: 
  assumes "a \<in>\<^sub>\<circ> r -`\<^sub>\<circ> A"
  shows "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (r \<restriction>\<^sup>r\<^sub>\<circ> A)"
  using assms by fastforce
                                       
lemma app_invimageE1:
  assumes "a \<in>\<^sub>\<circ> r -`\<^sub>\<circ> A " and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (r \<restriction>\<^sup>r\<^sub>\<circ> A) \<Longrightarrow> P"
  shows P
  using assms unfolding invimage_def by auto

lemma app_invimageI2: 
  assumes "a \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<circ> `\<^sub>\<circ> A"
  shows "a \<in>\<^sub>\<circ> r -`\<^sub>\<circ> A" 
  using assms unfolding invimage_def by simp

lemma app_invimageD2:
  assumes "a \<in>\<^sub>\<circ> r -`\<^sub>\<circ> A"
  shows "a \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<circ> `\<^sub>\<circ> A"
  using assms unfolding invimage_def by simp

lemma app_invimageE2:
  assumes "a \<in>\<^sub>\<circ> r -`\<^sub>\<circ> A" and "a \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<circ> `\<^sub>\<circ> A \<Longrightarrow> P"
  shows P
  unfolding vimage_def by (simp add: assms app_invimageD2)

lemma invimage_iff: "a \<in>\<^sub>\<circ> r -`\<^sub>\<circ> A \<longleftrightarrow> (\<exists>b\<in>\<^sub>\<circ>A. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r)" by auto

lemma invimage_iff1: "a \<in>\<^sub>\<circ> r -`\<^sub>\<circ> A \<longleftrightarrow> a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (r \<restriction>\<^sup>r\<^sub>\<circ> A)" by auto

lemma invimage_iff2: "a \<in>\<^sub>\<circ> r -`\<^sub>\<circ> A \<longleftrightarrow> a \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<circ> `\<^sub>\<circ> A" by auto


text\<open>Set operations.\<close>

lemma invimage_vempty[simp]: "0 -`\<^sub>\<circ> A = 0" by (auto intro!: vsubset_antisym)

lemma invimage_of_vempty[simp]: "r -`\<^sub>\<circ> 0 = 0" by (auto intro!: vsubset_antisym)

lemma invimage_vsingleton_in[intro, simp]: 
  assumes "b \<in>\<^sub>\<circ> A"
  shows "set {\<langle>a, b\<rangle>} -`\<^sub>\<circ> A = set {a}" 
  using assms by auto

lemma invimage_vsingleton_nin[intro, simp]: 
  assumes "b \<notin>\<^sub>\<circ> A"
  shows "set {\<langle>a, b\<rangle>} -`\<^sub>\<circ> A = 0" 
  using assms by auto

lemma invimage_vsingleton_vinsert[intro, simp]: 
  "set {\<langle>a, b\<rangle>} -`\<^sub>\<circ> vinsert b A = set {a}" 
  by auto

lemma invimage_mono: 
  assumes "r' \<subseteq>\<^sub>\<circ> r" and "A' \<subseteq>\<^sub>\<circ> A"
  shows "(r' -`\<^sub>\<circ> A') \<subseteq>\<^sub>\<circ> (r -`\<^sub>\<circ> A)" 
  using assms by fastforce

lemma invimage_vinsert: "r -`\<^sub>\<circ> (vinsert a A) = r -`\<^sub>\<circ> set {a} \<union>\<^sub>\<circ> r -`\<^sub>\<circ> A" 
  by (auto intro!: vsubset_antisym)

lemma invimage_vunion_left: "(r \<union>\<^sub>\<circ> s) -`\<^sub>\<circ> A = r -`\<^sub>\<circ> A \<union>\<^sub>\<circ> s -`\<^sub>\<circ> A" 
  by (auto intro!: vsubset_antisym)

lemma invimage_vunion_right: "r -`\<^sub>\<circ> (A \<union>\<^sub>\<circ> B) = r -`\<^sub>\<circ> A \<union>\<^sub>\<circ> r -`\<^sub>\<circ> B" 
  by (auto intro!: vsubset_antisym)

lemma invimage_vintersection: "r -`\<^sub>\<circ> (A \<inter>\<^sub>\<circ> B) \<subseteq>\<^sub>\<circ> r -`\<^sub>\<circ> A \<inter>\<^sub>\<circ> r -`\<^sub>\<circ> B" by auto

lemma invimage_vdiff: "r -`\<^sub>\<circ> A -\<^sub>\<circ> r -`\<^sub>\<circ> B \<subseteq>\<^sub>\<circ> r -`\<^sub>\<circ> (A -\<^sub>\<circ> B)" by auto


text\<open>Special properties.\<close>

lemma invimage_set_def: "r -`\<^sub>\<circ> A = set {a. \<exists>b\<in>\<^sub>\<circ>A. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}" by fastforce

lemma invimage_eq_vdomain_vrestriction: "r -`\<^sub>\<circ> A = \<D>\<^sub>\<circ> (r \<restriction>\<^sup>r\<^sub>\<circ> A)" by fastforce

lemma invimage_vrange[simp]: "r -`\<^sub>\<circ> \<R>\<^sub>\<circ> r = \<D>\<^sub>\<circ> r"
  unfolding invimage_def by (auto intro!: vsubset_antisym)

lemma invimage_vrange_vsubset[simp]: 
  assumes "\<R>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> B"
  shows "r -`\<^sub>\<circ> B = \<D>\<^sub>\<circ> r"
  using assms unfolding app_invimage_def by (blast intro!: vsubset_antisym)


text\<open>Connections.\<close>

lemma invimage_vid_on[simp]: "vid_on A -`\<^sub>\<circ> B = A \<inter>\<^sub>\<circ> B" 
  by (auto intro!: vsubset_antisym)

lemma invimage_vconst_on_vsubset_vdomain[simp]: "vconst_on A c -`\<^sub>\<circ> B \<subseteq>\<^sub>\<circ> A" 
  unfolding invimage_def by auto

lemma invimage_vconst_on_ne[simp]: 
  assumes "c \<in>\<^sub>\<circ> B"
  shows "vconst_on A c -`\<^sub>\<circ> B = A" 
  by (simp add: assms invimage_eq_vdomain_vrestriction vrrestriction_vconst_on)

lemma invimage_vconst_on_vempty[simp]: 
  assumes "c \<notin>\<^sub>\<circ> B"
  shows "vconst_on A c -`\<^sub>\<circ> B = 0" 
  using assms by auto

lemma invimage_vcomp: "(r \<circ>\<^sub>\<circ> s) -`\<^sub>\<circ> x = s -`\<^sub>\<circ> (r -`\<^sub>\<circ> x) "
  by (simp add: invimage_def vconverse_vcomp vcomp_vimage)

lemma invimage_vconverse[simp]: "r\<inverse>\<^sub>\<circ> -`\<^sub>\<circ> A = r `\<^sub>\<circ> A" 
  by (auto intro!: vsubset_antisym)

lemma invimage_vlrestriction[simp]: "(r \<restriction>\<^sup>l\<^sub>\<circ> A) -`\<^sub>\<circ> B = A \<inter>\<^sub>\<circ> r -`\<^sub>\<circ> B" by auto

lemma invimage_vrrestriction[simp]: "(r \<restriction>\<^sup>r\<^sub>\<circ> A) -`\<^sub>\<circ> B = (r -`\<^sub>\<circ> (A \<inter>\<^sub>\<circ> B))" 
  by (auto intro!: vsubset_antisym)

lemma invimage_vrestriction[simp]: "(r \<restriction>\<^sub>\<circ> A) -`\<^sub>\<circ> B = A \<inter>\<^sub>\<circ> (r -`\<^sub>\<circ> (A \<inter>\<^sub>\<circ> B))" 
  by blast


text\<open>Previous connections.\<close>

lemma vcomp_vconst_on_rel_vtimes: "vconst_on A c \<circ>\<^sub>\<circ> r = (r -`\<^sub>\<circ> A) \<times>\<^sub>\<circ> set {c}"
proof(intro vsubset_antisym vsubsetI)
  fix x assume "x \<in>\<^sub>\<circ> r -`\<^sub>\<circ> A \<times>\<^sub>\<circ> set {c}" 
  then obtain a where x_def: "x = \<langle>a, c\<rangle>" and "a \<in>\<^sub>\<circ> r -`\<^sub>\<circ> A" by auto
  then obtain b where ab: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" and "b \<in>\<^sub>\<circ> A" using invimage_iff by auto
  with \<open>b \<in>\<^sub>\<circ> A\<close> show "x \<in>\<^sub>\<circ> vconst_on A c \<circ>\<^sub>\<circ> r" unfolding x_def by auto
qed auto

lemma vdomain_vcomp[simp]: "\<D>\<^sub>\<circ> (r \<circ>\<^sub>\<circ> s) = s -`\<^sub>\<circ> \<D>\<^sub>\<circ> r" by blast

lemma vrange_vcomp[simp]: "\<R>\<^sub>\<circ> (r \<circ>\<^sub>\<circ> s) = r `\<^sub>\<circ> \<R>\<^sub>\<circ> s" by blast

lemma vdomain_vcomp_vsubset:
  assumes "\<R>\<^sub>\<circ> s \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  shows "\<D>\<^sub>\<circ> (r \<circ>\<^sub>\<circ> s) = \<D>\<^sub>\<circ> s"
  using assms by simp



subsection\<open>Classification of relations\<close>


subsubsection\<open>Binary relation\<close>

locale vbrelation = 
  fixes r :: V
  assumes vbrelation: "vpairs r = r"


text\<open>Rules.\<close>

lemma vpairs_eqI[intro!]:
  assumes "\<And>x. x \<in>\<^sub>\<circ> r \<Longrightarrow> \<exists>a b. x = \<langle>a, b\<rangle>"
  shows "vpairs r = r"
  using assms by auto

lemma vpairs_eqD[dest]: 
  assumes "vpairs r = r"
  shows "\<And>x. x \<in>\<^sub>\<circ> r \<Longrightarrow> \<exists>a b. x = \<langle>a, b\<rangle>"
  using assms by auto

lemma vpairs_eqE[elim!]: 
  assumes "vpairs r = r" and "(\<And>x. x \<in>\<^sub>\<circ> r \<Longrightarrow> \<exists>a b. x = \<langle>a, b\<rangle>) \<Longrightarrow> P"
  shows P
  using assms by auto

lemmas vbrelationI[intro!] = vbrelation.intro 
lemmas vbrelationD[dest!] = vbrelation.vbrelation

lemma vbrelationE[elim!]: 
  assumes "vbrelation r" and "(vpairs r = r) \<Longrightarrow> P"
  shows P
  using assms unfolding vbrelation_def by auto

lemma vbrelationE1[elim]:
  assumes "vbrelation r" and "x \<in>\<^sub>\<circ> r" 
  obtains a b where "x = \<langle>a, b\<rangle>"
  using assms by auto

lemma vbrelationD1[dest]:
  assumes "vbrelation r" and "x \<in>\<^sub>\<circ> r" 
  shows "\<exists>a b. x = \<langle>a, b\<rangle>"
  using assms by auto

lemma (in vbrelation) vbrelation_vinE:
  assumes "x \<in>\<^sub>\<circ> r" 
  obtains a b where "x = \<langle>a, b\<rangle>" and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r"
  using assms vbrelation_axioms by blast


text\<open>Set operations.\<close>

lemma vbrelation_vsubset:
  assumes "vbrelation s" and "r \<subseteq>\<^sub>\<circ> s" 
  shows "vbrelation r"
  using assms by auto

lemma vbrelation_vinsert[simp]: "vbrelation (vinsert \<langle>a, b\<rangle> r) \<longleftrightarrow> vbrelation r"  
  by auto

lemma (in vbrelation) vbrelation_vinsertI[intro, simp]: 
  "vbrelation (vinsert \<langle>a, b\<rangle> r)"
  using vbrelation_axioms by auto

lemma vbrelation_vinsertD[dest]:
  assumes "vbrelation (vinsert \<langle>a, b\<rangle> r)"
  shows "vbrelation r"
  using assms by auto

lemma vbrelation_vunion: "vbrelation (r \<union>\<^sub>\<circ> s) \<longleftrightarrow> vbrelation r \<and> vbrelation s"
  by auto

lemma vbrelation_vunionI: 
  assumes "vbrelation r" and "vbrelation s"
  shows "vbrelation (r \<union>\<^sub>\<circ> s)"
  using assms by auto

lemma vbrelation_vunionD[dest]: 
  assumes "vbrelation (r \<union>\<^sub>\<circ> s)"
  shows "vbrelation r" and "vbrelation s"
  using assms by auto

lemma (in vbrelation) vbrelation_vintersectionI: "vbrelation (r \<inter>\<^sub>\<circ> s)"
  using vbrelation_axioms by auto

lemma (in vbrelation) vbrelation_vdiffI: "vbrelation (r -\<^sub>\<circ> s)"
  using vbrelation_axioms by auto


text\<open>Connections.\<close>

lemma vbrelation_vempty: "vbrelation 0" by auto

lemma vbrelation_vsingleton: "vbrelation (set {\<langle>a, b\<rangle>})" by auto

lemma vbrelation_vdoubleton: "vbrelation (set {\<langle>a, b\<rangle>, \<langle>c, d\<rangle>})" by auto

lemma vbrelation_vid_on[simp]: "vbrelation (vid_on A)" by auto

lemma vbrelation_vconst_on[simp]: "vbrelation (vconst_on A c)" by auto

lemma vbrelation_VLambda[simp]: "vbrelation (VLambda A f)"
  unfolding VLambda_def by (intro vbrelationI) auto
  
global_interpretation rel_VLambda: vbrelation \<open>VLambda U f\<close> 
  by (rule vbrelation_VLambda)

lemma vbrelation_vcomp: 
  assumes "vbrelation r" and "vbrelation s"
  shows "vbrelation (r \<circ>\<^sub>\<circ> s)" 
  using assms by auto

lemma (in vbrelation) vbrelation_vconverse: "vbrelation (r\<inverse>\<^sub>\<circ>)"
  using vbrelation_axioms by clarsimp

lemma vbrelation_vlrestriction[intro, simp]: "vbrelation (r \<restriction>\<^sup>l\<^sub>\<circ> A)" by auto

lemma vbrelation_vrrestriction[intro, simp]: "vbrelation (r \<restriction>\<^sup>r\<^sub>\<circ> A)" by auto

lemma vbrelation_vrestriction[intro, simp]: "vbrelation (r \<restriction>\<^sub>\<circ> A)" by auto


text\<open>Previous connections.\<close>

lemma (in vbrelation) vconverse_vconverse[simp]: "(r\<inverse>\<^sub>\<circ>)\<inverse>\<^sub>\<circ> = r"
  using vbrelation_axioms by auto

lemma vconverse_mono[simp]: 
  assumes "vbrelation r" and "vbrelation s"
  shows "r\<inverse>\<^sub>\<circ> \<subseteq>\<^sub>\<circ> s\<inverse>\<^sub>\<circ> \<longleftrightarrow> r \<subseteq>\<^sub>\<circ> s"
  using assms by (force intro: vconverse_vunion)+

lemma vconverse_inject[simp]: 
  assumes "vbrelation r" and "vbrelation s"
  shows "r\<inverse>\<^sub>\<circ> = s\<inverse>\<^sub>\<circ> \<longleftrightarrow> r = s"
  using assms by fast

lemma (in vbrelation) vconverse_vsubset_swap_2: 
  assumes "r\<inverse>\<^sub>\<circ> \<subseteq>\<^sub>\<circ> s"
  shows "r \<subseteq>\<^sub>\<circ> s\<inverse>\<^sub>\<circ>" 
  using assms vbrelation_axioms by auto

lemma (in vbrelation) vlrestriction_vdomain[simp]: "r \<restriction>\<^sup>l\<^sub>\<circ> \<D>\<^sub>\<circ> r = r"
  using vbrelation_axioms by (elim vbrelationE) auto

lemma (in vbrelation) vrrestriction_vrange[simp]: "r \<restriction>\<^sup>r\<^sub>\<circ> \<R>\<^sub>\<circ> r = r"
  using vbrelation_axioms by (elim vbrelationE) auto


text\<open>Special properties.\<close>

lemma brel_vsubset_vtimes:
  "vbrelation r \<longleftrightarrow> r \<subseteq>\<^sub>\<circ> set (vfst ` elts r) \<times>\<^sub>\<circ> set (vsnd ` elts r)"
  by force

lemma vsubset_vtimes_vbrelation: 
  assumes "r \<subseteq>\<^sub>\<circ> A \<times>\<^sub>\<circ> B"
  shows "vbrelation r" 
  using assms by auto

lemma (in vbrelation) vbrelation_vintersection_vdomain:
  assumes "vdisjnt (\<D>\<^sub>\<circ> r) (\<D>\<^sub>\<circ> s)"
  shows "vdisjnt r s"
proof(intro vsubset_antisym vsubsetI)
  fix x assume "x \<in>\<^sub>\<circ> r \<inter>\<^sub>\<circ> s"
  then obtain a b where "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r \<inter>\<^sub>\<circ> s"
    by (metis vbrelationE1 vbrelation_vintersectionI)
  with assms show "x \<in>\<^sub>\<circ> 0" by auto
qed simp

lemma (in vbrelation) vbrelation_vintersection_vrange:
  assumes "vdisjnt (\<R>\<^sub>\<circ> r) (\<R>\<^sub>\<circ> s)"
  shows "vdisjnt r s"
proof(intro vsubset_antisym vsubsetI)
  fix x assume "x \<in>\<^sub>\<circ> r \<inter>\<^sub>\<circ> s"
  then obtain a b where "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r \<inter>\<^sub>\<circ> s"
    by (metis vbrelationE1 vbrelation_vintersectionI)
  with assms show "x \<in>\<^sub>\<circ> 0" by auto
qed simp

lemma (in vbrelation) vbrelation_vintersection_vfield:
  assumes "vdisjnt (vfield r) (vfield s)"
  shows "vdisjnt r s"
proof(intro vsubset_antisym vsubsetI)
  fix x assume "x \<in>\<^sub>\<circ> r \<inter>\<^sub>\<circ> s"
  then obtain a b where "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r \<inter>\<^sub>\<circ> s"
    by (metis vbrelationE1 vbrelation_vintersectionI)
  with assms show "x \<in>\<^sub>\<circ> 0" by auto
qed auto

lemma (in vbrelation) vdomain_vrange_vtimes: "r \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> r \<times>\<^sub>\<circ> \<R>\<^sub>\<circ> r"
  using vbrelation by auto

lemma (in vbrelation) vbrelation_vsubset_vtimes:
  assumes "\<D>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> A" and "\<R>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> B"
  shows "r \<subseteq>\<^sub>\<circ> A \<times>\<^sub>\<circ> B"
proof(intro vsubsetI)
  fix x assume prems: "x \<in>\<^sub>\<circ> r"
  with vbrelation obtain a b where x_def: "x = \<langle>a, b\<rangle>" by auto
  from prems have a: "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and b: "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r" unfolding x_def by auto
  with assms have "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> B" by auto
  then show "x \<in>\<^sub>\<circ> A \<times>\<^sub>\<circ> B" unfolding x_def by simp
qed

lemma (in vbrelation) vlrestriction_vsubset_vrange[intro, simp]:
  assumes "\<D>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> A"
  shows "r \<restriction>\<^sup>l\<^sub>\<circ> A = r"
proof(intro vsubset_antisym)
  show "r \<subseteq>\<^sub>\<circ> r \<restriction>\<^sup>l\<^sub>\<circ> A"
    by (rule vlrestriction_mono[OF assms, of r, unfolded vlrestriction_vdomain])
qed auto

lemma (in vbrelation) vrrestriction_vsubset_vrange[intro, simp]:
  assumes "\<R>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> B"
  shows "r \<restriction>\<^sup>r\<^sub>\<circ> B = r"
proof(intro vsubset_antisym)
  show "r \<subseteq>\<^sub>\<circ> r \<restriction>\<^sup>r\<^sub>\<circ> B"
    by (rule vrrestriction_mono[OF assms, of r, unfolded vrrestriction_vrange])
qed auto

lemma (in vbrelation) vbrelation_vcomp_vid_on_left[simp]:
  assumes "\<R>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> A"
  shows "vid_on A \<circ>\<^sub>\<circ> r = r"
  using assms by auto

lemma (in vbrelation) vbrelation_vcomp_vid_on_right[simp]:
  assumes "\<D>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> A"
  shows "r \<circ>\<^sub>\<circ> vid_on A = r"
  using assms by auto


text\<open>Alternative forms of existing results.\<close>

lemmas [intro, simp] = vbrelation.vconverse_vconverse
  and [intro, simp] = vbrelation.vlrestriction_vsubset_vrange
  and [intro, simp] = vbrelation.vrrestriction_vsubset_vrange



subsubsection\<open>Simple single-valued relation\<close>

locale vsv = vbrelation r for r + 
  assumes vsv: "\<lbrakk> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r; \<langle>a, c\<rangle> \<in>\<^sub>\<circ> r \<rbrakk> \<Longrightarrow> b = c"


text\<open>Rules.\<close>

lemmas (in vsv) [intro] = vsv_axioms

mk_ide rf vsv_def[unfolded vsv_axioms_def]
  |intro vsvI[intro]| 
  |dest vsvD[dest]|
  |elim vsvE[elim]|


text\<open>Set operations.\<close>

lemma (in vsv) vsv_vinsert[simp]:
  assumes "a \<notin>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  shows "vsv (vinsert \<langle>a, b\<rangle> r)" 
  using assms vsv_axioms by blast

lemma vsv_vinsertD:
  assumes "vsv (vinsert x r)"
  shows "vsv r"
  using assms by (intro vsvI) auto

lemma vsv_vunion[intro, simp]:
  assumes "vsv r" and "vsv s" and "vdisjnt (\<D>\<^sub>\<circ> r) (\<D>\<^sub>\<circ> s)"
  shows "vsv (r \<union>\<^sub>\<circ> s)"
proof
  from assms have F: "\<lbrakk> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r; \<langle>a, c\<rangle> \<in>\<^sub>\<circ> s \<rbrakk> \<Longrightarrow> False" for a b c
    using elts_0 by blast
  fix a b c assume "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r \<union>\<^sub>\<circ> s" and "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> r \<union>\<^sub>\<circ> s" 
  then consider 
      "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r \<and> \<langle>a, c\<rangle> \<in>\<^sub>\<circ> r"
    | "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r \<and> \<langle>a, c\<rangle> \<in>\<^sub>\<circ> s"
    | "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> s \<and> \<langle>a, c\<rangle> \<in>\<^sub>\<circ> r"
    | "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> s \<and> \<langle>a, c\<rangle> \<in>\<^sub>\<circ> s"
    by blast
  then show "b = c" using assms by cases auto
qed (use assms in auto) 

lemma (in vsv) vsv_vintersection[intro, simp]: "vsv (r \<inter>\<^sub>\<circ> s)" 
  using vsv_axioms by blast

lemma (in vsv) vsv_vdiff[intro, simp]: "vsv (r -\<^sub>\<circ> s)" using vsv_axioms by blast


text\<open>Connections.\<close>

lemma vsv_vempty[simp]: "vsv 0" by auto

lemma vsv_vsingleton[simp]: "vsv (set {\<langle>a, b\<rangle>})" by auto

global_interpretation rel_vsingleton: vsv \<open>set {\<langle>a, b\<rangle>}\<close>
  by (rule vsv_vsingleton)

lemma vsv_vdoubleton: 
  assumes "a \<noteq> c"
  shows "vsv (set {\<langle>a, b\<rangle>, \<langle>c, d\<rangle>})" 
  using assms by (auto simp: vinsert_set_insert_eq)

lemma vsv_vid_on[simp]: "vsv (vid_on A)" by auto

lemma vsv_vconst_on[simp]: "vsv (vconst_on A c)" by auto

lemma vsv_VLambda[simp]: "vsv (\<lambda>a\<in>\<^sub>\<circ>A. f a)" by auto

global_interpretation rel_VLambda: vsv \<open>(\<lambda>a\<in>\<^sub>\<circ>A. f a)\<close>
  unfolding VLambda_def by (intro vsvI) auto

lemma vsv_vcomp: 
  assumes "vsv r" and "vsv s"
  shows "vsv (r \<circ>\<^sub>\<circ> s)" 
  using assms
  by (intro vsvI; elim vsvE) (simp add: vbrelation_vcomp, metis vcompD)

lemma (in vsv) vsv_vlrestriction[intro, simp]: "vsv (r \<restriction>\<^sup>l\<^sub>\<circ> A)" 
  using vsv_axioms by blast

lemma (in vsv) vsv_vrrestriction[intro, simp]: "vsv (r \<restriction>\<^sup>r\<^sub>\<circ> A)" 
  using vsv_axioms by blast

lemma (in vsv) vsv_vrestriction[intro, simp]: "vsv (r \<restriction>\<^sub>\<circ> A)" 
  using vsv_axioms by blast


text\<open>Special properties.\<close>

lemma small_vsv[simp]: "small {f. vsv f \<and> \<D>\<^sub>\<circ> f = A \<and> \<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> B}"
proof-
  have "small {f. f \<subseteq>\<^sub>\<circ> A \<times>\<^sub>\<circ> B}" by (auto simp: small_iff)
  moreover have "{f. vsv f \<and> \<D>\<^sub>\<circ> f = A \<and> \<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> B} \<subseteq> {f. f \<subseteq>\<^sub>\<circ> A \<times>\<^sub>\<circ> B}"
    by auto
  ultimately show "small {f. vsv f \<and> \<D>\<^sub>\<circ> f = A \<and> \<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> B}" 
    by (auto simp: smaller_than_small)
qed

context vsv
begin

lemma vsv_ex1: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  shows "\<exists>!b. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
  using vsv_axioms assms by auto

lemma vsv_ex1_app1: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  shows "b = r\<lparr>a\<rparr> \<longleftrightarrow> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
proof 
  assume b_def: "b = r\<lparr>a\<rparr>" show "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" 
    unfolding app_def b_def by (rule theI') (rule vsv_ex1[OF assms])
next
  assume [simp]: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
  from assms vsv_axioms vsvD have THE_b: "(THE y. \<langle>a, y\<rangle> \<in>\<^sub>\<circ> r) = b" by auto
  show "b = r\<lparr>a\<rparr>" unfolding app_def THE_b[symmetric] by (rule refl)  
qed

lemma vsv_ex1_app2[iff]: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  shows "r\<lparr>a\<rparr> = b \<longleftrightarrow> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
  using vsv_ex1_app1[OF assms] by auto

lemma vsv_appI[intro, simp]: 
  assumes "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
  shows "r\<lparr>a\<rparr> = b" 
  using assms by (subgoal_tac \<open>a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r\<close>) auto

lemma vsv_appE:
  assumes "r\<lparr>a\<rparr> = b" and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r \<Longrightarrow> P"
  shows P
  using assms vsv_ex1_app1 by blast

lemma vdomain_vrange_is_vempty: "\<D>\<^sub>\<circ> r = 0 \<longleftrightarrow> \<R>\<^sub>\<circ> r = 0" by fastforce

lemma vsv_vrange_vempty: 
  assumes "\<R>\<^sub>\<circ> r = 0"
  shows "r = 0"
  using assms vdomain_vrange_is_vempty vlrestriction_vdomain by auto

lemma vsv_vdomain_vempty_vrange_vempty:
  assumes "\<D>\<^sub>\<circ> r \<noteq> 0"
  shows "\<R>\<^sub>\<circ> r \<noteq> 0"
  using assms by fastforce

lemma vsv_vdomain_vsingleton_vrange_vsingleton:
  assumes "\<D>\<^sub>\<circ> r = set {a}"
  obtains b where "\<R>\<^sub>\<circ> r = set {b}"
proof-
  from assms obtain b where ab: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" by auto
  then have "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> r \<Longrightarrow> c = b" for c by (auto simp: vsv)
  moreover with assms have "\<langle>b, c\<rangle> \<in>\<^sub>\<circ> r \<Longrightarrow> c = a" for c by force
  ultimately have "\<langle>c, d\<rangle> \<in>\<^sub>\<circ> r \<Longrightarrow> d = b" for c d
    by (metis app_vdomainI assms vsingletonD)
  with ab have "\<R>\<^sub>\<circ> r = set {b}" by blast
  with that show ?thesis by simp
qed

lemma vsv_vsubset_vimageE:
  assumes "B \<subseteq>\<^sub>\<circ> r `\<^sub>\<circ> A"
  obtains C where "C \<subseteq>\<^sub>\<circ> A" and "B = r `\<^sub>\<circ> C"
proof-
  define C where C_def: "C = (r\<inverse>\<^sub>\<circ> `\<^sub>\<circ> B) \<inter>\<^sub>\<circ> A"
  then have "C \<subseteq>\<^sub>\<circ> A" by auto
  moreover have "B = r `\<^sub>\<circ> C"
    unfolding C_def
  proof(intro vsubset_antisym vsubsetI)
    fix b assume "b \<in>\<^sub>\<circ> B"
    with assms obtain a where "a \<in>\<^sub>\<circ> A" and "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" 
      using app_vimageE vsubsetD by metis
    then have "a \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<circ> `\<^sub>\<circ> B \<inter>\<^sub>\<circ> A" by (auto simp: \<open>b \<in>\<^sub>\<circ> B\<close>)
    then show "b \<in>\<^sub>\<circ> r `\<^sub>\<circ> (r\<inverse>\<^sub>\<circ> `\<^sub>\<circ> B \<inter>\<^sub>\<circ> A)" by (auto intro: \<open>\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r\<close>)
  qed (use vsv_axioms in auto)
  ultimately show ?thesis using that by auto
qed

lemma vsv_vimage_eqI[intro]:
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "r\<lparr>a\<rparr> = b" and "a \<in>\<^sub>\<circ> A"
  shows "b \<in>\<^sub>\<circ> r `\<^sub>\<circ> A"
  using assms(2)[unfolded vsv_ex1_app2[OF assms(1)]] assms(3) by auto

lemma vsv_vimageI1: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "a \<in>\<^sub>\<circ> A" 
  shows "r\<lparr>a\<rparr> \<in>\<^sub>\<circ> r `\<^sub>\<circ> A"
  using assms by (simp add: vsv_vimage_eqI)

lemma vsv_vimageI2: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  shows "r\<lparr>a\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r"
  using assms by (blast dest: vsv_ex1_app1)

lemma vsv_vimageI2':
  assumes "b = r\<lparr>a\<rparr>" and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  shows "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r"
  using assms by (blast dest: vsv_ex1_app1)

lemma vsv_value: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  obtains b where "r\<lparr>a\<rparr> = b" and "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r"
  using assms by (blast dest: vsv_ex1_app1)

lemma vsv_vimageE:
  assumes "b \<in>\<^sub>\<circ> r `\<^sub>\<circ> A"
  obtains x where "r\<lparr>x\<rparr> = b" and "x \<in>\<^sub>\<circ> A"
  using assms vsv_axioms vsv_ex1_app2 by blast

lemma vsv_vimage_iff: "b \<in>\<^sub>\<circ> r `\<^sub>\<circ> A \<longleftrightarrow> (\<exists>a. a \<in>\<^sub>\<circ> A \<and> a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r \<and> r\<lparr>a\<rparr> = b)"
  using vsv_axioms by (blast intro: vsv_ex1_app1[THEN iffD1])+

lemma vsv_vimage_vsingleton:
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  shows "r `\<^sub>\<circ> set {a} = set {r\<lparr>a\<rparr>}"
  using assms by force

lemma vsv_vimage_vsubsetI: 
  assumes "\<And>a. \<lbrakk> a \<in>\<^sub>\<circ> A; a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r \<rbrakk> \<Longrightarrow> r\<lparr>a\<rparr> \<in>\<^sub>\<circ> B" 
  shows "r `\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> B"
  using assms by (metis vsv_vimage_iff vsubsetI)

lemma vsv_image_vsubset_iff: 
  "r `\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> B \<longleftrightarrow> (\<forall>a\<in>\<^sub>\<circ>A. a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r \<longrightarrow> r\<lparr>a\<rparr> \<in>\<^sub>\<circ> B)"
  by (auto simp: vsv_vimage_iff)

lemma vsv_vimage_vinsert:
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  shows "r `\<^sub>\<circ> vinsert a A = vinsert (r\<lparr>a\<rparr>) (r `\<^sub>\<circ> A)"
  using assms vsv_vimage_iff by (intro vsubset_antisym vsubsetI) auto  

lemma vsv_vinsert_vimage[intro, simp]: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "a \<in>\<^sub>\<circ> A" 
  shows "vinsert (r\<lparr>a\<rparr>) (r `\<^sub>\<circ> A) = r `\<^sub>\<circ> A"
  using assms by auto

lemma vsv_is_VLambda[simp]: "(\<lambda>x\<in>\<^sub>\<circ>\<D>\<^sub>\<circ> r. r\<lparr>x\<rparr>) = r"
  using vbrelation 
  by (auto simp: app_vdomainI VLambda_iff2 intro!: vsubset_antisym)

lemma vsv_is_VLambda_on_vlrestriction[intro, simp]: 
  assumes "A \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  shows "(\<lambda>x\<in>\<^sub>\<circ>A. r\<lparr>x\<rparr>) = r \<restriction>\<^sup>l\<^sub>\<circ> A"
  using assms by (force simp: VLambda_iff2)+

lemma pairwise_vimageI:
  assumes "\<And>x y. 
    \<lbrakk> x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r; y \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r; x \<noteq> y; r\<lparr>x\<rparr> \<noteq> r\<lparr>y\<rparr> \<rbrakk> \<Longrightarrow> P (r\<lparr>x\<rparr>) (r\<lparr>y\<rparr>)"
  shows "vpairwise P (\<R>\<^sub>\<circ> r)"
  by (intro vpairwiseI) (metis assms app_vdomainI app_vrangeE vsv_appI)

lemma vsv_vrange_vsubset:
  assumes "\<And>x. x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r \<Longrightarrow> r\<lparr>x\<rparr> \<in>\<^sub>\<circ> A"
  shows "\<R>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> A"
  using assms by fastforce

lemma vsv_vlrestriction_vinsert:
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  shows "r \<restriction>\<^sup>l\<^sub>\<circ> vinsert a A = vinsert \<langle>a, r\<lparr>a\<rparr>\<rangle> (r \<restriction>\<^sup>l\<^sub>\<circ> A)"  
  using assms by (auto intro!: vsubset_antisym)

end

lemma vsv_eqI: 
  assumes "vsv r" 
    and "vsv s"
    and "\<D>\<^sub>\<circ> r = \<D>\<^sub>\<circ> s" 
    and "\<And>a. a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r \<Longrightarrow> r\<lparr>a\<rparr> = s\<lparr>a\<rparr>"
  shows "r = s"
proof(intro vsubset_antisym vsubsetI)
  interpret r: vsv r by (rule assms(1))
  interpret s: vsv s by (rule assms(2))
  fix x assume "x \<in>\<^sub>\<circ> r"
  then obtain a b where x_def[simp]: "x = \<langle>a, b\<rangle>" and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" 
    by (elim r.vbrelation_vinE)
  with \<open>x \<in>\<^sub>\<circ> r\<close> have "r\<lparr>a\<rparr> = b" by simp
  with assms \<open>a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r\<close> show "x \<in>\<^sub>\<circ> s" by fastforce
next
  interpret r: vsv r by (rule assms(1))
  interpret s: vsv s by (rule assms(2))
  fix x assume "x \<in>\<^sub>\<circ> s"
  with assms(2) obtain a b where x_def[simp]: "x = \<langle>a, b\<rangle>" and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> s" 
    by (elim vsvE) blast
  with assms \<open>x \<in>\<^sub>\<circ> s\<close> have "s\<lparr>a\<rparr> = b" by blast
  with assms \<open>a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> s\<close> show "x \<in>\<^sub>\<circ> r" by fastforce
qed

lemma (in vsv) vsv_VLambda_cong: 
  assumes "\<And>a. a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r \<Longrightarrow> r\<lparr>a\<rparr> = f a"
  shows "(\<lambda>a\<in>\<^sub>\<circ>\<D>\<^sub>\<circ> r. f a) = r"
proof(rule vsv_eqI[symmetric])
  show "\<D>\<^sub>\<circ> r = \<D>\<^sub>\<circ> (VLambda (\<D>\<^sub>\<circ> r) f)" by simp
  fix a assume a: "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  then show "r\<lparr>a\<rparr> = VLambda (\<D>\<^sub>\<circ> r) f \<lparr>a\<rparr>" using assms(1)[OF a] by auto
qed auto

lemma Axiom_of_Choice:
  obtains f where "\<And>x. x \<in>\<^sub>\<circ> A \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> f\<lparr>x\<rparr> \<in>\<^sub>\<circ> x" and "vsv f"
proof-
  obtain f where f: "x \<in>\<^sub>\<circ> A \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> f\<lparr>x\<rparr> \<in>\<^sub>\<circ> x" for x
    by (metis beta vemptyE)
  define f' where "f' = (\<lambda>x\<in>\<^sub>\<circ>A. f\<lparr>x\<rparr>)"
  have "x \<in>\<^sub>\<circ> A \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> f'\<lparr>x\<rparr> \<in>\<^sub>\<circ> x" for x
    unfolding f'_def using f by simp
  moreover have "vsv f'" unfolding f'_def by simp
  ultimately show ?thesis using that by auto
qed

lemma VLambda_eqI:
  assumes "X = Y" and "\<And>x. x \<in>\<^sub>\<circ> X \<Longrightarrow> f x = g x"
  shows "(\<lambda>x\<in>\<^sub>\<circ>X. f x) = (\<lambda>y\<in>\<^sub>\<circ>Y. g y)"
proof(rule vsv_eqI, unfold vdomain_VLambda; (intro assms(1) vsv_VLambda)?)
  fix x assume "x \<in>\<^sub>\<circ> X"
  with assms show "VLambda X f\<lparr>x\<rparr> = VLambda Y g\<lparr>x\<rparr>" by simp
qed

lemma VLambda_vsingleton_def: "(\<lambda>i\<in>\<^sub>\<circ>set {j}. f i) = (\<lambda>i\<in>\<^sub>\<circ>set {j}. f j)" by auto


text\<open>Alternative forms of the available results.\<close>

lemmas [iff] = vsv.vsv_ex1_app2
  and [intro, simp] = vsv.vsv_appI
  and [elim] = vsv.vsv_appE
  and [intro] = vsv.vsv_vimage_eqI
  and [simp] = vsv.vsv_vinsert_vimage
  and [intro] = vsv.vsv_is_VLambda_on_vlrestriction
  and [simp] = vsv.vsv_is_VLambda
  and [intro, simp] = vsv.vsv_vintersection
  and [intro, simp] = vsv.vsv_vdiff
  and [intro, simp] = vsv.vsv_vlrestriction
  and [intro, simp] = vsv.vsv_vrrestriction
  and [intro, simp] = vsv.vsv_vrestriction


subsubsection\<open>Specialization of existing properties to single-valued relations.\<close>


text\<open>Identity relation.\<close>

lemma vid_on_eq_atI[intro, simp]: 
  assumes "a = b" and "a \<in>\<^sub>\<circ> A"
  shows "vid_on A \<lparr>a\<rparr> = b"
  using assms by auto

lemma vid_on_atI[intro, simp]: 
  assumes "a \<in>\<^sub>\<circ> A"
  shows "vid_on A \<lparr>a\<rparr> = a"
  using assms by auto

lemma vid_on_at_iff[intro, simp]:
  assumes "a \<in>\<^sub>\<circ> A"
  shows "vid_on A \<lparr>a\<rparr> = b \<longleftrightarrow> a = b" 
  using assms by auto


text\<open>Constant function.\<close>

lemma vconst_on_atI[simp]: 
  assumes "a \<in>\<^sub>\<circ> A"
  shows "vconst_on A c \<lparr>a\<rparr> = c"
  using assms by auto


text\<open>Composition.\<close>

lemma vcomp_atI[intro, simp]: 
  assumes "vsv r" 
    and "vsv s" 
    and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" 
    and "b \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> s" 
    and "s\<lparr>b\<rparr> = c" 
    and "r\<lparr>a\<rparr> = b" 
  shows "(s \<circ>\<^sub>\<circ> r)\<lparr>a\<rparr> = c"
  using assms by (auto simp: app_invimageI intro!: vsv_vcomp)

lemma vcomp_atD[dest]: 
  assumes "(s \<circ>\<^sub>\<circ> r)\<lparr>a\<rparr> = c"
    and "vsv r" 
    and "vsv s"  
    and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" 
    and "r\<lparr>a\<rparr> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> s" 
  shows "\<exists>b. s\<lparr>b\<rparr> = c \<and> r\<lparr>a\<rparr> = b" 
  using assms by (metis vcomp_atI)

lemma vcomp_atE1: 
  assumes "(s \<circ>\<^sub>\<circ> r)\<lparr>a\<rparr> = c"
    and "vsv r" 
    and "vsv s" 
    and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
    and "r\<lparr>a\<rparr> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> s"
    and "\<exists>b. s\<lparr>b\<rparr> = c \<and> r\<lparr>a\<rparr> = b \<Longrightarrow> P"  
  shows P
  using assms assms vcomp_atD by blast

lemma vcomp_atE[elim]:
  assumes "(s \<circ>\<^sub>\<circ> r)\<lparr>a\<rparr> = c"
    and "vsv r" 
    and "vsv s"  
    and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" 
    and "r\<lparr>a\<rparr> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> s"
  obtains b where "r\<lparr>a\<rparr> = b" and "s\<lparr>b\<rparr> = c"
  using assms that by (force elim!: vcomp_atE1)

lemma vsv_vcomp_at[simp]:
  assumes "vsv r" and "vsv s" and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "r\<lparr>a\<rparr> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> s"
  shows "(s \<circ>\<^sub>\<circ> r)\<lparr>a\<rparr> = s\<lparr>r\<lparr>a\<rparr>\<rparr>"
  using assms by auto

context vsv
begin


text\<open>Converse relation.\<close>

lemma vconverse_atI[intro]: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "r\<lparr>a\<rparr> = b" 
  shows "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<circ>"
  using assms by auto

lemma vconverse_atD[dest]: 
  assumes "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<circ>"
  shows "r\<lparr>a\<rparr> = b" 
  using assms by auto

lemma vconverse_atE[elim]: 
  assumes "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<circ>" and "r\<lparr>a\<rparr> = b \<Longrightarrow> P" 
  shows P
  using assms by auto

lemma vconverse_iff: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  shows "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<circ> \<longleftrightarrow> r\<lparr>a\<rparr> = b" 
  using assms by auto


text\<open>Left restriction.\<close>

interpretation vlrestriction: vsv \<open>r \<restriction>\<^sup>l\<^sub>\<circ> A\<close> by (rule vsv_vlrestriction)

lemma vlrestriction_atI[intro, simp]: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "a \<in>\<^sub>\<circ> A" and "r\<lparr>a\<rparr> = b" 
  shows "(r \<restriction>\<^sup>l\<^sub>\<circ> A)\<lparr>a\<rparr> = b"
  using assms by (auto simp: vdomain_vlrestriction)

lemma vlrestriction_atD[dest]: 
  assumes "(r \<restriction>\<^sup>l\<^sub>\<circ> A)\<lparr>a\<rparr> = b" and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "a \<in>\<^sub>\<circ> A"
  shows "r\<lparr>a\<rparr> = b"
  using assms by (auto simp: vdomain_vlrestriction)

lemma vlrestriction_atE1[elim]: 
  assumes "(r \<restriction>\<^sup>l\<^sub>\<circ> A)\<lparr>a\<rparr> = b" 
    and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
    and "a \<in>\<^sub>\<circ> A"
    and "r\<lparr>a\<rparr> = b \<Longrightarrow> P"
  shows P
  using assms vlrestrictionD by blast

lemma vlrestriction_atE2[elim]: 
  assumes "x \<in>\<^sub>\<circ> r \<restriction>\<^sup>l\<^sub>\<circ> A"
  obtains a b where "x = \<langle>a, b\<rangle>" and "a \<in>\<^sub>\<circ> A" and "r\<lparr>a\<rparr> = b"
  using assms by auto


text\<open>Right restriction.\<close>

interpretation vrrestriction: vsv \<open>r \<restriction>\<^sup>r\<^sub>\<circ> A\<close> by (rule vsv_vrrestriction)

lemma vrrestriction_atI[intro, simp]: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "b \<in>\<^sub>\<circ> A" and "r\<lparr>a\<rparr> = b" 
  shows "(r \<restriction>\<^sup>r\<^sub>\<circ> A)\<lparr>a\<rparr> = b" 
  using assms by (auto simp: app_vrrestrictionI)

lemma vrrestriction_atD[dest]: 
  assumes "(r \<restriction>\<^sup>r\<^sub>\<circ> A)\<lparr>a\<rparr> = b" and "a \<in>\<^sub>\<circ> r -`\<^sub>\<circ> A"
  shows "b \<in>\<^sub>\<circ> A" and "r\<lparr>a\<rparr> = b"
  using assms by force+

lemma vrrestriction_atE1[elim]: 
  assumes "(r \<restriction>\<^sup>r\<^sub>\<circ> A)\<lparr>a\<rparr> = b" and "a \<in>\<^sub>\<circ> r -`\<^sub>\<circ> A" and "r\<lparr>a\<rparr> = b \<Longrightarrow> P"
  shows P
  using assms by (auto simp: vrrestriction_atD(2))

lemma vrrestriction_atE2[elim]:
  assumes "x \<in>\<^sub>\<circ> r \<restriction>\<^sup>r\<^sub>\<circ> A"
  obtains a b where "x = \<langle>a, b\<rangle>" and "b \<in>\<^sub>\<circ> A" and "r\<lparr>a\<rparr> = b"
  using assms unfolding vrrestriction_def by auto


text\<open>Restriction.\<close>

interpretation vrestriction: vsv \<open>r \<restriction>\<^sub>\<circ> A\<close> by (rule vsv_vrestriction)

lemma vlrestriction_app[intro, simp]: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "a \<in>\<^sub>\<circ> A"
  shows "(r \<restriction>\<^sup>l\<^sub>\<circ> A)\<lparr>a\<rparr> = r\<lparr>a\<rparr>"
  using assms by auto

lemma vrestriction_atD[dest]:
  assumes "(r \<restriction>\<^sub>\<circ> A)\<lparr>a\<rparr> = b" and "a \<in>\<^sub>\<circ> r -`\<^sub>\<circ> A" and "a \<in>\<^sub>\<circ> A"
  shows "b \<in>\<^sub>\<circ> A" and "r\<lparr>a\<rparr> = b"
proof-
  from assms have "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" by auto
  then show "r\<lparr>a\<rparr> = b"  
    by 
      (
        metis 
          assms 
          app_invimageD1 
          vrrestriction.vlrestriction_atD 
          vrrestriction_atD(2) 
          vrrestriction_vlrestriction
      )
  then show "b \<in>\<^sub>\<circ> A" using assms(2) by blast
qed
 
lemma vrestriction_atE1[elim]: 
  assumes "(r \<restriction>\<^sub>\<circ> A)\<lparr>a\<rparr> = b" 
    and "a \<in>\<^sub>\<circ> r -`\<^sub>\<circ> A" 
    and "a \<in>\<^sub>\<circ> A" 
    and "r\<lparr>a\<rparr> = b \<Longrightarrow> P"
  shows P
  using assms vrestriction_atD(2) by blast

lemma vrestriction_atE2[elim]:
  assumes "x \<in>\<^sub>\<circ> r \<restriction>\<^sub>\<circ> A"
  obtains a b where "x = \<langle>a, b\<rangle>" and "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A" and "r\<lparr>a\<rparr> = b"
  using assms unfolding vrestriction_def by clarsimp


text\<open>Domain.\<close>

lemma vdomain_atD: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  shows "\<exists>b\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> r. r\<lparr>a\<rparr> = b" 
  using assms by (blast intro: vsv_vimageI2)

lemma vdomain_atE:
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" 
  obtains b where "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r" and "r\<lparr>a\<rparr> = b"
  using assms by auto


text\<open>Range.\<close>

lemma vrange_atD: 
  assumes "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r"
  shows "\<exists>a\<in>\<^sub>\<circ>\<D>\<^sub>\<circ> r. r\<lparr>a\<rparr> = b" 
  using assms by auto

lemma vrange_atE:
  assumes "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r" 
  obtains a where "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "r\<lparr>a\<rparr> = b"
  using assms by auto


text\<open>Image.\<close>

lemma vimage_set_eq_at: 
  "{b. \<exists>a\<in>\<^sub>\<circ>A \<inter>\<^sub>\<circ> \<D>\<^sub>\<circ> r. r\<lparr>a\<rparr> = b} = {b. \<exists>a\<in>\<^sub>\<circ>A. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}"
  by (rule subset_antisym; rule subsetI; unfold mem_Collect_eq) auto

lemma vimage_small[simp]: "small {b. \<exists>a\<in>\<^sub>\<circ>A \<inter>\<^sub>\<circ> \<D>\<^sub>\<circ> r. r\<lparr>a\<rparr> = b}"
  unfolding vimage_set_eq_at by auto

lemma vimage_set_def: "r `\<^sub>\<circ> A = set {b. \<exists>a\<in>\<^sub>\<circ>A \<inter>\<^sub>\<circ> \<D>\<^sub>\<circ> r. r\<lparr>a\<rparr> = b}"
  unfolding vimage_set_eq_at by (simp add: app_vimage_set_def)

lemma vimage_set_iff: "b \<in>\<^sub>\<circ> r `\<^sub>\<circ> A \<longleftrightarrow> (\<exists>a\<in>\<^sub>\<circ>A \<inter>\<^sub>\<circ> \<D>\<^sub>\<circ> r. r\<lparr>a\<rparr> = b)"
  unfolding vimage_set_eq_at using vsv_vimage_iff by auto


text\<open>Further derived results.\<close>

lemma vimage_image:
  assumes "A \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  shows "elts (r `\<^sub>\<circ> A) = (\<lambda>x. r\<lparr>x\<rparr>) ` (elts A)"
  using vimage_def assms small_elts by blast

lemma vsv_vinsert_match_appI[intro, simp]:
  assumes "a \<notin>\<^sub>\<circ> \<D>\<^sub>\<circ> r" 
  shows "vinsert \<langle>a, b\<rangle> r \<lparr>a\<rparr> = b" 
  using assms vsv_axioms by simp

lemma vsv_vinsert_no_match_appI:
  assumes "a \<notin>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "c \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "r \<lparr>c\<rparr> = d" 
  shows "vinsert \<langle>a, b\<rangle> r \<lparr>c\<rparr> = d" 
  using assms vsv_axioms by simp

lemma vsv_is_vconst_onI:
  assumes "\<D>\<^sub>\<circ> r = A" and "\<R>\<^sub>\<circ> r = set {a}"
  shows "r = vconst_on A a"
  unfolding assms(1)[symmetric]
proof(cases \<open>\<D>\<^sub>\<circ> r = 0\<close>)
  case True
  with assms show "r = vconst_on (\<D>\<^sub>\<circ> r) a" 
    by (auto simp: vdomain_vrange_is_vempty)
next
  case False
  show "r = vconst_on (\<D>\<^sub>\<circ> r) a"
  proof(rule vsv_eqI)
    fix a' assume prems: "a' \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
    then obtain b where "r\<lparr>a'\<rparr> = b" and "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r" by auto
    moreover then have "b = a" unfolding assms by simp
    ultimately show "r\<lparr>a'\<rparr> = vconst_on (\<D>\<^sub>\<circ> r) a\<lparr>a'\<rparr>" by (simp add: prems)
  qed auto
qed

lemma vsv_vdomain_vrange_vsingleton:
  assumes "\<D>\<^sub>\<circ> r = set {a}" and "\<R>\<^sub>\<circ> r = set{b}"
  shows "r = set {\<langle>a, b\<rangle>}"
  using assms vsv_is_vconst_onI by auto

end


text\<open>Alternative forms of existing results.\<close>

lemmas [intro] = vsv.vconverse_atI
  and vsv_vconverse_atD[dest] = vsv.vconverse_atD[rotated]
  and vsv_vconverse_atE[elim] = vsv.vconverse_atE[rotated]
  and [intro, simp] = vsv.vlrestriction_atI
  and vsv_vlrestriction_atD[dest] = vsv.vlrestriction_atD[rotated]
  and vsv_vlrestriction_atE1[elim] = vsv.vlrestriction_atE1[rotated]
  and vsv_vlrestriction_atE2[elim] = vsv.vlrestriction_atE2[rotated]
  and [intro, simp] = vsv.vrrestriction_atI
  and vsv_vrrestriction_atD[dest] = vsv.vrrestriction_atD[rotated]
  and vsv_vrrestriction_atE1[elim] = vsv.vrrestriction_atE1[rotated]
  and vsv_vrrestriction_atE2[elim] = vsv.vrrestriction_atE2[rotated]
  and [intro, simp] = vsv.vlrestriction_app
  and vsv_vrestriction_atD[dest] = vsv.vrestriction_atD[rotated]
  and vsv_vrestriction_atE1[elim] = vsv.vrestriction_atE1[rotated]
  and vsv_vrestriction_atE2[elim] = vsv.vrestriction_atE2[rotated]
  and vsv_vdomain_atD = vsv.vdomain_atD[rotated]
  and vsv_vdomain_atE = vsv.vdomain_atE[rotated]
  and vrange_atD = vsv.vrange_atD[rotated]
  and vrange_atE = vsv.vrange_atE[rotated]
  and vsv_vinsert_match_appI[intro, simp] = vsv.vsv_vinsert_match_appI 
  and vsv_vinsert_no_match_appI[intro, simp] = 
    vsv.vsv_vinsert_no_match_appI[rotated 3]


text\<open>Corollaries of the alternative forms of existing results.\<close>

lemma vsv_vlrestriction_vrange:
  assumes "vsv s" and "vsv (r \<restriction>\<^sup>l\<^sub>\<circ> \<R>\<^sub>\<circ> s)"
  shows "vsv (r \<circ>\<^sub>\<circ> s)"
proof(rule vsvI)
  show "vbrelation (r \<circ>\<^sub>\<circ> s)" by auto
  fix a c c' assume "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> r \<circ>\<^sub>\<circ> s" "\<langle>a, c'\<rangle> \<in>\<^sub>\<circ> r \<circ>\<^sub>\<circ> s"
  then obtain b and b' 
    where ab: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> s" 
      and bc: "\<langle>b, c\<rangle> \<in>\<^sub>\<circ> r"
      and ab': "\<langle>a, b'\<rangle> \<in>\<^sub>\<circ> s" 
      and b'c': "\<langle>b', c'\<rangle> \<in>\<^sub>\<circ> r"
    by clarsimp
  moreover then have "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> s" and "b' \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> s" by auto
  ultimately have "\<langle>b, c\<rangle> \<in>\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<circ> \<R>\<^sub>\<circ> s)" and "\<langle>b', c'\<rangle> \<in>\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<circ> \<R>\<^sub>\<circ> s)" by auto
  with ab ab' have "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<circ> \<R>\<^sub>\<circ> s) \<circ>\<^sub>\<circ> s" and "\<langle>a, c'\<rangle> \<in>\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<circ> \<R>\<^sub>\<circ> s) \<circ>\<^sub>\<circ> s"
    by blast+
  moreover from assms have "vsv ((r \<restriction>\<^sup>l\<^sub>\<circ> \<R>\<^sub>\<circ> s) \<circ>\<^sub>\<circ> s)" by (intro vsv_vcomp)
  ultimately show "c = c'" by auto
qed

lemma vsv_vunion_app_right[simp]:
  assumes "vsv r" and "vsv s" and "vdisjnt (\<D>\<^sub>\<circ> r) (\<D>\<^sub>\<circ> s)" and "x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> s"
  shows "(r \<union>\<^sub>\<circ> s)\<lparr>x\<rparr> = s\<lparr>x\<rparr>"
  using assms vsubsetD by blast  

lemma vsv_vunion_app_left[simp]:
  assumes "vsv r" and "vsv s" and "vdisjnt (\<D>\<^sub>\<circ> r) (\<D>\<^sub>\<circ> s)" and "x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  shows "(r \<union>\<^sub>\<circ> s)\<lparr>x\<rparr> = r\<lparr>x\<rparr>"
  using assms vsubsetD by blast  


subsubsection\<open>One-to-one relation\<close>

locale v11 = vsv r for r +
  assumes vsv_vconverse: "vsv (r\<inverse>\<^sub>\<circ>)"


text\<open>Rules.\<close>

lemmas (in v11) [intro] = v11_axioms

mk_ide rf v11_def[unfolded v11_axioms_def]
  |intro v11I[intro]| 
  |dest v11D[dest]|
  |elim v11E[elim]|


text\<open>Set operations.\<close>

lemma (in v11) v11_vinsert[intro, simp]:
  assumes "a \<notin>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "b \<notin>\<^sub>\<circ> \<R>\<^sub>\<circ> r"
  shows "v11 (vinsert \<langle>a, b\<rangle> r)" 
  using assms v11_axioms 
  by (intro v11I; elim v11E) (simp_all add: vconverse_vinsert vsv.vsv_vinsert)

lemma v11_vinsertD:
  assumes "v11 (vinsert x r)"
  shows "v11 r"
  using assms by (intro v11I) (auto simp: vsv_vinsertD)

lemma v11_vunion:
  assumes "v11 r" 
    and "v11 s" 
    and "vdisjnt (\<D>\<^sub>\<circ> r) (\<D>\<^sub>\<circ> s)" 
    and "vdisjnt (\<R>\<^sub>\<circ> r) (\<R>\<^sub>\<circ> s)"
  shows "v11 (r \<union>\<^sub>\<circ> s)"
proof
  interpret r: v11 r by (rule assms(1))
  interpret s: v11 s by (rule assms(2))
  show "vsv (r \<union>\<^sub>\<circ> s)" by (simp add: assms v11D)
  from assms show "vsv ((r \<union>\<^sub>\<circ> s)\<inverse>\<^sub>\<circ>)"
    by (simp add: assms r.vsv_vconverse s.vsv_vconverse vconverse_vunion)
qed

lemma (in v11) v11_vintersection[intro, simp]: "v11 (r \<inter>\<^sub>\<circ> s)"
  using v11_axioms by (intro v11I) auto

lemma (in v11) v11_vdiff[intro, simp]: "v11 (r -\<^sub>\<circ> s)"
  using v11_axioms by (intro v11I) auto


text\<open>Special properties.\<close>

lemma (in vsv) vsv_valneq_v11I:
  assumes "\<And>x y. \<lbrakk> x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r; y \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r; x \<noteq> y \<rbrakk> \<Longrightarrow> r\<lparr>x\<rparr> \<noteq> r\<lparr>y\<rparr>"
  shows "v11 r"
proof(intro v11I)
  from vsv_axioms show "vsv r" by simp
  show "vsv (r\<inverse>\<^sub>\<circ>)"
    by 
      (
        metis
          assms 
          vbrelation_vconverse 
          vconverse_atD 
          app_vrangeI 
          vrange_vconverse 
          vsvI
      )
qed

lemma (in vsv) vsv_valeq_v11I:
  assumes "\<And>x y. \<lbrakk> x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r; y \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r; r\<lparr>x\<rparr> = r\<lparr>y\<rparr> \<rbrakk> \<Longrightarrow> x = y"
  shows "v11 r"
  using assms vsv_valneq_v11I by auto


text\<open>Connections.\<close>

lemma v11_vempty[simp]: "v11 0" by (simp add: v11I)

lemma v11_vsingleton[simp]: "v11 (set {\<langle>a, b\<rangle>})" by auto

lemma v11_vdoubleton: 
  assumes "a \<noteq> c" and "b \<noteq> d"
  shows "v11 (set {\<langle>a, b\<rangle>, \<langle>c, d\<rangle>})" 
  using assms by (auto simp: vinsert_set_insert_eq)

lemma v11_vid_on[simp]: "v11 (vid_on A)" by auto

lemma v11_VLambda[intro]:
  assumes "inj_on f (elts A)"
  shows "v11 (\<lambda>a\<in>\<^sub>\<circ>A. f a)"
proof(rule rel_VLambda.vsv_valneq_v11I)
  fix x y 
  assume "x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>A. f a)" and "y \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>A. f a)" and "x \<noteq> y"
  then have "x \<in>\<^sub>\<circ> A" and "y \<in>\<^sub>\<circ> A" by auto
  with assms \<open>x \<noteq> y\<close> have "f x \<noteq> f y" by (auto dest: inj_onD)
  then show "(\<lambda>a\<in>\<^sub>\<circ>A. f a)\<lparr>x\<rparr> \<noteq> (\<lambda>a\<in>\<^sub>\<circ>A. f a)\<lparr>y\<rparr>" 
    by (simp add: \<open>x \<in>\<^sub>\<circ> A\<close> \<open>y \<in>\<^sub>\<circ> A\<close>)
qed

lemma v11_vcomp:  
  assumes "v11 r" and "v11 s"
  shows "v11 (r \<circ>\<^sub>\<circ> s)"
  using assms by (intro v11I; elim v11E) (auto simp: vsv_vcomp vconverse_vcomp)

context v11
begin

lemma v11_vconverse: "v11 (r\<inverse>\<^sub>\<circ>)" by (auto simp: vsv_axioms vsv_vconverse)

interpretation v11 \<open>r\<inverse>\<^sub>\<circ>\<close> by (rule v11_vconverse)

lemma v11_vlrestriction[intro, simp]: "v11 (r \<restriction>\<^sup>l\<^sub>\<circ> A)"
  using vsv_vrrestriction by (auto simp: vrrestriction_vconverse)

lemma v11_vrrestriction[intro, simp]: "v11 (r \<restriction>\<^sup>r\<^sub>\<circ> A)"
  using vsv_vlrestriction by (auto simp: vlrestriction_vconverse)

lemma v11_vrestriction[intro, simp]: "v11 (r \<restriction>\<^sub>\<circ> A)"
  using vsv_vrestriction by (auto simp: vrestriction_vconverse)

end


text\<open>Further Special properties.\<close>

context v11
begin

lemma v11_injective: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "b \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "r\<lparr>a\<rparr> = r\<lparr>b\<rparr>" 
  shows "a = b"
  using assms v11_axioms by auto

lemma v11_double_pair: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "a' \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "r\<lparr>a\<rparr> = b" and "r\<lparr>a'\<rparr> = b'" 
  shows "a = a' \<longleftrightarrow> b = b'"
  using assms v11_axioms by auto

lemma v11_vrange_ex1_eq: "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r \<longleftrightarrow> (\<exists>!a\<in>\<^sub>\<circ>\<D>\<^sub>\<circ> r. r\<lparr>a\<rparr> = b)"
proof(rule iffI)
  from app_vdomainI v11_injective show 
    "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r \<Longrightarrow> \<exists>!a. a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r \<and> r\<lparr>a\<rparr> = b"
    by (elim app_vrangeE) auto
  show "\<exists>!a. a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r \<and> r\<lparr>a\<rparr> = b \<Longrightarrow> b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r"
    by (auto intro: vsv_vimageI2)
qed

lemma v11_VLambda_iff: "inj_on f (elts A) \<longleftrightarrow> v11 (\<lambda>a\<in>\<^sub>\<circ>A. f a)"
  by (rule iffI; (intro inj_onI | tactic\<open>all_tac\<close>)) 
    (auto simp: v11.v11_injective)

lemma v11_vimage_vpsubset_neq:
  assumes "A \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "B \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "A \<noteq> B"
  shows "r `\<^sub>\<circ> A \<noteq> r `\<^sub>\<circ> B" 
proof-
  from assms obtain a where AB: "a \<in>\<^sub>\<circ> A \<or> a \<in>\<^sub>\<circ> B" and nAB: "a \<notin>\<^sub>\<circ> A \<or> a \<notin>\<^sub>\<circ> B" 
    by auto
  then have "r\<lparr>a\<rparr> \<notin>\<^sub>\<circ> r `\<^sub>\<circ> A \<or> r\<lparr>a\<rparr> \<notin>\<^sub>\<circ> r `\<^sub>\<circ> B"
    unfolding vsv_vimage_iff by (metis assms(1,2) v11_injective vsubsetD)
  moreover from AB nAB assms(1,2) have "r\<lparr>a\<rparr> \<in>\<^sub>\<circ> r `\<^sub>\<circ> A \<or> r\<lparr>a\<rparr> \<in>\<^sub>\<circ> r `\<^sub>\<circ> B"
    by auto
  ultimately show "r `\<^sub>\<circ> A \<noteq> r `\<^sub>\<circ> B" by clarsimp
qed

lemma v11_eq_iff[simp]:
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "b \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  shows "r\<lparr>a\<rparr> = r\<lparr>b\<rparr> \<longleftrightarrow> a = b"
  using assms v11_double_pair by blast

lemma v11_vcomp_vconverse: "r\<inverse>\<^sub>\<circ> \<circ>\<^sub>\<circ> r = vid_on (\<D>\<^sub>\<circ> r)"
proof(intro vsubset_antisym vsubsetI)
  fix x assume prems: "x \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<circ> \<circ>\<^sub>\<circ> r"
  then obtain a c where x_def: "x = \<langle>a, c\<rangle>" and a: "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" by auto
  with prems obtain b where "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" and "\<langle>b, c\<rangle> \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<circ>" by auto
  with v11.vsv_vconverse v11_axioms have ca: "c = a" by auto
  from a show "x \<in>\<^sub>\<circ> vid_on (\<D>\<^sub>\<circ> r)" unfolding x_def ca by auto
next
  fix x assume "x \<in>\<^sub>\<circ> vid_on (\<D>\<^sub>\<circ> r)"
  then obtain a where x_def: "x = \<langle>a, a\<rangle>" and a: "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" by clarsimp
  then obtain b where "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" by auto
  then show "x \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<circ> \<circ>\<^sub>\<circ> r" unfolding x_def using a by auto
qed

lemma v11_vcomp_vconverse': "r \<circ>\<^sub>\<circ> r\<inverse>\<^sub>\<circ> = vid_on (\<R>\<^sub>\<circ> r)"
  using v11.v11_vcomp_vconverse v11_vconverse by force

lemma v11_vconverse_app[simp]:
  assumes "r\<lparr>a\<rparr> = b" and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  shows "r\<inverse>\<^sub>\<circ>\<lparr>b\<rparr> = a"
  using assms by (simp add: vsv.vconverse_iff vsv_axioms vsv_vconverse)

lemma v11_vconverse_app_in_vdomain:
  assumes "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r"
  shows "r\<inverse>\<^sub>\<circ>\<lparr>y\<rparr> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  using assms v11_vconverse 
  unfolding vrange_vconverse[symmetric] 
  by (auto simp: v11_def)

lemma v11_app_if_vconverse_app:
  assumes "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r" and "r\<inverse>\<^sub>\<circ>\<lparr>y\<rparr> = x"
  shows "r\<lparr>x\<rparr> = y"
  using assms vsv_vconverse by auto

lemma v11_app_vconverse_app:
  assumes "a \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r"
  shows "r\<lparr>r\<inverse>\<^sub>\<circ>\<lparr>a\<rparr>\<rparr> = a"
  using assms by (meson v11_app_if_vconverse_app)

lemma v11_vconverse_app_app:
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r"
  shows "r\<inverse>\<^sub>\<circ>\<lparr>r\<lparr>a\<rparr>\<rparr> = a"
  using assms v11_vconverse_app by auto

end

lemma v11_vlrestriction_vsubset:
  assumes "v11 (f \<restriction>\<^sup>l\<^sub>\<circ> A)" and "B \<subseteq>\<^sub>\<circ> A"
  shows "v11 (f \<restriction>\<^sup>l\<^sub>\<circ> B)"
proof-
  from assms have fB_def: "f \<restriction>\<^sup>l\<^sub>\<circ> B = (f \<restriction>\<^sup>l\<^sub>\<circ> A) \<restriction>\<^sup>l\<^sub>\<circ> B" by auto
  show ?thesis unfolding fB_def by (intro v11.v11_vlrestriction assms(1))
qed

lemma v11_vlrestriction_vrange:
  assumes "v11 s" and "v11 (r \<restriction>\<^sup>l\<^sub>\<circ> \<R>\<^sub>\<circ> s)"
  shows "v11 (r \<circ>\<^sub>\<circ> s)"
proof(intro v11I)
  interpret v11 s by (rule assms(1)) 
  from assms vsv_vlrestriction_vrange show "vsv (r \<circ>\<^sub>\<circ> s)"
    by (simp add: v11.axioms(1))
  show "vsv ((r \<circ>\<^sub>\<circ> s)\<inverse>\<^sub>\<circ>)"
    unfolding vconverse_vcomp
  proof(rule vsvI)
    fix a c c' assume "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> s\<inverse>\<^sub>\<circ> \<circ>\<^sub>\<circ> r\<inverse>\<^sub>\<circ>" "\<langle>a, c'\<rangle> \<in>\<^sub>\<circ> s\<inverse>\<^sub>\<circ> \<circ>\<^sub>\<circ> r\<inverse>\<^sub>\<circ>"
    then obtain b and b' 
      where "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> r" 
      and bc: "\<langle>c, b\<rangle> \<in>\<^sub>\<circ> s"
      and "\<langle>b', a\<rangle> \<in>\<^sub>\<circ> r" 
      and b'c': "\<langle>c', b'\<rangle> \<in>\<^sub>\<circ> s"
      by auto
    moreover then have "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> s" and "b' \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> s" by auto
    ultimately have "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<circ> \<R>\<^sub>\<circ> s)" and "\<langle>b', a\<rangle> \<in>\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<circ> \<R>\<^sub>\<circ> s)" by auto
    with assms(2) have bb': "b = b'" by auto
    from assms bc[unfolded bb'] b'c' show "c = c'" by auto
  qed auto
qed

lemma v11_vlrestriction_vcomp:
  assumes "v11 (f \<restriction>\<^sup>l\<^sub>\<circ> A)" and "v11 (g \<restriction>\<^sup>l\<^sub>\<circ> (f `\<^sub>\<circ> A))"
  shows "v11 ((g \<circ>\<^sub>\<circ> f) \<restriction>\<^sup>l\<^sub>\<circ> A)"
  using assms v11_vlrestriction_vrange by (auto simp: assms(2) app_vimage_def)


text\<open>Alternative forms of existing results.\<close>

lemmas [intro, simp] = v11.v11_vinsert
  and [intro, simp] = v11.v11_vintersection
  and [intro, simp] = v11.v11_vdiff
  and [intro, simp] = v11.v11_vrrestriction
  and [intro, simp] = v11.v11_vlrestriction
  and [intro, simp] = v11.v11_vrestriction
  and [intro] = v11.v11_vimage_vpsubset_neq



subsection\<open>Tools: \<open>mk_VLambda\<close>\<close>

ML\<open>

(* low level unfold *)
(*Designed based on an algorithm from HOL-Types_To_Sets/unoverload_def.ML*)
fun pure_unfold ctxt thms = ctxt
  |> 
    (
      thms
      |> Conv.rewrs_conv 
      |> Conv.try_conv 
      |> K
      |> Conv.top_conv
    )
  |> Conv.fconv_rule;

val msg_args = "mk_VLambda: invalid arguments"

val vsv_VLambda_thm = @{thm vsv_VLambda};
val vsv_VLambda_match = vsv_VLambda_thm 
  |> Thm.full_prop_of
  |> HOLogic.dest_Trueprop
  |> dest_comb 
  |> #2;

val vdomain_VLambda_thm = @{thm vdomain_VLambda};
val vdomain_VLambda_match = vdomain_VLambda_thm 
  |> Thm.full_prop_of
  |> HOLogic.dest_Trueprop
  |> HOLogic.dest_eq
  |> #1
  |> dest_comb
  |> #2;

val app_VLambda_thm = @{thm ZFC_Cardinals.beta};
val app_VLambda_match = app_VLambda_thm 
  |> Thm.concl_of
  |> HOLogic.dest_Trueprop
  |> HOLogic.dest_eq
  |> #1
  |> strip_comb
  |> #2
  |> hd;

fun mk_VLabmda_thm match_t match_thm ctxt thm =
  let
    val thm_ct = Thm.cprop_of thm
    val (_, rhs_ct) = Thm.dest_equals thm_ct
      handle TERM ("dest_equals", _) => error msg_args
    val insts = Thm.match (Thm.cterm_of ctxt match_t, rhs_ct)
      handle Pattern.MATCH => error msg_args
  in 
    match_thm
    |> Drule.instantiate_normalize insts
    |> pure_unfold ctxt (thm |> Thm.symmetric |> single) 
  end;

val mk_VLambda_vsv =
  mk_VLabmda_thm vsv_VLambda_match vsv_VLambda_thm;
val mk_VLambda_vdomain =
  mk_VLabmda_thm vdomain_VLambda_match vdomain_VLambda_thm;
val mk_VLambda_app = 
  mk_VLabmda_thm app_VLambda_match app_VLambda_thm;

val mk_VLambda_parser = Parse.thm --
  (
    Scan.repeat
      (
        (\<^keyword>\<open>|vsv\<close> -- Parse_Spec.opt_thm_name "|") ||
        (\<^keyword>\<open>|app\<close> -- Parse_Spec.opt_thm_name "|") ||
        (\<^keyword>\<open>|vdomain\<close> -- Parse_Spec.opt_thm_name "|")
      )
  );

fun process_mk_VLambda_thm mk_VLambda_thm (b, thm) ctxt =
  let 
    val thm' = mk_VLambda_thm ctxt thm
    val ((c, thms'), ctxt') = ctxt
      |> Local_Theory.note (b ||> map (Attrib.check_src ctxt), single thm') 
    val _ = IDE_Utilities.thm_printer ctxt' true c thms'
  in ctxt' end;

fun folder_mk_VLambda (("|vsv", b), thm) ctxt =
      process_mk_VLambda_thm mk_VLambda_vsv (b, thm) ctxt
  | folder_mk_VLambda (("|app", b), thm) ctxt =
      process_mk_VLambda_thm mk_VLambda_app (b, thm) ctxt
  | folder_mk_VLambda (("|vdomain", b), thm) ctxt =
      process_mk_VLambda_thm mk_VLambda_vdomain (b, thm) ctxt
  | folder_mk_VLambda _ _ = error msg_args

fun process_mk_VLambda (thm, ins) ctxt =
  let
    val _ = ins |> map fst |> has_duplicates op= |> not orelse error msg_args
    val thm' = thm
      |> singleton (Attrib.eval_thms ctxt)
      |> Local_Defs.meta_rewrite_rule ctxt;
  in fold folder_mk_VLambda (map (fn x => (x, thm')) ins) ctxt end;

val _ =
  Outer_Syntax.local_theory
    \<^command_keyword>\<open>mk_VLambda\<close>
    "VLambda"
    (mk_VLambda_parser >> process_mk_VLambda);

\<close>

text\<open>\newpage\<close>

end