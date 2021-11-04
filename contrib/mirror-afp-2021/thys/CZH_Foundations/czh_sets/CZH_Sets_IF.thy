(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Operations on indexed families of sets\<close>
theory CZH_Sets_IF
  imports CZH_Sets_BRelations
begin



subsection\<open>Background\<close>


text\<open>
This section presents results about the fundamental operations on the indexed
families of sets, such as unions and intersections of the indexed families
of sets, disjoint unions and infinite Cartesian products.

Certain elements of the content of this section were inspired by
elements of the content of \cite{paulson_hereditarily_2013}. 
However, as previously, many other results were ported (with amendments) from 
the main library of Isabelle/HOL.
\<close>

abbreviation (input) imVLambda :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "imVLambda A f \<equiv> (\<lambda>a\<in>\<^sub>\<circ>A. f a) `\<^sub>\<circ> A"



subsection\<open>Intersection of an indexed family of sets\<close>

syntax "_VIFINTER" :: "pttrn \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"  (\<open>(3\<Inter>\<^sub>\<circ>_\<in>\<^sub>\<circ>_./ _)\<close> [0, 0, 10] 10)

translations "\<Inter>\<^sub>\<circ>x\<in>\<^sub>\<circ>A. f" \<rightleftharpoons> "CONST VInter (CONST imVLambda A (\<lambda>x. f))"


text\<open>Rules.\<close>

lemma vifintersectionI[intro]:
  assumes "I \<noteq> 0" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> a \<in>\<^sub>\<circ> f i"  
  shows "a \<in>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i)"
  using assms by (auto intro!: vsubset_antisym)

lemma vifintersectionD[dest]:
  assumes "a \<in>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i)" and "i \<in>\<^sub>\<circ> I"
  shows "a \<in>\<^sub>\<circ> f i"
  using assms by blast

lemma vifintersectionE1[elim]:
  assumes "a \<in>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i)" and "a \<in>\<^sub>\<circ> f i \<Longrightarrow> P" and "i \<notin>\<^sub>\<circ> I \<Longrightarrow> P" 
  shows P
  using assms by blast

lemma vifintersectionE3[elim]:
  assumes "a \<in>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i)"
  obtains "\<And>i. i\<in>\<^sub>\<circ>I \<Longrightarrow> a \<in>\<^sub>\<circ> f i"
  using assms by blast

lemma vifintersectionE2[elim]:
  assumes "a \<in>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i)"
  obtains i where "i \<in>\<^sub>\<circ> I" and "a \<in>\<^sub>\<circ> f i"
  using assms by (elim vifintersectionE3) (meson assms VInterE2 app_vimageE)


text\<open>Set operations.\<close>

lemma vifintersection_vempty_is[simp]: "(\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>0. f i) = 0" by auto

lemma vifintersection_vsingleton_is[simp]: "(\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>set{i}. f i) = f i"
  using elts_0 by blast

lemma vifintersection_vdoubleton_is[simp]: "(\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>set {i, j}. f i) = f i \<inter>\<^sub>\<circ> f j"  
  by 
    (
      intro vsubset_antisym vsubsetI; 
      (elim vifintersectionE3 | intro vifintersectionI)
    )
    auto

lemma vifintersection_antimono1: 
  assumes "I \<noteq> 0" and "I \<subseteq>\<^sub>\<circ> J"
  shows "(\<Inter>\<^sub>\<circ>j\<in>\<^sub>\<circ>J. f j) \<subseteq>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i)"
  using assms by blast

lemma vifintersection_antimono2: 
  assumes "I \<noteq> 0" and " I \<subseteq>\<^sub>\<circ> J" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> f i \<subseteq>\<^sub>\<circ> g i"
  shows "(\<Inter>\<^sub>\<circ>j\<in>\<^sub>\<circ>J. f j) \<subseteq>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. g i)"
  using assms by blast

lemma vifintersection_vintersection: 
  assumes "I \<noteq> 0" and "J \<noteq> 0"
  shows "(\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) \<inter>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>J. f i) = (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I \<union>\<^sub>\<circ> J. f i)"
  using assms by (auto intro!: vsubset_antisym)

lemma vifintersection_vintersection_family: 
  assumes "I \<noteq> 0" 
  shows "(\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<inter>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. B i) = (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i \<inter>\<^sub>\<circ> B i)"
  using assms
  by (intro vsubset_antisym vsubsetI, intro vifintersectionI | tactic\<open>all_tac\<close>) 
    blast+

lemma vifintersection_vunion:
  assumes "I \<noteq> 0" and "J \<noteq> 0"
  shows "(\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) \<union>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>j\<in>\<^sub>\<circ>J. g j) = (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<Inter>\<^sub>\<circ>j\<in>\<^sub>\<circ>J. f i \<union>\<^sub>\<circ> g j)"
  using assms by (blast intro!: vsubset_antisym)

lemma vifintersection_vinsert_is[intro, simp]:
  assumes "I \<noteq> 0" 
  shows "(\<Inter>\<^sub>\<circ>i \<in>\<^sub>\<circ> vinsert j I. f i) = f j \<inter>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i)"
  apply(insert assms, intro vsubset_antisym vsubsetI)
  subgoal for b by (subgoal_tac \<open>b \<in>\<^sub>\<circ> f j\<close> \<open>b \<in>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i)\<close>) blast+
  subgoal for b 
    by (subgoal_tac \<open>b \<in>\<^sub>\<circ> f j\<close> \<open>b \<in>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i)\<close>) 
      (blast intro!: vsubset_antisym)+
  done

lemma vifintersection_VPow: 
  assumes "I \<noteq> 0"
  shows "VPow (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) = (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. VPow (f i))"
  using assms by (auto intro!: vsubset_antisym)


text\<open>Elementary properties.\<close>

lemma vifintersection_constant[intro, simp]:
  assumes "I \<noteq> 0"
  shows "(\<Inter>\<^sub>\<circ>y\<in>\<^sub>\<circ>I. c) = c"
  using assms by auto

lemma vifintersection_vsubset_iff: 
  assumes "I \<noteq> 0"
  shows "A \<subseteq>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) \<longleftrightarrow> (\<forall>i\<in>\<^sub>\<circ>I. A \<subseteq>\<^sub>\<circ> f i)"
  using assms by blast

lemma vifintersection_vsubset_lower: 
  assumes "i \<in>\<^sub>\<circ> I"
  shows "(\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) \<subseteq>\<^sub>\<circ> f i"
  using assms by blast

lemma vifintersection_vsubset_greatest: 
  assumes "I \<noteq> 0" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> A \<subseteq>\<^sub>\<circ> f i" 
  shows "A \<subseteq>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i)"
  using assms by (intro vsubsetI vifintersectionI) auto 

lemma vifintersection_vintersection_value: 
  assumes "i \<in>\<^sub>\<circ> I"
  shows "f i \<inter>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) = (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i)"
  using assms by blast

lemma vifintersection_vintersection_single: 
  assumes "I \<noteq> 0"
  shows "B \<union>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) = (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. B \<union>\<^sub>\<circ> A i)"
  by (insert assms, intro vsubset_antisym vsubsetI vifintersectionI) 
    blast+


text\<open>Connections.\<close>

lemma vifintersection_vrange_VLambda: "(\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) = \<Inter>\<^sub>\<circ> (\<R>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>I. f a))"
  by (simp add: vimage_VLambda_vrange_rep)



subsection\<open>Union of an indexed family of sets\<close>

syntax "_VIFUNION" :: "pttrn \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (\<open>(3\<Union>\<^sub>\<circ>_\<in>\<^sub>\<circ>_./ _)\<close> [0, 0, 10] 10)

translations "\<Union>\<^sub>\<circ>x\<in>\<^sub>\<circ>A. f" \<rightleftharpoons> "CONST VUnion (CONST imVLambda A (\<lambda>x. f))"


text\<open>Rules.\<close>

lemma vifunion_iff: "b \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) \<longleftrightarrow> (\<exists>i\<in>\<^sub>\<circ>I. b \<in>\<^sub>\<circ> f i)" by force

lemma vifunionI[intro]: 
  assumes "i \<in>\<^sub>\<circ> I" and "a \<in>\<^sub>\<circ> f i" 
  shows "a \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i)" 
  using assms by force

lemma vifunionD[dest]: 
  assumes "a \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i)" 
  shows "\<exists>i\<in>\<^sub>\<circ>I. a \<in>\<^sub>\<circ> f i" 
  using assms by auto

lemma vifunionE[elim!]: 
  assumes "a \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i)" and "\<And>i. \<lbrakk> i \<in>\<^sub>\<circ> I; a \<in>\<^sub>\<circ> f i \<rbrakk> \<Longrightarrow> R" 
  shows R
  using assms by auto


text\<open>Set operations.\<close>

lemma vifunion_vempty_family[simp]: "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. 0) = 0" by auto

lemma vifunion_vsingleton_is[simp]: "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>set {i}. f i) = f i" by force

lemma vifunion_vsingleton_family[simp]: "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. set {i}) = I" by force

lemma vifunion_vdoubleton: "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>set {i, j}. f i) = f i \<union>\<^sub>\<circ> f j" 
  using VLambda_vinsert vimage_vunion_left
  by (force simp: VLambda_vsingleton simp: vinsert_set_insert_eq)

lemma vifunion_mono:
  assumes "I \<subseteq>\<^sub>\<circ> J" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> f i \<subseteq>\<^sub>\<circ> g i" 
  shows "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>j\<in>\<^sub>\<circ>J. g j)"
  using assms by force

lemma vifunion_vunion_is: "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) \<union>\<^sub>\<circ> (\<Union>\<^sub>\<circ>j\<in>\<^sub>\<circ>J. f j) = (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I \<union>\<^sub>\<circ> J. f i)"
  by force

lemma vifunion_vunion_family:
  "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) \<union>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. g i) = (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i \<union>\<^sub>\<circ> g i)"  
  by (intro vsubset_antisym vsubsetI; elim vunionE vifunionE) force+

lemma vifunion_vintersection: 
  "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) \<inter>\<^sub>\<circ> (\<Union>\<^sub>\<circ>j\<in>\<^sub>\<circ>J. g j) = (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<Union>\<^sub>\<circ>j\<in>\<^sub>\<circ>J. f i \<inter>\<^sub>\<circ> g j)"
  by (force simp: vrange_VLambda vimage_VLambda_vrange_rep)

lemma vifunion_vinsert_is: 
  "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>vinsert j I. f i) = f j \<union>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i)"
  by (force simp: vimage_VLambda_vrange_rep)

lemma vifunion_VPow: "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. VPow (f i)) \<subseteq>\<^sub>\<circ> VPow (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i)" by force


text\<open>Elementary properties.\<close>

lemma vifunion_vempty_conv:
  "0 = (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) \<longleftrightarrow> (\<forall>i\<in>\<^sub>\<circ>I. f i = 0)"
  "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) = 0 \<longleftrightarrow> (\<forall>i\<in>\<^sub>\<circ>I. f i = 0)"
  by (auto simp: vrange_VLambda vimage_VLambda_vrange_rep)

lemma vifunion_constant[simp]: "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. c) = (if I = 0 then 0 else c)" 
proof(intro vsubset_antisym)
  show "(if I = 0 then 0 else c) \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. c)"
    by (cases \<open>vdisjnt I I\<close>) (auto simp: VLambda_vconst_on)
qed auto

lemma vifunion_upper:
  assumes "i \<in>\<^sub>\<circ> I"
  shows "f i \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i)"
  using assms by force

lemma vifunion_least: 
  assumes "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> f i \<subseteq>\<^sub>\<circ> C"
  shows "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) \<subseteq>\<^sub>\<circ> C"
  using assms by auto

lemma vifunion_absorb: 
  assumes "j \<in>\<^sub>\<circ> I"
  shows "f j \<union>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) = (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i)" 
  using assms by force

lemma vifunion_vifunion_flatten: 
  "(\<Union>\<^sub>\<circ>j\<in>\<^sub>\<circ>(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i). g j) = (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<Union>\<^sub>\<circ>j\<in>\<^sub>\<circ>f i. g j)"
  by (force simp: vrange_VLambda vimage_VLambda_vrange_rep)

lemma vifunion_vsubset_iff: "((\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) \<subseteq>\<^sub>\<circ> B) = (\<forall>i\<in>\<^sub>\<circ>I. f i \<subseteq>\<^sub>\<circ> B)" by force

lemma vifunion_vsingleton_eq_vrange: "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. set {f i}) = \<R>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>I. f a)"
  by force

lemma vball_vifunion[simp]: "(\<forall>z\<in>\<^sub>\<circ>(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i). P z) \<longleftrightarrow> (\<forall>x\<in>\<^sub>\<circ>I. \<forall>z\<in>\<^sub>\<circ>f x. P z)"
  by force

lemma vbex_vifunion[simp]: "(\<exists>z\<in>\<^sub>\<circ>(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i). P z) \<longleftrightarrow> (\<exists>x\<in>\<^sub>\<circ>I. \<exists>z\<in>\<^sub>\<circ>f x. P z)"
  by force

lemma vifunion_vintersection_index_right[simp]: "(\<Union>\<^sub>\<circ>C\<in>\<^sub>\<circ>B. A \<inter>\<^sub>\<circ> C) = A \<inter>\<^sub>\<circ> \<Union>\<^sub>\<circ>B" 
  by (force simp: vimage_VLambda_vrange_rep)

lemma vifunion_vintersection_index_left[simp]: "(\<Union>\<^sub>\<circ>C\<in>\<^sub>\<circ>B. C \<inter>\<^sub>\<circ> A) = \<Union>\<^sub>\<circ>B \<inter>\<^sub>\<circ> A" 
  by (force simp: vimage_VLambda_vrange_rep)

lemma vifunion_vunion_index[intro, simp]:
  assumes "B \<noteq> 0"
  shows "(\<Inter>\<^sub>\<circ>C\<in>\<^sub>\<circ>B. A \<union>\<^sub>\<circ> C) = A \<union>\<^sub>\<circ> \<Inter>\<^sub>\<circ>B"
  using assms
  by 
    (
      (intro vsubset_antisym vsubsetI); 
      (intro vifintersectionI | tactic\<open>all_tac\<close>)
    ) 
    blast+

lemma vifunion_vintersection_single: "B \<inter>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) = (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. B \<inter>\<^sub>\<circ> f i)" 
  by (force simp: vrange_VLambda vimage_VLambda_vrange_rep)

lemma vifunion_vifunion_flip: 
  "(\<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. \<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. f b a) = (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. f b a)"
proof-
  have "x \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. f b a)" if "x \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. \<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. f b a)" 
    for x f A B 
  proof-
    from that obtain b where b: "b \<in>\<^sub>\<circ> B" and x_b: "x \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. f b a)" 
      by fastforce
    then obtain a where a: "a \<in>\<^sub>\<circ> A" and x_fba: "x \<in>\<^sub>\<circ> f b a" by fastforce
    show "x \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. f b a)"
      unfolding vifunion_iff by (auto intro: a b x_fba)
  qed
  then show ?thesis by (intro vsubset_antisym vsubsetI) auto
qed


text\<open>Connections.\<close>

lemma vifunion_disjoint: "(\<Union>\<^sub>\<circ>C \<inter>\<^sub>\<circ> A = 0) \<longleftrightarrow> (\<forall>B\<in>\<^sub>\<circ>C. vdisjnt B A)" 
  by (intro iffI)
    (auto intro!: vsubset_antisym simp: Sup_upper vdisjnt_vsubset_left)

lemma vdisjnt_vifunion_iff: 
  "vdisjnt A (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) \<longleftrightarrow> (\<forall>i\<in>\<^sub>\<circ>I. vdisjnt A (f i))"
  by (force intro!: vsubset_antisym simp: vdisjnt_iff)+

lemma vifunion_VLambda: "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>A. set {\<langle>i, f i\<rangle>}) = (\<lambda>a\<in>\<^sub>\<circ>A. f a)" 
  using vifunionI by (intro vsubset_antisym vsubsetI) auto

lemma vifunion_vrange_VLambda: "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) = \<Union>\<^sub>\<circ>(\<R>\<^sub>\<circ> (\<lambda>a\<in>\<^sub>\<circ>I. f a))"
  using vimage_VLambda_vrange_rep by auto

lemma (in vsv) vsv_vrange_vsubset_vifunion_app:
  assumes "\<D>\<^sub>\<circ> r = I" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> r\<lparr>i\<rparr> \<in>\<^sub>\<circ> A i" 
  shows "\<R>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)"
proof(intro vsubsetI)
  fix x assume "x \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r"
  with assms(1) obtain i where x_def: "x = r\<lparr>i\<rparr>" and i: "i \<in>\<^sub>\<circ> I"
    by (metis vrange_atE)
  from i assms(2)[rule_format, OF i] show "x \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)"
    unfolding x_def by (intro vifunionI) auto
qed

lemma v11_vlrestriction_vifintersection: 
  assumes "I \<noteq> 0" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> v11 (f \<restriction>\<^sup>l\<^sub>\<circ> (A i))" 
  shows "v11 (f \<restriction>\<^sup>l\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i))"
proof(intro v11I)
  show "vsv (f \<restriction>\<^sup>l\<^sub>\<circ> \<Inter>\<^sub>\<circ> ((\<lambda>a\<in>\<^sub>\<circ>I. A a) `\<^sub>\<circ> I))"
    (*slow*)
    apply(subgoal_tac \<open>\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> vsv (f \<restriction>\<^sup>l\<^sub>\<circ> (A i))\<close>)
    subgoal by (insert assms(1), intro vsvI) (blast intro!: vsubset_antisym)+
    subgoal using assms by blast
    done
  show "vsv ((f \<restriction>\<^sup>l\<^sub>\<circ> \<Inter>\<^sub>\<circ> ((\<lambda>a\<in>\<^sub>\<circ>I. A a) `\<^sub>\<circ> I))\<inverse>\<^sub>\<circ>)"
  proof(intro vsvI) 
    fix a b c
    assume ab: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> (f \<restriction>\<^sup>l\<^sub>\<circ> \<Inter>\<^sub>\<circ> ((\<lambda>a\<in>\<^sub>\<circ>I. A a) `\<^sub>\<circ> I))\<inverse>\<^sub>\<circ>"
      and ac: "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> (f \<restriction>\<^sup>l\<^sub>\<circ> \<Inter>\<^sub>\<circ> ((\<lambda>a\<in>\<^sub>\<circ>I. A a) `\<^sub>\<circ> I))\<inverse>\<^sub>\<circ>"
    from assms(2) have hyp: "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> vsv ((f \<restriction>\<^sup>l\<^sub>\<circ> (A i))\<inverse>\<^sub>\<circ>)" by blast
    from assms(1) obtain i where "i \<in>\<^sub>\<circ> I" and "\<Inter>\<^sub>\<circ> ((\<lambda>a\<in>\<^sub>\<circ>I. A a) `\<^sub>\<circ> I) \<subseteq>\<^sub>\<circ> A i"
      by (auto intro!: vsubset_antisym)
    with ab ac hyp \<open>i \<in>\<^sub>\<circ> I\<close> show "b = c" by auto
  qed auto
qed



subsection\<open>Additional simplification rules for indexed families of sets.\<close>


text\<open>Union.\<close>

lemma vifunion_simps[simp]:
  "\<And>a B I. (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. vinsert a (B i)) = 
    (if I=0 then 0 else vinsert a (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. B i))"
  "\<And>A B I. (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i \<union>\<^sub>\<circ> B) = ((if I=0 then 0 else (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<union>\<^sub>\<circ> B))"
  "\<And>A B I. (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A \<union>\<^sub>\<circ> B i) = ((if I=0 then 0 else A \<union>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. B i)))"
  "\<And>A B I. (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i \<inter>\<^sub>\<circ> B) = ((\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<inter>\<^sub>\<circ> B)"
  "\<And>A B I. (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A \<inter>\<^sub>\<circ> B i) = (A \<inter>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. B i))"
  "\<And>A B I. (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i -\<^sub>\<circ> B) = ((\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) -\<^sub>\<circ> B)"
  "\<And>A B. (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>\<Union>\<^sub>\<circ>A. B i) = (\<Union>\<^sub>\<circ>y\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>y. B i)"
  by 
    (
      force 
        simp: vrange_VLambda vimage_VLambda_vrange_rep
        intro!: vsubset_antisym
    )+

lemma vifunion_simps_ext:
  "\<And>a B I. vinsert a (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. B i) = 
    (if I=0 then set {a} else (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. vinsert a (B i)))"
  "\<And>A B I. (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<union>\<^sub>\<circ> B = (if I=0 then B else (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i \<union>\<^sub>\<circ> B))"
  "\<And>A B I. A \<union>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. B i) = (if I=0 then A else (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A \<union>\<^sub>\<circ> B i))"
  "\<And>A B I. ((\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<inter>\<^sub>\<circ> B) = (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i \<inter>\<^sub>\<circ> B)"
  "\<And>A B I. ((\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) -\<^sub>\<circ> B) = (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i -\<^sub>\<circ> B)"
  "\<And>A B. (\<Union>\<^sub>\<circ>y\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>y. B i) = (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>\<Union>\<^sub>\<circ>A. B i)"
  by (auto simp: vrange_VLambda)

lemma vifunion_vball_vbex_simps[simp]:
  "\<And>A P. (\<forall>a\<in>\<^sub>\<circ>\<Union>\<^sub>\<circ>A. P a) \<longleftrightarrow> (\<forall>y\<in>\<^sub>\<circ>A. \<forall>a\<in>\<^sub>\<circ>y. P a)"
  "\<And>A P. (\<exists>a\<in>\<^sub>\<circ>\<Union>\<^sub>\<circ>A. P a) \<longleftrightarrow> (\<exists>y\<in>\<^sub>\<circ>A. \<exists>a\<in>\<^sub>\<circ>y. P a)"
  using vball_vifunion vbex_vifunion by auto


text\<open>Intersection.\<close>

lemma vifintersection_simps[simp]: 
  "\<And>I A B. (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i \<inter>\<^sub>\<circ> B) = (if I = 0 then 0 else (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<inter>\<^sub>\<circ> B)"
  "\<And>I A B. (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A \<inter>\<^sub>\<circ> B i) = (if I = 0 then 0 else A \<inter>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. B i))"
  "\<And>I A B. (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i -\<^sub>\<circ> B) = (if I = 0 then 0 else (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) -\<^sub>\<circ> B)"
  "\<And>I A B. (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A -\<^sub>\<circ> B i) = (if I = 0 then 0 else A -\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. B i))"
  "\<And>I a B. 
    (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. vinsert a (B i)) = (if I = 0 then 0 else vinsert a (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. B i))"
  "\<And>I A B. (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i \<union>\<^sub>\<circ> B) = (if I = 0 then 0 else ((\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<union>\<^sub>\<circ> B))"
  "\<And>I A B. (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A \<union>\<^sub>\<circ> B i) = (if I = 0 then 0 else (A \<union>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. B i)))"
  by force+

lemma vifintersection_simps_ext:
  "\<And>A B I. (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<inter>\<^sub>\<circ> B = (if I = 0 then 0 else (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i \<inter>\<^sub>\<circ> B))"
  "\<And>A B I. A \<inter>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. B i) = (if I = 0 then 0 else (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A \<inter>\<^sub>\<circ> B i))"
  "\<And>A B I. (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) -\<^sub>\<circ> B = (if I = 0 then 0 else (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i -\<^sub>\<circ> B))"
  "\<And>A B I. A -\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. B i) = (if I = 0 then A else (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A -\<^sub>\<circ> B i))"
  "\<And>a B I. vinsert a (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. B i) = 
    (if I = 0 then set {a} else (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. vinsert a (B i)))"
  "\<And>A B I. ((\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<union>\<^sub>\<circ> B) = (if I = 0 then B else (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i \<union>\<^sub>\<circ> B))"
  "\<And>A B I. A \<union>\<^sub>\<circ> (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. B i) = (if I = 0 then A else (\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A \<union>\<^sub>\<circ> B i))"
  using vifintersection_simps by auto



subsection\<open>Knowledge transfer: union and intersection of indexed families\<close>

lemma SUP_vifunion: "(SUP \<xi>\<in>elts \<alpha>. A \<xi>) = (\<Union>\<^sub>\<circ>\<xi>\<in>\<^sub>\<circ>\<alpha>. A \<xi>)"
  by (simp add: vimage_VLambda_vrange_rep vrange_VLambda)

lemma INF_vifintersection: "(INF \<xi>\<in>elts \<alpha>. A \<xi>) = (\<Inter>\<^sub>\<circ>\<xi>\<in>\<^sub>\<circ>\<alpha>. A \<xi>)"
  by (simp add: vimage_VLambda_vrange_rep vrange_VLambda)

lemmas Ord_induct3'[consumes 1, case_names 0 succ Limit, induct type: V] =
  Ord_induct3[unfolded SUP_vifunion]

lemma Limit_vifunion_def[simp]:
  assumes "Limit \<alpha>"
  shows "(\<Union>\<^sub>\<circ>\<xi>\<in>\<^sub>\<circ>\<alpha>. \<xi>) = \<alpha>"
  using assms unfolding SUP_vifunion[symmetric] by simp

lemmas_with[unfolded SUP_vifunion INF_vifintersection]: 
  TC = ZFC_Cardinals.TC
  and rank_Sup = ZFC_Cardinals.rank_Sup
  and TC_def = ZFC_Cardinals.TC_def
  and Ord_equality = ZFC_in_HOL.Ord_equality
  and Aleph_Limit = ZFC_Cardinals.Aleph_Limit
  and rank = ZFC_Cardinals.rank
  and Vset = ZFC_in_HOL.Vset
  and mult = Kirby.mult
  and Aleph_def = ZFC_Cardinals.Aleph_def
  and times_V_def = Kirby.times_V_def
  and mult_Limit = Kirby.mult_Limit
  and Vfrom = ZFC_in_HOL.Vfrom
  and Vfrom_def = ZFC_in_HOL.Vfrom_def
  and rank_def = ZFC_Cardinals.rank_def
  and add_Limit = Kirby.add_Limit
  and Limit_Vfrom_eq = ZFC_in_HOL.Limit_Vfrom_eq
  and VSigma_def = ZFC_Cardinals.VSigma_def
  and add_Sup_distrib_id = Kirby.add_Sup_distrib_id
  and Limit_add_Sup_distrib = Kirby.Limit_add_Sup_distrib
  and TC_mult = Kirby.TC_mult
  and add_Sup_distrib = Kirby.add_Sup_distrib



subsection\<open>Disjoint union\<close>


text\<open>
Fundamental properties have already been exposed in the main library
of \<open>ZFC in HOL\<close>.
\<close>

syntax "_VPRODUCT" :: "pttrn \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (\<open>(3\<Coprod>\<^sub>\<times>_\<in>\<^sub>\<circ>_./ _)\<close> [0, 0, 10] 10)

translations "\<Coprod>\<^sub>\<times>i\<in>\<^sub>\<circ>I. A" \<rightleftharpoons> "CONST VSigma I (\<lambda>i. A)"


text\<open>Further rules.\<close>

lemma vdunion_expE[elim!]:
  assumes "c \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<Union>\<^sub>\<circ>x\<in>\<^sub>\<circ>A i. set {\<langle>i, x\<rangle>})"
  obtains i a where "i \<in>\<^sub>\<circ> I" and "a \<in>\<^sub>\<circ> A i" and "c = \<langle>i, a\<rangle>"
  using assms by (clarsimp simp: vrange_VLambda vimage_VLambda_vrange_rep)

lemma vdunion_def: "(\<Coprod>\<^sub>\<times>i\<in>\<^sub>\<circ>I. A i) = (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<Union>\<^sub>\<circ>x\<in>\<^sub>\<circ>A i. set {\<langle>i, x\<rangle>})" 
  by (auto simp: vrange_VLambda vimage_VLambda_vrange_rep)


text\<open>Set operations.\<close>

lemma vdunion_vsingleton: "(\<Coprod>\<^sub>\<times>i\<in>\<^sub>\<circ>set{c}. A i) = set {c} \<times>\<^sub>\<circ> A c" by auto

lemma vdunion_vdoubleton: 
  "(\<Coprod>\<^sub>\<times>i\<in>\<^sub>\<circ>set{a, b}. A i) = set {a} \<times>\<^sub>\<circ> A a \<union>\<^sub>\<circ> set {b} \<times>\<^sub>\<circ> A b" 
  by auto


text\<open>Connections.\<close>

lemma vdunion_vsum: "(\<Coprod>\<^sub>\<times>i\<in>\<^sub>\<circ>set{0, 1}. if i=0 then A else B) = A \<Uplus> B"
  unfolding vdunion_vdoubleton vsum_def by simp



subsection\<open>Infinite Cartesian product\<close>

definition vproduct :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "vproduct I A = set {f. vsv f \<and> \<D>\<^sub>\<circ> f = I \<and> (\<forall>i\<in>\<^sub>\<circ>I. f\<lparr>i\<rparr> \<in>\<^sub>\<circ> A i)}"

syntax "_VPRODUCT" :: "pttrn \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (\<open>(3\<Prod>\<^sub>\<circ>_\<in>\<^sub>\<circ>_./ _)\<close> [0, 0, 10] 10)

translations "\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A" \<rightleftharpoons> "CONST vproduct I (\<lambda>i. A)"

lemma small_vproduct[simp]:
  "small {f. vsv f \<and> \<D>\<^sub>\<circ> f = I \<and> (\<forall>i\<in>\<^sub>\<circ>I. f\<lparr>i\<rparr> \<in>\<^sub>\<circ> A i)}"
  (is \<open>small ?A\<close>)
proof-
  from small_vsv[of I \<open>(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)\<close>] have 
    "small {f. vsv f \<and> \<D>\<^sub>\<circ> f = I \<and> \<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)}"
    by simp
  moreover have "?A \<subseteq> {f. vsv f \<and> \<D>\<^sub>\<circ> f = I \<and> \<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)}"
  proof(intro subsetI, unfold mem_Collect_eq, elim conjE, intro conjI)
    fix f assume prems: "vsv f" "\<D>\<^sub>\<circ> f = I" "\<forall>i\<in>elts I. f\<lparr>i\<rparr> \<in>\<^sub>\<circ> A i"
    interpret vsv f by (rule prems(1))
    show "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)"
    proof(intro vsubsetI)
      fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> f"
      with prems(2) obtain i where y_def: "y = f\<lparr>i\<rparr>" and i: "i \<in>\<^sub>\<circ> I"
        by (blast dest: vrange_atD)
      from i prems(3) vifunionI show "y \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)" 
        unfolding y_def by auto
    qed
  qed
  ultimately show ?thesis by (metis (lifting) smaller_than_small)
qed


text\<open>Rules.\<close>

lemma vproductI[intro!]:
  assumes "vsv f" and "\<D>\<^sub>\<circ> f = I" and "\<forall>i\<in>\<^sub>\<circ>I. f\<lparr>i\<rparr> \<in>\<^sub>\<circ> A i"
  shows "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)"
  using assms small_vproduct unfolding vproduct_def by auto

lemma vproductD[dest]:
  assumes "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)"
  shows "vsv f" 
    and "\<D>\<^sub>\<circ> f = I"
    and "\<forall>i\<in>\<^sub>\<circ>I. f\<lparr>i\<rparr> \<in>\<^sub>\<circ> A i"
  using assms unfolding vproduct_def by auto

lemma vproductE[elim!]:
  assumes "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)"
  obtains "vsv f" and "\<D>\<^sub>\<circ> f = I" and "\<forall>i\<in>\<^sub>\<circ>I. f\<lparr>i\<rparr> \<in>\<^sub>\<circ> A i"
  using assms unfolding vproduct_def by auto


text\<open>Set operations.\<close>

lemma vproduct_index_vempty[simp]: "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>0. A i) = set {0}"
proof-
  have "{f. vsv f \<and> \<D>\<^sub>\<circ> f = 0 \<and> (\<forall>i\<in>\<^sub>\<circ>0. f\<lparr>i\<rparr> \<in>\<^sub>\<circ> A i)} = {0}"
    using vbrelation.vlrestriction_vdomain vsv_eqI by fastforce
  then show ?thesis unfolding vproduct_def by simp
qed

lemma vproduct_vsingletonI:
  assumes "f\<lparr>c\<rparr> \<in>\<^sub>\<circ> A c" and "f = set {\<langle>c, f\<lparr>c\<rparr>\<rangle>}" 
  shows "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>set{c}. A i)"
  using assms 
  apply(intro vproductI)
  subgoal by (metis rel_vsingleton.vsv_axioms)
  subgoal by (force intro!: vsubset_antisym)
  subgoal by auto
  done

lemma vproduct_vsingletonD: 
  assumes "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>set{c}. A i)" 
  shows "vsv f" and "f\<lparr>c\<rparr> \<in>\<^sub>\<circ> A c" and "f = set {\<langle>c, f\<lparr>c\<rparr>\<rangle>}"
proof-
  from assms show "f = set {\<langle>c, f\<lparr>c\<rparr>\<rangle>}"
    by (elim vproductE) (metis VLambda_vsingleton  vsv.vsv_is_VLambda)
qed (use assms in auto)

lemma vproduct_vsingletonE: 
  assumes "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>set{c}. A i)" 
  obtains "vsv f" and "f\<lparr>c\<rparr> \<in>\<^sub>\<circ> A c" and "f = set {\<langle>c, f\<lparr>c\<rparr>\<rangle>}"
  using assms vproduct_vsingletonD that by auto

lemma vproduct_vsingleton_iff: 
  "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>set{c}. A i) \<longleftrightarrow> f\<lparr>c\<rparr> \<in>\<^sub>\<circ> A c \<and> f = set {\<langle>c, f\<lparr>c\<rparr>\<rangle>}" 
  by (rule iffI) (auto simp: vproduct_vsingletonD intro!: vproduct_vsingletonI)

lemma vproduct_vdoubletonI[intro]:
  assumes "vsv f"
    and "f\<lparr>a\<rparr> \<in>\<^sub>\<circ> A a" 
    and "f\<lparr>b\<rparr> \<in>\<^sub>\<circ> A b" 
    and "\<D>\<^sub>\<circ> f = set {a, b}"
    and "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A a \<union>\<^sub>\<circ> A b"
  shows "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>set {a, b}. A i)"
  using assms vifunion_vdoubleton by (intro vproductI) auto

lemma vproduct_vdoubletonD[dest]: 
  assumes "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>set{a, b}. A i)" 
  shows "vsv f"
    and "f\<lparr>a\<rparr> \<in>\<^sub>\<circ> A a" 
    and "f\<lparr>b\<rparr> \<in>\<^sub>\<circ> A b" 
    and "\<D>\<^sub>\<circ> f = set {a, b}" 
    and "f = set {\<langle>a, f\<lparr>a\<rparr>\<rangle>, \<langle>b, f\<lparr>b\<rparr>\<rangle>}"
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms by auto
  subgoal using assms vifunion_vdoubleton by fastforce
  subgoal by (metis assms VLambda_vdoubleton vproductE vsv.vsv_is_VLambda)
  done

lemma vproduct_vdoubletonE: 
  assumes "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>set{a, b}. A i)" 
  obtains "vsv f"
    and "f\<lparr>a\<rparr> \<in>\<^sub>\<circ> A a" 
    and "f\<lparr>b\<rparr> \<in>\<^sub>\<circ> A b" 
    and "\<D>\<^sub>\<circ> f = set {a, b}" 
    and "f = set {\<langle>a, f\<lparr>a\<rparr>\<rangle>, \<langle>b, f\<lparr>b\<rparr>\<rangle>}"
  using assms vproduct_vdoubletonD that by simp

lemma vproduct_vdoubleton_iff: 
  "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>set {a, b}. A i) \<longleftrightarrow> 
    vsv f \<and> 
    f\<lparr>a\<rparr> \<in>\<^sub>\<circ> A a \<and> 
    f\<lparr>b\<rparr> \<in>\<^sub>\<circ> A b \<and> 
    \<D>\<^sub>\<circ> f = set {a, b} \<and> 
    f = set {\<langle>a, f\<lparr>a\<rparr>\<rangle>, \<langle>b, f\<lparr>b\<rparr>\<rangle>}" 
  by (force elim!: vproduct_vdoubletonE)+


text\<open>Elementary properties.\<close>

lemma vproduct_eq_vemptyI:
  assumes "i \<in>\<^sub>\<circ> I" and "A i = 0"
  shows "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) = 0"
proof(intro vsubset_antisym vsubsetI)
  fix x assume prems: "x \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)"
  from assms vproductD(3)[OF prems] show "x \<in>\<^sub>\<circ> 0" by auto
qed auto

lemma vproduct_eq_vemptyD:
  assumes "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<noteq> 0"
  shows "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> A i \<noteq> 0"
proof(rule ccontr, unfold not_not)
  fix i assume prems: "i \<in>\<^sub>\<circ> I" "A i = 0"
  with vproduct_eq_vemptyI[where A=A, OF prems] assms show False by simp
qed

lemma vproduct_vrange:
  assumes "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)"
  shows "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)"
proof(intro vsubsetI)
  fix x assume prems: "x \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> f"
  have vsv_f: "vsv f"
    and dom_f: "\<D>\<^sub>\<circ> f = I"
    and fi: "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> f\<lparr>i\<rparr> \<in>\<^sub>\<circ> A i"
    by (simp_all add: vproductD[OF assms, rule_format])
  interpret f: vsv f by (rule vsv_f)
  from prems dom_f obtain i where x_def: "x = f\<lparr>i\<rparr>" and i: "i \<in>\<^sub>\<circ> I"
    by (auto elim: f.vrange_atE) 
  from i fi show "x \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)" unfolding x_def by (intro vifunionI) auto
qed

lemma vproduct_vsubset_VPow: "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<subseteq>\<^sub>\<circ> VPow (I \<times>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i))"
proof(intro vsubsetI)
  fix f assume "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)"
  then have vsv: "vsv f" 
    and domain: "\<D>\<^sub>\<circ> f = I" 
    and range: "\<forall>i\<in>elts I. f\<lparr>i\<rparr> \<in>\<^sub>\<circ> A i" 
    by auto
  interpret f: vsv f by (rule vsv)
  have "f \<subseteq>\<^sub>\<circ> I \<times>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)"
  proof(intro vsubsetI)
    fix x assume prems: "x \<in>\<^sub>\<circ> f"
    then obtain a b where x_def: "x = \<langle>a, b\<rangle>" by (elim f.vbrelation_vinE)
    with prems have "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> f" and "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> f" by auto
    with range domain prems show "x \<in>\<^sub>\<circ> I \<times>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)"
      by (fastforce simp: x_def)
  qed
  then show "f \<in>\<^sub>\<circ> VPow (I \<times>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i))" by simp
qed

lemma VLambda_in_vproduct:
  assumes "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> f i \<in>\<^sub>\<circ> A i"
  shows "(\<lambda>i\<in>\<^sub>\<circ>I. f i) \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)"
  using assms by (simp add: vproductI vsv.vsv_vrange_vsubset_vifunion_app)

lemma vproduct_cong:
  assumes "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> f i = g i"
  shows "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) = (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. g i)"
proof-
  have "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i) \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. g i)" if "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> f i = g i" for f g
  proof(intro vsubsetI)
    fix x assume "x \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. f i)"
    note xD = vproductD[OF this]     
    interpret vsv x by (rule xD(1))
    show "x \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. g i)" 
      by (metis xD(2,3) that VLambda_in_vproduct vsv_is_VLambda)
  qed
  with assms show ?thesis by (intro vsubset_antisym) auto
qed

lemma vproduct_ex_in_vproduct:
  assumes "x \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>J. A i)" and "J \<subseteq>\<^sub>\<circ> I" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> A i \<noteq> 0"
  obtains X where "X \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)" and "x = X \<restriction>\<^sup>l\<^sub>\<circ> J"
proof-
  define X where "X = (\<lambda>i\<in>\<^sub>\<circ>I. if i \<in>\<^sub>\<circ> J then x\<lparr>i\<rparr> else (SOME x. x \<in>\<^sub>\<circ> A i))" 
  have X: "X \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)"
    by (intro vproductI) (use assms in \<open>auto simp: X_def\<close>)
  moreover have "x = X \<restriction>\<^sup>l\<^sub>\<circ> J"
  proof(rule vsv_eqI)
    from assms(1) have [simp]: "\<D>\<^sub>\<circ> x = J" by clarsimp 
    moreover from assms(2) have "\<D>\<^sub>\<circ> (X \<restriction>\<^sup>l\<^sub>\<circ> J) = J" unfolding X_def by fastforce
    ultimately show "\<D>\<^sub>\<circ> x = \<D>\<^sub>\<circ> (X \<restriction>\<^sup>l\<^sub>\<circ> J)" by simp 
    show "x\<lparr>i\<rparr> = (X \<restriction>\<^sup>l\<^sub>\<circ> J)\<lparr>i\<rparr>" if "i \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> x" for i
      using that assms(2) unfolding X_def by auto
  qed (use assms X in auto)
  ultimately show ?thesis using that by simp
qed

lemma vproduct_vsingleton_def: "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>set {j}. A i) = (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>set {j}. A j)"
  by auto

lemma vprojection_in_VUnionI:
  assumes "A \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i)" and "f \<in>\<^sub>\<circ> A" and "i \<in>\<^sub>\<circ> I"
  shows "f\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>A))"
proof(intro VUnionI)
  show "f \<in>\<^sub>\<circ> A" by (rule assms(2))
  from assms(1,2) have "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i)" by auto
  note f = vproductD[OF this, rule_format]
  interpret vsv f rewrites "\<D>\<^sub>\<circ> f = I" by (auto intro: f(1) simp: f(2))
  show "\<langle>i, f\<lparr>i\<rparr>\<rangle> \<in>\<^sub>\<circ> f" by (meson assms(3) vsv_appE)
  show "set {i, f\<lparr>i\<rparr>} \<in>\<^sub>\<circ> \<langle>i, f\<lparr>i\<rparr>\<rangle>" unfolding vpair_def by simp
qed simp


subsection\<open>Projection\<close>

definition vprojection :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> V"
  where "vprojection I A i = (\<lambda>f\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i). f\<lparr>i\<rparr>)"


text\<open>Rules.\<close>

mk_VLambda vprojection_def
  |vsv vprojection_vsv[intro]|
  |vdomain vprojection_vdomain[simp]|
  |app vprojection_app[simp, intro]|


text\<open>Elementary results.\<close>

lemma vprojection_vrange_vsubset: 
  assumes "i \<in>\<^sub>\<circ> I" 
  shows "\<R>\<^sub>\<circ> (vprojection I A i) \<subseteq>\<^sub>\<circ> A i"
  unfolding vprojection_def
proof(intro vrange_VLambda_vsubset)
  fix f assume prems: "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)"
  show "f\<lparr>i\<rparr> \<in>\<^sub>\<circ> A i" by (intro vproductD(3)[OF prems, rule_format] assms)
qed

lemma vprojection_vrange: 
  assumes "i \<in>\<^sub>\<circ> I" and "\<And>j. j \<in>\<^sub>\<circ> I \<Longrightarrow> A j \<noteq> 0"
  shows "\<R>\<^sub>\<circ> (vprojection I A i) = A i"
proof
  (
    intro 
      vsubset_antisym vprojection_vrange_vsubset vrange_VLambda_vsubset assms(1)
  )
  show "A i \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (vprojection I A i)"
  proof(intro vsubsetI)
    fix x assume prems: "x \<in>\<^sub>\<circ> A i"
    obtain f 
      where f: "\<And>x. x \<in>\<^sub>\<circ> set {A i | i. i \<in>\<^sub>\<circ> I} \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> f\<lparr>x\<rparr> \<in>\<^sub>\<circ> x" 
        and "vsv f"
      using that by (rule Axiom_of_Choice)
    define f' where "f' = (\<lambda>j\<in>\<^sub>\<circ>I. if j = i then x else f\<lparr>A j\<rparr>)"
    show "x \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (vprojection I A i)"               
      unfolding vprojection_def
    proof(rule rel_VLambda.vsv_vimageI2')
      show "f' \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<lambda>f\<in>\<^sub>\<circ>vproduct I A. f\<lparr>i\<rparr>)"
        unfolding vdomain_VLambda
      proof(intro vproductI, unfold Ball_def; (intro allI conjI impI)?)
        fix j assume "j \<in>\<^sub>\<circ> I"
        with prems assms(2) show "f'\<lparr>j\<rparr> \<in>\<^sub>\<circ> A j"
          unfolding f'_def by (cases \<open>j = i\<close>) (auto intro!: f)
      qed (simp_all add: f'_def)
      with assms(1) show "x = (\<lambda>f\<in>\<^sub>\<circ>vproduct I A. f\<lparr>i\<rparr>)\<lparr>f'\<rparr>"
        unfolding f'_def by simp
    qed
  qed
qed



subsection\<open>Cartesian power of a set\<close>

definition vcpower :: "V \<Rightarrow> V \<Rightarrow> V" (infixr \<open>^\<^sub>\<times>\<close> 80)
  where "A ^\<^sub>\<times> n = (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>n. A)"


text\<open>Rules.\<close>

lemma vcpowerI[intro]:
  assumes "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>n. A)"
  shows "f \<in>\<^sub>\<circ> (A ^\<^sub>\<times> n)" 
  using assms unfolding vcpower_def by auto

lemma vcpowerD[dest]:
  assumes "f \<in>\<^sub>\<circ> (A ^\<^sub>\<times> n)"
  shows "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>n. A)"
  using assms unfolding vcpower_def by auto

lemma vcpowerE[elim]:
  assumes "f \<in>\<^sub>\<circ> (A ^\<^sub>\<times> n)" and "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>n. A) \<Longrightarrow> P"
  shows P
  using assms unfolding vcpower_def by auto


text\<open>Set operations.\<close>

lemma vcpower_index_vempty[simp]: "A ^\<^sub>\<times> 0 = set {0}"
  unfolding vcpower_def by (rule vproduct_index_vempty)

lemma vcpower_of_vempty: 
  assumes "n \<noteq> 0"
  shows "0 ^\<^sub>\<times> n = 0"
  using assms unfolding vcpower_def vproduct_def by simp


text\<open>Connections.\<close>

lemma vcpower_vdomain: 
  assumes "f \<in>\<^sub>\<circ> (A ^\<^sub>\<times> n)"
  shows "\<D>\<^sub>\<circ> f = n"
  using assms by auto

lemma vcpower_vrange:
  assumes "f \<in>\<^sub>\<circ> (A ^\<^sub>\<times> n)"
  shows "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A"
  using assms by (intro vsubsetI; elim vcpowerE vproductE) auto

text\<open>\newpage\<close>

end