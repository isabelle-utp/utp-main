(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Further set algebra and other miscellaneous results\<close>
theory CZH_Sets_Sets
  imports CZH_Sets_Introduction
begin



subsection\<open>Background\<close>


text\<open>
This section presents further set algebra and various elementary properties
of sets.

Many of the results that are presented in this section
were carried over (with amendments) from the theories \<^text>\<open>Set\<close> 
and \<^text>\<open>Complete_Lattices\<close> in the main library.
\<close>

declare elts_sup_iff[simp del] 



subsection\<open>Further notation\<close>


subsubsection\<open>Set membership\<close>

abbreviation vmember :: "V \<Rightarrow> V \<Rightarrow> bool" ("(_/ \<in>\<^sub>\<circ> _)" [51, 51] 50) 
  where "vmember x A \<equiv> (x \<in> elts A)"
notation vmember ("'(\<in>\<^sub>\<circ>')")
  and vmember ("(_/ \<in>\<^sub>\<circ> _)" [51, 51] 50)

abbreviation not_vmember :: "V \<Rightarrow> V \<Rightarrow> bool" ("(_/ \<notin>\<^sub>\<circ> _)" [51, 51] 50) 
  where "not_vmember x A \<equiv> (x \<notin> elts A)" 
notation
  not_vmember ("'(\<notin>\<^sub>\<circ>')") and
  not_vmember ("(_/ \<notin>\<^sub>\<circ> _)" [51, 51] 50)


subsubsection\<open>Subsets\<close>

abbreviation vsubset :: "V \<Rightarrow> V \<Rightarrow> bool"
  where "vsubset \<equiv> less"
abbreviation vsubset_eq :: "V \<Rightarrow> V \<Rightarrow> bool"
  where "vsubset_eq \<equiv> less_eq"

notation vsubset ("'(\<subset>\<^sub>\<circ>')") 
  and vsubset ("(_/ \<subset>\<^sub>\<circ> _)" [51, 51] 50) 
  and vsubset_eq ("'(\<subseteq>\<^sub>\<circ>')") 
  and vsubset_eq ("(_/ \<subseteq>\<^sub>\<circ> _)" [51, 51] 50)


subsubsection\<open>Ball\<close>

syntax
  "_VBall" :: "pttrn \<Rightarrow> V \<Rightarrow> bool \<Rightarrow> bool" ("(3\<forall>(_/\<in>\<^sub>\<circ>_)./ _)" [0, 0, 10] 10)
  "_VBex" :: "pttrn \<Rightarrow> V \<Rightarrow> bool \<Rightarrow> bool" ("(3\<exists>(_/\<in>\<^sub>\<circ>_)./ _)" [0, 0, 10] 10)
  "_VBex1" :: "pttrn \<Rightarrow> V \<Rightarrow> bool \<Rightarrow> bool" ("(3\<exists>!(_/\<in>\<^sub>\<circ>_)./ _)" [0, 0, 10] 10)

translations
  "\<forall>x\<in>\<^sub>\<circ>A. P" \<rightleftharpoons> "CONST Ball (CONST elts A) (\<lambda>x. P)"
  "\<exists>x\<in>\<^sub>\<circ>A. P" \<rightleftharpoons> "CONST Bex (CONST elts A) (\<lambda>x. P)"
  "\<exists>!x\<in>\<^sub>\<circ>A. P" \<rightharpoonup> "\<exists>!x. x \<in>\<^sub>\<circ> A \<and> P"


subsubsection\<open>\<open>VLambda\<close>\<close>


text\<open>The following notation was adapted from \cite{paulson_hereditarily_2013}.\<close>

syntax "_vlam" :: "[pttrn, V, V] \<Rightarrow> V" (\<open>(3\<lambda>_\<in>\<^sub>\<circ>_./ _)\<close> 10)
translations "\<lambda>x\<in>\<^sub>\<circ>A. f" \<rightleftharpoons> "CONST VLambda A (\<lambda>x. f)"


subsubsection\<open>Intersection and union\<close>

abbreviation vintersection :: "V \<Rightarrow> V \<Rightarrow> V" (infixl "\<inter>\<^sub>\<circ>" 70)
  where "(\<inter>\<^sub>\<circ>) \<equiv> (\<sqinter>)"
notation vintersection (infixl "\<inter>\<^sub>\<circ>" 70)

abbreviation vunion :: "V \<Rightarrow> V \<Rightarrow> V"  (infixl "\<union>\<^sub>\<circ>" 65)
  where "vunion \<equiv> sup"
notation vunion (infixl "\<union>\<^sub>\<circ>" 65)

abbreviation VInter :: "V \<Rightarrow> V" (\<open>\<Inter>\<^sub>\<circ>\<close>)
  where "\<Inter>\<^sub>\<circ> A \<equiv> \<Sqinter> (elts A)"
notation VInter (\<open>\<Inter>\<^sub>\<circ>\<close>)

abbreviation VUnion :: "V \<Rightarrow> V" (\<open>\<Union>\<^sub>\<circ>\<close>)
  where "\<Union>\<^sub>\<circ>A \<equiv> \<Squnion> (elts A)"
notation VUnion (\<open>\<Union>\<^sub>\<circ>\<close>)


subsubsection\<open>Miscellaneous\<close>

notation app (\<open>_\<lparr>_\<rparr>\<close> [999, 50] 999)
notation vtimes (infixr "\<times>\<^sub>\<circ>" 80)



subsection\<open>Elementary results.\<close>

lemma vempty_nin[simp]: "a \<notin>\<^sub>\<circ> 0" by simp

lemma vemptyE:
  assumes "A \<noteq> 0"
  obtains x where "x \<in>\<^sub>\<circ> A" 
  using assms trad_foundation by auto

lemma in_set_CollectI:
  assumes "P x" and "small {x. P x}"
  shows "x \<in>\<^sub>\<circ> set {x. P x}"
  using assms by simp

lemma small_setcompr2:
  assumes "small {f x y | x y. P x y}" and "a \<in>\<^sub>\<circ> set {f x y | x y. P x y}"
  obtains x' y' where "a = f x' y'" and "P x' y'"
  using assms by auto

lemma in_small_setI:
  assumes "small A" and "x \<in> A"
  shows "x \<in>\<^sub>\<circ> set A"
  using assms by simp

lemma in_small_setD:
  assumes "x \<in>\<^sub>\<circ> set A" and "small A" 
  shows "x \<in> A"
  using assms by simp

lemma in_small_setE:
  assumes "a \<in>\<^sub>\<circ> set A" and "small A"
  obtains "a \<in> A"
  using assms by auto

lemma small_set_vsubset:
  assumes "small A" and "A \<subseteq> elts B"
  shows "set A \<subseteq>\<^sub>\<circ> B"
  using assms by auto

lemma some_in_set_if_set_neq_vempty[simp]:
  assumes "A \<noteq> 0"
  shows "(SOME x. x \<in>\<^sub>\<circ> A) \<in>\<^sub>\<circ> A"
  by (meson assms someI_ex vemptyE)

lemma small_vsubset_set[intro, simp]:
  assumes "small B" and "A \<subseteq> B"
  shows "set A \<subseteq>\<^sub>\<circ> set B"
  using assms by (auto simp: subset_iff_less_eq_V)

lemma vset_neq_1:
  assumes "b \<notin>\<^sub>\<circ> A" and "a \<in>\<^sub>\<circ> A"
  shows "b \<noteq> a"
  using assms by auto

lemma vset_neq_2:
  assumes "b \<in>\<^sub>\<circ> A" and "a \<notin>\<^sub>\<circ> A"
  shows "b \<noteq> a"
  using assms by auto

lemma nin_vinsertI:
  assumes "a \<noteq> b" and "a \<notin>\<^sub>\<circ> A"
  shows "a \<notin>\<^sub>\<circ> vinsert b A"
  using assms by clarsimp

lemma vsubset_if_subset:
  assumes "elts A \<subseteq> elts B"
  shows "A \<subseteq>\<^sub>\<circ> B"
  using assms by auto

lemma small_set_comprehension[simp]: "small {A i | i. i \<in>\<^sub>\<circ> I}"
proof(rule smaller_than_small)
  show "small (A ` elts I)" by auto
qed auto



subsection\<open>\<open>VBall\<close>\<close>

lemma vball_cong:
  assumes "A = B" and "\<And>x. x \<in>\<^sub>\<circ> B \<Longrightarrow> P x \<longleftrightarrow> Q x"
  shows "(\<forall>x\<in>\<^sub>\<circ>A. P x) \<longleftrightarrow> (\<forall>x\<in>\<^sub>\<circ>B. Q x)"
  by (simp add: assms)

lemma vball_cong_simp[cong]:
  assumes "A = B" and "\<And>x. x \<in>\<^sub>\<circ> B =simp=> P x \<longleftrightarrow> Q x " 
  shows "(\<forall>x\<in>\<^sub>\<circ>A. P x) \<longleftrightarrow> (\<forall>x\<in>\<^sub>\<circ>B. Q x)"
  using assms by (simp add: simp_implies_def)



subsection\<open>\<open>VBex\<close>\<close>

lemma vbex_cong:
  assumes "A = B" and  "\<And>x. x \<in>\<^sub>\<circ> B \<Longrightarrow> P x \<longleftrightarrow> Q x" 
  shows "(\<exists>x\<in>\<^sub>\<circ>A. P x) \<longleftrightarrow> (\<exists>x\<in>\<^sub>\<circ>B. Q x)"
  using assms by (simp cong: conj_cong)

lemma vbex_cong_simp[cong]:
  assumes "A = B" and "\<And>x. x \<in>\<^sub>\<circ> B =simp=> P x \<longleftrightarrow> Q x "
  shows "(\<exists>x\<in>\<^sub>\<circ>A. P x) \<longleftrightarrow> (\<exists>x\<in>\<^sub>\<circ>B. Q x)"
  using assms by (simp add:  simp_implies_def)



subsection\<open>Subset\<close>


text\<open>Rules.\<close>

lemma vsubset_antisym: 
  assumes "A \<subseteq>\<^sub>\<circ> B" and "B \<subseteq>\<^sub>\<circ> A" 
  shows "A = B"
  using assms by simp

lemma vsubsetI:
  assumes "\<And>x. x \<in>\<^sub>\<circ> A \<Longrightarrow> x \<in>\<^sub>\<circ> B"
  shows "A \<subseteq>\<^sub>\<circ> B"
  using assms by auto

lemma vpsubsetI:
  assumes "A \<subseteq>\<^sub>\<circ> B" and "x \<notin>\<^sub>\<circ> A" and "x \<in>\<^sub>\<circ> B"
  shows "A \<subset>\<^sub>\<circ> B"
  using assms unfolding less_V_def by auto

lemma vsubsetD:
  assumes "A \<subseteq>\<^sub>\<circ> B"
  shows "\<And>x. x \<in>\<^sub>\<circ> A \<Longrightarrow> x \<in>\<^sub>\<circ> B"
  using assms by auto

lemma vsubsetE:
  assumes "A \<subseteq>\<^sub>\<circ> B" and "(\<And>x. x \<in>\<^sub>\<circ> A \<Longrightarrow> x \<in>\<^sub>\<circ> B) \<Longrightarrow> P"
  shows P
  using assms by auto

lemma vpsubsetE:
  assumes "A \<subset>\<^sub>\<circ> B"
  obtains x where "A \<subseteq>\<^sub>\<circ> B" and "x \<notin>\<^sub>\<circ> A" and "x \<in>\<^sub>\<circ> B"
  using assms unfolding less_V_def by (meson V_equalityI vsubsetE)

lemma vsubset_iff: "A \<subseteq>\<^sub>\<circ> B \<longleftrightarrow> (\<forall>t. t \<in>\<^sub>\<circ> A \<longrightarrow> t \<in>\<^sub>\<circ> B)" by blast


text\<open>Elementary properties.\<close>

lemma vsubset_eq: "A \<subseteq>\<^sub>\<circ> B \<longleftrightarrow> (\<forall>x\<in>\<^sub>\<circ>A. x \<in>\<^sub>\<circ> B)" by auto

lemma vsubset_transitive[intro]: 
  assumes "A \<subseteq>\<^sub>\<circ> B" and "B \<subseteq>\<^sub>\<circ> C"
  shows "A \<subseteq>\<^sub>\<circ> C"
  using assms by simp

lemma vsubset_reflexive: "A \<subseteq>\<^sub>\<circ> A" by simp


text\<open>Set operations.\<close>

lemma vsubset_vempty: "0 \<subseteq>\<^sub>\<circ> A" by simp

lemma vsubset_vsingleton_left: "set {a} \<subseteq>\<^sub>\<circ> A \<longleftrightarrow> a \<in>\<^sub>\<circ> A" by auto

lemmas vsubset_vsingleton_leftD[dest] = vsubset_vsingleton_left[THEN iffD1]
  and vsubset_vsingleton_leftI[intro] = vsubset_vsingleton_left[THEN iffD2]

lemma vsubset_vsingleton_right: "A \<subseteq>\<^sub>\<circ> set {a} \<longleftrightarrow> A = set {a} \<or> A = 0" 
  by (auto intro!: vsubset_antisym)

lemmas vsubset_vsingleton_rightD[dest] = vsubset_vsingleton_right[THEN iffD1]
  and vsubset_vsingleton_rightI[intro] = vsubset_vsingleton_right[THEN iffD2]

lemma vsubset_vdoubleton_leftD[dest]:
  assumes "set {a, b} \<subseteq>\<^sub>\<circ> A"
  shows "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A"
  using assms by auto

lemma vsubset_vdoubleton_leftI[intro]:
  assumes "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A"
  shows "set {a, b} \<subseteq>\<^sub>\<circ> A"
  using assms by auto

lemma vsubset_vinsert_leftD[dest]:
  assumes "vinsert a A \<subseteq>\<^sub>\<circ> B"
  shows "A \<subseteq>\<^sub>\<circ> B"
  using assms by auto

lemma vsubset_vinsert_leftI[intro]:
  assumes "A \<subseteq>\<^sub>\<circ> B" and "a \<in>\<^sub>\<circ> B"
  shows "vinsert a A \<subseteq>\<^sub>\<circ> B" 
  using assms by auto

lemma vsubset_vinsert_vinsertI[intro]:
  assumes "A \<subseteq>\<^sub>\<circ> vinsert b B"
  shows "vinsert b A \<subseteq>\<^sub>\<circ> vinsert b B"
  using assms by auto

lemma vsubset_vinsert_rightI[intro]:
  assumes "A \<subseteq>\<^sub>\<circ> B"
  shows "A \<subseteq>\<^sub>\<circ> vinsert b B"
  using assms by auto
                                     
lemmas vsubset_VPow = VPow_le_VPow_iff

lemmas vsubset_VPowD = vsubset_VPow[THEN iffD1]
  and vsubset_VPowI = vsubset_VPow[THEN iffD2]


text\<open>Special properties.\<close>

lemma vsubset_contraD:
  assumes "A \<subseteq>\<^sub>\<circ> B" and "c \<notin>\<^sub>\<circ> B" 
  shows "c \<notin>\<^sub>\<circ> A" 
  using assms by auto



subsection\<open>Equality\<close>


text\<open>Rules.\<close>

lemma vequalityD1: 
  assumes "A = B"
  shows "A \<subseteq>\<^sub>\<circ> B" 
  using assms by simp

lemma vequalityD2: 
  assumes "A = B"
  shows "B \<subseteq>\<^sub>\<circ> A" 
  using assms by simp

lemma vequalityE: 
  assumes "A = B" and "\<lbrakk> A \<subseteq>\<^sub>\<circ> B; B \<subseteq>\<^sub>\<circ> A \<rbrakk> \<Longrightarrow> P" 
  shows P
  using assms by simp

lemma vequalityCE[elim]: 
  assumes "A = B" and "\<lbrakk> c \<in>\<^sub>\<circ> A; c \<in>\<^sub>\<circ> B \<rbrakk> \<Longrightarrow> P" and "\<lbrakk> c \<notin>\<^sub>\<circ> A; c \<notin>\<^sub>\<circ> B \<rbrakk> \<Longrightarrow> P" 
  shows P
  using assms by auto



subsection\<open>Binary intersection\<close>

lemma vintersection_def: "A \<inter>\<^sub>\<circ> B = set {x. x \<in>\<^sub>\<circ> A \<and> x \<in>\<^sub>\<circ> B}" 
  by (metis Int_def inf_V_def)

lemma small_vintersection_set[simp]: "small {x. x \<in>\<^sub>\<circ> A \<and> x \<in>\<^sub>\<circ> B}" 
  by (rule down[of _ A]) auto


text\<open>Rules.\<close>

lemma vintersection_iff[simp]: "x \<in>\<^sub>\<circ> A \<inter>\<^sub>\<circ> B \<longleftrightarrow> x \<in>\<^sub>\<circ> A \<and> x \<in>\<^sub>\<circ> B" 
  unfolding vintersection_def by simp

lemma vintersectionI[intro!]: 
  assumes "x \<in>\<^sub>\<circ> A" and "x \<in>\<^sub>\<circ> B" 
  shows "x \<in>\<^sub>\<circ> A \<inter>\<^sub>\<circ> B" 
  using assms by simp

lemma vintersectionD1[dest]: 
  assumes "x \<in>\<^sub>\<circ> A \<inter>\<^sub>\<circ> B"
  shows "x \<in>\<^sub>\<circ> A" 
  using assms by simp

lemma vintersectionD2[dest]: 
  assumes "x \<in>\<^sub>\<circ> A \<inter>\<^sub>\<circ> B"
  shows "x \<in>\<^sub>\<circ> B" 
  using assms by simp

lemma vintersectionE[elim!]: 
  assumes "x \<in>\<^sub>\<circ> A \<inter>\<^sub>\<circ> B" and "x \<in>\<^sub>\<circ> A \<Longrightarrow> x \<in>\<^sub>\<circ> B \<Longrightarrow> P" 
  shows P 
  using assms by simp


text\<open>Elementary properties.\<close>

lemma vintersection_intersection: "A \<inter>\<^sub>\<circ> B = set (elts A \<inter> elts B)"
  unfolding inf_V_def by simp

lemma vintersection_assoc: "A \<inter>\<^sub>\<circ> (B \<inter>\<^sub>\<circ> C) = (A \<inter>\<^sub>\<circ> B) \<inter>\<^sub>\<circ> C" by auto

lemma vintersection_commutativity: "A \<inter>\<^sub>\<circ> B = B \<inter>\<^sub>\<circ> A" by auto


text\<open>Previous set operations.\<close>

lemma vsubset_vintersection_right: "A \<subseteq>\<^sub>\<circ> (B \<inter>\<^sub>\<circ> C) = (A \<subseteq>\<^sub>\<circ> B \<and> A \<subseteq>\<^sub>\<circ> C)" 
  by clarsimp

lemma vsubset_vintersection_rightD[dest]:
  assumes "A \<subseteq>\<^sub>\<circ> (B \<inter>\<^sub>\<circ> C)"
  shows "A \<subseteq>\<^sub>\<circ> B" and "A \<subseteq>\<^sub>\<circ> C"
  using assms by auto

lemma vsubset_vintersection_rightI[intro]:
  assumes "A \<subseteq>\<^sub>\<circ> B" and "A \<subseteq>\<^sub>\<circ> C" 
  shows "A \<subseteq>\<^sub>\<circ> (B \<inter>\<^sub>\<circ> C)"
  using assms by auto


text\<open>Set operations.\<close>

lemma vintersection_vempty: "0 \<subseteq>\<^sub>\<circ> A" by simp

lemma vintersection_vsingleton: "a \<in>\<^sub>\<circ> set {a}" by simp

lemma vintersection_vdoubleton: "a \<in>\<^sub>\<circ> set {a, b}" and "b \<in>\<^sub>\<circ> set {a, b}"  
  by simp_all

lemma vintersection_VPow[simp]: "VPow (A \<inter>\<^sub>\<circ> B) = VPow A \<inter>\<^sub>\<circ> VPow B" by auto


text\<open>Special properties.\<close>

lemma vintersection_function_mono:
  assumes "mono f"
  shows "f (A \<inter>\<^sub>\<circ> B) \<subseteq>\<^sub>\<circ> f A \<inter>\<^sub>\<circ> f B"
  using assms by (fact mono_inf)



subsection\<open>Binary union\<close>

lemma small_vunion_set: "small {x. x \<in>\<^sub>\<circ> A \<or> x \<in>\<^sub>\<circ> B}" 
  by (rule down[of _ \<open>A \<union>\<^sub>\<circ> B\<close>]) (auto simp: elts_sup_iff)


text\<open>Rules.\<close>

lemma vunion_def: "A \<union>\<^sub>\<circ> B = set {x. x \<in>\<^sub>\<circ> A \<or> x \<in>\<^sub>\<circ> B}"
  unfolding Un_def sup_V_def by simp

lemma vunion_iff[simp]: "x \<in>\<^sub>\<circ> A \<union>\<^sub>\<circ> B \<longleftrightarrow> x \<in>\<^sub>\<circ> A \<or> x \<in>\<^sub>\<circ> B" 
  by (simp add: elts_sup_iff)

lemma vunionI1:
  assumes "a \<in>\<^sub>\<circ> A"
  shows "a \<in>\<^sub>\<circ> A \<union>\<^sub>\<circ> B"
  using assms by simp

lemma vunionI2:
  assumes "a \<in>\<^sub>\<circ> B"
  shows "a \<in>\<^sub>\<circ> A \<union>\<^sub>\<circ> B"
  using assms by simp

lemma vunionCI[intro!]: 
  assumes "x \<notin>\<^sub>\<circ> B \<Longrightarrow> x \<in>\<^sub>\<circ> A"
  shows "x \<in>\<^sub>\<circ> A \<union>\<^sub>\<circ> B" 
  using assms by clarsimp

lemma vunionE[elim!]: 
  assumes "x \<in>\<^sub>\<circ> A \<union>\<^sub>\<circ> B" and "x \<in>\<^sub>\<circ> A \<Longrightarrow> P" and "x \<in>\<^sub>\<circ> B \<Longrightarrow> P" 
  shows P
  using assms by auto


text\<open>Elementary properties.\<close>

lemma vunion_union: "A \<union>\<^sub>\<circ> B = set (elts A \<union> elts B)" by auto

lemma vunion_assoc: "A \<union>\<^sub>\<circ> (B \<union>\<^sub>\<circ> C) = (A \<union>\<^sub>\<circ> B) \<union>\<^sub>\<circ> C" by auto

lemma vunion_comm: "A \<union>\<^sub>\<circ> B = B \<union>\<^sub>\<circ> A" by auto


text\<open>Previous set operations.\<close>

lemma vsubset_vunion_left: "(A \<union>\<^sub>\<circ> B) \<subseteq>\<^sub>\<circ> C \<longleftrightarrow> (A \<subseteq>\<^sub>\<circ> C \<and> B \<subseteq>\<^sub>\<circ> C)" by simp

lemma vsubset_vunion_leftD[dest]:
  assumes "(A \<union>\<^sub>\<circ> B) \<subseteq>\<^sub>\<circ> C"
  shows "A \<subseteq>\<^sub>\<circ> C" and "B \<subseteq>\<^sub>\<circ> C"
  using assms by auto

lemma vsubset_vunion_leftI[intro]:
  assumes "A \<subseteq>\<^sub>\<circ> C" and "B \<subseteq>\<^sub>\<circ> C"
  shows "(A \<union>\<^sub>\<circ> B) \<subseteq>\<^sub>\<circ> C"
  using assms by auto

lemma vintersection_vunion_left: "(A \<union>\<^sub>\<circ> B) \<inter>\<^sub>\<circ> C = (A \<inter>\<^sub>\<circ> C) \<union>\<^sub>\<circ> (B \<inter>\<^sub>\<circ> C)"
  by auto

lemma vintersection_vunion_right: "A \<inter>\<^sub>\<circ> (B \<union>\<^sub>\<circ> C) = (A \<inter>\<^sub>\<circ> B) \<union>\<^sub>\<circ> (A \<inter>\<^sub>\<circ> C)"
  by auto


text\<open>Set operations.\<close>

lemmas vunion_vempty_left = sup_V_0_left 
  and vunion_vempty_right = sup_V_0_right 

lemma vunion_vsingleton[simp]: "set {a} \<union>\<^sub>\<circ> A = vinsert a A" by auto

lemma vunion_vdoubleton[simp]: "set {a, b} \<union>\<^sub>\<circ> A = vinsert a (vinsert b A)" 
  by auto

lemma vunion_vinsert_commutativity_left: 
  "(vinsert a A) \<union>\<^sub>\<circ> B = A \<union>\<^sub>\<circ> (vinsert a B)" 
  by auto

lemma vunion_vinsert_commutativity_right: 
  "A \<union>\<^sub>\<circ> (vinsert a B) = (vinsert a A) \<union>\<^sub>\<circ> B" 
  by auto

lemma vinsert_def: "vinsert y B = set {x. x = y} \<union>\<^sub>\<circ> B" by auto

lemma vunion_vinsert_left: "(vinsert a A) \<union>\<^sub>\<circ> B = vinsert a (A \<union>\<^sub>\<circ> B)" by auto

lemma vunion_vinsert_right: "A \<union>\<^sub>\<circ> (vinsert a B) = vinsert a (A \<union>\<^sub>\<circ> B)" by auto


text\<open>Special properties.\<close>

lemma vunion_fun_mono: 
  assumes "mono f"
  shows "f A \<union>\<^sub>\<circ> f B \<subseteq>\<^sub>\<circ> f (A \<union>\<^sub>\<circ> B)"
  using assms by (fact mono_sup)



subsection\<open>Set difference\<close>

definition vdiff :: "V \<Rightarrow> V \<Rightarrow> V" (infixl \<open>-\<^sub>\<circ>\<close> 65) 
  where "A -\<^sub>\<circ> B = set {x. x \<in>\<^sub>\<circ> A \<and> x \<notin>\<^sub>\<circ> B}"
notation vdiff (infixl "-\<^sub>\<circ>" 65)

lemma small_set_vdiff[simp]: "small {x. x \<in>\<^sub>\<circ> A \<and> x \<notin>\<^sub>\<circ> B}" 
  by (rule down[of _ A]) simp


text\<open>Rules.\<close>

lemma vdiff_iff[simp]: "x \<in>\<^sub>\<circ> A -\<^sub>\<circ> B \<longleftrightarrow> x \<in>\<^sub>\<circ> A \<and> x \<notin>\<^sub>\<circ> B" 
  unfolding vdiff_def by simp

lemma vdiffI[intro!]: 
  assumes "x \<in>\<^sub>\<circ> A" and "x \<notin>\<^sub>\<circ> B" 
  shows "x \<in>\<^sub>\<circ> A -\<^sub>\<circ> B" 
  using assms by simp

lemma vdiffD1: 
  assumes "x \<in>\<^sub>\<circ> A -\<^sub>\<circ> B"
  shows "x \<in>\<^sub>\<circ> A" 
  using assms by simp

lemma vdiffD2: 
  assumes "x \<in>\<^sub>\<circ> A -\<^sub>\<circ> B" and "x \<in>\<^sub>\<circ> B" 
  shows P 
  using assms by simp

lemma vdiffE[elim!]: 
  assumes "x \<in>\<^sub>\<circ> A -\<^sub>\<circ> B" and "\<lbrakk> x \<in>\<^sub>\<circ> A; x \<notin>\<^sub>\<circ> B \<rbrakk> \<Longrightarrow> P" 
  shows P 
  using assms by simp


text\<open>Previous set operations.\<close>

lemma vsubset_vdiff: 
  assumes "A \<subseteq>\<^sub>\<circ> B -\<^sub>\<circ> C"
  shows "A \<subseteq>\<^sub>\<circ> B" 
  using assms by auto

lemma vinsert_vdiff_nin[simp]: 
  assumes "a \<notin>\<^sub>\<circ> B"
  shows "vinsert a (A -\<^sub>\<circ> B) = vinsert a A -\<^sub>\<circ> B"
  using assms by auto


text\<open>Set operations.\<close>

lemma vdiff_vempty_left[simp]: "0 -\<^sub>\<circ> A = 0" by auto

lemma vdiff_vempty_right[simp]: "A -\<^sub>\<circ> 0 = A" by auto

lemma vdiff_vsingleton_vinsert[simp]: "set {a} -\<^sub>\<circ> vinsert a A = 0" by auto

lemma vdiff_vsingleton_in[simp]: 
  assumes "a \<in>\<^sub>\<circ> A"
  shows "set {a} -\<^sub>\<circ> A = 0" 
  using assms by auto

lemma vdiff_vsingleton_nin[simp]: 
  assumes "a \<notin>\<^sub>\<circ> A"
  shows "set {a} -\<^sub>\<circ> A = set {a}" 
  using assms by auto

lemma vdiff_vinsert_vsingleton[simp]: "vinsert a A -\<^sub>\<circ> set {a} = A -\<^sub>\<circ> set {a}"
  by auto

lemma vdiff_vsingleton[simp]: 
  assumes "a \<notin>\<^sub>\<circ> A"
  shows "A -\<^sub>\<circ> set {a} = A"
  using assms by auto

lemma vdiff_vsubset: 
  assumes "A \<subseteq>\<^sub>\<circ> B" and "D \<subseteq>\<^sub>\<circ> C"
  shows "A -\<^sub>\<circ> C \<subseteq>\<^sub>\<circ> B -\<^sub>\<circ> D"
  using assms by auto

lemma vdiff_vinsert_left_in[simp]: 
  assumes "a \<in>\<^sub>\<circ> B"
  shows "(vinsert a A) -\<^sub>\<circ> B = A -\<^sub>\<circ> B"
  using assms by auto

lemma vdiff_vinsert_left_nin: 
  assumes "a \<notin>\<^sub>\<circ> B"
  shows "(vinsert a A) -\<^sub>\<circ> B = vinsert a (A -\<^sub>\<circ> B)"
  using assms by auto

lemma vdiff_vinsert_right_in: "A -\<^sub>\<circ> (vinsert a B) = A -\<^sub>\<circ> B -\<^sub>\<circ> set {a}" by auto

lemma vdiff_vinsert_right_nin[simp]: 
  assumes "a \<notin>\<^sub>\<circ> A"
  shows "A -\<^sub>\<circ> (vinsert a B) = A -\<^sub>\<circ> B"
  using assms by auto

lemma vdiff_vintersection_left: "(A \<inter>\<^sub>\<circ> B) -\<^sub>\<circ> C = (A -\<^sub>\<circ> C) \<inter>\<^sub>\<circ> (B -\<^sub>\<circ> C)" by auto

lemma vdiff_vunion_left: "(A \<union>\<^sub>\<circ> B) -\<^sub>\<circ> C = (A -\<^sub>\<circ> C) \<union>\<^sub>\<circ> (B -\<^sub>\<circ> C)" by auto


text\<open>Special properties.\<close>

lemma complement_vsubset: "I -\<^sub>\<circ> J \<subseteq>\<^sub>\<circ> I" by auto

lemma vintersection_complement: "(I -\<^sub>\<circ> J) \<inter>\<^sub>\<circ> J = 0" by auto

lemma vunion_complement: 
  assumes "J \<subseteq>\<^sub>\<circ> I"
  shows "I -\<^sub>\<circ> J \<union>\<^sub>\<circ> J = I"
  using assms by auto


subsection\<open>Augmenting a set with an element\<close>

lemma vinsert_compr: "vinsert y A = set {x. x = y \<or> x \<in>\<^sub>\<circ> A}"
  unfolding vunion_def vinsert_def by simp_all


text\<open>Rules.\<close>

lemma vinsert_iff[simp]: "x \<in>\<^sub>\<circ> vinsert y A \<longleftrightarrow> x = y \<or> x \<in>\<^sub>\<circ> A" by simp

lemma vinsertI1: "x \<in>\<^sub>\<circ> vinsert x A" by simp

lemma vinsertI2: 
  assumes "x \<in>\<^sub>\<circ> A"
  shows "x \<in>\<^sub>\<circ> vinsert y A" 
  using assms by simp

lemma vinsertE1[elim!]: 
  assumes "x \<in>\<^sub>\<circ> vinsert y A" and "x = y \<Longrightarrow> P" and "x \<in>\<^sub>\<circ> A \<Longrightarrow> P" 
  shows P
  using assms unfolding vinsert_def by auto

lemma vinsertCI[intro!]: 
  assumes "x \<notin>\<^sub>\<circ> A \<Longrightarrow> x = y"
  shows "x \<in>\<^sub>\<circ> vinsert y A" 
  using assms by clarsimp


text\<open>Elementary properties.\<close>

lemma vinsert_insert: "vinsert a A = set (insert a (elts A))" by auto

lemma vinsert_commutativity: "vinsert a (vinsert b C) = vinsert b (vinsert a C)" 
  by auto

lemma vinsert_ident:
  assumes "x \<notin>\<^sub>\<circ> A" and "x \<notin>\<^sub>\<circ> B" 
  shows "vinsert x A = vinsert x B \<longleftrightarrow> A = B"
  using assms by force

lemmas vinsert_identD[dest] = vinsert_ident[THEN iffD1, rotated 2]
  and vinsert_identI[intro] = vinsert_ident[THEN iffD2]


text\<open>Set operations.\<close>

lemma vinsert_vempty: "vinsert a 0 = set {a}" by auto

lemma vinsert_vsingleton: "vinsert a (set {b}) = set {a, b}" by auto

lemma vinsert_vdoubleton: "vinsert a (set {b, c}) = set {a, b, c}" by auto

lemma vinsert_vinsert: "vinsert a (vinsert b C) = set {a, b} \<union>\<^sub>\<circ> C" by auto

lemma vinsert_vunion_left: "vinsert a (A \<union>\<^sub>\<circ> B) = vinsert a A \<union>\<^sub>\<circ> B" by auto

lemma vinsert_vunion_right: "vinsert a (A \<union>\<^sub>\<circ> B) = A \<union>\<^sub>\<circ> vinsert a B" by auto

lemma vinsert_vintersection: "vinsert a (A \<inter>\<^sub>\<circ> B) = vinsert a A \<inter>\<^sub>\<circ> vinsert a B"
  by auto


text\<open>Special properties.\<close>

lemma vinsert_set_insert_empty_anyI:
  assumes "P (vinsert a 0)"
  shows "P (set (insert a {}))"  
  using assms by (simp add: vinsert_def)

lemma vinsert_set_insert_anyI:
  assumes "small B" and "P (vinsert a (set (insert b B)))"
  shows "P (set (insert a (insert b B)))"  
  using assms by (simp add: ZFC_in_HOL.vinsert_def)

lemma vinsert_set_insert_eq:
  assumes "small B" 
  shows "set (insert a (insert b B)) = vinsert a (set (insert b B))"
  using assms by (simp add: ZFC_in_HOL.vinsert_def)

lemma vsubset_vinsert: 
  "A \<subseteq>\<^sub>\<circ> vinsert x B \<longleftrightarrow> (if x \<in>\<^sub>\<circ> A then A -\<^sub>\<circ> set {x} \<subseteq>\<^sub>\<circ> B else A \<subseteq>\<^sub>\<circ> B)"
  by auto

lemma vinsert_obtain_ne:
  assumes "A \<noteq> 0" 
  obtains a A' where "A = vinsert a A'" and "a \<notin>\<^sub>\<circ> A'"
proof-
  from assms mem_not_refl obtain a where "a \<in>\<^sub>\<circ> A" 
    by (auto intro!: vsubset_antisym)
  with \<open>a \<in>\<^sub>\<circ> A\<close> have "A = vinsert a (A -\<^sub>\<circ> set {a})" by auto
  then show ?thesis using that by auto
qed



subsection\<open>Power set\<close>


text\<open>Rules.\<close>

lemma VPowI:
  assumes "A \<subseteq>\<^sub>\<circ> B"
  shows "A \<in>\<^sub>\<circ> VPow B" 
  using assms by simp

lemma VPowD: 
  assumes "A \<in>\<^sub>\<circ> VPow B"
  shows "A \<subseteq>\<^sub>\<circ> B" 
  using assms by (simp add: Pow_def)

lemma VPowE[elim]:
  assumes "A \<in>\<^sub>\<circ> VPow B" and "A \<subseteq>\<^sub>\<circ> B \<Longrightarrow> P"
  shows P
  using assms by auto


text\<open>Elementary properties.\<close>

lemma VPow_bottom: "0 \<in>\<^sub>\<circ> VPow B" by simp

lemma VPow_top: "A \<in>\<^sub>\<circ> VPow A" by simp


text\<open>Set operations.\<close>

lemma VPow_vempty[simp]: "VPow 0 = set {0}" by auto

lemma VPow_vsingleton[simp]: "VPow (set {a}) = set {0, set {a}}" 
  by (rule vsubset_antisym; rule vsubsetI) auto

lemma VPow_not_vempty: "VPow A \<noteq> 0" by auto

lemma VPow_mono: 
  assumes "A \<subseteq>\<^sub>\<circ> B"
  shows "VPow A \<subseteq>\<^sub>\<circ> VPow B"
  using assms by simp

lemma VPow_vunion_subset: "VPow A \<union>\<^sub>\<circ> VPow B \<subseteq>\<^sub>\<circ> VPow (A \<union>\<^sub>\<circ> B)" by simp



subsection\<open>Singletons, using insert\<close>


text\<open>Rules.\<close>

lemma vsingletonI[intro!]: "x \<in>\<^sub>\<circ> set {x}" by auto

lemma vsingletonD[dest!]: 
  assumes "y \<in>\<^sub>\<circ> set {x}"
  shows "y = x" 
  using assms by auto

lemma vsingleton_iff: "y \<in>\<^sub>\<circ> set {x} \<longleftrightarrow> y = x" by simp


text\<open>Previous set operations.\<close>

lemma VPow_vdoubleton[simp]:
  "VPow (set {a, b}) = set {0, set {a}, set {b}, set {a, b}}"   
  by (intro vsubset_antisym vsubsetI) 
    (auto intro!: vsubset_antisym simp: vinsert_set_insert_eq)

lemma vsubset_vinsertI: 
  assumes "A -\<^sub>\<circ> set {x} \<subseteq>\<^sub>\<circ> B"
  shows "A \<subseteq>\<^sub>\<circ> vinsert x B" 
  using assms by auto


text\<open>Special properties.\<close>

lemma vsingleton_inject:  
  assumes "set {x} = set {y}"
  shows "x = y" 
  using assms by simp

lemma vsingleton_insert_inj_eq[iff]:
  "set {y} = vinsert x A \<longleftrightarrow> x = y \<and> A \<subseteq>\<^sub>\<circ> set {y}"
  by auto

lemma vsingleton_insert_inj_eq'[iff]: 
  "vinsert x A = set {y} \<longleftrightarrow> x = y \<and> A \<subseteq>\<^sub>\<circ> set {y}"
  by auto

lemma vsubset_vsingletonD: 
  assumes "A \<subseteq>\<^sub>\<circ> set {x}"
  shows "A = 0 \<or> A = set {x}" 
  using assms by auto

lemma vsubset_vsingleton_iff: "a \<subseteq>\<^sub>\<circ> set {x} \<longleftrightarrow> a = 0 \<or> a = set {x}" by auto

lemma vsubset_vdiff_vinsert: "A \<subseteq>\<^sub>\<circ> B -\<^sub>\<circ> vinsert x C \<longleftrightarrow> A \<subseteq>\<^sub>\<circ> B -\<^sub>\<circ> C \<and> x \<notin>\<^sub>\<circ> A"
  by auto

lemma vunion_vsingleton_iff: 
  "A \<union>\<^sub>\<circ> B = set {x} \<longleftrightarrow> 
    A = 0 \<and> B = set {x} \<or> A = set {x} \<and> B = 0 \<or> A = set {x} \<and> B = set {x}"
  by 
    (
      metis 
        vsubset_vsingletonD inf_sup_ord(4) sup.idem sup_V_0_right sup_commute
    )

lemma vsingleton_Un_iff: 
  "set {x} = A \<union>\<^sub>\<circ> B \<longleftrightarrow> 
    A = 0 \<and> B = set {x} \<or> A = set {x} \<and> B = 0 \<or> A = set {x} \<and> B = set {x}"
  by (metis vunion_vsingleton_iff sup_V_0_left sup_V_0_right sup_idem)

lemma VPow_vsingleton_iff[simp]: "VPow X = set {Y} \<longleftrightarrow> X = 0 \<and> Y = 0" 
  by (auto intro!: vsubset_antisym)



subsection\<open>Intersection of elements\<close>

lemma small_VInter[simp]:
  assumes "A \<noteq> 0"
  shows "small {a. \<forall>x \<in>\<^sub>\<circ> A. a \<in>\<^sub>\<circ> x}"
  by (metis (no_types, lifting) assms down eq0_iff mem_Collect_eq subsetI)

lemma VInter_def: "\<Inter>\<^sub>\<circ> A = (if A = 0 then 0 else set {a. \<forall>x \<in>\<^sub>\<circ> A. a \<in>\<^sub>\<circ> x})"
proof(cases \<open>A = 0\<close>)
  case True show ?thesis unfolding True Inf_V_def by simp
next
  case False 
  from False have "(\<Inter> (elts ` elts A)) = {a. \<forall>x \<in>\<^sub>\<circ> A. a \<in>\<^sub>\<circ> x}" by auto
  with False show ?thesis unfolding Inf_V_def by auto
qed


text\<open>Rules.\<close>

lemma VInter_iff[simp]: 
  assumes [simp]: "A \<noteq> 0"
  shows "a \<in>\<^sub>\<circ> \<Inter>\<^sub>\<circ> A \<longleftrightarrow> (\<forall>x\<in>\<^sub>\<circ>A. a \<in>\<^sub>\<circ> x)"
  unfolding VInter_def by auto

lemma VInterI[intro]: 
  assumes "A \<noteq> 0" and "\<And>x. x \<in>\<^sub>\<circ> A \<Longrightarrow> a \<in>\<^sub>\<circ> x"
  shows "a \<in>\<^sub>\<circ> \<Inter>\<^sub>\<circ> A"
  using assms by auto

lemma VInter0I[intro]:
  assumes "A = 0"
  shows "\<Inter>\<^sub>\<circ> A = 0"
  using assms unfolding VInter_def by simp

lemma VInterD[dest]:
  assumes "a \<in>\<^sub>\<circ> \<Inter>\<^sub>\<circ> A" and "x \<in>\<^sub>\<circ> A"
  shows "a \<in>\<^sub>\<circ> x"
  using assms by (cases \<open>A = 0\<close>) auto

lemma VInterE1[elim]: 
  assumes "a \<in>\<^sub>\<circ> \<Inter>\<^sub>\<circ> A" and "x \<notin>\<^sub>\<circ> A \<Longrightarrow> R" and "a \<in>\<^sub>\<circ> x \<Longrightarrow> R" 
  shows R
  using assms elts_0 unfolding Inter_eq by blast

lemma VInterE2[elim]:
  assumes "a \<in>\<^sub>\<circ> \<Inter>\<^sub>\<circ> A" 
  obtains x where "a \<in>\<^sub>\<circ> x" and "x \<in>\<^sub>\<circ> A"
proof(cases \<open>A = 0\<close>)
  show "(\<And>x. a \<in>\<^sub>\<circ> x \<Longrightarrow> x \<in>\<^sub>\<circ> A \<Longrightarrow> thesis) \<Longrightarrow> A = 0 \<Longrightarrow> thesis"
    using assms unfolding Inf_V_def by auto
  show "(\<And>x. a \<in>\<^sub>\<circ> x \<Longrightarrow> x \<in>\<^sub>\<circ> A \<Longrightarrow> thesis) \<Longrightarrow> A \<noteq> 0 \<Longrightarrow> thesis"
    using assms by (meson assms VInterE1 that trad_foundation)
qed

lemma VInterE3: (*not elim*)
  assumes "a \<in>\<^sub>\<circ> \<Inter>\<^sub>\<circ> A" and "(\<And>y. y \<in>\<^sub>\<circ> A \<Longrightarrow> a \<in>\<^sub>\<circ> y) \<Longrightarrow> P"
  shows P
  using assms by auto


text\<open>Elementary properties.\<close>

lemma VInter_Inter: "\<Inter>\<^sub>\<circ> A = set (\<Inter> (elts ` (elts A)))"
  by (simp add: Inf_V_def ext)

lemma VInter_eq:
  assumes [simp]: "A \<noteq> 0"
  shows "\<Inter>\<^sub>\<circ> A = set {a. \<forall>x \<in>\<^sub>\<circ> A. a \<in>\<^sub>\<circ> x}"
  unfolding VInter_def by auto


text\<open>Set operations.\<close>

lemma VInter_vempty[simp]: "\<Inter>\<^sub>\<circ> 0 = 0" using VInter0I by auto

lemma VInf_vempty[simp]: "\<Sqinter>{} = (0::V)" by (simp add: Inf_V_def)

lemma VInter_vdoubleton: "\<Inter>\<^sub>\<circ> (set {a, b}) = a \<inter>\<^sub>\<circ> b"
proof(intro vsubset_antisym vsubsetI)
  show "x \<in>\<^sub>\<circ> \<Inter>\<^sub>\<circ> (set {a, b}) \<Longrightarrow> x \<in>\<^sub>\<circ> a \<inter>\<^sub>\<circ> b" for x by (elim VInterE3) auto
  show "x \<in>\<^sub>\<circ> a \<inter>\<^sub>\<circ> b \<Longrightarrow> x \<in>\<^sub>\<circ> \<Inter>\<^sub>\<circ> (set {a, b})" for x by (intro VInterI) force+
qed

lemma VInter_antimono: 
  assumes "B \<noteq> 0" and "B \<subseteq>\<^sub>\<circ> A"
  shows "\<Inter>\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> \<Inter>\<^sub>\<circ> B"
  using assms by blast

lemma VInter_vsubset: 
  assumes "\<And>x. x \<in>\<^sub>\<circ> A \<Longrightarrow> x \<subseteq>\<^sub>\<circ> B" and "A \<noteq> 0" 
  shows "\<Inter>\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> B"
  using assms by auto

lemma VInter_vinsert: 
  assumes "A \<noteq> 0"
  shows "\<Inter>\<^sub>\<circ> (vinsert a A) = a \<inter>\<^sub>\<circ> \<Inter>\<^sub>\<circ> A"
  using assms by (blast intro!: vsubset_antisym)

lemma VInter_vunion: 
  assumes "A \<noteq> 0" and "B \<noteq> 0"   
  shows "\<Inter>\<^sub>\<circ>(A \<union>\<^sub>\<circ> B) = \<Inter>\<^sub>\<circ>A \<inter>\<^sub>\<circ> \<Inter>\<^sub>\<circ>B"
  using assms by (blast intro!: vsubset_antisym)

lemma VInter_vintersection: 
  assumes "A \<inter>\<^sub>\<circ> B \<noteq> 0"
  shows "\<Inter>\<^sub>\<circ> A \<union>\<^sub>\<circ> \<Inter>\<^sub>\<circ> B \<subseteq>\<^sub>\<circ> \<Inter>\<^sub>\<circ> (A \<inter>\<^sub>\<circ> B)" 
  using assms by auto

lemma VInter_VPow: "\<Inter>\<^sub>\<circ> (VPow A) \<subseteq>\<^sub>\<circ> VPow (\<Inter>\<^sub>\<circ> A)" by auto


text\<open>Elementary properties.\<close>

lemma VInter_lower: 
  assumes "x \<in>\<^sub>\<circ> A"
  shows "\<Inter>\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> x"
  using assms by auto

lemma VInter_greatest: 
  assumes "A \<noteq> 0" and "\<And>x. x \<in>\<^sub>\<circ> A \<Longrightarrow> B \<subseteq>\<^sub>\<circ> x" 
  shows "B \<subseteq>\<^sub>\<circ> \<Inter>\<^sub>\<circ> A"
  using assms by auto



subsection\<open>Union of elements\<close>

lemma Union_eq_VUnion: "\<Union>(elts ` elts A) = {a. \<exists>x \<in>\<^sub>\<circ> A. a \<in>\<^sub>\<circ> x}" by auto

lemma small_VUnion[simp]: "small {a. \<exists>x \<in>\<^sub>\<circ> A. a \<in>\<^sub>\<circ> x}"
  by (fold Union_eq_VUnion) simp

lemma VUnion_def: "\<Union>\<^sub>\<circ>A = set {a. \<exists>x \<in>\<^sub>\<circ> A. a \<in>\<^sub>\<circ> x}"
  unfolding Sup_V_def by auto


text\<open>Rules.\<close>

lemma VUnion_iff[simp]: "A \<in>\<^sub>\<circ> \<Union>\<^sub>\<circ>C \<longleftrightarrow> (\<exists>x\<in>\<^sub>\<circ>C. A \<in>\<^sub>\<circ> x)" by auto

lemma VUnionI[intro]: 
  assumes "x \<in>\<^sub>\<circ> A" and "a \<in>\<^sub>\<circ> x"
  shows "a \<in>\<^sub>\<circ> \<Union>\<^sub>\<circ>A" 
  using assms by auto

lemma VUnionE[elim!]: 
  assumes "a \<in>\<^sub>\<circ> \<Union>\<^sub>\<circ>A" and "\<And>x. a \<in>\<^sub>\<circ> x \<Longrightarrow> x \<in>\<^sub>\<circ> A \<Longrightarrow> R" 
  shows R
  using assms by clarsimp


text\<open>Elementary properties.\<close>

lemma VUnion_Union: "\<Union>\<^sub>\<circ>A = set (\<Union> (elts ` (elts A)))"
  by (simp add: Inf_V_def ext)


text\<open>Set operations.\<close>

lemma VUnion_vempty[simp]: "\<Union>\<^sub>\<circ>0 = 0" by simp

lemma VUnion_vsingleton[simp]: "\<Union>\<^sub>\<circ>(set {a}) = a" by simp

lemma VUnion_vdoubleton[simp]: "\<Union>\<^sub>\<circ>(set {a, b}) = a \<union>\<^sub>\<circ> b" by auto

lemma VUnion_mono: 
  assumes "A \<subseteq>\<^sub>\<circ> B"
  shows "\<Union>\<^sub>\<circ>A \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>B" 
  using assms by auto

lemma VUnion_vinsert: "\<Union>\<^sub>\<circ>(vinsert x A) = x \<union>\<^sub>\<circ> \<Union>\<^sub>\<circ>A" by auto

lemma VUnion_vintersection: "\<Union>\<^sub>\<circ>(A \<inter>\<^sub>\<circ> B) \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>A \<inter>\<^sub>\<circ> \<Union>\<^sub>\<circ>B" by auto

lemma VUnion_vunion[simp]: "\<Union>\<^sub>\<circ>(A \<union>\<^sub>\<circ> B) = \<Union>\<^sub>\<circ>A \<union>\<^sub>\<circ> \<Union>\<^sub>\<circ>B" by auto

lemma VUnion_VPow[simp]: "\<Union>\<^sub>\<circ>(VPow A) = A" by auto


text\<open>Special properties.\<close>

lemma VUnion_vempty_conv_left: "0 = \<Union>\<^sub>\<circ>A \<longleftrightarrow> (\<forall>x\<in>\<^sub>\<circ>A. x = 0)" by auto

lemma VUnion_vempty_conv_right: "\<Union>\<^sub>\<circ>A = 0 \<longleftrightarrow> (\<forall>x\<in>\<^sub>\<circ>A. x = 0)" by auto

lemma vsubset_VPow_VUnion: "A \<subseteq>\<^sub>\<circ> VPow (\<Union>\<^sub>\<circ>A)" by auto

lemma VUnion_vsubsetI: 
  assumes "\<And>x. x \<in>\<^sub>\<circ> A \<Longrightarrow> \<exists>y. y \<in>\<^sub>\<circ> B \<and> x \<subseteq>\<^sub>\<circ> y"
  shows "\<Union>\<^sub>\<circ>A \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>B"
  using assms by auto

lemma VUnion_upper: 
  assumes "x \<in>\<^sub>\<circ> A"
  shows "x \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>A" 
  using assms by auto

lemma VUnion_least: 
  assumes "\<And>x. x \<in>\<^sub>\<circ> A \<Longrightarrow> x \<subseteq>\<^sub>\<circ> B" 
  shows "\<Union>\<^sub>\<circ>A \<subseteq>\<^sub>\<circ> B" 
  using assms by (fact Sup_least)



subsection\<open>Pairs\<close>


subsubsection\<open>Further results\<close>

lemma small_elts_of_set[simp, intro]:
  assumes "small x"
  shows "elts (set x) = x"
  by (simp add: assms)

lemma small_vpair[intro, simp]:
  assumes "small {a. P a}"
  shows "small {\<langle>a, b\<rangle> | a. P a}"
  by (subgoal_tac \<open>{\<langle>a, b\<rangle> | a. P a} = (\<lambda>a. \<langle>a, b\<rangle>) ` {a. P a}\<close>)
    (auto simp: assms)


subsubsection\<open>\<open>vpairs\<close>\<close>

definition vpairs :: "V \<Rightarrow> V" where
  "vpairs r = set {x. x \<in>\<^sub>\<circ> r \<and> (\<exists>a b. x = \<langle>a, b\<rangle>)}"

lemma small_vpairs[simp]: "small {\<langle>a, b\<rangle> | a b. \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r}"
  by (rule down[of _ r]) clarsimp


text\<open>Rules.\<close>

lemma vpairsI[intro]: 
  assumes "x \<in>\<^sub>\<circ> r" and "x = \<langle>a, b\<rangle>" 
  shows "x \<in>\<^sub>\<circ> vpairs r"
  using assms unfolding vpairs_def by auto

lemma vpairsD[dest]:
  assumes "x \<in>\<^sub>\<circ> vpairs r" 
  shows "x \<in>\<^sub>\<circ> r" and "\<exists>a b. x = \<langle>a, b\<rangle>" 
  using assms unfolding vpairs_def by auto

lemma vpairsE[elim]:
  assumes "x \<in>\<^sub>\<circ> vpairs r"
  obtains a b where "x = \<langle>a, b\<rangle>" and "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r"
  using assms unfolding vpairs_def by auto

lemma vpairs_iff: "x \<in>\<^sub>\<circ> vpairs r \<longleftrightarrow> x \<in>\<^sub>\<circ> r \<and> (\<exists>a b. x = \<langle>a, b\<rangle>)" by auto


text\<open>Elementary properties.\<close>

lemma vpairs_iff_elts: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> vpairs r \<longleftrightarrow> \<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" by auto

lemma vpairs_iff_pairs: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> vpairs r \<longleftrightarrow> (a, b) \<in> pairs r"
  by (simp add: vpairs_iff_elts pairs_iff_elts)


text\<open>Set operations.\<close>

lemma vpairs_vempty[simp]: "vpairs 0 = 0" by auto

lemma vpairs_vsingleton[simp]: "vpairs (set {\<langle>a, b\<rangle>}) = set {\<langle>a, b\<rangle>}" by auto

lemma vpairs_vinsert: "vpairs (vinsert \<langle>a, b\<rangle> A) = set {\<langle>a, b\<rangle>} \<union>\<^sub>\<circ> vpairs A" 
  by auto

lemma vpairs_mono:
  assumes "r \<subseteq>\<^sub>\<circ> s"
  shows "vpairs r \<subseteq>\<^sub>\<circ> vpairs s"
  using assms by blast

lemma vpairs_vunion: "vpairs (A \<union>\<^sub>\<circ> B) = vpairs A \<union>\<^sub>\<circ> vpairs B" by auto

lemma vpairs_vintersection: "vpairs (A \<inter>\<^sub>\<circ> B) = vpairs A \<inter>\<^sub>\<circ> vpairs B" by auto

lemma vpairs_vdiff: "vpairs (A -\<^sub>\<circ> B) = vpairs A -\<^sub>\<circ> vpairs B" by auto


text\<open>Special properties.\<close>

lemma vpairs_ex_vfst:
  assumes "x \<in>\<^sub>\<circ> vpairs r"
  shows "\<exists>b. \<langle>vfst x, b\<rangle> \<in>\<^sub>\<circ> r"
  using assms by force

lemma vpairs_ex_vsnd:
  assumes "y \<in>\<^sub>\<circ> vpairs r"
  shows "\<exists>a. \<langle>a, vsnd y\<rangle> \<in>\<^sub>\<circ> r"
  using assms by force



subsection\<open>Cartesian products\<close>

text\<open>
The following lemma is based on Theorem 6.2 from 
\cite{takeuti_introduction_1971}.
\<close>

lemma vtimes_vsubset_VPowVPow: "A \<times>\<^sub>\<circ> B \<subseteq>\<^sub>\<circ> VPow (VPow (A \<union>\<^sub>\<circ> B))"
proof(intro vsubsetI)
  fix x assume "x \<in>\<^sub>\<circ> A \<times>\<^sub>\<circ> B" 
  then obtain a b where x_def: "x = \<langle>a, b\<rangle>" and "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> B" by clarsimp
  then show "x \<in>\<^sub>\<circ> VPow (VPow (A \<union>\<^sub>\<circ> B))"
    unfolding x_def vpair_def by auto
qed



subsection\<open>Pairwise\<close>

definition vpairwise :: "(V \<Rightarrow> V \<Rightarrow> bool) \<Rightarrow> V \<Rightarrow> bool"
  where "vpairwise R S \<longleftrightarrow> (\<forall>x\<in>\<^sub>\<circ>S. \<forall>y\<in>\<^sub>\<circ>S. x \<noteq> y \<longrightarrow> R x y)"


text\<open>Rules.\<close>

lemma vpairwiseI[intro?]:
  assumes "\<And>x y. x \<in>\<^sub>\<circ> S \<Longrightarrow> y \<in>\<^sub>\<circ> S \<Longrightarrow> x \<noteq> y \<Longrightarrow> R x y"
  shows "vpairwise R S" 
  using assms by (simp add: vpairwise_def)

lemma vpairwiseD[dest]: 
  assumes "vpairwise R S" and "x \<in>\<^sub>\<circ> S" and "y \<in>\<^sub>\<circ> S" and "x \<noteq> y"
  shows "R x y" and "R y x"
  using assms unfolding vpairwise_def by auto


text\<open>Elementary properties.\<close>

lemma vpairwise_trivial[simp]: "vpairwise (\<lambda>i j. j \<noteq> i) I"
  by (auto simp: vpairwise_def)


text\<open>Set operations.\<close>

lemma vpairwise_vempty[simp]: "vpairwise P 0" by (force intro: vpairwiseI)

lemma vpairwise_vsingleton[simp]: "vpairwise P (set {A})"
  by (simp add: vpairwise_def)

lemma vpairwise_vinsert:
  "vpairwise r (vinsert x s) \<longleftrightarrow> 
    (\<forall>y. y \<in>\<^sub>\<circ> s \<and> y \<noteq> x \<longrightarrow> r x y \<and> r y x) \<and> vpairwise r s"
  by (intro iffI conjI allI impI; (elim conjE | tactic\<open>all_tac\<close>))
    (auto simp: vpairwise_def)

lemma vpairwise_vsubset: 
  assumes "vpairwise P S" and "T \<subseteq>\<^sub>\<circ> S" 
  shows "vpairwise P T"
  using assms by (metis less_eq_V_def subset_eq vpairwiseD(2) vpairwiseI)

lemma vpairwise_mono: 
  assumes "vpairwise P A" and "\<And>x y. P x y \<Longrightarrow> Q x y" and "B \<subseteq>\<^sub>\<circ> A" 
  shows "vpairwise Q B"
  using assms by (simp add: less_eq_V_def subset_eq vpairwiseD(2) vpairwiseI)



subsection\<open>Disjoint sets\<close>

abbreviation vdisjnt :: "V \<Rightarrow> V \<Rightarrow> bool"
  where "vdisjnt A B \<equiv> A \<inter>\<^sub>\<circ> B = 0"


text\<open>Elementary properties.\<close>

lemma vdisjnt_sym: 
  assumes "vdisjnt A B"
  shows "vdisjnt B A"
  using assms by blast

lemma vdisjnt_iff: "vdisjnt A B \<longleftrightarrow> (\<forall>x. ~ (x \<in>\<^sub>\<circ> A \<and> x \<in>\<^sub>\<circ> B))" by auto


text\<open>Set operations.\<close>

lemma vdisjnt_vempty1[simp]: "vdisjnt 0 A"
  and vdisjnt_vempty2[simp]: "vdisjnt A 0"
  by auto

lemma vdisjnt_singleton0[simp]: "vdisjnt (set {a}) (set {b}) \<longleftrightarrow> a \<noteq> b"
  and vdisjnt_singleton1[simp]: "vdisjnt (set {a}) A \<longleftrightarrow> a \<notin>\<^sub>\<circ> A"
  and vdisjnt_singleton2[simp]: "vdisjnt A (set {a}) \<longleftrightarrow> a \<notin>\<^sub>\<circ> A"
  by force+

lemma vdisjnt_vinsert_left: "vdisjnt (vinsert a X) Y \<longleftrightarrow> a \<notin>\<^sub>\<circ> Y \<and> vdisjnt X Y"
  by (metis vdisjnt_iff vdisjnt_sym vinsertE1 vinsertI2 vinsert_iff)

lemma vdisjnt_vinsert_right: "vdisjnt Y (vinsert a X) \<longleftrightarrow> a \<notin>\<^sub>\<circ> Y \<and> vdisjnt Y X"
  using vdisjnt_sym vdisjnt_vinsert_left by meson

lemma vdisjnt_vsubset_left: 
  assumes "vdisjnt X Y" and "Z \<subseteq>\<^sub>\<circ> X" 
  shows "vdisjnt Z Y"
  using assms by (auto intro!: vsubset_antisym)

lemma vdisjnt_vsubset_right: 
  assumes "vdisjnt X Y" and "Z \<subseteq>\<^sub>\<circ> Y"
  shows "vdisjnt X Z"
  using assms by (auto intro!: vsubset_antisym)

lemma vdisjnt_vunion_left: "vdisjnt (A \<union>\<^sub>\<circ> B) C \<longleftrightarrow> vdisjnt A C \<and> vdisjnt B C"
  by auto

lemma vdisjnt_vunion_right: "vdisjnt C (A \<union>\<^sub>\<circ> B) \<longleftrightarrow> vdisjnt C A \<and> vdisjnt C B"
  by auto


text\<open>Special properties.\<close>

lemma vdisjnt_vemptyI[intro]:
  assumes "\<And>x. x \<in>\<^sub>\<circ> A \<Longrightarrow> x \<in>\<^sub>\<circ> B \<Longrightarrow> False"
  shows "vdisjnt A B" 
  using assms by (auto intro!: vsubset_antisym)

lemma vdisjnt_self_iff_vempty[simp]: "vdisjnt S S \<longleftrightarrow> S = 0" by auto

lemma vdisjntI:
  assumes "\<And>x y. x \<in>\<^sub>\<circ> A \<Longrightarrow> y \<in>\<^sub>\<circ> B \<Longrightarrow> x \<noteq> y"
  shows "vdisjnt A B"
  using assms by auto

lemma vdisjnt_nin_right:
  assumes "vdisjnt A B" and "a \<in>\<^sub>\<circ> A"
  shows "a \<notin>\<^sub>\<circ> B"
  using assms by auto

lemma vdisjnt_nin_left:
  assumes "vdisjnt B A" and "a \<in>\<^sub>\<circ> A"
  shows "a \<notin>\<^sub>\<circ> B"
  using assms by auto

text\<open>\newpage\<close>

end