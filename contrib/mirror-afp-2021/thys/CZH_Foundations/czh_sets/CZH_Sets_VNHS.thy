(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Further results related to the von Neumann hierarchy of sets\<close>
theory CZH_Sets_VNHS
  imports 
    CZH_Sets_FBRelations
    CZH_Sets_Ordinals
begin



subsection\<open>Background\<close>


text\<open>
The subsection presents several further auxiliary results about the 
von Neumann hierarchy of sets. The primary general reference for this section
is \cite{takeuti_introduction_1971}.
\<close>



subsection\<open>Further elementary properties of \<open>Vfrom\<close>\<close>


text\<open>Reusable patterns.\<close>

lemma Vfrom_Ord_bundle:
  assumes "A = A" and "i = i"
  shows "Vfrom A i = Vfrom A (rank i)" and "Ord (rank i)"
  by (simp_all add: Vfrom_rank_eq )

lemma Vfrom_in_bundle:
  assumes "i \<in>\<^sub>\<circ> j" and "A = A" and "B = B"
  shows "Vfrom A i = Vfrom A (rank i)"
    and "Ord (rank i)"
    and "Vfrom B j = Vfrom B (rank j)"
    and "Ord (rank j)"
    and "rank i \<in>\<^sub>\<circ> rank j"
  by (simp_all add: assms(1) Vfrom_rank_eq Ord_mem_iff_lt rank_lt)


text\<open>Elementary corollaries.\<close>

lemma Ord_Vset_in_Vset_succI[intro]:
  assumes "Ord \<alpha>" 
  shows "Vset \<alpha> \<in>\<^sub>\<circ> Vset (succ \<alpha>)"
  by (simp add: Vset_succ assms)

lemma Ord_in_in_VsetI[intro]:
  assumes "Ord \<alpha>" and "a \<in>\<^sub>\<circ> \<alpha>"
  shows "a \<in>\<^sub>\<circ> Vset \<alpha>"
  by (metis assms Ord_VsetI Ord_iff_rank rank_lt)


text\<open>Transitivity of the constant \<^const>\<open>Vfrom\<close>.\<close>

lemma Vfrom_trans[intro]:
  assumes "Transset A" and "x \<in>\<^sub>\<circ> X" and "X \<in>\<^sub>\<circ> Vfrom A i" 
  shows "x \<in>\<^sub>\<circ> Vfrom A i"
  using Transset_def by (blast intro: assms Transset_Vfrom)

lemma Vset_trans[intro]:
  assumes "x \<in>\<^sub>\<circ> X" and "X \<in>\<^sub>\<circ> Vset i" 
  shows "x \<in>\<^sub>\<circ> Vset i"
  by (auto intro: assms)


text\<open>Monotonicity of the constant \<^const>\<open>Vfrom\<close>.\<close>

lemma Vfrom_in_mono:
  assumes "A \<subseteq>\<^sub>\<circ> B" and "i \<in>\<^sub>\<circ> j"
  shows "Vfrom A i \<in>\<^sub>\<circ> Vfrom B j"
proof-
  define i' where "i' = rank i"
  define j' where "j' = rank j"
  note rank_conv = 
    Vfrom_in_bundle[
      OF assms(2) HOL.refl[of A] HOL.refl[of B], folded i'_def j'_def
      ]
  show ?thesis
    unfolding rank_conv using rank_conv(4,5)
  proof induction
    case (succ j')
    from succ have "Ord (succ j')" by auto
    from succ(3) succ.hyps have "i' \<subseteq>\<^sub>\<circ> j'" by (auto simp: Ord_def Transset_def)
    from Vfrom_mono[OF \<open>Ord i'\<close> assms(1) this] show ?case 
      unfolding Vfrom_succ_Ord[OF \<open>Ord j'\<close>, of B] by simp
  next
    case (Limit j')
    from Limit(3) obtain \<xi> where "i' \<in>\<^sub>\<circ> \<xi>" and "\<xi> \<in>\<^sub>\<circ> j'" by auto
    with vifunionI have "Vfrom A i' \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>\<xi>\<in>\<^sub>\<circ>j'. Vfrom B \<xi>)" 
      by (auto simp: Limit.IH)
    then show "Vfrom A i' \<in>\<^sub>\<circ> Vfrom B (\<Union>\<^sub>\<circ>\<xi>\<in>\<^sub>\<circ>j'. \<xi>)"
      unfolding Limit_Vfrom_eq[symmetric, OF Limit(1)] 
      by (simp add: SUP_vifunion[symmetric] Limit.hyps)
  qed auto
qed

lemmas Vset_in_mono = Vfrom_in_mono[OF order_refl, of _ _ 0]

lemma Vfrom_vsubset_mono:
  assumes "A \<subseteq>\<^sub>\<circ> B" and "i \<subseteq>\<^sub>\<circ> j"
  shows "Vfrom A i \<subseteq>\<^sub>\<circ> Vfrom B j"
  by (metis assms Vfrom_Ord_bundle(1,2) Vfrom_mono rank_mono)

lemmas Vset_vsubset_mono = Vfrom_vsubset_mono[OF order_refl, of _ _ 0]

lemma arg1_vsubset_Vfrom: "a \<subseteq>\<^sub>\<circ> Vfrom a i" using Vfrom by blast
                                                     
lemma VPow_vsubset_Vset:
  \<comment>\<open>Based on Theorem 9.10 from \cite{takeuti_introduction_1971}\<close>
  assumes "X \<in>\<^sub>\<circ> Vset i" 
  shows "VPow X \<subseteq>\<^sub>\<circ> Vset i"
proof-
  define i' where "i' = rank i"
  note rank_conv = Vfrom_Ord_bundle[OF refl[of 0] refl[of i], folded i'_def]
  show ?thesis 
    using rank_conv(2) assms unfolding rank_conv
  proof induction
    case (Limit \<alpha>)
    from Limit have "X \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>\<alpha>. Vset i)"
      by (simp add: SUP_vifunion[symmetric] Limit_Vfrom_eq)
    then have "VPow X \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>\<alpha>. Vset i)"
      by (intro vsubsetI) (metis Limit.IH vifunionE vifunionI vsubsetE)
    then show ?case 
      by (simp add: SUP_vifunion[symmetric] Limit.hyps Limit_Vfrom_eq)
  qed (simp_all add: Vset_succ)
qed

lemma Vfrom_vsubset_VPow_Vfrom:
  assumes "Transset A"
  shows "Vfrom A i \<subseteq>\<^sub>\<circ> VPow (Vfrom A i)"
  using assms Transset_VPow Transset_Vfrom by (auto simp: Transset_def)

lemma arg1_vsubset_VPow_Vfrom:
  assumes "Transset A"
  shows "A \<subseteq>\<^sub>\<circ> VPow (Vfrom A i)"
  by (meson assms Vfrom_vsubset_VPow_Vfrom arg1_vsubset_Vfrom dual_order.trans)



subsection\<open>Operations closed with respect to \<^const>\<open>Vset\<close>\<close>


text\<open>Empty set.\<close>

lemma Limit_vempty_in_VsetI:
  assumes "Limit \<alpha>"
  shows "0 \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms by (auto simp: Limit_def)


text\<open>Subset.\<close>

lemma vsubset_in_VsetI[intro]:
  assumes "a \<subseteq>\<^sub>\<circ> A" and "A \<in>\<^sub>\<circ> Vset i" 
  shows "a \<in>\<^sub>\<circ> Vset i"
  using assms by (auto dest: VPow_vsubset_Vset)

lemma Ord_vsubset_in_Vset_succI:
  assumes "Ord \<alpha>" and "A \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  shows "A \<in>\<^sub>\<circ> Vset (succ \<alpha>)"
  using assms Ord_Vset_in_Vset_succI by auto


text\<open>Power set.\<close>

lemma Limit_VPow_in_VsetI[intro]:
  assumes "Limit \<alpha>" and "A \<in>\<^sub>\<circ> Vset \<alpha>" 
  shows "VPow A \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  from assms(1) have "Ord \<alpha>" by auto
  with assms obtain i where "A \<in>\<^sub>\<circ> Vset i" and "i \<in>\<^sub>\<circ> \<alpha>" and "Ord i"
    by (fastforce simp: Ord_in_Ord Limit_Vfrom_eq)
  have "Vset i \<in>\<^sub>\<circ> Vset \<alpha>" by (rule Vset_in_mono) (auto intro: \<open>i \<in>\<^sub>\<circ> \<alpha>\<close>)
  from VPow_vsubset_Vset[OF \<open>A \<in>\<^sub>\<circ> Vset i\<close>] this show ?thesis
    by (rule vsubset_in_VsetI)
qed

lemma VPow_in_Vset_revD:
  assumes "VPow A \<in>\<^sub>\<circ> Vset i"
  shows "A \<in>\<^sub>\<circ> Vset i"
  using assms Vset_trans by blast

lemma Ord_VPow_in_Vset_succI:
  assumes "Ord \<alpha>" and "a \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "VPow a \<in>\<^sub>\<circ> Vset (succ \<alpha>)"
  using VPow_vsubset_Vset[OF assms(2)] 
  by (auto intro: Ord_Vset_in_Vset_succI[OF assms(1)])

lemma Ord_VPow_in_Vset_succD:
  assumes "Ord \<alpha>" and "VPow a \<in>\<^sub>\<circ> Vset (succ \<alpha>)"
  shows "a \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms by (fastforce dest: Vset_succ)


text\<open>Union of elements.\<close>

lemma VUnion_in_VsetI[intro]:
  assumes "A \<in>\<^sub>\<circ> Vset i"
  shows "\<Union>\<^sub>\<circ>A \<in>\<^sub>\<circ> Vset i"
proof-
  define i' where "i' = rank i"
  note rank_conv = Vfrom_Ord_bundle[OF refl[of 0] refl[of i], folded i'_def]
  from rank_conv(2) assms show ?thesis 
    unfolding rank_conv
  proof induction
    case (succ \<alpha>)
    show "\<Union>\<^sub>\<circ>A \<in>\<^sub>\<circ> Vset (succ \<alpha>)"
      by (metis succ(1,3) VPow_iff VUnion_least Vset_trans Vset_succ)
  qed (auto simp: vrange_VLambda vimage_VLambda_vrange_rep Limit_Vfrom_eq)
qed

lemma Limit_VUnion_in_VsetD:
  assumes "Limit \<alpha>" and "\<Union>\<^sub>\<circ>A \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "A \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  have "A \<subseteq>\<^sub>\<circ> VPow (\<Union>\<^sub>\<circ>A)" by auto
  moreover from assms have "VPow (\<Union>\<^sub>\<circ>A) \<in>\<^sub>\<circ> Vset \<alpha>" by (rule Limit_VPow_in_VsetI)
  ultimately show ?thesis using assms(1) by auto
qed


text\<open>Intersection of elements.\<close>

lemma VInter_in_VsetI[intro]:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "\<Inter>\<^sub>\<circ>A \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  have subset: "\<Inter>\<^sub>\<circ>A \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>A" by auto
  moreover from assms have "\<Union>\<^sub>\<circ>A \<in>\<^sub>\<circ> Vset \<alpha>" by (rule VUnion_in_VsetI)
  ultimately show ?thesis by (rule vsubset_in_VsetI)
qed


text\<open>Singleton.\<close>

lemma Limit_vsingleton_in_VsetI[intro]:
  assumes "Limit \<alpha>" and "a \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "set {a} \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  have aa: "set {a} \<subseteq>\<^sub>\<circ> VPow a" by auto
  from assms(1) have "Ord \<alpha>" by auto
  from vsubset_in_VsetI[OF aa Limit_VPow_in_VsetI[OF assms(1)]] show ?thesis
    by (simp add: Limit_is_Ord assms(2))
qed

lemma Limit_vsingleton_in_VsetD:
  assumes "set {a} \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "a \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms by auto

lemma Ord_vsingleton_in_Vset_succI:
  assumes "Ord \<alpha>" and "a \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "set {a} \<in>\<^sub>\<circ> Vset (succ \<alpha>)"
  using assms by (simp add: Vset_succ vsubset_vsingleton_leftI)


text\<open>Doubleton.\<close>

lemma Limit_vdoubleton_in_VsetI[intro]:
  assumes "Limit \<alpha>" and "a \<in>\<^sub>\<circ> Vset \<alpha>" and "b \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "set {a, b} \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  from assms(1) have "Ord \<alpha>" by auto
  from assms have "a \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>\<xi>\<in>\<^sub>\<circ>\<alpha>. Vset \<xi>)" and "b \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>\<xi>\<in>\<^sub>\<circ>\<alpha>. Vset \<xi>)" 
    by (simp_all add: SUP_vifunion[symmetric] Limit_Vfrom_eq)
  then obtain A B 
    where a: "a \<in>\<^sub>\<circ> Vset A" and "A \<in>\<^sub>\<circ> \<alpha>" and b: "b \<in>\<^sub>\<circ> Vset B" and "B \<in>\<^sub>\<circ> \<alpha>"
    by blast
  moreover with assms have "Ord A" and "Ord B" by auto
  ultimately have "A \<union>\<^sub>\<circ> B \<in>\<^sub>\<circ> \<alpha>" 
    by (metis Ord_linear_le le_iff_sup sup.order_iff)
  then have "Vset (A \<union>\<^sub>\<circ> B) \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (simp add: assms Limit_is_Ord Vset_in_mono)
  moreover from a b have "set {a, b} \<subseteq>\<^sub>\<circ> Vset (A \<union>\<^sub>\<circ> B)" 
    by (simp add: Vfrom_sup vsubset_vdoubleton_leftI)
  ultimately show "set {a, b} \<in>\<^sub>\<circ> Vset \<alpha>" by (rule vsubset_in_VsetI[rotated 1])
qed

lemma vdoubleton_in_VsetD:
  assumes "set {a, b} \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "a \<in>\<^sub>\<circ> Vset \<alpha>" and "b \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms by (auto intro!: Vset_trans[of _ \<open>set {a, b}\<close>])

lemma Ord_vdoubleton_in_Vset_succI:
  assumes "Ord \<alpha>" and "a \<in>\<^sub>\<circ> Vset \<alpha>" and "b \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "set {a, b} \<in>\<^sub>\<circ> Vset (succ \<alpha>)"
  by 
    (
      meson 
        assms Ord_Vset_in_Vset_succI vsubset_in_VsetI vsubset_vdoubleton_leftI
    )


text\<open>Pairwise union.\<close>

lemma vunion_in_VsetI[intro]:
  assumes "a \<in>\<^sub>\<circ> Vset i" and "b \<in>\<^sub>\<circ> Vset i"
  shows "a \<union>\<^sub>\<circ> b \<in>\<^sub>\<circ> Vset i"
proof-
  define i' where "i' = rank i"
  note rank_conv = Vfrom_Ord_bundle[OF refl[of 0] refl[of i], folded i'_def]
  show ?thesis 
    using rank_conv(2) assms unfolding rank_conv
  proof induction
    case (Limit \<alpha>)
    from Limit have "set {a, b} \<in>\<^sub>\<circ> Vset \<alpha>"  
      by (intro Limit_vdoubleton_in_VsetI; unfold SUP_vifunion[symmetric]) 
        simp_all
    then have "\<Union>\<^sub>\<circ>(set {a, b}) \<in>\<^sub>\<circ> Vset \<alpha>" by (blast intro: Limit.hyps)
    with Limit.hyps VUnion_vdoubleton have "a \<union>\<^sub>\<circ> b \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>\<xi>\<in>\<^sub>\<circ>\<alpha>. Vset \<xi>)"
      by (auto simp: Limit_Vfrom_eq)
    then show "a \<union>\<^sub>\<circ> b \<in>\<^sub>\<circ> Vset (\<Union>\<^sub>\<circ>\<xi>\<in>\<^sub>\<circ>\<alpha>. \<xi>)" 
      by (simp add: \<open>Limit \<alpha>\<close> Limit_Vfrom_eq)
  qed (auto simp add: Vset_succ)
qed

lemma vunion_in_VsetD:
  assumes "a \<union>\<^sub>\<circ> b \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "a \<in>\<^sub>\<circ> Vset \<alpha>" and "b \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms by (meson vsubset_in_VsetI inf_sup_ord(3,4))+


text\<open>Pairwise intersection.\<close>

lemma vintersection_in_VsetI[intro]:
  assumes "a \<in>\<^sub>\<circ> Vset \<alpha>" and "b \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "a \<inter>\<^sub>\<circ> b \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms by (meson vsubset_in_VsetI inf_sup_ord(2))


text\<open>Set difference.\<close>

lemma vdiff_in_VsetI[intro]:
  assumes "a \<in>\<^sub>\<circ> Vset \<alpha>" and "b \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "a -\<^sub>\<circ> b \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms by auto


text\<open>\<^const>\<open>vinsert\<close>.\<close>

lemma vinsert_in_VsetI[intro]:
  assumes "Limit \<alpha>" and "a \<in>\<^sub>\<circ> Vset \<alpha>" and "b \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "vinsert a b \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  have ab: "vinsert a b = set {a} \<union>\<^sub>\<circ> b" by simp
  from assms(2) have "set {a} \<in>\<^sub>\<circ> Vset \<alpha>"
    by (simp add: Limit_vsingleton_in_VsetI assms(1))
  from this assms(1,3) show "vinsert a b \<in>\<^sub>\<circ> Vset \<alpha>"
    unfolding ab by blast
qed

lemma vinsert_in_Vset_succI[intro]:
  assumes "Ord \<alpha>" and "a \<in>\<^sub>\<circ> Vset \<alpha>" and "b \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "vinsert a b \<in>\<^sub>\<circ> Vset (succ \<alpha>)"
  using assms by blast

lemma vinsert_in_Vset_succI'[intro]:
  assumes "Ord \<alpha>" and "a \<in>\<^sub>\<circ> Vset \<alpha>" and "b \<in>\<^sub>\<circ> Vset (succ \<alpha>)"
  shows "vinsert a b \<in>\<^sub>\<circ> Vset (succ \<alpha>)"
proof-
  have ab: "vinsert a b = set {a} \<union>\<^sub>\<circ> b" by simp
  show ?thesis
    unfolding ab by (intro vunion_in_VsetI Ord_vsingleton_in_Vset_succI assms)
qed

lemma vinsert_in_VsetD:
  assumes "vinsert a b \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "a \<in>\<^sub>\<circ> Vset \<alpha>" and "b \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms Vset_trans by blast+

lemma Limit_insert_in_VsetI:
  assumes [intro]: "Limit \<alpha>" 
    and [simp]: "small x" 
    and "set x \<in>\<^sub>\<circ> Vset \<alpha>"
    and [intro]: "a \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "set (insert a x) \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  have ax: "set (insert a x) = vinsert a (set x)" by auto
  from assms show ?thesis unfolding ax by auto
qed


text\<open>Pair.\<close>

lemma Limit_vpair_in_VsetI[intro]:
  assumes "Limit \<alpha>" and "a \<in>\<^sub>\<circ> Vset \<alpha>" and "b \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms Limit_vdoubleton_in_VsetI Limit_vsingleton_in_VsetI 
  unfolding vpair_def
  by simp

lemma vpair_in_VsetD[intro]:
  assumes "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "a \<in>\<^sub>\<circ> Vset \<alpha>" and "b \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms unfolding vpair_def by (meson vdoubleton_in_VsetD)+


text\<open>Cartesian product.\<close>

lemma Limit_vtimes_in_VsetI[intro]:  
  assumes "Limit \<alpha>" and "A \<in>\<^sub>\<circ> Vset \<alpha>" and "B \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "A \<times>\<^sub>\<circ> B \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  from assms(1) have "Ord \<alpha>" by auto
  have "VPow (VPow (A \<union>\<^sub>\<circ> B)) \<in>\<^sub>\<circ> Vset \<alpha>"
    by (simp add: assms Limit_VPow_in_VsetI Limit_is_Ord vunion_in_VsetI)
  from assms(1) vsubset_in_VsetI[OF vtimes_vsubset_VPowVPow this] show ?thesis 
    by auto
qed


text\<open>Binary relations.\<close>

lemma (in vbrelation) vbrelation_Limit_in_VsetI[intro]: 
  assumes "Limit \<alpha>" and "\<D>\<^sub>\<circ> r \<in>\<^sub>\<circ> Vset \<alpha>" and "\<R>\<^sub>\<circ> r \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "r \<in>\<^sub>\<circ> Vset \<alpha>"  
  using assms vdomain_vrange_vtimes by auto

lemma 
  assumes "r \<in>\<^sub>\<circ> Vset \<alpha>"
  shows vdomain_in_VsetI: "\<D>\<^sub>\<circ> r \<in>\<^sub>\<circ> Vset \<alpha>" 
    and vrange_in_VsetI: "\<R>\<^sub>\<circ> r \<in>\<^sub>\<circ> Vset \<alpha>" 
    and vfield_in_VsetI: "\<F>\<^sub>\<circ> r \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  from assms have "\<Union>\<^sub>\<circ>r \<in>\<^sub>\<circ> Vset \<alpha>" by auto
  with assms(1) have r: "\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>r) \<in>\<^sub>\<circ> Vset \<alpha>" by blast
  from r assms(1) vfield_vsubset_VUnion2 show "\<F>\<^sub>\<circ> r \<in>\<^sub>\<circ> Vset \<alpha>" by auto
  from r assms(1) vdomain_vsubset_VUnion2 vrange_vsubset_VUnion2 show 
    "\<D>\<^sub>\<circ> r \<in>\<^sub>\<circ> Vset \<alpha>" "\<R>\<^sub>\<circ> r \<in>\<^sub>\<circ> Vset \<alpha>"
    by auto
qed

lemma (in vbrelation) vbrelation_Limit_vsubset_VsetI:
  assumes "Limit \<alpha>" and "\<D>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> Vset \<alpha>" and "\<R>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  shows "r \<subseteq>\<^sub>\<circ> Vset \<alpha>"
proof(intro vsubsetI)
  fix x assume "x \<in>\<^sub>\<circ> r"
  moreover then obtain a b where x_def: "x = \<langle>a, b\<rangle>" by (elim vbrelation_vinE)
  ultimately have "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r" by auto
  with assms show "x \<in>\<^sub>\<circ> Vset \<alpha>" unfolding x_def by auto
qed

lemma 
  assumes "r \<in>\<^sub>\<circ> Vset \<alpha>"
  shows fdomain_in_VsetI: "\<D>\<^sub>\<bullet> r \<in>\<^sub>\<circ> Vset \<alpha>" 
    and frange_in_VsetI: "\<R>\<^sub>\<bullet> r \<in>\<^sub>\<circ> Vset \<alpha>" 
    and ffield_in_VsetI: "\<F>\<^sub>\<bullet> r \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  from assms have "\<Union>\<^sub>\<circ>r \<in>\<^sub>\<circ> Vset \<alpha>" by auto
  with assms have r: "\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>r)) \<in>\<^sub>\<circ> Vset \<alpha>" by blast
  from r assms(1) fdomain_vsubset_VUnion2 frange_vsubset_VUnion2 show 
    "\<D>\<^sub>\<bullet> r \<in>\<^sub>\<circ> Vset \<alpha>" "\<R>\<^sub>\<bullet> r \<in>\<^sub>\<circ> Vset \<alpha>"
    by auto
  from r assms(1) ffield_vsubset_VUnion2 show "\<F>\<^sub>\<bullet> r \<in>\<^sub>\<circ> Vset \<alpha>" by auto
qed

lemma (in vsv) vsv_Limit_vrange_in_VsetI[intro]: 
  assumes "Limit \<alpha>" and "\<R>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> Vset \<alpha>" and "vfinite (\<D>\<^sub>\<circ> r)" 
  shows "\<R>\<^sub>\<circ> r \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms(3,1,2) vsv_axioms
proof(induction \<open>\<D>\<^sub>\<circ> r\<close> arbitrary: r rule: vfinite_induct)
  case vempty
  interpret r': vsv r by (rule vempty(4))
  from vempty(1) r'.vlrestriction_vdomain have "r = 0" by simp
  from Vset_in_mono vempty.prems(1) show ?case 
    unfolding \<open>r = 0\<close> by (auto simp: Limit_def)
next
  case (vinsert x F)
  interpret r': vsv r by (rule vinsert(7))
  have RrF_Rr: "\<R>\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<circ> F) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> r" by auto
  have F_DrF: "F = \<D>\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<circ> F)" 
    unfolding vdomain_vlrestriction vinsert(4)[symmetric] by auto
  moreover note assms(1)
  moreover from RrF_Rr vinsert(6) have "\<R>\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<circ> F) \<subseteq>\<^sub>\<circ> Vset \<alpha>" by auto
  moreover have "vsv (r \<restriction>\<^sup>l\<^sub>\<circ> F)" by simp
  ultimately have RrF_V\<alpha>: "\<R>\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<circ> F) \<in>\<^sub>\<circ> Vset \<alpha>" by (rule vinsert(3))
  have "\<R>\<^sub>\<circ> r = vinsert (r\<lparr>x\<rparr>) (\<R>\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<circ> F))" 
  proof(intro vsubset_antisym vsubsetI)
    fix b assume "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r"
    then obtain a where "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and b_def: "b = r\<lparr>a\<rparr>" by force
    with vinsert.hyps(4) have "a = x \<or> a \<in>\<^sub>\<circ> F" by auto
    with \<open>a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r\<close> show "b \<in>\<^sub>\<circ> vinsert (r\<lparr>x\<rparr>) (\<R>\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<circ> F))"
      unfolding b_def by (blast dest: r'.vsv_vimageI1)
  next
    fix b assume "b \<in>\<^sub>\<circ> vinsert (r\<lparr>x\<rparr>) (\<R>\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<circ> F))"
    with RrF_Rr r'.vsv_axioms vinsert.hyps(4) show "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r" by auto
  qed
  moreover with vinsert.prems(2) have "r\<lparr>x\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" by auto
  moreover have "\<R>\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<circ> F) \<in>\<^sub>\<circ> Vset \<alpha>" by (blast intro: RrF_V\<alpha>)
  ultimately show "\<R>\<^sub>\<circ> r \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (simp add: vinsert.prems(1) vinsert_in_VsetI)
qed

lemma (in vsv) vsv_Limit_vsv_in_VsetI[intro]: 
  assumes "Limit \<alpha>" 
    and "\<D>\<^sub>\<circ> r \<in>\<^sub>\<circ> Vset \<alpha>"
    and "\<R>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> Vset \<alpha>" 
    and "vfinite (\<D>\<^sub>\<circ> r)" 
  shows "r \<in>\<^sub>\<circ> Vset \<alpha>"
  by (simp add: assms vsv_Limit_vrange_in_VsetI vbrelation_Limit_in_VsetI)

lemma Limit_vcomp_in_VsetI:
  assumes "Limit \<alpha>" and "r \<in>\<^sub>\<circ> Vset \<alpha>" and "s \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "r \<circ>\<^sub>\<circ> s \<in>\<^sub>\<circ> Vset \<alpha>"
proof(rule vbrelation.vbrelation_Limit_in_VsetI; (intro assms(1))?)
  show "vbrelation (r \<circ>\<^sub>\<circ> s)" by auto
  have "\<D>\<^sub>\<circ> (r \<circ>\<^sub>\<circ> s) \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> s" by auto
  with assms(3) show "\<D>\<^sub>\<circ> (r \<circ>\<^sub>\<circ> s) \<in>\<^sub>\<circ> Vset \<alpha>"  
    by (auto simp: vdomain_in_VsetI vsubset_in_VsetI)
  have "\<R>\<^sub>\<circ> (r \<circ>\<^sub>\<circ> s) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> r" by auto
  with assms(2) show "\<R>\<^sub>\<circ> (r \<circ>\<^sub>\<circ> s) \<in>\<^sub>\<circ> Vset \<alpha>"
    by (auto simp: vrange_in_VsetI vsubset_in_VsetI)
qed


text\<open>Operations on indexed families of sets.\<close>

lemma Limit_vifintersection_in_VsetI:
  assumes "Limit \<alpha>" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> A i \<in>\<^sub>\<circ> Vset \<alpha>" and "vfinite I"
  shows "(\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  from assms(2) have range: "\<R>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>I. A i) \<subseteq>\<^sub>\<circ> Vset \<alpha>" by auto
  from assms(1) range assms(3) have "\<R>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>I. A i) \<in>\<^sub>\<circ> Vset \<alpha>"
    by (rule rel_VLambda.vsv_Limit_vrange_in_VsetI[unfolded vdomain_VLambda])
  then have "(\<lambda>i\<in>\<^sub>\<circ>I. A i) `\<^sub>\<circ> I \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (simp add: vimage_VLambda_vrange_rep)
  then show "(\<Inter>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<in>\<^sub>\<circ> Vset \<alpha>" by auto
qed

lemma Limit_vifunion_in_VsetI:
  assumes "Limit \<alpha>" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> A i \<in>\<^sub>\<circ> Vset \<alpha>" and "vfinite I"
  shows "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  from assms(2) have range: "\<R>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>I. A i) \<subseteq>\<^sub>\<circ> Vset \<alpha>" by auto
  from assms(1) range assms(3) have "\<R>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>I. A i) \<in>\<^sub>\<circ> Vset \<alpha>"
    by (rule rel_VLambda.vsv_Limit_vrange_in_VsetI[unfolded vdomain_VLambda])
  then have "(\<lambda>i\<in>\<^sub>\<circ>I. A i) `\<^sub>\<circ> I \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (simp add: vimage_VLambda_vrange_rep)
  then show "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<in>\<^sub>\<circ> Vset \<alpha>" by auto
qed

lemma Limit_vifunion_in_Vset_if_VLambda_in_VsetI:
  assumes "Limit \<alpha>" and "VLambda I A \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  from assms(2) have "\<R>\<^sub>\<circ> (\<lambda>i\<in>\<^sub>\<circ>I. A i) \<in>\<^sub>\<circ> Vset \<alpha>"
    by (simp add: vrange_in_VsetI)
  then have "(\<lambda>i\<in>\<^sub>\<circ>I. A i) `\<^sub>\<circ> I \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (simp add: vimage_VLambda_vrange_rep)
  then show "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<in>\<^sub>\<circ> Vset \<alpha>" by auto
qed

lemma Limit_vproduct_in_VsetI:
  assumes "Limit \<alpha>" 
    and "I \<in>\<^sub>\<circ> Vset \<alpha>" 
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> A i \<in>\<^sub>\<circ> Vset \<alpha>" 
    and "vfinite I"
  shows "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  have "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<in>\<^sub>\<circ> Vset \<alpha>"
    by (rule Limit_vifunion_in_VsetI) (simp_all add: assms(1,3,4))
  with assms have "I \<times>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<in>\<^sub>\<circ> Vset \<alpha>" by auto
  with assms(1) have "VPow (I \<times>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)) \<in>\<^sub>\<circ> Vset \<alpha>" by auto
  from vsubset_in_VsetI[OF vproduct_vsubset_VPow[of I A] this] show ?thesis 
    by simp
qed

lemma Limit_vproduct_in_Vset_if_VLambda_in_VsetI:
  assumes "Limit \<alpha>" and "VLambda I A \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  have "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<in>\<^sub>\<circ> Vset \<alpha>"
    by (rule Limit_vifunion_in_Vset_if_VLambda_in_VsetI) 
      (simp_all add: assms)
  moreover from assms(2) have "I \<in>\<^sub>\<circ> Vset \<alpha>"
    by (metis vdomain_VLambda vdomain_in_VsetI)
  ultimately have "I \<times>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<in>\<^sub>\<circ> Vset \<alpha>" 
    using assms by auto
  with assms(1) have "VPow (I \<times>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)) \<in>\<^sub>\<circ> Vset \<alpha>" by auto
  from vsubset_in_VsetI[OF vproduct_vsubset_VPow[of I A] this] show ?thesis 
    by simp  
qed

lemma vrange_vprojection_in_VsetI:
  assumes "Limit \<alpha>" 
    and "A \<in>\<^sub>\<circ> Vset \<alpha>" 
    and "\<And>f. f \<in>\<^sub>\<circ> A \<Longrightarrow> vsv f"
    and "\<And>f. f \<in>\<^sub>\<circ> A \<Longrightarrow> x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> f"
  shows "\<R>\<^sub>\<circ> (\<lambda>f\<in>\<^sub>\<circ>A. f\<lparr>x\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  have "\<R>\<^sub>\<circ> (\<lambda>f\<in>\<^sub>\<circ>A. f\<lparr>x\<rparr>) \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>A))"
  proof(intro vsubsetI)
    fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<lambda>f\<in>\<^sub>\<circ>A. f\<lparr>x\<rparr>)"
    then obtain f where f: "f \<in>\<^sub>\<circ> A" and y_def: "y = f\<lparr>x\<rparr>" by auto
    from f have "vsv f" and "x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> f" by (auto intro: assms(3,4))+
    with y_def have xy: "\<langle>x, y\<rangle> \<in>\<^sub>\<circ> f" by auto
    show "y \<in>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>A))"
    proof(intro VUnionI)
      show "f \<in>\<^sub>\<circ> A" by (rule f)
      show "\<langle>x, y\<rangle> \<in>\<^sub>\<circ> f" by (rule xy)
      show "set {x, y} \<in>\<^sub>\<circ> \<langle>x, y\<rangle>" unfolding vpair_def by simp
    qed auto
  qed
  moreover from assms(1,2) have "\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>A)) \<in>\<^sub>\<circ> Vset \<alpha>"
    by (intro VUnion_in_VsetI)
  ultimately show ?thesis by auto
qed

lemma Limit_vcpower_in_VsetI:
  assumes "Limit \<alpha>" and "n \<in>\<^sub>\<circ> Vset \<alpha>" and "A \<in>\<^sub>\<circ> Vset \<alpha>" and "vfinite n"
  shows "A ^\<^sub>\<times> n \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms Limit_vproduct_in_VsetI unfolding vcpower_def by auto


text\<open>Finite sets.\<close>

lemma Limit_vfinite_in_VsetI:
  assumes "Limit \<alpha>" and "A \<subseteq>\<^sub>\<circ> Vset \<alpha>" and "vfinite A"
  shows "A \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  from assms(3) obtain n where n: "n \<in>\<^sub>\<circ> \<omega>" and "n \<approx>\<^sub>\<circ> A" by clarsimp
  then obtain f where f: "v11 f" and dr: "\<D>\<^sub>\<circ> f = n" "\<R>\<^sub>\<circ> f = A" by auto
  interpret f: v11 f by (rule f)
  from n have n: "vfinite n" by auto
  show ?thesis 
    by (rule f.vsv_Limit_vrange_in_VsetI[simplified dr, OF assms(1,2) n])
qed


text\<open>Ordinal numbers.\<close>

lemma Limit_omega_in_VsetI:
  assumes "Limit \<alpha>"
  shows "a\<^sub>\<nat> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  from assms have "\<alpha> \<subseteq>\<^sub>\<circ> Vset \<alpha>" by force
  moreover have "\<omega> \<subseteq>\<^sub>\<circ> \<alpha>" by (simp add: assms omega_le_Limit)
  moreover have "a\<^sub>\<nat> \<in>\<^sub>\<circ> \<omega>" by simp
  ultimately show "a\<^sub>\<nat> \<in>\<^sub>\<circ> Vset \<alpha>" by auto
qed

lemma Limit_succ_in_VsetI:
  assumes "Limit \<alpha>" and "a \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "succ a \<in>\<^sub>\<circ> Vset \<alpha>"
  by (simp add: assms succ_def vinsert_in_VsetI)


text\<open>Sequences.\<close>

lemma (in vfsequence) vfsequence_Limit_vcons_in_VsetI:
  assumes "Limit \<alpha>" and "x \<in>\<^sub>\<circ> Vset \<alpha>" and "xs \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "vcons xs x \<in>\<^sub>\<circ> Vset \<alpha>"
  unfolding vcons_def
proof(intro vinsert_in_VsetI Limit_vpair_in_VsetI assms)
  show "vcard xs \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (metis assms(3) vdomain_in_VsetI vfsequence_vdomain)
qed


text\<open>\<open>ftimes\<close>.\<close>

lemma Limit_ftimes_in_VsetI: 
  assumes "Limit \<alpha>" and "A \<in>\<^sub>\<circ> Vset \<alpha>" and "B \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "A \<times>\<^sub>\<bullet> B \<in>\<^sub>\<circ> Vset \<alpha>"
    unfolding ftimes_def
proof(rule Limit_vproduct_in_VsetI)
  from assms(1) show "2\<^sub>\<nat> \<in>\<^sub>\<circ> Vset \<alpha>" by (meson Limit_omega_in_VsetI)
  fix i assume "i \<in>\<^sub>\<circ> 2\<^sub>\<nat>"
  with assms(2,3) show "(i = 0 ? A : B) \<in>\<^sub>\<circ> Vset \<alpha>" by simp
qed (auto simp: assms(1))


text\<open>Auxiliary results.\<close>

lemma vempty_in_Vset_succ[simp, intro]: "0 \<in>\<^sub>\<circ> Vfrom a (succ b)"
  unfolding Vfrom_succ by force

lemma Ord_vpair_in_Vset_succI[intro]:
  assumes "Ord \<alpha>" and "a \<in>\<^sub>\<circ> Vset \<alpha>" and "b \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> Vset (succ (succ \<alpha>))"
  unfolding vpair_def
proof-
  have aab: "set {set {a}, set {a, b}} = vinsert (set {a}) (set {set {a, b}})"
    by auto
  show "set {set {a}, set {a, b}} \<in>\<^sub>\<circ> Vset (succ (succ \<alpha>))"
    unfolding aab
    by 
      (
        intro
          assms
          vinsert_in_Vset_succI'
          Ord_vsingleton_in_Vset_succI 
          Ord_vdoubleton_in_Vset_succI 
          Ord_succ
      ) 
qed

lemma Limit_vifunion_vsubset_VsetI:
  assumes "Limit \<alpha>" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> A i \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<subseteq>\<^sub>\<circ> Vset \<alpha>"
proof(intro vsubsetI)
  fix x assume "x \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)"
  then obtain i where i: "i \<in>\<^sub>\<circ> I" and "x \<in>\<^sub>\<circ> A i" by auto
  with assms(1) assms(2)[OF i] show "x \<in>\<^sub>\<circ> Vset \<alpha>" by auto
qed

lemma Limit_vproduct_vsubset_Vset_succI:
  assumes "Limit \<alpha>" and "I \<in>\<^sub>\<circ> Vset \<alpha>" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> A i \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  shows "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<subseteq>\<^sub>\<circ> Vset (succ \<alpha>)"
proof(intro vsubsetI)
  fix a assume prems: "a \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)"
  note a = vproductD[OF prems]
  interpret vsv a by (rule a(1))
  from prems have "\<R>\<^sub>\<circ> a \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)" by (rule vproduct_vrange)  
  moreover have "(\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<subseteq>\<^sub>\<circ> Vset \<alpha>" by (intro vifunion_least assms(3))
  ultimately have "\<R>\<^sub>\<circ> a \<subseteq>\<^sub>\<circ> Vset \<alpha>" by auto
  moreover from assms(2) prems have "\<D>\<^sub>\<circ> a \<subseteq>\<^sub>\<circ> Vset \<alpha>" unfolding a(2) by auto
  ultimately have "a \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    by (intro assms(1) vbrelation_Limit_vsubset_VsetI)
  with assms(1) show "a \<in>\<^sub>\<circ> Vset (succ \<alpha>)"
    by (simp add: Limit_is_Ord Ord_vsubset_in_Vset_succI)
qed

lemma Limit_vproduct_vsubset_Vset_succI':
  assumes "Limit \<alpha>" and "I \<in>\<^sub>\<circ> Vset \<alpha>" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> A i \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<subseteq>\<^sub>\<circ> Vset (succ \<alpha>)"
proof-
  have "A i \<subseteq>\<^sub>\<circ> Vset \<alpha>" if "i \<in>\<^sub>\<circ> I" for i
    by (simp add: Vset_trans vsubsetI assms(3) that)
  from assms(1,2) this show ?thesis by (rule Limit_vproduct_vsubset_Vset_succI)
qed

lemma (in vfsequence) vfsequence_Ord_vcons_in_Vset_succI: 
  assumes "Ord \<alpha>"
    and "\<omega> \<in>\<^sub>\<circ> \<alpha>"
    and "x \<in>\<^sub>\<circ> Vset \<alpha>"
    and "xs \<in>\<^sub>\<circ> Vset (succ (succ (succ \<alpha>)))"
  shows "vcons xs x \<in>\<^sub>\<circ> Vset (succ (succ (succ \<alpha>)))"
  unfolding vcons_def
proof(intro vinsert_in_Vset_succI' Ord_succ Ord_vpair_in_Vset_succI assms)
  have "vcard xs = \<D>\<^sub>\<circ> xs" by (simp add: vfsequence_vdomain)
  from assms(1,2) vfsequence_vdomain_in_omega show "vcard xs \<in>\<^sub>\<circ> Vset \<alpha>" 
    unfolding vfsequence_vdomain[symmetric]
    by (meson Ord_in_in_VsetI Vset_trans)
qed

lemma Limit_VUnion_vdomain_in_VsetI:
  assumes "Limit \<alpha>" and "Q \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "(\<Union>\<^sub>\<circ>r\<in>\<^sub>\<circ>Q. \<D>\<^sub>\<circ> r) \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  have "(\<Union>\<^sub>\<circ>r\<in>\<^sub>\<circ>Q. \<D>\<^sub>\<circ> r) \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>Q))"
  proof(intro vsubsetI)
    fix a assume "a \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>r\<in>\<^sub>\<circ>Q. \<D>\<^sub>\<circ> r)"
    then obtain r where r: "r \<in>\<^sub>\<circ> Q" and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" by auto
    with assms obtain b where ab: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" by auto
    show "a \<in>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>Q))"
    proof(intro VUnionI)
      show "r \<in>\<^sub>\<circ> Q" by (rule r)  
      show "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" by (rule ab)
      show "set {a, b} \<in>\<^sub>\<circ> \<langle>a, b\<rangle>" unfolding vpair_def by simp
    qed auto
  qed
  moreover from assms(2) have "\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>Q)) \<in>\<^sub>\<circ> Vset \<alpha>"
    by (blast dest!: VUnion_in_VsetI)
  ultimately show ?thesis using assms(1) by (auto simp: vsubset_in_VsetI)
qed

lemma Limit_VUnion_vrange_in_VsetI:
  assumes "Limit \<alpha>" and "Q \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "(\<Union>\<^sub>\<circ>r\<in>\<^sub>\<circ>Q. \<R>\<^sub>\<circ> r) \<in>\<^sub>\<circ> Vset \<alpha>"
proof-(*FIXME: duality*)
  have "(\<Union>\<^sub>\<circ>r\<in>\<^sub>\<circ>Q. \<R>\<^sub>\<circ> r) \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>Q))"
  proof(intro vsubsetI)
    fix b assume "b \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>r\<in>\<^sub>\<circ>Q. \<R>\<^sub>\<circ> r)"
    then obtain r where r: "r \<in>\<^sub>\<circ> Q" and "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r" by auto
    with assms obtain a where ab: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" by auto
    show "b \<in>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>Q))"
    proof(intro VUnionI)
      show "r \<in>\<^sub>\<circ> Q" by (rule r)  
      show "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> r" by (rule ab)
      show "set {a, b} \<in>\<^sub>\<circ> \<langle>a, b\<rangle>" unfolding vpair_def by simp
    qed auto
  qed
  moreover from assms(2) have "\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>Q)) \<in>\<^sub>\<circ> Vset \<alpha>"
    by (blast dest!: VUnion_in_VsetI)
  ultimately show ?thesis using assms(1) by (auto simp: vsubset_in_VsetI)
qed



subsection\<open>Axioms for \<^term>\<open>Vset \<alpha>\<close>\<close>


text\<open>
The subsection demonstrates that the axioms of ZFC except for the 
Axiom Schema of Replacement hold in \<^term>\<open>Vset \<alpha>\<close> for any limit ordinal
\<^term>\<open>\<alpha>\<close> such that \<^term>\<open>\<omega> \<in>\<^sub>\<circ> \<alpha>\<close>\footnote{The presentation of the axioms is 
loosely based on the statement of the axioms of ZFC in Chapters 1-11 in 
\cite{takeuti_introduction_1971}.}.
\<close>

locale \<Z> = 
  fixes \<alpha> 
  assumes Limit_\<alpha>[intro, simp]: "Limit \<alpha>"
    and omega_in_\<alpha>[intro, simp]: "\<omega> \<in>\<^sub>\<circ> \<alpha>"
begin

lemmas [intro] = \<Z>_axioms

lemma vempty_Z_def: "0 = set {x. x \<noteq> x}" by auto

lemma vempty_is_zet[intro, simp]: "0 \<in>\<^sub>\<circ> Vset \<alpha>" 
  using Vset_in_mono omega_in_\<alpha> by auto

lemma Axiom_of_Extensionality:
  assumes "a \<in>\<^sub>\<circ> Vset \<alpha>" and "x = y" and "x \<in>\<^sub>\<circ> a" 
  shows "y \<in>\<^sub>\<circ> a" and "x \<in>\<^sub>\<circ> Vset \<alpha>" and "y \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms by (simp_all add: Vset_trans)

lemma Axiom_of_Pairing:
  assumes "a \<in>\<^sub>\<circ> Vset \<alpha>" and "b \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "set {a, b} \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms by (simp add: Limit_vdoubleton_in_VsetI)

lemma Axiom_of_Unions:
  assumes "a \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "\<Union>\<^sub>\<circ>a \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms by (simp add: VUnion_in_VsetI)

lemma Axiom_of_Powers:
  assumes "a \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "VPow a \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms by (simp add: Limit_VPow_in_VsetI)

lemma Axiom_of_Regularity:
  assumes "a \<noteq> 0" and "a \<in>\<^sub>\<circ> Vset \<alpha>"
  obtains x where "x \<in>\<^sub>\<circ> a" and "x \<inter>\<^sub>\<circ> a = 0"
  using assms by (auto dest: trad_foundation)

lemma Axiom_of_Infinity: "\<omega> \<in>\<^sub>\<circ> Vset \<alpha>"
  using Limit_is_Ord by (auto simp: Ord_iff_rank Ord_VsetI OrdmemD)

lemma Axiom_of_Choice: 
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>"
  obtains f where "f \<in>\<^sub>\<circ> Vset \<alpha>" and "\<And>x. x \<in>\<^sub>\<circ> A \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> f\<lparr>x\<rparr> \<in>\<^sub>\<circ> x"
proof-
  define f where "f = (\<lambda>x\<in>\<^sub>\<circ>A. (SOME a. a \<in>\<^sub>\<circ> x \<or> (x = 0 \<and> a = 0)))"
  interpret vsv f unfolding f_def by auto
  have A_def: "A = \<D>\<^sub>\<circ> f" unfolding f_def by simp
  have Rf: "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> vinsert 0 (\<Union>\<^sub>\<circ>A)"
  proof(rule vsubsetI)
    fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> f" 
    then obtain x where "x \<in>\<^sub>\<circ> A" and "y = f\<lparr>x\<rparr>" 
      unfolding A_def by (blast dest: vrange_atD)
    then have y_def: "y = (SOME a. a \<in>\<^sub>\<circ> x \<or> x = 0 \<and> a = 0)"
      unfolding f_def unfolding A_def by simp
    have "y = 0 \<or> y \<in>\<^sub>\<circ> x"
    proof(cases \<open>x = 0\<close>)
      case False then show ?thesis 
        unfolding y_def by (metis (mono_tags, lifting) verit_sko_ex' vemptyE)
    qed (simp add: y_def)
    with \<open>x \<in>\<^sub>\<circ> A\<close> show "y \<in>\<^sub>\<circ> vinsert 0 (\<Union>\<^sub>\<circ>A)" by clarsimp
  qed
  from assms have "\<Union>\<^sub>\<circ>A \<in>\<^sub>\<circ> Vset \<alpha>" by (simp add: Axiom_of_Unions)
  with vempty_is_zet Limit_\<alpha> have "vinsert 0 (\<Union>\<^sub>\<circ>A) \<in>\<^sub>\<circ> Vset \<alpha>" by auto
  with Rf have "\<R>\<^sub>\<circ> f \<in>\<^sub>\<circ> Vset \<alpha>" by auto
  with Limit_\<alpha> assms[unfolded A_def] have "f \<in>\<^sub>\<circ> Vset \<alpha>" by auto
  moreover have "x \<in>\<^sub>\<circ> A \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> f\<lparr>x\<rparr> \<in>\<^sub>\<circ> x" for x
  proof-
    assume prems: "x \<in>\<^sub>\<circ> A" "x \<noteq> 0"
    then have "f\<lparr>x\<rparr> = (SOME a. a \<in>\<^sub>\<circ> x \<or> (x = 0 \<and> a = 0))"
      unfolding f_def by simp
    with prems(2) show "f\<lparr>x\<rparr> \<in>\<^sub>\<circ> x"
      by (metis (mono_tags, lifting) someI_ex vemptyE)
  qed
  ultimately show ?thesis by (simp add: that)
qed

end


text\<open>Trivial corollaries.\<close>

lemma (in \<Z>) Ord_\<alpha>: "Ord \<alpha>" by auto

lemma (in \<Z>) \<Z>_Vset_\<omega>2_vsubset_Vset: "Vset (\<omega> + \<omega>) \<subseteq>\<^sub>\<circ> Vset \<alpha>" 
  by (simp add: Vset_vsubset_mono omega2_vsubset_Limit)

lemma (in \<Z>) \<Z>_Limit_\<alpha>\<omega>: "Limit (\<alpha> + \<omega>)" by (simp add: Limit_is_Ord)

lemma (in \<Z>) \<Z>_\<alpha>_\<alpha>\<omega>: "\<alpha> \<in>\<^sub>\<circ> \<alpha> + \<omega>" 
  by (simp add: Limit_is_Ord Ord_mem_iff_lt)

lemma (in \<Z>) \<Z>_\<omega>_\<alpha>\<omega>: "\<omega> \<in>\<^sub>\<circ> \<alpha> + \<omega>" 
  using add_le_cancel_left0 by blast

lemma \<Z>_\<omega>\<omega>: "\<Z> (\<omega> + \<omega>)"
  using \<omega>_gt0 by (auto intro: \<Z>.intro simp: Ord_mem_iff_lt)

lemma (in \<Z>) in_omega_in_omega_plus[intro]:
  assumes "a \<in>\<^sub>\<circ> \<omega>"
  shows "a \<in>\<^sub>\<circ> Vset (\<alpha> + \<omega>)"
proof-
  from assms have "a \<in>\<^sub>\<circ> Vset \<omega>" by auto
  moreover have "Vset \<omega> \<in>\<^sub>\<circ> Vset (\<alpha> + \<omega>)" by (simp add: Vset_in_mono \<Z>_\<omega>_\<alpha>\<omega>)
  ultimately show "a \<in>\<^sub>\<circ> Vset (\<alpha> + \<omega>)" by auto
qed

lemma (in \<Z>) ord_of_nat_in_Vset[simp]: "a\<^sub>\<nat> \<in>\<^sub>\<circ> Vset \<alpha>" by force



subsection\<open>Existence of a disjoint subset in \<^term>\<open>Vset \<alpha>\<close>\<close>

definition mk_doubleton :: "V \<Rightarrow> V \<Rightarrow> V"
  where "mk_doubleton X a = set {a, X}"

definition mk_doubleton_image :: "V \<Rightarrow> V \<Rightarrow> V"
  where "mk_doubleton_image X Y = set (mk_doubleton Y ` elts X)"

lemma inj_on_mk_doubleton: "inj_on (mk_doubleton X) (elts X)"
proof
  fix a b assume "mk_doubleton X a = mk_doubleton X b" 
  then have "{a, X} = {b, X}" unfolding mk_doubleton_def by auto
  then show "a = b" by (metis doubleton_eq_iff)
qed

lemma mk_doubleton_image_vsubset_veqpoll: 
  assumes "X \<subseteq>\<^sub>\<circ> Y"
  shows "mk_doubleton_image X X \<approx>\<^sub>\<circ> mk_doubleton_image X Y"
  unfolding eqpoll_def
proof(intro exI[of _ \<open>\<lambda>A. vinsert Y (A -\<^sub>\<circ> set {X})\<close>] bij_betw_imageI)
  show "inj_on (\<lambda>A. vinsert Y (A -\<^sub>\<circ> set {X})) (elts (mk_doubleton_image X X))"
    unfolding mk_doubleton_image_def
  proof(intro inj_onI)
    fix y y' assume prems: 
      "y \<in>\<^sub>\<circ> set (mk_doubleton X ` elts X)" 
      "y' \<in>\<^sub>\<circ> set (mk_doubleton X ` elts X)" 
      "vinsert Y (y -\<^sub>\<circ> set {X}) = vinsert Y (y' -\<^sub>\<circ> set {X})" 
    then obtain x x' 
      where "x \<in>\<^sub>\<circ> X" 
        and "x' \<in>\<^sub>\<circ> X" 
        and y_def: "y = set {x, X}" 
        and y'_def: "y' = set {x', X}"
      by (clarsimp simp: mk_doubleton_def)
    with assms have xX_X: "set {x, X} -\<^sub>\<circ> set {X} = set {x}" 
      and x'X_X: "set {x', X} -\<^sub>\<circ> set {X} = set {x'}"
      by fastforce+
    from prems(3)[unfolded y_def y'_def] have "set {x, Y} = set {x', Y}"
      unfolding xX_X x'X_X by auto
    then have "x = x'" by (auto simp: doubleton_eq_iff)
    then show "y = y'" unfolding y_def y'_def by simp
  qed
  show 
    "(\<lambda>A. vinsert Y (A -\<^sub>\<circ> set {X})) ` (elts (mk_doubleton_image X X)) = 
      (elts (mk_doubleton_image X Y))"
  proof(intro subset_antisym subsetI)
    fix z
    assume prems:
      "z \<in> (\<lambda>A. vinsert Y (A -\<^sub>\<circ> set {X})) ` (elts (mk_doubleton_image X X))"
    then obtain y 
      where "y \<in>\<^sub>\<circ> set (mk_doubleton X ` elts X)"
        and z_def: "z = vinsert Y (y -\<^sub>\<circ> set {X})"
      unfolding mk_doubleton_image_def by auto
    then obtain x where xX: "x \<in>\<^sub>\<circ> X" and y_def: "y = set {x, X}" 
      unfolding mk_doubleton_def by clarsimp
    from xX have y_X: "y -\<^sub>\<circ> set {X} = set {x}" unfolding y_def by fastforce
    from z_def have z_def': "z = set {x, Y}"
      unfolding y_X by (simp add: doubleton_eq_iff vinsert_vsingleton)
    from xX show "z \<in>\<^sub>\<circ> mk_doubleton_image X Y"
      unfolding z_def' mk_doubleton_def mk_doubleton_image_def by simp
  next
    fix z assume prems: "z \<in>\<^sub>\<circ> mk_doubleton_image X Y"
    then obtain x where xX: "x \<in>\<^sub>\<circ> X" and z_def: "z = set {x, Y}" 
      unfolding mk_doubleton_def mk_doubleton_image_def by clarsimp
    from xX have xX_XX: "set {x, X} \<in>\<^sub>\<circ> set (mk_doubleton X ` elts X)"
      unfolding mk_doubleton_def by simp
    from xX have xX_X: "set {x, X} -\<^sub>\<circ> set {X} = set {x}" by fastforce
    have z_def': "z = vinsert Y (set {x, X} -\<^sub>\<circ> set {X})"
      unfolding xX_X z_def by auto
    with xX_XX show 
      "z \<in> (\<lambda>A. vinsert Y (A -\<^sub>\<circ> set {X})) ` (elts (mk_doubleton_image X X))"
      unfolding z_def' mk_doubleton_image_def by simp
  qed
qed

lemma mk_doubleton_image_veqpoll: 
  assumes "X \<subseteq>\<^sub>\<circ> Y"
  shows "X \<approx>\<^sub>\<circ> mk_doubleton_image X Y"
proof-
  have "X \<approx>\<^sub>\<circ> mk_doubleton_image X X"
    unfolding mk_doubleton_image_def by (auto simp: inj_on_mk_doubleton)
  also have "\<dots> \<approx> elts (mk_doubleton_image X Y)"
    by (rule mk_doubleton_image_vsubset_veqpoll[OF assms])
  finally show "X \<approx>\<^sub>\<circ> mk_doubleton_image X Y".
qed

lemma vdisjnt_mk_doubleton_image: "vdisjnt (mk_doubleton_image X Y) Y"
proof
  fix b assume prems: "b \<in>\<^sub>\<circ> Y" "b \<in>\<^sub>\<circ> mk_doubleton_image X Y" 
  then obtain a where "a \<in>\<^sub>\<circ> X" and "set {a, Y} = b" 
    unfolding mk_doubleton_def mk_doubleton_image_def by clarsimp
  then have "Y \<in>\<^sub>\<circ> b" by clarsimp
  with mem_not_sym show False by (simp add: prems)
qed

lemma Limit_mk_doubleton_image_vsubset_Vset: 
  assumes "Limit \<alpha>" and "X \<subseteq>\<^sub>\<circ> Y" and "Y \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "mk_doubleton_image X Y \<subseteq>\<^sub>\<circ> Vset \<alpha>"
proof(intro vsubsetI)
  fix b assume "b \<in>\<^sub>\<circ> mk_doubleton_image X Y"
  then obtain a where "b = mk_doubleton Y a" and "a \<in>\<^sub>\<circ> X" 
    unfolding mk_doubleton_image_def by clarsimp
  with assms have b_def: "b = set {a, Y}" and a\<alpha>: "a \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (auto simp: mk_doubleton_def)
  from this(2) assms show "b \<in>\<^sub>\<circ> Vset \<alpha>"
    unfolding b_def by (simp add: Limit_vdoubleton_in_VsetI)
qed

lemma Ord_mk_doubleton_image_vsubset_Vset_succ: 
  assumes "Ord \<alpha>" and "X \<subseteq>\<^sub>\<circ> Y" and "Y \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "mk_doubleton_image X Y \<subseteq>\<^sub>\<circ> Vset (succ \<alpha>)"
proof(intro vsubsetI)
  fix b assume "b \<in>\<^sub>\<circ> mk_doubleton_image X Y"
  then obtain a where "b = mk_doubleton Y a" and "a \<in>\<^sub>\<circ> X" 
    unfolding mk_doubleton_image_def by clarsimp
  with assms have b_def: "b = set {a, Y}" and a\<alpha>: "a \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (auto simp: mk_doubleton_def)
  from this(2) assms show "b \<in>\<^sub>\<circ> Vset (succ \<alpha>)"
    unfolding b_def by (simp add: Ord_vdoubleton_in_Vset_succI)
qed

lemma Limit_ex_eqpoll_vdisjnt:
  assumes "Limit \<alpha>" and "X \<subseteq>\<^sub>\<circ> Y" and "Y \<in>\<^sub>\<circ> Vset \<alpha>"
  obtains Z where "X \<approx>\<^sub>\<circ> Z" and "vdisjnt Z Y" and "Z \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  using assms
  by (intro that[of \<open>mk_doubleton_image X Y\<close>])
    (
      simp_all add: 
        mk_doubleton_image_veqpoll 
        vdisjnt_mk_doubleton_image 
        Limit_mk_doubleton_image_vsubset_Vset
    )

lemma Ord_ex_eqpoll_vdisjnt:
  assumes "Ord \<alpha>" and "X \<subseteq>\<^sub>\<circ> Y" and "Y \<in>\<^sub>\<circ> Vset \<alpha>"
  obtains Z where "X \<approx>\<^sub>\<circ> Z" and "vdisjnt Z Y" and "Z \<subseteq>\<^sub>\<circ> Vset (succ \<alpha>)"
  using assms
  by (intro that[of \<open>mk_doubleton_image X Y\<close>])
    (
      simp_all add: 
        mk_doubleton_image_veqpoll 
        vdisjnt_mk_doubleton_image 
        Ord_mk_doubleton_image_vsubset_Vset_succ
    )

text\<open>\newpage\<close>

end