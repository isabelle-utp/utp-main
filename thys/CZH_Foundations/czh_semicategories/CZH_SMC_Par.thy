(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>Par\<close> as a semicategory\<close>
theory CZH_SMC_Par
  imports 
    CZH_DG_Par
    CZH_SMC_Rel
    CZH_SMC_Subsemicategory
begin



subsection\<open>Background\<close>


text\<open>
The methodology chosen for the exposition 
of \<open>Par\<close> as a semicategory is analogous to the 
one used in the previous chapter for the exposition of \<open>Par\<close> as a digraph. 
\<close>

named_theorems smc_Par_cs_simps
named_theorems smc_Par_cs_intros

lemmas (in arr_Par) [smc_Par_cs_simps] = 
  dg_Rel_shared_cs_simps

lemmas [smc_Par_cs_simps] = 
  dg_Rel_shared_cs_simps
  arr_Par.arr_Par_length
  arr_Par_comp_Par_id_Par_left
  arr_Par_comp_Par_id_Par_right

lemmas [smc_Par_cs_intros] = 
  dg_Rel_shared_cs_intros
  arr_Par_comp_Par



subsection\<open>\<open>Par\<close> as a semicategory\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition smc_Par :: "V \<Rightarrow> V"
  where "smc_Par \<alpha> =
    [
      Vset \<alpha>,
      set {T. arr_Par \<alpha> T},
      (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Par \<alpha> T}. T\<lparr>ArrDom\<rparr>),
      (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Par \<alpha> T}. T\<lparr>ArrCod\<rparr>),
      (\<lambda>ST\<in>\<^sub>\<circ>composable_arrs (dg_Par \<alpha>). ST\<lparr>0\<rparr> \<circ>\<^sub>R\<^sub>e\<^sub>l ST\<lparr>1\<^sub>\<nat>\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smc_Par_components:
  shows "smc_Par \<alpha>\<lparr>Obj\<rparr> = Vset \<alpha>"
    and "smc_Par \<alpha>\<lparr>Arr\<rparr> = set {T. arr_Par \<alpha> T}"
    and "smc_Par \<alpha>\<lparr>Dom\<rparr> = (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Par \<alpha> T}. T\<lparr>ArrDom\<rparr>)"
    and "smc_Par \<alpha>\<lparr>Cod\<rparr> = (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Par \<alpha> T}. T\<lparr>ArrCod\<rparr>)"
    and "smc_Par \<alpha>\<lparr>Comp\<rparr> = (\<lambda>ST\<in>\<^sub>\<circ>composable_arrs (dg_Par \<alpha>). ST\<lparr>0\<rparr> \<circ>\<^sub>R\<^sub>e\<^sub>l ST\<lparr>1\<^sub>\<nat>\<rparr>)"
  unfolding smc_Par_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smc_dg_smc_Par: "smc_dg (smc_Par \<alpha>) = dg_Par \<alpha>"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> (smc_dg (smc_Par \<alpha>)) = 4\<^sub>\<nat>" 
    unfolding smc_dg_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (dg_Par \<alpha>) = 4\<^sub>\<nat>"
    unfolding dg_Par_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (smc_dg (smc_Par \<alpha>)) = \<D>\<^sub>\<circ> (dg_Par \<alpha>)"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_dg (smc_Par \<alpha>)) \<Longrightarrow> smc_dg (smc_Par \<alpha>)\<lparr>a\<rparr> = dg_Par \<alpha>\<lparr>a\<rparr>"
    for a
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral, 
        unfold smc_dg_def dg_field_simps smc_Par_def dg_Par_def
      )
      (auto simp: nat_omega_simps)
qed (auto simp: dg_Par_def smc_dg_def)

lemmas_with [folded smc_dg_smc_Par, unfolded slicing_simps]: 
  smc_Par_Obj_iff = dg_Par_Obj_iff
  and smc_Par_Arr_iff[smc_Par_cs_simps] = dg_Par_Arr_iff
  and smc_Par_Dom_vsv[smc_Par_cs_intros] = dg_Par_Dom_vsv
  and smc_Par_Dom_vdomain[smc_Par_cs_simps] = dg_Par_Dom_vdomain
  and smc_Par_Dom_vrange = dg_Par_Dom_vrange
  and smc_Par_Dom_app[smc_Par_cs_simps] = dg_Par_Dom_app
  and smc_Par_Cod_vsv[smc_Par_cs_intros] = dg_Par_Cod_vsv
  and smc_Par_Cod_vdomain[smc_Par_cs_simps] = dg_Par_Cod_vdomain
  and smc_Par_Cod_vrange = dg_Par_Cod_vrange
  and smc_Par_Cod_app[smc_Par_cs_simps] = dg_Par_Cod_app
  and smc_Par_is_arrI = dg_Par_is_arrI
  and smc_Par_is_arrD = dg_Par_is_arrD
  and smc_Par_is_arrE = dg_Par_is_arrE

lemmas [smc_cs_simps] = smc_Par_is_arrD(2,3)

lemmas [smc_Par_cs_intros] = smc_Par_is_arrI

lemmas_with (in \<Z>) [folded smc_dg_smc_Par, unfolded slicing_simps]: 
  smc_Par_Hom_vifunion_in_Vset = dg_Par_Hom_vifunion_in_Vset
  and smc_Par_incl_Par_is_arr = dg_Par_incl_Par_is_arr
  and smc_Par_incl_Par_is_arr'[smc_Par_cs_intros] = dg_Par_incl_Par_is_arr'

lemmas [smc_Par_cs_intros] = \<Z>.smc_Par_incl_Par_is_arr'


subsubsection\<open>Composable arrows\<close>

lemma smc_Par_composable_arrs_dg_Par: 
  "composable_arrs (dg_Par \<alpha>) = composable_arrs (smc_Par \<alpha>)"
  unfolding composable_arrs_def smc_dg_smc_Par[symmetric] slicing_simps by simp

lemma smc_Par_Comp: 
  "smc_Par \<alpha>\<lparr>Comp\<rparr> = (\<lambda>ST\<in>\<^sub>\<circ>composable_arrs (smc_Par \<alpha>). ST\<lparr>0\<rparr> \<circ>\<^sub>R\<^sub>e\<^sub>l ST\<lparr>1\<^sub>\<nat>\<rparr>)"
  unfolding smc_Par_components smc_Par_composable_arrs_dg_Par ..


subsubsection\<open>Composition\<close>

lemma smc_Par_Comp_app[smc_Par_cs_simps]:
  assumes "S : B \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> C" and "T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B"
  shows "S \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> T = S \<circ>\<^sub>R\<^sub>e\<^sub>l T"
proof-
  from assms have "[S, T]\<^sub>\<circ> \<in>\<^sub>\<circ> composable_arrs (smc_Par \<alpha>)" 
    by (auto simp: smc_cs_intros)
  then show "S \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> T = S \<circ>\<^sub>R\<^sub>e\<^sub>l T"
    unfolding smc_Par_Comp by (simp add: nat_omega_simps)
qed 

lemma smc_Par_Comp_vdomain: "\<D>\<^sub>\<circ> (smc_Par \<alpha>\<lparr>Comp\<rparr>) = composable_arrs (smc_Par \<alpha>)" 
  unfolding smc_Par_Comp by simp

lemma (in \<Z>) smc_Par_Comp_vrange: "\<R>\<^sub>\<circ> (smc_Par \<alpha>\<lparr>Comp\<rparr>) \<subseteq>\<^sub>\<circ> set {T. arr_Par \<alpha> T}"
proof(rule vsubsetI)
  interpret digraph \<alpha> \<open>smc_dg (smc_Par \<alpha>)\<close>
    unfolding smc_dg_smc_Par by (simp add: digraph_dg_Par)
  fix R assume "R \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (smc_Par \<alpha>\<lparr>Comp\<rparr>)"
  then obtain ST 
    where R_def: "R = smc_Par \<alpha>\<lparr>Comp\<rparr>\<lparr>ST\<rparr>"
      and "ST \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_Par \<alpha>\<lparr>Comp\<rparr>)"
    unfolding smc_Par_components by (blast dest: rel_VLambda.vrange_atD)
  then obtain S T A B C 
    where "ST = [S, T]\<^sub>\<circ>" 
      and S: "S : B \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> C" 
      and T: "T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B"
    by (auto simp: smc_Par_Comp_vdomain)
  with R_def have R_def': "R = S \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> T" by simp
  note S_D = dg_is_arrD(1)[unfolded slicing_simps, OF S]
    and T_D = dg_is_arrD(1)[unfolded slicing_simps, OF T]
  from S_D T_D have "arr_Par \<alpha> S" "arr_Par \<alpha> T" 
    by (simp_all add: smc_Par_components)
  from this show "R \<in>\<^sub>\<circ> set {T. arr_Par \<alpha> T}" 
    unfolding R_def' smc_Par_Comp_app[OF S T] by (auto simp: arr_Par_comp_Par)
qed


subsubsection\<open>\<open>Par\<close> is a semicategory\<close>

lemma (in \<Z>) semicategory_smc_Par: "semicategory \<alpha> (smc_Par \<alpha>)"
proof(intro semicategoryI, unfold smc_dg_smc_Par)
  show "vfsequence (smc_Par \<alpha>)" unfolding smc_Par_def by simp
  show "vcard (smc_Par \<alpha>) = 5\<^sub>\<nat>"
    unfolding smc_Par_def by (simp add: nat_omega_simps)
  show "(GF \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_Par \<alpha>\<lparr>Comp\<rparr>)) \<longleftrightarrow>
    (\<exists>G F B C A. GF = [G, F]\<^sub>\<circ> \<and> G : B \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> C \<and> F : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B)"
    for GF
    unfolding smc_Par_Comp_vdomain by (auto intro: composable_arrsI)
  show [intro]: "G \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> F : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> C"
    if "G : B \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> C" and "F : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B" for G B C F A
  proof-
    from that have "arr_Par \<alpha> G" "arr_Par \<alpha> F" by (auto elim: smc_Par_is_arrE)
    with that show ?thesis
      by 
        (
          cs_concl 
            cs_simp: smc_cs_simps smc_Par_cs_simps 
            cs_intro: smc_Par_cs_intros
        )
  qed 
  show "H \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> G \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> F = H \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> (G \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> F)"
    if "H : C \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> D" 
      and "G : B \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> C"
      and "F : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B"
    for H C D G B F A
  proof-
    from that have "arr_Par \<alpha> H" "arr_Par \<alpha> G" "arr_Par \<alpha> F" 
      by (auto simp: smc_Par_is_arrD)
    with that show ?thesis
      by 
        (
          cs_concl 
            cs_simp: smc_cs_simps smc_Par_cs_simps 
            cs_intro: smc_Par_cs_intros
        )
  qed
qed (auto simp: digraph_dg_Par smc_Par_components)


subsubsection\<open>\<open>Par\<close> is a wide subsemicategory of \<open>Rel\<close>\<close>

lemma (in \<Z>) wide_subsemicategory_smc_Par_smc_Rel: 
  "smc_Par \<alpha> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> smc_Rel \<alpha>"
proof-
  interpret Rel: semicategory \<alpha> \<open>smc_Rel \<alpha>\<close> by (rule semicategory_smc_Rel)
  interpret Par: semicategory \<alpha> \<open>smc_Par \<alpha>\<close> by (rule semicategory_smc_Par)
  show ?thesis
  proof
    (
      intro wide_subsemicategoryI subsemicategoryI,
      unfold smc_dg_smc_Par smc_dg_smc_Rel
    )
    from wide_subdigraph_dg_Par_dg_Rel show wsd:
      "dg_Par \<alpha> \<subseteq>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> dg_Rel \<alpha>" "dg_Par \<alpha> \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> dg_Rel \<alpha>"
      by auto
    interpret wide_subdigraph \<alpha> \<open>dg_Par \<alpha>\<close> \<open>dg_Rel \<alpha>\<close> by (rule wsd(2))
    show "G \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> F = G \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> F"
      if "G : B \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> C" and "F : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B" for G B C F A
    proof-
      from that have "G : B \<mapsto>\<^bsub>dg_Par \<alpha>\<^esub> C" and "F : A \<mapsto>\<^bsub>dg_Par \<alpha>\<^esub> B" 
        by (cs_concl cs_simp: smc_dg_smc_Par[symmetric] cs_intro: slicing_intros)+
      then have "G : B \<mapsto>\<^bsub>dg_Rel \<alpha>\<^esub> C" and "F : A \<mapsto>\<^bsub>dg_Rel \<alpha>\<^esub> B" 
        by (cs_concl cs_intro: dg_sub_fw_cs_intros)+
      then have "G : B \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> C" and "F : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B" 
        unfolding smc_dg_smc_Rel[symmetric] slicing_simps by simp_all
      from that this show "G \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> F = G \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> F"
        by (cs_concl cs_simp: smc_Par_cs_simps smc_Rel_cs_simps)
    qed
  qed (auto simp: smc_cs_intros)
qed



subsection\<open>Monic arrow and epic arrow\<close>

lemma (in \<Z>) smc_Par_is_monic_arrI[intro]:
  assumes "T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B" and "v11 (T\<lparr>ArrVal\<rparr>)" and "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A"
  shows "T : A \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>smc_Par \<alpha>\<^esub> B"
proof(intro is_monic_arrI)
  interpret Par_Rel: wide_subsemicategory \<alpha> \<open>smc_Par \<alpha>\<close> \<open>smc_Rel \<alpha>\<close>
    by (rule wide_subsemicategory_smc_Par_smc_Rel)
  interpret v11: v11 \<open>T\<lparr>ArrVal\<rparr>\<close> by (rule assms(2))
  show T: "T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B" by (rule assms(1))
  fix S R A'
  assume S: "S : A' \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> A" 
    and R: "R : A' \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> A"
    and TS_TR: "T \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> S = T \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> R"
  from assms(3) T Par_Rel.subsemicategory_axioms have "T : A \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>smc_Rel \<alpha>\<^esub> B"
    by (intro smc_Rel_is_monic_arrI)
      (auto dest: v11.v11_vimage_vpsubset_neq elim!: smc_sub_fw_cs_intros)
  moreover from S Par_Rel.subsemicategory_axioms have "S : A' \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> A"
    by (cs_concl cs_intro: smc_sub_fw_cs_intros)
  moreover from R Par_Rel.subsemicategory_axioms have "R : A' \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> A" 
    by (cs_concl cs_intro: smc_sub_fw_cs_intros)
  moreover from T S R TS_TR Par_Rel.subsemicategory_axioms have 
    "T \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> S = T \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> R" 
    by (auto simp: smc_sub_bw_cs_simps)
  ultimately show "S = R" by (rule is_monic_arrD(2))
qed

lemma (in \<Z>) smc_Par_is_monic_arrD:
  assumes "T : A \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>smc_Par \<alpha>\<^esub> B"
  shows "T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B" and "v11 (T\<lparr>ArrVal\<rparr>)" and "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A"
proof-

  from assms show T: "T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B" by auto
  interpret T: arr_Par \<alpha> T 
    rewrites [simp]: "T\<lparr>ArrDom\<rparr> = A" and [simp]: "T\<lparr>ArrCod\<rparr> = B"
    using T by (auto dest: smc_Par_is_arrD)

  show "v11 (T\<lparr>ArrVal\<rparr>)"
  proof(intro v11I)

    show "vsv ((T\<lparr>ArrVal\<rparr>)\<inverse>\<^sub>\<circ>)"
    proof(intro vsvI)

      fix a b c assume "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)\<inverse>\<^sub>\<circ>" and "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)\<inverse>\<^sub>\<circ>"

      then have bar: "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>" and car: "\<langle>c, a\<rangle> \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>" by auto
      with T.arr_Rel_ArrVal_vdomain have [intro]: "b \<in>\<^sub>\<circ> A" "c \<in>\<^sub>\<circ> A" by auto

      define R where "R = [set {\<langle>0, b\<rangle>}, set {0}, A]\<^sub>\<circ>"
      define S where "S = [set {\<langle>0, c\<rangle>}, set {0}, A]\<^sub>\<circ>"

      have R_components: 
        "R\<lparr>ArrVal\<rparr> = set {\<langle>0, b\<rangle>}" "R\<lparr>ArrDom\<rparr> = set {0}" "R\<lparr>ArrCod\<rparr> = A"
        unfolding R_def by (simp_all add: arr_Rel_components)

      have S_components: 
        "S\<lparr>ArrVal\<rparr> = set {\<langle>0, c\<rangle>}" "S\<lparr>ArrDom\<rparr> = set {0}" "S\<lparr>ArrCod\<rparr> = A"
        unfolding S_def by (simp_all add: arr_Rel_components)

      have R: "R : set {0} \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> A"
      proof(rule smc_Par_is_arrI)
        show "arr_Par \<alpha> R"
          unfolding R_def
          by (rule arr_Par_vfsequenceI) (auto simp: T.arr_Rel_ArrDom_in_Vset)
      qed (simp_all add: R_components)

      have S: "S : set {0} \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> A"
      proof(rule smc_Par_is_arrI)
        show "arr_Par \<alpha> S"
          unfolding S_def
          by (rule arr_Par_vfsequenceI) (auto simp: T.arr_Rel_ArrDom_in_Vset)
      qed (simp_all add: S_components)

      have "T \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> R = [set {\<langle>0, a\<rangle>}, set {0}, B]\<^sub>\<circ>"
        unfolding smc_Par_Comp_app[OF T R]
      proof
        (
          rule arr_Par_eqI[of \<alpha>],
          unfold comp_Rel_components arr_Rel_components R_components
        )
        from R T show "arr_Par \<alpha> (T \<circ>\<^sub>R\<^sub>e\<^sub>l R)"
          by (intro arr_Par_comp_Par) (auto elim!: smc_Par_is_arrE)
        show "arr_Par \<alpha> [set {\<langle>0, a\<rangle>}, set {0}, B]\<^sub>\<circ>"
        proof(rule arr_Par_vfsequenceI)
          from T.arr_Rel_ArrVal_vrange bar show "\<R>\<^sub>\<circ> (set {\<langle>0, a\<rangle>}) \<subseteq>\<^sub>\<circ> B" by auto
        qed (auto simp: T.arr_Rel_ArrCod_in_Vset Axiom_of_Powers)
        show "T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> set {\<langle>0, b\<rangle>} = set {\<langle>0, a\<rangle>}"
        proof(rule vsv_eqI, unfold vdomain_vsingleton)
          from bar show "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> set {\<langle>0, b\<rangle>}) = set {0}" by auto
          with bar show 
            "a' \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> set {\<langle>0, b\<rangle>}) \<Longrightarrow>
              (T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> set {\<langle>0, b\<rangle>})\<lparr>a'\<rparr> = set {\<langle>0, a\<rangle>}\<lparr>a'\<rparr>"
            for a'
            by auto
        qed (auto intro: vsv_vcomp)
      qed simp_all

      moreover have "T \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> S = [set {\<langle>0, a\<rangle>}, set {0}, B]\<^sub>\<circ>" 
        unfolding smc_Par_Comp_app[OF T S]
      proof
        (
          rule arr_Par_eqI[of \<alpha>],
          unfold comp_Rel_components arr_Rel_components S_components
        )
        from T S show "arr_Par \<alpha> (T \<circ>\<^sub>R\<^sub>e\<^sub>l S)"
          by (intro arr_Par_comp_Par) (auto elim!: smc_Par_is_arrE)
        show "arr_Par \<alpha> [set {\<langle>0, a\<rangle>}, set {0}, B]\<^sub>\<circ>"
        proof(rule arr_Par_vfsequenceI)
          from T.arr_Rel_ArrVal_vrange bar show "\<R>\<^sub>\<circ> (set {\<langle>0, a\<rangle>}) \<subseteq>\<^sub>\<circ> B" by auto
        qed (auto simp: T.arr_Rel_ArrCod_in_Vset Axiom_of_Powers)
        show "T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> set {\<langle>0, c\<rangle>} = set {\<langle>0, a\<rangle>}"
        proof(rule vsv_eqI, unfold vdomain_vsingleton)
          from car show "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> set {\<langle>0, c\<rangle>}) = set {0}" by auto
          with car show "a' \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> set {\<langle>0, c\<rangle>}) \<Longrightarrow> 
            (T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> set {\<langle>0, c\<rangle>})\<lparr>a'\<rparr> = set {\<langle>0, a\<rangle>}\<lparr>a'\<rparr>"
            for a'
            by auto
        qed (auto intro: vsv_vcomp)
      qed simp_all
      ultimately have "T \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> R = T \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> S" by simp
      from assms R S this have "R = S" by blast
      with R_components(1) S_components(1) show "b = c" by simp
    qed auto

  qed auto

  show "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A"
  proof(intro vsubset_antisym vsubsetI)
    from T.arr_Rel_ArrVal_vdomain show "x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) \<Longrightarrow> x \<in>\<^sub>\<circ> A" for x
      by auto
    fix a assume [simp]: "a \<in>\<^sub>\<circ> A" show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)"
    proof(rule ccontr)
      assume a: "a \<notin>\<^sub>\<circ> \<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)"
      define R where "R = [set {\<langle>0, a\<rangle>}, set {0, 1}, A]\<^sub>\<circ>"
      define S where "S = [set {\<langle>1, a\<rangle>}, set {0, 1}, A]\<^sub>\<circ>"
      have R: "R : set {0, 1} \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> A"
      proof(rule smc_Par_is_arrI)
        show "arr_Par \<alpha> R"
          unfolding R_def
        proof(rule arr_Par_vfsequenceI)
          from Axiom_of_Infinity vone_in_omega show "set {0, 1} \<in>\<^sub>\<circ> Vset \<alpha>" 
            by blast
        qed (auto simp: T.arr_Rel_ArrDom_in_Vset)
      qed (auto simp: R_def arr_Rel_components)
      have S: "S : set {0, 1} \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> A"
      proof(rule smc_Par_is_arrI)
        show "arr_Par \<alpha> S"
          unfolding S_def
        proof(rule arr_Par_vfsequenceI)
          from Axiom_of_Infinity vone_in_omega show "set {0, 1} \<in>\<^sub>\<circ> Vset \<alpha>" 
            by blast
        qed (auto simp: T.arr_Rel_ArrDom_in_Vset)
      qed (auto simp: S_def arr_Rel_components)
      with a have "T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> R\<lparr>ArrVal\<rparr> = 0" 
        unfolding R_def arr_Rel_components
        by (intro vsubset_antisym vsubsetI) auto
      moreover with a have "T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> S\<lparr>ArrVal\<rparr> = 0" 
        unfolding S_def arr_Rel_components
        by (intro vsubset_antisym vsubsetI) auto
      ultimately have "T \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> R = T \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> S" 
        using R T S
        by
          (
            intro arr_Par_eqI[of \<alpha> \<open>T \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> R\<close> \<open>T \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> S\<close>]; 
            elim smc_Par_is_arrE
          )
          (
            auto simp:
              dg_Par_cs_intros
              smc_Par_Comp_app[OF T R] 
              smc_Par_Comp_app[OF T S] 
              comp_Rel_components
          )
      from R S this assms have "R = S" by blast
      then show False unfolding R_def S_def by simp
    qed 
  qed

qed 

lemma (in \<Z>) smc_Par_is_monic_arr: 
  "T : A \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>smc_Par \<alpha>\<^esub> B \<longleftrightarrow>
    T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B \<and> v11 (T\<lparr>ArrVal\<rparr>) \<and> \<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A"
  by (intro iffI) (auto simp: smc_Par_is_monic_arrD smc_Par_is_monic_arrI)

context \<Z>
begin

context
begin

private lemma smc_Par_is_epic_arr_vsubset:
  assumes "T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B"
    and "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B"
    and "R : B \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> C" 
    and "S : B \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> C" 
    and "R \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> T = S \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> T" 
  shows "R\<lparr>ArrVal\<rparr> \<subseteq>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>"
proof
  interpret T: arr_Par \<alpha> T
    rewrites [simp]: "T\<lparr>ArrDom\<rparr> = A" and [simp]: "T\<lparr>ArrCod\<rparr> = B"
    using assms smc_Par_is_arrD by auto
  interpret R: arr_Par \<alpha> R 
    rewrites [simp]: "R\<lparr>ArrDom\<rparr> = B" and [simp]: "R\<lparr>ArrCod\<rparr> = C"
    using assms smc_Par_is_arrD by auto
  from assms(5) have "(R \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> T)\<lparr>ArrVal\<rparr> = (S \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> T)\<lparr>ArrVal\<rparr>"
    by simp
  then have eq: "R\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> T\<lparr>ArrVal\<rparr> = S\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>" 
    unfolding 
      smc_Par_Comp_app[OF assms(3,1)] 
      smc_Par_Comp_app[OF assms(4,1)]
      comp_Rel_components
    by simp
  fix bc assume prems: "bc \<in>\<^sub>\<circ> R\<lparr>ArrVal\<rparr>"
  moreover with R.ArrVal.vbrelation obtain b c where bc_def: "bc = \<langle>b, c\<rangle>" by auto
  ultimately have [simp]: "b \<in>\<^sub>\<circ> B" and "c \<in>\<^sub>\<circ> C"
    using R.arr_Rel_ArrVal_vdomain R.arr_Rel_ArrVal_vrange by auto
  note [intro] = prems[unfolded bc_def]
  have "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)" by (simp add: assms(2))
  then obtain a where ab: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>" by auto
  then have "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> S\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>" unfolding eq[symmetric] by auto
  then obtain b' where ab': "\<langle>b', c\<rangle> \<in>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>" and "\<langle>a, b'\<rangle> \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>" 
    by clarsimp
  with ab ab' T.vsv T.ArrVal.vsv show "bc \<in>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>" unfolding bc_def by blast
qed

lemma smc_Par_is_epic_arrI:
  assumes "T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B" and "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B"
  shows "T : A \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>smc_Par \<alpha>\<^esub> B"
  unfolding is_epic_arr_def
proof
  (
    intro is_monic_arrI[
      of \<open>op_smc (smc_Par \<alpha>)\<close>, unfolded smc_op_simps, OF assms(1)
      ]
  )

  interpret semicategory \<alpha> \<open>smc_Par \<alpha>\<close> by (rule semicategory_smc_Par)

  fix R S a 
  assume prems: 
    "R : B \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> a" 
    "S : B \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> a" 
    "T \<circ>\<^sub>A\<^bsub>op_smc (smc_Par \<alpha>)\<^esub> R = T \<circ>\<^sub>A\<^bsub>op_smc (smc_Par \<alpha>)\<^esub> S"

  from prems(3) have RT_ST: "R \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> T = S \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> T"
    unfolding 
      op_smc_Comp[OF prems(1) assms(1)]
      op_smc_Comp[OF prems(2) assms(1)]
    by simp
  from smc_Par_is_epic_arr_vsubset[OF assms(1,2) prems(1,2) this] 
  have RS: "R\<lparr>ArrVal\<rparr> \<subseteq>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>".

  from smc_Par_is_epic_arr_vsubset[OF assms(1,2) prems(2,1) RT_ST[symmetric]]
  have SR: "S\<lparr>ArrVal\<rparr> \<subseteq>\<^sub>\<circ> R\<lparr>ArrVal\<rparr>".
  
  from prems show "R = S"    
    by (intro arr_Par_eqI[of \<alpha> R S])
      (auto simp: RS SR vsubset_antisym elim!: smc_Par_is_arrE)

qed

lemma smc_Par_is_epic_arrD:
  assumes "T : A \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>smc_Par \<alpha>\<^esub> B"
  shows "T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B" and "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B"
proof-

  interpret semicategory \<alpha> \<open>smc_Par \<alpha>\<close> by (rule semicategory_smc_Par)

  from assms show T: "T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B" 
    unfolding is_epic_arr_def by (auto simp: op_smc_is_arr)

  interpret T: arr_Par \<alpha> T
    rewrites [simp]: "T\<lparr>ArrDom\<rparr> = A" and [simp]: "T\<lparr>ArrCod\<rparr> = B"
    using T by (auto elim: smc_Par_is_arrE)

  show "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B"
  proof(intro vsubset_antisym vsubsetI)
    from T.arr_Rel_ArrVal_vrange show "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) \<Longrightarrow> y \<in>\<^sub>\<circ> B" for y
      by auto
    fix b assume [intro]: "b \<in>\<^sub>\<circ> B" show "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)"
    proof(rule ccontr)
      assume prems: "b \<notin>\<^sub>\<circ> \<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)"
      define R where "R = [set {\<langle>b, 0\<rangle>}, B, set {0, 1}]\<^sub>\<circ>"
      define S where "S = [set {\<langle>b, 1\<rangle>}, B, set {0, 1}]\<^sub>\<circ>"
      have R: "R : B \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> set {0, 1}" 
        unfolding R_def
      proof(intro smc_Par_is_arrI arr_Par_vfsequenceI, unfold arr_Rel_components)
        from Axiom_of_Infinity vone_in_omega show "set {0, 1} \<in>\<^sub>\<circ> Vset \<alpha>" 
          by blast
      qed (auto simp: T.arr_Rel_ArrCod_in_Vset)
      have S: "S : B \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> set {0, 1}"
        unfolding S_def
      proof(intro smc_Par_is_arrI arr_Par_vfsequenceI, unfold arr_Rel_components)
        from Axiom_of_Infinity vone_in_omega show "set {0, 1} \<in>\<^sub>\<circ> Vset \<alpha>" 
          by blast
      qed (auto simp: T.arr_Rel_ArrCod_in_Vset)
      from prems have "R\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> T\<lparr>ArrVal\<rparr> = 0"
        unfolding R_def arr_Rel_components
        by (auto intro!: vsubset_antisym vsubsetI)
      moreover from prems have "S\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> T\<lparr>ArrVal\<rparr> = 0" 
        unfolding S_def arr_Rel_components
        by (auto intro!: vsubset_antisym vsubsetI)
      ultimately have "R \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> T = S \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> T" 
        unfolding smc_Par_Comp_app[OF R T] smc_Par_Comp_app[OF S T]
        by (simp add: R_def S_def arr_Rel_components comp_Rel_def)
      from is_epic_arrD(2)[OF assms R S this] show False 
        unfolding R_def S_def by simp
    qed
  qed

qed

end

end

lemma (in \<Z>) smc_Par_is_epic_arr: 
  "T : A \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>smc_Par \<alpha>\<^esub> B \<longleftrightarrow> T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B \<and> \<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B" 
  by (intro iffI) (simp_all add: smc_Par_is_epic_arrD smc_Par_is_epic_arrI)



subsection\<open>Terminal object, initial object and null object\<close>

lemma (in \<Z>) smc_Par_obj_terminal: "obj_terminal (smc_Par \<alpha>) A \<longleftrightarrow> A = 0"
proof-

  interpret semicategory \<alpha> \<open>smc_Par \<alpha>\<close> by (rule semicategory_smc_Par)

  have "(\<forall>A\<in>\<^sub>\<circ>Vset \<alpha>. \<exists>!T. T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B) \<longleftrightarrow> B = 0" for B
  proof(intro iffI allI ballI)

    assume prems[rule_format]: "\<forall>A\<in>\<^sub>\<circ>Vset \<alpha>. \<exists>!T. T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B" 
    
    then obtain T where "T : 0 \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B" by (meson vempty_is_zet)
    then have [simp]: "B \<in>\<^sub>\<circ> Vset \<alpha>" by (fastforce simp: smc_Par_components(1))
    
    show "B = 0"
    proof(rule ccontr)
      assume "B \<noteq> 0"
      then obtain b where "b \<in>\<^sub>\<circ> B" using trad_foundation by auto
      have "[set {\<langle>0, b\<rangle>}, set {0}, B]\<^sub>\<circ> : set {0} \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B"
        by (intro smc_Par_is_arrI arr_Par_vfsequenceI, unfold arr_Rel_components)
          (auto simp: \<open>b \<in>\<^sub>\<circ> B\<close> vsubset_vsingleton_leftI)
      moreover have "[0, set {0}, B]\<^sub>\<circ> : set {0} \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B"
        by (intro smc_Par_is_arrI arr_Par_vfsequenceI, unfold arr_Rel_components)
          (auto simp: \<open>b \<in>\<^sub>\<circ> B\<close> vsubset_vsingleton_leftI)
      moreover have "[set {\<langle>0, b\<rangle>}, set {0}, B]\<^sub>\<circ> \<noteq> [0, set {0}, B]\<^sub>\<circ>" by simp
      ultimately show False
        by (metis prems smc_is_arrE smc_Par_components(1))
    qed

  next

    fix A assume [simp]: "B = 0" "A \<in>\<^sub>\<circ> Vset \<alpha>"
    show "\<exists>!T. T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B"
    proof(intro ex1I [of _ \<open>[0, A, 0]\<^sub>\<circ>\<close>])
      show zAz: "[0, A, 0]\<^sub>\<circ> : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B"
        by 
          ( 
            intro smc_Par_is_arrI arr_Par_vfsequenceI, 
            unfold arr_Rel_components
          ) 
          simp_all
      show "T = [0, A, 0]\<^sub>\<circ>" if "T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B" for T
      proof(rule arr_Par_eqI[of \<alpha>], unfold arr_Rel_components)
        interpret arr_Par \<alpha> T using that by (simp add: smc_Par_is_arrD(1))
        from zAz show "arr_Par \<alpha> [0, A, 0]\<^sub>\<circ>" by (auto elim: smc_Par_is_arrE)
        from arr_Par_axioms that show "T\<lparr>ArrVal\<rparr> = 0"
          by (clarsimp simp: vsv.vsv_vrange_vempty smc_Par_is_arrD(3))
      qed (use that in \<open>auto dest: smc_Par_is_arrD\<close>)
    qed

  qed

  then show ?thesis
    apply(intro iffI obj_terminalI)
    subgoal by (metis smc_is_arrD(2) obj_terminalE)
    subgoal by blast
    subgoal by (metis smc_Par_components(1))
    done

qed

lemma (in \<Z>) smc_Par_obj_initial: "obj_initial (smc_Par \<alpha>) A \<longleftrightarrow> A = 0"
proof-

  interpret Par: semicategory \<alpha> \<open>smc_Par \<alpha>\<close> by (rule semicategory_smc_Par)

  have "(\<forall>B\<in>\<^sub>\<circ>Vset \<alpha>. \<exists>!T. T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B) \<longleftrightarrow> (A = 0)" for A
  proof(intro iffI allI ballI)

    assume prems[rule_format]: "\<forall>B\<in>\<^sub>\<circ>Vset \<alpha>. \<exists>!T. T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B" 

    then obtain T where "T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> 0" 
      by (meson vempty_is_zet)
    then have [simp]: "A \<in>\<^sub>\<circ> Vset \<alpha>" by (fastforce simp: smc_Par_components(1))

    show "A = 0"
    proof(rule ccontr)
      assume "A \<noteq> 0"
      then obtain a where "a \<in>\<^sub>\<circ> A" using trad_foundation by auto
      have "[set {\<langle>a, 0\<rangle>}, A, set {0}]\<^sub>\<circ> : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> set {0}"
        by (intro smc_Par_is_arrI arr_Par_vfsequenceI, unfold arr_Rel_components)
          (auto simp: \<open>a \<in>\<^sub>\<circ> A\<close> vsubset_vsingleton_leftI)
      moreover have "[0, A, set {0}]\<^sub>\<circ> : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> set {0}"
        by (intro smc_Par_is_arrI arr_Par_vfsequenceI, unfold arr_Rel_components)
          (auto simp: \<open>a \<in>\<^sub>\<circ> A\<close> vsubset_vsingleton_leftI)
      moreover have "[set {\<langle>a, 0\<rangle>}, A, set {0}]\<^sub>\<circ> \<noteq> [0, A, set {0}]\<^sub>\<circ>" by simp
      ultimately show False 
        by (metis prems Par.smc_is_arrE smc_Par_components(1))
    qed

  next

    fix B assume prems[simp]: "A = 0" "B \<in>\<^sub>\<circ> Vset \<alpha>"

    show "\<exists>!T. T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B"
    proof(intro ex1I[of _ \<open>[0, 0, B]\<^sub>\<circ>\<close>])
      show zzB: "[0, 0, B]\<^sub>\<circ> : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B"
        by 
          ( 
            intro smc_Par_is_arrI arr_Par_vfsequenceI, 
            unfold arr_Rel_components
          ) 
          simp_all
      show "T = [0, 0, B]\<^sub>\<circ>" if "T : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B" for T
      proof(rule arr_Par_eqI[of \<alpha>], unfold arr_Rel_components)
        interpret arr_Par \<alpha> T using that by (simp add: smc_Par_is_arrD(1))
        show "arr_Par \<alpha> T" by (rule arr_Par_axioms)
        from zzB show "arr_Par \<alpha> [0, 0, B]\<^sub>\<circ>" by (auto elim: smc_Par_is_arrE)
        from arr_Par_axioms that show "T\<lparr>ArrVal\<rparr> = 0"
          by (elim smc_Par_is_arrE arr_ParE)
            (
              auto 
                intro: ArrVal.vsv_vrange_vempty 
                simp: ArrVal.vdomain_vrange_is_vempty
            )
      qed (use that in \<open>auto dest: smc_Par_is_arrD\<close>)
    qed
  qed

  then show ?thesis
    unfolding obj_initial_def
    apply(intro iffI obj_terminalI, elim obj_terminalE, unfold smc_op_simps)
    subgoal by (metis smc_Par_components(1))
    subgoal by (simp add: smc_Par_components(1))
    subgoal by (metis smc_Par_components(1))
    done

qed

lemma (in \<Z>) smc_Par_obj_terminal_obj_initial:
  "obj_initial (smc_Par \<alpha>) A \<longleftrightarrow> obj_terminal (smc_Par \<alpha>) A"
  unfolding smc_Par_obj_initial smc_Par_obj_terminal by simp

lemma (in \<Z>) smc_Par_obj_null: "obj_null (smc_Par \<alpha>) A \<longleftrightarrow> A = 0"
  unfolding obj_null_def smc_Par_obj_terminal smc_Par_obj_initial by simp



subsection\<open>Zero arrow\<close>

lemma (in \<Z>) smc_Par_is_zero_arr: 
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" and "B \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "T : A \<mapsto>\<^sub>0\<^bsub>smc_Par \<alpha>\<^esub> B \<longleftrightarrow> T = [0, A, B]\<^sub>\<circ>"
proof(intro HOL.ext iffI)
  interpret Par: semicategory \<alpha> \<open>smc_Par \<alpha>\<close> by (rule semicategory_smc_Par)
  fix T A B assume "T : A \<mapsto>\<^sub>0\<^bsub>smc_Par \<alpha>\<^esub> B"
  with smc_Par_is_arrD(1) obtain R S 
    where T_def: "T = R \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> S" 
      and S: "S : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> 0" 
      and R: "R : 0 \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B"
    by (auto simp: arr_Par_def \<Z>.smc_Par_obj_initial obj_null_def) 
  interpret S: arr_Par \<alpha> S
    rewrites [simp]: "S\<lparr>ArrDom\<rparr> = A" and [simp]: "S\<lparr>ArrCod\<rparr> = 0"
    using S smc_Par_is_arrD by auto
  interpret R: arr_Par \<alpha> R
    rewrites [simp]: "R\<lparr>ArrDom\<rparr> = 0" and [simp]: "R\<lparr>ArrCod\<rparr> = B"
    using R smc_Par_is_arrD by auto
  have S_def: "S = [0, A, 0]\<^sub>\<circ>"
    by 
      (
        rule arr_Rel_eqI[of \<alpha>], 
        unfold arr_Rel_components,
        insert S.arr_Rel_ArrVal_vrange S.ArrVal.vbrelation_vintersection_vrange
      )
      (
        auto simp: 
        S.arr_Rel_axioms 
        S.arr_Rel_ArrDom_in_Vset 
        arr_Rel_vfsequenceI vbrelationI
      )
  show "T = [0, A, B]\<^sub>\<circ>" 
     unfolding T_def smc_Par_Comp_app[OF R S] 
     by (rule arr_Rel_eqI[of \<alpha>], unfold comp_Rel_components)
       (
         auto simp: 
          \<Z>_axioms
          S_def
          R.arr_Rel_axioms 
          S.arr_Rel_axioms 
          arr_Rel_comp_Rel
          arr_Rel_components
          R.arr_Rel_ArrCod_in_Vset 
          S.arr_Rel_ArrDom_in_Vset 
          \<Z>.arr_Rel_vfsequenceI 
          vbrelation_vempty
       )
next
  fix T assume prems: "T = [0, A, B]\<^sub>\<circ>"
  let ?S = \<open>[0, A, 0]\<^sub>\<circ>\<close> and ?R = \<open>[0, 0, B]\<^sub>\<circ>\<close>
  have S: "arr_Par \<alpha> ?S" and R: "arr_Par \<alpha> ?R"  
    by (all\<open>intro arr_Par_vfsequenceI\<close>) (simp_all add: assms)
  have SA0: "?S : A \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> 0"
    by (intro smc_Par_is_arrI) (simp_all add: S arr_Rel_components)
  moreover have R0B: "?R : 0 \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> B"
    by (intro smc_Par_is_arrI) (simp_all add: R arr_Rel_components)
  moreover have "T = ?R \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> ?S" 
    unfolding smc_Par_Comp_app[OF R0B SA0]
  proof
    (
      rule arr_Par_eqI[of \<alpha>],
      unfold comp_Rel_components arr_Rel_components prems
    )
    show "arr_Par \<alpha> [0, A, B]\<^sub>\<circ>"
      unfolding prems by (intro arr_Par_vfsequenceI) (auto simp: assms)
  qed (use R S in \<open>auto simp: smc_Par_cs_intros\<close>)
  ultimately show "T : A \<mapsto>\<^sub>0\<^bsub>smc_Par \<alpha>\<^esub> B" 
    by (simp add: is_zero_arrI smc_Par_obj_null)
qed

text\<open>\newpage\<close>

end