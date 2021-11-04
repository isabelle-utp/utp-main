(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>Set\<close> as a semicategory\<close>
theory CZH_SMC_Set
  imports 
    CZH_DG_Set
    CZH_SMC_Par
    CZH_SMC_Subsemicategory
begin



subsection\<open>Background\<close>


text\<open>
The methodology chosen for the exposition 
of \<open>Set\<close> as a semicategory is analogous to the 
one used in the previous chapter for the exposition of \<open>Set\<close> as a digraph. 
\<close>

named_theorems smc_Set_cs_simps
named_theorems smc_Set_cs_intros

lemmas (in arr_Set) [smc_Set_cs_simps] = 
  dg_Rel_shared_cs_simps

lemmas [smc_Set_cs_simps] =
  dg_Rel_shared_cs_simps
  arr_Set.arr_Set_ArrVal_vdomain
  arr_Set_comp_Set_id_Set_left
  arr_Set_comp_Set_id_Set_right

lemmas [smc_Set_cs_intros] = 
  dg_Rel_shared_cs_intros
  arr_Set_comp_Set



subsection\<open>\<open>Set\<close> as a semicategory\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition smc_Set :: "V \<Rightarrow> V"
  where "smc_Set \<alpha> =
    [
      Vset \<alpha>,
      set {T. arr_Set \<alpha> T},
      (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Set \<alpha> T}. T\<lparr>ArrDom\<rparr>),
      (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Set \<alpha> T}. T\<lparr>ArrCod\<rparr>),
      (\<lambda>ST\<in>\<^sub>\<circ>composable_arrs (dg_Set \<alpha>). ST\<lparr>0\<rparr> \<circ>\<^sub>R\<^sub>e\<^sub>l ST\<lparr>1\<^sub>\<nat>\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smc_Set_components:
  shows "smc_Set \<alpha>\<lparr>Obj\<rparr> = Vset \<alpha>"
    and "smc_Set \<alpha>\<lparr>Arr\<rparr> = set {T. arr_Set \<alpha> T}"
    and "smc_Set \<alpha>\<lparr>Dom\<rparr> = (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Set \<alpha> T}. T\<lparr>ArrDom\<rparr>)"
    and "smc_Set \<alpha>\<lparr>Cod\<rparr> = (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Set \<alpha> T}. T\<lparr>ArrCod\<rparr>)"
    and "smc_Set \<alpha>\<lparr>Comp\<rparr> = (\<lambda>ST\<in>\<^sub>\<circ>composable_arrs (dg_Set \<alpha>). ST\<lparr>0\<rparr> \<circ>\<^sub>R\<^sub>e\<^sub>l ST\<lparr>1\<^sub>\<nat>\<rparr>)"
  unfolding smc_Set_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smc_dg_smc_Set: "smc_dg (smc_Set \<alpha>) = dg_Set \<alpha>"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> (smc_dg (smc_Set \<alpha>)) = 4\<^sub>\<nat>" 
    unfolding smc_dg_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (dg_Set \<alpha>) = 4\<^sub>\<nat>"
    unfolding dg_Set_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (smc_dg (smc_Set \<alpha>)) = \<D>\<^sub>\<circ> (dg_Set \<alpha>)"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_dg (smc_Set \<alpha>)) \<Longrightarrow> smc_dg (smc_Set \<alpha>)\<lparr>a\<rparr> = dg_Set \<alpha>\<lparr>a\<rparr>"
    for a
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral,
        unfold smc_dg_def dg_field_simps smc_Set_def dg_Set_def
      )
      (auto simp: nat_omega_simps)
qed (auto simp: smc_dg_def dg_Set_def)

lemmas_with [folded smc_dg_smc_Set, unfolded slicing_simps]: 
  smc_Set_Obj_iff = dg_Set_Obj_iff
  and smc_Set_Arr_iff[smc_Set_cs_simps] = dg_Set_Arr_iff
  and smc_Set_Dom_vsv[smc_Set_cs_intros] = dg_Set_Dom_vsv
  and smc_Set_Dom_vdomain[smc_Set_cs_simps] = dg_Set_Dom_vdomain
  and smc_Set_Dom_vrange = dg_Set_Dom_vrange
  and smc_Set_Dom_app[smc_Set_cs_simps] = dg_Set_Dom_app
  and smc_Set_Cod_vsv[smc_Set_cs_intros] = dg_Set_Cod_vsv
  and smc_Set_Cod_vdomain[smc_Set_cs_simps] = dg_Set_Cod_vdomain
  and smc_Set_Cod_vrange = dg_Set_Cod_vrange
  and smc_Set_Cod_app[smc_Set_cs_simps] = dg_Set_Cod_app
  and smc_Set_is_arrI = dg_Set_is_arrI
  and smc_Set_is_arrD = dg_Set_is_arrD
  and smc_Set_is_arrE = dg_Set_is_arrE
  and smc_Set_ArrVal_vdomain[smc_Set_cs_simps] = dg_Set_ArrVal_vdomain
  and smc_Set_ArrVal_app_vrange[smc_Set_cs_intros] = dg_Set_ArrVal_app_vrange

lemmas [smc_cs_simps] = smc_Set_is_arrD(2,3)

lemmas_with (in \<Z>) [folded smc_dg_smc_Set, unfolded slicing_simps]: 
  smc_Set_Hom_vifunion_in_Vset = dg_Set_Hom_vifunion_in_Vset
  and smc_Set_incl_Set_is_arr = dg_Set_incl_Set_is_arr
  and smc_Set_incl_Set_is_arr'[smc_Set_cs_intros] = dg_Set_incl_Set_is_arr'

lemmas [smc_Set_cs_intros] = 
  smc_Set_is_arrI
  \<Z>.smc_Set_incl_Set_is_arr'


subsubsection\<open>Composable arrows\<close>

lemma smc_Set_composable_arrs_dg_Set: 
  "composable_arrs (dg_Set \<alpha>) = composable_arrs (smc_Set \<alpha>)"
  unfolding composable_arrs_def smc_dg_smc_Set[symmetric] slicing_simps by simp

lemma smc_Set_Comp: 
  "smc_Set \<alpha>\<lparr>Comp\<rparr> =
    VLambda (composable_arrs (smc_Set \<alpha>)) (\<lambda>ST. ST\<lparr>0\<rparr> \<circ>\<^sub>R\<^sub>e\<^sub>l ST\<lparr>1\<^sub>\<nat>\<rparr>)"
  unfolding smc_Set_components smc_Set_composable_arrs_dg_Set ..


subsubsection\<open>Composition\<close>

lemma smc_Set_Comp_app[smc_Set_cs_simps]:
  assumes "S : b \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> c" and "T : a \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> b"
  shows "S \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> T = S \<circ>\<^sub>R\<^sub>e\<^sub>l T"
proof-
  from assms have "[S, T]\<^sub>\<circ> \<in>\<^sub>\<circ> composable_arrs (smc_Set \<alpha>)" 
    by (auto simp: smc_cs_intros)
  then show "S \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> T = S \<circ>\<^sub>R\<^sub>e\<^sub>l T"
    unfolding smc_Set_Comp by (simp add: nat_omega_simps)
qed 

lemma smc_Set_Comp_vdomain: "\<D>\<^sub>\<circ> (smc_Set \<alpha>\<lparr>Comp\<rparr>) = composable_arrs (smc_Set \<alpha>)" 
  unfolding smc_Set_Comp by simp

lemma (in \<Z>) smc_Set_Comp_vrange: 
  "\<R>\<^sub>\<circ> (smc_Set \<alpha>\<lparr>Comp\<rparr>) \<subseteq>\<^sub>\<circ> set {T. arr_Set \<alpha> T}"
proof(rule vsubsetI)
  interpret digraph \<alpha> \<open>smc_dg (smc_Set \<alpha>)\<close>
    unfolding smc_dg_smc_Set by (simp add: digraph_dg_Set)
  fix R assume "R \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (smc_Set \<alpha>\<lparr>Comp\<rparr>)"
  then obtain ST 
    where R_def: "R = smc_Set \<alpha>\<lparr>Comp\<rparr>\<lparr>ST\<rparr>"
      and "ST \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_Set \<alpha>\<lparr>Comp\<rparr>)"
    unfolding smc_Set_components by (blast dest: rel_VLambda.vrange_atD) 
  then obtain S T a b c 
    where "ST = [S, T]\<^sub>\<circ>" 
      and S: "S : b \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> c" 
      and T: "T : a \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> b"
    by (auto simp: smc_Set_Comp_vdomain)
  with R_def have R_def': "R = S \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> T" by simp
  interpret S: arr_Set \<alpha> S + T: arr_Set \<alpha> T 
    rewrites [simp]: "S\<lparr>ArrDom\<rparr> = b" 
      and [simp]: "S\<lparr>ArrCod\<rparr> = c"
      and [simp]: "T\<lparr>ArrDom\<rparr> = a"
      and [simp]: "T\<lparr>ArrCod\<rparr> = b"
    using S T by (auto elim!: smc_Set_is_arrD)
  have "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> (S\<lparr>ArrVal\<rparr>)"
  proof(intro vsubsetI)
    fix y assume prems: "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)"
    with T.ArrVal.vrange_atD obtain x 
      where y_def: "y = T\<lparr>ArrVal\<rparr>\<lparr>x\<rparr>" and x: "x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)"
      by metis
    from prems x T.arr_Set_ArrVal_vrange show "y \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (S\<lparr>ArrVal\<rparr>)"
      unfolding y_def by (auto simp: smc_Set_cs_simps)
  qed
  with S.arr_Set_axioms T.arr_Set_axioms have "arr_Set \<alpha> (S \<circ>\<^sub>R\<^sub>e\<^sub>l T)"
    by (simp add: arr_Set_comp_Set)
  from this show "R \<in>\<^sub>\<circ> set {T. arr_Set \<alpha> T}" 
    unfolding R_def' smc_Set_Comp_app[OF S T] by simp
qed

lemma smc_Set_composable_vrange_vdomain[smc_Set_cs_intros]:
  assumes "g : b \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> c" and "f : a \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> b"
  shows "\<R>\<^sub>\<circ> (f\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> (g\<lparr>ArrVal\<rparr>)"
proof(intro vsubsetI)
  from assms have g: "arr_Set \<alpha> g" and f: "arr_Set \<alpha> f" 
    by (auto simp: smc_Set_is_arrD)
  fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (f\<lparr>ArrVal\<rparr>)"
  with assms f have "y \<in>\<^sub>\<circ> b" by (force simp: smc_Set_is_arrD(3))
  with assms g show "y \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (g\<lparr>ArrVal\<rparr>)" 
    by (simp add: smc_Set_is_arrD(2) arr_SetD(5))
qed

lemma smc_Set_Comp_ArrVal[smc_cs_simps]:
  assumes "S : y \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> z" and "T : x \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> y" and "a \<in>\<^sub>\<circ> x"
  shows "(S \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> T)\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> = S\<lparr>ArrVal\<rparr>\<lparr>T\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>\<rparr>"
proof-
  interpret S: arr_Set \<alpha> S + T: arr_Set \<alpha> T
    using assms by (auto simp: smc_Set_is_arrD)
  have Ta: "T\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> y"
  proof-
    from assms have "a \<in>\<^sub>\<circ> T\<lparr>ArrDom\<rparr>" by (auto simp: smc_Set_is_arrD)
    with assms T.arr_Set_ArrVal_vrange show ?thesis
      by 
        (
          simp add: 
            T.ArrVal.vsv_vimageI2 vsubset_iff smc_Set_is_arrD smc_Set_cs_simps
        )
  qed
  from Ta assms S.arr_Set_axioms T.arr_Set_axioms show ?thesis
    by ((cs_concl_step smc_Set_cs_simps)+, intro arr_Set_comp_Set_ArrVal[of \<alpha>])
      (simp_all add: smc_Set_is_arrD smc_Set_cs_simps)
qed


subsubsection\<open>\<open>Set\<close> is a semicategory\<close>

lemma (in \<Z>) semicategory_smc_Set: "semicategory \<alpha> (smc_Set \<alpha>)"
proof(rule semicategoryI, unfold smc_dg_smc_Set)

  interpret wide_subdigraph \<alpha> \<open>dg_Set \<alpha>\<close> \<open>dg_Par \<alpha>\<close> 
    by (rule wide_subdigraph_dg_Set_dg_Par)
  interpret smc_Par: semicategory \<alpha> \<open>smc_Par \<alpha>\<close> by (rule semicategory_smc_Par)

  show "vfsequence (smc_Set \<alpha>)" unfolding smc_Set_def by simp
  show "vcard (smc_Set \<alpha>) = 5\<^sub>\<nat>"
    unfolding smc_Set_def by (simp add: nat_omega_simps)

  show "(gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_Set \<alpha>\<lparr>Comp\<rparr>)) \<longleftrightarrow> 
    (\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> c \<and> f : a \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> b)"
    for gf
    unfolding smc_Set_Comp_vdomain by (auto intro: composable_arrsI)

  show [intro]: "g \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> f : a \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> c"
    if "g : b \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> c" "f : a \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> b" for g b c f a
  proof-
    from that have g: "arr_Set \<alpha> g" and f: "arr_Set \<alpha> f" 
      by (auto simp: smc_Set_is_arrD)
    with that show ?thesis
      by 
        (
          cs_concl 
            cs_simp: smc_cs_simps smc_Set_cs_simps 
            cs_intro: smc_Set_cs_intros
        )
  qed
    
  show "h \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> g \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> f = h \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> (g \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> f)"
    if "h : c \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> d" 
      and "g : b \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> c"
      and "f : a \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> b"
    for h c d g b f a
  proof-
    from that have "arr_Set \<alpha> h" "arr_Set \<alpha> g" "arr_Set \<alpha> f" 
      by (auto simp: smc_Set_is_arrD)
    with that show ?thesis
      by 
        (
          cs_concl 
            cs_simp: smc_cs_simps smc_Set_cs_simps 
            cs_intro: smc_Set_cs_intros
        )      
  qed

qed (auto simp: digraph_dg_Set smc_Set_components)


subsubsection\<open>\<open>Set\<close> is a wide subsemicategory of \<open>Par\<close>\<close>

lemma (in \<Z>) wide_subsemicategory_smc_Set_smc_Par: 
  "smc_Set \<alpha> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> smc_Par \<alpha>"
proof-
  interpret Par: semicategory \<alpha> \<open>smc_Par \<alpha>\<close> by (rule semicategory_smc_Par)
  interpret Set: semicategory \<alpha> \<open>smc_Set \<alpha>\<close> by (rule semicategory_smc_Set)
  show ?thesis
  proof
    (
      intro wide_subsemicategoryI subsemicategoryI, 
      unfold smc_dg_smc_Par smc_dg_smc_Set
    )
    from wide_subdigraph_dg_Set_dg_Par show wsd:  
      "dg_Set \<alpha> \<subseteq>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> dg_Par \<alpha>" 
      "dg_Set \<alpha> \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> dg_Par \<alpha>"
      by auto
    interpret wide_subdigraph \<alpha> \<open>dg_Set \<alpha>\<close> \<open>dg_Par \<alpha>\<close> by (rule wsd(2))
    show "g \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> f = g \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> f"
      if "g : b \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> c" and "f : a \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> b" for g b c f a
    proof-
      from that have "g : b \<mapsto>\<^bsub>dg_Set \<alpha>\<^esub> c" and "f : a \<mapsto>\<^bsub>dg_Set \<alpha>\<^esub> b" 
        by (cs_concl cs_simp: smc_dg_smc_Set[symmetric] cs_intro: slicing_intros)+
      then have "g : b \<mapsto>\<^bsub>dg_Par \<alpha>\<^esub> c" and "f : a \<mapsto>\<^bsub>dg_Par \<alpha>\<^esub> b" 
        by (cs_concl cs_intro: dg_sub_fw_cs_intros)+
      then have "g : b \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> c" and "f : a \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> b" 
        unfolding smc_dg_smc_Par[symmetric] slicing_simps by simp_all
      from that this show "g \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> f = g \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> f"
        by (cs_concl cs_simp: smc_Set_cs_simps smc_Par_cs_simps)
    qed
  qed (auto simp: smc_cs_intros)
qed



subsection\<open>Monic arrow and epic arrow\<close>

lemma (in \<Z>) smc_Set_is_monic_arrI:
  \<comment>\<open>See Chapter I-5 in \cite{mac_lane_categories_2010}).\<close>
  assumes "T : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B" and "v11 (T\<lparr>ArrVal\<rparr>)" and "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A"
  shows "T : A \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>smc_Set \<alpha>\<^esub> B"
proof(rule is_monic_arrI)
  interpret wide_subsemicategory \<alpha> \<open>smc_Set \<alpha>\<close> \<open>smc_Par \<alpha>\<close>
    by (rule wide_subsemicategory_smc_Set_smc_Par)
  interpret v11 \<open>T\<lparr>ArrVal\<rparr>\<close> by (rule assms(2))
  show T: "T : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B" by (rule assms(1))
  fix S R A'
  assume S: "S : A' \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> A" 
    and R: "R : A' \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> A" 
    and TS_TR: "T \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> S = T \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> R"
  from assms(3) T have "T : A \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>smc_Par \<alpha>\<^esub> B" 
    by (intro smc_Par_is_monic_arrI) 
      (auto simp: v11_axioms dest: subsmc_is_arrD)
  moreover from S subsemicategory_axioms have "S : A' \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> A" 
    by (cs_concl cs_intro: smc_sub_fw_cs_intros)
  moreover from R subsemicategory_axioms have "R : A' \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> A" 
    by (cs_concl cs_intro: smc_sub_fw_cs_intros)
  moreover from T S R TS_TR subsemicategory_axioms have 
    "T \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> S = T \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> R" 
    by (auto simp: smc_sub_bw_cs_simps)
  ultimately show "S = R" by (rule is_monic_arrD(2))
qed

lemma (in \<Z>) smc_Set_is_monic_arrD:
  assumes "T : A \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>smc_Set \<alpha>\<^esub> B"
  shows "T : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B" and "v11 (T\<lparr>ArrVal\<rparr>)" and "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A"
proof-

  interpret wide_subdigraph \<alpha> \<open>dg_Set \<alpha>\<close> \<open>dg_Par \<alpha>\<close> 
    by (rule wide_subdigraph_dg_Set_dg_Par)
  interpret Par: semicategory \<alpha> \<open>smc_Par \<alpha>\<close> by (rule semicategory_smc_Par)

  from assms show T: "T : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B" by auto

  interpret T: arr_Set \<alpha> T 
    rewrites [simp]: "T\<lparr>ArrDom\<rparr> = A" and [simp]: "T\<lparr>ArrCod\<rparr> = B"
    using T by (auto elim!: smc_Set_is_arrE)
  
  show "v11 (T\<lparr>ArrVal\<rparr>)"
  proof(rule v11I)
  
    show "vsv ((T\<lparr>ArrVal\<rparr>)\<inverse>\<^sub>\<circ>)"
    proof(rule vsvI)

      fix a b c assume "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)\<inverse>\<^sub>\<circ>" and "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)\<inverse>\<^sub>\<circ>"

      then have bar: "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>" and car: "\<langle>c, a\<rangle> \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>"
        by auto
      with T.arr_Set_ArrVal_vdomain have [intro]: "b \<in>\<^sub>\<circ> A" "c \<in>\<^sub>\<circ> A" by blast+

      define R where "R = [set {\<langle>0, b\<rangle>}, set {0}, A]\<^sub>\<circ>"
      define S where "S = [set {\<langle>0, c\<rangle>}, set {0}, A]\<^sub>\<circ>"

      have R: "R : set {0} \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> A"
      proof(rule smc_Set_is_arrI)
        show "arr_Set \<alpha> R"
          unfolding R_def
          by (rule arr_Set_vfsequenceI) (auto simp: T.arr_Rel_ArrDom_in_Vset)
      qed (simp_all add: R_def arr_Rel_components)
      interpret R: arr_Set \<alpha> R 
        rewrites [simp]: "R\<lparr>ArrDom\<rparr> = set {0}" and [simp]: "R\<lparr>ArrCod\<rparr> = A"
        using R by (auto elim!: smc_Set_is_arrE)

      have S: "S : set {0} \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> A"
      proof(rule smc_Set_is_arrI)
        show "arr_Set \<alpha> S"
          unfolding S_def
          by (rule arr_Set_vfsequenceI) (auto simp: T.arr_Rel_ArrDom_in_Vset)
      qed (simp_all add: S_def arr_Rel_components)
      interpret S: arr_Set \<alpha> S 
        rewrites [simp]: "S\<lparr>ArrDom\<rparr> = set {0}" and [simp]: "S\<lparr>ArrCod\<rparr> = A"
        using S by (auto elim!: smc_Set_is_arrE)

      have "T \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> R = [set {\<langle>0, a\<rangle>}, set {0}, B]\<^sub>\<circ>"        
        unfolding smc_Set_Comp_app[OF T R]
      proof
        (
          rule arr_Set_eqI[of \<alpha>], 
          unfold comp_Rel_components arr_Rel_components
        )
        from R T show "arr_Set \<alpha> (T \<circ>\<^sub>R\<^sub>e\<^sub>l R)"
          by (intro arr_Set_comp_Set) 
            (auto elim!: smc_Set_is_arrE simp: smc_Set_cs_simps)
        show "arr_Set \<alpha> [set {\<langle>0, a\<rangle>}, set {0}, B]\<^sub>\<circ>"
        proof(rule arr_Set_vfsequenceI)
          from T.arr_Rel_ArrVal_vrange bar show "\<R>\<^sub>\<circ> (set {\<langle>0, a\<rangle>}) \<subseteq>\<^sub>\<circ> B" by auto
        qed (auto simp: T.arr_Rel_ArrCod_in_Vset Axiom_of_Powers)
        show "T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> R\<lparr>ArrVal\<rparr> = set {\<langle>0, a\<rangle>}"
          unfolding R_def arr_Rel_components
        proof(rule vsv_eqI, unfold vdomain_vsingleton)
          from bar show "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> set {\<langle>0, b\<rangle>}) = set {0}" by auto
          with bar show "a' \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> set {\<langle>0, b\<rangle>}) \<Longrightarrow> 
            (T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> set {\<langle>0, b\<rangle>})\<lparr>a'\<rparr> = set {\<langle>0, a\<rangle>}\<lparr>a'\<rparr>"
            for a'
            by auto
        qed (auto intro: vsv_vcomp)
      qed (simp_all add: R_def arr_Rel_components)
      moreover have "T \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> S = [set {\<langle>0, a\<rangle>}, set {0}, B]\<^sub>\<circ>" 
        unfolding smc_Set_Comp_app[OF T S]
      proof
        (
          rule arr_Set_eqI[of \<alpha>],
          unfold comp_Rel_components arr_Rel_components
        )
        from T S show "arr_Set \<alpha> (T \<circ>\<^sub>R\<^sub>e\<^sub>l S)"  
          by (intro arr_Set_comp_Set)
            (
              auto simp: 
                T.arr_Set_axioms 
                smc_Set_is_arrD 
                S.arr_Set_ArrVal_vrange 
                smc_Set_cs_simps
            )
        show "arr_Set \<alpha> [set {\<langle>0, a\<rangle>}, set {0}, B]\<^sub>\<circ>"
        proof(rule arr_Set_vfsequenceI)
          from T.arr_Rel_ArrVal_vrange bar show "\<R>\<^sub>\<circ> (set {\<langle>0, a\<rangle>}) \<subseteq>\<^sub>\<circ> B" by auto
        qed (auto simp: T.arr_Rel_ArrCod_in_Vset Axiom_of_Powers)
        show "T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> S\<lparr>ArrVal\<rparr> = set {\<langle>0, a\<rangle>}"
          unfolding S_def arr_Rel_components
        proof(rule vsv_eqI, unfold vdomain_vsingleton)
          from car show "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> set {\<langle>0, c\<rangle>}) = set {0}" by auto
          with car show "a' \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> set {\<langle>0, c\<rangle>}) \<Longrightarrow> 
            (T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> set {\<langle>0, c\<rangle>})\<lparr>a'\<rparr> = set {\<langle>0, a\<rangle>}\<lparr>a'\<rparr>"
            for a'
            by auto
        qed (auto intro: vsv_vcomp)
      qed (simp_all add: S_def arr_Rel_components)
      ultimately have "T \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> R = T \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> S" by simp
      from R S assms this have "R = S" by clarsimp
      then have "R\<lparr>ArrVal\<rparr> = S\<lparr>ArrVal\<rparr>" by simp
      then show "b = c" unfolding R_def S_def arr_Rel_components by simp
    qed clarsimp

  qed auto

  show "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A" by (simp add: smc_Set_cs_simps)

qed

lemma (in \<Z>) smc_Set_is_monic_arr: 
  "T : A \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>smc_Set \<alpha>\<^esub> B \<longleftrightarrow>  
    T : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B \<and> v11 (T\<lparr>ArrVal\<rparr>) \<and> \<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A"
  by (rule iffI) (auto simp: smc_Set_is_monic_arrD smc_Set_is_monic_arrI)


text\<open>
An epic arrow in \<open>Set\<close> is a total surjective function (see Chapter I-5 
in \cite{mac_lane_categories_2010}).
\<close>

lemma (in \<Z>) smc_Set_is_epic_arrI:
  assumes "T : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B" and "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B"
  shows "T : A \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>smc_Set \<alpha>\<^esub> B"
proof-
  interpret wide_subsemicategory \<alpha> \<open>smc_Set \<alpha>\<close> \<open>smc_Par \<alpha>\<close>
    by (rule wide_subsemicategory_smc_Set_smc_Par)
  have epi_T: "T : A \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>smc_Par \<alpha>\<^esub> B"
    using assms by (meson smc_Par_is_epic_arr subsmc_is_arrD)
  show ?thesis
  proof(rule sdg.is_epic_arrI)
    show T: "T : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B" by (rule assms(1))
    fix f g a
    assume prems: 
      "f : B \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> a" 
      "g : B \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> a"
      "f \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> T = g \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> T" 
    from prems(1) subsemicategory_axioms have "f : B \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> a" 
      by (cs_concl cs_intro: smc_sub_fw_cs_intros)
    moreover from prems(2) subsemicategory_axioms have "g : B \<mapsto>\<^bsub>smc_Par \<alpha>\<^esub> a" 
      by (cs_concl cs_intro: smc_sub_fw_cs_intros)
    moreover from prems T subsemicategory_axioms have 
      "f \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> T = g \<circ>\<^sub>A\<^bsub>smc_Par \<alpha>\<^esub> T"
      by (auto simp: smc_sub_bw_cs_simps)
    ultimately show "f = g"
      by (rule dg.is_epic_arrD(2)[OF epi_T])
  qed
qed

lemma (in \<Z>) smc_Set_is_epic_arrD:
  assumes "T : A \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>smc_Set \<alpha>\<^esub> B"
  shows "T : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B" and "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B"
proof-

  interpret semicategory \<alpha> \<open>smc_Set \<alpha>\<close> by (rule semicategory_smc_Set)

  from assms show T: "T : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B" by auto
  interpret T: arr_Set \<alpha> T
    rewrites "T\<lparr>ArrDom\<rparr> = A" and "T\<lparr>ArrCod\<rparr> = B"
    using T by (auto elim!: smc_Set_is_arrE)
  show "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B"
  proof(intro vsubset_antisym vsubsetI)
    fix b assume [intro]: "b \<in>\<^sub>\<circ> B" 
    show "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)"
    proof(rule ccontr)
      assume b: "b \<notin>\<^sub>\<circ> \<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)"
      define R 
        where "R = [vinsert \<langle>b, 0\<rangle> ((B -\<^sub>\<circ> set {b}) \<times>\<^sub>\<circ> set {1}), B, set {0, 1}]\<^sub>\<circ>"
      define S where "S = [B \<times>\<^sub>\<circ> set {1}, B, set {0, 1}]\<^sub>\<circ>"
      have R: "R : B \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> set {0, 1}" 
        unfolding R_def
      proof(intro smc_Set_is_arrI arr_Set_vfsequenceI, unfold arr_Rel_components)
        from Axiom_of_Infinity vone_in_omega show "set {0, 1} \<in>\<^sub>\<circ> Vset \<alpha>" by blast
      qed (auto simp: T.arr_Rel_ArrCod_in_Vset)
      have S: "S : B \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> set {0, 1}"
        unfolding S_def
      proof(intro smc_Set_is_arrI arr_Set_vfsequenceI, unfold arr_Rel_components)
        from Axiom_of_Infinity vone_in_omega show "set {0, 1} \<in>\<^sub>\<circ> Vset \<alpha>" by blast
      qed (auto simp: T.arr_Rel_ArrCod_in_Vset)
      from b have "R\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> T\<lparr>ArrVal\<rparr> = S\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>" 
        unfolding S_def R_def arr_Rel_components 
        by (auto intro!: vsubset_antisym vsubsetI)
      then have "R \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> T = S \<circ>\<^sub>A\<^bsub>smc_Set \<alpha>\<^esub> T"
        unfolding smc_Set_Comp_app[OF R T] smc_Set_Comp_app[OF S T]
        by (simp add: R_def S_def arr_Rel_components comp_Rel_def)
      from R S this have "R = S" by (rule is_epic_arrD(2)[OF assms])
      with zero_neq_one show False unfolding R_def S_def by blast
    qed
  qed (use T.arr_Set_ArrVal_vrange in auto)
qed

lemma (in \<Z>) smc_Set_is_epic_arr: 
  "T : A \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>smc_Set \<alpha>\<^esub> B \<longleftrightarrow> T : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B \<and> \<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B" 
  by (rule iffI) (simp_all add: smc_Set_is_epic_arrD smc_Set_is_epic_arrI)



subsection\<open>Terminal object, initial object and null object\<close>


text\<open>An object in \<open>Set\<close> is terminal if and only if it is a singleton 
set (see Chapter I-5 in \cite{mac_lane_categories_2010}).\<close>

lemma (in \<Z>) smc_Set_obj_terminal: 
  "obj_terminal (smc_Set \<alpha>) A \<longleftrightarrow> (\<exists>B\<in>\<^sub>\<circ>Vset \<alpha>. A = set {B})"
proof-

  interpret semicategory \<alpha> \<open>smc_Set \<alpha>\<close> by (rule semicategory_smc_Set)
  
  have "(\<forall>A\<in>\<^sub>\<circ>Vset \<alpha>. \<exists>!T. T : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B) \<longleftrightarrow> (\<exists>C\<in>\<^sub>\<circ>Vset \<alpha>. B = set {C})" 
    for B
  proof(intro iffI ballI)

    assume prems[rule_format]: "\<forall>A\<in>\<^sub>\<circ>Vset \<alpha>. \<exists>!T. T : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B"

    then obtain T where T0B: "T : 0 \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B" by (meson vempty_is_zet)
    then have B[simp]: "B \<in>\<^sub>\<circ> Vset \<alpha>" by (fastforce simp: smc_Set_components(1))

    show "\<exists>C\<in>\<^sub>\<circ>Vset \<alpha>. B = set {C}"
    proof(rule ccontr, cases \<open>B = 0\<close>)
      case True
      from prems have "\<exists>!T. T : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> 0" if "A \<in>\<^sub>\<circ> Vset \<alpha>" for A
        using that unfolding True by simp
      then obtain T where T: "T : set {0} \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> 0" 
        by (metis Axiom_of_Pairing insert_absorb2 vempty_is_zet)
      interpret T: arr_Set \<alpha> T
        rewrites "T\<lparr>ArrDom\<rparr> = set {0}" and "T\<lparr>ArrCod\<rparr> = 0"
        using T by (auto elim!: smc_Set_is_arrE)
      from 
        T.vdomain_vrange_is_vempty
        T.ArrVal.vdomain_vrange_is_vempty 
        T.arr_Set_ArrVal_vrange
      show False  
        by (auto simp: smc_Set_cs_simps)
    next
      case False 
      assume "\<not>(\<exists>C\<in>\<^sub>\<circ>Vset \<alpha>. B = set {C})"
      with B have "\<nexists>C. B = set {C}" by blast
      with False obtain a b where ab: "a \<noteq> b" "a \<in>\<^sub>\<circ> B" "b \<in>\<^sub>\<circ> B"
        by (metis V_equalityI vemptyE vintersection_vsingleton vsingletonD)
      have "[set {\<langle>0, a\<rangle>}, set {0}, B]\<^sub>\<circ> : set {0} \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B"
        by (intro smc_Set_is_arrI arr_SetI, unfold arr_Rel_components)
          (auto simp: ab(2) nat_omega_simps)
      moreover from ab have 
        "[set {\<langle>0, b\<rangle>}, set {0}, B]\<^sub>\<circ> : set {0} \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B"
        by (intro smc_Set_is_arrI arr_SetI, unfold arr_Rel_components)
          (auto simp: ab(2) nat_omega_simps)
      moreover with ab have 
        "[set {\<langle>0, a\<rangle>}, set {0}, B]\<^sub>\<circ> \<noteq> [set {\<langle>0, b\<rangle>}, set {0}, B]\<^sub>\<circ>"
        by simp
      ultimately show False
        by (metis prems smc_is_arrE smc_Set_components(1))
    qed
  next
    
    fix A assume prems: "\<exists>b\<in>\<^sub>\<circ>Vset \<alpha>. B = set {b}" "A \<in>\<^sub>\<circ> Vset \<alpha>"
    then obtain b where B_def: "B = set {b}" and b: "b \<in>\<^sub>\<circ> Vset \<alpha>" by blast

    have "vconst_on A b = A \<times>\<^sub>\<circ> set {b}" by (simp add: vconst_on_eq_vtimes)

    show "\<exists>!T. T : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B"
      unfolding B_def
    proof(rule ex1I[of _ \<open>[A \<times>\<^sub>\<circ> set {b}, A, set {b}]\<^sub>\<circ>\<close>])
      
      show "[A \<times>\<^sub>\<circ> set {b}, A, set {b}]\<^sub>\<circ> : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> set {b}"
        using b 
        by 
          ( 
            intro smc_Set_is_arrI arr_Set_vfsequenceI, 
            unfold arr_Rel_components
          )
          (auto simp: prems(2) vconst_on_eq_vtimes[symmetric])
      
      fix T assume prems: "T : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> set {b}"

      interpret T: arr_Set \<alpha> T
        rewrites [simp]: "T\<lparr>ArrDom\<rparr> = A" and [simp]: "T\<lparr>ArrCod\<rparr> = set {b}"
        using prems by (auto elim!: smc_Set_is_arrE)

      have [simp]: "T\<lparr>ArrVal\<rparr> = A \<times>\<^sub>\<circ> set {b}"
      proof(intro vsubset_antisym vsubsetI)
        fix x assume prems: "x \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>"
        with T.vbrelation_axioms app_vdomainI obtain a b' 
          where "x = \<langle>a, b'\<rangle>" and "a \<in>\<^sub>\<circ> A"
          by (metis T.ArrVal.vbrelation_vinE T.arr_Set_ArrVal_vdomain)
        with prems T.arr_Set_ArrVal_vrange show "x \<in>\<^sub>\<circ> A \<times>\<^sub>\<circ> set {b}" by auto
      next
        fix x assume "x \<in>\<^sub>\<circ> A \<times>\<^sub>\<circ> set {b}" 
        then obtain a where x_def: "x = \<langle>a, b\<rangle>" and "a \<in>\<^sub>\<circ> A" by clarsimp
        have "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A" by (simp add: smc_Set_cs_simps)
        moreover with 
          T.arr_Set_ArrVal_vrange T.ArrVal.vdomain_vrange_is_vempty \<open>a \<in>\<^sub>\<circ> A\<close>   
        have "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = set {b}"
          by auto
        ultimately show "x \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>"
          using \<open>a \<in>\<^sub>\<circ> A\<close>
          unfolding x_def 
          by 
            (
              metis 
                T.ArrVal.vsv_ex1_app1 
                T.ArrVal.vsv_vimageI1 
                vimage_vdomain 
                vsingletonD
            )
      qed
      
      show "T = [A \<times>\<^sub>\<circ> set {b}, A, set {b}]\<^sub>\<circ>"
      proof(rule arr_Set_eqI[of \<alpha>], unfold arr_Rel_components)
        show "arr_Set \<alpha> [A \<times>\<^sub>\<circ> set {b}, A, set {b}]\<^sub>\<circ>"
          using T.arr_Rel_def T.arr_Set_axioms by auto
      qed (auto simp: T.arr_Set_axioms)

    qed
  qed

  then show ?thesis
    apply(intro iffI obj_terminalI)
    subgoal by (metis smc_is_arrD(2) obj_terminalE)
    subgoal by blast
    subgoal by (metis smc_Set_components(1))
    done

qed


text\<open>An object in \<open>Set\<close> is initial if and only if it is the empty 
set (see Chapter I-5 in \cite{mac_lane_categories_2010}).\<close>

lemma (in \<Z>) smc_Set_obj_initial: "obj_initial (smc_Set \<alpha>) A \<longleftrightarrow> A = 0"
proof-

  interpret semicategory \<alpha> \<open>smc_Set \<alpha>\<close> by (rule semicategory_smc_Set)

  have "(\<forall>B\<in>\<^sub>\<circ>Vset \<alpha>. \<exists>!T. T : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B) \<longleftrightarrow> A = 0" for A
  proof(intro iffI ballI)

    assume prems[rule_format]: "\<forall>B\<in>\<^sub>\<circ>Vset \<alpha>. \<exists>!T. T : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B" 

    then obtain T where T0B: "T : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> 0" by (meson vempty_is_zet)
    then have A[simp]: "A \<in>\<^sub>\<circ> Vset \<alpha>" by (fastforce simp: smc_Set_components(1))

    show "A = 0"
    proof(rule ccontr)
      assume "A \<noteq> 0"
      then obtain a where a: "a \<in>\<^sub>\<circ> A" by (auto dest: trad_foundation)
      from Axiom_of_Powers a have A0: 
        "[A \<times>\<^sub>\<circ> set {0}, A, set {0}]\<^sub>\<circ> : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> set {0}"
        by 
          ( 
            intro smc_Set_is_arrI arr_Set_vfsequenceI, 
            unfold arr_Rel_components
          )
          auto
      have A1: "[A \<times>\<^sub>\<circ> set {1}, A, set {1}]\<^sub>\<circ> : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> set {1}"
      proof
          ( 
            intro smc_Set_is_arrI arr_Set_vfsequenceI, 
            unfold arr_Rel_components
          )
        show "set {1} \<in>\<^sub>\<circ> Vset \<alpha>" by (blast intro: vone_in_omega Axiom_of_Infinity)
      qed auto
      have "[A \<times>\<^sub>\<circ> set {0}, A, set {0, 1}]\<^sub>\<circ> : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> set {0, 1}"
      proof
        (
          intro smc_Set_is_arrI arr_Set_vfsequenceI, 
          unfold arr_Rel_components
        )
        show "set {[]\<^sub>\<circ>, 1} \<in>\<^sub>\<circ> Vset \<alpha>"
          by (intro Limit_vdoubleton_in_VsetI) (force simp: nat_omega_simps)+
      qed auto
      moreover have 
        "[A \<times>\<^sub>\<circ> set {1}, A, set {0, 1}]\<^sub>\<circ> : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> set {0, 1}"
      proof
        (
          intro smc_Set_is_arrI arr_Set_vfsequenceI, 
          unfold arr_Rel_components
        )
        show "set {[]\<^sub>\<circ>, 1} \<in>\<^sub>\<circ> Vset \<alpha>"
          by (intro Limit_vdoubleton_in_VsetI) (force simp: nat_omega_simps)+
      qed auto
      moreover from \<open>A \<noteq> 0\<close> one_neq_zero have 
        "[A \<times>\<^sub>\<circ> set {0}, A, set {0, 1}]\<^sub>\<circ> \<noteq> [A \<times>\<^sub>\<circ> set {1}, A, set {0, 1}]\<^sub>\<circ>" 
        by (blast intro!: vsubset_antisym)
      ultimately show False 
        by (metis prems smc_is_arrE smc_Set_components(1))
    qed
  next
    fix B assume prems: "A = 0" "B \<in>\<^sub>\<circ> Vset \<alpha>"
    show "\<exists>!T. T : A \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B"
    proof(rule ex1I[of _ \<open>[0, 0, B]\<^sub>\<circ>\<close>], unfold prems(1))
      show zzB: "[0, 0, B]\<^sub>\<circ> : 0 \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B"
        by 
          (
            intro smc_Set_is_arrI arr_Set_vfsequenceI, 
            unfold arr_Rel_components
          )
          (simp_all add: prems)
      fix T assume prems: "T : 0 \<mapsto>\<^bsub>smc_Set \<alpha>\<^esub> B"
      interpret T: arr_Set \<alpha> T
        rewrites [simp]: "T\<lparr>ArrDom\<rparr> = 0" and [simp]: "T\<lparr>ArrCod\<rparr> = B"
        using prems by (auto simp: smc_Set_is_arrD)
      show "T = [0, 0, B]\<^sub>\<circ>"  
      proof(rule arr_Set_eqI[of \<alpha>], unfold arr_Rel_components)
        show "arr_Set \<alpha> T" by (rule T.arr_Set_axioms)
        from zzB show "arr_Set \<alpha> [[]\<^sub>\<circ>, []\<^sub>\<circ>, B]\<^sub>\<circ>" by (meson smc_Set_is_arrE)
        from T.ArrVal.vdomain_vrange_is_vempty show "T\<lparr>ArrVal\<rparr> = []\<^sub>\<circ>"
          by (auto intro: T.ArrVal.vsv_vrange_vempty simp: smc_Set_cs_simps)
      qed simp_all
    qed
  qed

  then show ?thesis 
    apply(intro iffI obj_initialI, elim obj_initialE)
    subgoal by (metis smc_Set_components(1))
    subgoal by (simp add: smc_Set_components(1))
    subgoal by (metis smc_Set_components(1))
    done

qed


text\<open>
There are no null objects in \<open>Set\<close> (this is a trivial corollary of the 
above).
\<close>

lemma (in \<Z>) smc_Set_obj_null: "obj_null (smc_Set \<alpha>) A \<longleftrightarrow> False"
  unfolding obj_null_def smc_Set_obj_terminal smc_Set_obj_initial by simp



subsection\<open>Zero arrow\<close>


text\<open>
There are no zero arrows in \<open>Set\<close> (this result is a trivial 
corollary of the absence of null objects).
\<close>

lemma (in \<Z>) smc_Set_is_zero_arr: "T : A \<mapsto>\<^sub>0\<^bsub>smc_Set \<alpha>\<^esub> B \<longleftrightarrow> False"
  using smc_Set_obj_null unfolding is_zero_arr_def by auto

text\<open>\newpage\<close>

end