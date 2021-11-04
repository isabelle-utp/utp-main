(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>Rel\<close> as a semicategory\<close>
theory CZH_SMC_Rel
  imports 
    CZH_DG_Rel
    CZH_SMC_Semifunctor
    CZH_SMC_Small_Semicategory
begin



subsection\<open>Background\<close>


text\<open>
The methodology chosen for the exposition 
of \<open>Rel\<close> as a semicategory is analogous to the 
one used in the previous chapter for the exposition of \<open>Rel\<close> as a digraph. 
The general references for this section are Chapter I-7 
in \cite{mac_lane_categories_2010} and nLab 
\cite{noauthor_nlab_nodate}\footnote{
\url{https://ncatlab.org/nlab/show/Rel}
}.
\<close>

named_theorems smc_Rel_cs_simps
named_theorems smc_Rel_cs_intros

lemmas (in arr_Rel) [smc_Rel_cs_simps] = 
  dg_Rel_shared_cs_simps

lemmas [smc_Rel_cs_simps] = 
  dg_Rel_shared_cs_simps
  arr_Rel.arr_Rel_length
  arr_Rel_comp_Rel_id_Rel_left
  arr_Rel_comp_Rel_id_Rel_right
  arr_Rel.arr_Rel_converse_Rel_converse_Rel
  arr_Rel_converse_Rel_eq_iff
  arr_Rel_converse_Rel_comp_Rel
  arr_Rel_comp_Rel_converse_Rel_left_if_v11
  arr_Rel_comp_Rel_converse_Rel_right_if_v11

lemmas [smc_Rel_cs_intros] =
  dg_Rel_shared_cs_intros
  arr_Rel_comp_Rel
  arr_Rel.arr_Rel_converse_Rel



subsection\<open>\<open>Rel\<close> as a semicategory\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition smc_Rel :: "V \<Rightarrow> V"
  where "smc_Rel \<alpha> =
    [
      Vset \<alpha>,
      set {T. arr_Rel \<alpha> T},
      (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Rel \<alpha> T}. T\<lparr>ArrDom\<rparr>),
      (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Rel \<alpha> T}. T\<lparr>ArrCod\<rparr>),
      (\<lambda>ST\<in>\<^sub>\<circ>composable_arrs (dg_Rel \<alpha>). ST\<lparr>0\<rparr> \<circ>\<^sub>R\<^sub>e\<^sub>l ST\<lparr>1\<^sub>\<nat>\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smc_Rel_components:
  shows "smc_Rel \<alpha>\<lparr>Obj\<rparr> = Vset \<alpha>"
    and "smc_Rel \<alpha>\<lparr>Arr\<rparr> = set {T. arr_Rel \<alpha> T}"
    and "smc_Rel \<alpha>\<lparr>Dom\<rparr> = (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Rel \<alpha> T}. T\<lparr>ArrDom\<rparr>)"
    and "smc_Rel \<alpha>\<lparr>Cod\<rparr> = (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Rel \<alpha> T}. T\<lparr>ArrCod\<rparr>)"
    and "smc_Rel \<alpha>\<lparr>Comp\<rparr> = (\<lambda>ST\<in>\<^sub>\<circ>composable_arrs (dg_Rel \<alpha>). ST\<lparr>0\<rparr> \<circ>\<^sub>R\<^sub>e\<^sub>l ST\<lparr>1\<^sub>\<nat>\<rparr>)"
  unfolding smc_Rel_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smc_dg_smc_Rel: "smc_dg (smc_Rel \<alpha>) = dg_Rel \<alpha>"
proof(rule vsv_eqI)
  show "vsv (smc_dg (smc_Rel \<alpha>))" unfolding smc_dg_def by auto
  show "vsv (dg_Rel \<alpha>)" unfolding dg_Rel_def by auto
  have dom_lhs: "\<D>\<^sub>\<circ> (smc_dg (smc_Rel \<alpha>)) = 4\<^sub>\<nat>" 
    unfolding smc_dg_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (dg_Rel \<alpha>) = 4\<^sub>\<nat>"
    unfolding dg_Rel_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (smc_dg (smc_Rel \<alpha>)) = \<D>\<^sub>\<circ> (dg_Rel \<alpha>)"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_dg (smc_Rel \<alpha>)) \<Longrightarrow> smc_dg (smc_Rel \<alpha>)\<lparr>a\<rparr> = dg_Rel \<alpha>\<lparr>a\<rparr>"
    for a
    by 
      (
        unfold dom_lhs,
        elim_in_numeral,
        unfold smc_dg_def dg_field_simps smc_Rel_def dg_Rel_def
      )
      (auto simp: nat_omega_simps)
qed

lemmas_with [folded smc_dg_smc_Rel, unfolded slicing_simps]: 
  smc_Rel_Obj_iff = dg_Rel_Obj_iff
  and smc_Rel_Arr_iff[smc_Rel_cs_simps] = dg_Rel_Arr_iff
  and smc_Rel_Dom_vsv[smc_Rel_cs_intros] = dg_Rel_Dom_vsv
  and smc_Rel_Dom_vdomain[smc_Rel_cs_simps] = dg_Rel_Dom_vdomain
  and smc_Rel_Dom_app[smc_Rel_cs_simps] = dg_Rel_Dom_app
  and smc_Rel_Dom_vrange = dg_Rel_Dom_vrange
  and smc_Rel_Cod_vsv[smc_Rel_cs_intros] = dg_Rel_Cod_vsv
  and smc_Rel_Cod_vdomain[smc_Rel_cs_simps] = dg_Rel_Cod_vdomain
  and smc_Rel_Cod_app[smc_Rel_cs_simps] = dg_Rel_Cod_app
  and smc_Rel_Cod_vrange = dg_Rel_Cod_vrange
  and smc_Rel_is_arrI[smc_Rel_cs_intros] = dg_Rel_is_arrI
  and smc_Rel_is_arrD = dg_Rel_is_arrD
  and smc_Rel_is_arrE = dg_Rel_is_arrE

lemmas [smc_cs_simps] = smc_Rel_is_arrD(2,3)

lemmas_with (in \<Z>) [folded smc_dg_smc_Rel, unfolded slicing_simps]: 
  smc_Rel_Hom_vifunion_in_Vset = dg_Rel_Hom_vifunion_in_Vset
  and smc_Rel_incl_Rel_is_arr = dg_Rel_incl_Rel_is_arr
  and smc_Rel_incl_Rel_is_arr'[smc_Rel_cs_intros] = dg_Rel_incl_Rel_is_arr'

lemmas [smc_Rel_cs_intros] = \<Z>.smc_Rel_incl_Rel_is_arr'


subsubsection\<open>Composable arrows\<close>

lemma smc_Rel_composable_arrs_dg_Rel: 
  "composable_arrs (dg_Rel \<alpha>) = composable_arrs (smc_Rel \<alpha>)"
  unfolding composable_arrs_def smc_dg_smc_Rel[symmetric] slicing_simps by simp

lemma smc_Rel_Comp: 
  "smc_Rel \<alpha>\<lparr>Comp\<rparr> = (\<lambda>ST\<in>\<^sub>\<circ>composable_arrs (smc_Rel \<alpha>). ST\<lparr>0\<rparr> \<circ>\<^sub>R\<^sub>e\<^sub>l ST\<lparr>1\<^sub>\<nat>\<rparr>)"
  unfolding smc_Rel_components smc_Rel_composable_arrs_dg_Rel ..


subsubsection\<open>Composition\<close>

lemma smc_Rel_Comp_app[smc_Rel_cs_simps]:
  assumes "S : b \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> c" and "T : a \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> b"
  shows "S \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> T = S \<circ>\<^sub>R\<^sub>e\<^sub>l T"
proof-
  from assms have "[S, T]\<^sub>\<circ> \<in>\<^sub>\<circ> composable_arrs (smc_Rel \<alpha>)" 
    by (auto intro: smc_cs_intros)
  then show "S \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> T = S \<circ>\<^sub>R\<^sub>e\<^sub>l T"
    unfolding smc_Rel_Comp by (simp add: nat_omega_simps)
qed 

lemma smc_Rel_Comp_vdomain: "\<D>\<^sub>\<circ> (smc_Rel \<alpha>\<lparr>Comp\<rparr>) = composable_arrs (smc_Rel \<alpha>)" 
  unfolding smc_Rel_Comp by simp

lemma (in \<Z>) smc_CAT_Comp_vrange:
  "\<R>\<^sub>\<circ> (smc_Rel \<alpha>\<lparr>Comp\<rparr>) \<subseteq>\<^sub>\<circ> set {T. arr_Rel \<alpha> T}"
proof(rule vsubsetI)
  interpret digraph \<alpha> \<open>smc_dg (smc_Rel \<alpha>)\<close>
    unfolding smc_dg_smc_Rel by (simp add: digraph_dg_Rel)
  fix R assume "R \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (smc_Rel \<alpha>\<lparr>Comp\<rparr>)"
  then obtain ST 
    where R_def: "R = smc_Rel \<alpha>\<lparr>Comp\<rparr>\<lparr>ST\<rparr>"
      and "ST \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_Rel \<alpha>\<lparr>Comp\<rparr>)"
    unfolding smc_Rel_components by (auto intro: smc_cs_intros)
  then obtain S T a b c 
    where "ST = [S, T]\<^sub>\<circ>" 
      and S: "S : b \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> c" 
      and T: "T : a \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> b"
    by (auto simp: smc_Rel_Comp_vdomain)
  with R_def have R_def': "R = S \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> T" by simp
  note S_D = dg_is_arrD(1)[unfolded slicing_simps, OF S]
  note T_D = dg_is_arrD(1)[unfolded slicing_simps, OF T]
  from S_D T_D have "arr_Rel \<alpha> S" "arr_Rel \<alpha> T" 
    by (simp_all add: smc_Rel_components)
  from this show "R \<in>\<^sub>\<circ> set {T. arr_Rel \<alpha> T}" 
    unfolding R_def' smc_Rel_Comp_app[OF S T] by (auto simp: arr_Rel_comp_Rel)
qed


subsubsection\<open>\<open>Rel\<close> is a semicategory\<close>

lemma (in \<Z>) semicategory_smc_Rel: "semicategory \<alpha> (smc_Rel \<alpha>)"
proof(rule semicategoryI, unfold smc_dg_smc_Rel)
  show "vfsequence (smc_Rel \<alpha>)" unfolding smc_Rel_def by simp
  show "vcard (smc_Rel \<alpha>) = 5\<^sub>\<nat>" 
    unfolding smc_Rel_def by (simp add: nat_omega_simps)
  show "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_Rel \<alpha>\<lparr>Comp\<rparr>) \<longleftrightarrow> 
    (\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> c \<and> f : a \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> b)"
    for gf
    unfolding smc_Rel_Comp_vdomain by (auto intro: composable_arrsI)
  show "g \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> f : a \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> c"
    if "g : b \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> c" and "f : a \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> b" for g b c f a
  proof-
    from that have "arr_Rel \<alpha> g" and "arr_Rel \<alpha> f" 
      by (auto simp: smc_Rel_is_arrD(1))
    with that show ?thesis
      by 
        (
          cs_concl 
            cs_simp: smc_cs_simps smc_Rel_cs_simps cs_intro: smc_Rel_cs_intros
        )
  qed
  show "h \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> g \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> f = h \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> (g \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> f)"
    if "h : c \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> d" 
      and "g : b \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> c"
      and "f : a \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> b"
    for h c d g b f a
  proof-
    from that have "arr_Rel \<alpha> h" and "arr_Rel \<alpha> g" and "arr_Rel \<alpha> f" 
      by (auto simp: smc_Rel_is_arrD(1))
    with that show ?thesis
      by 
        (
          cs_concl 
            cs_simp: smc_cs_simps smc_Rel_cs_simps 
            cs_intro: smc_Rel_cs_intros
        )
  qed
qed (auto simp: digraph_dg_Rel smc_Rel_components)



subsection\<open>Canonical dagger for \<open>Rel\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition smcf_dag_Rel :: "V \<Rightarrow> V" (\<open>\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l\<close>)
  where "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> =
    [
      vid_on (smc_Rel \<alpha>\<lparr>Obj\<rparr>),
      VLambda (smc_Rel \<alpha>\<lparr>Arr\<rparr>) converse_Rel,
      op_smc (smc_Rel \<alpha>), 
      smc_Rel \<alpha>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smcf_dag_Rel_components:
  shows "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr> = vid_on (smc_Rel \<alpha>\<lparr>Obj\<rparr>)"
    and "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr> = VLambda (smc_Rel \<alpha>\<lparr>Arr\<rparr>) converse_Rel"
    and "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>HomDom\<rparr> = op_smc (smc_Rel \<alpha>)"
    and "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>HomCod\<rparr> = smc_Rel \<alpha>"
  unfolding smcf_dag_Rel_def dghm_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smcf_dghm_smcf_dag_Rel: "smcf_dghm (\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>) = \<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>"
proof(rule vsv_eqI)
  show "vsv (smcf_dghm (\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>))" unfolding smcf_dghm_def by auto
  show "vsv (\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)" unfolding dghm_dag_Rel_def by auto
  have dom_lhs: "\<D>\<^sub>\<circ> (smcf_dghm (\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)) = 4\<^sub>\<nat>" 
    unfolding smcf_dghm_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>) = 4\<^sub>\<nat>"
    unfolding dghm_dag_Rel_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (smcf_dghm (\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)) = \<D>\<^sub>\<circ> (\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smcf_dghm (\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)) \<Longrightarrow>
    smcf_dghm (\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)\<lparr>a\<rparr> = \<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>a\<rparr>"
    for a
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral, 
        unfold dghm_field_simps[symmetric],
        unfold 
          smc_dg_smc_Rel
          slicing_commute[symmetric]
          smcf_dghm_components 
          dghm_dag_Rel_components
          smcf_dag_Rel_components
          dg_Rel_components
          smc_Rel_components
      )
      simp_all
qed

lemmas_with [
    folded smc_dg_smc_Rel smcf_dghm_smcf_dag_Rel, 
    unfolded slicing_simps
    ]: 
  smcf_dag_Rel_ObjMap_vsv[smc_Rel_cs_intros] = dghm_dag_Rel_ObjMap_vsv
  and smcf_dag_Rel_ObjMap_vdomain[smc_Rel_cs_simps] = 
    dghm_dag_Rel_ObjMap_vdomain
  and smcf_dag_Rel_ObjMap_app[smc_Rel_cs_simps] = dghm_dag_Rel_ObjMap_app
  and smcf_dag_Rel_ObjMap_vrange[smc_Rel_cs_simps] = dghm_dag_Rel_ObjMap_vrange
  and smcf_dag_Rel_ArrMap_vsv[smc_Rel_cs_intros] = dghm_dag_Rel_ArrMap_vsv
  and smcf_dag_Rel_ArrMap_vdomain[smc_Rel_cs_simps] = dghm_dag_Rel_ArrMap_vdomain
  and smcf_dag_Rel_ArrMap_app[smc_Rel_cs_simps] = dghm_dag_Rel_ArrMap_app
  and smcf_dag_Rel_ArrMap_vrange[smc_Rel_cs_simps] = dghm_dag_Rel_ArrMap_vrange

lemmas_with (in \<Z>) [
    folded smc_dg_smc_Rel smcf_dghm_smcf_dag_Rel, unfolded slicing_simps
    ]: 
  smcf_dag_Rel_app_is_arr = dghm_dag_Rel_ArrMap_app_is_arr


subsubsection\<open>Canonical dagger is a contravariant isomorphism of \<open>Rel\<close>\<close>

lemma (in \<Z>) smcf_dag_Rel_is_iso_semifunctor: 
  "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> : op_smc (smc_Rel \<alpha>) \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> smc_Rel \<alpha>"
proof(rule is_iso_semifunctorI)
  interpret dag: is_iso_dghm \<alpha> \<open>op_dg (dg_Rel \<alpha>)\<close> \<open>dg_Rel \<alpha>\<close> \<open>\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<close>
    by (rule dghm_dag_Rel_is_iso_dghm)
  interpret Rel: semicategory \<alpha> \<open>smc_Rel \<alpha>\<close> 
    by (rule semicategory_smc_Rel)
  show "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> : op_smc (smc_Rel \<alpha>) \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> smc_Rel \<alpha>"
  proof
    (
      rule is_semifunctorI,
      unfold 
        smc_dg_smc_Rel 
        smcf_dghm_smcf_dag_Rel 
        smc_op_simps 
        slicing_commute[symmetric] 
        smcf_dag_Rel_components(3,4)
    )
    show "vfsequence (\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)"
      unfolding smcf_dag_Rel_def by (simp add: nat_omega_simps)
    show "vcard (\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>) = 4\<^sub>\<nat>"
      unfolding smcf_dag_Rel_def by (simp add: nat_omega_simps)
    show "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>f \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> g\<rparr> =
      \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      if "g : c \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> b" and "f : b \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> a"
      for g b c f a
    proof-
      from that have "arr_Rel \<alpha> g" and "arr_Rel \<alpha> f" 
        by (auto simp: smc_Rel_is_arrD(1))
      with that show ?thesis
        by 
          (
            cs_concl 
              cs_simp: smc_cs_simps smc_Rel_cs_simps 
              cs_intro: smc_Rel_cs_intros
          )
    qed
  qed (auto simp: dg_cs_intros smc_op_intros semicategory_smc_Rel) 

  show "smcf_dghm (\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>) :
    smc_dg (op_smc (smc_Rel \<alpha>)) \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> smc_dg (smc_Rel \<alpha>)"
    by 
      (
        simp add: 
          smc_dg_smc_Rel 
          smcf_dghm_smcf_dag_Rel 
          smc_op_simps 
          slicing_simps 
          slicing_commute[symmetric] 
          dghm_dag_Rel_is_iso_dghm
      )
                                        
qed


subsubsection\<open>Further properties of the canonical dagger\<close>

lemma (in \<Z>) smcf_cn_comp_smcf_dag_Rel_smcf_dag_Rel: 
  "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> = smcf_id (smc_Rel \<alpha>)"
proof(rule smcf_dghm_eqI)
  interpret semicategory \<alpha> \<open>smc_Rel \<alpha>\<close> by (simp add: semicategory_smc_Rel)
  from smcf_dag_Rel_is_iso_semifunctor have dag:
    "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> : op_smc (smc_Rel \<alpha>) \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> smc_Rel \<alpha>"
    by (simp add: is_iso_semifunctor.axioms(1))
  from smcf_cn_comp_is_semifunctor[OF semicategory_axioms dag dag] show 
    "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> : smc_Rel \<alpha> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> smc_Rel \<alpha>" .
  show "smcf_id (smc_Rel \<alpha>) : smc_Rel \<alpha> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> smc_Rel \<alpha>"
    by (auto simp: smc_smcf_id_is_semifunctor)
  show "smcf_dghm (\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>) = smcf_dghm (smcf_id (smc_Rel \<alpha>))"
    unfolding 
      slicing_simps slicing_commute[symmetric] 
      smc_dg_smc_Rel 
      smcf_dghm_smcf_dag_Rel
    by (simp add: dghm_cn_comp_dghm_dag_Rel_dghm_dag_Rel)
qed simp_all

lemma (in \<Z>) smcf_dag_Rel_ArrMap_smc_Rel_Comp:
  assumes "S : b \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> c" and "T : a \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> b"
  shows "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>S \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> T\<rparr> =
    \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr> \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>S\<rparr>"
proof-
  from assms have "arr_Rel \<alpha> S" and "arr_Rel \<alpha> T" 
    by (auto simp: smc_Rel_is_arrD(1))
  with assms show ?thesis
    by 
      (
        cs_concl 
          cs_simp: smc_cs_simps smc_Rel_cs_simps cs_intro: smc_Rel_cs_intros
      )
qed



subsection\<open>Monic arrow and epic arrow\<close>


text\<open>
The conditions for an arrow of \<open>Rel\<close> to be either monic or epic are 
outlined in nLab \cite{noauthor_nlab_nodate}\footnote{
\url{https://ncatlab.org/nlab/show/Rel}
}.
\<close>

context \<Z>
begin

context
begin

private lemma smc_Rel_is_monic_arr_vsubset: 
  assumes "T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B" 
    and "R : A' \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> A" 
    and "S : A' \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> A" 
    and "T \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> R = T \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> S"
    and "\<And>y z X. 
      \<lbrakk> y \<subseteq>\<^sub>\<circ> A; z \<subseteq>\<^sub>\<circ> A; T\<lparr>ArrVal\<rparr> `\<^sub>\<circ> y = X; T\<lparr>ArrVal\<rparr> `\<^sub>\<circ> z = X \<rbrakk> \<Longrightarrow> y = z"
  shows "R\<lparr>ArrVal\<rparr> \<subseteq>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>"
proof-
  interpret Rel: semicategory \<alpha> \<open>smc_Rel \<alpha>\<close> by (rule semicategory_smc_Rel)
  interpret R: arr_Rel \<alpha> R 
    rewrites "R\<lparr>ArrDom\<rparr> = A'" and "R\<lparr>ArrCod\<rparr> = A"
    using assms(2)
    by (all\<open>elim Rel.smc_is_arrE\<close>) (simp_all add: smc_Rel_components)
  interpret S: arr_Rel \<alpha> S
    rewrites "S\<lparr>ArrDom\<rparr> = A'" and "S\<lparr>ArrCod\<rparr> = A"
    using assms(3)
    by (all\<open>elim Rel.smc_is_arrE\<close>) (simp_all add: smc_Rel_components)
  from assms(4) have "(T \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> R)\<lparr>ArrVal\<rparr> = (T \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> S)\<lparr>ArrVal\<rparr>"
    by simp
  then have eq: "T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> R\<lparr>ArrVal\<rparr> = T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>"
    unfolding 
      smc_Rel_Comp_app[OF assms(1,2)]
      smc_Rel_Comp_app[OF assms(1,3)]
      comp_Rel_components
    by simp
  show "R\<lparr>ArrVal\<rparr> \<subseteq>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>"
  proof(rule vsubsetI)    
    fix ab assume ab[intro]: "ab \<in>\<^sub>\<circ> R\<lparr>ArrVal\<rparr>"
    with R.ArrVal.vbrelation obtain a b where ab_def: "ab = \<langle>a, b\<rangle>" by auto 
    with ab R.arr_Rel_ArrVal_vrange have "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (R\<lparr>ArrVal\<rparr>)" and "b \<in>\<^sub>\<circ> A" 
      by auto
    define B' and C' where "B' = R\<lparr>ArrVal\<rparr> `\<^sub>\<circ> set {a}" and "C' = T\<lparr>ArrVal\<rparr> `\<^sub>\<circ> B'"
    have ne_C': "C' \<noteq> 0"
    proof(rule ccontr, unfold not_not)
      assume prems: "C' = 0"
      from ab have "b \<in>\<^sub>\<circ> B'" unfolding ab_def B'_def by simp
      with C'_def[unfolded prems] have b0: "T\<lparr>ArrVal\<rparr> `\<^sub>\<circ> set {b} = 0" by auto
      from assms(5)[OF _ _ b0, of 0] \<open>b \<in>\<^sub>\<circ> A\<close> show False by auto
    qed
    have cac''[intro, simp]: 
      "c \<in>\<^sub>\<circ> C' \<Longrightarrow> \<langle>a, c\<rangle> \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>" for c
      unfolding eq[symmetric] C'_def B'_def 
      by (metis vcomp_vimage vimage_vsingleton_iff)
    define A'' where "A'' = (T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>) -`\<^sub>\<circ> C'"
    define B'' where "B'' = S\<lparr>ArrVal\<rparr> `\<^sub>\<circ> set {a}"
    define C'' where "C'' = T\<lparr>ArrVal\<rparr> `\<^sub>\<circ> B''"
    have a'': "a \<in>\<^sub>\<circ> A''"
    proof-
      from ne_C' obtain c' where [intro]: "c' \<in>\<^sub>\<circ> C'" 
        by (auto intro!: vsubset_antisym)
      then have "\<langle>a, c'\<rangle> \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>" by simp
      then show ?thesis unfolding A''_def by auto
    qed
    have "C' \<subseteq>\<^sub>\<circ> C''"
      unfolding C''_def B''_def A''_def C'_def B'_def
      by (rule vsubsetI) (metis eq vcomp_vimage)
    have "C' = C''"
    proof(rule ccontr)
      assume "C' \<noteq> C''"
      with \<open>C' \<subseteq>\<^sub>\<circ> C''\<close> obtain c' where c': "c' \<in>\<^sub>\<circ> C'' -\<^sub>\<circ> C'" 
        by (auto intro!: vsubset_antisym)
      then obtain b'' where "b'' \<in>\<^sub>\<circ> B''" and "\<langle>b'', c'\<rangle> \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>"
        unfolding C''_def by auto
      then have "\<langle>a, c'\<rangle> \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> R\<lparr>ArrVal\<rparr>" unfolding eq B''_def by auto
      with c' show False unfolding B'_def C'_def by auto
    qed
    then have "T\<lparr>ArrVal\<rparr> `\<^sub>\<circ> B'' = T\<lparr>ArrVal\<rparr> `\<^sub>\<circ> B'" by (simp add: C''_def C'_def)
    moreover have "B' \<subseteq>\<^sub>\<circ> A" and "B'' \<subseteq>\<^sub>\<circ> A"
      using R.arr_Rel_ArrVal_vrange S.arr_Rel_ArrVal_vrange         
      unfolding B'_def B''_def 
      by auto
    ultimately have "B'' = B'" by (simp add: assms(5))
    with ab have "b \<in>\<^sub>\<circ> B''" unfolding B'_def ab_def by simp
    then show "ab \<in>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>" unfolding ab_def B''_def by simp
  qed
qed

lemma smc_Rel_is_monic_arrI:
  assumes "T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B"  
    and "\<And>y z X. \<lbrakk> y \<subseteq>\<^sub>\<circ> A; z \<subseteq>\<^sub>\<circ> A; T\<lparr>ArrVal\<rparr> `\<^sub>\<circ> y = X; T\<lparr>ArrVal\<rparr> `\<^sub>\<circ> z = X \<rbrakk> \<Longrightarrow> 
      y = z"
  shows "T : A \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>smc_Rel \<alpha>\<^esub> B"
proof(rule is_monic_arrI)

  interpret Rel: semicategory \<alpha> \<open>smc_Rel \<alpha>\<close> by (simp add: semicategory_smc_Rel)

  fix R S A'
  assume prems: 
    "R : A' \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> A" 
    "S : A' \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> A"
    "T \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> R = T \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> S"

  interpret T: arr_Rel \<alpha> T
    rewrites "T\<lparr>ArrDom\<rparr> = A" and "T\<lparr>ArrCod\<rparr> = B"
    using assms(1)
    by (all\<open>elim Rel.smc_is_arrE\<close>) (simp_all add: smc_Rel_components)
  interpret R: arr_Rel \<alpha> R 
    rewrites [simp]: "R\<lparr>ArrDom\<rparr> = A'" and [simp]: "R\<lparr>ArrCod\<rparr> = A"
    using prems(1)
    by (all\<open>elim Rel.smc_is_arrE\<close>) (simp_all add: smc_Rel_components)
  interpret S: arr_Rel \<alpha> S
    rewrites [simp]: "S\<lparr>ArrDom\<rparr> = A'" and [simp]: "S\<lparr>ArrCod\<rparr> = A"
    using prems(2)
    by (all\<open>elim Rel.smc_is_arrE\<close>) (simp_all add: smc_Rel_components)

  from assms prems have 
    "R\<lparr>ArrVal\<rparr> \<subseteq>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>" "S\<lparr>ArrVal\<rparr> \<subseteq>\<^sub>\<circ> R\<lparr>ArrVal\<rparr>" 
    by (auto simp: smc_Rel_is_monic_arr_vsubset)
  then show "R = S"
    using R.arr_Rel_axioms S.arr_Rel_axioms 
    by (intro arr_Rel_eqI[of \<alpha> R S]) auto

qed (rule assms(1))

end

end

lemma (in \<Z>) smc_Rel_is_monic_arrD[dest]:
  assumes "T : A \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>smc_Rel \<alpha>\<^esub> B"
    and "y \<subseteq>\<^sub>\<circ> A"
    and "z \<subseteq>\<^sub>\<circ> A" 
    and "T\<lparr>ArrVal\<rparr> `\<^sub>\<circ> y = X" 
    and "T\<lparr>ArrVal\<rparr> `\<^sub>\<circ> z = X" 
  shows "y = z"
proof-

  interpret Rel: semicategory \<alpha> \<open>smc_Rel \<alpha>\<close> by (simp add: semicategory_smc_Rel)

  from assms have T: "T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B" by (simp add: is_monic_arr_def)
  interpret T: arr_Rel \<alpha> T
    rewrites "T\<lparr>ArrDom\<rparr> = A" and [simp]: "T\<lparr>ArrCod\<rparr> = B"
    using T
    by (all\<open>elim Rel.smc_is_arrE\<close>) (simp_all add: smc_Rel_components)
 
  define R where "R = [set {0} \<times>\<^sub>\<circ> y, set {0}, A]\<^sub>\<circ>"
  define S where "S = [set {0} \<times>\<^sub>\<circ> z, set {0}, A]\<^sub>\<circ>"
  
  have R: "R : set {0} \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> A" 
  proof(intro smc_Rel_is_arrI)
    show "arr_Rel \<alpha> R"
      unfolding R_def
    proof(intro arr_Rel_vfsequenceI)
      from assms(2) show "\<R>\<^sub>\<circ> (set {0} \<times>\<^sub>\<circ> y) \<subseteq>\<^sub>\<circ> A" by auto
    qed (auto simp: T.arr_Rel_ArrDom_in_Vset)
  qed (simp_all add: R_def arr_Rel_components)

  from assms(3) have S: "S : set {0} \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> A"
  proof(intro smc_Rel_is_arrI)
    show "arr_Rel \<alpha> S"
      unfolding S_def
    proof(intro arr_Rel_vfsequenceI)
      from assms(3) show "\<R>\<^sub>\<circ> (set {0} \<times>\<^sub>\<circ> z) \<subseteq>\<^sub>\<circ> A" by auto
    qed (auto simp: T.arr_Rel_ArrDom_in_Vset)
  qed (simp_all add: S_def arr_Rel_components)

  from assms(4) have "T \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> R = [set {0} \<times>\<^sub>\<circ> X, set {0}, B]\<^sub>\<circ>"
    unfolding smc_Rel_Comp_app[OF T R]
    unfolding comp_Rel_components R_def comp_Rel_def arr_Rel_components
    by (simp add: vcomp_vimage_vtimes_right)
  moreover from assms have "T \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> S = [set {0} \<times>\<^sub>\<circ> X, set {0}, B]\<^sub>\<circ>"
    unfolding smc_Rel_Comp_app[OF T S]
    unfolding comp_Rel_components S_def comp_Rel_def arr_Rel_components
    by (simp add: vcomp_vimage_vtimes_right)
  ultimately have "T \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> R = T \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> S" by simp
  from R S assms(1) this have "R = S" by (elim is_monic_arrE)
  then show "y = z" unfolding R_def S_def by auto

qed

lemma (in \<Z>) smc_Rel_is_monic_arr:
  "T : A \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>smc_Rel \<alpha>\<^esub> B \<longleftrightarrow>
    T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B \<and>
    (
      \<forall>y z X.
        y \<subseteq>\<^sub>\<circ> A \<longrightarrow>
        z \<subseteq>\<^sub>\<circ> A \<longrightarrow>
        (T\<lparr>ArrVal\<rparr>) `\<^sub>\<circ> y = X \<longrightarrow>
        (T\<lparr>ArrVal\<rparr>) `\<^sub>\<circ> z = X \<longrightarrow>
        y = z
    )"
  by (rule iffI allI impI) 
    (auto simp: smc_Rel_is_monic_arrD smc_Rel_is_monic_arrI)

lemma (in \<Z>) smc_Rel_is_monic_arr_is_epic_arr: 
  assumes "T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B" 
    and "(\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)\<lparr>ArrMap\<rparr>\<lparr>T\<rparr> : B \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>smc_Rel \<alpha>\<^esub> A"
  shows "T : A \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>smc_Rel \<alpha>\<^esub> B"
proof-

  interpret is_iso_semifunctor \<alpha> \<open>op_smc (smc_Rel \<alpha>)\<close> \<open>smc_Rel \<alpha>\<close> \<open>\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<close>
    rewrites "(op_smc \<CC>')\<lparr>Obj\<rparr> = \<CC>'\<lparr>Obj\<rparr>" 
      and "(op_smc \<CC>')\<lparr>Arr\<rparr> = \<CC>'\<lparr>Arr\<rparr>"
      and "f : b \<mapsto>\<^bsub>op_smc \<CC>'\<^esub> a \<longleftrightarrow> f : a \<mapsto>\<^bsub>\<CC>'\<^esub> b" 
      for \<CC>' f a b
    unfolding smc_op_simps by (auto simp: smcf_dag_Rel_is_iso_semifunctor)
  
  show ?thesis
  proof(intro HomCod.is_epic_arrI)

    show T: "T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B" by (rule assms(1))
  
    fix f g a assume prems: 
      "f : B \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> a" 
      "g : B \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> a" 
      "f \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> T = g \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> T" 
  
    from prems(1) have "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> :
      \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>\<lparr>B\<rparr>"
      by (auto intro: smc_cs_intros)
    with prems(1) HomCod.smc_is_arrD(3) T have dag_f: 
      "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : a \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B" 
      unfolding smcf_dag_Rel_components(1) by auto
    from prems(2) have "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> : 
      \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>\<lparr>B\<rparr>"
      by (auto intro: smc_cs_intros)
    with prems(2) have dag_g: "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> : a \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B"
      unfolding smcf_dag_Rel_components(1) 
      by (metis HomCod.smc_is_arrD(3) T vid_on_eq_atI)
    from prems T have 
      "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr> \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = 
        \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr> \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>"
      by (simp add: smcf_dag_Rel_ArrMap_smc_Rel_Comp[symmetric])
    from is_monic_arrD(2)[OF assms(2) dag_f dag_g this] show "f = g"
      by (meson prems HomDom.smc_is_arrD(1) ArrMap.v11_eq_iff)
  
  qed
qed

lemma (in \<Z>) smc_Rel_is_epic_arr_is_monic_arr:
  assumes "T : A \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>smc_Rel \<alpha>\<^esub> B" 
  shows "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr> : B \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>smc_Rel \<alpha>\<^esub> A"
proof(rule is_monic_arrI)

  interpret is_iso_semifunctor \<alpha> \<open>op_smc (smc_Rel \<alpha>)\<close> \<open>smc_Rel \<alpha>\<close> \<open>\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<close> 
    rewrites "f : b \<mapsto>\<^bsub>op_smc \<CC>'\<^esub> a \<longleftrightarrow> f : a \<mapsto>\<^bsub>\<CC>'\<^esub> b" for \<CC>' f a b
    unfolding smc_op_simps by (auto simp: smcf_dag_Rel_is_iso_semifunctor)

  have dag: "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> : op_smc (smc_Rel \<alpha>) \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> smc_Rel \<alpha>" 
    by (auto intro: smc_cs_intros)

  from HomCod.is_epic_arrD(1)[OF assms] have T: "T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B".

  from T have "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr> : 
    \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>\<lparr>B\<rparr> \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr>"
    by (auto intro: smc_cs_intros)
  with T show dag_T: "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr> : B \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> A"
    unfolding smcf_dag_Rel_components(1)
    by (metis HomCod.smc_is_arrD(2) HomCod.smc_is_arrD(3) vid_on_eq_atI)

  fix f g a :: V
  assume prems:
    "f : a \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B" 
    "g : a \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B" 
    "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr> \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> f = \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr> \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> g" 
  then have a: "a \<in>\<^sub>\<circ> smc_Rel \<alpha>\<lparr>Obj\<rparr>" by auto
  from prems(1) have "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> :
    \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>\<lparr>B\<rparr> \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    by (auto intro: smc_cs_intros)
  with prems(1) have dag_f: "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : B \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> a"
    by (cs_concl cs_intro: smc_cs_intros cs_simp: smc_Rel_cs_simps)
  from prems(2) have "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> : 
    \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>\<lparr>B\<rparr> \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    by (cs_concl cs_intro: smc_cs_intros cs_simp:)
  with prems(2) have dag_g: "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> : B \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> a" 
    by (cs_concl cs_intro: smc_cs_intros cs_simp: smc_Rel_cs_simps)
  from T dag have 
    "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr>\<rparr> =
      (\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)\<lparr>ArrMap\<rparr>\<lparr>T\<rparr>"
    by
      (
        cs_concl
          cs_intro: smc_cs_intros 
          cs_simp: smc_Rel_cs_simps smc_cn_cs_simps smc_cs_simps
      )
  also from T have "\<dots> = T" 
    unfolding dghm_id_components smcf_cn_comp_smcf_dag_Rel_smcf_dag_Rel by auto
  finally have dag_dag_T: "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr>\<rparr> = T" by simp
  have 
    "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> T = \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> T"
    by (metis dag_T dag_dag_T prems smcf_dag_Rel_ArrMap_smc_Rel_Comp)
  from HomCod.is_epic_arrD(2)[OF assms dag_f dag_g this] prems ArrMap.v11_eq_iff
  show "f = g"
    by blast

qed

lemma (in \<Z>) smc_Rel_is_epic_arrI:
  assumes "T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B"  
    and "\<And>y z X. \<lbrakk> y \<subseteq>\<^sub>\<circ> B; z \<subseteq>\<^sub>\<circ> B; T\<lparr>ArrVal\<rparr> -`\<^sub>\<circ> y = X; T\<lparr>ArrVal\<rparr> -`\<^sub>\<circ> z = X \<rbrakk> \<Longrightarrow>
      y = z"
  shows "T : A \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>smc_Rel \<alpha>\<^esub> B"
proof-
  interpret is_iso_semifunctor \<alpha> \<open>op_smc (smc_Rel \<alpha>)\<close> \<open>smc_Rel \<alpha>\<close> \<open>\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<close> 
    rewrites "f : b \<mapsto>\<^bsub>op_smc \<CC>'\<^esub> a \<longleftrightarrow> f : a \<mapsto>\<^bsub>\<CC>'\<^esub> b" for \<CC>' f a b 
    unfolding smc_op_simps by (auto simp: smcf_dag_Rel_is_iso_semifunctor)
  from assms have T: "arr_Rel \<alpha> T" by (auto simp: smc_Rel_is_arrD(1))
  have "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr> : B \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>smc_Rel \<alpha>\<^esub> A"
  proof(rule smc_Rel_is_monic_arrI)
    from assms(1) have "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr> :
      \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>\<lparr>B\<rparr> \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr>"
      by (cs_concl cs_intro: smc_cs_intros)
    with assms(1) show "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr> : B \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> A"
      by (cs_concl cs_intro: smc_cs_intros cs_simp: smc_Rel_cs_simps)
    fix y z X
    assume
      "y \<subseteq>\<^sub>\<circ> B"
      "z \<subseteq>\<^sub>\<circ> B" 
      "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr>\<lparr>ArrVal\<rparr> `\<^sub>\<circ> y = X" 
      "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr>\<lparr>ArrVal\<rparr> `\<^sub>\<circ> z = X" 
    then show "y = z"
      unfolding 
        converse_Rel_components 
        smcf_dag_Rel_ArrMap_app[OF T] 
        app_invimage_def[symmetric]
      by (rule assms(2))
  qed
  from smc_Rel_is_monic_arr_is_epic_arr[OF assms(1) this] show ?thesis by simp
qed

lemma (in \<Z>) smc_Rel_is_epic_arrD[dest]:
  assumes "T : A \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>smc_Rel \<alpha>\<^esub> B"
    and "y \<subseteq>\<^sub>\<circ> B"
    and "z \<subseteq>\<^sub>\<circ> B" 
    and "T\<lparr>ArrVal\<rparr> -`\<^sub>\<circ> y = X" 
    and "T\<lparr>ArrVal\<rparr> -`\<^sub>\<circ> z = X" 
  shows "y = z"
proof-
  interpret is_iso_semifunctor \<alpha> \<open>op_smc (smc_Rel \<alpha>)\<close> \<open>smc_Rel \<alpha>\<close> \<open>\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<close> 
    rewrites "f : b \<mapsto>\<^bsub>op_smc \<CC>'\<^esub> a \<longleftrightarrow> f : a \<mapsto>\<^bsub>\<CC>'\<^esub> b" 
    for \<CC>' f a b 
    unfolding smc_op_simps by (auto simp: smcf_dag_Rel_is_iso_semifunctor)
  have dag_T: "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr> : B \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>smc_Rel \<alpha>\<^esub> A"
    by (rule smc_Rel_is_epic_arr_is_monic_arr[OF assms(1)])
  from HomCod.is_epic_arrD(1)[OF assms(1)] have T: "T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B".
  then have T: "arr_Rel \<alpha> T" by (auto simp: smc_Rel_is_arrD(1))
  from 
    assms(4,5) 
    smc_Rel_is_monic_arrD
      [
        OF dag_T assms(2,3), 
        unfolded 
          smc_dg_smc_Rel 
          smcf_dghm_smcf_dag_Rel 
          converse_Rel_components 
          smcf_dag_Rel_ArrMap_app[OF T]
      ]
  show ?thesis
    by (auto simp: app_invimage_def)
qed

lemma (in \<Z>) smc_Rel_is_epic_arr:
  "T : A \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>smc_Rel \<alpha>\<^esub> B \<longleftrightarrow>
    T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B \<and> 
      (
        \<forall>y z X.
          y \<subseteq>\<^sub>\<circ> B \<longrightarrow>
          z \<subseteq>\<^sub>\<circ> B \<longrightarrow>
          T\<lparr>ArrVal\<rparr> -`\<^sub>\<circ> y = X \<longrightarrow>
          T\<lparr>ArrVal\<rparr> -`\<^sub>\<circ> z = X \<longrightarrow>
          y = z
      )"
proof(intro iffI allI impI conjI)
  show "T : A \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>smc_Rel \<alpha>\<^esub> B \<Longrightarrow> T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B"
    by (simp add: is_epic_arr_def is_monic_arr_def op_smc_is_arr)
qed (auto simp: smc_Rel_is_epic_arrI)



subsection\<open>Terminal object, initial object and null object\<close>


text\<open>
An object in the semicategory \<open>Rel\<close> is terminal/initial/null if and only if 
it is the empty set (see
nLab \cite{noauthor_nlab_nodate})\footnote{
\url{https://ncatlab.org/nlab/show/database+of+categories}
}. 
\<close>

lemma (in \<Z>) smc_Rel_obj_terminal: "obj_terminal (smc_Rel \<alpha>) A \<longleftrightarrow> A = 0"
proof-

  interpret semicategory \<alpha> \<open>smc_Rel \<alpha>\<close> by (rule semicategory_smc_Rel)

  have "(\<forall>A\<in>\<^sub>\<circ>Vset \<alpha>. \<exists>!T. T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B) \<longleftrightarrow> B = 0" for B
  proof(intro iffI allI ballI)

    assume prems[rule_format]: "\<forall>A\<in>\<^sub>\<circ>Vset \<alpha>. \<exists>!T. T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B"

    then obtain T where "T : 0 \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B" by (meson vempty_is_zet)
    then have [simp]: "B \<in>\<^sub>\<circ> Vset \<alpha>" by (fastforce simp: smc_Rel_components(1))
    
    show "B = 0"
    proof(rule ccontr)
      assume "B \<noteq> 0"
      with trad_foundation obtain b where "b \<in>\<^sub>\<circ> B" by auto
      let ?b0B = \<open>[set {\<langle>0, b\<rangle>}, set {0}, B]\<^sub>\<circ>\<close>
      let ?z0B = \<open>[0, set {0}, B]\<^sub>\<circ>\<close>
      have "?b0B : set {0} \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B"
      proof(intro smc_Rel_is_arrI)
        show b0B: "arr_Rel \<alpha> ?b0B"
          by (intro arr_Rel_vfsequenceI)
            (force simp: \<open>b \<in>\<^sub>\<circ> B\<close> vsubset_vsingleton_leftI)+
      qed (simp_all add: arr_Rel_components)
      moreover have "?z0B : set {0} \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B"
      proof(intro smc_Rel_is_arrI)
        show b0B: "arr_Rel \<alpha> ?z0B"
          by (intro arr_Rel_vfsequenceI)
            (force simp: \<open>b \<in>\<^sub>\<circ> B\<close> vsubset_vsingleton_leftI)+
      qed (simp_all add: arr_Rel_components)
      moreover have "[set {\<langle>0, b\<rangle>}, set {0}, B]\<^sub>\<circ> \<noteq> [0, set {0}, B]\<^sub>\<circ>" by simp
      ultimately show False  
        by (metis prems smc_is_arrE smc_Rel_components(1))
    qed

  next

    fix A assume prems[simp]: "B = 0" "A \<in>\<^sub>\<circ> Vset \<alpha>" 
    let ?zAz = \<open>[0, A, 0]\<^sub>\<circ>\<close>
    have zAz: "arr_Rel \<alpha> ?zAz"
      by 
        (
          simp add: 
            \<Z>.arr_Rel_vfsequenceI 
            \<Z>_axioms 
            smc_Rel_components(2) 
            vbrelation_vempty
        )

    show "\<exists>!T. T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B"
    proof(rule ex1I[of _ \<open>?zAz\<close>])
      show "?zAz : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B"
        by (intro smc_Rel_is_arrI)
          (
            simp_all add: 
              zAz 
              smc_Rel_Dom_app[OF zAz] 
              smc_Rel_Cod_app[OF zAz] 
              arr_Rel_components
          )      
      fix T assume "T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B"
      then have T: "T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> 0" by simp
      then interpret T: arr_Rel \<alpha> T by (fastforce simp: smc_Rel_components(2))
      show "T = [0, A, 0]\<^sub>\<circ>"
      proof
        (
          subst T.arr_Rel_def, 
          rule arr_Rel_eqI[of \<alpha>], 
          unfold arr_Rel_components
        )
        show "arr_Rel \<alpha> [T\<lparr>ArrVal\<rparr>, T\<lparr>ArrDom\<rparr>, T\<lparr>ArrCod\<rparr>]\<^sub>\<circ>"
          by (fold T.arr_Rel_def) (simp add: T.arr_Rel_axioms)
        from zAz show "arr_Rel \<alpha> ?zAz" 
          by (simp add: arr_Rel_vfsequenceI vbrelationI)
        from T have "T \<in>\<^sub>\<circ> smc_Rel \<alpha>\<lparr>Arr\<rparr>" by (auto intro: smc_cs_intros)
        with is_arrD(2,3)[OF T] show "T\<lparr>ArrDom\<rparr> = A" "T\<lparr>ArrCod\<rparr> = 0"
          using T smc_Rel_is_arrD(2,3) by auto
        with T.arr_Rel_ArrVal_vrange T.ArrVal.vbrelation_vintersection_vrange 
        show "T\<lparr>ArrVal\<rparr> = []\<^sub>\<circ>"
          by auto
      qed

    qed

  qed

  then show ?thesis
    apply(intro iffI obj_terminalI)
    subgoal by (metis smc_is_arrD(2) obj_terminalE)
    subgoal by blast
    subgoal by (metis smc_Rel_components(1))
    done

qed

(*TODO: generalize: duality/dagger*)
lemma (in \<Z>) smc_Rel_obj_initial: "obj_initial (smc_Rel \<alpha>) A \<longleftrightarrow> A = 0"
proof-

  interpret semicategory \<alpha> \<open>smc_Rel \<alpha>\<close> by (rule semicategory_smc_Rel)

  have "(\<forall>B\<in>\<^sub>\<circ>Vset \<alpha>. \<exists>!T. T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B) \<longleftrightarrow> A = 0" for A
  proof(intro iffI allI ballI)

    assume prems[rule_format]: "\<forall>B\<in>\<^sub>\<circ>Vset \<alpha>. \<exists>!T. T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B" 

    then obtain T where TA0: "T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> 0" by (meson vempty_is_zet)
    then have [simp]: "A \<in>\<^sub>\<circ> Vset \<alpha>" by (fastforce simp: smc_Rel_components(1))

    show "A = 0"
    proof(rule ccontr)
      assume "A \<noteq> 0"
      with trad_foundation obtain a where "a \<in>\<^sub>\<circ> A" by auto
      have "[set {\<langle>a, 0\<rangle>}, A, set {0}]\<^sub>\<circ> : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> set {0}"
      proof(intro smc_Rel_is_arrI)
        show "arr_Rel \<alpha> [set {\<langle>a, 0\<rangle>}, A, set {0}]\<^sub>\<circ>"
          by (intro arr_Rel_vfsequenceI)
            (auto simp: \<open>a \<in>\<^sub>\<circ> A\<close> vsubset_vsingleton_leftI)
      qed (simp_all add: arr_Rel_components)
      moreover have "[0, A, set {0}]\<^sub>\<circ> : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> set {0}"
      proof(intro smc_Rel_is_arrI)
        show "arr_Rel \<alpha> [0, A, set {0}]\<^sub>\<circ>"
          by (intro arr_Rel_vfsequenceI)
            (auto simp: \<open>a \<in>\<^sub>\<circ> A\<close> vsubset_vsingleton_leftI)
      qed (simp_all add: arr_Rel_components)
      moreover have "[set {\<langle>a, 0\<rangle>}, A, set {0}]\<^sub>\<circ> \<noteq> [0, A, set {0}]\<^sub>\<circ>" by simp
      ultimately show False
        by (metis prems smc_is_arrE smc_Rel_components(1))
    qed
  next

    fix B assume [simp]: "A = 0" "B \<in>\<^sub>\<circ> Vset \<alpha>" 
    show "\<exists>!T. T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B"
    proof(rule ex1I[of _ \<open>[0, 0, B]\<^sub>\<circ>\<close>])
      show "[0, 0, B]\<^sub>\<circ> : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B"
        by (rule is_arrI)
          (
            simp_all add:
              smc_Rel_cs_simps
              smc_Rel_components(2) 
              vbrelation_vempty
              arr_Rel_vfsequenceI 
          )
      fix T assume "T : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B"
      then have T: "T : 0 \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B" by simp
      interpret T: arr_Rel \<alpha> T 
        using T by (fastforce simp: smc_Rel_components(2))
      show "T = [0, 0, B]\<^sub>\<circ>"
      proof
        (
          subst T.arr_Rel_def, 
          rule arr_Rel_eqI[of \<alpha>], 
          unfold arr_Rel_components
        )
        show "arr_Rel \<alpha> [T\<lparr>ArrVal\<rparr>, T\<lparr>ArrDom\<rparr>, T\<lparr>ArrCod\<rparr>]\<^sub>\<circ>"
          by (fold T.arr_Rel_def) (simp add: T.arr_Rel_axioms)
        show "arr_Rel \<alpha> [[]\<^sub>\<circ>, []\<^sub>\<circ>, B]\<^sub>\<circ>" 
          by (simp add: arr_Rel_vfsequenceI vbrelationI)
        from T have "T \<in>\<^sub>\<circ> smc_Rel \<alpha>\<lparr>Arr\<rparr>" by (auto intro: smc_cs_intros)
        with T is_arrD(2,3)[OF T] show "T\<lparr>ArrDom\<rparr> = 0" "T\<lparr>ArrCod\<rparr> = B"
          by (auto simp: smc_Rel_is_arrD(2,3))
        with 
          T.arr_Rel_ArrVal_vrange 
          T.arr_Rel_ArrVal_vdomain 
          T.ArrVal.vbrelation_vintersection_vdomain
        show "T\<lparr>ArrVal\<rparr> = []\<^sub>\<circ>"
          by auto
      qed
    qed
  qed

  then show ?thesis
    apply(intro iffI obj_initialI, elim obj_initialE)
    subgoal by (metis smc_Rel_components(1))
    subgoal by (simp add: smc_Rel_components(1))
    subgoal by (metis smc_Rel_components(1))
    done

qed

lemma (in \<Z>) smc_Rel_obj_terminal_obj_initial:
  "obj_initial (smc_Rel \<alpha>) A \<longleftrightarrow> obj_terminal (smc_Rel \<alpha>) A"
  unfolding smc_Rel_obj_initial smc_Rel_obj_terminal by simp

lemma (in \<Z>) smc_Rel_obj_null: "obj_null (smc_Rel \<alpha>) A \<longleftrightarrow> A = 0"
  unfolding obj_null_def smc_Rel_obj_terminal smc_Rel_obj_initial by simp



subsection\<open>Zero arrow\<close>


text\<open>
A zero arrow for \<open>Rel\<close> is any admissible \<open>V\<close>-arrow, such that its value 
is the empty set. A reference for this result is not given, but the 
result is not expected to be original.
\<close>

lemma (in \<Z>) smc_Rel_is_zero_arr: 
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" and "B \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "T : A \<mapsto>\<^sub>0\<^bsub>smc_Rel \<alpha>\<^esub> B \<longleftrightarrow> T = [0, A, B]\<^sub>\<circ>"
proof(rule HOL.ext iffI)

  interpret Rel: semicategory \<alpha> \<open>smc_Rel \<alpha>\<close> by (rule semicategory_smc_Rel)
  
  fix T A B assume "T : A \<mapsto>\<^sub>0\<^bsub>smc_Rel \<alpha>\<^esub> B"
  then obtain R S
    where T_def: "T = R \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> S" 
      and S: "S : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> 0" 
      and R: "R : 0 \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B"
    by (elim is_zero_arrE) (simp add: obj_null_def smc_Rel_obj_terminal)

  interpret S: arr_Rel \<alpha> S
    rewrites [simp]: "S\<lparr>ArrDom\<rparr> = A" and [simp]: "S\<lparr>ArrCod\<rparr> = 0"
    using S by (all\<open>elim Rel.smc_is_arrE\<close>) (simp_all add: smc_Rel_components)
  interpret R: arr_Rel \<alpha> R
    rewrites [simp]: "R\<lparr>ArrDom\<rparr> = 0" and [simp]: "R\<lparr>ArrCod\<rparr> = B"
    using R by (all\<open>elim Rel.smc_is_arrE\<close>) (simp_all add: smc_Rel_components)

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
          arr_Rel_vfsequenceI 
          vbrelationI
      )
  show "T = [0, A, B]\<^sub>\<circ>" 
     unfolding T_def smc_Rel_Comp_app[OF R S] 
     by (rule arr_Rel_eqI[of \<alpha>], unfold comp_Rel_components)
       (
         auto simp: 
          S_def 
          \<Z>_axioms
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

  assume prems: "T = [0, A, B]\<^sub>\<circ>"
  let ?S = \<open>[0, A, 0]\<^sub>\<circ>\<close> and ?R = \<open>[0, 0, B]\<^sub>\<circ>\<close>
  have S: "arr_Rel \<alpha> ?S" and R: "arr_Rel \<alpha> ?R" 
    by (all\<open>intro arr_Rel_vfsequenceI\<close>) (auto simp: assms)
  have SA0: "?S : A \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> 0"
    by (intro smc_Rel_is_arrI) (simp_all add: S arr_Rel_components)
  moreover have R0B: "?R : 0 \<mapsto>\<^bsub>smc_Rel \<alpha>\<^esub> B"
    by (intro smc_Rel_is_arrI) (simp_all add: R arr_Rel_components)
  moreover have "T = ?R \<circ>\<^sub>A\<^bsub>smc_Rel \<alpha>\<^esub> ?S" 
    unfolding smc_Rel_Comp_app[OF R0B SA0]
  proof(rule arr_Rel_eqI, unfold comp_Rel_components arr_Rel_components prems)
    show "arr_Rel \<alpha> [0, A, B]\<^sub>\<circ>"
      unfolding prems by (intro arr_Rel_vfsequenceI) (auto simp: assms)
  qed (use R S in \<open>auto simp: smc_Rel_cs_intros\<close>)
  ultimately show "T : A \<mapsto>\<^sub>0\<^bsub>smc_Rel \<alpha>\<^esub> B" 
    by (simp add: is_zero_arrI smc_Rel_obj_null)

qed

text\<open>\newpage\<close>

end