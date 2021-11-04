(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>FUNCT\<close> and \<open>Funct\<close> as semicategories\label{sec:smc_FUNCT}\<close>
theory CZH_SMC_FUNCT
  imports 
    CZH_DG_FUNCT
    CZH_Foundations.CZH_SMC_Subsemicategory
begin



subsection\<open>Background\<close>


text\<open>
The subsection presents the theory of the semicategories of \<open>\<alpha>\<close>-functors
between two \<open>\<alpha>\<close>-categories.
It continues the development that was initiated in section
\ref{sec:dg_FUNCT}.
A general reference for this section is Chapter II-4 in 
\cite{mac_lane_categories_2010}.
\<close>

named_theorems smc_FUNCT_cs_simps
named_theorems smc_FUNCT_cs_intros

lemmas [smc_FUNCT_cs_simps] = cat_map_cs_simps
lemmas [smc_FUNCT_cs_intros] =  cat_map_cs_intros



subsection\<open>\<open>FUNCT\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition smc_FUNCT :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "smc_FUNCT \<alpha> \<AA> \<BB> =
    [
      cf_maps \<alpha> \<AA> \<BB>,
      ntcf_arrows \<alpha> \<AA> \<BB>,
      (\<lambda>\<NN>\<in>\<^sub>\<circ>ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTDom\<rparr>),
      (\<lambda>\<NN>\<in>\<^sub>\<circ>ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTCod\<rparr>),
      (\<lambda>\<MM>\<NN>\<in>\<^sub>\<circ>composable_arrs (dg_FUNCT \<alpha> \<AA> \<BB>). \<MM>\<NN>\<lparr>0\<rparr> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>\<AA>,\<BB>\<^esub> \<MM>\<NN>\<lparr>1\<^sub>\<nat>\<rparr>)
    ]\<^sub>\<circ>"
                     

text\<open>Components.\<close>

lemma smc_FUNCT_components:
  shows "smc_FUNCT \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr> = cf_maps \<alpha> \<AA> \<BB>"
    and "smc_FUNCT \<alpha> \<AA> \<BB>\<lparr>Arr\<rparr> = ntcf_arrows \<alpha> \<AA> \<BB>"
    and "smc_FUNCT \<alpha> \<AA> \<BB>\<lparr>Dom\<rparr> = (\<lambda>\<NN>\<in>\<^sub>\<circ>ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTDom\<rparr>)"
    and "smc_FUNCT \<alpha> \<AA> \<BB>\<lparr>Cod\<rparr> = (\<lambda>\<NN>\<in>\<^sub>\<circ>ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTCod\<rparr>)"
    and "smc_FUNCT \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr> =
      (\<lambda>\<MM>\<NN>\<in>\<^sub>\<circ>composable_arrs (dg_FUNCT \<alpha> \<AA> \<BB>). \<MM>\<NN>\<lparr>0\<rparr> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>\<AA>,\<BB>\<^esub> \<MM>\<NN>\<lparr>1\<^sub>\<nat>\<rparr>)"
  unfolding smc_FUNCT_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smc_dg_FUNCT: "smc_dg (smc_FUNCT \<alpha> \<AA> \<BB>) = dg_FUNCT \<alpha> \<AA> \<BB>"
proof(rule vsv_eqI)
  show "vsv (smc_dg (smc_FUNCT \<alpha> \<AA> \<BB>))" unfolding smc_dg_def by auto
  show "vsv (dg_FUNCT \<alpha> \<AA> \<BB>)" unfolding dg_FUNCT_def by auto
  have dom_lhs: "\<D>\<^sub>\<circ> (smc_dg (smc_FUNCT \<alpha> \<AA> \<BB>)) = 4\<^sub>\<nat>" 
    unfolding smc_dg_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (dg_FUNCT \<alpha> \<AA> \<BB>) = 4\<^sub>\<nat>"
    unfolding dg_FUNCT_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (smc_dg (smc_FUNCT \<alpha> \<AA> \<BB>)) = \<D>\<^sub>\<circ> (dg_FUNCT \<alpha> \<AA> \<BB>)"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_dg (smc_FUNCT \<alpha> \<AA> \<BB>)) \<Longrightarrow> 
    smc_dg (smc_FUNCT \<alpha> \<AA> \<BB>)\<lparr>a\<rparr> = dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>a\<rparr>"
    for a
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral,
        unfold smc_dg_def dg_field_simps smc_FUNCT_def dg_FUNCT_def
      )
      (auto simp: nat_omega_simps)
qed

context is_ntcf
begin

lemmas_with [folded smc_dg_FUNCT, unfolded slicing_simps]: 
  smc_FUNCT_Dom_app = dg_FUNCT_Dom_app
  and smc_FUNCT_Cod_app = dg_FUNCT_Cod_app

end

lemmas [smc_FUNCT_cs_simps] = 
  is_ntcf.smc_FUNCT_Dom_app
  is_ntcf.smc_FUNCT_Cod_app

lemmas_with [folded smc_dg_FUNCT, unfolded slicing_simps]: 
  smc_FUNCT_Dom_vsv[intro] = dg_FUNCT_Dom_vsv
  and smc_FUNCT_Dom_vdomain[smc_FUNCT_cs_simps] = dg_FUNCT_Dom_vdomain
  and smc_FUNCT_Cod_vsv[intro] = dg_FUNCT_Cod_vsv
  and smc_FUNCT_Cod_vdomain[smc_FUNCT_cs_simps] = dg_FUNCT_Cod_vdomain
  and smc_FUNCT_Dom_vrange = dg_FUNCT_Dom_vrange
  and smc_FUNCT_Cod_vrange = dg_FUNCT_Cod_vrange
  and smc_FUNCT_is_arrI = dg_FUNCT_is_arrI
  and smc_FUNCT_is_arrI'[smc_FUNCT_cs_intros] = dg_FUNCT_is_arrI'
  and smc_FUNCT_is_arrD = dg_FUNCT_is_arrD
  and smc_FUNCT_is_arrE[elim] = dg_FUNCT_is_arrE



subsubsection\<open>Composable arrows\<close>

lemma smc_FUNCT_composable_arrs_dg_FUNCT: 
  "composable_arrs (dg_FUNCT \<alpha> \<AA> \<BB>) = composable_arrs (smc_FUNCT \<alpha> \<AA> \<BB>)"
  unfolding composable_arrs_def smc_dg_FUNCT[symmetric] slicing_simps by auto

lemma smc_FUNCT_Comp: 
  "smc_FUNCT \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr> =
    (\<lambda>\<GG>\<FF>\<in>\<^sub>\<circ>composable_arrs (smc_FUNCT \<alpha> \<AA> \<BB>). \<GG>\<FF>\<lparr>0\<rparr> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>\<AA>,\<BB>\<^esub> \<GG>\<FF>\<lparr>1\<^sub>\<nat>\<rparr>)"
  unfolding smc_FUNCT_components smc_FUNCT_composable_arrs_dg_FUNCT ..


subsubsection\<open>Composition\<close>

lemma smc_FUNCT_Comp_vsv[intro]: "vsv (smc_FUNCT \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr>)" 
  unfolding smc_FUNCT_Comp by simp

lemma smc_FUNCT_Comp_vdomain:
  "\<D>\<^sub>\<circ> (smc_FUNCT \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr>) = composable_arrs (smc_FUNCT \<alpha> \<AA> \<BB>)" 
  unfolding smc_FUNCT_Comp by auto

lemma smc_FUNCT_Comp_app[smc_FUNCT_cs_simps]:
  assumes "\<MM> : \<GG> \<mapsto>\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<HH>" and "\<NN> : \<FF> \<mapsto>\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<GG>"
  shows "\<MM> \<circ>\<^sub>A\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<NN> = \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>\<AA>,\<BB>\<^esub> \<NN>"
proof-
  from assms have "[\<MM>, \<NN>]\<^sub>\<circ> \<in>\<^sub>\<circ> composable_arrs (smc_FUNCT \<alpha> \<AA> \<BB>)" 
    by (auto intro: smc_cs_intros)
  then show "\<MM> \<circ>\<^sub>A\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<NN> = \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>\<AA>,\<BB>\<^esub> \<NN>"
    unfolding smc_FUNCT_Comp by (simp add: nat_omega_simps)
qed

lemma smc_FUNCT_Comp_vrange: "\<R>\<^sub>\<circ> (smc_FUNCT \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr>) \<subseteq>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>"
proof(rule vsubsetI)
  fix \<LL> assume prems: "\<LL> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (smc_FUNCT \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr>)"
  then obtain \<MM>\<NN>
    where \<LL>_def: "\<LL> = smc_FUNCT \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr>\<lparr>\<MM>\<NN>\<rparr>" 
      and "\<MM>\<NN> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_FUNCT \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr>)"
    unfolding smc_FUNCT_components by (auto intro: smc_cs_intros)
  then obtain \<MM> \<NN> \<FF> \<GG> \<HH> 
    where "\<MM>\<NN> = [\<MM>, \<NN>]\<^sub>\<circ>" 
      and \<MM>: "\<MM> : \<GG> \<mapsto>\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<HH>" 
      and \<NN>: "\<NN> : \<FF> \<mapsto>\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<GG>"
    by (auto simp: smc_FUNCT_Comp_vdomain) 
  with \<LL>_def have \<LL>_def': "\<LL> = \<MM> \<circ>\<^sub>A\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<NN>" by simp
  note \<MM> = smc_FUNCT_is_arrD[OF \<MM>]
    and \<NN> = smc_FUNCT_is_arrD[OF \<NN>]
  from \<MM>(1) \<NN>(1) show "\<LL> \<in>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>" 
    unfolding \<LL>_def'
    by (subst \<MM>(2), subst \<NN>(2), remdups)
      (
        cs_concl 
          cs_simp: smc_FUNCT_cs_simps cs_intro: cat_cs_intros smc_FUNCT_cs_intros
      )
qed


subsubsection\<open>\<open>FUNCT\<close> is a semicategory\<close>

lemma (in \<Z>) tiny_semicategory_smc_FUNCT: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "tiny_semicategory \<beta> (smc_FUNCT \<alpha> \<AA> \<BB>)"
proof(intro tiny_semicategoryI)
  show "vfsequence (smc_FUNCT \<alpha> \<AA> \<BB>)" by (simp add: smc_FUNCT_def)
  show "vcard (smc_FUNCT \<alpha> \<AA> \<BB>) = 5\<^sub>\<nat>"
    unfolding smc_FUNCT_def by (simp add: nat_omega_simps)
  show "(\<MM>\<NN> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_FUNCT \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr>)) =
    (
      \<exists>\<MM> \<NN> \<GG> \<HH> \<FF>.
        \<MM>\<NN> = [\<MM>, \<NN>]\<^sub>\<circ> \<and>
        \<MM> : \<GG> \<mapsto>\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<HH> \<and>
        \<NN> : \<FF> \<mapsto>\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<GG>
    )"
    for \<MM>\<NN> 
    unfolding smc_FUNCT_Comp by (auto intro: smc_cs_intros)
  show Comp_is_arr: "\<MM> \<circ>\<^sub>A\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<NN> : \<FF> \<mapsto>\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<HH>"
    if "\<MM> : \<GG> \<mapsto>\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<HH>" and "\<NN> : \<FF> \<mapsto>\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<GG>"
    for \<MM> \<GG> \<HH> \<NN> \<FF>
  proof-
    note g = smc_FUNCT_is_arrD[OF that(1)]
    note f = smc_FUNCT_is_arrD[OF that(2)]
    from g(1) f(1) show "\<MM> \<circ>\<^sub>A\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<NN> : \<FF> \<mapsto>\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<HH>"
      by (subst g(2), subst g(4), subst f(2), subst f(3), remdups)
        (
          cs_concl 
            cs_simp: smc_FUNCT_cs_simps
            cs_intro: smc_FUNCT_cs_intros cat_cs_intros
        )
  qed
  fix \<LL> \<HH> \<KK> \<MM> \<GG> \<NN> \<FF>
  assume prems:
    "\<LL> : \<HH> \<mapsto>\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<KK>"
    "\<MM> : \<GG> \<mapsto>\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<HH>"
    "\<NN> : \<FF> \<mapsto>\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<GG>"
  note \<LL> = smc_FUNCT_is_arrD[OF prems(1)]
  note \<MM> = smc_FUNCT_is_arrD[OF prems(2)]
  note \<NN> = smc_FUNCT_is_arrD[OF prems(3)]
  from \<LL>(1) \<MM>(1) \<NN>(1) show 
    "(\<LL> \<circ>\<^sub>A\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<MM>) \<circ>\<^sub>A\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<NN> =
      \<LL> \<circ>\<^sub>A\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> (\<MM> \<circ>\<^sub>A\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<NN>)"    
    by (subst (1 2) \<LL>(2), subst (1 2) \<MM>(2), subst (1 2) \<NN>(2), remdups)
      (
        cs_concl 
          cs_simp: smc_FUNCT_cs_simps cat_cs_simps 
          cs_intro: smc_FUNCT_cs_intros cat_cs_intros
      )
qed 
  (
    simp_all add: 
      assms 
      smc_dg_FUNCT 
      smc_FUNCT_components 
      tiny_digraph_dg_FUNCT[OF assms(1,2)]  
  ) 



subsection\<open>\<open>Funct\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition smc_Funct :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "smc_Funct \<alpha> \<AA> \<BB> =
    [
      tm_cf_maps \<alpha> \<AA> \<BB>,
      tm_ntcf_arrows \<alpha> \<AA> \<BB>,
      (\<lambda>\<NN>\<in>\<^sub>\<circ>tm_ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTDom\<rparr>),
      (\<lambda>\<NN>\<in>\<^sub>\<circ>tm_ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTCod\<rparr>),
      (\<lambda>\<MM>\<NN>\<in>\<^sub>\<circ>composable_arrs (dg_Funct \<alpha> \<AA> \<BB>). \<MM>\<NN>\<lparr>0\<rparr> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>\<AA>,\<BB>\<^esub> \<MM>\<NN>\<lparr>1\<^sub>\<nat>\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smc_Funct_components: 
  shows "smc_Funct \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr> = tm_cf_maps \<alpha> \<AA> \<BB>"
    and "smc_Funct \<alpha> \<AA> \<BB>\<lparr>Arr\<rparr> = tm_ntcf_arrows \<alpha> \<AA> \<BB>"
    and "smc_Funct \<alpha> \<AA> \<BB>\<lparr>Dom\<rparr> = (\<lambda>\<NN>\<in>\<^sub>\<circ>tm_ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTDom\<rparr>)"
    and "smc_Funct \<alpha> \<AA> \<BB>\<lparr>Cod\<rparr> = (\<lambda>\<NN>\<in>\<^sub>\<circ>tm_ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTCod\<rparr>)"
    and "smc_Funct \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr> =
      (\<lambda>\<MM>\<NN>\<in>\<^sub>\<circ>composable_arrs (dg_Funct \<alpha> \<AA> \<BB>). \<MM>\<NN>\<lparr>0\<rparr> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>\<AA>,\<BB>\<^esub> \<MM>\<NN>\<lparr>1\<^sub>\<nat>\<rparr>)"
  unfolding smc_Funct_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smc_dg_Funct: "smc_dg (smc_Funct \<alpha> \<AA> \<BB>) = dg_Funct \<alpha> \<AA> \<BB>"
proof(rule vsv_eqI)
  show "vsv (smc_dg (smc_Funct \<alpha> \<AA> \<BB>))" unfolding smc_dg_def by auto
  show "vsv (dg_Funct \<alpha> \<AA> \<BB>)" unfolding dg_Funct_def by auto
  have dom_lhs: "\<D>\<^sub>\<circ> (smc_dg (smc_Funct \<alpha> \<AA> \<BB>)) = 4\<^sub>\<nat>" 
    unfolding smc_dg_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (dg_Funct \<alpha> \<AA> \<BB>) = 4\<^sub>\<nat>"
    unfolding dg_Funct_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (smc_dg (smc_Funct \<alpha> \<AA> \<BB>)) = \<D>\<^sub>\<circ> (dg_Funct \<alpha> \<AA> \<BB>)"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_dg (smc_Funct \<alpha> \<AA> \<BB>)) \<Longrightarrow>
    smc_dg (smc_Funct \<alpha> \<AA> \<BB>)\<lparr>a\<rparr> = dg_Funct \<alpha> \<AA> \<BB>\<lparr>a\<rparr>"
    for a
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral,
        unfold smc_dg_def dg_field_simps smc_Funct_def dg_Funct_def
      )
      (auto simp: nat_omega_simps)
qed

context is_tm_ntcf
begin

lemmas_with [folded smc_dg_Funct, unfolded slicing_simps]: 
  smc_Funct_Dom_app = dg_Funct_Dom_app
  and smc_Funct_Cod_app = dg_Funct_Cod_app

end

lemmas [smc_FUNCT_cs_simps] = 
  is_tm_ntcf.smc_Funct_Dom_app
  is_tm_ntcf.smc_Funct_Cod_app

lemmas_with [folded smc_dg_Funct, unfolded slicing_simps]: 
  smc_Funct_Dom_vsv[intro] = dg_Funct_Dom_vsv
  and smc_Funct_Dom_vdomain[smc_FUNCT_cs_simps] = dg_Funct_Dom_vdomain
  and smc_Funct_Cod_vsv[intro] = dg_Funct_Cod_vsv
  and smc_Funct_Cod_vdomain[smc_FUNCT_cs_simps] = dg_Funct_Cod_vdomain
  and smc_Funct_Dom_vrange = dg_Funct_Dom_vrange
  and smc_Funct_Cod_vrange = dg_Funct_Cod_vrange
  and smc_Funct_is_arrI = dg_Funct_is_arrI
  and smc_Funct_is_arrI'[smc_FUNCT_cs_intros] = dg_Funct_is_arrI'
  and smc_Funct_is_arrD = dg_Funct_is_arrD
  and smc_Funct_is_arrE[elim] = dg_Funct_is_arrE


subsubsection\<open>Composable arrows\<close>

lemma smc_Funct_composable_arrs_dg_FUNCT: 
  "composable_arrs (dg_Funct \<alpha> \<AA> \<BB>) = composable_arrs (smc_Funct \<alpha> \<AA> \<BB>)"
  unfolding composable_arrs_def smc_dg_Funct[symmetric] slicing_simps by auto

lemma smc_Funct_Comp: 
  "smc_Funct \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr> =
    (\<lambda>\<GG>\<FF>\<in>\<^sub>\<circ>composable_arrs (smc_Funct \<alpha> \<AA> \<BB>). \<GG>\<FF>\<lparr>0\<rparr> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>\<AA>,\<BB>\<^esub> \<GG>\<FF>\<lparr>1\<^sub>\<nat>\<rparr>)"
  unfolding smc_Funct_components smc_Funct_composable_arrs_dg_FUNCT ..


subsubsection\<open>Composition\<close>

lemma smc_Funct_Comp_vsv[intro]: "vsv (smc_Funct \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr>)" 
  unfolding smc_Funct_Comp by simp

lemma smc_Funct_Comp_vdomain:
  "\<D>\<^sub>\<circ> (smc_Funct \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr>) = composable_arrs (smc_Funct \<alpha> \<AA> \<BB>)" 
  unfolding smc_Funct_Comp by auto

lemma smc_Funct_Comp_app[smc_FUNCT_cs_simps]:
  assumes "\<MM> : \<GG> \<mapsto>\<^bsub>smc_Funct \<alpha> \<AA> \<BB>\<^esub> \<HH>" and "\<NN> : \<FF> \<mapsto>\<^bsub>smc_Funct \<alpha> \<AA> \<BB>\<^esub> \<GG>"
  shows "\<MM> \<circ>\<^sub>A\<^bsub>smc_Funct \<alpha> \<AA> \<BB>\<^esub> \<NN> = \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>\<AA>,\<BB>\<^esub> \<NN>"
proof-
  from assms have "[\<MM>, \<NN>]\<^sub>\<circ> \<in>\<^sub>\<circ> composable_arrs (smc_Funct \<alpha> \<AA> \<BB>)" 
    by (auto intro: smc_cs_intros)
  then show "\<MM> \<circ>\<^sub>A\<^bsub>smc_Funct \<alpha> \<AA> \<BB>\<^esub> \<NN> = \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>\<AA>,\<BB>\<^esub> \<NN>"
    unfolding smc_Funct_Comp by (simp add: nat_omega_simps)
qed

lemma smc_Funct_Comp_vrange: 
  assumes "category \<alpha> \<BB>"
  shows "\<R>\<^sub>\<circ> (smc_Funct \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr>) \<subseteq>\<^sub>\<circ> tm_ntcf_arrows \<alpha> \<AA> \<BB>"
proof(rule vsubsetI)
  fix \<LL> assume "\<LL> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (smc_Funct \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr>)"
  then obtain \<MM>\<NN>
    where \<LL>_def: "\<LL> = smc_Funct \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr>\<lparr>\<MM>\<NN>\<rparr>" 
      and "\<MM>\<NN> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_Funct \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr>)"
    unfolding smc_Funct_components 
    by (auto intro: smc_cs_intros)
  then obtain \<MM> \<NN> \<FF> \<GG> \<HH> 
    where "\<MM>\<NN> = [\<MM>, \<NN>]\<^sub>\<circ>" 
      and \<MM>: "\<MM> : \<GG> \<mapsto>\<^bsub>smc_Funct \<alpha> \<AA> \<BB>\<^esub> \<HH>" 
      and \<NN>: "\<NN> : \<FF> \<mapsto>\<^bsub>smc_Funct \<alpha> \<AA> \<BB>\<^esub> \<GG>"
    by (auto simp: smc_Funct_Comp_vdomain) 
  with \<LL>_def have \<LL>_def': "\<LL> = \<MM> \<circ>\<^sub>A\<^bsub>smc_Funct \<alpha> \<AA> \<BB>\<^esub> \<NN>" by simp
  note \<MM> = smc_Funct_is_arrD[OF \<MM>]
    and \<NN> = smc_Funct_is_arrD[OF \<NN>]
  from assms \<MM>(1) \<NN>(1) show "\<LL> \<in>\<^sub>\<circ> tm_ntcf_arrows \<alpha> \<AA> \<BB>" 
    unfolding \<LL>_def'
    by (subst \<MM>(2), use nothing in \<open>subst \<NN>(2)\<close>)
      (
        cs_concl 
          cs_simp: smc_FUNCT_cs_simps 
          cs_intro: smc_FUNCT_cs_intros cat_small_cs_intros
      )
qed


subsubsection\<open>\<open>Funct\<close> is a semicategory\<close>

lemma semicategory_smc_Funct:
  assumes "tiny_category \<alpha> \<AA>" and "category \<alpha> \<BB>"
  shows "semicategory \<alpha> (smc_Funct \<alpha> \<AA> \<BB>)" (is \<open>semicategory \<alpha> ?Funct\<close>)
proof-
  interpret tiny_category \<alpha> \<AA> by (rule assms(1))
  show ?thesis
  proof(intro semicategoryI)
    show "vfsequence ?Funct" by (simp add: smc_Funct_def)
    show "vcard ?Funct = 5\<^sub>\<nat>" 
      unfolding smc_Funct_def by (simp add: nat_omega_simps)
    show "(\<MM>\<NN> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_Funct \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr>)) =
      (\<exists>\<MM> \<NN> \<GG> \<HH> \<FF>. \<MM>\<NN> = [\<MM>, \<NN>]\<^sub>\<circ> \<and> \<MM> : \<GG> \<mapsto>\<^bsub>?Funct\<^esub> \<HH> \<and> \<NN> : \<FF> \<mapsto>\<^bsub>?Funct\<^esub> \<GG>)"
      for \<MM>\<NN> 
      unfolding smc_Funct_Comp by (auto intro: smc_cs_intros)
    show Comp_is_arr: "\<MM> \<circ>\<^sub>A\<^bsub>?Funct\<^esub> \<NN> : \<FF> \<mapsto>\<^bsub>?Funct\<^esub> \<HH>"
      if "\<MM> : \<GG> \<mapsto>\<^bsub>?Funct\<^esub> \<HH>" and "\<NN> : \<FF> \<mapsto>\<^bsub>?Funct\<^esub> \<GG>"
      for \<MM> \<GG> \<HH> \<NN> \<FF>
    proof-
      note \<MM> = smc_Funct_is_arrD[OF that(1)]
      note \<NN> = smc_Funct_is_arrD[OF that(2)]
      from assms \<MM>(1) \<NN>(1) show 
        "\<MM> \<circ>\<^sub>A\<^bsub>?Funct\<^esub> \<NN> : \<FF> \<mapsto>\<^bsub>?Funct\<^esub> \<HH>"
        by (subst \<MM>(2), use nothing in \<open>subst \<MM>(4), subst \<NN>(2), subst \<NN>(3)\<close>)
          (
            cs_concl 
              cs_simp: smc_FUNCT_cs_simps 
              cs_intro: smc_FUNCT_cs_intros cat_small_cs_intros
          )
    qed
    show "\<LL> \<circ>\<^sub>A\<^bsub>?Funct\<^esub> \<MM> \<circ>\<^sub>A\<^bsub>?Funct\<^esub> \<NN> = \<LL> \<circ>\<^sub>A\<^bsub>?Funct\<^esub> (\<MM> \<circ>\<^sub>A\<^bsub>?Funct\<^esub> \<NN>)"
      if "\<LL> : \<HH> \<mapsto>\<^bsub>?Funct\<^esub> \<KK>" "\<MM> : \<GG> \<mapsto>\<^bsub>?Funct\<^esub> \<HH>" "\<NN> : \<FF> \<mapsto>\<^bsub>?Funct\<^esub> \<GG>"
      for \<LL> \<HH> \<KK> \<MM> \<GG> \<NN> \<FF>
    proof-
      note \<LL> = smc_Funct_is_arrD[OF that(1)]
      note \<MM> = smc_Funct_is_arrD[OF that(2)]
      note \<NN> = smc_Funct_is_arrD[OF that(3)]
      from assms \<LL>(1) \<MM>(1) \<NN>(1) show
        "(\<LL> \<circ>\<^sub>A\<^bsub>?Funct\<^esub> \<MM>) \<circ>\<^sub>A\<^bsub>?Funct\<^esub> \<NN> = \<LL> \<circ>\<^sub>A\<^bsub>?Funct\<^esub> (\<MM> \<circ>\<^sub>A\<^bsub>?Funct\<^esub> \<NN>)"    
        by 
          (
            subst (1 2) \<LL>(2),
            use nothing in \<open>subst (1 2) \<MM>(2), subst (1 2) \<NN>(2)\<close>
          )
          (
            cs_concl
              cs_simp: smc_FUNCT_cs_simps cat_cs_simps cat_small_cs_simps 
              cs_intro: smc_FUNCT_cs_intros cat_cs_intros cat_small_cs_intros
          )
    qed
  qed (auto simp: assms smc_dg_Funct smc_Funct_components digraph_dg_Funct)
qed


subsubsection\<open>\<open>Funct\<close> is a subsemicategory of \<open>FUNCT\<close>\<close>

lemma subsemicategory_smc_Funct_smc_FUNCT:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" and "tiny_category \<alpha> \<AA>" and "category \<alpha> \<BB>"
  shows "smc_Funct \<alpha> \<AA> \<BB> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<beta>\<^esub> smc_FUNCT \<alpha> \<AA> \<BB>"
proof(intro subsemicategoryI, unfold smc_dg_FUNCT smc_dg_Funct)
  interpret category \<alpha> \<BB> by (rule assms(4))
  interpret smc_Funct: semicategory \<alpha> \<open>smc_Funct \<alpha> \<AA> \<BB>\<close>
    by (rule semicategory_smc_Funct[OF assms(3,4)])
  show "semicategory \<beta> (smc_Funct \<alpha> \<AA> \<BB>)"
    by (rule semicategory.smc_semicategory_if_ge_Limit[OF _ assms(1,2)]) 
      (auto simp: smc_cs_simps intro: smc_cs_intros)
  from assms show "semicategory \<beta> (smc_FUNCT \<alpha> \<AA> \<BB>)"
    by 
      (
        cs_concl
          cs_intro: smc_small_cs_intros tiny_semicategory_smc_FUNCT
      )
  show "dg_Funct \<alpha> \<AA> \<BB> \<subseteq>\<^sub>D\<^sub>G\<^bsub>\<beta>\<^esub> dg_FUNCT \<alpha> \<AA> \<BB>"
    by (rule subdigraph_dg_Funct_dg_FUNCT[OF assms])
  show "\<MM> \<circ>\<^sub>A\<^bsub>smc_Funct \<alpha> \<AA> \<BB>\<^esub> \<NN> = \<MM> \<circ>\<^sub>A\<^bsub>smc_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<NN>"
    if "\<MM> : \<GG> \<mapsto>\<^bsub>smc_Funct \<alpha> \<AA> \<BB>\<^esub> \<HH>" and "\<NN> : \<FF> \<mapsto>\<^bsub>smc_Funct \<alpha> \<AA> \<BB>\<^esub> \<GG>"
    for \<GG> \<HH> \<MM> \<FF> \<NN>
  proof-
    note \<MM> = smc_Funct_is_arrD[OF that(1)]
    note \<NN> = smc_Funct_is_arrD[OF that(2)]
    from \<MM>(1) \<NN>(1) show ?thesis
      by (subst (1 2) \<MM>(2), use nothing in \<open>subst (1 2) \<NN>(2)\<close>)
        (
          cs_concl 
            cs_simp: smc_FUNCT_cs_simps cat_small_cs_simps 
            cs_intro: smc_FUNCT_cs_intros cat_small_cs_intros
        )
  qed
qed

text\<open>\newpage\<close>

end