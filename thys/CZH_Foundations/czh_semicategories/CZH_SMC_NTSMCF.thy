(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Natural transformation of a semifunctor\<close>
theory CZH_SMC_NTSMCF
  imports 
    CZH_SMC_Semifunctor
    CZH_DG_TDGHM
begin



subsection\<open>Background\<close>

named_theorems ntsmcf_cs_simps
named_theorems ntsmcf_cs_intros

lemmas [smc_cs_simps] = dg_shared_cs_simps
lemmas [smc_cs_intros] = dg_shared_cs_intros


subsubsection\<open>Slicing\<close>

definition ntsmcf_tdghm :: "V \<Rightarrow> V"
  where "ntsmcf_tdghm \<NN> = 
    [
      \<NN>\<lparr>NTMap\<rparr>, 
      smcf_dghm (\<NN>\<lparr>NTDom\<rparr>),
      smcf_dghm (\<NN>\<lparr>NTCod\<rparr>),
      smc_dg (\<NN>\<lparr>NTDGDom\<rparr>),
      smc_dg (\<NN>\<lparr>NTDGCod\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma ntsmcf_tdghm_components:
  shows [slicing_simps]: "ntsmcf_tdghm \<NN>\<lparr>NTMap\<rparr> = \<NN>\<lparr>NTMap\<rparr>"
    and [slicing_commute]: "ntsmcf_tdghm \<NN>\<lparr>NTDom\<rparr> = smcf_dghm (\<NN>\<lparr>NTDom\<rparr>)"
    and [slicing_commute]: "ntsmcf_tdghm \<NN>\<lparr>NTCod\<rparr> = smcf_dghm (\<NN>\<lparr>NTCod\<rparr>)"
    and [slicing_commute]: "ntsmcf_tdghm \<NN>\<lparr>NTDGDom\<rparr> = smc_dg (\<NN>\<lparr>NTDGDom\<rparr>)"
    and [slicing_commute]: "ntsmcf_tdghm \<NN>\<lparr>NTDGCod\<rparr> = smc_dg (\<NN>\<lparr>NTDGCod\<rparr>)"
  unfolding ntsmcf_tdghm_def nt_field_simps by (auto simp: nat_omega_simps)



subsection\<open>Definition and elementary properties\<close>


text\<open>
A natural transformation of semifunctors, as presented in this work,
is a generalization of the concept of a natural transformation, as presented in
Chapter I-4 in \cite{mac_lane_categories_2010}, to semicategories and
semifunctors.
\<close>

locale is_ntsmcf = 
  \<Z> \<alpha> + 
  vfsequence \<NN> + 
  NTDom: is_semifunctor \<alpha> \<AA> \<BB> \<FF> + 
  NTCod: is_semifunctor \<alpha> \<AA> \<BB> \<GG>
  for \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> +
  assumes ntsmcf_length[smc_cs_simps]: "vcard \<NN> = 5\<^sub>\<nat>"  
    and ntsmcf_is_tdghm[slicing_intros]: "ntsmcf_tdghm \<NN> :
      smcf_dghm \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M smcf_dghm \<GG> : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg \<BB>"
    and ntsmcf_NTDom[smc_cs_simps]: "\<NN>\<lparr>NTDom\<rparr> = \<FF>"
    and ntsmcf_NTCod[smc_cs_simps]: "\<NN>\<lparr>NTCod\<rparr> = \<GG>"
    and ntsmcf_NTDGDom[smc_cs_simps]: "\<NN>\<lparr>NTDGDom\<rparr> = \<AA>"
    and ntsmcf_NTDGCod[smc_cs_simps]: "\<NN>\<lparr>NTDGCod\<rparr> = \<BB>"
    and ntsmcf_Comp_commute[smc_cs_intros]: "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b \<Longrightarrow>
      \<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>" 

syntax "_is_ntsmcf" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F _ :/ _ \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> 
  "CONST is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>"

abbreviation all_ntsmcfs :: "V \<Rightarrow> V"
  where "all_ntsmcfs \<alpha> \<equiv> set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation ntsmcfs :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "ntsmcfs \<alpha> \<AA> \<BB> \<equiv> set {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation these_ntsmcfs :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "these_ntsmcfs \<alpha> \<AA> \<BB> \<FF> \<GG> \<equiv> set {\<NN>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"

lemmas [smc_cs_simps] =
  is_ntsmcf.ntsmcf_length
  is_ntsmcf.ntsmcf_NTDom
  is_ntsmcf.ntsmcf_NTCod
  is_ntsmcf.ntsmcf_NTDGDom
  is_ntsmcf.ntsmcf_NTDGCod
  is_ntsmcf.ntsmcf_Comp_commute

lemmas [smc_cs_intros] = is_ntsmcf.ntsmcf_Comp_commute

lemma (in is_ntsmcf) ntsmcf_is_tdghm':
  assumes "\<FF>' = smcf_dghm \<FF>"
    and "\<GG>' = smcf_dghm \<GG>"
    and "\<AA>' = smc_dg \<AA>"
    and "\<BB>' = smc_dg \<BB>"
  shows "ntsmcf_tdghm \<NN> : \<FF>' \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms(1-4) by (rule ntsmcf_is_tdghm)

lemmas [slicing_intros] = is_ntsmcf.ntsmcf_is_tdghm'


text\<open>Rules.\<close>

lemma (in is_ntsmcf) is_ntsmcf_axioms'[smc_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>" and "\<FF>' = \<FF>" and "\<GG>' = \<GG>"
  shows "\<NN> : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_ntsmcf_axioms)

mk_ide rf is_ntsmcf_def[unfolded is_ntsmcf_axioms_def]
  |intro is_ntsmcfI|
  |dest is_ntsmcfD[dest]|
  |elim is_ntsmcfE[elim]|

lemmas [smc_cs_intros] = 
  is_ntsmcfD(3,4)

lemma is_ntsmcfI':
  assumes "\<Z> \<alpha>"
    and "vfsequence \<NN>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "vcard \<NN> = 5\<^sub>\<nat>"
    and "\<NN>\<lparr>NTDom\<rparr> = \<FF>"
    and "\<NN>\<lparr>NTCod\<rparr> = \<GG>"
    and "\<NN>\<lparr>NTDGDom\<rparr> = \<AA>"
    and "\<NN>\<lparr>NTDGCod\<rparr> = \<BB>"
    and "vsv (\<NN>\<lparr>NTMap\<rparr>)"
    and "\<D>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    and "\<And>a. a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<Longrightarrow> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "\<And>a b f. f : a \<mapsto>\<^bsub>\<AA>\<^esub> b \<Longrightarrow>
      \<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  by (intro is_ntsmcfI is_tdghmI, unfold ntsmcf_tdghm_components slicing_simps)
    (
      simp_all add: 
        assms nat_omega_simps 
        ntsmcf_tdghm_def  
        is_semifunctorD(6)[OF assms(3)] 
        is_semifunctorD(6)[OF assms(4)]
    )

lemma is_ntsmcfD':
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<Z> \<alpha>"
    and "vfsequence \<NN>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "vcard \<NN> = 5\<^sub>\<nat>"
    and "\<NN>\<lparr>NTDom\<rparr> = \<FF>"
    and "\<NN>\<lparr>NTCod\<rparr> = \<GG>"
    and "\<NN>\<lparr>NTDGDom\<rparr> = \<AA>"
    and "\<NN>\<lparr>NTDGCod\<rparr> = \<BB>"
    and "vsv (\<NN>\<lparr>NTMap\<rparr>)"
    and "\<D>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    and "\<And>a. a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<Longrightarrow> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "\<And>a b f. f : a \<mapsto>\<^bsub>\<AA>\<^esub> b \<Longrightarrow>
      \<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
  by 
    (
      simp_all add: 
        is_ntsmcfD(2-11)[OF assms] 
        is_tdghmD[OF is_ntsmcfD(6)[OF assms], unfolded slicing_simps]
    )

lemma is_ntsmcfE':
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  obtains "\<Z> \<alpha>"
    and "vfsequence \<NN>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "vcard \<NN> = 5\<^sub>\<nat>"
    and "\<NN>\<lparr>NTDom\<rparr> = \<FF>"
    and "\<NN>\<lparr>NTCod\<rparr> = \<GG>"
    and "\<NN>\<lparr>NTDGDom\<rparr> = \<AA>"
    and "\<NN>\<lparr>NTDGCod\<rparr> = \<BB>"
    and "vsv (\<NN>\<lparr>NTMap\<rparr>)"
    and "\<D>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    and "\<And>a. a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<Longrightarrow> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "\<And>a b f. f : a \<mapsto>\<^bsub>\<AA>\<^esub> b \<Longrightarrow>
      \<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
  using assms by (simp add: is_ntsmcfD')


text\<open>Slicing.\<close>

context is_ntsmcf
begin

interpretation tdghm: is_tdghm 
  \<alpha> \<open>smc_dg \<AA>\<close> \<open>smc_dg \<BB>\<close> \<open>smcf_dghm \<FF>\<close> \<open>smcf_dghm \<GG>\<close> \<open>ntsmcf_tdghm \<NN>\<close>
  by (rule ntsmcf_is_tdghm)

lemmas_with [unfolded slicing_simps]:
  ntsmcf_NTMap_vsv = tdghm.tdghm_NTMap_vsv
  and ntsmcf_NTMap_vdomain[smc_cs_simps] = tdghm.tdghm_NTMap_vdomain
  and ntsmcf_NTMap_is_arr = tdghm.tdghm_NTMap_is_arr
  and ntsmcf_NTMap_is_arr'[smc_cs_intros]  = tdghm.tdghm_NTMap_is_arr'

sublocale NTMap: vsv \<open>\<NN>\<lparr>NTMap\<rparr>\<close>
  rewrites "\<D>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
  by (rule ntsmcf_NTMap_vsv) (simp add: smc_cs_simps)

lemmas_with [unfolded slicing_simps]:
  ntsmcf_NTMap_app_in_Arr[smc_cs_intros] = tdghm.tdghm_NTMap_app_in_Arr
  and ntsmcf_NTMap_vrange_vifunion = tdghm.tdghm_NTMap_vrange_vifunion
  and ntsmcf_NTMap_vrange = tdghm.tdghm_NTMap_vrange
  and ntsmcf_NTMap_vsubset_Vset = tdghm.tdghm_NTMap_vsubset_Vset
  and ntsmcf_NTMap_in_Vset = tdghm.tdghm_NTMap_in_Vset
  and ntsmcf_is_tdghm_if_ge_Limit = tdghm.tdghm_is_tdghm_if_ge_Limit

end

lemmas [smc_cs_intros] = is_ntsmcf.ntsmcf_NTMap_is_arr'

lemma (in is_ntsmcf) ntsmcf_Comp_commute':
  assumes "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" and "g : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
  shows 
    "\<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> (\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> g) =
      (\<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> g"
  using assms
  by 
    (
      cs_concl 
        cs_simp: ntsmcf_Comp_commute semicategory.smc_Comp_assoc[symmetric] 
        cs_intro: smc_cs_intros
    )

lemma (in is_ntsmcf) ntsmcf_Comp_commute'':
  assumes "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" and "g : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
  shows 
    "\<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> (\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> g) =
      (\<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>) \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> g"
  using assms
  by 
    (
      cs_concl 
        cs_simp: ntsmcf_Comp_commute semicategory.smc_Comp_assoc[symmetric] 
        cs_intro: smc_cs_intros
    )


text\<open>Elementary properties.\<close>

lemma ntsmcf_eqI:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN>' : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
    and "\<NN>\<lparr>NTMap\<rparr> = \<NN>'\<lparr>NTMap\<rparr>"
    and "\<FF> = \<FF>'"
    and "\<GG> = \<GG>'"
    and "\<AA> = \<AA>'"
    and "\<BB> = \<BB>'"
  shows "\<NN> = \<NN>'"
proof-
  interpret L: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret R: is_ntsmcf \<alpha> \<AA>' \<BB>' \<FF>' \<GG>' \<NN>' by (rule assms(2))
  show ?thesis
  proof(rule vsv_eqI)
    have dom: "\<D>\<^sub>\<circ> \<NN> = 5\<^sub>\<nat>" by (cs_concl cs_simp: smc_cs_simps V_cs_simps)
    show "\<D>\<^sub>\<circ> \<NN> = \<D>\<^sub>\<circ> \<NN>'" by (cs_concl cs_simp: smc_cs_simps V_cs_simps)
    from assms(4-7) have sup: 
      "\<NN>\<lparr>NTDom\<rparr> = \<NN>'\<lparr>NTDom\<rparr>" "\<NN>\<lparr>NTCod\<rparr> = \<NN>'\<lparr>NTCod\<rparr>" 
      "\<NN>\<lparr>NTDGDom\<rparr> = \<NN>'\<lparr>NTDGDom\<rparr>" "\<NN>\<lparr>NTDGCod\<rparr> = \<NN>'\<lparr>NTDGCod\<rparr>" 
      by (simp_all add: smc_cs_simps)
    show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<NN> \<Longrightarrow> \<NN>\<lparr>a\<rparr> = \<NN>'\<lparr>a\<rparr>" for a 
      by (unfold dom, elim_in_numeral, insert assms(3) sup)
        (auto simp: nt_field_simps)
  qed auto
qed

lemma ntsmcf_tdghm_eqI:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN>' : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
    and "\<FF> = \<FF>'"
    and "\<GG> = \<GG>'"
    and "\<AA> = \<AA>'"
    and "\<BB> = \<BB>'"
    and "ntsmcf_tdghm \<NN> = ntsmcf_tdghm \<NN>'"
  shows "\<NN> = \<NN>'"
proof(rule ntsmcf_eqI[of \<alpha>])
  from assms(7) have "ntsmcf_tdghm \<NN>\<lparr>NTMap\<rparr> = ntsmcf_tdghm \<NN>'\<lparr>NTMap\<rparr>" by simp
  then show "\<NN>\<lparr>NTMap\<rparr> = \<NN>'\<lparr>NTMap\<rparr>" unfolding slicing_simps by simp_all
  from assms(3-6) show "\<FF> = \<FF>'" "\<GG> = \<GG>'" "\<AA> = \<AA>'" "\<BB> = \<BB>'" by simp_all
qed (simp_all add: assms(1,2))

lemma (in is_ntsmcf) ntsmcf_def:
  "\<NN> = [\<NN>\<lparr>NTMap\<rparr>, \<NN>\<lparr>NTDom\<rparr>, \<NN>\<lparr>NTCod\<rparr>, \<NN>\<lparr>NTDGDom\<rparr>, \<NN>\<lparr>NTDGCod\<rparr>]\<^sub>\<circ>"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> \<NN> = 5\<^sub>\<nat>" by (cs_concl cs_simp: smc_cs_simps V_cs_simps)
  have dom_rhs:
    "\<D>\<^sub>\<circ> [\<NN>\<lparr>NTMap\<rparr>, \<NN>\<lparr>NTDGDom\<rparr>, \<NN>\<lparr>NTDGCod\<rparr>, \<NN>\<lparr>NTDom\<rparr>, \<NN>\<lparr>NTCod\<rparr>]\<^sub>\<circ> = 5\<^sub>\<nat>"
    by (simp add: nat_omega_simps)
  then show "\<D>\<^sub>\<circ> \<NN> = \<D>\<^sub>\<circ> [\<NN>\<lparr>NTMap\<rparr>, \<NN>\<lparr>NTDom\<rparr>, \<NN>\<lparr>NTCod\<rparr>, \<NN>\<lparr>NTDGDom\<rparr>, \<NN>\<lparr>NTDGCod\<rparr>]\<^sub>\<circ>"
    unfolding dom_lhs dom_rhs by (simp add: nat_omega_simps)
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<NN> \<Longrightarrow>
    \<NN>\<lparr>a\<rparr> = [\<NN>\<lparr>NTMap\<rparr>, \<NN>\<lparr>NTDom\<rparr>, \<NN>\<lparr>NTCod\<rparr>, \<NN>\<lparr>NTDGDom\<rparr>, \<NN>\<lparr>NTDGCod\<rparr>]\<^sub>\<circ>\<lparr>a\<rparr>" 
    for a
    by (unfold dom_lhs, elim_in_numeral, unfold nt_field_simps)
      (simp_all add: nat_omega_simps)
qed (auto simp: vsv_axioms)


text\<open>Size.\<close>

lemma (in is_ntsmcf) ntsmcf_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<NN> \<in>\<^sub>\<circ> Vset \<beta>"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  note [smc_cs_intros] = 
    ntsmcf_NTMap_in_Vset
    NTDom.smcf_in_Vset
    NTCod.smcf_in_Vset
    NTDom.HomDom.smc_in_Vset
    NTDom.HomCod.smc_in_Vset
  from assms(2) show ?thesis
    by (subst ntsmcf_def) 
      (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros V_cs_intros)
qed

lemma (in is_ntsmcf) ntsmcf_is_ntsmcf_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<beta>\<^esub> \<BB>"
proof(intro is_ntsmcfI )
  show "ntsmcf_tdghm \<NN> :
    smcf_dghm \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M smcf_dghm \<GG> : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<beta>\<^esub> smc_dg \<BB>"
    by (rule is_tdghm.tdghm_is_tdghm_if_ge_Limit[OF ntsmcf_is_tdghm assms])
  show "\<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
    if "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" for f a b
    using that by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)+
qed 
  (
    cs_concl 
      cs_simp: smc_cs_simps 
      cs_intro:
        smc_cs_intros
        V_cs_intros
        assms 
        NTDom.smcf_is_semifunctor_if_ge_Limit
        NTCod.smcf_is_semifunctor_if_ge_Limit
   )+

lemma small_all_ntsmcfs[simp]: 
  "small {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(cases \<open>\<Z> \<alpha>\<close>)
  case True
  from is_ntsmcf.ntsmcf_in_Vset show ?thesis
    by (intro down[of _ \<open>Vset (\<alpha> + \<omega>)\<close>]) 
      (auto simp: True \<Z>.\<Z>_Limit_\<alpha>\<omega> \<Z>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>.intro \<Z>.\<Z>_\<alpha>_\<alpha>\<omega>)
next
  case False
  then have "{\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>} = {}" by auto
  then show ?thesis by simp
qed

lemma small_ntsmcfs[simp]: "small {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"
  by (rule down[of _ \<open>set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}\<close>])
    auto

lemma small_these_ntcfs[simp]: "small {\<NN>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"
  by (rule down[of _ \<open>set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}\<close>]) 
    auto


text\<open>Further elementary results.\<close>

lemma these_ntsmcfs_iff(*not simp*):  
  "\<NN> \<in>\<^sub>\<circ> these_ntsmcfs \<alpha> \<AA> \<BB> \<FF> \<GG> \<longleftrightarrow> \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  by auto



subsection\<open>Opposite natural transformation of semifunctors\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See section 1.5 in \cite{bodo_categories_1970}.\<close>

definition op_ntsmcf :: "V \<Rightarrow> V"
  where "op_ntsmcf \<NN> =
    [
      \<NN>\<lparr>NTMap\<rparr>,
      op_smcf (\<NN>\<lparr>NTCod\<rparr>),
      op_smcf (\<NN>\<lparr>NTDom\<rparr>),
      op_smc (\<NN>\<lparr>NTDGDom\<rparr>),
      op_smc (\<NN>\<lparr>NTDGCod\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma op_ntsmcf_components[smc_op_simps]:
  shows "op_ntsmcf \<NN>\<lparr>NTMap\<rparr> = \<NN>\<lparr>NTMap\<rparr>"
    and "op_ntsmcf \<NN>\<lparr>NTDom\<rparr> = op_smcf (\<NN>\<lparr>NTCod\<rparr>)"
    and "op_ntsmcf \<NN>\<lparr>NTCod\<rparr> = op_smcf (\<NN>\<lparr>NTDom\<rparr>)"
    and "op_ntsmcf \<NN>\<lparr>NTDGDom\<rparr> = op_smc (\<NN>\<lparr>NTDGDom\<rparr>)"
    and "op_ntsmcf \<NN>\<lparr>NTDGCod\<rparr> = op_smc (\<NN>\<lparr>NTDGCod\<rparr>)"
  unfolding op_ntsmcf_def nt_field_simps by (auto simp: nat_omega_simps)


text\<open>Slicing.\<close>

lemma op_tdghm_ntsmcf_tdghm[slicing_commute]: 
  "op_tdghm (ntsmcf_tdghm \<NN>) = ntsmcf_tdghm (op_ntsmcf \<NN>)"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> (op_tdghm (ntsmcf_tdghm \<NN>)) = 5\<^sub>\<nat>"
    unfolding op_tdghm_def by (auto simp: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (ntsmcf_tdghm (op_ntsmcf \<NN>)) = 5\<^sub>\<nat>"
    unfolding ntsmcf_tdghm_def by (auto simp: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (op_tdghm (ntsmcf_tdghm \<NN>)) = \<D>\<^sub>\<circ> (ntsmcf_tdghm (op_ntsmcf \<NN>))"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (op_tdghm (ntsmcf_tdghm \<NN>)) \<Longrightarrow> 
    op_tdghm (ntsmcf_tdghm \<NN>)\<lparr>a\<rparr> = ntsmcf_tdghm (op_ntsmcf \<NN>)\<lparr>a\<rparr>"
    for a
    by
      (
        unfold dom_lhs,
        elim_in_numeral,
        unfold ntsmcf_tdghm_def op_ntsmcf_def op_tdghm_def nt_field_simps
      )
      (auto simp: nat_omega_simps slicing_commute[symmetric])
qed (auto simp: ntsmcf_tdghm_def op_tdghm_def)


subsubsection\<open>Further properties\<close>

lemma (in is_ntsmcf) is_ntsmcf_op: 
  "op_ntsmcf \<NN> : op_smcf \<GG> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F op_smcf \<FF> : op_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> op_smc \<BB>"
proof(rule is_ntsmcfI, unfold smc_op_simps)
  show "vfsequence (op_ntsmcf \<NN>)" by (simp add: op_ntsmcf_def)
  show "vcard (op_ntsmcf \<NN>) = 5\<^sub>\<nat>" by (simp add: op_ntsmcf_def nat_omega_simps)
  fix f a b assume "f : b \<mapsto>\<^bsub>\<AA>\<^esub> a"
  with is_ntsmcf_axioms show 
    "\<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>op_smc \<BB>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
      \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>op_smc \<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
    by (cs_concl cs_simp: smc_cs_simps smc_op_simps cs_intro: smc_cs_intros)
qed
  (
    insert is_ntsmcf_axioms,
    (
      cs_concl 
        cs_simp: smc_cs_simps slicing_commute[symmetric]
        cs_intro: smc_cs_intros smc_op_intros dg_op_intros slicing_intros
    )+
  )

lemma (in is_ntsmcf) is_ntsmcf_op'[smc_op_intros]: 
  assumes "\<GG>' = op_smcf \<GG>"
    and "\<FF>' = op_smcf \<FF>"
    and "\<AA>' = op_smc \<AA>"
    and "\<BB>' = op_smc \<BB>"
  shows "op_ntsmcf \<NN> : \<GG>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>' : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule is_ntsmcf_op)

lemmas [smc_op_intros] = is_ntsmcf.is_ntsmcf_op'

lemma (in is_ntsmcf) ntsmcf_op_ntsmcf_op_ntsmcf[smc_op_simps]: 
  "op_ntsmcf (op_ntsmcf \<NN>) = \<NN>"
proof(rule ntsmcf_eqI[of \<alpha> \<AA> \<BB> \<FF> \<GG> _ \<AA> \<BB> \<FF> \<GG>], unfold smc_op_simps)
  interpret op: 
    is_ntsmcf \<alpha> \<open>op_smc \<AA>\<close> \<open>op_smc \<BB>\<close> \<open>op_smcf \<GG>\<close> \<open>op_smcf \<FF>\<close> \<open>op_ntsmcf \<NN>\<close>
    by (rule is_ntsmcf_op)
  from op.is_ntsmcf_op show 
    "op_ntsmcf (op_ntsmcf \<NN>) : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (simp add: smc_op_simps)
qed (auto simp: smc_cs_intros)

lemmas ntsmcf_op_ntsmcf_op_ntsmcf[smc_op_simps] =
  is_ntsmcf.ntsmcf_op_ntsmcf_op_ntsmcf

lemma eq_op_ntsmcf_iff: 
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN>' : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  shows "op_ntsmcf \<NN> = op_ntsmcf \<NN>' \<longleftrightarrow> \<NN> = \<NN>'"
proof
  interpret L: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret R: is_ntsmcf \<alpha> \<AA>' \<BB>' \<FF>' \<GG>' \<NN>' by (rule assms(2))
  assume prems: "op_ntsmcf \<NN> = op_ntsmcf \<NN>'"
  show "\<NN> = \<NN>'"
  proof(rule ntsmcf_eqI[OF assms])
    from prems L.ntsmcf_op_ntsmcf_op_ntsmcf R.ntsmcf_op_ntsmcf_op_ntsmcf show 
      "\<NN>\<lparr>NTMap\<rparr> = \<NN>'\<lparr>NTMap\<rparr>"
      by metis+
    from prems L.ntsmcf_op_ntsmcf_op_ntsmcf R.ntsmcf_op_ntsmcf_op_ntsmcf 
    have "\<NN>\<lparr>NTDom\<rparr> = \<NN>'\<lparr>NTDom\<rparr>" 
      and "\<NN>\<lparr>NTCod\<rparr> = \<NN>'\<lparr>NTCod\<rparr>" 
      and "\<NN>\<lparr>NTDGDom\<rparr> = \<NN>'\<lparr>NTDGDom\<rparr>" 
      and "\<NN>\<lparr>NTDGCod\<rparr> = \<NN>'\<lparr>NTDGCod\<rparr>" 
      by metis+
    then show "\<FF> = \<FF>'" "\<GG> = \<GG>'" "\<AA> = \<AA>'" "\<BB> = \<BB>'" by (auto simp: smc_cs_simps)
  qed
qed auto



subsection\<open>Vertical composition of natural transformations\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter II-4 in \cite{mac_lane_categories_2010}.\<close>

definition ntsmcf_vcomp :: "V \<Rightarrow> V \<Rightarrow> V" (infixl \<open>\<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<close> 55)
  where "ntsmcf_vcomp \<MM> \<NN> = 
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<NN>\<lparr>NTDGDom\<rparr>\<lparr>Obj\<rparr>. (\<MM>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) \<circ>\<^sub>A\<^bsub>\<NN>\<lparr>NTDGCod\<rparr>\<^esub> (\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)),
      \<NN>\<lparr>NTDom\<rparr>,
      \<MM>\<lparr>NTCod\<rparr>,
      \<NN>\<lparr>NTDGDom\<rparr>,
      \<MM>\<lparr>NTDGCod\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma ntsmcf_vcomp_components:
  shows
    "(\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr> =
      (\<lambda>a\<in>\<^sub>\<circ>\<NN>\<lparr>NTDGDom\<rparr>\<lparr>Obj\<rparr>. (\<MM>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) \<circ>\<^sub>A\<^bsub>\<NN>\<lparr>NTDGCod\<rparr>\<^esub> (\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>))"
    and [dg_shared_cs_simps, smc_cs_simps]: "(\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTDom\<rparr> = \<NN>\<lparr>NTDom\<rparr>" 
    and [dg_shared_cs_simps, smc_cs_simps]: "(\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTCod\<rparr> = \<MM>\<lparr>NTCod\<rparr>"
    and [dg_shared_cs_simps, smc_cs_simps]: 
      "(\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTDGDom\<rparr> = \<NN>\<lparr>NTDGDom\<rparr>"
    and [dg_shared_cs_simps, smc_cs_simps]: 
      "(\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTDGCod\<rparr> = \<MM>\<lparr>NTDGCod\<rparr>"
  unfolding nt_field_simps ntsmcf_vcomp_def by (simp_all add: nat_omega_simps)


subsubsection\<open>Natural transformation map\<close>

lemma ntsmcf_vcomp_NTMap_vsv[dg_shared_cs_intros, smc_cs_intros]: 
  "vsv ((\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>)"
  unfolding ntsmcf_vcomp_components by simp

lemma ntsmcf_vcomp_NTMap_vdomain[smc_cs_simps]:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
proof-
  interpret \<NN>: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> using assms by auto
  show ?thesis unfolding ntsmcf_vcomp_components by (simp add: smc_cs_simps)
qed

lemma ntsmcf_vcomp_NTMap_app[smc_cs_simps]:
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
  shows "(\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<MM>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
proof-
  interpret \<MM>: is_ntsmcf \<alpha> \<AA> \<BB> \<GG> \<HH> \<MM> using assms by auto
  interpret \<NN>: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> using assms by auto
  from assms show ?thesis 
    unfolding ntsmcf_vcomp_components by (simp add: smc_cs_simps)
qed

lemma ntsmcf_vcomp_NTMap_vrange:
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
  unfolding ntsmcf_vcomp_components
proof(rule vrange_VLambda_vsubset)
  fix x assume prems: "x \<in>\<^sub>\<circ> \<NN>\<lparr>NTDGDom\<rparr>\<lparr>Obj\<rparr>"
  from prems assms show "\<MM>\<lparr>NTMap\<rparr>\<lparr>x\<rparr> \<circ>\<^sub>A\<^bsub>\<NN>\<lparr>NTDGCod\<rparr>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>x\<rparr> \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
    by (cs_prems cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
      (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
qed


subsubsection\<open>Further properties\<close>

lemma ntsmcf_vcomp_composable_commute[smc_cs_simps]:
  \<comment>\<open>See Chapter II-4 in \cite{mac_lane_categories_2010}).\<close>
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
  shows 
    "(\<MM>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>) \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = 
      \<HH>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> (\<MM>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)"
    (is \<open>(?MC \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> ?NC) \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> ?R = ?T \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> (?MD \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> ?ND)\<close>)
proof-
  interpret \<MM>: is_ntsmcf \<alpha> \<AA> \<BB> \<GG> \<HH> \<MM> by (rule assms(1)) 
  interpret \<NN>: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  from assms show ?thesis
    by (intro \<MM>.NTDom.HomCod.smc_pattern_rectangle_left)
      (cs_concl cs_intro: smc_cs_intros cs_simp: \<NN>.ntsmcf_Comp_commute)
qed 

lemma ntsmcf_vcomp_is_ntsmcf[smc_cs_intros]:
  \<comment>\<open>See Chapter II-4 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<MM>: is_ntsmcf \<alpha> \<AA> \<BB> \<GG> \<HH> \<MM> by (rule assms(1))
  interpret \<NN>: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  show ?thesis 
  proof(intro is_ntsmcfI')
    show "vfsequence (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)" by (simp add: ntsmcf_vcomp_def)
    show "vcard (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>) = 5\<^sub>\<nat>"
      by (auto simp: nat_omega_simps ntsmcf_vcomp_def)
    show "vsv ((\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>)"
      unfolding ntsmcf_vcomp_components by simp
    from assms show "(\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" for a
      using that by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
    fix f a b assume "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
    with assms show 
      "(\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
        \<HH>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: smc_cs_simps is_ntsmcf.ntsmcf_Comp_commute' 
            cs_intro: smc_cs_intros
        )
  qed (use assms in \<open>auto simp: smc_cs_simps ntsmcf_vcomp_NTMap_vrange\<close>)
qed

lemma ntsmcf_vcomp_assoc[smc_cs_simps]: 
  \<comment>\<open>See Chapter II-4 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<LL> : \<HH> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<MM> : \<GG> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "(\<LL> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<MM>) \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> = \<LL> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)"
proof-
  interpret \<LL>: is_ntsmcf \<alpha> \<AA> \<BB> \<HH> \<KK> \<LL> by (rule assms(1))
  interpret \<MM>: is_ntsmcf \<alpha> \<AA> \<BB> \<GG> \<HH> \<MM> by (rule assms(2))
  interpret \<NN>: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(3))
  show ?thesis
  proof(rule ntsmcf_eqI[of \<alpha>])
    show "((\<LL> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<MM>) \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr> = (\<LL> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI)
      fix a assume "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((\<LL> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>)"
      then have "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
        unfolding ntsmcf_vcomp_components by (simp add: smc_cs_simps)
      with assms show 
        "((\<LL> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<MM>) \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
          (\<LL> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
    qed (simp_all add: ntsmcf_vcomp_components)
  qed (auto intro: smc_cs_intros)
qed


subsubsection\<open>
Opposite of the vertical composition of natural transformations
of semifunctors
\<close>

lemma op_ntsmcf_ntsmcf_vcomp[smc_op_simps]: 
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "op_ntsmcf (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>) = op_ntsmcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F op_ntsmcf \<MM>"
proof-
  interpret \<MM>: is_ntsmcf \<alpha> \<AA> \<BB> \<GG> \<HH> \<MM> using assms(1) by auto
  interpret \<NN>: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> using assms(2) by auto
  show ?thesis
  proof(rule ntsmcf_eqI[of \<alpha>]; (intro symmetric)?)
    show "op_ntsmcf (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr> = 
      (op_ntsmcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F op_ntsmcf \<MM>)\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI)
      fix a assume "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (op_ntsmcf (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>)"
      then have a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
        unfolding smc_op_simps ntsmcf_vcomp_NTMap_vdomain[OF assms(2)] by simp
      with 
        \<MM>.NTDom.HomCod.op_smc_Comp 
        \<MM>.ntsmcf_NTMap_is_arr[OF a]
        \<NN>.ntsmcf_NTMap_is_arr[OF a] 
      show "op_ntsmcf (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
        (op_ntsmcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F op_ntsmcf \<MM>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        unfolding smc_op_simps ntsmcf_vcomp_components 
        by (simp add: smc_cs_simps)
    qed (simp_all add: smc_op_simps smc_cs_simps ntsmcf_vcomp_components(1))
  qed (auto intro: smc_cs_intros smc_op_intros)
qed



subsection\<open>Horizontal composition of natural transformations\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter II-5 in \cite{mac_lane_categories_2010}.\<close>

definition ntsmcf_hcomp :: "V \<Rightarrow> V \<Rightarrow> V" (infixl \<open>\<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<close> 55)
  where "ntsmcf_hcomp \<MM> \<NN> =
    [
      (
        \<lambda>a\<in>\<^sub>\<circ>\<NN>\<lparr>NTDGDom\<rparr>\<lparr>Obj\<rparr>.
          (
            \<MM>\<lparr>NTCod\<rparr>\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<MM>\<lparr>NTDGCod\<rparr>\<^esub> 
            \<MM>\<lparr>NTMap\<rparr>\<lparr>\<NN>\<lparr>NTDom\<rparr>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>
          )
      ),
      (\<MM>\<lparr>NTDom\<rparr> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>\<lparr>NTDom\<rparr>),
      (\<MM>\<lparr>NTCod\<rparr> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>\<lparr>NTCod\<rparr>),
      (\<NN>\<lparr>NTDGDom\<rparr>),
      (\<MM>\<lparr>NTDGCod\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>                                            

lemma ntsmcf_hcomp_components:
  shows 
    "(\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr> = 
      (
        \<lambda>a\<in>\<^sub>\<circ>\<NN>\<lparr>NTDGDom\<rparr>\<lparr>Obj\<rparr>.
          (
            \<MM>\<lparr>NTCod\<rparr>\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<MM>\<lparr>NTDGCod\<rparr>\<^esub> 
            \<MM>\<lparr>NTMap\<rparr>\<lparr>\<NN>\<lparr>NTDom\<rparr>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>
          )
      )"
    and [dg_shared_cs_simps, smc_cs_simps]:
      "(\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTDom\<rparr> = \<MM>\<lparr>NTDom\<rparr> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>\<lparr>NTDom\<rparr>" 
    and [dg_shared_cs_simps, smc_cs_simps]:
      "(\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTCod\<rparr> = \<MM>\<lparr>NTCod\<rparr> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>\<lparr>NTCod\<rparr>"
    and [dg_shared_cs_simps, smc_cs_simps]: 
      "(\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTDGDom\<rparr> = \<NN>\<lparr>NTDGDom\<rparr>"
    and [dg_shared_cs_simps, smc_cs_simps]:
      "(\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTDGCod\<rparr> = \<MM>\<lparr>NTDGCod\<rparr>"
  unfolding nt_field_simps ntsmcf_hcomp_def by (auto simp: nat_omega_simps)


subsubsection\<open>Natural transformation map\<close>

lemma ntsmcf_hcomp_NTMap_vsv[smc_cs_intros]: "vsv ((\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>)"
  unfolding ntsmcf_hcomp_components by auto

lemma ntsmcf_hcomp_NTMap_vdomain[smc_cs_simps]: 
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
proof-
  interpret \<NN>: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  show ?thesis unfolding ntsmcf_hcomp_components by (simp add: smc_cs_simps)
qed

lemma ntsmcf_hcomp_NTMap_app[smc_cs_simps]:
  assumes "\<MM> : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
  shows "(\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = 
    \<GG>'\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<MM>\<lparr>NTMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
proof-
  interpret \<MM>: is_ntsmcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<MM> by (rule assms(1))
  interpret \<NN>: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  from assms(3) show ?thesis 
    unfolding ntsmcf_hcomp_components by (simp add: smc_cs_simps)
qed

lemma ntsmcf_hcomp_NTMap_vrange:
  assumes "\<MM> : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof
  interpret \<MM>: is_ntsmcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<MM> by (rule assms(1))
  interpret \<NN>: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  fix f assume "f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> ((\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>)"
  with ntsmcf_hcomp_NTMap_vdomain obtain a 
    where a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and f_def: "f = (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
    unfolding ntsmcf_hcomp_components by (force simp: smc_cs_simps)
  have \<FF>a: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
    by (simp add: \<NN>.NTDom.smcf_ObjMap_app_in_HomCod_Obj a)
  from \<NN>.ntsmcf_NTMap_is_arr[OF a] have "\<GG>'\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr> :
    \<GG>'\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>'\<lparr>ObjMap\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
    by (force intro: smc_cs_intros)
  then have "\<GG>'\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<MM>\<lparr>NTMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    by 
      (
        meson 
          \<MM>.ntsmcf_NTMap_is_arr[OF \<FF>a] 
          \<MM>.NTDom.HomCod.smc_is_arrE 
          \<MM>.NTDom.HomCod.smc_Comp_is_arr
      )
  with a show "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" 
    unfolding f_def ntsmcf_hcomp_components by (simp add: smc_cs_simps)
qed


subsubsection\<open>Further properties\<close>

lemma ntsmcf_hcomp_composable_commute:
  \<comment>\<open>See Chapter II-5 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<MM> : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" 
  shows 
    "(\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<FF>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = 
      (\<GG>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
proof-
  interpret \<MM>: is_ntsmcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<MM> by (rule assms(1))
  interpret \<NN>: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  from assms(3) have [simp]: "b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" by auto
  from \<MM>.is_ntsmcf_axioms \<NN>.is_ntsmcf_axioms have \<MM>\<NN>b: 
    "(\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>b\<rparr> =
      (\<GG>'\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>\<rparr>) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<MM>\<lparr>NTMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<rparr>)"
    by (auto simp: smc_cs_simps)
  let ?\<GG>'\<FF>f = \<open>\<GG>'\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr>\<close>
  from a \<MM>.is_ntsmcf_axioms \<NN>.is_ntsmcf_axioms have \<MM>\<NN>a: 
    "(\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
      \<GG>'\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<MM>\<lparr>NTMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
    by (cs_concl cs_simp: smc_cs_simps)+
  note \<MM>.NTCod.smcf_ArrMap_Comp[smc_cs_simps del]
  from assms show ?thesis
    unfolding \<MM>\<NN>b \<MM>\<NN>a 
    by (intro \<MM>.NTDom.HomCod.smc_pattern_rectangle_left)
      (
        cs_concl 
          cs_simp: smc_cs_simps is_semifunctor.smcf_ArrMap_Comp[symmetric] 
          cs_intro: smc_cs_intros
      )+
qed

lemma ntsmcf_hcomp_is_ntsmcf:
  \<comment>\<open>See Chapter II-5 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<MM> : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> : \<FF>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<MM>: is_ntsmcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<MM> by (rule assms(1))
  interpret \<NN>: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  show ?thesis
  proof(intro is_ntsmcfI', unfold ntsmcf_hcomp_components(3,4)) 
    show "vfsequence (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)" unfolding ntsmcf_hcomp_def by auto
    show "vcard (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>) = 5\<^sub>\<nat>"
      unfolding ntsmcf_hcomp_def by (simp add: nat_omega_simps)
    from assms show "(\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : 
      (\<FF>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> (\<GG>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" for a
      using that by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
    fix f a b assume "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
    with ntsmcf_hcomp_composable_commute[OF assms] 
    show "(\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<FF>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = 
      (\<GG>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      by auto
  qed (auto simp: ntsmcf_hcomp_components(1) smc_cs_simps intro: smc_cs_intros)
qed

lemma ntsmcf_hcomp_is_ntsmcf'[smc_cs_intros]:
  assumes "\<MM> : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<SS> = \<FF>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>"
    and "\<SS>' = \<GG>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>"
  shows "\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> : \<SS> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<SS>' : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1,2) unfolding assms(3,4) by (rule ntsmcf_hcomp_is_ntsmcf)

lemma ntsmcf_hcomp_assoc[smc_cs_simps]: 
  \<comment>\<open>See Chapter II-5 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<LL> : \<FF>'' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>'' : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" 
    and "\<MM> : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "(\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<MM>) \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> = \<LL> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)"
proof-
  interpret \<LL>: is_ntsmcf \<alpha> \<CC> \<DD> \<FF>'' \<GG>'' \<LL> by (rule assms(1))
  interpret \<MM>: is_ntsmcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<MM>  by (rule assms(2))
  interpret \<NN>: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(3))
  interpret \<LL>\<MM>: is_ntsmcf \<alpha> \<BB> \<DD> \<open>\<FF>'' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>'\<close> \<open>\<GG>'' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>'\<close> \<open>\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<MM>\<close> 
    by (auto intro: smc_cs_intros)
  interpret \<MM>\<NN>: is_ntsmcf \<alpha> \<AA> \<CC> \<open>\<FF>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>\<close> \<open>\<GG>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>\<close> \<open>\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>\<close> 
    by (auto intro: smc_cs_intros)
  note smcf_axioms =
    \<LL>.NTDom.is_semifunctor_axioms 
    \<LL>.NTCod.is_semifunctor_axioms 
    \<MM>.NTDom.is_semifunctor_axioms 
    \<MM>.NTCod.is_semifunctor_axioms 
    \<NN>.NTDom.is_semifunctor_axioms 
    \<NN>.NTCod.is_semifunctor_axioms 
  show ?thesis
  proof(rule ntsmcf_eqI)
    from assms show 
      "\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> :
        (\<FF>'' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>') \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<GG>'' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>') \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> :
        \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
      by (auto intro: smc_cs_intros)
    from \<LL>\<MM>.is_ntsmcf_axioms \<NN>.is_ntsmcf_axioms have dom_lhs:
      "\<D>\<^sub>\<circ> ((\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
      by (simp add: smc_cs_simps)
    from \<MM>\<NN>.is_ntsmcf_axioms \<LL>.is_ntsmcf_axioms have dom_rhs:  
      "\<D>\<^sub>\<circ> ((\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
      by (simp add: smc_cs_simps)
    show "(\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr> = (\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
      with assms show
        "(\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
          (\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
    qed (simp_all add: ntsmcf_hcomp_components)
  qed 
    (
      insert smcf_axioms, 
      auto simp: smcf_comp_assoc intro!: smc_cs_intros
    )
qed


subsubsection\<open>Opposite of the horizontal composition of the 
natural transformation of semifunctors\<close>

lemma op_ntsmcf_ntsmcf_hcomp[smc_op_simps]: 
  assumes "\<MM> : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "op_ntsmcf (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>) = op_ntsmcf \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F op_ntsmcf \<NN>"
proof-
  interpret \<MM>: is_ntsmcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<MM> by (rule assms(1))
  interpret \<NN>: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  have op_\<MM>: "op_ntsmcf \<MM> :
    op_smcf \<GG>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F op_smcf \<FF>' : op_smc \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> op_smc \<CC>"
    and op_\<NN>: "op_ntsmcf \<NN> :
    op_smcf \<GG> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F op_smcf \<FF> : op_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> op_smc \<BB>" 
    by (cs_concl cs_simp: smc_op_simps cs_intro: smc_cs_intros smc_op_intros)
  show ?thesis
  proof(rule sym, rule ntsmcf_eqI, unfold smc_op_simps slicing_simps)
    show 
      "op_ntsmcf \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F op_ntsmcf \<NN> :
        op_smcf \<GG>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F op_smcf \<GG> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F op_smcf \<FF>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F op_smcf \<FF> :
        op_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> op_smc \<CC>"
      by (cs_concl cs_simp: smc_op_simps cs_intro: smc_cs_intros smc_op_intros)
    show "op_ntsmcf (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>) :
      op_smcf \<GG>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F op_smcf \<GG> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F op_smcf \<FF>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F op_smcf \<FF> :
      op_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> op_smc \<CC>"
      by (cs_concl cs_simp: smc_op_simps cs_intro: smc_cs_intros smc_op_intros)
    show "(op_ntsmcf \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F op_ntsmcf \<NN>)\<lparr>NTMap\<rparr> = (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>"
    proof
      (
        rule vsv_eqI, 
        unfold 
          ntsmcf_hcomp_NTMap_vdomain[OF assms(2)]
          ntsmcf_hcomp_NTMap_vdomain[OF op_\<NN>]
          smc_op_simps
      )
      fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
      with assms show 
        "(op_ntsmcf \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F op_ntsmcf \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by 
          (
            cs_concl 
              cs_simp: smc_cs_simps smc_op_simps 
              cs_intro: smc_cs_intros smc_op_intros
          )
    qed (auto simp: ntsmcf_hcomp_components)
  qed simp_all
qed 



subsection\<open>Interchange law\<close>

lemma ntsmcf_comp_interchange_law:
  \<comment>\<open>See Chapter II-5 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<MM>' : \<GG>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>' : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN>' : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows 
    "((\<MM>' \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>') \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)) =
      (\<MM>' \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<MM>) \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<NN>' \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)"
proof-
  interpret \<MM>: is_ntsmcf \<alpha> \<AA> \<BB> \<GG> \<HH> \<MM> by (rule assms(1))
  interpret \<NN>: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  interpret \<MM>': is_ntsmcf \<alpha> \<BB> \<CC> \<GG>' \<HH>' \<MM>' by (rule assms(3))
  interpret \<NN>': is_ntsmcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<NN>' by (rule assms(4))
  interpret \<NN>'\<NN>: 
    is_ntsmcf \<alpha> \<AA> \<CC> \<open>\<FF>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>\<close> \<open>\<GG>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>\<close> \<open>\<NN>' \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>\<close> 
    by (auto intro: smc_cs_intros)
  interpret \<MM>\<NN>: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<HH> \<open>\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>\<close> 
    by (auto intro: smc_cs_intros)
  show ?thesis
  proof(rule ntsmcf_eqI[of \<alpha>])
    show 
      "(\<MM>' \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>' \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr> =
        (\<MM>' \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<NN>' \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>"
    proof
      (
        rule vsv_eqI,
        unfold 
          ntsmcf_vcomp_NTMap_vdomain[OF \<NN>'\<NN>.is_ntsmcf_axioms]
          ntsmcf_hcomp_NTMap_vdomain[OF \<MM>\<NN>.is_ntsmcf_axioms]
      )
      fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
      with assms show
        "(\<MM>' \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>' \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
          ((\<MM>' \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<MM>) \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<NN>' \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by
          (
            cs_concl
              cs_simp: smc_cs_simps is_ntsmcf.ntsmcf_Comp_commute' 
              cs_intro: smc_cs_intros
          )
    qed (auto intro: smc_cs_intros)
  qed (auto intro: smc_cs_intros)
qed



subsection\<open>
Composition of a natural transformation of semifunctors and a semifunctor
\<close>


subsubsection\<open>Definition and elementary properties\<close>

abbreviation (input) ntsmcf_smcf_comp :: "V \<Rightarrow> V \<Rightarrow> V" (infixl "\<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F" 55)
  where "ntsmcf_smcf_comp \<equiv> tdghm_dghm_comp"


text\<open>Slicing.\<close>

lemma ntsmcf_tdghm_ntsmcf_smcf_comp[slicing_commute]: 
  "ntsmcf_tdghm \<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M smcf_dghm \<HH> = ntsmcf_tdghm (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>)"
  unfolding 
    tdghm_dghm_comp_def 
    dghm_comp_def 
    ntsmcf_tdghm_def 
    smcf_dghm_def 
    smc_dg_def
    dg_field_simps
    dghm_field_simps 
    nt_field_simps 
  by (simp add: nat_omega_simps) (*slow*)


subsubsection\<open>Natural transformation map\<close>

mk_VLambda (in is_semifunctor) 
  tdghm_dghm_comp_components(1)[where \<HH>=\<FF>, unfolded smcf_HomDom]
  |vdomain ntsmcf_smcf_comp_NTMap_vdomain[smc_cs_simps]|
  |app ntsmcf_smcf_comp_NTMap_app[smc_cs_simps]|

lemmas [smc_cs_simps] = 
  is_semifunctor.ntsmcf_smcf_comp_NTMap_vdomain
  is_semifunctor.ntsmcf_smcf_comp_NTMap_app

lemma ntsmcf_smcf_comp_NTMap_vrange: 
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>)\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof-
  interpret \<NN>: is_ntsmcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<HH>: is_semifunctor \<alpha> \<AA> \<BB> \<HH> by (rule assms(2))
  show ?thesis 
    unfolding tdghm_dghm_comp_components 
    by (auto simp: smc_cs_simps intro: smc_cs_intros)
qed


subsubsection\<open>
Opposite of the composition of a natural transformation of 
semifunctors and a semifunctor
\<close>

lemma op_ntsmcf_ntsmcf_smcf_comp[smc_op_simps]: 
  "op_ntsmcf (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>) = op_ntsmcf \<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F op_smcf \<HH>"
  unfolding 
    tdghm_dghm_comp_def 
    dghm_comp_def 
    op_ntsmcf_def 
    op_smcf_def 
    op_smc_def
    dg_field_simps
    dghm_field_simps
    nt_field_simps
  by (simp add: nat_omega_simps) (*slow*)


subsubsection\<open>
Composition of a natural transformation of semifunctors and a 
semifunctors is a natural transformation of semifunctors
\<close>

lemma ntsmcf_smcf_comp_is_ntsmcf[intro]:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> : \<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<NN>: is_ntsmcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<HH>: is_semifunctor \<alpha> \<AA> \<BB> \<HH> by (rule assms(2))
  show ?thesis
  proof(rule is_ntsmcfI)
    show "vfsequence (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>)"
      unfolding tdghm_dghm_comp_def by (simp add: nat_omega_simps)
    from assms show "\<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_intro: smc_cs_intros)
    from assms show "\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
      by (cs_concl cs_intro: smc_cs_intros)
    show "vcard (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>) = 5\<^sub>\<nat>"
      unfolding tdghm_dghm_comp_def by (simp add: nat_omega_simps)
    from assms show 
      "ntsmcf_tdghm (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>) :
        smcf_dghm (\<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>) \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M smcf_dghm (\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>) :
        smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg \<CC>"
      by 
        (
          cs_concl 
            cs_simp: slicing_commute[symmetric] 
            cs_intro: slicing_intros dg_cs_intros
        )
    show 
      "(\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>)\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
        (\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      if "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" for a b f
      using that by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
  qed (auto simp: smc_cs_simps)
qed

lemma ntsmcf_smcf_comp_is_semifunctor'[smc_cs_intros]:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF>' = \<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>"
    and "\<GG>' = \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>"
  shows "\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1,2) unfolding assms(3,4) ..


subsubsection\<open>Further properties\<close>

lemma ntsmcf_smcf_comp_ntsmcf_smcf_comp_assoc:
  assumes "\<NN> : \<HH> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>' : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" 
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "(\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>) \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> = \<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>)"
proof-
  interpret \<NN>: is_ntsmcf \<alpha> \<CC> \<DD> \<HH> \<HH>' \<NN> by (rule assms(1))
  interpret \<GG>: is_semifunctor \<alpha> \<BB> \<CC> \<GG> by (rule assms(2))
  interpret \<FF>: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(3))
  show ?thesis  
  proof(rule ntsmcf_tdghm_eqI)
    from assms show 
      "(\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>) \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> :
        \<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> :
        \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
      by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
    show "\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>) :
      \<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> :
      \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
      by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
    from assms show 
      "ntsmcf_tdghm ((\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>) \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>) =
        ntsmcf_tdghm (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>))"
      by 
        (
          cs_concl
            cs_simp: slicing_commute[symmetric] 
            cs_intro: slicing_intros tdghm_dghm_comp_tdghm_dghm_comp_assoc
        )
  qed simp_all
qed

lemma (in is_ntsmcf) ntsmcf_ntsmcf_smcf_comp_smcf_id[smc_cs_simps]:
  "\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F smcf_id \<AA> = \<NN>"
proof(rule ntsmcf_tdghm_eqI)
  show "\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F smcf_id \<AA> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
  show "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
  show "ntsmcf_tdghm (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F smcf_id \<AA>) = ntsmcf_tdghm \<NN>"
    by 
      (
        cs_concl
          cs_simp: slicing_simps slicing_commute[symmetric] 
          cs_intro: smc_cs_intros slicing_intros dg_cs_simps
      )
qed simp_all

lemmas [smc_cs_simps] = is_ntsmcf.ntsmcf_ntsmcf_smcf_comp_smcf_id

lemma ntsmcf_vcomp_ntsmcf_smcf_comp[smc_cs_simps]:
  assumes "\<KK> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<MM> : \<GG> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows 
    "(\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK>) \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK>) = 
      (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>) \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK>"
proof(rule ntsmcf_eqI)
  from assms show "(\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>) \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK> : 
    \<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: smc_cs_intros)
  from assms show "\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK>) : 
    \<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: smc_cs_intros)
  from assms have dom_lhs: 
    "\<D>\<^sub>\<circ> ((\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK>))\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
  from assms have dom_rhs: "\<D>\<^sub>\<circ> ((\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK>)\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
  show 
    "(\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK>))\<lparr>NTMap\<rparr> = 
      (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK>)\<lparr>NTMap\<rparr>"
  proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
    fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    with assms show 
      "(\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK>))\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
        (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
  qed (cs_concl cs_intro: smc_cs_intros)+
qed simp_all



subsection\<open>
Composition of a semifunctor and a natural transformation of semifunctors
\<close>


subsubsection\<open>Definition and elementary properties\<close>

abbreviation (input) smcf_ntsmcf_comp :: "V \<Rightarrow> V \<Rightarrow> V" (infixl "\<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F" 55)
  where "smcf_ntsmcf_comp \<equiv> dghm_tdghm_comp"


text\<open>Slicing.\<close>

lemma ntsmcf_tdghm_smcf_ntsmcf_comp[slicing_commute]: 
  "smcf_dghm \<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M ntsmcf_tdghm \<NN> = ntsmcf_tdghm (\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)"
  unfolding 
    dghm_tdghm_comp_def 
    dghm_comp_def 
    ntsmcf_tdghm_def 
    smcf_dghm_def 
    smc_dg_def
    dg_field_simps
    dghm_field_simps 
    nt_field_simps 
  by (simp add: nat_omega_simps) (*slow*)


subsubsection\<open>Natural transformation map\<close>

mk_VLambda (in is_ntsmcf) 
  dghm_tdghm_comp_components(1)[where \<NN>=\<NN>, unfolded ntsmcf_NTDGDom]
  |vdomain smcf_ntsmcf_comp_NTMap_vdomain[smc_cs_simps]|
  |app smcf_ntsmcf_comp_NTMap_app[smc_cs_simps]|

lemmas [smc_cs_simps] = 
  is_ntsmcf.smcf_ntsmcf_comp_NTMap_vdomain
  is_ntsmcf.smcf_ntsmcf_comp_NTMap_app

lemma smcf_ntsmcf_comp_NTMap_vrange: 
  assumes "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof-
  interpret \<HH>: is_semifunctor \<alpha> \<BB> \<CC> \<HH> by (rule assms(1))
  interpret \<NN>: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  show ?thesis 
    unfolding dghm_tdghm_comp_components 
    by (auto simp: smc_cs_simps intro: smc_cs_intros)
qed


subsubsection\<open>
Opposite of the composition of a semifunctor
and a natural transformation of semifunctors 
\<close>

lemma op_ntsmcf_smcf_ntsmcf_comp[smc_op_simps]: 
  "op_ntsmcf (\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>) = op_smcf \<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F op_ntsmcf \<NN>"
  unfolding 
    dghm_tdghm_comp_def
    dghm_comp_def
    op_ntsmcf_def
    op_smcf_def
    op_smc_def
    dg_field_simps
    dghm_field_simps
    nt_field_simps
  by (simp add: nat_omega_simps) (*slow*)


subsubsection\<open>
Composition of a semifunctor and a natural transformation of
semifunctors is a natural transformation of semifunctors
\<close>

lemma smcf_ntsmcf_comp_is_ntsmcf[intro]:
  assumes "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> : \<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<HH>: is_semifunctor \<alpha> \<BB> \<CC> \<HH> by (rule assms(1))
  interpret \<NN>: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  show ?thesis
  proof(rule is_ntsmcfI)
    show "vfsequence (\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)" unfolding dghm_tdghm_comp_def by simp
    from assms show "\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_intro: smc_cs_intros)
    from assms show "\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_intro: smc_cs_intros)
    show "vcard (\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>) = 5\<^sub>\<nat>"
      unfolding dghm_tdghm_comp_def by (simp add: nat_omega_simps)
    from assms show "ntsmcf_tdghm (\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>) :
      smcf_dghm (\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>) \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M smcf_dghm (\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>) :
      smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg \<CC>"
      by 
        (
          cs_concl 
            cs_simp: slicing_commute[symmetric]  
            cs_intro: dg_cs_intros slicing_intros
        )
    have [smc_cs_simps]:  
      "\<HH>\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr> =
        \<HH>\<lparr>ArrMap\<rparr>\<lparr>\<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr>"
      if "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" for a b f
      using assms that 
      by 
        (
          cs_concl 
            cs_simp:
              is_ntsmcf.ntsmcf_Comp_commute 
              is_semifunctor.smcf_ArrMap_Comp[symmetric]
            cs_intro: smc_cs_intros
        )
    from assms show 
      "(\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
        (\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      if "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" for a b f
      using assms that
      by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
  qed (auto simp: smc_cs_simps)
qed

lemma smcf_ntsmcf_comp_is_semifunctor'[smc_cs_intros]:
  assumes "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF>' = \<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>"
    and "\<GG>' = \<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>"
  shows "\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1,2) unfolding assms(3,4) ..


subsubsection\<open>Further properties\<close>

lemma smcf_comp_smcf_ntsmcf_comp_assoc:
  assumes "\<NN> : \<HH> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>' : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "(\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>) \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> = \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)"
proof(rule ntsmcf_tdghm_eqI)
  interpret \<NN>: is_ntsmcf \<alpha> \<AA> \<BB> \<HH> \<HH>' \<NN> by (rule assms(1))
  interpret \<FF>: is_semifunctor \<alpha> \<BB> \<CC> \<FF> by (rule assms(2))
  interpret \<GG>: is_semifunctor \<alpha> \<CC> \<DD> \<GG> by (rule assms(3))
  from assms show "(\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>) \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> :
    \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>' : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
  from assms show "\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>) :
    \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>' : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
  from assms show 
    "ntsmcf_tdghm (\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>) =
      ntsmcf_tdghm (\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>))"
    by
      (
        cs_concl
          cs_simp: slicing_commute[symmetric] 
          cs_intro: slicing_intros dghm_comp_dghm_tdghm_comp_assoc
      )
qed simp_all

lemma (in is_ntsmcf) ntsmcf_smcf_ntsmcf_comp_smcf_id[smc_cs_simps]:
  "smcf_id \<BB> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> = \<NN>"
proof(rule ntsmcf_tdghm_eqI)
  show "smcf_id \<BB> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
  show "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
  show "ntsmcf_tdghm (dghm_id \<BB> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>) = ntsmcf_tdghm \<NN>"
    by 
      (
        cs_concl
          cs_simp: slicing_simps slicing_commute[symmetric] 
          cs_intro: smc_cs_intros slicing_intros dg_cs_simps
      )
qed simp_all

lemmas [smc_cs_simps] = is_ntsmcf.ntsmcf_smcf_ntsmcf_comp_smcf_id

lemma smcf_ntsmcf_comp_ntsmcf_smcf_comp_assoc:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<KK> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "(\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>) \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK> = \<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<KK>)"
proof-
  interpret \<NN>: is_ntsmcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<HH>: is_semifunctor \<alpha> \<CC> \<DD> \<HH> by (rule assms(2))
  interpret \<KK>: is_semifunctor \<alpha> \<AA> \<BB> \<KK> by (rule assms(3))
  show ?thesis
    by (rule ntsmcf_tdghm_eqI)
      (
        use assms in
          \<open>
            cs_concl
              cs_simp: smc_cs_simps slicing_commute[symmetric]
              cs_intro:
                smc_cs_intros
                slicing_intros
                dghm_tdghm_comp_tdghm_dghm_comp_assoc
          \<close>
      )+
qed

lemma smcf_ntsmcf_comp_ntsmcf_vcomp: 
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<MM> : \<GG> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows 
    "\<KK> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>) =
      (\<KK> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<MM>) \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<KK> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)"
proof-
  interpret \<KK>: is_semifunctor \<alpha> \<BB> \<CC> \<KK> by (rule assms(1))
  interpret \<MM>: is_ntsmcf \<alpha> \<AA> \<BB> \<GG> \<HH> \<MM> by (rule assms(2))
  interpret \<NN>: is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(3))
  show 
    "\<KK> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>) = \<KK> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<KK> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>)"
  proof(rule ntsmcf_eqI)
    have dom_lhs: "\<D>\<^sub>\<circ> ((\<KK> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
      unfolding dghm_tdghm_comp_components smc_cs_simps by simp
    have dom_rhs: 
      "\<D>\<^sub>\<circ> ((\<KK> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<KK> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
      unfolding ntsmcf_vcomp_components smc_cs_simps by simp
    show
      "(\<KK> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr> =
        (\<KK> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<KK> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs smc_cs_simps)
      fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
      then show 
        "(\<KK> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
          (\<KK> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<KK> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
    qed (cs_concl cs_intro: smc_cs_intros)+
  qed (cs_concl cs_intro: smc_cs_intros)+
qed

text\<open>\newpage\<close>

end