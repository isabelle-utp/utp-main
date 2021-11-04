(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Semifunctor\<close>
theory CZH_SMC_Semifunctor
  imports 
    CZH_DG_DGHM
    CZH_SMC_Semicategory
begin



subsection\<open>Background\<close>

named_theorems smcf_cs_simps
named_theorems smcf_cs_intros

named_theorems smc_cn_cs_simps
named_theorems smc_cn_cs_intros

lemmas [smc_cs_simps] = dg_shared_cs_simps
lemmas [smc_cs_intros] = dg_shared_cs_intros


subsubsection\<open>Slicing\<close>

definition smcf_dghm :: "V \<Rightarrow> V"
  where "smcf_dghm \<CC> = 
    [\<CC>\<lparr>ObjMap\<rparr>, \<CC>\<lparr>ArrMap\<rparr>, smc_dg (\<CC>\<lparr>HomDom\<rparr>), smc_dg (\<CC>\<lparr>HomCod\<rparr>)]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smcf_dghm_components:
  shows [slicing_simps]: "smcf_dghm \<FF>\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>"
    and [slicing_simps]: "smcf_dghm \<FF>\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
    and [slicing_commute]: "smcf_dghm \<FF>\<lparr>HomDom\<rparr> = smc_dg (\<FF>\<lparr>HomDom\<rparr>)"
    and [slicing_commute]: "smcf_dghm \<FF>\<lparr>HomCod\<rparr> = smc_dg (\<FF>\<lparr>HomCod\<rparr>)"
  unfolding smcf_dghm_def dghm_field_simps by (auto simp: nat_omega_simps)



subsection\<open>Definition and elementary properties\<close>


text\<open>
See Chapter I-3 in \cite{mac_lane_categories_2010} and the description
of the concept of a digraph homomorphism in the previous chapter.
\<close>

locale is_semifunctor = 
  \<Z> \<alpha> +
  vfsequence \<FF> + 
  HomDom: semicategory \<alpha> \<AA> + 
  HomCod: semicategory \<alpha> \<BB> 
  for \<alpha> \<AA> \<BB> \<FF> +
  assumes smcf_length[smc_cs_simps]: "vcard \<FF> = 4\<^sub>\<nat>" 
    and smcf_is_dghm[slicing_intros]: 
      "smcf_dghm \<FF> : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg \<BB>" 
    and smcf_HomDom[smc_cs_simps]: "\<FF>\<lparr>HomDom\<rparr> = \<AA>"
    and smcf_HomCod[smc_cs_simps]: "\<FF>\<lparr>HomCod\<rparr> = \<BB>"
    and smcf_ArrMap_Comp[smc_cs_simps]: "\<lbrakk> g : b \<mapsto>\<^bsub>\<AA>\<^esub> c; f : a \<mapsto>\<^bsub>\<AA>\<^esub> b \<rbrakk> \<Longrightarrow>
      \<FF>\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"

syntax "_is_semifunctor" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_semifunctor \<alpha> \<AA> \<BB> \<FF>"

abbreviation (input) is_cn_semifunctor :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "is_cn_semifunctor \<alpha> \<AA> \<BB> \<FF> \<equiv> \<FF> : op_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"

syntax "_is_cn_semifunctor" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool" 
  (\<open>(_ :/ _ \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>" \<rightharpoonup> "CONST is_cn_semifunctor \<alpha> \<AA> \<BB> \<FF>"

abbreviation all_smcfs :: "V \<Rightarrow> V"
  where "all_smcfs \<alpha> \<equiv> set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation smcfs :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "smcfs \<alpha> \<AA> \<BB> \<equiv> set {\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"

lemmas [smc_cs_simps] =
  is_semifunctor.smcf_HomDom
  is_semifunctor.smcf_HomCod
  is_semifunctor.smcf_ArrMap_Comp

lemma smcf_is_dghm'[slicing_intros]:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<AA>' = smc_dg \<AA>"
    and "\<BB>' = smc_dg \<BB>"
  shows "smcf_dghm \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>'"
  using assms(1) unfolding assms(2,3) by (rule is_semifunctor.smcf_is_dghm)

lemma cn_dghm_comp_is_dghm: 
  assumes "\<FF> : op_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "smcf_dghm \<FF> : op_dg (smc_dg \<AA>) \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg \<BB>"
  using assms 
  unfolding slicing_simps slicing_commute
  by (cs_concl cs_intro: slicing_intros)

lemma cn_dghm_comp_is_dghm'[slicing_intros]: 
  assumes "\<FF> : op_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<AA>' = op_dg (smc_dg \<AA>)"
    and "\<BB>' = smc_dg \<BB>"
  shows "smcf_dghm \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>'"
  using assms(1) unfolding assms(2,3) by (rule cn_dghm_comp_is_dghm)


text\<open>Rules.\<close>

lemma (in is_semifunctor) is_semifunctor_axioms'[smc_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_semifunctor_axioms)

mk_ide rf is_semifunctor_def[unfolded is_semifunctor_axioms_def]
  |intro is_semifunctorI|
  |dest is_semifunctorD[dest]|
  |elim is_semifunctorE[elim]|

lemmas [smc_cs_intros] =
  is_semifunctorD(3,4)

lemma is_semifunctorI':
  assumes "\<Z> \<alpha>" 
    and "vfsequence \<FF>" 
    and "semicategory \<alpha> \<AA>"
    and "semicategory \<alpha> \<BB>" 
    and "vcard \<FF> = 4\<^sub>\<nat>"
    and "\<FF>\<lparr>HomDom\<rparr> = \<AA>"
    and "\<FF>\<lparr>HomCod\<rparr> = \<BB>"
    and "vsv (\<FF>\<lparr>ObjMap\<rparr>)"
    and "vsv (\<FF>\<lparr>ArrMap\<rparr>)"
    and "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    and "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
    and "\<And>a b f. f : a \<mapsto>\<^bsub>\<AA>\<^esub> b \<Longrightarrow>
      \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    and "\<And>b c g a f. \<lbrakk> g : b \<mapsto>\<^bsub>\<AA>\<^esub> c; f : a \<mapsto>\<^bsub>\<AA>\<^esub> b \<rbrakk> \<Longrightarrow>
      \<FF>\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  by (intro is_semifunctorI is_dghmI, unfold smcf_dghm_components slicing_simps)
    (simp_all add: assms smcf_dghm_def nat_omega_simps semicategory.smc_digraph)

lemma is_semifunctorD':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<Z> \<alpha>" 
    and "vfsequence \<FF>" 
    and "semicategory \<alpha> \<AA>"
    and "semicategory \<alpha> \<BB>" 
    and "vcard \<FF> = 4\<^sub>\<nat>"
    and "\<FF>\<lparr>HomDom\<rparr> = \<AA>"
    and "\<FF>\<lparr>HomCod\<rparr> = \<BB>"
    and "vsv (\<FF>\<lparr>ObjMap\<rparr>)"
    and "vsv (\<FF>\<lparr>ArrMap\<rparr>)"
    and "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    and "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
    and "\<And>a b f. f : a \<mapsto>\<^bsub>\<AA>\<^esub> b \<Longrightarrow>
      \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    and "\<And>b c g a f. \<lbrakk> g : b \<mapsto>\<^bsub>\<AA>\<^esub> c; f : a \<mapsto>\<^bsub>\<AA>\<^esub> b \<rbrakk> \<Longrightarrow>
      \<FF>\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
  by
    (
      simp_all add: 
        is_semifunctorD(2-9)[OF assms] 
        is_dghmD[OF is_semifunctorD(6)[OF assms], unfolded slicing_simps]
    )

lemma is_semifunctorE':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  obtains "\<Z> \<alpha>" 
    and "vfsequence \<FF>" 
    and "semicategory \<alpha> \<AA>"
    and "semicategory \<alpha> \<BB>" 
    and "vcard \<FF> = 4\<^sub>\<nat>"
    and "\<FF>\<lparr>HomDom\<rparr> = \<AA>"
    and "\<FF>\<lparr>HomCod\<rparr> = \<BB>"
    and "vsv (\<FF>\<lparr>ObjMap\<rparr>)"
    and "vsv (\<FF>\<lparr>ArrMap\<rparr>)"
    and "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    and "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
    and "\<And>a b f. f : a \<mapsto>\<^bsub>\<AA>\<^esub> b \<Longrightarrow>
      \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    and "\<And>b c g a f. \<lbrakk> g : b \<mapsto>\<^bsub>\<AA>\<^esub> c; f : a \<mapsto>\<^bsub>\<AA>\<^esub> b \<rbrakk> \<Longrightarrow>
      \<FF>\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
  using assms by (simp add: is_semifunctorD')


text\<open>Slicing.\<close>

context is_semifunctor
begin

interpretation dghm: is_dghm \<alpha> \<open>smc_dg \<AA>\<close> \<open>smc_dg \<BB>\<close> \<open>smcf_dghm \<FF>\<close>
  by (rule smcf_is_dghm)

sublocale ObjMap: vsv \<open>\<FF>\<lparr>ObjMap\<rparr>\<close>
  by (rule dghm.ObjMap.vsv_axioms[unfolded slicing_simps])
sublocale ArrMap: vsv \<open>\<FF>\<lparr>ArrMap\<rparr>\<close>
  by (rule dghm.ArrMap.vsv_axioms[unfolded slicing_simps])

lemmas_with [unfolded slicing_simps]:
  smcf_ObjMap_vsv = dghm.dghm_ObjMap_vsv
  and smcf_ArrMap_vsv = dghm.dghm_ArrMap_vsv
  and smcf_ObjMap_vdomain[smc_cs_simps] = dghm.dghm_ObjMap_vdomain
  and smcf_ObjMap_vrange = dghm.dghm_ObjMap_vrange
  and smcf_ArrMap_vdomain[smc_cs_simps] = dghm.dghm_ArrMap_vdomain
  and smcf_ArrMap_is_arr = dghm.dghm_ArrMap_is_arr
  and smcf_ArrMap_is_arr''[smc_cs_intros] = dghm.dghm_ArrMap_is_arr''
  and smcf_ArrMap_is_arr'[smc_cs_intros] = dghm.dghm_ArrMap_is_arr'
  and smcf_ObjMap_app_in_HomCod_Obj[smc_cs_intros] = 
    dghm.dghm_ObjMap_app_in_HomCod_Obj
  and smcf_ArrMap_vrange = dghm.dghm_ArrMap_vrange
  and smcf_ArrMap_app_in_HomCod_Arr[smc_cs_intros] = 
    dghm.dghm_ArrMap_app_in_HomCod_Arr
  and smcf_ObjMap_vsubset_Vset = dghm.dghm_ObjMap_vsubset_Vset
  and smcf_ArrMap_vsubset_Vset = dghm.dghm_ArrMap_vsubset_Vset
  and smcf_ObjMap_in_Vset = dghm.dghm_ObjMap_in_Vset
  and smcf_ArrMap_in_Vset = dghm.dghm_ArrMap_in_Vset
  and smcf_is_dghm_if_ge_Limit = dghm.dghm_is_dghm_if_ge_Limit
  and smcf_is_arr_HomCod = dghm.dghm_is_arr_HomCod
  and smcf_vimage_dghm_ArrMap_vsubset_Hom = 
    dghm.dghm_vimage_dghm_ArrMap_vsubset_Hom

end

lemmas [smc_cs_simps] =
  is_semifunctor.smcf_ObjMap_vdomain
  is_semifunctor.smcf_ArrMap_vdomain

lemmas [smc_cs_intros] =
  is_semifunctor.smcf_ObjMap_app_in_HomCod_Obj
  is_semifunctor.smcf_ArrMap_app_in_HomCod_Arr
  is_semifunctor.smcf_ArrMap_is_arr'


text\<open>Elementary properties.\<close>

lemma cn_smcf_ArrMap_Comp[smc_cs_simps]:
  assumes "semicategory \<alpha> \<AA>"
    and "\<FF> : op_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "g : c \<mapsto>\<^bsub>\<AA>\<^esub> b"
    and "f : b \<mapsto>\<^bsub>\<AA>\<^esub> a"
  shows "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> g\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
proof-
  from assms(3,4) have gf:
    "\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>op_smc \<AA>\<^esub> f\<rparr>"
    by
      (
        force
          intro: is_semifunctor.smcf_ArrMap_Comp[OF assms(2), symmetric]
          simp: slicing_simps smc_op_simps
      )
  from assms show ?thesis
    unfolding gf by (cs_concl cs_simp: smc_op_simps) 
qed

lemma smcf_eqI:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<GG>\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>"
    and "\<GG>\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
    and "\<AA> = \<CC>"
    and "\<BB> = \<DD>"
  shows "\<GG> = \<FF>"
proof-
  interpret L: is_semifunctor \<alpha> \<AA> \<BB> \<GG> by (rule assms(1))
  interpret R: is_semifunctor \<alpha> \<CC> \<DD> \<FF> by (rule assms(2))
  show ?thesis
  proof(rule vsv_eqI)
    have dom: "\<D>\<^sub>\<circ> \<GG> = 4\<^sub>\<nat>" by (cs_concl cs_simp: smc_cs_simps V_cs_simps)
    show "\<D>\<^sub>\<circ> \<GG> = \<D>\<^sub>\<circ> \<FF>" by (cs_concl cs_simp: smc_cs_simps V_cs_simps)
    from assms(5,6) have sup: "\<GG>\<lparr>HomDom\<rparr> = \<FF>\<lparr>HomDom\<rparr>" "\<GG>\<lparr>HomCod\<rparr> = \<FF>\<lparr>HomCod\<rparr>" 
      by (simp_all add: smc_cs_simps)
    show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<GG> \<Longrightarrow> \<GG>\<lparr>a\<rparr> = \<FF>\<lparr>a\<rparr>" for a 
      by (unfold dom, elim_in_numeral, insert assms(3,4) sup)
        (auto simp: dghm_field_simps)
  qed auto
qed

lemma smcf_dghm_eqI:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<AA> = \<CC>"
    and "\<BB> = \<DD>"
    and "smcf_dghm \<GG> = smcf_dghm \<FF>"
  shows "\<GG> = \<FF>"
proof(rule smcf_eqI)
  from assms(5) have 
    "smcf_dghm \<GG>\<lparr>ObjMap\<rparr> = smcf_dghm \<FF>\<lparr>ObjMap\<rparr>"
    "smcf_dghm \<GG>\<lparr>ArrMap\<rparr> = smcf_dghm \<FF>\<lparr>ArrMap\<rparr>"
    by simp_all
  then show "\<GG>\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>" "\<GG>\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
    unfolding slicing_simps by simp_all
qed (auto intro: assms(1,2) simp: assms)

lemma (in is_semifunctor) smcf_def: 
  "\<FF> = [\<FF>\<lparr>ObjMap\<rparr>, \<FF>\<lparr>ArrMap\<rparr>, \<FF>\<lparr>HomDom\<rparr>, \<FF>\<lparr>HomCod\<rparr>]\<^sub>\<circ>"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> \<FF> = 4\<^sub>\<nat>" by (cs_concl cs_simp: smc_cs_simps V_cs_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> [\<FF>\<lparr>Obj\<rparr>, \<FF>\<lparr>Arr\<rparr>, \<FF>\<lparr>Dom\<rparr>, \<FF>\<lparr>Cod\<rparr>]\<^sub>\<circ> = 4\<^sub>\<nat>"
    by (simp add: nat_omega_simps)
  then show "\<D>\<^sub>\<circ> \<FF> = \<D>\<^sub>\<circ> [\<FF>\<lparr>ObjMap\<rparr>, \<FF>\<lparr>ArrMap\<rparr>, \<FF>\<lparr>HomDom\<rparr>, \<FF>\<lparr>HomCod\<rparr>]\<^sub>\<circ>"
    unfolding dom_lhs dom_rhs by (simp add: nat_omega_simps)
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<FF> \<Longrightarrow> \<FF>\<lparr>a\<rparr> = [\<FF>\<lparr>ObjMap\<rparr>, \<FF>\<lparr>ArrMap\<rparr>, \<FF>\<lparr>HomDom\<rparr>, \<FF>\<lparr>HomCod\<rparr>]\<^sub>\<circ>\<lparr>a\<rparr>" 
    for a
    by (unfold dom_lhs, elim_in_numeral, unfold dghm_field_simps)
      (simp_all add: nat_omega_simps)
qed (auto simp: vsv_axioms)

lemma (in is_semifunctor) smcf_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<FF> \<in>\<^sub>\<circ> Vset \<beta>"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  note [smc_cs_intros] = 
    smcf_ObjMap_in_Vset 
    smcf_ArrMap_in_Vset 
    HomDom.smc_in_Vset 
    HomCod.smc_in_Vset
  from assms(2) show ?thesis
    by (subst smcf_def) 
      (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros V_cs_intros)
qed

lemma (in is_semifunctor) smcf_is_semifunctor_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<beta>\<^esub> \<BB>"
  by (rule is_semifunctorI)
    (
      simp_all add: 
        assms 
        vfsequence_axioms
        smcf_is_dghm_if_ge_Limit
        HomDom.smc_semicategory_if_ge_Limit
        HomCod.smc_semicategory_if_ge_Limit
        smc_cs_simps
    )

lemma small_all_smcfs[simp]: "small {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(cases \<open>\<Z> \<alpha>\<close>)
  case True
  from is_semifunctor.smcf_in_Vset show ?thesis
    by (intro down[of _ \<open>Vset (\<alpha> + \<omega>)\<close>]) 
      (auto simp: True \<Z>.\<Z>_Limit_\<alpha>\<omega> \<Z>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>.intro \<Z>.\<Z>_\<alpha>_\<alpha>\<omega>)
next
  case False
  then have "{\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>} = {}" by auto
  then show ?thesis by simp
qed

lemma (in is_semifunctor) smcf_in_Vset_7: "\<FF> \<in>\<^sub>\<circ> Vset (\<alpha> + 7\<^sub>\<nat>)"
proof-
  note [folded VPow_iff, folded Vset_succ[OF Ord_\<alpha>], smc_cs_intros] =
    smcf_ObjMap_vsubset_Vset 
    smcf_ArrMap_vsubset_Vset
  from HomDom.smc_semicategory_in_Vset_4 have [smc_cs_intros]:
    "\<AA> \<in>\<^sub>\<circ> Vset (succ (succ (succ (succ \<alpha>))))"
    by (succ_of_numeral) (cs_prems cs_simp: plus_V_succ_right V_cs_simps)
  from HomCod.smc_semicategory_in_Vset_4 have [smc_cs_intros]:
    "\<BB> \<in>\<^sub>\<circ> Vset (succ (succ (succ (succ \<alpha>))))"
    by (succ_of_numeral) (cs_prems cs_simp: plus_V_succ_right V_cs_simps)
  show ?thesis
    by (subst smcf_def, succ_of_numeral)
      (
        cs_concl 
          cs_simp: plus_V_succ_right V_cs_simps smc_cs_simps 
          cs_intro: smc_cs_intros V_cs_intros
      )
qed

lemma (in \<Z>) all_smcfs_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "all_smcfs \<alpha> \<in>\<^sub>\<circ> Vset \<beta>"
proof(rule vsubset_in_VsetI)
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "all_smcfs \<alpha> \<subseteq>\<^sub>\<circ> Vset (\<alpha> + 7\<^sub>\<nat>)"
  proof(intro vsubsetI)
    fix \<FF> assume "\<FF> \<in>\<^sub>\<circ> all_smcfs \<alpha>"
    then obtain \<AA> \<BB> where \<FF>: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by clarsimp
    then interpret is_semifunctor \<alpha> \<AA> \<BB> \<FF> .
    show "\<FF> \<in>\<^sub>\<circ> Vset (\<alpha> + 7\<^sub>\<nat>)" by (rule smcf_in_Vset_7)
  qed
  from assms(2) show "Vset (\<alpha> + 7\<^sub>\<nat>) \<in>\<^sub>\<circ> Vset \<beta>"
    by (cs_concl cs_intro: V_cs_intros Ord_cs_intros)
qed

lemma small_smcfs[simp]: "small {\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"
  by (rule down[of _ \<open>set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}\<close>]) auto



subsection\<open>Opposite semifunctor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter II-2 in \cite{mac_lane_categories_2010}.\<close>

definition op_smcf :: "V \<Rightarrow> V"
  where "op_smcf \<FF> =
    [\<FF>\<lparr>ObjMap\<rparr>, \<FF>\<lparr>ArrMap\<rparr>, op_smc (\<FF>\<lparr>HomDom\<rparr>), op_smc (\<FF>\<lparr>HomCod\<rparr>)]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma op_smcf_components[smc_op_simps]:
  shows "op_smcf \<FF>\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>"
    and "op_smcf \<FF>\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
    and "op_smcf \<FF>\<lparr>HomDom\<rparr> = op_smc (\<FF>\<lparr>HomDom\<rparr>)"
    and "op_smcf \<FF>\<lparr>HomCod\<rparr> = op_smc (\<FF>\<lparr>HomCod\<rparr>)"
  unfolding op_smcf_def dghm_field_simps by (auto simp: nat_omega_simps)


text\<open>Slicing.\<close>

lemma op_dghm_smcf_dghm[slicing_commute]: 
  "op_dghm (smcf_dghm \<FF>) = smcf_dghm (op_smcf \<FF>)"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> (op_dghm (smcf_dghm \<FF>)) = 4\<^sub>\<nat>"
    unfolding op_dghm_def by (auto simp: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (smcf_dghm (op_smcf \<FF>)) = 4\<^sub>\<nat>"
    unfolding smcf_dghm_def by (auto simp: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (op_dghm (smcf_dghm \<FF>)) = \<D>\<^sub>\<circ> (smcf_dghm (op_smcf \<FF>))"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (op_dghm (smcf_dghm \<FF>)) \<Longrightarrow>
    op_dghm (smcf_dghm \<FF>)\<lparr>a\<rparr> = smcf_dghm (op_smcf \<FF>)\<lparr>a\<rparr>"
    for a
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral,
        unfold smcf_dghm_def op_smcf_def op_dghm_def dghm_field_simps
      ) 
      (auto simp: nat_omega_simps slicing_simps slicing_commute)
qed (auto simp: smcf_dghm_def op_dghm_def)


subsubsection\<open>Further properties\<close>

lemma (in is_semifunctor) is_semifunctor_op:
  "op_smcf \<FF> : op_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> op_smc \<BB>"
proof(intro is_semifunctorI)
  show "vfsequence (op_smcf \<FF>)" unfolding op_smcf_def by simp
  show "vcard (op_smcf \<FF>) = 4\<^sub>\<nat>" 
    unfolding op_smcf_def by (auto simp: nat_omega_simps)
  fix g b c f a assume "g : b \<mapsto>\<^bsub>op_smc \<AA>\<^esub> c" "f : a \<mapsto>\<^bsub>op_smc \<AA>\<^esub> b"
  then have "g : c \<mapsto>\<^bsub>\<AA>\<^esub> b" and "f : b \<mapsto>\<^bsub>\<AA>\<^esub> a"  
    unfolding smc_op_simps by simp_all
  with is_semifunctor_axioms show 
    "op_smcf \<FF>\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>op_smc \<AA>\<^esub> f\<rparr> =
      op_smcf \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>op_smc \<BB>\<^esub> op_smcf \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
    by 
      (
        cs_concl 
          cs_simp: smc_op_simps smc_cs_simps 
          cs_intro: smc_op_intros smc_cs_intros
      )
qed 
  (
    auto simp: 
      smc_cs_simps
      smc_op_simps
      slicing_simps
      slicing_commute[symmetric]
      is_dghm.is_dghm_op 
      smcf_is_dghm
      HomCod.semicategory_op 
      HomDom.semicategory_op
  )

lemma (in is_semifunctor) is_semifunctor_op':  
  assumes "\<AA>' = op_smc \<AA>" and "\<BB>' = op_smc \<BB>" and "\<alpha>' = \<alpha>"
  shows "op_smcf \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_semifunctor_op)

lemmas is_semifunctor_op'[smc_op_intros] = is_semifunctor.is_semifunctor_op'

lemma (in is_semifunctor) smcf_op_smcf_op_smcf[smc_op_simps]: 
  "op_smcf (op_smcf \<FF>) = \<FF>" 
proof(rule smcf_eqI, unfold smc_op_simps)
  show "op_smcf (op_smcf \<FF>) : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by 
      (
        metis 
          HomCod.smc_op_smc_op_smc 
          HomDom.smc_op_smc_op_smc 
          is_semifunctor.is_semifunctor_op 
          is_semifunctor_op
      )
qed (simp_all add: is_semifunctor_axioms)

lemmas smcf_op_smcf_op_smcf[smc_op_simps] = is_semifunctor.smcf_op_smcf_op_smcf

lemma eq_op_smcf_iff[smc_op_simps]: 
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "op_smcf \<GG> = op_smcf \<FF> \<longleftrightarrow> \<GG> = \<FF>"
proof
  interpret L: is_semifunctor \<alpha> \<AA> \<BB> \<GG> by (rule assms(1))
  interpret R: is_semifunctor \<alpha> \<CC> \<DD> \<FF> by (rule assms(2))
  assume prems: "op_smcf \<GG> = op_smcf \<FF>"
  show "\<GG> = \<FF>"
  proof(rule smcf_eqI[OF assms])
    from prems R.smcf_op_smcf_op_smcf L.smcf_op_smcf_op_smcf show 
      "\<GG>\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>" and "\<GG>\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
      by metis+
    from prems R.smcf_op_smcf_op_smcf L.smcf_op_smcf_op_smcf have 
      "\<GG>\<lparr>HomDom\<rparr> = \<FF>\<lparr>HomDom\<rparr>" "\<GG>\<lparr>HomCod\<rparr> = \<FF>\<lparr>HomCod\<rparr>"
      by auto
    then show "\<AA> = \<CC>" "\<BB> = \<DD>" by (simp_all add: smc_cs_simps)
  qed
qed auto



subsection\<open>Composition of covariant semifunctors\<close>


subsubsection\<open>Definition and elementary properties\<close>

abbreviation (input) smcf_comp :: "V \<Rightarrow> V \<Rightarrow> V" (infixl "\<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F" 55)
  where "smcf_comp \<equiv> dghm_comp"


text\<open>Slicing.\<close>

lemma smcf_dghm_smcf_comp[slicing_commute]: 
  "smcf_dghm \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M smcf_dghm \<FF> = smcf_dghm (\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>)"
  unfolding dghm_comp_def smcf_dghm_def dghm_field_simps 
  by (simp add: nat_omega_simps)


subsubsection\<open>Object map\<close>

lemma smcf_comp_ObjMap_vsv[smc_cs_intros]: 
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "vsv ((\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>)"
proof-
  interpret L: is_semifunctor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_comp_ObjMap_vsv
          [
            OF L.smcf_is_dghm R.smcf_is_dghm, 
            unfolded slicing_simps slicing_commute
          ]
      )
qed

lemma smcf_comp_ObjMap_vdomain[smc_cs_simps]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
proof-
  interpret L: is_semifunctor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_comp_ObjMap_vdomain
          [
            OF L.smcf_is_dghm R.smcf_is_dghm, 
            unfolded slicing_simps slicing_commute
          ]
      )
qed

lemma smcf_comp_ObjMap_vrange:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
proof-
  interpret L: is_semifunctor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_comp_ObjMap_vrange
          [
            OF L.smcf_is_dghm R.smcf_is_dghm, 
            unfolded slicing_simps slicing_commute
          ]
      )
qed

lemma smcf_comp_ObjMap_app[smc_cs_simps]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and [simp]: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "(\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
proof-
  interpret L: is_semifunctor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_comp_ObjMap_app
          [
            OF L.smcf_is_dghm R.smcf_is_dghm, 
            unfolded slicing_simps slicing_commute, 
            OF assms(3)
          ]
      )
qed


subsubsection\<open>Arrow map\<close>

lemma smcf_comp_ArrMap_vsv[smc_cs_intros]: 
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "vsv ((\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>)"
proof-
  interpret L: is_semifunctor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis 
    by 
      (
        rule dghm_comp_ArrMap_vsv
          [
            OF L.smcf_is_dghm R.smcf_is_dghm, 
            unfolded slicing_simps slicing_commute
          ]
      )
qed

lemma smcf_comp_ArrMap_vdomain[smc_cs_simps]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
proof-
  interpret L: is_semifunctor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_comp_ArrMap_vdomain
          [
            OF L.smcf_is_dghm R.smcf_is_dghm, 
            unfolded slicing_simps slicing_commute
          ]
      )
qed

lemma smcf_comp_ArrMap_vrange:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof-
  interpret L: is_semifunctor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_comp_ArrMap_vrange
          [
            OF L.smcf_is_dghm R.smcf_is_dghm, 
            unfolded slicing_simps slicing_commute
          ]
      )
qed

lemma smcf_comp_ArrMap_app[smc_cs_simps]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and [simp]: "f \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
  shows "(\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr>"
proof-
  interpret L: is_semifunctor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_comp_ArrMap_app
          [
            OF L.smcf_is_dghm R.smcf_is_dghm, 
            unfolded slicing_simps slicing_commute,
            OF assms(3)
          ]
      )
qed


subsubsection\<open>Further properties\<close>

lemma smcf_comp_is_semifunctor[smc_cs_intros]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret L: is_semifunctor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1))
  interpret R: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
  proof(rule is_semifunctorI, unfold dghm_comp_components(3,4))
    show "vfsequence (\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>)" by (simp add: dghm_comp_def)
    show "vcard (\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>) = 4\<^sub>\<nat>"  
      unfolding dghm_comp_def by (simp add: nat_omega_simps)
    fix g b c f a assume "g : b \<mapsto>\<^bsub>\<AA>\<^esub> c" "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
    with assms show "(\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f\<rparr> = 
      (\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
  qed 
    (
      auto 
        simp: slicing_commute[symmetric] smc_cs_simps smc_cs_intros 
        intro: dg_cs_intros slicing_intros
    )
qed 

lemma smcf_comp_assoc[smc_cs_simps]:
  assumes "\<HH> : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" 
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "(\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>) \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> = \<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>)"
proof(rule smcf_eqI[of \<alpha> \<AA> \<DD> _ \<AA> \<DD>])
  interpret \<HH>: is_semifunctor \<alpha> \<CC> \<DD> \<HH> by (rule assms(1)) 
  interpret \<GG>: is_semifunctor \<alpha> \<BB> \<CC> \<GG> by (rule assms(2)) 
  interpret \<FF>: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(3)) 
  from \<FF>.is_semifunctor_axioms \<GG>.is_semifunctor_axioms \<HH>.is_semifunctor_axioms 
  show "\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F (\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>) : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" 
    and "\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"  
    by (auto intro: smc_cs_intros)
qed (simp_all add: dghm_comp_components vcomp_assoc)

lemma op_smcf_smcf_comp[smc_op_simps]: 
  "op_smcf (\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>) = op_smcf \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F op_smcf \<FF>"
  unfolding dghm_comp_def op_smcf_def dghm_field_simps 
  by (simp add: nat_omega_simps)



subsection\<open>Composition of contravariant semifunctors\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See section 1.2 in \cite{bodo_categories_1970}.\<close>

definition smcf_cn_comp :: "V \<Rightarrow> V \<Rightarrow> V" (infixl \<open>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ>\<close> 55)
  where "\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF> =
    [
      \<GG>\<lparr>ObjMap\<rparr> \<circ>\<^sub>\<circ> \<FF>\<lparr>ObjMap\<rparr>, 
      \<GG>\<lparr>ArrMap\<rparr> \<circ>\<^sub>\<circ> \<FF>\<lparr>ArrMap\<rparr>, 
      op_smc (\<FF>\<lparr>HomDom\<rparr>), 
      \<GG>\<lparr>HomCod\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smcf_cn_comp_components:
  shows "(\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr> = \<GG>\<lparr>ObjMap\<rparr> \<circ>\<^sub>\<circ> \<FF>\<lparr>ObjMap\<rparr>"
    and "(\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr> = \<GG>\<lparr>ArrMap\<rparr> \<circ>\<^sub>\<circ> \<FF>\<lparr>ArrMap\<rparr>"
    and [smc_cn_cs_simps]: "(\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>HomDom\<rparr> = op_smc (\<FF>\<lparr>HomDom\<rparr>)"
    and [smc_cn_cs_simps]: "(\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>HomCod\<rparr> = \<GG>\<lparr>HomCod\<rparr>"
  unfolding smcf_cn_comp_def dghm_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smcf_dghm_smcf_cn_comp[slicing_commute]: 
  "smcf_dghm \<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> smcf_dghm \<FF> = smcf_dghm (\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)"
  unfolding dghm_cn_comp_def smcf_cn_comp_def smcf_dghm_def  
  by (simp add: nat_omega_simps slicing_commute dghm_field_simps)


subsubsection\<open>Object map: two contravariant semifunctors\<close>

lemma smcf_cn_comp_ObjMap_vsv[smc_cn_cs_intros]: 
  assumes "\<GG> : \<BB> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "vsv ((\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr>)"
proof-
  interpret L: is_semifunctor \<alpha> \<open>op_smc \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<open>op_smc \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_cn_cov_comp_ObjMap_vsv
          [
            OF 
              L.smcf_is_dghm[unfolded slicing_commute[symmetric]] 
              R.smcf_is_dghm[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma smcf_cn_comp_ObjMap_vdomain[smc_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
proof-
  interpret L: is_semifunctor \<alpha> \<open>op_smc \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<open>op_smc \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_cn_comp_ObjMap_vdomain
          [
            OF 
              L.smcf_is_dghm[unfolded slicing_commute[symmetric]] 
              R.smcf_is_dghm[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma smcf_cn_comp_ObjMap_vrange:
  assumes "\<GG> : \<BB> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
proof-
  interpret L: is_semifunctor \<alpha> \<open>op_smc \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<open>op_smc \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_cn_comp_ObjMap_vrange
          [
            OF 
              L.smcf_is_dghm[unfolded slicing_commute[symmetric]] 
              R.smcf_is_dghm[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma smcf_cn_comp_ObjMap_app[smc_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "(\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
proof-
  interpret L: is_semifunctor \<alpha> \<open>op_smc \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<open>op_smc \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_cn_comp_ObjMap_app
          [
            OF 
              L.smcf_is_dghm[unfolded slicing_commute[symmetric]] 
              R.smcf_is_dghm[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps, 
            OF assms(3)
          ]
      )
qed


subsubsection\<open>Arrow map: two contravariant semifunctors\<close>

lemma smcf_cn_comp_ArrMap_vsv[smc_cn_cs_intros]: 
  assumes "\<GG> : \<BB> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "vsv ((\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>)"
proof-
  interpret L: is_semifunctor \<alpha> \<open>op_smc \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<open>op_smc \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_cn_cov_comp_ArrMap_vsv
          [
            OF 
              L.smcf_is_dghm[unfolded slicing_commute[symmetric]] 
              R.smcf_is_dghm[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma smcf_cn_comp_ArrMap_vdomain[smc_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
proof-
  interpret L: is_semifunctor \<alpha> \<open>op_smc \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<open>op_smc \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_cn_comp_ArrMap_vdomain
          [
            OF 
              L.smcf_is_dghm[unfolded slicing_commute[symmetric]] 
              R.smcf_is_dghm[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma smcf_cn_comp_ArrMap_vrange:
  assumes "\<GG> : \<BB> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof-
  interpret L: is_semifunctor \<alpha> \<open>op_smc \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<open>op_smc \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_cn_comp_ArrMap_vrange
          [
            OF 
              L.smcf_is_dghm[unfolded slicing_commute[symmetric]] 
              R.smcf_is_dghm[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma smcf_cn_comp_ArrMap_app[smc_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
  shows "(\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>\<rparr>"
proof-
  interpret L: is_semifunctor \<alpha> \<open>op_smc \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<open>op_smc \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_cn_comp_ArrMap_app
          [
            OF 
              L.smcf_is_dghm[unfolded slicing_commute[symmetric]] 
              R.smcf_is_dghm[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps,
            OF assms(3)
          ]
      )
qed


subsubsection\<open>Object map: contravariant and covariant semifunctors\<close>

lemma smcf_cn_cov_comp_ObjMap_vsv[smc_cn_cs_intros]: 
  assumes "\<GG> : \<BB> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "vsv ((\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr>)"
proof-
  interpret L: is_semifunctor \<alpha> \<open>op_smc \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_cn_cov_comp_ObjMap_vsv
          [
            OF 
              L.smcf_is_dghm[unfolded slicing_commute[symmetric]]
              R.smcf_is_dghm[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma smcf_cn_cov_comp_ObjMap_vdomain[smc_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
proof-
  interpret L: is_semifunctor \<alpha> \<open>op_smc \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_cn_cov_comp_ObjMap_vdomain
          [
            OF 
              L.smcf_is_dghm[unfolded slicing_commute[symmetric]] 
              R.smcf_is_dghm,
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma smcf_cn_cov_comp_ObjMap_vrange:
  assumes "\<GG> : \<BB> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
proof-
  interpret L: is_semifunctor \<alpha> \<open>op_smc \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_cn_cov_comp_ObjMap_vrange
          [
            OF 
              L.smcf_is_dghm[unfolded slicing_commute[symmetric]] 
              R.smcf_is_dghm,
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma smcf_cn_cov_comp_ObjMap_app[smc_cn_cs_simps]:
    assumes "\<GG> : \<BB> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "(\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
proof-
  interpret L: is_semifunctor \<alpha> \<open>op_smc \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_cn_cov_comp_ObjMap_app
          [
            OF 
              L.smcf_is_dghm[unfolded slicing_commute[symmetric]] 
              R.smcf_is_dghm,
            unfolded slicing_commute slicing_simps,
            OF assms(3)
          ]
      )
qed


subsubsection\<open>Arrow map: contravariant and covariant semifunctors\<close>

lemma smcf_cn_cov_comp_ArrMap_vsv[smc_cn_cs_intros]: 
  assumes "\<GG> : \<BB> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "vsv ((\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>)"
proof-
  interpret L: is_semifunctor \<alpha> \<open>op_smc \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_cn_cov_comp_ArrMap_vsv
          [
            OF 
              L.smcf_is_dghm[unfolded slicing_commute[symmetric]]
              R.smcf_is_dghm[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma smcf_cn_cov_comp_ArrMap_vdomain[smc_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
proof-
  interpret L: is_semifunctor \<alpha> \<open>op_smc \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_cn_cov_comp_ArrMap_vdomain
          [
            OF 
              L.smcf_is_dghm[unfolded slicing_commute[symmetric]] 
              R.smcf_is_dghm,
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma smcf_cn_cov_comp_ArrMap_vrange:
  assumes "\<GG> : \<BB> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof-
  interpret L: is_semifunctor \<alpha> \<open>op_smc \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_cn_cov_comp_ArrMap_vrange
          [
            OF 
              L.smcf_is_dghm[unfolded slicing_commute[symmetric]] 
              R.smcf_is_dghm,
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma smcf_cn_cov_comp_ArrMap_app[smc_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "f \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
  shows "(\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr>"
proof-
  interpret L: is_semifunctor \<alpha> \<open>op_smc \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule dghm_cn_cov_comp_ArrMap_app
          [
            OF 
              L.smcf_is_dghm[unfolded slicing_commute[symmetric]] 
              R.smcf_is_dghm,
            unfolded slicing_commute slicing_simps,
            OF assms(3)
          ]
      )
qed


subsubsection\<open>Opposite of the contravariant composition of semifunctors\<close>

lemma op_smcf_smcf_cn_comp[smc_op_simps]: 
  "op_smcf (\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>) = op_smcf \<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> op_smcf \<FF>"
  unfolding op_smcf_def smcf_cn_comp_def dghm_field_simps
  by (auto simp: nat_omega_simps)


subsubsection\<open>Further properties\<close>

lemma smcf_cn_comp_is_semifunctor[smc_cn_cs_intros]:
  \<comment>\<open>See section 1.2 in \cite{bodo_categories_1970}.\<close>
  assumes "semicategory \<alpha> \<AA>" and "\<GG> : \<BB> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret L: is_semifunctor \<alpha> \<open>op_smc \<BB>\<close> \<CC> \<GG> 
    rewrites "f : b \<mapsto>\<^bsub>op_smc \<CC>'\<^esub> a = f : a \<mapsto>\<^bsub>\<CC>'\<^esub> b" for \<CC>' f b a 
    by (rule assms(2)) (simp_all add: smc_op_simps)
  interpret R: is_semifunctor \<alpha> \<open>op_smc \<AA>\<close> \<BB> \<FF> 
    rewrites "f : b \<mapsto>\<^bsub>op_smc \<CC>'\<^esub> a = f : a \<mapsto>\<^bsub>\<CC>'\<^esub> b" for \<CC>' f b a
    by (rule assms(3)) (simp_all add: smc_op_simps)
  interpret \<AA>: semicategory \<alpha> \<AA> by (rule assms(1))
  show ?thesis
  proof(rule is_semifunctorI, unfold smcf_cn_comp_components(3,4) smc_op_simps)
    from assms show "smcf_dghm (\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>) : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg \<CC>"
      by 
        (
          cs_concl 
            cs_simp: slicing_commute[symmetric] 
            cs_intro: dg_cn_cs_intros slicing_intros
        )
    fix g b c f a assume "g : b \<mapsto>\<^bsub>\<AA>\<^esub> c" "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
    with assms show "(\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f\<rparr> = 
      (\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: smc_cs_simps smc_cn_cs_simps smc_op_simps 
            cs_intro: smc_cs_intros
        )
  qed 
    (
      auto simp: 
        smcf_cn_comp_def 
        nat_omega_simps 
        smc_cs_simps
        smc_op_simps 
        smc_cs_intros
    )
qed

lemma smcf_cn_cov_comp_is_semifunctor[smc_cs_intros]:
  \<comment>\<open>See section 1.2 in \cite{bodo_categories_1970}.\<close>
  assumes "\<GG> : \<BB> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF> : \<AA> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret L: is_semifunctor \<alpha> \<open>op_smc \<BB>\<close> \<CC> \<GG> 
    rewrites "f : b \<mapsto>\<^bsub>op_smc \<CC>'\<^esub> a = f : a \<mapsto>\<^bsub>\<CC>'\<^esub> b" for \<CC>' f b a 
    by (rule assms(1)) (simp_all add: smc_op_simps)
  interpret R: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
  proof(rule is_semifunctorI, unfold smcf_cn_comp_components(3,4) smc_op_simps)
    from assms show 
      "smcf_dghm (\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>) : smc_dg (op_smc \<AA>) \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg \<CC>"
      by 
        (
          cs_concl 
            cs_simp: slicing_commute[symmetric]
            cs_intro: dg_cn_cs_intros slicing_intros
        )
    show "vfsequence (\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)" unfolding smcf_cn_comp_def by simp
    show "vcard (\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>) = 4\<^sub>\<nat>"
      unfolding smcf_cn_comp_def by (auto simp: nat_omega_simps)
    show "op_smc (\<FF>\<lparr>HomDom\<rparr>) = op_smc \<AA>" by (simp add: smc_cs_simps)
    show "\<GG>\<lparr>HomCod\<rparr> = \<CC>" by (simp add: smc_cs_simps)
    fix g b c f a assume "g : c \<mapsto>\<^bsub>\<AA>\<^esub> b" "f : b \<mapsto>\<^bsub>\<AA>\<^esub> a"
    with assms show 
      "(\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> g\<rparr> = 
        (\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: smc_cs_simps smc_cn_cs_simps smc_op_simps 
            cs_intro: smc_cs_intros
        )
  qed (auto intro: smc_cs_intros smc_op_intros)
qed

lemma smcf_cov_cn_comp_is_semifunctor[smc_cn_cs_intros]:
  \<comment>\<open>See section 1.2 in \cite{bodo_categories_1970}.\<close>
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> : \<AA> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms by (rule smcf_comp_is_semifunctor)



subsection\<open>Identity semifunctor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>

abbreviation (input) smcf_id :: "V \<Rightarrow> V" where "smcf_id \<equiv> dghm_id"


text\<open>Slicing.\<close>

lemma smcf_dghm_smcf_id[slicing_commute]: 
  "dghm_id (smc_dg \<CC>) = smcf_dghm (smcf_id \<CC>)"
  unfolding dghm_id_def smc_dg_def smcf_dghm_def dghm_field_simps dg_field_simps
  by (simp add: nat_omega_simps)

context semicategory
begin

interpretation dg: digraph \<alpha> \<open>smc_dg \<CC>\<close> by (rule smc_digraph)

lemmas_with [unfolded slicing_simps]:
  smc_dghm_id_is_dghm = dg.dg_dghm_id_is_dghm

end


subsubsection\<open>Object map\<close>

lemmas [smc_cs_simps] = dghm_id_ObjMap_app


subsubsection\<open>Arrow map\<close>

lemmas [smc_cs_simps] = dghm_id_ArrMap_app


subsubsection\<open>Opposite identity semifunctor\<close>

lemma op_smcf_smcf_id[smc_op_simps]: "op_smcf (smcf_id \<CC>) = smcf_id (op_smc \<CC>)"
  unfolding dghm_id_def op_smc_def op_smcf_def dghm_field_simps dg_field_simps
  by (auto simp: nat_omega_simps)


subsubsection\<open>An identity semifunctor is a semifunctor\<close>

lemma (in semicategory) smc_smcf_id_is_semifunctor: "smcf_id \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof(rule is_semifunctorI, unfold dghm_id_components)
  from smc_dghm_id_is_dghm show 
    "smcf_dghm (smcf_id \<CC>) : smc_dg \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg \<CC>"
    by (auto simp: slicing_simps slicing_commute)
  fix g b c f a assume "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  then show "vid_on (\<CC>\<lparr>Arr\<rparr>)\<lparr>g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<rparr> = 
    vid_on (\<CC>\<lparr>Arr\<rparr>)\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> vid_on (\<CC>\<lparr>Arr\<rparr>)\<lparr>f\<rparr>"
    by (metis smc_is_arrD(1) smc_Comp_is_arr vid_on_eq_atI)
qed (auto simp: semicategory_axioms dghm_id_def nat_omega_simps)

lemma (in semicategory) smc_smcf_id_is_semifunctor': 
  assumes "\<AA> = \<CC>" and "\<BB> = \<CC>"
  shows "smcf_id \<CC> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  unfolding assms by (rule smc_smcf_id_is_semifunctor)

lemmas [smc_cs_intros] = semicategory.smc_smcf_id_is_semifunctor'


subsubsection\<open>Further properties\<close>

lemma (in is_semifunctor) smcf_smcf_comp_smcf_id_left[smc_cs_simps]:
  \<comment>\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}).\<close>
  "smcf_id \<BB> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> = \<FF>"
  by (rule smcf_eqI, unfold dghm_id_components dghm_comp_components)
    (auto simp: smcf_ObjMap_vrange smcf_ArrMap_vrange intro: smc_cs_intros)

lemmas [smc_cs_simps] = is_semifunctor.smcf_smcf_comp_smcf_id_left

lemma (in is_semifunctor) smcf_smcf_comp_smcf_id_right[smc_cs_simps]: 
  \<comment>\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}).\<close>
  "\<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F smcf_id \<AA> = \<FF>"
  by (rule smcf_eqI, unfold dghm_id_components dghm_comp_components)
    (
      auto 
        simp: smcf_ObjMap_vrange smcf_ArrMap_vrange smc_cs_simps
        intro: smc_cs_intros
    )

lemmas [smc_cs_simps] = is_semifunctor.smcf_smcf_comp_smcf_id_right



subsection\<open>Constant semifunctor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter III-3 in \cite{mac_lane_categories_2010}.\<close>

abbreviation (input) smcf_const :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "smcf_const \<equiv> dghm_const"


text\<open>Slicing.\<close>

lemma smcf_dghm_smcf_const[slicing_commute]: 
  "dghm_const (smc_dg \<CC>) (smc_dg \<DD>) a f = smcf_dghm (smcf_const \<CC> \<DD> a f)"
  unfolding 
    dghm_const_def smc_dg_def smcf_dghm_def dghm_field_simps dg_field_simps
  by (simp add: nat_omega_simps)


subsubsection\<open>Object map\<close>

lemmas [smc_cs_simps] = 
  dghm_const_ObjMap_app 


subsubsection\<open>Arrow map\<close>

lemmas [smc_cs_simps] = 
  dghm_const_ArrMap_app


subsubsection\<open>Opposite constant semifunctor\<close>

lemma op_smcf_smcf_const[smc_op_simps]:
  "op_smcf (smcf_const \<CC> \<DD> a f) = smcf_const (op_smc \<CC>) (op_smc \<DD>) a f"
  unfolding dghm_const_def op_smc_def op_smcf_def dghm_field_simps dg_field_simps
  by (auto simp: nat_omega_simps)


subsubsection\<open>A constant semifunctor is a semifunctor\<close>

lemma smcf_const_is_semifunctor: 
  assumes "semicategory \<alpha> \<CC>"
    and "semicategory \<alpha> \<DD>" 
    and "f : a \<mapsto>\<^bsub>\<DD>\<^esub> a" 
    and [simp]: "f \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> f = f"
  shows "smcf_const \<CC> \<DD> a f : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
proof-
  interpret \<CC>: semicategory \<alpha> \<CC> by (rule assms(1))
  interpret \<DD>: semicategory \<alpha> \<DD> by (rule assms(2))
  show ?thesis
  proof(intro is_semifunctorI, tactic\<open>distinct_subgoals_tac\<close>)
    from assms show 
      "smcf_dghm (dghm_const \<CC> \<DD> a f) : smc_dg \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg \<DD>"
      by 
        ( 
          cs_concl 
            cs_simp: slicing_commute[symmetric] 
            cs_intro: dg_cs_intros slicing_intros
        )
    show "vfsequence (smcf_const \<CC> \<DD> a f)" unfolding dghm_const_def by simp
    show "vcard (smcf_const \<CC> \<DD> a f) = 4\<^sub>\<nat>"
      unfolding dghm_const_def by (simp add: nat_omega_simps)
    fix g' b c f' a' assume "g' : b \<mapsto>\<^bsub>\<CC>\<^esub> c" "f' : a' \<mapsto>\<^bsub>\<CC>\<^esub> b"
    with assms(1-3) show "smcf_const \<CC> \<DD> a f\<lparr>ArrMap\<rparr>\<lparr>g' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'\<rparr> =
      smcf_const \<CC> \<DD> a f\<lparr>ArrMap\<rparr>\<lparr>g'\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> smcf_const \<CC> \<DD> a f\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>"
      by (cs_concl cs_simp: assms(4) smc_cs_simps cs_intro: smc_cs_intros)
  qed (auto simp: assms(1,2) dghm_const_components)
qed 

lemma smcf_const_is_semifunctor'[smc_cs_intros]: 
  assumes "semicategory \<alpha> \<CC>" 
    and "semicategory \<alpha> \<DD>" 
    and "f : a \<mapsto>\<^bsub>\<DD>\<^esub> a"
    and "f \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> f = f"
    and "\<AA> = \<CC>"
    and "\<BB> = \<DD>"
  shows "smcf_const \<CC> \<DD> a f : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms(1-4) unfolding assms(5,6) by (rule smcf_const_is_semifunctor)



subsection\<open>Faithful semifunctor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>

locale is_ft_semifunctor = is_semifunctor \<alpha> \<AA> \<BB> \<FF> for \<alpha> \<AA> \<BB> \<FF> + 
  assumes ft_smcf_is_ft_dghm: 
    "smcf_dghm \<FF> : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> smc_dg \<BB>"

syntax "_is_ft_semifunctor" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_ft_semifunctor \<alpha> \<AA> \<BB> \<FF>"

lemma (in is_ft_semifunctor) ft_smcf_is_ft_dghm'[slicing_intros]:
  assumes "\<AA>' = smc_dg \<AA>" and "\<BB>' = smc_dg \<BB>"
  shows "smcf_dghm \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule ft_smcf_is_ft_dghm)

lemmas [slicing_intros] = is_ft_semifunctor.ft_smcf_is_ft_dghm'


text\<open>Rules.\<close>

lemma (in is_ft_semifunctor) is_ft_semifunctor_axioms'[smcf_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_ft_semifunctor_axioms)

mk_ide rf is_ft_semifunctor_def[unfolded is_ft_semifunctor_axioms_def]
  |intro is_ft_semifunctorI|
  |dest is_ft_semifunctorD[dest]|
  |elim is_ft_semifunctorE[elim]|

lemmas [smcf_cs_intros] = is_ft_semifunctorD(1)

lemma is_ft_semifunctorI':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<And>a b. \<lbrakk> a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow> v11 (\<FF>\<lparr>ArrMap\<rparr> \<restriction>\<^sup>l\<^sub>\<circ> Hom \<AA> a b)"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms
  by (intro is_ft_semifunctorI)
    (
      simp_all add: 
        assms(1) 
        is_ft_dghmI[OF is_semifunctorD(6)[OF assms(1)], unfolded slicing_simps]
    )

lemma is_ft_semifunctorD':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<And>a b. \<lbrakk> a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow> v11 (\<FF>\<lparr>ArrMap\<rparr> \<restriction>\<^sup>l\<^sub>\<circ> Hom \<AA> a b)"
  by 
    (
      simp_all add: 
        is_ft_semifunctorD[OF assms(1)] 
        is_ft_dghmD(2)[
          OF is_ft_semifunctorD(2)[OF assms(1)], unfolded slicing_simps
          ]
    )

lemma is_ft_semifunctorE':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>"
  obtains "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<And>a b. \<lbrakk> a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow> v11 (\<FF>\<lparr>ArrMap\<rparr> \<restriction>\<^sup>l\<^sub>\<circ> Hom \<AA> a b)"
  using assms by (simp_all add: is_ft_semifunctorD')


text\<open>Elementary properties.\<close>

context is_ft_semifunctor
begin

interpretation dghm: is_ft_dghm \<alpha> \<open>smc_dg \<AA>\<close> \<open>smc_dg \<BB>\<close> \<open>smcf_dghm \<FF>\<close>
  by (rule ft_smcf_is_ft_dghm) 

lemmas_with [unfolded slicing_simps]:
  ft_smcf_v11_on_Hom = dghm.ft_dghm_v11_on_Hom

end


subsubsection\<open>Opposite faithful semifunctor\<close>

lemma (in is_ft_semifunctor) is_ft_semifunctor_op: 
  "op_smcf \<FF> : op_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> op_smc \<BB>"   
  by 
    (
      rule is_ft_semifunctorI, 
      unfold smc_op_simps slicing_simps slicing_commute[symmetric]
    )
    (
      simp_all add: 
        is_semifunctor_op is_ft_dghm.ft_dghm_op_dghm_is_ft_dghm 
        ft_smcf_is_ft_dghm
    )

lemma (in is_ft_semifunctor) is_ft_semifunctor_op'[smc_op_intros]: 
  assumes "\<AA>' = op_smc \<AA>" and "\<BB>' = op_smc \<BB>"
  shows "op_smcf \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule is_ft_semifunctor_op)

lemmas is_ft_semifunctor_op[smc_op_intros] = 
  is_ft_semifunctor.is_ft_semifunctor_op'


subsubsection\<open>
The composition of faithful semifunctors is a faithful semifunctor
\<close>

lemma smcf_comp_is_ft_semifunctor[smcf_cs_intros]:
  \<comment>\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_ft_semifunctorI)
  interpret \<GG>: is_ft_semifunctor \<alpha> \<BB> \<CC> \<GG> by (simp add: assms(1))
  interpret \<FF>: is_ft_semifunctor \<alpha> \<AA> \<BB> \<FF> by (simp add: assms(2))
  from \<FF>.is_semifunctor_axioms \<GG>.is_semifunctor_axioms show \<GG>\<FF>: 
    "\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (auto intro: smc_cs_intros)
  then interpret is_semifunctor \<alpha> \<AA> \<CC> \<open>\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>\<close> .
  show "smcf_dghm (\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>) : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> smc_dg \<CC>"
    unfolding slicing_simps slicing_commute[symmetric] 
    by (auto intro: dghm_cs_intros slicing_intros)
qed



subsection\<open>Full semifunctor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>

locale is_fl_semifunctor = is_semifunctor \<alpha> \<AA> \<BB> \<FF> for \<alpha> \<AA> \<BB> \<FF> + 
  assumes fl_smcf_is_fl_dghm:
    "smcf_dghm \<FF> : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> smc_dg \<BB>"

syntax "_is_fl_semifunctor" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_fl_semifunctor \<alpha> \<AA> \<BB> \<FF>"

lemma (in is_fl_semifunctor) fl_smcf_is_fl_dghm'[slicing_intros]:
  assumes "\<AA>' = smc_dg \<AA>" and "\<BB>' = smc_dg \<BB>"
  shows "smcf_dghm \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule fl_smcf_is_fl_dghm)

lemmas [slicing_intros] = is_fl_semifunctor.fl_smcf_is_fl_dghm'


text\<open>Rules.\<close>

mk_ide rf is_fl_semifunctor_def[unfolded is_fl_semifunctor_axioms_def]
  |intro is_fl_semifunctorI|
  |dest is_fl_semifunctorD[dest]|
  |elim is_fl_semifunctorE[elim]|

lemmas [smcf_cs_intros] = is_fl_semifunctorD(1)

lemma is_fl_semifunctorI':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<And>a b. \<lbrakk> a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow>
      \<FF>\<lparr>ArrMap\<rparr> `\<^sub>\<circ> (Hom \<AA> a b) = Hom \<BB> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms
  by (intro is_fl_semifunctorI)
    (
      simp_all add: 
        assms(1) 
        is_fl_dghmI[OF is_semifunctorD(6)[OF assms(1)], unfolded slicing_simps]
    )

lemma is_fl_semifunctorD':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<And>a b. \<lbrakk> a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow> 
      \<FF>\<lparr>ArrMap\<rparr> `\<^sub>\<circ> (Hom \<AA> a b) = Hom \<BB> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
  by 
    (
      simp_all add: 
        is_fl_semifunctorD[OF assms(1)] 
        is_fl_dghmD(2)[
          OF is_fl_semifunctorD(2)[OF assms(1)], unfolded slicing_simps
          ]
    )

lemma is_fl_semifunctorE':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>"
  obtains "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<And>a b. \<lbrakk> a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow> 
      \<FF>\<lparr>ArrMap\<rparr> `\<^sub>\<circ> (Hom \<AA> a b) = Hom \<BB> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
  using assms by (simp_all add: is_fl_semifunctorD')


text\<open>Elementary properties.\<close>

context is_fl_semifunctor
begin

interpretation dghm: is_fl_dghm \<alpha> \<open>smc_dg \<AA>\<close> \<open>smc_dg \<BB>\<close> \<open>smcf_dghm \<FF>\<close>
  by (rule fl_smcf_is_fl_dghm) 

lemmas_with [unfolded slicing_simps]:
  fl_smcf_surj_on_Hom = dghm.fl_dghm_surj_on_Hom

end


subsubsection\<open>Opposite full semifunctor\<close>

lemma (in is_fl_semifunctor) is_fl_semifunctor_op: 
  "op_smcf \<FF> : op_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> op_smc \<BB>"    
  by 
    (
      rule is_fl_semifunctorI, 
      unfold smc_op_simps slicing_simps slicing_commute[symmetric]
    )
    (
      simp_all add: 
        is_semifunctor_op 
        is_fl_dghm.fl_dghm_op_dghm_is_fl_dghm 
        fl_smcf_is_fl_dghm
    )

lemma (in is_fl_semifunctor) is_fl_semifunctor_op'[smc_op_intros]: 
  assumes "\<AA>' = op_smc \<AA>" and "\<BB>' = op_smc \<BB>"
  shows "op_smcf \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule is_fl_semifunctor_op)

lemmas is_fl_semifunctor_op[smc_op_intros] = 
  is_fl_semifunctor.is_fl_semifunctor_op


subsubsection\<open>The composition of full semifunctors is a full semifunctor\<close>

lemma smcf_comp_is_fl_semifunctor[smcf_cs_intros]:
  \<comment>\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_fl_semifunctorI)
  interpret \<FF>: is_fl_semifunctor \<alpha> \<AA> \<BB> \<FF> using assms(2) by simp
  interpret \<GG>: is_fl_semifunctor \<alpha> \<BB> \<CC> \<GG> using assms(1) by simp
  from \<FF>.is_semifunctor_axioms \<GG>.is_semifunctor_axioms show
    "\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    by (auto intro: smc_cs_intros)
  show "smcf_dghm (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>) : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> smc_dg \<CC>"
    unfolding slicing_commute[symmetric] 
    by (auto intro: dghm_cs_intros slicing_intros)
qed 



subsection\<open>Fully faithful semifunctor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}).\<close>

locale is_ff_semifunctor = 
  is_ft_semifunctor \<alpha> \<AA> \<BB> \<FF> + is_fl_semifunctor \<alpha> \<AA> \<BB> \<FF> for \<alpha> \<AA> \<BB> \<FF>

syntax "_is_ff_semifunctor" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>f\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_ff_semifunctor \<alpha> \<AA> \<BB> \<FF>"


text\<open>Rules.\<close>

mk_ide rf is_ff_semifunctor_def
  |intro is_ff_semifunctorI|
  |dest is_ff_semifunctorD[dest]|
  |elim is_ff_semifunctorE[elim]|

lemmas [smcf_cs_intros] = is_ff_semifunctorD


text\<open>Elementary properties.\<close>

lemma (in is_ff_semifunctor) ff_smcf_is_ff_dghm:
  "smcf_dghm \<FF> : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> smc_dg \<BB>"
  by (rule is_ff_dghmI) (auto intro: slicing_intros)

lemma (in is_ff_semifunctor) ff_smcf_is_ff_dghm'[slicing_intros]:
  assumes "\<AA>' = smc_dg \<AA>" and "\<BB>' = smc_dg \<BB>"
  shows "smcf_dghm \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule ff_smcf_is_ff_dghm)

lemmas [slicing_intros] = is_ff_semifunctor.ff_smcf_is_ff_dghm'


subsubsection\<open>Opposite fully faithful semifunctor\<close>

lemma (in is_ff_semifunctor) is_ff_semifunctor_op: 
  "op_smcf \<FF> : op_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> op_smc \<BB>"    
  by (rule is_ff_semifunctorI) 
    (auto simp: is_fl_semifunctor_op is_ft_semifunctor_op)

lemma (in is_ff_semifunctor) is_ff_semifunctor_op'[smc_op_intros]: 
  assumes "\<AA>' = op_smc \<AA>" and "\<BB>' = op_smc \<BB>"
  shows "op_smcf \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule is_ff_semifunctor_op)

lemmas is_ff_semifunctor_op[smc_op_intros] = 
  is_ff_semifunctor.is_ff_semifunctor_op'


subsubsection\<open>
The composition of fully faithful semifunctors is a fully faithful
semifunctor
\<close>

lemma smcf_comp_is_ff_semifunctor[smcf_cs_intros]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms 
  by (intro is_ff_semifunctorI, elim is_ff_semifunctorE) 
    (auto intro: smcf_cs_intros)



subsection\<open>Isomorphism of semicategories\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>

locale is_iso_semifunctor = is_semifunctor \<alpha> \<AA> \<BB> \<FF> for \<alpha> \<AA> \<BB> \<FF> + 
  assumes iso_smcf_is_iso_dghm: 
    "smcf_dghm \<FF> : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> smc_dg \<BB>"

syntax "_is_iso_semifunctor" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_iso_semifunctor \<alpha> \<AA> \<BB> \<FF>"

lemma (in is_iso_semifunctor) iso_smcf_is_iso_dghm'[slicing_intros]:
  assumes "\<AA>' = smc_dg \<AA>" "\<BB>' = smc_dg \<BB>"
  shows "smcf_dghm \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule iso_smcf_is_iso_dghm)

lemmas [slicing_intros] = is_iso_semifunctor.iso_smcf_is_iso_dghm'


text\<open>Rules.\<close>

lemma (in is_iso_semifunctor) is_iso_semifunctor_axioms'[smcf_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_iso_semifunctor_axioms)

mk_ide rf is_iso_semifunctor_def[unfolded is_iso_semifunctor_axioms_def]
  |intro is_iso_semifunctorI|
  |dest is_iso_semifunctorD[dest]|
  |elim is_iso_semifunctorE[elim]|

lemma is_iso_semifunctorI':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "v11 (\<FF>\<lparr>ObjMap\<rparr>)"
    and "v11 (\<FF>\<lparr>ArrMap\<rparr>)"
    and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
    and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms
  by (intro is_iso_semifunctorI)
    (
      simp_all add: 
        assms(1) 
        is_iso_dghmI[OF is_semifunctorD(6)[OF assms(1)], unfolded slicing_simps]
    )

lemma is_iso_semifunctorD':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "v11 (\<FF>\<lparr>ObjMap\<rparr>)"
    and "v11 (\<FF>\<lparr>ArrMap\<rparr>)"
    and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
    and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>"
  by 
    (
      simp_all add: 
        is_iso_semifunctorD[OF assms(1)] 
        is_iso_dghmD(2-5)[
          OF is_iso_semifunctorD(2)[OF assms(1)], unfolded slicing_simps
          ]
    )

lemma is_iso_semifunctorE':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  obtains "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "v11 (\<FF>\<lparr>ObjMap\<rparr>)"
    and "v11 (\<FF>\<lparr>ArrMap\<rparr>)"
    and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
    and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>"
  using assms by (simp_all add: is_iso_semifunctorD')


text\<open>Elementary properties.\<close>

context is_iso_semifunctor
begin

interpretation dghm: is_iso_dghm \<alpha> \<open>smc_dg \<AA>\<close> \<open>smc_dg \<BB>\<close> \<open>smcf_dghm \<FF>\<close>
  by (rule iso_smcf_is_iso_dghm) 

lemmas_with [unfolded slicing_simps]:
  iso_smcf_ObjMap_vrange[smcf_cs_simps] = dghm.iso_dghm_ObjMap_vrange
  and iso_smcf_ArrMap_vrange[smcf_cs_simps] = dghm.iso_dghm_ArrMap_vrange

sublocale ObjMap: v11 \<open>\<FF>\<lparr>ObjMap\<rparr>\<close>
  rewrites "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>" and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
  by (rule dghm.iso_dghm_ObjMap_v11[unfolded slicing_simps]) 
    (simp_all add: smc_cs_simps smcf_cs_simps)

sublocale ArrMap: v11 \<open>\<FF>\<lparr>ArrMap\<rparr>\<close>
  rewrites "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>" and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>"
  by (rule dghm.iso_dghm_ArrMap_v11[unfolded slicing_simps])
    (simp_all add: smc_cs_simps smcf_cs_simps)

lemmas_with [unfolded slicing_simps]:
  iso_smcf_Obj_HomDom_if_Obj_HomCod[elim] = 
    dghm.iso_dghm_Obj_HomDom_if_Obj_HomCod
  and iso_smcf_Arr_HomDom_if_Arr_HomCod[elim] = 
    dghm.iso_dghm_Arr_HomDom_if_Arr_HomCod
  and iso_smcf_ObjMap_eqE[elim] = dghm.iso_dghm_ObjMap_eqE
  and iso_smcf_ArrMap_eqE[elim] = dghm.iso_dghm_ArrMap_eqE

end

sublocale is_iso_semifunctor \<subseteq> is_ff_semifunctor 
proof-
  interpret dghm: is_iso_dghm \<alpha> \<open>smc_dg \<AA>\<close> \<open>smc_dg \<BB>\<close> \<open>smcf_dghm \<FF>\<close>
    by (rule iso_smcf_is_iso_dghm) 
  show "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> \<BB>" by unfold_locales
qed

lemmas (in is_iso_semifunctor) iso_smcf_is_ff_semifunctor = 
  is_ff_semifunctor_axioms

lemmas [smcf_cs_intros] = is_iso_semifunctor.iso_smcf_is_ff_semifunctor


subsubsection\<open>Opposite isomorphism of semicategories\<close>

lemma (in is_iso_semifunctor) is_iso_semifunctor_op: 
  "op_smcf \<FF> : op_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> op_smc \<BB>"   
  by 
    (
      rule is_iso_semifunctorI, 
      unfold smc_op_simps slicing_simps slicing_commute[symmetric]
    )
    (
      simp_all add: 
        is_semifunctor_op is_iso_dghm.is_iso_dghm_op iso_smcf_is_iso_dghm
    )

lemmas is_iso_semifunctor_op[smc_op_intros] =
  is_iso_semifunctor.is_iso_semifunctor_op


subsubsection\<open>
The composition of isomorphisms of semicategories is an isomorphism of 
semicategories
\<close>

lemma smcf_comp_is_iso_semifunctor[smcf_cs_intros]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_iso_semifunctorI)
  interpret \<FF>: is_iso_semifunctor \<alpha> \<AA> \<BB> \<FF> using assms by auto
  interpret \<GG>: is_iso_semifunctor \<alpha> \<BB> \<CC> \<GG> using assms by auto
  from \<FF>.is_semifunctor_axioms \<GG>.is_semifunctor_axioms show 
    "\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    by (auto intro: smcf_cs_intros)
  show "smcf_dghm (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>) : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> smc_dg \<CC>"
    by 
      (
        auto 
          intro: dghm_cs_intros slicing_intros 
          simp: slicing_commute[symmetric]
      )
qed



subsection\<open>Inverse semifunctor\<close>

abbreviation (input) inv_smcf :: "V \<Rightarrow> V"
  where "inv_smcf \<equiv> inv_dghm"

lemmas [smc_cs_simps] = inv_dghm_components(3,4)


text\<open>Slicing.\<close>

lemma dghm_inv_smcf[slicing_commute]: 
  "inv_dghm (smcf_dghm \<FF>) = smcf_dghm (inv_smcf \<FF>)"
  unfolding smcf_dghm_def inv_dghm_def dghm_field_simps 
  by (simp_all add: nat_omega_simps)

context is_iso_semifunctor
begin

interpretation dghm: is_iso_dghm \<alpha> \<open>smc_dg \<AA>\<close> \<open>smc_dg \<BB>\<close> \<open>smcf_dghm \<FF>\<close>
  by (rule iso_smcf_is_iso_dghm) 

lemmas_with [unfolded slicing_simps slicing_commute]:
  inv_smcf_ObjMap_v11 = dghm.inv_dghm_ObjMap_v11
  and inv_smcf_ObjMap_vdomain = dghm.inv_dghm_ObjMap_vdomain
  and inv_smcf_ObjMap_app = dghm.inv_dghm_ObjMap_app
  and inv_smcf_ObjMap_vrange = dghm.inv_dghm_ObjMap_vrange
  and inv_smcf_ArrMap_v11 = dghm.inv_dghm_ArrMap_v11
  and inv_smcf_ArrMap_vdomain = dghm.inv_dghm_ArrMap_vdomain
  and inv_smcf_ArrMap_app = dghm.inv_dghm_ArrMap_app
  and inv_smcf_ArrMap_vrange = dghm.inv_dghm_ArrMap_vrange
  and iso_smcf_ObjMap_inv_smcf_ObjMap_app =
    dghm.iso_dghm_ObjMap_inv_dghm_ObjMap_app
  and iso_smcf_ArrMap_inv_smcf_ArrMap_app = 
    dghm.iso_dghm_ArrMap_inv_dghm_ArrMap_app
  and iso_smcf_HomDom_is_arr_conv = dghm.iso_dghm_HomDom_is_arr_conv
  and iso_smcf_HomCod_is_arr_conv = dghm.iso_dghm_HomCod_is_arr_conv

end

lemmas [smcf_cs_intros] = 
  is_iso_semifunctor.inv_smcf_ObjMap_v11
  is_iso_semifunctor.inv_smcf_ArrMap_v11

lemmas [smcf_cs_simps] = 
  is_iso_semifunctor.inv_smcf_ObjMap_vdomain
  is_iso_semifunctor.inv_smcf_ObjMap_app
  is_iso_semifunctor.inv_smcf_ObjMap_vrange
  is_iso_semifunctor.inv_smcf_ArrMap_vdomain
  is_iso_semifunctor.inv_smcf_ArrMap_app
  is_iso_semifunctor.inv_smcf_ArrMap_vrange
  is_iso_semifunctor.iso_smcf_ObjMap_inv_smcf_ObjMap_app
  is_iso_semifunctor.iso_smcf_ArrMap_inv_smcf_ArrMap_app



subsection\<open>
An isomorphism of semicategories is an isomorphism in the category \<open>SemiCAT\<close>
\<close>

lemma is_arr_isomorphism_is_iso_semifunctor:
  \<comment>\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> = smcf_id \<AA>"
    and "\<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> = smcf_id \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<FF>: is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(1))
  interpret \<GG>: is_semifunctor \<alpha> \<BB> \<AA> \<GG> by (rule assms(2))
  show ?thesis
  proof(rule is_iso_semifunctorI)
    have dg_\<GG>\<FF>\<AA>: "smcf_dghm \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M smcf_dghm \<FF> = dghm_id (smc_dg \<AA>)"
      by (simp add: assms(3) smcf_dghm_smcf_id smcf_dghm_smcf_comp)
    have dg_\<FF>\<GG>\<BB>: "smcf_dghm \<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M smcf_dghm \<GG> = dghm_id (smc_dg \<BB>)"
      by (simp add: assms(4) smcf_dghm_smcf_id smcf_dghm_smcf_comp)
    from \<FF>.smcf_is_dghm \<GG>.smcf_is_dghm dg_\<GG>\<FF>\<AA> dg_\<FF>\<GG>\<BB> show 
      "smcf_dghm \<FF> : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> smc_dg \<BB>"
      by (rule is_arr_isomorphism_is_iso_dghm)
  qed (simp add: \<FF>.is_semifunctor_axioms)
qed

lemma is_iso_semifunctor_is_arr_isomorphism:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  shows [smcf_cs_intros]: "inv_smcf \<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<AA>"
    and "inv_smcf \<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> = smcf_id \<AA>"
    and "\<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F inv_smcf \<FF> = smcf_id \<BB>"
proof-

  let ?\<GG> = \<open>inv_smcf \<FF>\<close>

  interpret is_iso_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(1))

  note is_iso_dghm = is_iso_dghm_is_arr_isomorphism[OF iso_smcf_is_iso_dghm]

  show \<GG>: "?\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<AA>"
  proof
    (
      intro is_iso_semifunctorI is_semifunctorI; 
      (unfold slicing_commute[symmetric])?
    )
    show "vfsequence (inv_smcf \<FF>)" unfolding inv_dghm_def by simp
    show "vcard (inv_smcf \<FF>) = 4\<^sub>\<nat>"
      unfolding inv_dghm_def by (simp add: nat_omega_simps)
    show inv_iso_dghm_\<FF>: 
      "inv_dghm (smcf_dghm \<FF>) : smc_dg \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> smc_dg \<AA>"
      by (rule is_iso_dghm(1))
    show inv_dghm_\<FF>: "inv_dghm (smcf_dghm \<FF>) : smc_dg \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg \<AA>"
      by (rule is_iso_dghmD(1)[OF inv_iso_dghm_\<FF>])
    fix b c g a f assume prems: "g : b \<mapsto>\<^bsub>\<BB>\<^esub> c" "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
    note is_arr_inv = is_dghm.dghm_ArrMap_is_arr[
        OF inv_dghm_\<FF>, unfolded slicing_simps slicing_commute
        ]
    from prems is_arr_inv[OF prems(1)] is_arr_inv[OF prems(2)] show 
      "inv_smcf \<FF>\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f\<rparr> =
        inv_smcf \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> inv_smcf \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
       unfolding inv_dghm_components
       by (intro v11.v11_vconverse_app)
         (
           cs_concl 
            cs_intro: smc_cs_intros V_cs_intros
            cs_simp: V_cs_simps smc_cs_simps
         )+
  qed (auto simp: smc_cs_simps intro: smc_cs_intros)

  show "?\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> = smcf_id \<AA>"
  proof(rule smcf_eqI, unfold dghm_comp_components inv_dghm_components)
    from \<GG> is_semifunctor_axioms show "inv_smcf \<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      by (blast intro: smc_cs_intros)
  qed
    (
      simp_all add: 
        HomDom.smc_smcf_id_is_semifunctor
        ObjMap.v11_vcomp_vconverse 
        ArrMap.v11_vcomp_vconverse 
        dghm_id_components
    )

  show "\<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F inv_smcf \<FF> = smcf_id \<BB>"
  proof(rule smcf_eqI, unfold dghm_comp_components inv_dghm_components)
    from \<GG> is_semifunctor_axioms show "\<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F inv_smcf \<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      by (blast intro: smc_cs_intros)
  qed 
    (
      simp_all add: 
        HomCod.smc_smcf_id_is_semifunctor
        ObjMap.v11_vcomp_vconverse' 
        ArrMap.v11_vcomp_vconverse' 
        dghm_id_components
    )

qed


subsubsection\<open>An identity semifunctor is an isomorphism of semicategories\<close>

lemma (in semicategory) smc_smcf_id_is_iso_semifunctor: 
  "smcf_id \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<CC>"
  by (rule is_iso_semifunctorI, unfold slicing_simps slicing_commute[symmetric])
    (
      simp_all add: 
        smc_smcf_id_is_semifunctor digraph.dg_dghm_id_is_iso_dghm smc_digraph
    )

lemma (in semicategory) smc_smcf_id_is_iso_semifunctor'[smcf_cs_intros]: 
  assumes "\<AA>' = \<CC>" and "\<BB>' = \<CC>"
  shows "smcf_id \<CC> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule smc_smcf_id_is_iso_semifunctor)

lemmas [smcf_cs_intros] = semicategory.smc_smcf_id_is_iso_semifunctor'



subsection\<open>Isomorphic semicategories\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}).\<close>

locale iso_semicategory = L: semicategory \<alpha> \<AA> + R: semicategory \<alpha> \<BB> 
  for \<alpha> \<AA> \<BB> +
  assumes iso_smc_is_iso_semifunctor: "\<exists>\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"

notation iso_semicategory (infixl "\<approx>\<^sub>S\<^sub>M\<^sub>C\<index>" 50)


text\<open>Rules.\<close>

lemma iso_semicategoryI:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "\<AA> \<approx>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms 
  unfolding iso_semicategory_def iso_semicategory_axioms_def 
  by blast

lemma iso_semicategoryD[dest]:
  assumes "\<AA> \<approx>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "\<exists>\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>" 
  using assms 
  unfolding iso_semicategory_def iso_semicategory_axioms_def 
  by simp_all

lemma iso_semicategoryE[elim]:
  assumes "\<AA> \<approx>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
  obtains \<FF> where "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by auto


text\<open>Elementary properties.\<close>

lemma (in iso_semicategory) iso_smc_iso_digraph: "smc_dg \<AA> \<approx>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg \<BB>"
  using iso_smc_is_iso_semifunctor 
  by (auto intro: slicing_intros iso_digraphI)


subsubsection\<open>A semicategory isomorphism is an equivalence relation\<close>

lemma iso_semicategory_refl: 
  assumes "semicategory \<alpha> \<AA>" 
  shows "\<AA> \<approx>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
proof(rule iso_semicategoryI[of _  _ _ \<open>smcf_id \<AA>\<close>])
  interpret semicategory \<alpha> \<AA> by (rule assms)
  show "smcf_id \<AA> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<AA>"  
    by (simp add: smc_smcf_id_is_iso_semifunctor)
qed

lemma iso_semicategory_sym[sym]:
  assumes "\<AA> \<approx>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "\<BB> \<approx>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
proof-
  interpret iso_semicategory \<alpha> \<AA> \<BB> by (rule assms)
  from iso_smc_is_iso_semifunctor obtain \<FF> where "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>" 
    by clarsimp
  then have "inv_smcf \<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<AA>" 
    by (simp add: is_iso_semifunctor_is_arr_isomorphism(1))
  then show ?thesis by (auto intro: iso_semicategoryI)
qed

lemma iso_semicategory_trans[trans]:
  assumes "\<AA> \<approx>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<BB> \<approx>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
  shows "\<AA> \<approx>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-  
  interpret L: iso_semicategory \<alpha> \<AA> \<BB> by (rule assms(1))
  interpret R: iso_semicategory \<alpha> \<BB> \<CC> by (rule assms(2))
  from L.iso_smc_is_iso_semifunctor R.iso_smc_is_iso_semifunctor show ?thesis
    by (auto intro: iso_semicategoryI smcf_cs_intros)
qed

text\<open>\newpage\<close>

end