(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Functor\<close>
theory CZH_ECAT_Functor
  imports 
    CZH_ECAT_Category
    CZH_Foundations.CZH_SMC_Semifunctor
begin



subsection\<open>Background\<close>

named_theorems cf_cs_simps
named_theorems cf_cs_intros

named_theorems cat_cn_cs_simps
named_theorems cat_cn_cs_intros

lemmas [cat_cs_simps] = dg_shared_cs_simps
lemmas [cat_cs_intros] = dg_shared_cs_intros


subsubsection\<open>Slicing\<close>

definition cf_smcf :: "V \<Rightarrow> V"
  where "cf_smcf \<CC> = 
    [\<CC>\<lparr>ObjMap\<rparr>, \<CC>\<lparr>ArrMap\<rparr>, cat_smc (\<CC>\<lparr>HomDom\<rparr>), cat_smc (\<CC>\<lparr>HomCod\<rparr>)]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_smcf_components:
  shows [slicing_simps]: "cf_smcf \<FF>\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>"
    and [slicing_simps]: "cf_smcf \<FF>\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
    and [slicing_commute]: "cf_smcf \<FF>\<lparr>HomDom\<rparr> = cat_smc (\<FF>\<lparr>HomDom\<rparr>)"
    and [slicing_commute]: "cf_smcf \<FF>\<lparr>HomCod\<rparr> = cat_smc (\<FF>\<lparr>HomCod\<rparr>)"
  unfolding cf_smcf_def dghm_field_simps by (auto simp: nat_omega_simps)



subsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>

locale is_functor = 
  \<Z> \<alpha> + vfsequence \<FF> + HomDom: category \<alpha> \<AA> + HomCod: category \<alpha> \<BB> 
  for \<alpha> \<AA> \<BB> \<FF> +
  assumes cf_length[cat_cs_simps]: "vcard \<FF> = 4\<^sub>\<nat>" 
    and cf_is_semifunctor[slicing_intros]: 
      "cf_smcf \<FF> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<BB>" 
    and cf_HomDom[cat_cs_simps]: "\<FF>\<lparr>HomDom\<rparr> = \<AA>"
    and cf_HomCod[cat_cs_simps]: "\<FF>\<lparr>HomCod\<rparr> = \<BB>"
    and cf_ObjMap_CId[cat_cs_intros]: 
      "c \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<Longrightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"

syntax "_is_functor" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_functor \<alpha> \<AA> \<BB> \<FF>"

abbreviation (input) is_cn_cf :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "is_cn_cf \<alpha> \<AA> \<BB> \<FF> \<equiv> \<FF> : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"

syntax "_is_cn_cf" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<^sub>C\<mapsto>\<mapsto>\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>" \<rightharpoonup> "CONST is_cn_cf \<alpha> \<AA> \<BB> \<FF>"

abbreviation all_cfs :: "V \<Rightarrow> V"
  where "all_cfs \<alpha> \<equiv> set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation cfs :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cfs \<alpha> \<AA> \<BB> \<equiv> set {\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"

lemmas [cat_cs_simps] =
  is_functor.cf_length
  is_functor.cf_HomDom
  is_functor.cf_HomCod
  is_functor.cf_ObjMap_CId

lemma cn_cf_ObjMap_CId[cat_cn_cs_simps]: 
  assumes "\<FF> : \<AA> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>" and "c \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "\<FF>\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
proof-
  interpret is_functor \<alpha> \<open>op_cat \<AA>\<close> \<BB> \<FF> by (rule assms(1))
  from assms(2) have c: "c \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr>" unfolding cat_op_simps by simp
  show ?thesis by (rule cf_ObjMap_CId[OF c, unfolded cat_op_simps])
qed

lemma (in is_functor) cf_is_semifunctor':
  assumes "\<AA>' = cat_smc \<AA>" and "\<BB>' = cat_smc \<BB>"
  shows "cf_smcf \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule cf_is_semifunctor)

lemmas [slicing_intros] = is_functor.cf_is_semifunctor'

lemma cn_smcf_comp_is_semifunctor: 
  assumes "\<FF> : \<AA> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "cf_smcf \<FF> : cat_smc \<AA> \<^sub>S\<^sub>M\<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub>cat_smc \<BB>"
  using assms 
  unfolding slicing_simps slicing_commute
  by (rule is_functor.cf_is_semifunctor)

lemma cn_smcf_comp_is_semifunctor'[slicing_intros]: 
  assumes "\<FF> : \<AA> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<AA>' = op_smc (cat_smc \<AA>)"
    and "\<BB>' = cat_smc \<BB>"
  shows "cf_smcf \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  using assms(1) unfolding assms(2,3) by (rule cn_smcf_comp_is_semifunctor)


text\<open>Rules.\<close>

lemma (in is_functor) is_functor_axioms'[cat_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_functor_axioms)

mk_ide rf is_functor_def[unfolded is_functor_axioms_def]
  |intro is_functorI|
  |dest is_functorD[dest]|
  |elim is_functorE[elim]|

lemmas [cat_cs_intros] = is_functorD(3,4)

lemma is_functorI':
  assumes "\<Z> \<alpha>"
    and "vfsequence \<FF>"
    and "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
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
    and "(\<And>c. c \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<Longrightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>)"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  by 
    (
      intro is_functorI is_semifunctorI', 
      unfold cf_smcf_components slicing_simps
    )
    (simp_all add: assms cf_smcf_def nat_omega_simps category.cat_semicategory)

lemma is_functorD':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<Z> \<alpha>"
    and "vfsequence \<FF>"
    and "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
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
    and "(\<And>c. c \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<Longrightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>)"
  by 
    (
      simp_all add: 
        is_functorD(2-9)[OF assms] 
        is_semifunctorD'[OF is_functorD(6)[OF assms], unfolded slicing_simps]
    )

lemma is_functorE':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  obtains "\<Z> \<alpha>"
    and "vfsequence \<FF>"
    and "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
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
    and "(\<And>c. c \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<Longrightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>)"
  using assms by (simp add: is_functorD')


text\<open>A functor is a semifunctor.\<close>

context is_functor
begin

interpretation smcf: is_semifunctor \<alpha> \<open>cat_smc \<AA>\<close> \<open>cat_smc \<BB>\<close> \<open>cf_smcf \<FF>\<close>
  by (rule cf_is_semifunctor)

sublocale ObjMap: vsv \<open>\<FF>\<lparr>ObjMap\<rparr>\<close>
  by (rule smcf.ObjMap.vsv_axioms[unfolded slicing_simps])
sublocale ArrMap: vsv \<open>\<FF>\<lparr>ArrMap\<rparr>\<close>
  by (rule smcf.ArrMap.vsv_axioms[unfolded slicing_simps])

lemmas_with [unfolded slicing_simps]:
  cf_ObjMap_vsv = smcf.smcf_ObjMap_vsv
  and cf_ArrMap_vsv = smcf.smcf_ArrMap_vsv
  and cf_ObjMap_vdomain[cat_cs_simps] = smcf.smcf_ObjMap_vdomain
  and cf_ObjMap_vrange = smcf.smcf_ObjMap_vrange
  and cf_ArrMap_vdomain[cat_cs_simps] = smcf.smcf_ArrMap_vdomain
  and cf_ArrMap_is_arr = smcf.smcf_ArrMap_is_arr
  and cf_ArrMap_is_arr''[cat_cs_intros] = smcf.smcf_ArrMap_is_arr''
  and cf_ArrMap_is_arr'[cat_cs_intros] = smcf.smcf_ArrMap_is_arr'
  and cf_ObjMap_app_in_HomCod_Obj[cat_cs_intros] = 
    smcf.smcf_ObjMap_app_in_HomCod_Obj
  and cf_ArrMap_vrange = smcf.smcf_ArrMap_vrange
  and cf_ArrMap_app_in_HomCod_Arr[cat_cs_intros] = 
    smcf.smcf_ArrMap_app_in_HomCod_Arr
  and cf_ObjMap_vsubset_Vset = smcf.smcf_ObjMap_vsubset_Vset
  and cf_ArrMap_vsubset_Vset = smcf.smcf_ArrMap_vsubset_Vset
  and cf_ObjMap_in_Vset = smcf.smcf_ObjMap_in_Vset
  and cf_ArrMap_in_Vset = smcf.smcf_ArrMap_in_Vset
  and cf_is_semifunctor_if_ge_Limit = smcf.smcf_is_semifunctor_if_ge_Limit
  and cf_is_arr_HomCod = smcf.smcf_is_arr_HomCod
  and cf_vimage_dghm_ArrMap_vsubset_Hom = 
    smcf.smcf_vimage_dghm_ArrMap_vsubset_Hom

lemmas_with [unfolded slicing_simps]: 
  cf_ArrMap_Comp = smcf.smcf_ArrMap_Comp

end

lemmas [cat_cs_simps] = 
  is_functor.cf_ObjMap_vdomain
  is_functor.cf_ArrMap_vdomain
  is_functor.cf_ArrMap_Comp

lemmas [cat_cs_intros] =
  is_functor.cf_ObjMap_app_in_HomCod_Obj
  is_functor.cf_ArrMap_app_in_HomCod_Arr
  is_functor.cf_ArrMap_is_arr'


text\<open>Elementary properties.\<close>

lemma cn_cf_ArrMap_Comp[cat_cn_cs_simps]: 
  assumes "category \<alpha> \<AA>" 
    and "\<FF> : \<AA> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
    and "g : c \<mapsto>\<^bsub>\<AA>\<^esub> b"
    and "f : b \<mapsto>\<^bsub>\<AA>\<^esub> a" 
  shows "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> g\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
proof-
  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<FF>: is_functor \<alpha> \<open>op_cat \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule cn_smcf_ArrMap_Comp
          [
            OF 
              \<AA>.cat_semicategory 
              \<FF>.cf_is_semifunctor[unfolded slicing_commute[symmetric]],
            unfolded slicing_simps,
            OF assms(3,4)
          ]
      )
qed

lemma cf_eqI:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<GG>\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>"
    and "\<GG>\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
    and "\<AA> = \<CC>"
    and "\<BB> = \<DD>"
  shows "\<GG> = \<FF>"
proof(rule vsv_eqI)
  interpret L: is_functor \<alpha> \<AA> \<BB> \<GG> by (rule assms(1))
  interpret R: is_functor \<alpha> \<CC> \<DD> \<FF> by (rule assms(2))
  from assms(1) show "vsv \<GG>" by auto
  from assms(2) show "vsv \<FF>" by auto
  have dom: "\<D>\<^sub>\<circ> \<GG> = 4\<^sub>\<nat>" by (cs_concl cs_simp: cat_cs_simps V_cs_simps)
  show "\<D>\<^sub>\<circ> \<GG> = \<D>\<^sub>\<circ> \<FF>" by (cs_concl cs_simp: cat_cs_simps V_cs_simps)
  from assms(5,6) have sup: "\<GG>\<lparr>HomDom\<rparr> = \<FF>\<lparr>HomDom\<rparr>" "\<GG>\<lparr>HomCod\<rparr> = \<FF>\<lparr>HomCod\<rparr>" 
    by (simp_all add: cat_cs_simps)
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<GG> \<Longrightarrow> \<GG>\<lparr>a\<rparr> = \<FF>\<lparr>a\<rparr>" for a 
    by (unfold dom, elim_in_numeral, insert assms(3,4) sup)
      (auto simp: dghm_field_simps)
qed

lemma cf_smcf_eqI:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<AA> = \<CC>"
    and "\<BB> = \<DD>"
    and "cf_smcf \<GG> = cf_smcf \<FF>"
  shows "\<GG> = \<FF>"
proof(rule cf_eqI)
  from assms(5) have 
    "cf_smcf \<GG>\<lparr>ObjMap\<rparr> = cf_smcf \<FF>\<lparr>ObjMap\<rparr>"
    "cf_smcf \<GG>\<lparr>ArrMap\<rparr> = cf_smcf \<FF>\<lparr>ArrMap\<rparr>"
    by simp_all
  then show "\<GG>\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>" "\<GG>\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
    unfolding slicing_simps by simp_all
qed (auto intro: assms(1,2) simp: assms(3-5))

lemma (in is_functor) cf_def: "\<FF> = [\<FF>\<lparr>ObjMap\<rparr>, \<FF>\<lparr>ArrMap\<rparr>, \<FF>\<lparr>HomDom\<rparr>, \<FF>\<lparr>HomCod\<rparr>]\<^sub>\<circ>"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> \<FF> = 4\<^sub>\<nat>" by (cs_concl cs_simp: cat_cs_simps V_cs_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> [\<FF>\<lparr>Obj\<rparr>, \<FF>\<lparr>Arr\<rparr>, \<FF>\<lparr>Dom\<rparr>, \<FF>\<lparr>Cod\<rparr>]\<^sub>\<circ> = 4\<^sub>\<nat>"
    by (simp add: nat_omega_simps)
  then show "\<D>\<^sub>\<circ> \<FF> = \<D>\<^sub>\<circ> [\<FF>\<lparr>ObjMap\<rparr>, \<FF>\<lparr>ArrMap\<rparr>, \<FF>\<lparr>HomDom\<rparr>, \<FF>\<lparr>HomCod\<rparr>]\<^sub>\<circ>"
    unfolding dom_lhs dom_rhs by (simp add: nat_omega_simps)
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<FF> \<Longrightarrow> \<FF>\<lparr>a\<rparr> = [\<FF>\<lparr>ObjMap\<rparr>, \<FF>\<lparr>ArrMap\<rparr>, \<FF>\<lparr>HomDom\<rparr>, \<FF>\<lparr>HomCod\<rparr>]\<^sub>\<circ>\<lparr>a\<rparr>" 
    for a
    by (unfold dom_lhs, elim_in_numeral, unfold dghm_field_simps)
      (simp_all add: nat_omega_simps)
qed (auto simp: vsv_axioms)


text\<open>Size.\<close>

lemma (in is_functor) cf_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"  
  shows "\<FF> \<in>\<^sub>\<circ> Vset \<beta>"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  note [cat_cs_intros] = 
    cf_ObjMap_in_Vset 
    cf_ArrMap_in_Vset 
    HomDom.cat_in_Vset 
    HomCod.cat_in_Vset
  from assms(2) show ?thesis
    by (subst cf_def) 
      (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros V_cs_intros)
qed

lemma (in is_functor) cf_is_functor_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> \<BB>"
  by (rule is_functorI)
    (
      auto simp:
        cat_cs_simps
        assms 
        vfsequence_axioms
        cf_is_semifunctor_if_ge_Limit
        HomDom.cat_category_if_ge_Limit
        HomCod.cat_category_if_ge_Limit
        intro: cat_cs_intros 
    )

lemma small_all_cfs[simp]: "small {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(cases \<open>\<Z> \<alpha>\<close>)
  case True
  from is_functor.cf_in_Vset show ?thesis
    by (intro down[of _ \<open>Vset (\<alpha> + \<omega>)\<close>])
      (auto simp: True \<Z>.\<Z>_Limit_\<alpha>\<omega> \<Z>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>.intro \<Z>.\<Z>_\<alpha>_\<alpha>\<omega>)
next
  case False
  then have "{\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>} = {}" by auto
  then show ?thesis by simp
qed

lemma (in is_functor) cf_in_Vset_7: "\<FF> \<in>\<^sub>\<circ> Vset (\<alpha> + 7\<^sub>\<nat>)"
proof-
  note [folded VPow_iff, folded Vset_succ[OF Ord_\<alpha>], cat_cs_intros] =
    cf_ObjMap_vsubset_Vset 
    cf_ArrMap_vsubset_Vset
  from HomDom.cat_category_in_Vset_4 have [cat_cs_intros]:
    "\<AA> \<in>\<^sub>\<circ> Vset (succ (succ (succ (succ \<alpha>))))"
    by (succ_of_numeral) (cs_prems cs_simp: plus_V_succ_right V_cs_simps)
  from HomCod.cat_category_in_Vset_4 have [cat_cs_intros]:
    "\<BB> \<in>\<^sub>\<circ> Vset (succ (succ (succ (succ \<alpha>))))"
    by (succ_of_numeral) (cs_prems cs_simp: plus_V_succ_right V_cs_simps)
  show ?thesis
    by (subst cf_def, succ_of_numeral)
      (
        cs_concl 
          cs_simp: plus_V_succ_right V_cs_simps cat_cs_simps 
          cs_intro: cat_cs_intros V_cs_intros
      )
qed

lemma (in \<Z>) all_cfs_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "all_cfs \<alpha> \<in>\<^sub>\<circ> Vset \<beta>"
proof(rule vsubset_in_VsetI)
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "all_cfs \<alpha> \<subseteq>\<^sub>\<circ> Vset (\<alpha> + 7\<^sub>\<nat>)"
  proof(intro vsubsetI)
    fix \<FF> assume "\<FF> \<in>\<^sub>\<circ> all_cfs \<alpha>"
    then obtain \<AA> \<BB> where \<FF>: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by clarsimp
    interpret is_functor \<alpha> \<AA> \<BB> \<FF> using \<FF> by simp
    show "\<FF> \<in>\<^sub>\<circ> Vset (\<alpha> + 7\<^sub>\<nat>)" by (rule cf_in_Vset_7)
  qed
  from assms(2) show "Vset (\<alpha> + 7\<^sub>\<nat>) \<in>\<^sub>\<circ> Vset \<beta>"
    by (cs_concl cs_intro: V_cs_intros Ord_cs_intros)
qed

lemma small_cfs[simp]: "small {\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"
  by (rule down[of _ \<open>set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}\<close>]) auto



subsection\<open>Opposite functor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter II-2 in \cite{mac_lane_categories_2010}.\<close>

definition op_cf :: "V \<Rightarrow> V"
  where "op_cf \<FF> =
    [\<FF>\<lparr>ObjMap\<rparr>, \<FF>\<lparr>ArrMap\<rparr>, op_cat (\<FF>\<lparr>HomDom\<rparr>), op_cat (\<FF>\<lparr>HomCod\<rparr>)]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma op_cf_components[cat_op_simps]:
  shows "op_cf \<FF>\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>"
    and "op_cf \<FF>\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
    and "op_cf \<FF>\<lparr>HomDom\<rparr> = op_cat (\<FF>\<lparr>HomDom\<rparr>)"
    and "op_cf \<FF>\<lparr>HomCod\<rparr> = op_cat (\<FF>\<lparr>HomCod\<rparr>)"
  unfolding op_cf_def dghm_field_simps by (auto simp: nat_omega_simps)


text\<open>Slicing.\<close>

lemma cf_smcf_op_cf[slicing_commute]: "op_smcf (cf_smcf \<FF>) = cf_smcf (op_cf \<FF>)"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> (op_smcf (cf_smcf \<FF>)) = 4\<^sub>\<nat>"
    unfolding op_smcf_def by (auto simp: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (cf_smcf (op_cf \<FF>)) = 4\<^sub>\<nat>"
    unfolding cf_smcf_def by (auto simp: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (op_smcf (cf_smcf \<FF>)) = \<D>\<^sub>\<circ> (cf_smcf (op_cf \<FF>))"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (op_smcf (cf_smcf \<FF>)) \<Longrightarrow> 
    op_smcf (cf_smcf \<FF>)\<lparr>a\<rparr> = cf_smcf (op_cf \<FF>)\<lparr>a\<rparr>"
    for a
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral,
        unfold cf_smcf_def op_cf_def op_smcf_def dghm_field_simps
      )
      (auto simp: nat_omega_simps slicing_commute)
qed (auto simp: cf_smcf_def op_smcf_def)


text\<open>Elementary properties.\<close>

lemma op_cf_vsv[cat_op_intros]: "vsv (op_cf \<FF>)" unfolding op_cf_def by auto


subsubsection\<open>Further properties\<close>

lemma (in is_functor) is_functor_op: "op_cf \<FF> : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<BB>"
proof(intro is_functorI, unfold cat_op_simps)
  show "vfsequence (op_cf \<FF>)" unfolding op_cf_def by simp
  show "vcard (op_cf \<FF>) = 4\<^sub>\<nat>" 
    unfolding op_cf_def by (auto simp: nat_omega_simps)
  fix c assume "c \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  then show "\<FF>\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
    unfolding cat_op_simps by (auto intro: cat_cs_intros)
qed 
  (
    auto simp: 
      cat_cs_simps
      slicing_commute[symmetric]
      is_semifunctor.is_semifunctor_op 
      cf_is_semifunctor
      HomCod.category_op 
      HomDom.category_op
  )

lemma (in is_functor) is_functor_op'[cat_op_intros]: 
  assumes "\<AA>' = op_cat \<AA>" and "\<BB>' = op_cat \<BB>"
  shows "op_cf \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms(1,2) by (rule is_functor_op)

lemmas is_functor_op[cat_op_intros] = is_functor.is_functor_op'

lemma (in is_functor) cf_op_cf_op_cf[cat_op_simps]: "op_cf (op_cf \<FF>) = \<FF>" 
proof(rule cf_eqI[of \<alpha> \<AA> \<BB> _ \<AA> \<BB>], unfold cat_op_simps)
  show "op_cf (op_cf \<FF>) : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by 
      (
        metis 
          HomCod.cat_op_cat_op_cat 
          HomDom.cat_op_cat_op_cat 
          is_functor.is_functor_op 
          is_functor_op
      )
qed (auto simp: cat_cs_intros)

lemmas cf_op_cf_op_cf[cat_op_simps] = is_functor.cf_op_cf_op_cf

lemma eq_op_cf_iff[cat_op_simps]: 
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "op_cf \<GG> = op_cf \<FF> \<longleftrightarrow> \<GG> = \<FF>"
proof
  interpret L: is_functor \<alpha> \<AA> \<BB> \<GG> by (rule assms(1))
  interpret R: is_functor \<alpha> \<CC> \<DD> \<FF> by (rule assms(2))
  assume prems: "op_cf \<GG> = op_cf \<FF>"
  show "\<GG> = \<FF>"
  proof(rule cf_eqI[OF assms])
    from prems R.cf_op_cf_op_cf L.cf_op_cf_op_cf show 
      "\<GG>\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>" "\<GG>\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
      by metis+
    from prems R.cf_op_cf_op_cf L.cf_op_cf_op_cf have 
      "\<GG>\<lparr>HomDom\<rparr> = \<FF>\<lparr>HomDom\<rparr>" "\<GG>\<lparr>HomCod\<rparr> = \<FF>\<lparr>HomCod\<rparr>"
      by auto
    then show "\<AA> = \<CC>" "\<BB> = \<DD>" by (simp_all add: cat_cs_simps)
  qed
qed auto



subsection\<open>Composition of covariant functors\<close>


subsubsection\<open>Definition and elementary properties\<close>

abbreviation (input) cf_comp :: "V \<Rightarrow> V \<Rightarrow> V" (infixl "\<circ>\<^sub>C\<^sub>F" 55)
  where "cf_comp \<equiv> dghm_comp"


text\<open>Slicing.\<close>

lemma cf_smcf_smcf_comp[slicing_commute]: 
  "cf_smcf \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F cf_smcf \<FF> = cf_smcf (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)"
  unfolding dghm_comp_def cf_smcf_def dghm_field_simps 
  by (simp add: nat_omega_simps)


subsubsection\<open>Object map\<close>

lemma cf_comp_ObjMap_vsv[cat_cs_intros]: 
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "vsv ((\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>)"
proof-
  interpret L: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_comp_ObjMap_vsv
          [
            OF L.cf_is_semifunctor R.cf_is_semifunctor, 
            unfolded slicing_simps slicing_commute
          ]
      )
qed

lemma cf_comp_ObjMap_vdomain[cat_cs_simps]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
proof-
  interpret L: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_comp_ObjMap_vdomain
          [
            OF L.cf_is_semifunctor R.cf_is_semifunctor, 
            unfolded slicing_simps slicing_commute
          ]
      )
qed

lemma cf_comp_ObjMap_vrange:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
proof-
  interpret L: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_comp_ObjMap_vrange
          [
            OF L.cf_is_semifunctor R.cf_is_semifunctor, 
            unfolded slicing_simps slicing_commute
          ]
      )
qed

lemma cf_comp_ObjMap_app[cat_cs_simps]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and [simp]: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "(\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
proof-
  interpret L: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_comp_ObjMap_app
          [
            OF L.cf_is_semifunctor R.cf_is_semifunctor, 
            unfolded slicing_simps slicing_commute, 
            OF assms(3)
          ]
      )
qed


subsubsection\<open>Arrow map\<close>

lemma cf_comp_ArrMap_vsv[cat_cs_intros]: 
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "vsv ((\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>)"
proof-
  interpret L: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis 
    by 
      (
        rule smcf_comp_ArrMap_vsv
          [
            OF L.cf_is_semifunctor R.cf_is_semifunctor, 
            unfolded slicing_simps slicing_commute
          ]
      )
qed

lemma cf_comp_ArrMap_vdomain[cat_cs_simps]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
proof-
  interpret L: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis 
    by 
      (
        rule smcf_comp_ArrMap_vdomain
          [
            OF L.cf_is_semifunctor R.cf_is_semifunctor, 
            unfolded slicing_simps slicing_commute
          ]
      )
qed

lemma cf_comp_ArrMap_vrange:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof-
  interpret L: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_comp_ArrMap_vrange
          [
            OF L.cf_is_semifunctor R.cf_is_semifunctor, 
            unfolded slicing_simps slicing_commute
          ]
      )
qed

lemma cf_comp_ArrMap_app[cat_cs_simps]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and [simp]: "f \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
  shows "(\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr>"
proof-
  interpret L: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_comp_ArrMap_app
          [
            OF L.cf_is_semifunctor R.cf_is_semifunctor, 
            unfolded slicing_simps slicing_commute,
            OF assms(3)
          ]
      )
qed


subsubsection\<open>Further properties\<close>

lemma cf_comp_is_functorI[cat_cs_intros]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret L: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1))
  interpret R: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
  proof(rule is_functorI, unfold dghm_comp_components(3,4))
    show "vfsequence (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)" by (simp add: dghm_comp_def)
    show "vcard (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) = 4\<^sub>\<nat>"  
      unfolding dghm_comp_def by (simp add: nat_omega_simps)
    show "cf_smcf (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<CC>"
      unfolding cf_smcf_smcf_comp[symmetric] 
      by (cs_concl cs_intro: smc_cs_intros slicing_intros cat_cs_intros)
    fix c assume "c \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    with assms show 
      "(\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>(\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed (auto simp: cat_cs_simps intro: cat_cs_intros)
qed

lemma cf_comp_assoc[cat_cs_simps]:
  assumes "\<HH> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "(\<HH> \<circ>\<^sub>C\<^sub>F \<GG>) \<circ>\<^sub>C\<^sub>F \<FF> = \<HH> \<circ>\<^sub>C\<^sub>F (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)"
proof(rule cf_eqI[of \<alpha> \<AA> \<DD> _ \<AA> \<DD>])
  interpret \<HH>: is_functor \<alpha> \<CC> \<DD> \<HH> by (rule assms(1)) 
  interpret \<GG>: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(2)) 
  interpret \<FF>: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(3)) 
  from \<FF>.is_functor_axioms \<GG>.is_functor_axioms \<HH>.is_functor_axioms 
  show "\<HH> \<circ>\<^sub>C\<^sub>F (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "\<HH> \<circ>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"  
    by (auto simp: cat_cs_simps intro: cat_cs_intros)
qed (simp_all add: dghm_comp_components vcomp_assoc)


text\<open>The opposite of the covariant composition of functors.\<close>

lemma op_cf_cf_comp[cat_op_simps]: "op_cf (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) = op_cf \<GG> \<circ>\<^sub>C\<^sub>F op_cf \<FF>"
  unfolding dghm_comp_def op_cf_def dghm_field_simps
  by (simp add: nat_omega_simps)



subsection\<open>Composition of contravariant functors\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See section 1.2 in \cite{bodo_categories_1970}.\<close>

definition cf_cn_comp :: "V \<Rightarrow> V \<Rightarrow> V" (infixl "\<^sub>C\<^sub>F\<circ>" 55)
  where "\<GG> \<^sub>C\<^sub>F\<circ> \<FF> =
    [
      \<GG>\<lparr>ObjMap\<rparr> \<circ>\<^sub>\<circ> \<FF>\<lparr>ObjMap\<rparr>,
      \<GG>\<lparr>ArrMap\<rparr> \<circ>\<^sub>\<circ> \<FF>\<lparr>ArrMap\<rparr>,
      op_cat (\<FF>\<lparr>HomDom\<rparr>),
      \<GG>\<lparr>HomCod\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_cn_comp_components:
  shows "(\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr> = \<GG>\<lparr>ObjMap\<rparr> \<circ>\<^sub>\<circ> \<FF>\<lparr>ObjMap\<rparr>"
    and "(\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr> = \<GG>\<lparr>ArrMap\<rparr> \<circ>\<^sub>\<circ> \<FF>\<lparr>ArrMap\<rparr>"
    and [cat_cn_cs_simps]: "(\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>HomDom\<rparr> = op_cat (\<FF>\<lparr>HomDom\<rparr>)"
    and [cat_cn_cs_simps]: "(\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>HomCod\<rparr> = \<GG>\<lparr>HomCod\<rparr>"
  unfolding cf_cn_comp_def dghm_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma cf_smcf_cf_cn_comp[slicing_commute]: 
  "cf_smcf \<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> cf_smcf \<FF> = cf_smcf (\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)"
  unfolding smcf_cn_comp_def cf_cn_comp_def cf_smcf_def  
  by (simp add: nat_omega_simps slicing_commute dghm_field_simps)


subsubsection\<open>Object map: two contravariant functors\<close>

lemma cf_cn_comp_ObjMap_vsv[cat_cn_cs_intros]: 
  assumes "\<GG> : \<BB> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "vsv ((\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr>)"
proof-
  interpret L: is_functor \<alpha> \<open>op_cat \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<open>op_cat \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_cn_cov_comp_ObjMap_vsv
          [
            OF 
              L.cf_is_semifunctor[unfolded slicing_commute[symmetric]] 
              R.cf_is_semifunctor[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma cf_cn_comp_ObjMap_vdomain[cat_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
proof-
  interpret L: is_functor \<alpha> \<open>op_cat \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<open>op_cat \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_cn_comp_ObjMap_vdomain
          [
            OF 
              L.cf_is_semifunctor[unfolded slicing_commute[symmetric]] 
              R.cf_is_semifunctor[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma cf_cn_comp_ObjMap_vrange:
  assumes "\<GG> : \<BB> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
proof-
  interpret L: is_functor \<alpha> \<open>op_cat \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<open>op_cat \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_cn_comp_ObjMap_vrange
          [
            OF 
              L.cf_is_semifunctor[unfolded slicing_commute[symmetric]] 
              R.cf_is_semifunctor[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma cf_cn_comp_ObjMap_app[cat_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "(\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
proof-
  interpret L: is_functor \<alpha> \<open>op_cat \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<open>op_cat \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_cn_comp_ObjMap_app
          [
            OF 
              L.cf_is_semifunctor[unfolded slicing_commute[symmetric]] 
              R.cf_is_semifunctor[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps, 
            OF assms(3)
          ]
      )
qed


subsubsection\<open>Arrow map: two contravariant functors\<close>

lemma cf_cn_comp_ArrMap_vsv[cat_cn_cs_intros]: 
  assumes "\<GG> : \<BB> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "vsv ((\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>)"
proof-
  interpret L: is_functor \<alpha> \<open>op_cat \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<open>op_cat \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_cn_cov_comp_ArrMap_vsv
          [
            OF 
              L.cf_is_semifunctor[unfolded slicing_commute[symmetric]] 
              R.cf_is_semifunctor[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma cf_cn_comp_ArrMap_vdomain[cat_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
proof-
  interpret L: is_functor \<alpha> \<open>op_cat \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<open>op_cat \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_cn_comp_ArrMap_vdomain
          [
            OF 
              L.cf_is_semifunctor[unfolded slicing_commute[symmetric]] 
              R.cf_is_semifunctor[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma cf_cn_comp_ArrMap_vrange:
  assumes "\<GG> : \<BB> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof-
  interpret L: is_functor \<alpha> \<open>op_cat \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<open>op_cat \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_cn_comp_ArrMap_vrange
          [
            OF 
              L.cf_is_semifunctor[unfolded slicing_commute[symmetric]] 
              R.cf_is_semifunctor[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma cf_cn_comp_ArrMap_app[cat_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
  shows "(\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>\<rparr>"
proof-
  interpret L: is_functor \<alpha> \<open>op_cat \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<open>op_cat \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_cn_comp_ArrMap_app
          [
            OF 
              L.cf_is_semifunctor[unfolded slicing_commute[symmetric]] 
              R.cf_is_semifunctor[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps,
            OF assms(3)
          ]
      )
qed


subsubsection\<open>Object map: contravariant and covariant functor\<close>

lemma cf_cn_cov_comp_ObjMap_vsv[cat_cn_cs_intros]: 
  assumes "\<GG> : \<BB> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "vsv ((\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr>)"
proof-
  interpret L: is_functor \<alpha> \<open>op_cat \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_cn_cov_comp_ObjMap_vsv
          [
            OF 
              L.cf_is_semifunctor[unfolded slicing_commute[symmetric]]
              R.cf_is_semifunctor[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma cf_cn_cov_comp_ObjMap_vdomain[cat_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
proof-
  interpret L: is_functor \<alpha> \<open>op_cat \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_cn_cov_comp_ObjMap_vdomain
          [
            OF 
              L.cf_is_semifunctor[unfolded slicing_commute[symmetric]] 
              R.cf_is_semifunctor,
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma cf_cn_cov_comp_ObjMap_vrange:
  assumes "\<GG> : \<BB> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
proof-
  interpret L: is_functor \<alpha> \<open>op_cat \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_cn_cov_comp_ObjMap_vrange
          [
            OF 
              L.cf_is_semifunctor[unfolded slicing_commute[symmetric]] 
              R.cf_is_semifunctor,
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma cf_cn_cov_comp_ObjMap_app[cat_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "(\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
proof-
  interpret L: is_functor \<alpha> \<open>op_cat \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_cn_cov_comp_ObjMap_app
          [
            OF 
              L.cf_is_semifunctor[unfolded slicing_commute[symmetric]] 
              R.cf_is_semifunctor,
            unfolded slicing_commute slicing_simps,
            OF assms(3)
          ]
      )
qed


subsubsection\<open>Arrow map: contravariant and covariant functors\<close>

lemma cf_cn_cov_comp_ArrMap_vsv[cat_cn_cs_intros]: 
  assumes "\<GG> : \<BB> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "vsv ((\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>)"
proof-
  interpret L: is_functor \<alpha> \<open>op_cat \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_cn_cov_comp_ArrMap_vsv
          [
            OF 
              L.cf_is_semifunctor[unfolded slicing_commute[symmetric]]
              R.cf_is_semifunctor[unfolded slicing_commute[symmetric]],
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma cf_cn_cov_comp_ArrMap_vdomain[cat_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
proof-
  interpret L: is_functor \<alpha> \<open>op_cat \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_cn_cov_comp_ArrMap_vdomain
          [
            OF 
              L.cf_is_semifunctor[unfolded slicing_commute[symmetric]] 
              R.cf_is_semifunctor,
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma cf_cn_cov_comp_ArrMap_vrange:
  assumes "\<GG> : \<BB> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof-
  interpret L: is_functor \<alpha> \<open>op_cat \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_cn_cov_comp_ArrMap_vrange
          [
            OF 
              L.cf_is_semifunctor[unfolded slicing_commute[symmetric]] 
              R.cf_is_semifunctor,
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma cf_cn_cov_comp_ArrMap_app[cat_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
  shows "(\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>\<rparr>"
proof-
  interpret L: is_functor \<alpha> \<open>op_cat \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
    by 
      (
        rule smcf_cn_cov_comp_ArrMap_app
          [
            OF 
              L.cf_is_semifunctor[unfolded slicing_commute[symmetric]] 
              R.cf_is_semifunctor,
            unfolded slicing_commute slicing_simps,
            OF assms(3)
          ]
      )
qed


subsubsection\<open>Further properties\<close>

lemma cf_cn_comp_is_functorI[cat_cn_cs_intros]:
  assumes "category \<alpha> \<AA>" and "\<GG> : \<BB> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<^sub>C\<^sub>F\<circ> \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret L: is_functor \<alpha> \<open>op_cat \<BB>\<close> \<CC> \<GG> by (rule assms(2))
  interpret R: is_functor \<alpha> \<open>op_cat \<AA>\<close> \<BB> \<FF> by (rule assms(3))
  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  show ?thesis
  proof(rule is_functorI, unfold cf_cn_comp_components(3,4) cat_op_simps)
    show "vfsequence (\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)"
      unfolding cf_cn_comp_def by (simp add: nat_omega_simps)
    show "vcard (\<GG> \<^sub>C\<^sub>F\<circ> \<FF>) = 4\<^sub>\<nat>"
      unfolding cf_cn_comp_def by (simp add: nat_omega_simps)
    from assms(1) L.cf_is_semifunctor R.cf_is_semifunctor show 
      "cf_smcf (\<GG> \<^sub>C\<^sub>F\<circ> \<FF>) : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<CC>"
      unfolding cf_smcf_cf_cn_comp[symmetric] 
      by 
        (
          cs_concl cs_intro: 
            cat_cs_intros slicing_intros smc_cn_cs_intros
        )
    fix c assume "c \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    with assms show 
      "(\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>(\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_op_simps cat_cn_cs_simps cs_intro: cat_cs_intros
        )
  qed (auto simp: cat_cs_simps cat_cs_intros cat_op_simps)
qed


text\<open>See section 1.2 in \cite{bodo_categories_1970}).\<close>

lemma cf_cn_cov_comp_is_functor[cat_cn_cs_intros]:
  assumes "\<GG> : \<BB> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<^sub>C\<^sub>F\<circ> \<FF> : \<AA> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret L: is_functor \<alpha> \<open>op_cat \<BB>\<close> \<CC> \<GG> by (rule assms(1))
  interpret R: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
  proof
    (
      rule is_functorI, 
      unfold cf_cn_comp_components(3,4) cat_op_simps slicing_commute[symmetric]
    )
    show "vfsequence (\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)" unfolding cf_cn_comp_def by simp
    show "vcard (\<GG> \<^sub>C\<^sub>F\<circ> \<FF>) = 4\<^sub>\<nat>"
      unfolding cf_cn_comp_def by (auto simp: nat_omega_simps)
    from L.cf_is_semifunctor show 
      "cf_smcf \<GG> \<^sub>S\<^sub>M\<^sub>C\<^sub>F\<circ> cf_smcf \<FF> : op_smc (cat_smc \<AA>) \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<CC>"
      by (cs_concl cs_intro: cat_cs_intros slicing_intros smc_cs_intros)
    fix c assume "c \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    with assms show "(\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>(\<GG> \<^sub>C\<^sub>F\<circ> \<FF>)\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_cn_cs_simps 
            cs_intro: cat_cs_intros
        )
  qed (auto simp: cat_cs_simps cat_cs_intros)
qed


text\<open>See section 1.2 in \cite{bodo_categories_1970}.\<close>

lemma cf_cov_cn_comp_is_functor[cat_cn_cs_intros]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<^sub>C\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms by (rule cf_comp_is_functorI)


text\<open>The opposite of the contravariant composition of functors.\<close>

lemma op_cf_cf_cn_comp[cat_op_simps]: "op_cf (\<GG> \<^sub>C\<^sub>F\<circ> \<FF>) = op_cf \<GG> \<^sub>C\<^sub>F\<circ> op_cf \<FF>"
  unfolding op_cf_def cf_cn_comp_def dghm_field_simps 
  by (auto simp: nat_omega_simps)



subsection\<open>Identity functor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>

abbreviation (input) cf_id :: "V \<Rightarrow> V" where "cf_id \<equiv> dghm_id"


text\<open>Slicing.\<close>

lemma cf_smcf_cf_id[slicing_commute]: "smcf_id (cat_smc \<CC>) = cf_smcf (cf_id \<CC>)"
  unfolding dghm_id_def cat_smc_def cf_smcf_def dghm_field_simps dg_field_simps
  by (simp add: nat_omega_simps)

context category
begin

interpretation smc: semicategory \<alpha> \<open>cat_smc \<CC>\<close> by (rule cat_semicategory)

lemmas_with [unfolded slicing_simps]:
  cat_smcf_id_is_semifunctor = smc.smc_smcf_id_is_semifunctor

end


subsubsection\<open>Object map\<close>

lemmas [cat_cs_simps] = dghm_id_ObjMap_app


subsubsection\<open>Arrow map\<close>

lemmas [cat_cs_simps] = dghm_id_ArrMap_app


subsubsection\<open>Opposite of an identity functor.\<close>

lemma op_cf_cf_id[cat_op_simps]: "op_cf (cf_id \<CC>) = cf_id (op_cat \<CC>)"
  unfolding dghm_id_def op_cat_def op_cf_def dghm_field_simps dg_field_simps
  by (auto simp: nat_omega_simps)


subsubsection\<open>An identity functor is a functor\<close>

lemma (in category) cat_cf_id_is_functor: "cf_id \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof(rule is_functorI, unfold dghm_id_components)
  from cat_smcf_id_is_semifunctor show 
    "cf_smcf (cf_id \<CC>) : cat_smc \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<CC>"
    by (simp add: slicing_commute)
  from cat_CId_is_arr show 
    "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> vid_on (\<CC>\<lparr>Arr\<rparr>)\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>vid_on (\<CC>\<lparr>Obj\<rparr>)\<lparr>c\<rparr>\<rparr>"
    for c
    by auto
qed (auto simp: dghm_id_def nat_omega_simps cat_cs_intros)

lemma (in category) cat_cf_id_is_functor': 
  assumes "\<AA> = \<CC>" and "\<BB> = \<CC>"
  shows "cf_id \<CC> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  unfolding assms by (rule cat_cf_id_is_functor)

lemmas [cat_cs_intros] = category.cat_cf_id_is_functor'


subsubsection\<open>Further properties\<close>

lemma (in is_functor) cf_cf_comp_cf_id_left[cat_cs_simps]: "cf_id \<BB> \<circ>\<^sub>C\<^sub>F \<FF> = \<FF>"
  \<comment>\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}).\<close>
  by 
    (
      rule cf_eqI,
      unfold dghm_id_components dghm_comp_components dghm_id_components
    )
    (auto intro: cat_cs_intros simp: cf_ArrMap_vrange cf_ObjMap_vrange)

lemmas [cat_cs_simps] = is_functor.cf_cf_comp_cf_id_left

lemma (in is_functor) cf_cf_comp_cf_id_right[cat_cs_simps]: "\<FF> \<circ>\<^sub>C\<^sub>F cf_id \<AA> = \<FF>"
  \<comment>\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}).\<close>
  by 
    (
      rule cf_eqI, 
      unfold dghm_id_components dghm_comp_components dghm_id_components
    )
    (
      auto 
        intro: cat_cs_intros 
        simp: cat_cs_simps cf_ArrMap_vrange cf_ObjMap_vrange 
    )

lemmas [cat_cs_simps] = is_functor.cf_cf_comp_cf_id_right



subsection\<open>Constant functor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter III-3 in \cite{mac_lane_categories_2010}.\<close>

abbreviation cf_const :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_const \<CC> \<DD> a \<equiv> smcf_const \<CC> \<DD> a (\<DD>\<lparr>CId\<rparr>\<lparr>a\<rparr>)"


text\<open>Slicing.\<close>

lemma cf_smcf_cf_const[slicing_commute]: 
  "smcf_const (cat_smc \<CC>) (cat_smc \<DD>) a (\<DD>\<lparr>CId\<rparr>\<lparr>a\<rparr>) = cf_smcf (cf_const \<CC> \<DD> a)"
  unfolding 
    dghm_const_def cat_smc_def cf_smcf_def dghm_field_simps dg_field_simps
  by (simp add: nat_omega_simps)


subsubsection\<open>Object map and arrow map\<close>

context
  fixes \<DD> a :: V
begin

lemmas_with [where \<DD>=\<DD> and a=a and f=\<open>\<DD>\<lparr>CId\<rparr>\<lparr>a\<rparr>\<close>, cat_cs_simps]: 
  dghm_const_ObjMap_app
  dghm_const_ArrMap_app

end


subsubsection\<open>Opposite constant functor\<close>

lemma op_cf_cf_const[cat_op_simps]:
  "op_cf (cf_const \<CC> \<DD> a) = cf_const (op_cat \<CC>) (op_cat \<DD>) a"
  unfolding dghm_const_def op_cat_def op_cf_def dghm_field_simps dg_field_simps
  by (auto simp: nat_omega_simps)


subsubsection\<open>A constant functor is a functor\<close>

lemma cf_const_is_functor: 
  assumes "category \<alpha> \<CC>" and "category \<alpha> \<DD>" and "a \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>" 
  shows "cf_const \<CC> \<DD> a : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
proof-
  interpret \<CC>: category \<alpha> \<CC> by (rule assms(1))
  interpret \<DD>: category \<alpha> \<DD> by (rule assms(2))
  show ?thesis
  proof(intro is_functorI, tactic\<open>distinct_subgoals_tac\<close>)
    show "vfsequence (dghm_const \<CC> \<DD> a (\<DD>\<lparr>CId\<rparr>\<lparr>a\<rparr>))"
      unfolding dghm_const_def by simp
    show "vcard (cf_const \<CC> \<DD> a) = 4\<^sub>\<nat>"
      unfolding dghm_const_def by (simp add: nat_omega_simps)
    from assms show "cf_smcf (cf_const \<CC> \<DD> a) : cat_smc \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<DD>"
      by 
        ( 
          cs_concl
            cs_simp: cat_cs_simps slicing_simps slicing_commute[symmetric] 
            cs_intro: smc_cs_intros cat_cs_intros slicing_intros
        )
    fix c assume "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    with assms show 
      "cf_const \<CC> \<DD> a\<lparr>ArrMap\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<DD>\<lparr>CId\<rparr>\<lparr>cf_const \<CC> \<DD> a\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed (auto simp: dghm_const_components assms)
qed 

lemma cf_const_is_functor'[cat_cs_intros]: 
  assumes "category \<alpha> \<CC>" 
    and "category \<alpha> \<DD>" 
    and "a \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>" 
    and "\<AA> = \<CC>"
    and "\<BB> = \<DD>"
  shows "cf_const \<CC> \<DD> a : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms(1-3) unfolding assms(4,5) by (rule cf_const_is_functor)



subsection\<open>Faithful functor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}).\<close>

locale is_ft_functor = is_functor \<alpha> \<AA> \<BB> \<FF> for \<alpha> \<AA> \<BB> \<FF> + 
  assumes ft_cf_is_ft_semifunctor[slicing_intros]: 
    "cf_smcf \<FF> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> cat_smc \<BB>"

syntax "_is_ft_functor" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_ft_functor \<alpha> \<AA> \<BB> \<FF>"

lemma (in is_ft_functor) ft_cf_is_ft_functor':
  assumes "\<AA>' = cat_smc \<AA>" and "\<BB>' = cat_smc \<BB>"
  shows "cf_smcf \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule ft_cf_is_ft_semifunctor)

lemmas [slicing_intros] = is_ft_functor.ft_cf_is_ft_functor'


text\<open>Rules.\<close>

lemma (in is_ft_functor) is_ft_functor_axioms'[cf_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_ft_functor_axioms)

mk_ide rf is_ft_functor_def[unfolded is_ft_functor_axioms_def]
  |intro is_ft_functorI|
  |dest is_ft_functorD[dest]|
  |elim is_ft_functorE[elim]|

lemmas [cf_cs_intros] = is_ft_functorD(1)

lemma is_ft_functorI':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<And>a b. \<lbrakk> a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow> v11 (\<FF>\<lparr>ArrMap\<rparr> \<restriction>\<^sup>l\<^sub>\<circ> Hom \<AA> a b)"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms
  by (intro is_ft_functorI)
    (
      simp_all add: 
        assms(1) 
        is_ft_semifunctorI'[OF is_functorD(6)[
          OF assms(1)], unfolded slicing_simps
          ]
    )

lemma is_ft_functorD':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<And>a b. \<lbrakk> a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow> v11 (\<FF>\<lparr>ArrMap\<rparr> \<restriction>\<^sup>l\<^sub>\<circ> Hom \<AA> a b)"
  by 
    (
      simp_all add: 
        is_ft_functorD[OF assms(1)] 
        is_ft_semifunctorD'(2)[
          OF is_ft_functorD(2)[OF assms(1)], unfolded slicing_simps
          ]
    )

lemma is_ft_functorE':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>"
  obtains "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<And>a b. \<lbrakk> a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow> v11 (\<FF>\<lparr>ArrMap\<rparr> \<restriction>\<^sup>l\<^sub>\<circ> Hom \<AA> a b)"
  using assms by (simp_all add: is_ft_functorD')


text\<open>Elementary properties.\<close>

context is_ft_functor
begin

interpretation smcf: is_ft_semifunctor \<alpha> \<open>cat_smc \<AA>\<close> \<open>cat_smc \<BB>\<close> \<open>cf_smcf \<FF>\<close>
  by (rule ft_cf_is_ft_semifunctor) 

lemmas_with [unfolded slicing_simps]:
  ft_cf_v11_on_Hom = smcf.ft_smcf_v11_on_Hom

end


subsubsection\<open>Opposite faithful functor.\<close>

lemma (in is_ft_functor) is_ft_functor_op': 
  "op_cf \<FF> : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> op_cat \<BB>"   
  by (rule is_ft_functorI, unfold slicing_commute[symmetric])
    (
      simp_all add: 
        is_functor_op is_ft_semifunctor.is_ft_semifunctor_op 
        ft_cf_is_ft_semifunctor
    )

lemma (in is_ft_functor) is_ft_functor_op: 
  assumes "\<AA>' = op_cat \<AA>" and "\<BB>' = op_cat \<BB>"
  shows "op_cf \<FF> : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> op_cat \<BB>"   
  unfolding assms by (rule is_ft_functor_op')

lemmas is_ft_functor_op[cat_op_intros] = is_ft_functor.is_ft_functor_op'


subsubsection\<open>The composition of faithful functors is a faithful functor\<close>

lemma cf_comp_is_ft_functor[cf_cs_intros]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_ft_functorI)
  interpret \<GG>: is_ft_functor \<alpha> \<BB> \<CC> \<GG> by (simp add: assms(1))
  interpret \<FF>: is_ft_functor \<alpha> \<AA> \<BB> \<FF> by (simp add: assms(2))
  from \<FF>.is_functor_axioms \<GG>.is_functor_axioms show "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: cat_cs_intros)
  then interpret is_functor \<alpha> \<AA> \<CC> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<FF>\<close> .
  show "cf_smcf (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> cat_smc \<CC>" 
    by 
      ( 
        cs_concl 
          cs_simp: slicing_commute[symmetric] 
          cs_intro: cf_cs_intros smcf_cs_intros slicing_intros
      )
qed



subsection\<open>Full functor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}).\<close>

locale is_fl_functor = is_functor \<alpha> \<AA> \<BB> \<FF> for \<alpha> \<AA> \<BB> \<FF> + 
  assumes fl_cf_is_fl_semifunctor:
    "cf_smcf \<FF> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> cat_smc \<BB>"

syntax "_is_fl_functor" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_fl_functor \<alpha> \<AA> \<BB> \<FF>"

lemma (in is_fl_functor) fl_cf_is_fl_functor'[slicing_intros]:
  assumes "\<AA>' = cat_smc \<AA>" and "\<BB>' = cat_smc \<BB>"
  shows "cf_smcf \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule fl_cf_is_fl_semifunctor)

lemmas [slicing_intros] = is_fl_functor.fl_cf_is_fl_semifunctor


text\<open>Rules.\<close>

lemma (in is_fl_functor) is_fl_functor_axioms'[cf_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_fl_functor_axioms)

mk_ide rf is_fl_functor_def[unfolded is_fl_functor_axioms_def]
  |intro is_fl_functorI|
  |dest is_fl_functorD[dest]|
  |elim is_fl_functorE[elim]|

lemmas [cf_cs_intros] = is_fl_functorD(1)

lemma is_fl_functorI':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<And>a b. \<lbrakk> a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow>
    \<FF>\<lparr>ArrMap\<rparr> `\<^sub>\<circ> (Hom \<AA> a b) = Hom \<BB> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms
  by (intro is_fl_functorI)
    (
      simp_all add: 
        assms(1) 
        is_fl_semifunctorI'[
          OF is_functorD(6)[OF assms(1)], unfolded slicing_simps
          ]
    )

lemma is_fl_functorD':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<And>a b. \<lbrakk> a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow>
    \<FF>\<lparr>ArrMap\<rparr> `\<^sub>\<circ> (Hom \<AA> a b) = Hom \<BB> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
  by 
    (
      simp_all add: 
        is_fl_functorD[OF assms(1)] 
        is_fl_semifunctorD'(2)[
          OF is_fl_functorD(2)[OF assms(1)], unfolded slicing_simps
          ]
    )

lemma is_fl_functorE':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>"
  obtains "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<And>a b. \<lbrakk> a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow> 
    \<FF>\<lparr>ArrMap\<rparr> `\<^sub>\<circ> (Hom \<AA> a b) = Hom \<BB> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
  using assms by (simp_all add: is_fl_functorD')


text\<open>Elementary properties.\<close>

context is_fl_functor
begin

interpretation smcf: is_fl_semifunctor \<alpha> \<open>cat_smc \<AA>\<close> \<open>cat_smc \<BB>\<close> \<open>cf_smcf \<FF>\<close>
  by (rule fl_cf_is_fl_semifunctor) 

lemmas_with [unfolded slicing_simps]:
  fl_cf_surj_on_Hom = smcf.fl_smcf_surj_on_Hom

end


subsubsection\<open>Opposite full functor\<close>

lemma (in is_fl_functor) is_fl_functor_op[cat_op_intros]: 
  "op_cf \<FF> : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> op_cat \<BB>"    
  by (rule is_fl_functorI, unfold slicing_commute[symmetric])
    (simp_all add: cat_op_intros smc_op_intros slicing_intros)

lemmas is_fl_functor_op[cat_op_intros] = is_fl_functor.is_fl_functor_op


subsubsection\<open>The composition of full functor is a full functor\<close>

lemma cf_comp_is_fl_functor[cf_cs_intros]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_fl_functorI)
  interpret \<FF>: is_fl_functor \<alpha> \<AA> \<BB> \<FF> using assms(2) by simp
  interpret \<GG>: is_fl_functor \<alpha> \<BB> \<CC> \<GG> using assms(1) by simp
  from \<FF>.is_functor_axioms \<GG>.is_functor_axioms show "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    by (cs_concl cs_intro: cat_cs_intros)
  show "cf_smcf (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> cat_smc \<CC>" 
    by 
      (
        cs_concl 
          cs_simp: slicing_commute[symmetric] 
          cs_intro: cf_cs_intros smcf_cs_intros slicing_intros
      )
qed



subsection\<open>Fully faithful functor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}).\<close>

locale is_ff_functor = is_ft_functor \<alpha> \<AA> \<BB> \<FF> + is_fl_functor \<alpha> \<AA> \<BB> \<FF>
  for \<alpha> \<AA> \<BB> \<FF>

syntax "_is_ff_functor" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>f\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_ff_functor \<alpha> \<AA> \<BB> \<FF>"


text\<open>Rules.\<close>

mk_ide rf is_ff_functor_def
  |intro is_ff_functorI|
  |dest is_ff_functorD[dest]|
  |elim is_ff_functorE[elim]|

lemmas [cf_cs_intros] = is_ff_functorD


text\<open>Elementary properties.\<close>

lemma (in is_ff_functor) ff_cf_is_ff_semifunctor:
  "cf_smcf \<FF> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> cat_smc \<BB>"
  by (rule is_ff_semifunctorI) (auto intro: slicing_intros)

lemma (in is_ff_functor) ff_cf_is_ff_semifunctor'[slicing_intros]:
  assumes "\<AA>' = cat_smc \<AA>" and "\<BB>' = cat_smc \<BB>"
  shows "cf_smcf \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule ff_cf_is_ff_semifunctor)

lemmas [slicing_intros] = is_ff_functor.ff_cf_is_ff_semifunctor'


subsubsection\<open>Opposite fully faithful functor\<close>

lemma (in is_ff_functor) is_ff_functor_op: 
  "op_cf \<FF> : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> op_cat \<BB>"    
  by (rule is_ff_functorI) (auto simp: is_fl_functor_op is_ft_functor_op)

lemma (in is_ff_functor) is_ff_functor_op'[cat_op_intros]: 
  assumes "\<AA>' = op_cat \<AA>" and "\<BB>' = op_cat \<BB>"
  shows "op_cf \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule is_ff_functor_op)

lemmas is_ff_functor_op[cat_op_intros] = is_ff_functor.is_ff_functor_op


subsubsection\<open>
The composition of fully faithful functors is a fully faithful functor
\<close>

lemma cf_comp_is_ff_functor[cf_cs_intros]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms 
  by (intro is_ff_functorI, elim is_ff_functorE) (auto simp: cf_cs_intros)



subsection\<open>Isomorphism of categories\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}).\<close>

locale is_iso_functor = is_functor \<alpha> \<AA> \<BB> \<FF> for \<alpha> \<AA> \<BB> \<FF> + 
  assumes iso_cf_is_iso_semifunctor: 
    "cf_smcf \<FF> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> cat_smc \<BB>"

syntax "_is_iso_functor" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_iso_functor \<alpha> \<AA> \<BB> \<FF>"

lemma (in is_iso_functor) iso_cf_is_iso_semifunctor'[slicing_intros]:
  assumes "\<AA>' = cat_smc \<AA>" "\<BB>' = cat_smc \<BB>"
  shows "cf_smcf \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule iso_cf_is_iso_semifunctor)

lemmas [slicing_intros] = is_iso_semifunctor.iso_smcf_is_iso_dghm'


text\<open>Rules.\<close>

lemma (in is_iso_functor) is_iso_functor_axioms'[cf_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_iso_functor_axioms)

mk_ide rf is_iso_functor_def[unfolded is_iso_functor_axioms_def]
  |intro is_iso_functorI|
  |dest is_iso_functorD[dest]|
  |elim is_iso_functorE[elim]|

lemma is_iso_functorI':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "v11 (\<FF>\<lparr>ObjMap\<rparr>)"
    and "v11 (\<FF>\<lparr>ArrMap\<rparr>)"
    and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
    and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms
  by (intro is_iso_functorI)
    (
      simp_all add: 
        assms(1) 
        is_iso_semifunctorI'[
          OF is_functorD(6)[OF assms(1)], unfolded slicing_simps
          ]
    )

lemma is_iso_functorD':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "v11 (\<FF>\<lparr>ObjMap\<rparr>)"
    and "v11 (\<FF>\<lparr>ArrMap\<rparr>)"
    and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
    and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>"
  by 
    (
      simp_all add: 
        is_iso_functorD[OF assms(1)] 
        is_iso_semifunctorD'(2-5)[
          OF is_iso_functorD(2)[OF assms(1)], unfolded slicing_simps
          ]
    )

lemma is_iso_functorE':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  obtains "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "v11 (\<FF>\<lparr>ObjMap\<rparr>)"
    and "v11 (\<FF>\<lparr>ArrMap\<rparr>)"
    and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
    and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>"
  using assms by (simp_all add: is_iso_functorD')


text\<open>Elementary properties.\<close>

context is_iso_functor
begin

interpretation smcf: is_iso_semifunctor \<alpha> \<open>cat_smc \<AA>\<close> \<open>cat_smc \<BB>\<close> \<open>cf_smcf \<FF>\<close>
  by (rule iso_cf_is_iso_semifunctor) 

lemmas_with [unfolded slicing_simps]:
  iso_cf_ObjMap_vrange[simp] = smcf.iso_smcf_ObjMap_vrange
  and iso_cf_ArrMap_vrange[simp] = smcf.iso_smcf_ArrMap_vrange

sublocale ObjMap: v11 \<open>\<FF>\<lparr>ObjMap\<rparr>\<close>
  rewrites "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>" and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
  by (rule smcf.ObjMap.v11_axioms[unfolded slicing_simps]) 
    (simp_all add: cat_cs_simps cf_cs_simps)
  
sublocale ArrMap: v11 \<open>\<FF>\<lparr>ArrMap\<rparr>\<close>
  rewrites "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>" and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>"
  by (rule smcf.ArrMap.v11_axioms[unfolded slicing_simps])
    (simp_all add: cat_cs_simps smcf_cs_simps)

lemmas_with [unfolded slicing_simps]:
  iso_cf_Obj_HomDom_if_Obj_HomCod[elim] = 
    smcf.iso_smcf_Obj_HomDom_if_Obj_HomCod
  and iso_cf_Arr_HomDom_if_Arr_HomCod[elim] = 
    smcf.iso_smcf_Arr_HomDom_if_Arr_HomCod
  and iso_cf_ObjMap_eqE[elim] = smcf.iso_smcf_ObjMap_eqE
  and iso_cf_ArrMap_eqE[elim] = smcf.iso_smcf_ArrMap_eqE

end

sublocale is_iso_functor \<subseteq> is_ff_functor 
proof(intro is_ff_functorI)
  interpret is_iso_semifunctor \<alpha> \<open>cat_smc \<AA>\<close> \<open>cat_smc \<BB>\<close> \<open>cf_smcf \<FF>\<close>
    by (rule iso_cf_is_iso_semifunctor)
  show "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>" by unfold_locales
  show "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>" by unfold_locales
qed

lemmas (in is_iso_functor) iso_cf_is_ff_functor = is_ff_functor_axioms
lemmas [cf_cs_intros] = is_iso_functor.iso_cf_is_ff_functor


subsubsection\<open>Opposite isomorphism of categories\<close>
 
lemma (in is_iso_functor) is_iso_functor_op: 
  "op_cf \<FF> : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> op_cat \<BB>"   
  by (rule is_iso_functorI, unfold slicing_simps slicing_commute[symmetric]) 
   (simp_all add: cat_op_intros smc_op_intros slicing_intros)

lemma (in is_iso_functor) is_iso_functor_op': 
  assumes "\<AA>' = op_cat \<AA>" and "\<BB>' = op_cat \<BB>"
  shows "op_cf \<FF> : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> op_cat \<BB>"   
  unfolding assms by (rule is_iso_functor_op)

lemmas is_iso_functor_op[cat_op_intros] = 
  is_iso_functor.is_iso_functor_op'


subsubsection\<open>
The composition of isomorphisms of categories is an isomorphism of categories
\<close>

lemma cf_comp_is_iso_functor[cf_cs_intros]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_iso_functorI)
  interpret \<FF>: is_iso_functor \<alpha> \<AA> \<BB> \<FF> using assms by auto
  interpret \<GG>: is_iso_functor \<alpha> \<BB> \<CC> \<GG> using assms by auto
  from \<FF>.is_functor_axioms \<GG>.is_functor_axioms show "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    by (cs_concl cs_intro: cat_cs_intros)
  show "cf_smcf (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> cat_smc \<CC>"
    unfolding slicing_commute[symmetric] 
    by (cs_concl cs_intro: smcf_cs_intros slicing_intros)
qed



subsection\<open>Inverse functor\<close>

abbreviation (input) inv_cf :: "V \<Rightarrow> V"
  where "inv_cf \<equiv> inv_dghm"


text\<open>Slicing.\<close>

lemma dghm_inv_semifunctor[slicing_commute]: 
  "inv_smcf (cf_smcf \<FF>) = cf_smcf (inv_cf \<FF>)"
  unfolding cf_smcf_def inv_dghm_def dghm_field_simps 
  by (simp_all add: nat_omega_simps)

context is_iso_functor
begin

interpretation smcf: is_iso_semifunctor \<alpha> \<open>cat_smc \<AA>\<close> \<open>cat_smc \<BB>\<close> \<open>cf_smcf \<FF>\<close>
  by (rule iso_cf_is_iso_semifunctor) 

lemmas_with [unfolded slicing_simps slicing_commute]:
  inv_cf_ObjMap_v11 = smcf.inv_smcf_ObjMap_v11
  and inv_cf_ObjMap_vdomain = smcf.inv_smcf_ObjMap_vdomain
  and inv_cf_ObjMap_app = smcf.inv_smcf_ObjMap_app
  and inv_cf_ObjMap_vrange = smcf.inv_smcf_ObjMap_vrange
  and inv_cf_ArrMap_v11 = smcf.inv_smcf_ArrMap_v11
  and inv_cf_ArrMap_vdomain = smcf.inv_smcf_ArrMap_vdomain
  and inv_cf_ArrMap_app = smcf.inv_smcf_ArrMap_app
  and inv_cf_ArrMap_vrange = smcf.inv_smcf_ArrMap_vrange
  and iso_cf_ObjMap_inv_cf_ObjMap_app =
    smcf.iso_smcf_ObjMap_inv_smcf_ObjMap_app
  and iso_cf_ArrMap_inv_cf_ArrMap_app = 
    smcf.iso_smcf_ArrMap_inv_smcf_ArrMap_app
  and iso_cf_HomDom_is_arr_conv = smcf.iso_smcf_HomDom_is_arr_conv
  and iso_cf_HomCod_is_arr_conv = smcf.iso_smcf_HomCod_is_arr_conv

end



subsection\<open>An isomorphism of categories is an isomorphism in the category \<open>CAT\<close>\<close>

lemma is_arr_isomorphism_is_iso_functor:
  \<comment>\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> = cf_id \<AA>"
    and "\<FF> \<circ>\<^sub>C\<^sub>F \<GG> = cf_id \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<FF>: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<BB> \<AA> \<GG> by (rule assms(2))
  show ?thesis
  proof(rule is_iso_functorI)
    have \<GG>\<FF>\<AA>: "cf_smcf \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F cf_smcf \<FF> = smcf_id (cat_smc \<AA>)"
      by (simp add: assms(3) cf_smcf_cf_id cf_smcf_smcf_comp)
    have \<FF>\<GG>\<BB>: "cf_smcf \<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F cf_smcf \<GG> = smcf_id (cat_smc \<BB>)"
      by (simp add: assms(4) cf_smcf_cf_id cf_smcf_smcf_comp)
    from \<FF>.cf_is_semifunctor \<GG>.cf_is_semifunctor \<GG>\<FF>\<AA> \<FF>\<GG>\<BB> show 
      "cf_smcf \<FF> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> cat_smc \<BB>" 
      by (rule is_arr_isomorphism_is_iso_semifunctor)
  qed (auto simp: cat_cs_intros)
qed

lemma is_iso_functor_is_arr_isomorphism:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  shows [cf_cs_intros]: "inv_cf \<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<AA>"
    and "inv_cf \<FF> \<circ>\<^sub>C\<^sub>F \<FF> = cf_id \<AA>"
    and "\<FF> \<circ>\<^sub>C\<^sub>F inv_cf \<FF> = cf_id \<BB>"
proof-

  let ?\<GG> = "inv_cf \<FF>"

  interpret is_iso_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(1))

  show \<GG>: "?\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<AA>"
  proof(intro is_iso_functorI is_functorI, unfold inv_dghm_components)
    show "vfsequence ?\<GG>" by (simp add: inv_dghm_def)
    show "vcard ?\<GG> = 4\<^sub>\<nat>"
      unfolding inv_dghm_def by (simp add: nat_omega_simps)
    show "cf_smcf ?\<GG> : cat_smc \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<AA>"
      by 
        (
          metis 
            dghm_inv_semifunctor 
            iso_cf_is_iso_semifunctor 
            is_iso_semifunctor_def 
            is_iso_semifunctor_is_arr_isomorphism(1)
        ) 
    show "cf_smcf ?\<GG> : cat_smc \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> cat_smc \<AA>"
      by 
        (
          metis 
            dghm_inv_semifunctor 
            iso_cf_is_iso_semifunctor 
            is_iso_semifunctor_is_arr_isomorphism(1)
        )
    fix c assume prems: "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    from prems show "(\<FF>\<lparr>ArrMap\<rparr>)\<inverse>\<^sub>\<circ>\<lparr>\<BB>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<AA>\<lparr>CId\<rparr>\<lparr>(\<FF>\<lparr>ObjMap\<rparr>)\<inverse>\<^sub>\<circ>\<lparr>c\<rparr>\<rparr>"
      by (intro v11.v11_vconverse_app)
        (
           cs_concl 
            cs_intro: cat_cs_intros V_cs_intros
            cs_simp: V_cs_simps cat_cs_simps
         )+
  qed (simp_all add: cat_cs_simps cat_cs_intros)

  show "?\<GG> \<circ>\<^sub>C\<^sub>F \<FF> = cf_id \<AA>"
  proof(rule cf_eqI, unfold dghm_comp_components inv_dghm_components)
    from \<GG> is_functor_axioms show "?\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
      by (blast intro: cat_cs_intros)
  qed 
    (
      simp_all add: 
        HomDom.cat_cf_id_is_functor
        ObjMap.v11_vcomp_vconverse 
        ArrMap.v11_vcomp_vconverse 
        dghm_id_components
    )

  show "\<FF> \<circ>\<^sub>C\<^sub>F ?\<GG> = cf_id \<BB>"
  proof(rule cf_eqI, unfold dghm_comp_components inv_dghm_components)
    from \<GG> is_functor_axioms show "\<FF> \<circ>\<^sub>C\<^sub>F ?\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
      by (blast intro: cat_cs_intros)
    show "cf_id \<BB> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by (simp add: HomCod.cat_cf_id_is_functor)
  qed 
    (
      simp_all add:
        ObjMap.v11_vcomp_vconverse' 
        ArrMap.v11_vcomp_vconverse' 
        dghm_id_components
    )

qed


subsubsection\<open>An identity functor is an isomorphism of categories\<close>

lemma (in category) cat_cf_id_is_iso_functor: "cf_id \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<CC>"
  by (rule is_iso_functorI, unfold slicing_commute[symmetric])
    (
      simp_all add: 
        cat_cf_id_is_functor
        semicategory.smc_smcf_id_is_iso_semifunctor
        cat_semicategory
    )



subsection\<open>Isomorphic categories\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}).\<close>

locale iso_category = L: category \<alpha> \<AA> + R: category \<alpha> \<BB> for \<alpha> \<AA> \<BB> +
  assumes iso_cat_is_iso_functor: "\<exists>\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"

notation iso_category (infixl "\<approx>\<^sub>C\<index>" 50)


text\<open>Rules.\<close>

lemma iso_categoryI:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "\<AA> \<approx>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms unfolding iso_category_def iso_category_axioms_def by auto

lemma iso_categoryD[dest]:
  assumes "\<AA> \<approx>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "\<exists>\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>" 
  using assms unfolding iso_category_def iso_category_axioms_def by simp_all

lemma iso_categoryE[elim]:
  assumes "\<AA> \<approx>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
  obtains \<FF> where "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by auto


text\<open>Isomorphic categories are isomorphic semicategories.\<close>

lemma (in iso_category) iso_cat_iso_semicategory: 
  "cat_smc \<AA> \<approx>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<BB>"
  using iso_cat_is_iso_functor 
  by (auto intro: slicing_intros iso_semicategoryI)


subsubsection\<open>A category isomorphism is an equivalence relation\<close>

lemma iso_category_refl: 
  assumes "category \<alpha> \<AA>" 
  shows "\<AA> \<approx>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
proof(rule iso_categoryI[of _ _ _ \<open>cf_id \<AA>\<close>])
  interpret category \<alpha> \<AA> by (rule assms)
  show "cf_id \<AA> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<AA>" by (simp add: cat_cf_id_is_iso_functor)
qed                                        

lemma iso_category_sym[sym]:
  assumes "\<AA> \<approx>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "\<BB> \<approx>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
proof-
  interpret iso_category \<alpha> \<AA> \<BB> by (rule assms)
  from iso_cat_is_iso_functor obtain \<FF> where "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>" by clarsimp
  from is_iso_functor_is_arr_isomorphism(1)[OF this] show ?thesis 
    by (auto intro: iso_categoryI)
qed

lemma iso_category_trans[trans]:
  assumes "\<AA> \<approx>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<BB> \<approx>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
  shows "\<AA> \<approx>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret L: iso_category \<alpha> \<AA> \<BB> by (rule assms(1))
  interpret R: iso_category \<alpha> \<BB> \<CC> by (rule assms(2))
  from L.iso_cat_is_iso_functor R.iso_cat_is_iso_functor show ?thesis 
    by (auto intro: iso_categoryI is_iso_functorI cf_comp_is_iso_functor)
qed

text\<open>\newpage\<close>

end