(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Natural transformation\<close>
theory CZH_ECAT_NTCF
  imports 
    CZH_Foundations.CZH_SMC_NTSMCF
    CZH_ECAT_Functor
begin



subsection\<open>Background\<close>

named_theorems ntcf_cs_simps
named_theorems ntcf_cs_intros

lemmas [cat_cs_simps] = dg_shared_cs_simps
lemmas [cat_cs_intros] = dg_shared_cs_intros


subsubsection\<open>Slicing\<close>

definition ntcf_ntsmcf :: "V \<Rightarrow> V"
  where "ntcf_ntsmcf \<NN> =
    [
      \<NN>\<lparr>NTMap\<rparr>,
      cf_smcf (\<NN>\<lparr>NTDom\<rparr>),
      cf_smcf (\<NN>\<lparr>NTCod\<rparr>),
      cat_smc (\<NN>\<lparr>NTDGDom\<rparr>),
      cat_smc (\<NN>\<lparr>NTDGCod\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma ntcf_ntsmcf_components:
  shows [slicing_simps]: "ntcf_ntsmcf \<NN>\<lparr>NTMap\<rparr> = \<NN>\<lparr>NTMap\<rparr>"
    and [slicing_commute]: "ntcf_ntsmcf \<NN>\<lparr>NTDom\<rparr> = cf_smcf (\<NN>\<lparr>NTDom\<rparr>)"
    and [slicing_commute]: "ntcf_ntsmcf \<NN>\<lparr>NTCod\<rparr> = cf_smcf (\<NN>\<lparr>NTCod\<rparr>)"
    and [slicing_commute]: "ntcf_ntsmcf \<NN>\<lparr>NTDGDom\<rparr> = cat_smc (\<NN>\<lparr>NTDGDom\<rparr>)"
    and [slicing_commute]: "ntcf_ntsmcf \<NN>\<lparr>NTDGCod\<rparr> = cat_smc (\<NN>\<lparr>NTDGCod\<rparr>)"
  unfolding ntcf_ntsmcf_def nt_field_simps by (auto simp: nat_omega_simps)



subsection\<open>Definition and elementary properties\<close>


text\<open>
The definition of a natural transformation that is used in this work is
is similar to the definition that can be found in Chapter I-4 in 
\cite{mac_lane_categories_2010}.
\<close>

locale is_ntcf = 
  \<Z> \<alpha> + 
  vfsequence \<NN> + 
  NTDom: is_functor \<alpha> \<AA> \<BB> \<FF> + 
  NTCod: is_functor \<alpha> \<AA> \<BB> \<GG>
  for \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> +
  assumes ntcf_length[cat_cs_simps]: "vcard \<NN> = 5\<^sub>\<nat>"  
    and ntcf_is_ntsmcf[slicing_intros]: "ntcf_ntsmcf \<NN> :
      cf_smcf \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F cf_smcf \<GG> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<BB>"
    and ntcf_NTDom[cat_cs_simps]: "\<NN>\<lparr>NTDom\<rparr> = \<FF>"
    and ntcf_NTCod[cat_cs_simps]: "\<NN>\<lparr>NTCod\<rparr> = \<GG>"
    and ntcf_NTDGDom[cat_cs_simps]: "\<NN>\<lparr>NTDGDom\<rparr> = \<AA>"
    and ntcf_NTDGCod[cat_cs_simps]: "\<NN>\<lparr>NTDGCod\<rparr> = \<BB>"

syntax "_is_ntcf" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<^sub>C\<^sub>F _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>"

abbreviation all_ntcfs :: "V \<Rightarrow> V"
  where "all_ntcfs \<alpha> \<equiv> set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation ntcfs :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "ntcfs \<alpha> \<AA> \<BB> \<equiv> set {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation these_ntcfs :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "these_ntcfs \<alpha> \<AA> \<BB> \<FF> \<GG> \<equiv> set {\<NN>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"

lemmas [cat_cs_simps] = 
  is_ntcf.ntcf_length
  is_ntcf.ntcf_NTDom
  is_ntcf.ntcf_NTCod
  is_ntcf.ntcf_NTDGDom
  is_ntcf.ntcf_NTDGCod

lemma (in is_ntcf) ntcf_is_ntsmcf':
  assumes "\<FF>' = cf_smcf \<FF>"
    and "\<GG>' = cf_smcf \<GG>"
    and "\<AA>' = cat_smc \<AA>"
    and "\<BB>' = cat_smc \<BB>"
  shows "ntcf_ntsmcf \<NN> : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms(1-4) by (rule ntcf_is_ntsmcf)

lemmas [slicing_intros] = is_ntcf.ntcf_is_ntsmcf'


text\<open>Rules.\<close>

lemma (in is_ntcf) is_ntcf_axioms'[cat_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>" and "\<FF>' = \<FF>" and "\<GG>' = \<GG>"
  shows "\<NN> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_ntcf_axioms)

mk_ide rf is_ntcf_def[unfolded is_ntcf_axioms_def]
  |intro is_ntcfI|
  |dest is_ntcfD[dest]|
  |elim is_ntcfE[elim]|

lemmas [cat_cs_intros] = 
  is_ntcfD(3,4)

lemma is_ntcfI':
  assumes "\<Z> \<alpha>"
    and "vfsequence \<NN>"
    and "vcard \<NN> = 5\<^sub>\<nat>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN>\<lparr>NTDom\<rparr> = \<FF>"
    and "\<NN>\<lparr>NTCod\<rparr> = \<GG>"
    and "\<NN>\<lparr>NTDGDom\<rparr> = \<AA>"
    and "\<NN>\<lparr>NTDGCod\<rparr> = \<BB>"
    and "vsv (\<NN>\<lparr>NTMap\<rparr>)"
    and "\<D>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    and "\<And>a. a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<Longrightarrow> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "\<And>a b f. f : a \<mapsto>\<^bsub>\<AA>\<^esub> b \<Longrightarrow>
      \<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  by (intro is_ntcfI is_ntsmcfI', unfold ntcf_ntsmcf_components slicing_simps)
    (
      simp_all add: 
        assms nat_omega_simps 
        ntcf_ntsmcf_def  
        is_functorD(6)[OF assms(4)] 
        is_functorD(6)[OF assms(5)]
    )

lemma is_ntcfD':
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<Z> \<alpha>"
    and "vfsequence \<NN>"
    and "vcard \<NN> = 5\<^sub>\<nat>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
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
        is_ntcfD(2-10)[OF assms] 
        is_ntsmcfD'[OF is_ntcfD(6)[OF assms], unfolded slicing_simps]
    )

lemma is_ntcfE':
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  obtains "\<Z> \<alpha>"
    and "vfsequence \<NN>"
    and "vcard \<NN> = 5\<^sub>\<nat>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN>\<lparr>NTDom\<rparr> = \<FF>"
    and "\<NN>\<lparr>NTCod\<rparr> = \<GG>"
    and "\<NN>\<lparr>NTDGDom\<rparr> = \<AA>"
    and "\<NN>\<lparr>NTDGCod\<rparr> = \<BB>"
    and "vsv (\<NN>\<lparr>NTMap\<rparr>)"
    and "\<D>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    and "\<And>a. a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<Longrightarrow> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "\<And>a b f. f : a \<mapsto>\<^bsub>\<AA>\<^esub> b \<Longrightarrow>
      \<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
  using assms by (simp add: is_ntcfD')


text\<open>Slicing.\<close>

context is_ntcf
begin

interpretation ntsmcf: 
  is_ntsmcf \<alpha> \<open>cat_smc \<AA>\<close> \<open>cat_smc \<BB>\<close> \<open>cf_smcf \<FF>\<close> \<open>cf_smcf \<GG>\<close> \<open>ntcf_ntsmcf \<NN>\<close>
  by (rule ntcf_is_ntsmcf)

lemmas_with [unfolded slicing_simps]:
  ntcf_NTMap_vsv = ntsmcf.ntsmcf_NTMap_vsv
  and ntcf_NTMap_vdomain[cat_cs_simps] = ntsmcf.ntsmcf_NTMap_vdomain
  and ntcf_NTMap_is_arr = ntsmcf.ntsmcf_NTMap_is_arr
  and ntcf_NTMap_is_arr'[cat_cs_intros] = ntsmcf.ntsmcf_NTMap_is_arr'

sublocale NTMap: vsv \<open>\<NN>\<lparr>NTMap\<rparr>\<close>
  rewrites "\<D>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
  by (rule ntcf_NTMap_vsv) (simp add: cat_cs_simps)

lemmas_with [unfolded slicing_simps]:
  ntcf_NTMap_app_in_Arr[cat_cs_intros] = ntsmcf.ntsmcf_NTMap_app_in_Arr
  and ntcf_NTMap_vrange_vifunion = ntsmcf.ntsmcf_NTMap_vrange_vifunion
  and ntcf_NTMap_vrange = ntsmcf.ntsmcf_NTMap_vrange
  and ntcf_NTMap_vsubset_Vset = ntsmcf.ntsmcf_NTMap_vsubset_Vset
  and ntcf_NTMap_in_Vset = ntsmcf.ntsmcf_NTMap_in_Vset
  and ntcf_is_ntsmcf_if_ge_Limit = ntsmcf.ntsmcf_is_ntsmcf_if_ge_Limit

lemmas_with [unfolded slicing_simps]:
  ntcf_Comp_commute[cat_cs_intros] = ntsmcf.ntsmcf_Comp_commute
  and ntcf_Comp_commute' = ntsmcf.ntsmcf_Comp_commute'
  and ntcf_Comp_commute'' = ntsmcf.ntsmcf_Comp_commute''

end

lemmas [cat_cs_simps] = is_ntcf.ntcf_NTMap_vdomain

lemmas [cat_cs_intros] = 
  is_ntcf.ntcf_NTMap_is_arr'
  ntsmcf_hcomp_NTMap_vsv


text\<open>Elementary properties.\<close>

lemma ntcf_eqI:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN>' : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
    and "\<NN>\<lparr>NTMap\<rparr> = \<NN>'\<lparr>NTMap\<rparr>"
    and "\<FF> = \<FF>'"
    and "\<GG> = \<GG>'"
    and "\<AA> = \<AA>'"
    and "\<BB> = \<BB>'"
  shows "\<NN> = \<NN>'"
proof-
  interpret L: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret R: is_ntcf \<alpha> \<AA>' \<BB>' \<FF>' \<GG>' \<NN>' by (rule assms(2))
  show ?thesis
  proof(rule vsv_eqI)
    have dom: "\<D>\<^sub>\<circ> \<NN> = 5\<^sub>\<nat>" by (cs_concl cs_simp: cat_cs_simps V_cs_simps)
    show "\<D>\<^sub>\<circ> \<NN> = \<D>\<^sub>\<circ> \<NN>'" by (cs_concl cs_simp: cat_cs_simps V_cs_simps)
    from assms(4-7) have sup: 
      "\<NN>\<lparr>NTDom\<rparr> = \<NN>'\<lparr>NTDom\<rparr>" "\<NN>\<lparr>NTCod\<rparr> = \<NN>'\<lparr>NTCod\<rparr>" 
      "\<NN>\<lparr>NTDGDom\<rparr> = \<NN>'\<lparr>NTDGDom\<rparr>" "\<NN>\<lparr>NTDGCod\<rparr> = \<NN>'\<lparr>NTDGCod\<rparr>" 
      by (simp_all add: cat_cs_simps)
    show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<NN> \<Longrightarrow> \<NN>\<lparr>a\<rparr> = \<NN>'\<lparr>a\<rparr>" for a
      by (unfold dom, elim_in_numeral, insert assms(3) sup) 
        (auto simp: nt_field_simps)
  qed auto
qed

lemma ntcf_ntsmcf_eqI:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN>' : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
    and "\<FF> = \<FF>'"
    and "\<GG> = \<GG>'"
    and "\<AA> = \<AA>'"
    and "\<BB> = \<BB>'"
    and "ntcf_ntsmcf \<NN> = ntcf_ntsmcf \<NN>'"
  shows "\<NN> = \<NN>'"
proof(rule ntcf_eqI[of \<alpha>])
  from assms(7) have "ntcf_ntsmcf \<NN>\<lparr>NTMap\<rparr> = ntcf_ntsmcf \<NN>'\<lparr>NTMap\<rparr>" by simp
  then show "\<NN>\<lparr>NTMap\<rparr> = \<NN>'\<lparr>NTMap\<rparr>" unfolding slicing_simps by simp_all
  from assms(3-6) show "\<FF> = \<FF>'" "\<GG> = \<GG>'" "\<AA> = \<AA>'" "\<BB> = \<BB>'" by simp_all
qed (auto simp: assms(1,2))

lemma (in is_ntcf) ntcf_def:
  "\<NN> = [\<NN>\<lparr>NTMap\<rparr>, \<NN>\<lparr>NTDom\<rparr>, \<NN>\<lparr>NTCod\<rparr>, \<NN>\<lparr>NTDGDom\<rparr>, \<NN>\<lparr>NTDGCod\<rparr>]\<^sub>\<circ>"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> \<NN> = 5\<^sub>\<nat>" by (cs_concl cs_simp: cat_cs_simps V_cs_simps)
  have dom_rhs:
    "\<D>\<^sub>\<circ> [\<NN>\<lparr>NTMap\<rparr>, \<NN>\<lparr>NTDGDom\<rparr>, \<NN>\<lparr>NTDGCod\<rparr>, \<NN>\<lparr>NTDom\<rparr>, \<NN>\<lparr>NTCod\<rparr>]\<^sub>\<circ> = 5\<^sub>\<nat>"
    by (simp add: nat_omega_simps)
  then show 
    "\<D>\<^sub>\<circ> \<NN> = \<D>\<^sub>\<circ> [\<NN>\<lparr>NTMap\<rparr>, \<NN>\<lparr>NTDom\<rparr>, \<NN>\<lparr>NTCod\<rparr>, \<NN>\<lparr>NTDGDom\<rparr>, \<NN>\<lparr>NTDGCod\<rparr>]\<^sub>\<circ>"
    unfolding dom_lhs dom_rhs by (simp add: nat_omega_simps)
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<NN> \<Longrightarrow>
    \<NN>\<lparr>a\<rparr> = [\<NN>\<lparr>NTMap\<rparr>, \<NN>\<lparr>NTDom\<rparr>, \<NN>\<lparr>NTCod\<rparr>, \<NN>\<lparr>NTDGDom\<rparr>, \<NN>\<lparr>NTDGCod\<rparr>]\<^sub>\<circ>\<lparr>a\<rparr>" 
    for a
    by (unfold dom_lhs, elim_in_numeral, unfold nt_field_simps)
      (simp_all add: nat_omega_simps)
qed (auto simp: vsv_axioms)

lemma (in is_ntcf) ntcf_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"  
  shows "\<NN> \<in>\<^sub>\<circ> Vset \<beta>"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  note [cat_cs_intros] = 
    ntcf_NTMap_in_Vset
    NTDom.cf_in_Vset
    NTCod.cf_in_Vset
    NTDom.HomDom.cat_in_Vset
    NTDom.HomCod.cat_in_Vset
  from assms(2) show ?thesis
    by (subst ntcf_def) 
      (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros V_cs_intros)
qed

lemma (in is_ntcf) ntcf_is_ntcf_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> \<BB>"
proof(intro is_ntcfI)
  show "ntcf_ntsmcf \<NN> :
    cf_smcf \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F cf_smcf \<GG> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<beta>\<^esub> cat_smc \<BB>"
    by (rule is_ntsmcf.ntsmcf_is_ntsmcf_if_ge_Limit[OF ntcf_is_ntsmcf assms])
qed 
  (
    cs_concl 
      cs_simp: cat_cs_simps 
      cs_intro:
        V_cs_intros
        assms 
        NTDom.cf_is_functor_if_ge_Limit
        NTCod.cf_is_functor_if_ge_Limit
   )+

lemma small_all_ntcfs[simp]:
  "small {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(cases \<open>\<Z> \<alpha>\<close>)
  case True
  from is_ntcf.ntcf_in_Vset show ?thesis
    by (intro down[of _ \<open>Vset (\<alpha> + \<omega>)\<close>])
      (auto simp: True \<Z>.\<Z>_Limit_\<alpha>\<omega> \<Z>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>.intro \<Z>.\<Z>_\<alpha>_\<alpha>\<omega>)
next
  case False
  then have "{\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>} = {}" by auto
  then show ?thesis by simp
qed

lemma small_ntcfs[simp]: "small {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"
  by (rule down[of _ \<open>set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}\<close>]) auto

lemma small_these_ntcfs[simp]: "small {\<NN>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"
  by (rule down[of _ \<open>set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}\<close>]) auto


text\<open>Further elementary results.\<close>

lemma these_ntcfs_iff: (*not simp*) 
  "\<NN> \<in>\<^sub>\<circ> these_ntcfs \<alpha> \<AA> \<BB> \<FF> \<GG> \<longleftrightarrow> \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  by auto



subsection\<open>Opposite natural transformation\<close>


text\<open>See section 1.5 in \cite{bodo_categories_1970}.\<close>

definition op_ntcf :: "V \<Rightarrow> V"
  where "op_ntcf \<NN> = 
    [
      \<NN>\<lparr>NTMap\<rparr>, 
      op_cf (\<NN>\<lparr>NTCod\<rparr>), 
      op_cf (\<NN>\<lparr>NTDom\<rparr>), 
      op_cat (\<NN>\<lparr>NTDGDom\<rparr>), 
      op_cat (\<NN>\<lparr>NTDGCod\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma op_ntcf_components[cat_op_simps]:
  shows "op_ntcf \<NN>\<lparr>NTMap\<rparr> = \<NN>\<lparr>NTMap\<rparr>"
    and "op_ntcf \<NN>\<lparr>NTDom\<rparr> = op_cf (\<NN>\<lparr>NTCod\<rparr>)"
    and "op_ntcf \<NN>\<lparr>NTCod\<rparr> = op_cf (\<NN>\<lparr>NTDom\<rparr>)"
    and "op_ntcf \<NN>\<lparr>NTDGDom\<rparr> = op_cat (\<NN>\<lparr>NTDGDom\<rparr>)"
    and "op_ntcf \<NN>\<lparr>NTDGCod\<rparr> = op_cat (\<NN>\<lparr>NTDGCod\<rparr>)"
  unfolding op_ntcf_def nt_field_simps by (auto simp: nat_omega_simps)


text\<open>Slicing.\<close>

lemma ntcf_ntsmcf_op_ntcf[slicing_commute]: 
  "op_ntsmcf (ntcf_ntsmcf \<NN>) = ntcf_ntsmcf (op_ntcf \<NN>)"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> (op_ntsmcf (ntcf_ntsmcf \<NN>)) = 5\<^sub>\<nat>"
    unfolding op_ntsmcf_def by (auto simp: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (ntcf_ntsmcf (op_ntcf \<NN>)) = 5\<^sub>\<nat>"
    unfolding ntcf_ntsmcf_def by (auto simp: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (op_ntsmcf (ntcf_ntsmcf \<NN>)) = \<D>\<^sub>\<circ> (ntcf_ntsmcf (op_ntcf \<NN>))"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (op_ntsmcf (ntcf_ntsmcf \<NN>)) \<Longrightarrow> 
    op_ntsmcf (ntcf_ntsmcf \<NN>)\<lparr>a\<rparr> = ntcf_ntsmcf (op_ntcf \<NN>)\<lparr>a\<rparr>"
    for a
    by 
      (
        unfold dom_lhs,
        elim_in_numeral,
        unfold nt_field_simps ntcf_ntsmcf_def op_ntcf_def op_ntsmcf_def
      )
      (auto simp: nat_omega_simps slicing_commute[symmetric])
qed (auto simp: ntcf_ntsmcf_def op_ntsmcf_def)


text\<open>Elementary properties.\<close>

lemma op_ntcf_vsv[cat_op_intros]: "vsv (op_ntcf \<FF>)" 
  unfolding op_ntcf_def by auto


subsubsection\<open>Further properties\<close>

lemma (in is_ntcf) is_ntcf_op: 
  "op_ntcf \<NN> : op_cf \<GG> \<mapsto>\<^sub>C\<^sub>F op_cf \<FF> : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<BB>"
proof(rule is_ntcfI, unfold cat_op_simps)
  show "vfsequence (op_ntcf \<NN>)" by (simp add: op_ntcf_def)
  show "vcard (op_ntcf \<NN>) = 5\<^sub>\<nat>" by (simp add: op_ntcf_def nat_omega_simps)
qed
  (
    use is_ntcf_axioms in
    \<open>
      cs_concl 
        cs_simp: cat_cs_simps slicing_commute[symmetric]
        cs_intro: cat_cs_intros cat_op_intros smc_op_intros slicing_intros
    \<close>
  )+

lemma (in is_ntcf) is_ntcf_op'[cat_op_intros]:
  assumes "\<GG>' = op_cf \<GG>"
    and "\<FF>' = op_cf \<FF>"
    and "\<AA>' = op_cat \<AA>"
    and "\<BB>' = op_cat \<BB>"
  shows "op_ntcf \<NN> : \<GG>' \<mapsto>\<^sub>C\<^sub>F \<FF>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule is_ntcf_op)

lemmas [cat_op_intros] = is_ntcf.is_ntcf_op'

lemma (in is_ntcf) ntcf_op_ntcf_op_ntcf[cat_op_simps]: 
  "op_ntcf (op_ntcf \<NN>) = \<NN>"
proof(rule ntcf_eqI[of \<alpha> \<AA> \<BB> \<FF> \<GG> _ \<AA> \<BB> \<FF> \<GG>], unfold cat_op_simps)
  interpret op: 
    is_ntcf \<alpha> \<open>op_cat \<AA>\<close> \<open>op_cat \<BB>\<close> \<open>op_cf \<GG>\<close> \<open>op_cf \<FF>\<close> \<open>op_ntcf \<NN>\<close>
    by (rule is_ntcf_op)
  from op.is_ntcf_op show 
    "op_ntcf (op_ntcf \<NN>) : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (simp add: cat_op_simps)
qed (auto simp: cat_cs_intros)

lemmas ntcf_op_ntcf_op_ntcf[cat_op_simps] = 
  is_ntcf.ntcf_op_ntcf_op_ntcf

lemma eq_op_ntcf_iff[cat_op_simps]: 
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<NN>' : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  shows "op_ntcf \<NN> = op_ntcf \<NN>' \<longleftrightarrow> \<NN> = \<NN>'"
proof
  interpret L: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret R: is_ntcf \<alpha> \<AA>' \<BB>' \<FF>' \<GG>' \<NN>' by (rule assms(2))
  assume prems: "op_ntcf \<NN> = op_ntcf \<NN>'"
  show "\<NN> = \<NN>'"
  proof(rule ntcf_eqI[OF assms])
    from prems L.ntcf_op_ntcf_op_ntcf R.ntcf_op_ntcf_op_ntcf show 
      "\<NN>\<lparr>NTMap\<rparr> = \<NN>'\<lparr>NTMap\<rparr>"
      by metis+
    from prems L.ntcf_op_ntcf_op_ntcf R.ntcf_op_ntcf_op_ntcf 
    have "\<NN>\<lparr>NTDom\<rparr> = \<NN>'\<lparr>NTDom\<rparr>" 
      and "\<NN>\<lparr>NTCod\<rparr> = \<NN>'\<lparr>NTCod\<rparr>" 
      and "\<NN>\<lparr>NTDGDom\<rparr> = \<NN>'\<lparr>NTDGDom\<rparr>" 
      and "\<NN>\<lparr>NTDGCod\<rparr> = \<NN>'\<lparr>NTDGCod\<rparr>" 
      by metis+
    then show "\<FF> = \<FF>'" "\<GG> = \<GG>'" "\<AA> = \<AA>'" "\<BB> = \<BB>'" 
      by (auto simp: cat_cs_simps)
  qed
qed auto



subsection\<open>Vertical composition of natural transformations\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter II-4 in \cite{mac_lane_categories_2010}.\<close>

abbreviation (input) ntcf_vcomp :: "V \<Rightarrow> V \<Rightarrow> V" (infixl \<open>\<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<close> 55)
  where "ntcf_vcomp \<equiv> ntsmcf_vcomp"

lemmas [cat_cs_simps] = ntsmcf_vcomp_components(2-5)


text\<open>Slicing.\<close>

lemma ntcf_ntsmcf_ntcf_vcomp[slicing_commute]: 
  "ntcf_ntsmcf \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F ntcf_ntsmcf \<NN> = ntcf_ntsmcf (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)"
  unfolding 
    ntsmcf_vcomp_def ntcf_ntsmcf_def cat_smc_def nt_field_simps dg_field_simps 
  by (simp add: nat_omega_simps)


subsubsection\<open>Natural transformation map\<close>

lemma ntcf_vcomp_NTMap_vdomain[cat_cs_simps]:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
proof-
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> using assms by auto
  show ?thesis
    by 
      (
        rule ntsmcf_vcomp_NTMap_vdomain
          [
            OF \<NN>.ntcf_is_ntsmcf, 
            of \<open>ntcf_ntsmcf \<MM>\<close>,
            unfolded slicing_commute slicing_simps
          ]
      )
qed

lemma ntcf_vcomp_NTMap_app[cat_cs_simps]:
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
  shows "(\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<MM>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
proof-
  interpret \<MM>: is_ntcf \<alpha> \<AA> \<BB> \<GG> \<HH> \<MM> using assms by clarsimp
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> using assms by clarsimp
  show ?thesis
    by 
      (
        rule ntsmcf_vcomp_NTMap_app
          [
            OF \<MM>.ntcf_is_ntsmcf \<NN>.ntcf_is_ntsmcf, 
            unfolded slicing_commute slicing_simps,
            OF assms(3)
          ]
      )
qed

lemma ntcf_vcomp_NTMap_vrange:
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
proof-
  interpret \<MM>: is_ntcf \<alpha> \<AA> \<BB> \<GG> \<HH> \<MM> using assms by auto
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> using assms by auto
  show ?thesis
    by 
      (
        rule 
          ntsmcf_vcomp_NTMap_vrange[
            OF \<MM>.ntcf_is_ntsmcf \<NN>.ntcf_is_ntsmcf, 
            unfolded slicing_simps slicing_commute
          ]
      )
qed


subsubsection\<open>Further properties\<close>

lemma ntcf_vcomp_composable_commute[cat_cs_simps]:
  \<comment>\<open>See Chapter II-4 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and [intro]: "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
  shows 
    "(\<MM>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>) \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = 
      \<HH>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> (\<MM>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)"
proof-
  interpret \<MM>: is_ntcf \<alpha> \<AA> \<BB> \<GG> \<HH> \<MM> by (rule assms(1)) 
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  show ?thesis
    by 
      (
        rule ntsmcf_vcomp_composable_commute[
            OF \<MM>.ntcf_is_ntsmcf \<NN>.ntcf_is_ntsmcf, 
            unfolded slicing_simps,
            OF assms(3)
          ]
      )
qed 

lemma ntcf_vcomp_is_ntcf[cat_cs_intros]:
  \<comment>\<open>see Chapter II-4 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<MM>: is_ntcf \<alpha> \<AA> \<BB> \<GG> \<HH> \<MM> by (rule assms(1))
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  show ?thesis 
  proof(intro is_ntcfI)
    show "vfsequence (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)" by (simp add: ntsmcf_vcomp_def)
    show "vcard (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) = 5\<^sub>\<nat>"
      unfolding ntsmcf_vcomp_def by (simp add: nat_omega_simps)
    show "ntcf_ntsmcf (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) : 
      cf_smcf \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F cf_smcf \<HH> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<BB>"
      by 
        (
          rule ntsmcf_vcomp_is_ntsmcf[
            OF \<MM>.ntcf_is_ntsmcf \<NN>.ntcf_is_ntsmcf, 
            unfolded slicing_simps slicing_commute
            ]
        )
  qed (auto simp: ntsmcf_vcomp_components(1) cat_cs_simps cat_cs_intros)
qed

lemma ntcf_vcomp_assoc[cat_cs_simps]:
  \<comment>\<open>See Chapter II-4 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<LL> : \<HH> \<mapsto>\<^sub>C\<^sub>F \<KK> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "(\<LL> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<MM>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> = \<LL> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)"
proof-
  interpret \<LL>: is_ntcf \<alpha> \<AA> \<BB> \<HH> \<KK> \<LL> by (rule assms(1))
  interpret \<MM>: is_ntcf \<alpha> \<AA> \<BB> \<GG> \<HH> \<MM> by (rule assms(2))
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(3))
  show ?thesis
  proof(rule ntcf_eqI[of \<alpha>])
    from ntsmcf_vcomp_assoc[
        OF \<LL>.ntcf_is_ntsmcf \<MM>.ntcf_is_ntsmcf \<NN>.ntcf_is_ntsmcf,
        unfolded slicing_simps slicing_commute
      ]
    have 
      "ntcf_ntsmcf (\<LL> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr> =
        ntcf_ntsmcf (\<LL> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>"
      by simp
    then show "(\<LL> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr> = (\<LL> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>"
      unfolding slicing_simps .
  qed (auto intro: cat_cs_intros)
qed


subsubsection\<open>
The opposite of the vertical composition of natural transformations
\<close>

lemma op_ntcf_ntcf_vcomp[cat_op_simps]: 
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "op_ntcf (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) = op_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf \<MM>"
proof-
  interpret \<MM>: is_ntcf \<alpha> \<AA> \<BB> \<GG> \<HH> \<MM> using assms(1) by auto
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> using assms(2) by auto
  show ?thesis
  proof(rule sym, rule ntcf_eqI[of \<alpha>])
    from 
      op_ntsmcf_ntsmcf_vcomp
        [
          OF \<MM>.ntcf_is_ntsmcf \<NN>.ntcf_is_ntsmcf, 
          unfolded slicing_simps slicing_commute
        ]
    have "ntcf_ntsmcf (op_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf \<MM>)\<lparr>NTMap\<rparr> = 
      ntcf_ntsmcf (op_ntcf (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>"
      by simp
    then show "(op_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf \<MM>)\<lparr>NTMap\<rparr> = op_ntcf (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>"
      unfolding slicing_simps .
  qed (auto intro: cat_cs_intros cat_op_intros)
qed



subsection\<open>Horizontal composition of natural transformations\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter II-5 in \cite{mac_lane_categories_2010}.\<close>

abbreviation (input) ntcf_hcomp :: "V \<Rightarrow> V \<Rightarrow> V" (infixl \<open>\<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<close> 55)
  where "ntcf_hcomp \<equiv> ntsmcf_hcomp"

lemmas [cat_cs_simps] = ntsmcf_hcomp_components(2-5)


text\<open>Slicing.\<close>

lemma ntcf_ntsmcf_ntcf_hcomp[slicing_commute]: 
  "ntcf_ntsmcf \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F ntcf_ntsmcf \<NN> = ntcf_ntsmcf (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)"
proof(rule vsv_eqI)
  show "vsv (ntcf_ntsmcf \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F ntcf_ntsmcf \<NN>)"
    unfolding ntsmcf_hcomp_def by auto
  show "vsv (ntcf_ntsmcf (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>))" unfolding ntcf_ntsmcf_def by auto
  have dom_lhs: 
    "\<D>\<^sub>\<circ> (ntcf_ntsmcf \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F ntcf_ntsmcf \<NN>) = 5\<^sub>\<nat>" 
    unfolding ntsmcf_hcomp_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (ntcf_ntsmcf (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)) = 5\<^sub>\<nat>"
    unfolding ntcf_ntsmcf_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (ntcf_ntsmcf \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F ntcf_ntsmcf \<NN>) = 
    \<D>\<^sub>\<circ> (ntcf_ntsmcf (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>))"
    unfolding dom_lhs dom_rhs ..
  fix a assume "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (ntcf_ntsmcf \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F ntcf_ntsmcf \<NN>)"
  then show 
    "(ntcf_ntsmcf \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F ntcf_ntsmcf \<NN>)\<lparr>a\<rparr> = ntcf_ntsmcf (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>a\<rparr>"
    unfolding dom_lhs
    by (elim_in_numeral; fold nt_field_simps) 
      (simp_all add: ntsmcf_hcomp_components slicing_simps slicing_commute)
qed


subsubsection\<open>Natural transformation map\<close>

lemma ntcf_hcomp_NTMap_vdomain[cat_cs_simps]: 
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
proof-
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  show ?thesis unfolding ntsmcf_hcomp_components by (simp add: cat_cs_simps)
qed

lemma ntcf_hcomp_NTMap_app[cat_cs_simps]:
  assumes "\<MM> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
  shows "(\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
    \<GG>'\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<MM>\<lparr>NTMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
proof-
  interpret \<MM>: is_ntcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<MM> by (rule assms(1))
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  from assms(3) show ?thesis 
    unfolding ntsmcf_hcomp_components by (simp add: cat_cs_simps)
qed

lemma ntcf_hcomp_NTMap_vrange:
  assumes "\<MM> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof-
  interpret \<MM>: is_ntcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<MM> by (rule assms(1))
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  show ?thesis
    by 
      (
        rule ntsmcf_hcomp_NTMap_vrange[
          OF \<MM>.ntcf_is_ntsmcf \<NN>.ntcf_is_ntsmcf, 
          unfolded slicing_simps slicing_commute
          ]
      )
qed


subsubsection\<open>Further properties\<close>

lemma ntcf_hcomp_composable_commute:
  \<comment>\<open>See Chapter II-5 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<MM> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" 
  shows 
    "(\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<FF>' \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = 
      (\<GG>' \<circ>\<^sub>C\<^sub>F \<GG>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
    (is \<open>?\<MM>\<NN>b \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<FF>'\<FF>f = ?\<GG>'\<GG>f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<MM>\<NN>a\<close>)
proof-
  interpret \<MM>: is_ntcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<MM> by (rule assms(1))
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  show ?thesis
    by 
      (
        rule ntsmcf_hcomp_composable_commute[
          OF \<MM>.ntcf_is_ntsmcf \<NN>.ntcf_is_ntsmcf,
          unfolded slicing_simps slicing_commute, 
          OF assms(3)
          ]
      )
qed

lemma ntcf_hcomp_is_ntcf:
  \<comment>\<open>See Chapter II-5 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<MM> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<FF>' \<circ>\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG>' \<circ>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<MM>: is_ntcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<MM> by (rule assms(1))
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  show ?thesis
  proof(intro is_ntcfI) 
    show "vfsequence (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)"
      unfolding ntsmcf_hcomp_def by (simp add: nat_omega_simps)
    show "vcard (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) = 5\<^sub>\<nat>"
      unfolding ntsmcf_hcomp_def by (simp add: nat_omega_simps)
    show "ntcf_ntsmcf (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) : 
      cf_smcf (\<FF>' \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>) \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F cf_smcf (\<GG>' \<circ>\<^sub>C\<^sub>F \<GG>) : 
      cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<CC>"
      by 
        (
          rule ntsmcf_hcomp_is_ntsmcf[
            OF \<MM>.ntcf_is_ntsmcf \<NN>.ntcf_is_ntsmcf, 
            unfolded slicing_simps slicing_commute
            ]
        )
  qed (auto simp: ntsmcf_hcomp_components(1) cat_cs_simps intro: cat_cs_intros)
qed

lemma ntcf_hcomp_is_ntcf'[cat_cs_intros]:
  assumes "\<MM> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<SS> = \<FF>' \<circ>\<^sub>C\<^sub>F \<FF>"
    and "\<SS>' = \<GG>' \<circ>\<^sub>C\<^sub>F \<GG>"
  shows "\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1,2) unfolding assms(3,4) by (rule ntcf_hcomp_is_ntcf)

lemma ntcf_hcomp_associativ[cat_cs_simps]: 
  assumes "\<LL> : \<FF>'' \<mapsto>\<^sub>C\<^sub>F \<GG>'' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" 
    and "\<MM> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "(\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<MM>) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> = \<LL> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)"
proof-
  interpret \<LL>: is_ntcf \<alpha> \<CC> \<DD> \<FF>'' \<GG>'' \<LL> by (rule assms(1))
  interpret \<MM>: is_ntcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<MM> by (rule assms(2))
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(3))
  show ?thesis
  proof(rule ntcf_eqI[of \<alpha>])
    show "\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) : 
      \<FF>'' \<circ>\<^sub>C\<^sub>F \<FF>' \<circ>\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG>'' \<circ>\<^sub>C\<^sub>F \<GG>' \<circ>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from ntsmcf_hcomp_assoc[
      OF \<LL>.ntcf_is_ntsmcf \<MM>.ntcf_is_ntsmcf \<NN>.ntcf_is_ntsmcf,
      unfolded slicing_commute
      ]
    have 
      "ntcf_ntsmcf (\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr> = 
        ntcf_ntsmcf (\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>"
      by simp
    then show "(\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr> = (\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>"
      unfolding slicing_simps .
  qed (auto intro: cat_cs_intros)
qed


subsubsection\<open>
The opposite of the horizontal composition of natural transformations
\<close>

lemma op_ntcf_ntcf_hcomp[cat_op_simps]: 
  assumes "\<MM> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "op_ntcf (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) = op_ntcf \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf \<NN>"
proof-
  interpret \<MM>: is_ntcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<MM> by (rule assms(1))
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  show ?thesis
  proof(rule sym, rule ntcf_eqI[of \<alpha>])
    from op_ntsmcf_ntsmcf_hcomp[
        OF \<MM>.ntcf_is_ntsmcf \<NN>.ntcf_is_ntsmcf, 
        unfolded slicing_simps slicing_commute 
        ]
    have "ntcf_ntsmcf (op_ntcf \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf \<NN>)\<lparr>NTMap\<rparr> =
      ntcf_ntsmcf (op_ntcf (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>"
      by simp
    then show "(op_ntcf \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf \<NN>)\<lparr>NTMap\<rparr> = op_ntcf (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>"
      unfolding slicing_simps .
    have "\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<FF>' \<circ>\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG>' \<circ>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (rule ntcf_hcomp_is_ntcf[OF assms])
    from is_ntcf.is_ntcf_op[OF this] show 
      "op_ntcf (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) : 
        op_cf \<GG>' \<circ>\<^sub>C\<^sub>F op_cf \<GG> \<mapsto>\<^sub>C\<^sub>F op_cf \<FF>' \<circ>\<^sub>C\<^sub>F op_cf \<FF> : 
        op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<CC>"
      unfolding cat_op_simps .
  qed (auto intro: cat_op_intros cat_cs_intros)
qed 



subsection\<open>Interchange law\<close>

lemma ntcf_comp_interchange_law:
  \<comment>\<open>See Chapter II-5 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<MM>' : \<GG>' \<mapsto>\<^sub>C\<^sub>F \<HH>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN>' : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "((\<MM>' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>') \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)) = (\<MM>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<MM>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<NN>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)"
proof-
  interpret \<MM>: is_ntcf \<alpha> \<AA> \<BB> \<GG> \<HH> \<MM> by (rule assms(1))
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  interpret \<MM>': is_ntcf \<alpha> \<BB> \<CC> \<GG>' \<HH>' \<MM>' by (rule assms(3))
  interpret \<NN>': is_ntcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<NN>' by (rule assms(4))
  show ?thesis
  proof(rule ntcf_eqI)
    from ntsmcf_comp_interchange_law
      [
        OF 
          \<MM>.ntcf_is_ntsmcf 
          \<NN>.ntcf_is_ntsmcf 
          \<MM>'.ntcf_is_ntsmcf 
          \<NN>'.ntcf_is_ntsmcf
      ]
    have 
      "(
        (ntcf_ntsmcf \<MM>' \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F ntcf_ntsmcf \<NN>') \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F
        (ntcf_ntsmcf \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F ntcf_ntsmcf \<NN>)
       )\<lparr>NTMap\<rparr> =
        (
          (ntcf_ntsmcf \<MM>' \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F ntcf_ntsmcf \<MM>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F
          (ntcf_ntsmcf \<NN>' \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F ntcf_ntsmcf \<NN>)
        )\<lparr>NTMap\<rparr>"
      by simp
    then show 
      "(\<MM>' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr> =
        (\<MM>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<NN>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>"
      unfolding slicing_simps slicing_commute .
  qed (auto intro: cat_cs_intros)
qed



subsection\<open>Identity natural transformation\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter II-4 in \cite{mac_lane_categories_2010}.\<close>

definition ntcf_id :: "V \<Rightarrow> V"
  where "ntcf_id \<FF> = [\<FF>\<lparr>HomCod\<rparr>\<lparr>CId\<rparr> \<circ>\<^sub>\<circ> \<FF>\<lparr>ObjMap\<rparr>, \<FF>, \<FF>, \<FF>\<lparr>HomDom\<rparr>, \<FF>\<lparr>HomCod\<rparr>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma ntcf_id_components:
  shows "ntcf_id \<FF>\<lparr>NTMap\<rparr> = \<FF>\<lparr>HomCod\<rparr>\<lparr>CId\<rparr> \<circ>\<^sub>\<circ> \<FF>\<lparr>ObjMap\<rparr>"
    and [dg_shared_cs_simps, cat_cs_simps]: "ntcf_id \<FF>\<lparr>NTDom\<rparr> = \<FF>" 
    and [dg_shared_cs_simps, cat_cs_simps]: "ntcf_id \<FF>\<lparr>NTCod\<rparr> = \<FF>" 
    and [dg_shared_cs_simps, cat_cs_simps]: "ntcf_id \<FF>\<lparr>NTDGDom\<rparr> = \<FF>\<lparr>HomDom\<rparr>" 
    and [dg_shared_cs_simps, cat_cs_simps]: "ntcf_id \<FF>\<lparr>NTDGCod\<rparr> = \<FF>\<lparr>HomCod\<rparr>" 
  unfolding ntcf_id_def nt_field_simps by (simp_all add: nat_omega_simps)

lemma (in is_functor) is_functor_ntcf_id_components:
  shows "ntcf_id \<FF>\<lparr>NTMap\<rparr> = \<BB>\<lparr>CId\<rparr> \<circ>\<^sub>\<circ> \<FF>\<lparr>ObjMap\<rparr>"
    and "ntcf_id \<FF>\<lparr>NTDom\<rparr> = \<FF>" 
    and "ntcf_id \<FF>\<lparr>NTCod\<rparr> = \<FF>" 
    and "ntcf_id \<FF>\<lparr>NTDGDom\<rparr> = \<AA>" 
    and "ntcf_id \<FF>\<lparr>NTDGCod\<rparr> = \<BB>" 
  unfolding ntcf_id_components by (simp_all add: cat_cs_simps)


subsubsection\<open>Natural transformation map\<close>

lemma (in is_functor) ntcf_id_NTMap_vdomain[cat_cs_simps]: 
  "\<D>\<^sub>\<circ> (ntcf_id \<FF>\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
  using cf_ObjMap_vrange unfolding is_functor_ntcf_id_components 
  by (auto simp: cat_cs_simps)

lemmas [cat_cs_simps] = is_functor.ntcf_id_NTMap_vdomain

lemma (in is_functor) ntcf_id_NTMap_app_vdomain[cat_cs_simps]: 
  assumes [simp]: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "ntcf_id \<FF>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
  unfolding is_functor_ntcf_id_components
  by (rule vsv_vcomp_at) (auto simp: cf_ObjMap_vrange cat_cs_simps cat_cs_intros)

lemmas [cat_cs_simps] = is_functor.ntcf_id_NTMap_app_vdomain

lemma (in is_functor) ntcf_id_NTMap_vsv[cat_cs_intros]: 
  "vsv (ntcf_id \<FF>\<lparr>NTMap\<rparr>)"
  unfolding is_functor_ntcf_id_components by (auto intro: vsv_vcomp)

lemmas [cat_cs_intros] = is_functor.ntcf_id_NTMap_vsv

lemma (in is_functor) ntcf_id_NTMap_vrange: 
  "\<R>\<^sub>\<circ> (ntcf_id \<FF>\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
proof(rule vsubsetI)
  interpret vsv \<open>ntcf_id \<FF>\<lparr>NTMap\<rparr>\<close> by (rule ntcf_id_NTMap_vsv)
  fix f assume "f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (ntcf_id \<FF>\<lparr>NTMap\<rparr>)"
  then obtain a 
    where f_def: "f = ntcf_id \<FF>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>" and a: "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (ntcf_id \<FF>\<lparr>NTMap\<rparr>)"
    using vrange_atD by metis
  then have "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and "f = \<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
    by (auto simp: cat_cs_simps)
  then show "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
    by (auto dest: cf_ObjMap_app_in_HomCod_Obj HomCod.cat_CId_is_arr)
qed


subsubsection\<open>Further properties\<close>

lemma (in is_functor) cf_ntcf_id_is_ntcf[cat_cs_intros]: 
  "ntcf_id \<FF> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
proof(rule is_ntcfI, unfold is_functor_ntcf_id_components(2,3,4,5))
  show "ntcf_ntsmcf (ntcf_id \<FF>) : 
    cf_smcf \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F cf_smcf \<FF> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<BB>"
  proof
    (
      rule is_ntsmcfI, 
      unfold slicing_simps slicing_commute is_functor_ntcf_id_components(2,3,4,5)
    )
    show "ntsmcf_tdghm (ntcf_ntsmcf (ntcf_id \<FF>)) : 
      smcf_dghm (cf_smcf \<FF>) \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M smcf_dghm (cf_smcf \<FF>) : 
      smc_dg (cat_smc \<AA>) \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg (cat_smc \<BB>)"
      by
        (
          rule is_tdghmI, 
          unfold 
            slicing_simps 
            slicing_commute 
            is_functor_ntcf_id_components(2,3,4,5)
        )
        (
          auto 
            simp:
              cat_cs_simps
              cat_cs_intros
              nat_omega_simps
              ntsmcf_tdghm_def
              cf_is_semifunctor 
            intro: slicing_intros
        )
    fix f a b assume "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
    with is_functor_axioms show "ntcf_id \<FF>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = 
      \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> ntcf_id \<FF>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed (auto simp: ntcf_ntsmcf_def nat_omega_simps intro: slicing_intros)
qed (auto simp: ntcf_id_def nat_omega_simps intro: cat_cs_intros)

lemma (in is_functor) cf_ntcf_id_is_ntcf': 
  assumes "\<GG>' = \<FF>" and "\<HH>' = \<FF>"
  shows "ntcf_id \<FF> : \<GG>' \<mapsto>\<^sub>C\<^sub>F \<HH>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  unfolding assms by (rule cf_ntcf_id_is_ntcf)

lemmas [cat_cs_intros] = is_functor.cf_ntcf_id_is_ntcf'

lemma (in is_ntcf) ntcf_ntcf_vcomp_ntcf_id_left_left[cat_cs_simps]:
  \<comment>\<open>See Chapter II-4 in \cite{mac_lane_categories_2010}.\<close>
  "ntcf_id \<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> = \<NN>"
proof(rule ntcf_eqI[of \<alpha>])
  interpret id: is_ntcf \<alpha> \<AA> \<BB> \<GG> \<GG> \<open>ntcf_id \<GG>\<close> 
    by (rule NTCod.cf_ntcf_id_is_ntcf)
  show "(ntcf_id \<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr> = \<NN>\<lparr>NTMap\<rparr>"
  proof(rule vsv_eqI)
    show [simp]: "\<D>\<^sub>\<circ> ((ntcf_id \<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>) = \<D>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>)"
      unfolding ntsmcf_vcomp_components 
      by (simp add: cat_cs_simps)
    fix a assume "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((ntcf_id \<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>)"
    then have "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" by (simp add: cat_cs_simps)
    then show "(ntcf_id \<GG> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed (auto simp: ntsmcf_vcomp_components)
qed (auto intro: cat_cs_intros)

lemmas [cat_cs_simps] = is_ntcf.ntcf_ntcf_vcomp_ntcf_id_left_left

lemma (in is_ntcf) ntcf_ntcf_vcomp_ntcf_id_right_left[cat_cs_simps]: 
  \<comment>\<open>See Chapter II-4 in \cite{mac_lane_categories_2010}.\<close>
  "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF> = \<NN>"
proof(rule ntcf_eqI[of \<alpha>])
  interpret id: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<FF> \<open>ntcf_id \<FF>\<close>    
    by (rule NTDom.cf_ntcf_id_is_ntcf)
  show "(\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF>)\<lparr>NTMap\<rparr> = \<NN>\<lparr>NTMap\<rparr>"
  proof(rule vsv_eqI)
    show [simp]: "\<D>\<^sub>\<circ> ((\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF>)\<lparr>NTMap\<rparr>) = \<D>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>)"
      unfolding ntsmcf_vcomp_components by (simp add: cat_cs_simps)
    fix a assume "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF>)\<lparr>NTMap\<rparr>)"
    then have "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" by (simp add: cat_cs_simps)
    then show "(\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>" 
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed (auto simp: ntsmcf_vcomp_components)
qed (auto intro: cat_cs_intros)

lemmas [cat_cs_simps] = is_ntcf.ntcf_ntcf_vcomp_ntcf_id_right_left

lemma (in is_ntcf) ntcf_ntcf_hcomp_ntcf_id_left_left[cat_cs_simps]:
  \<comment>\<open>See Chapter II-5 in \cite{mac_lane_categories_2010}.\<close>
  "ntcf_id (cf_id \<BB>) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> = \<NN>"
proof(rule ntcf_eqI)
  interpret id: is_ntcf \<alpha> \<BB> \<BB> \<open>cf_id \<BB>\<close> \<open>cf_id \<BB>\<close> \<open>ntcf_id (cf_id \<BB>)\<close> 
    by 
      (
        simp add: 
          NTDom.HomCod.cat_cf_id_is_functor is_functor.cf_ntcf_id_is_ntcf
      )
  show "ntcf_id (cf_id \<BB>) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : 
    cf_id \<BB> \<circ>\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>C\<^sub>F cf_id \<BB> \<circ>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: cat_cs_intros)
  show "(ntcf_id (cf_id \<BB>) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr> = \<NN>\<lparr>NTMap\<rparr>"
  proof(rule vsv_eqI)
    fix a assume "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((ntcf_id (cf_id \<BB>) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>)"    
    then have a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
      unfolding ntcf_hcomp_NTMap_vdomain[OF is_ntcf_axioms] by simp
    with is_ntcf_axioms show 
      "(ntcf_id (cf_id \<BB>) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed (auto simp: ntsmcf_hcomp_components(1) cat_cs_simps)
qed (auto simp: cat_cs_simps intro: cat_cs_intros)

lemmas [cat_cs_simps] = is_ntcf.ntcf_ntcf_hcomp_ntcf_id_left_left

lemma (in is_ntcf) ntcf_ntcf_hcomp_ntcf_id_right_left[cat_cs_simps]: 
  \<comment>\<open>See Chapter II-5 in \cite{mac_lane_categories_2010}.\<close>
  "\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id (cf_id \<AA>) = \<NN>"
proof(rule ntcf_eqI[of \<alpha>])
  interpret id: is_ntcf \<alpha> \<AA> \<AA> \<open>cf_id \<AA>\<close> \<open>cf_id \<AA>\<close> \<open>ntcf_id (cf_id \<AA>)\<close> 
    by 
      (
        simp add: 
          NTDom.HomDom.cat_cf_id_is_functor is_functor.cf_ntcf_id_is_ntcf
      )
  show "\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id (cf_id \<AA>) :
    \<FF> \<circ>\<^sub>C\<^sub>F cf_id \<AA> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F cf_id \<AA> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: cat_cs_intros)
  show "(\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id (cf_id \<AA>))\<lparr>NTMap\<rparr> = \<NN>\<lparr>NTMap\<rparr>"
  proof(rule vsv_eqI)
    fix a assume "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id (cf_id \<AA>))\<lparr>NTMap\<rparr>)"
    then have a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
      unfolding ntcf_hcomp_NTMap_vdomain[OF id.is_ntcf_axioms] by simp
    with is_ntcf_axioms show 
      "(\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id (cf_id \<AA>))\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed (auto simp: ntsmcf_hcomp_components(1) cat_cs_simps)
qed (auto simp: cat_cs_simps cat_cs_intros)

lemmas [cat_cs_simps] = is_ntcf.ntcf_ntcf_hcomp_ntcf_id_right_left


subsubsection\<open>The opposite identity natural transformation\<close>

lemma (in is_functor) cf_ntcf_id_op_cf: "ntcf_id (op_cf \<FF>) = op_ntcf (ntcf_id \<FF>)"
proof(rule ntcf_eqI)
  show ntcfid_op: 
    "ntcf_id (op_cf \<FF>) : op_cf \<FF> \<mapsto>\<^sub>C\<^sub>F op_cf \<FF> : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<BB>"
    by (simp add: is_functor.cf_ntcf_id_is_ntcf local.is_functor_op)
  show "ntcf_id (op_cf \<FF>)\<lparr>NTMap\<rparr> = op_ntcf (ntcf_id \<FF>)\<lparr>NTMap\<rparr>"
    by (rule vsv_eqI, unfold cat_op_simps)
      (
        auto 
          simp: cat_op_simps cat_cs_simps ntcf_id_components(1) 
          intro: vsv_vcomp
      )
qed (auto intro: cat_op_intros cat_cs_intros)


subsubsection\<open>Identity natural transformation of a composition of functors\<close>

lemma ntcf_id_cf_comp:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "ntcf_id (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) = ntcf_id \<GG> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF>"
proof(rule ntcf_eqI)
  from assms show \<GG>\<FF>: "ntcf_id (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) : \<GG> \<circ>\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  interpret \<GG>\<FF>: is_ntcf \<alpha> \<AA> \<CC> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<FF>\<close> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<FF>\<close> \<open>ntcf_id (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<close>
    by (rule \<GG>\<FF>)
  from assms show \<GG>_\<FF>:
    "ntcf_id \<GG> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF> : \<GG> \<circ>\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  interpret \<GG>_\<FF>: is_ntcf \<alpha> \<AA> \<CC> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<FF>\<close> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<FF>\<close> \<open>ntcf_id \<GG> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF>\<close>
    by (rule \<GG>_\<FF>)
  show "ntcf_id (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>NTMap\<rparr> = (ntcf_id \<GG> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF>)\<lparr>NTMap\<rparr>"
  proof(rule vsv_eqI, unfold \<GG>\<FF>.ntcf_NTMap_vdomain \<GG>_\<FF>.ntcf_NTMap_vdomain)
    fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    with assms show 
      "ntcf_id (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (ntcf_id \<GG> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed auto
qed auto

lemmas [cat_cs_simps] = ntcf_id_cf_comp[symmetric]



subsection\<open>Composition of a natural transformation and a functor\<close>


subsubsection\<open>Definition and elementary properties\<close>

abbreviation (input) ntcf_cf_comp :: "V \<Rightarrow> V \<Rightarrow> V" (infixl "\<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F" 55)
  where "ntcf_cf_comp \<equiv> tdghm_dghm_comp"


text\<open>Slicing.\<close>

lemma ntsmcf_tdghm_ntsmcf_smcf_comp[slicing_commute]: 
  "ntcf_ntsmcf \<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F cf_smcf \<HH> = ntcf_ntsmcf (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<HH>)"
  unfolding 
    ntcf_ntsmcf_def
    cf_smcf_def
    cat_smc_def
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

mk_VLambda (in is_functor) 
  tdghm_dghm_comp_components(1)[where \<HH>=\<FF>, unfolded cf_HomDom]
  |vdomain ntcf_cf_comp_NTMap_vdomain[cat_cs_simps]|
  |app ntcf_cf_comp_NTMap_app[cat_cs_simps]|

lemmas [cat_cs_simps] = 
  is_functor.ntcf_cf_comp_NTMap_vdomain
  is_functor.ntcf_cf_comp_NTMap_app

lemma ntcf_cf_comp_NTMap_vrange: 
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<HH>)\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof-
  interpret \<NN>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<HH>: is_functor \<alpha> \<AA> \<BB> \<HH> by (rule assms(2))
  show ?thesis unfolding tdghm_dghm_comp_components 
    by (auto simp: cat_cs_simps intro: cat_cs_intros)
qed


subsubsection\<open>
Opposite of the composition of a natural transformation and a functor
\<close>

lemma op_ntcf_ntcf_cf_comp[cat_op_simps]:
  "op_ntcf (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<HH>) = op_ntcf \<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F op_cf \<HH>"
  unfolding 
    tdghm_dghm_comp_def 
    dghm_comp_def 
    op_ntcf_def 
    op_cf_def 
    op_cat_def
    dg_field_simps
    dghm_field_simps
    nt_field_simps
  by (simp add: nat_omega_simps) (*slow*)


subsubsection\<open>
Composition of a natural transformation and a
functor is a natural transformation
\<close>

lemma ntcf_cf_comp_is_ntcf:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<HH> : \<FF> \<circ>\<^sub>C\<^sub>F \<HH> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<NN>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<HH>: is_functor \<alpha> \<AA> \<BB> \<HH> by (rule assms(2))
  show ?thesis
  proof(rule is_ntcfI)
    show "vfsequence (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<HH>)"
      unfolding tdghm_dghm_comp_def by (simp add: nat_omega_simps)
    from assms show "\<FF> \<circ>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
      by (cs_concl cs_intro: cat_cs_intros)
    from assms show "\<GG> \<circ>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
      by (cs_concl cs_intro: cat_cs_intros)
    show "vcard (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<HH>) = 5\<^sub>\<nat>"
      unfolding tdghm_dghm_comp_def by (simp add: nat_omega_simps)
    from assms show 
      "ntcf_ntsmcf (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<HH>) :
        cf_smcf (\<FF> \<circ>\<^sub>C\<^sub>F \<HH>) \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F cf_smcf (\<GG> \<circ>\<^sub>C\<^sub>F \<HH>) :
        cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<CC>"
      by 
        (
          cs_concl 
            cs_simp: slicing_commute[symmetric] 
            cs_intro: slicing_intros smc_cs_intros cat_cs_intros
        )
  qed (auto simp: tdghm_dghm_comp_components(1) cat_cs_simps)
qed

lemma ntcf_cf_comp_is_functor'[cat_cs_intros]:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF>' = \<FF> \<circ>\<^sub>C\<^sub>F \<HH>"
    and "\<GG>' = \<GG> \<circ>\<^sub>C\<^sub>F \<HH>"
  shows "\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<HH> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1,2) unfolding assms(3,4) by (simp add: ntcf_cf_comp_is_ntcf)


subsubsection\<open>Further properties\<close>

lemma ntcf_cf_comp_ntcf_cf_comp_assoc:
  assumes "\<NN> : \<HH> \<mapsto>\<^sub>C\<^sub>F \<HH>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" 
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "(\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF> = \<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)"
proof-
  interpret \<NN>: is_ntcf \<alpha> \<CC> \<DD> \<HH> \<HH>' \<NN> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(2))
  interpret \<FF>: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(3))
  show ?thesis  
  proof(rule ntcf_ntsmcf_eqI)
    from assms show
      "(\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF> :
        \<HH> \<circ>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>C\<^sub>F \<HH>' \<circ>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
      by (cs_concl cs_intro: cat_cs_intros)
    show "\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) :
      \<HH> \<circ>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>C\<^sub>F \<HH>' \<circ>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from assms show 
      "ntcf_ntsmcf ((\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF>) =
        ntcf_ntsmcf (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>))"
      by 
        (
          cs_concl
            cs_simp: slicing_commute[symmetric] 
            cs_intro: slicing_intros ntsmcf_smcf_comp_ntsmcf_smcf_comp_assoc
        )
  qed simp_all
qed

lemma (in is_ntcf) ntcf_ntcf_cf_comp_cf_id[cat_cs_simps]:
  "\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F cf_id \<AA> = \<NN>"
proof(rule ntcf_ntsmcf_eqI)
  show "\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F cf_id \<AA> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  show "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: cat_cs_intros)
  show "ntcf_ntsmcf (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F cf_id \<AA>) = ntcf_ntsmcf \<NN>"
    by
      (
        cs_concl
          cs_simp: slicing_commute[symmetric] 
          cs_intro: cat_cs_intros slicing_intros smc_cs_simps
      )
qed simp_all

lemmas [cat_cs_simps] = is_ntcf.ntcf_ntcf_cf_comp_cf_id

lemma ntcf_vcomp_ntcf_cf_comp[cat_cs_simps]:
  assumes "\<KK> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "(\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>) = (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>"
proof(rule ntcf_ntsmcf_eqI)
  from assms show 
    "\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>) :
      \<FF> \<circ>\<^sub>C\<^sub>F \<KK> \<mapsto>\<^sub>C\<^sub>F \<HH> \<circ>\<^sub>C\<^sub>F \<KK> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: cat_cs_intros)
  from assms show 
    "ntcf_ntsmcf (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)) =
      ntcf_ntsmcf (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)"
    unfolding slicing_commute[symmetric]
    by (intro ntsmcf_vcomp_ntsmcf_smcf_comp)
      (cs_concl cs_intro: slicing_intros)
qed (use assms in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+



subsection\<open>Composition of a functor and a natural transformation\<close>


subsubsection\<open>Definition and elementary properties\<close>

abbreviation (input) cf_ntcf_comp :: "V \<Rightarrow> V \<Rightarrow> V" (infixl "\<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F" 55)
  where "cf_ntcf_comp \<equiv> dghm_tdghm_comp"


text\<open>Slicing.\<close>

lemma ntcf_ntsmcf_cf_ntcf_comp[slicing_commute]: 
  "cf_smcf \<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F ntcf_ntsmcf \<NN> = ntcf_ntsmcf (\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)"
  unfolding 
    ntcf_ntsmcf_def
    cf_smcf_def
    cat_smc_def
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

mk_VLambda (in is_ntcf) 
  dghm_tdghm_comp_components(1)[where \<NN>=\<NN>, unfolded ntcf_NTDGDom]
  |vdomain cf_ntcf_comp_NTMap_vdomain|
  |app cf_ntcf_comp_NTMap_app|

lemmas [cat_cs_simps] = 
  is_ntcf.cf_ntcf_comp_NTMap_vdomain
  is_ntcf.cf_ntcf_comp_NTMap_app

lemma cf_ntcf_comp_NTMap_vrange: 
  assumes "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof-
  interpret \<HH>: is_functor \<alpha> \<BB> \<CC> \<HH> by (rule assms(1))
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  show ?thesis 
    unfolding dghm_tdghm_comp_components 
    by (auto simp: cat_cs_simps intro: cat_cs_intros)
qed


subsubsection\<open>
Opposite of the composition of a functor and a natural transformation
\<close>

lemma op_ntcf_cf_ntcf_comp[cat_op_simps]:
  "op_ntcf (\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) = op_cf \<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf \<NN>"
  unfolding 
    dghm_tdghm_comp_def
    dghm_comp_def
    op_ntcf_def
    op_cf_def
    op_cat_def
    dg_field_simps
    dghm_field_simps
    nt_field_simps
  by (simp add: nat_omega_simps) (*slow*)


subsubsection\<open>
Composition of a functor and a natural transformation 
is a natural transformation
\<close>

lemma cf_ntcf_comp_is_ntcf:
  assumes "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<HH> \<circ>\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>C\<^sub>F \<HH> \<circ>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<HH>: is_functor \<alpha> \<BB> \<CC> \<HH> by (rule assms(1))
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  show ?thesis
  proof(rule is_ntcfI)
    show "vfsequence (\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)" unfolding dghm_tdghm_comp_def by simp
    from assms show "\<HH> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
      by (cs_concl cs_intro: cat_cs_intros)
    from assms show "\<HH> \<circ>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_intro: cat_cs_intros)
    show "vcard (\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) = 5\<^sub>\<nat>"
      unfolding dghm_tdghm_comp_def by (simp add: nat_omega_simps)
    from assms show "ntcf_ntsmcf (\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) :
      cf_smcf (\<HH> \<circ>\<^sub>C\<^sub>F \<FF>) \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F cf_smcf (\<HH> \<circ>\<^sub>C\<^sub>F \<GG>) :
      cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc \<CC>"
      by 
        (
          cs_concl 
            cs_simp: slicing_commute[symmetric]
            cs_intro: slicing_intros smc_cs_intros 
        )
  qed (auto simp: dghm_tdghm_comp_components(1) cat_cs_simps)
qed

lemma cf_ntcf_comp_is_functor'[cat_cs_intros]:
  assumes "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF>' = \<HH> \<circ>\<^sub>C\<^sub>F \<FF>"
    and "\<GG>' = \<HH> \<circ>\<^sub>C\<^sub>F \<GG>"
  shows "\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1,2) unfolding assms(3,4) by (simp add: cf_ntcf_comp_is_ntcf)


subsubsection\<open>Further properties\<close>

lemma cf_comp_cf_ntcf_comp_assoc:
  assumes "\<NN> : \<HH> \<mapsto>\<^sub>C\<^sub>F \<HH>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "(\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> = \<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)"
proof(rule ntcf_ntsmcf_eqI)
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<HH> \<HH>' \<NN> by (rule assms(1))
  interpret \<FF>: is_functor \<alpha> \<BB> \<CC> \<FF> by (rule assms(2))
  interpret \<GG>: is_functor \<alpha> \<CC> \<DD> \<GG> by (rule assms(3))
  from assms show "(\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> :
    \<GG> \<circ>\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>C\<^sub>F \<HH> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>C\<^sub>F \<HH>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    by (cs_concl cs_intro: cat_cs_intros)
  from assms show "\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) :
    \<GG> \<circ>\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>C\<^sub>F \<HH> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>C\<^sub>F \<HH>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms show 
    "ntcf_ntsmcf (\<GG> \<circ>\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) =
      ntcf_ntsmcf (\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>))"
    by
      (
        cs_concl
          cs_simp: slicing_commute[symmetric] 
          cs_intro: slicing_intros smcf_comp_smcf_ntsmcf_comp_assoc
      )
qed simp_all

lemma (in is_ntcf) ntcf_cf_ntcf_comp_cf_id[cat_cs_simps]:
  "cf_id \<BB> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> = \<NN>"
proof(rule ntcf_ntsmcf_eqI)
  show "cf_id \<BB> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  show "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: cat_cs_intros)
  show "ntcf_ntsmcf (smcf_id \<BB> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN>) = ntcf_ntsmcf \<NN>"
    by 
      (
        cs_concl
          cs_simp: slicing_commute[symmetric] 
          cs_intro: cat_cs_intros slicing_intros smc_cs_simps
      )
qed simp_all

lemmas [cat_cs_simps] = is_ntcf.ntcf_cf_ntcf_comp_cf_id

lemma cf_ntcf_comp_ntcf_cf_comp_assoc:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<KK> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "(\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK> = \<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)"
proof-
  interpret \<NN>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<HH>: is_functor \<alpha> \<CC> \<DD> \<HH> by (rule assms(2))
  interpret \<KK>: is_functor \<alpha> \<AA> \<BB> \<KK> by (rule assms(3))
  show ?thesis
    by (rule ntcf_ntsmcf_eqI)
      (
        use assms in
          \<open>
            cs_concl
              cs_simp: cat_cs_simps slicing_commute[symmetric]
              cs_intro:
                cat_cs_intros
                slicing_intros
                smcf_ntsmcf_comp_ntsmcf_smcf_comp_assoc
          \<close>
      )+
qed

lemma ntcf_cf_comp_ntcf_id[cat_cs_simps]:
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<KK> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "ntcf_id \<FF> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK> = ntcf_id \<FF> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<KK>"
proof(rule ntcf_eqI)
  from assms have dom_lhs: "\<D>\<^sub>\<circ> ((ntcf_id \<FF> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)
  from assms have dom_rhs: "\<D>\<^sub>\<circ> ((ntcf_id \<FF> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<KK>)\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  show "(ntcf_id \<FF> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)\<lparr>NTMap\<rparr> = (ntcf_id \<FF> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<KK>)\<lparr>NTMap\<rparr>"
  proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
    fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    with assms show 
      "(ntcf_id \<FF> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (ntcf_id \<FF> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<KK>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed (auto intro: cat_cs_intros)
qed (use assms in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+

lemma cf_comp_cf_const_right[cat_cs_simps]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<aa> \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<GG> \<circ>\<^sub>C\<^sub>F cf_const \<AA> \<BB> \<aa> = cf_const \<AA> \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>)"
proof(rule cf_eqI)

  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(2))
  interpret \<GG>: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(3))

  from assms(4) show "\<GG> \<circ>\<^sub>C\<^sub>F cf_const \<AA> \<BB> \<aa> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: cat_cs_intros)
  from assms(4) show "cf_const \<AA> \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>) : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms(4) have ObjMap_dom_lhs: 
    "\<D>\<^sub>\<circ> ((\<GG> \<circ>\<^sub>C\<^sub>F cf_const \<AA> \<BB> \<aa>)\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms(4) have ObjMap_dom_rhs: 
    "\<D>\<^sub>\<circ> (cf_const \<AA> \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>)\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)
  show "(\<GG> \<circ>\<^sub>C\<^sub>F cf_const \<AA> \<BB> \<aa>)\<lparr>ObjMap\<rparr> = cf_const \<AA> \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>)\<lparr>ObjMap\<rparr>"
  proof(rule vsv_eqI, unfold ObjMap_dom_lhs ObjMap_dom_rhs)
    fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    with assms(4) show "(\<GG> \<circ>\<^sub>C\<^sub>F cf_const \<AA> \<BB> \<aa>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> =
      cf_const \<AA> \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed (auto intro: assms(4) cat_cs_intros)
  from assms(4) have ArrMap_dom_lhs: 
    "\<D>\<^sub>\<circ> ((\<GG> \<circ>\<^sub>C\<^sub>F cf_const \<AA> \<BB> \<aa>)\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms(4) have ArrMap_dom_rhs: 
    "\<D>\<^sub>\<circ> (cf_const \<AA> \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>)\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  show
    "(\<GG> \<circ>\<^sub>C\<^sub>F cf_const \<AA> \<BB> \<aa>)\<lparr>ArrMap\<rparr> = cf_const \<AA> \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>)\<lparr>ArrMap\<rparr>"
  proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
    fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
    with assms(4) show "(\<GG> \<circ>\<^sub>C\<^sub>F cf_const \<AA> \<BB> \<aa>)\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> =
      cf_const \<AA> \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>\<aa>\<rparr>)\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed (auto intro: assms(4) cat_cs_intros)

qed simp_all

lemma cf_ntcf_comp_ntcf_vcomp: 
  assumes "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<KK> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) = (\<KK> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<MM>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<KK> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)"
proof-
  interpret \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(1))
  interpret \<MM>: is_ntcf \<alpha> \<AA> \<BB> \<GG> \<HH> \<MM> by (rule assms(2))
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(3))
  show "\<KK> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) = \<KK> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<KK> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)"
    by (rule ntcf_ntsmcf_eqI)
      (
        use assms in
          \<open>
            cs_concl
              cs_simp: smc_cs_simps slicing_commute[symmetric]
              cs_intro:
                cat_cs_intros
                slicing_intros
                smcf_ntsmcf_comp_ntsmcf_vcomp
          \<close>
      )+
qed



subsection\<open>Constant natural transformation\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter III in \cite{mac_lane_categories_2010}.\<close>

definition ntcf_const :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_const \<JJ> \<CC> f = 
    [
      vconst_on (\<JJ>\<lparr>Obj\<rparr>) f, 
      cf_const \<JJ> \<CC> (\<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr>), 
      cf_const \<JJ> \<CC> (\<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr>), 
      \<JJ>, 
      \<CC>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma ntcf_const_components:
  shows "ntcf_const \<JJ> \<CC> f\<lparr>NTMap\<rparr> = vconst_on (\<JJ>\<lparr>Obj\<rparr>) f"
    and "ntcf_const \<JJ> \<CC> f\<lparr>NTDom\<rparr> = cf_const \<JJ> \<CC> (\<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr>)"
    and "ntcf_const \<JJ> \<CC> f\<lparr>NTCod\<rparr> = cf_const \<JJ> \<CC> (\<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr>)"
    and "ntcf_const \<JJ> \<CC> f\<lparr>NTDGDom\<rparr> = \<JJ>"
    and "ntcf_const \<JJ> \<CC> f\<lparr>NTDGCod\<rparr> = \<CC>"
  unfolding ntcf_const_def nt_field_simps by (auto simp: nat_omega_simps)


subsubsection\<open>Natural transformation map\<close>

mk_VLambda ntcf_const_components(1)[folded VLambda_vconst_on]
  |vsv ntcf_const_ObjMap_vsv[cat_cs_intros]|
  |vdomain ntcf_const_ObjMap_vdomain[cat_cs_simps]|
  |app ntcf_const_ObjMap_app[cat_cs_simps]|

lemma ntcf_const_NTMap_ne_vrange: 
  assumes "\<JJ>\<lparr>Obj\<rparr> \<noteq> 0"
  shows "\<R>\<^sub>\<circ> (ntcf_const \<JJ> \<CC> f\<lparr>NTMap\<rparr>) = set {f}"
  using assms unfolding ntcf_const_components by simp

lemma ntcf_const_NTMap_vempty_vrange: 
  assumes "\<JJ>\<lparr>Obj\<rparr> = 0"
  shows "\<R>\<^sub>\<circ> (ntcf_const \<JJ> \<CC> f\<lparr>NTMap\<rparr>) = 0"
  using assms unfolding ntcf_const_components by simp


subsubsection\<open>Constant natural transformation is a natural transformation\<close>

lemma ntcf_const_is_ntcf:
  assumes "category \<alpha> \<JJ>" and "category \<alpha> \<CC>" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "ntcf_const \<JJ> \<CC> f : cf_const \<JJ> \<CC> a \<mapsto>\<^sub>C\<^sub>F cf_const \<JJ> \<CC> b : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<JJ>: category \<alpha> \<JJ> by (rule assms(1))
  interpret \<CC>: category \<alpha> \<CC> by (rule assms(2))
  show ?thesis  
  proof(intro is_ntcfI')
    show "vfsequence (ntcf_const \<JJ> \<CC> f)" unfolding ntcf_const_def by auto
    show "cf_const \<JJ> \<CC> a : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    proof(rule cf_const_is_functor)
      from assms(3) show "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by (simp add: cat_cs_intros)
    qed (auto simp: cat_cs_intros)
    from assms(3) show const_b_is_functor: 
      "cf_const \<JJ> \<CC> b : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (auto intro: cf_const_is_functor cat_cs_intros)
    show "vcard (ntcf_const \<JJ> \<CC> f) = 5\<^sub>\<nat>"
      unfolding ntcf_const_def by (simp add: nat_omega_simps)
    show 
      "ntcf_const \<JJ> \<CC> f\<lparr>NTMap\<rparr>\<lparr>a'\<rparr> : 
        cf_const \<JJ> \<CC> a\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> cf_const \<JJ> \<CC> b\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>"
      if "a' \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>" for a'
      by (simp add: that assms(3) ntcf_const_components(1) dghm_const_ObjMap_app)
    from assms(3) show 
      "ntcf_const \<JJ> \<CC> f\<lparr>NTMap\<rparr>\<lparr>b'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> cf_const \<JJ> \<CC> a\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> =
        cf_const \<JJ> \<CC> b \<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ntcf_const \<JJ> \<CC> f\<lparr>NTMap\<rparr>\<lparr>a'\<rparr>"
      if "f' : a' \<mapsto>\<^bsub>\<JJ>\<^esub> b'" for f' a' b'
      using that dghm_const_ArrMap_app 
      by (auto simp: ntcf_const_components cat_cs_intros cat_cs_simps)
  qed (use assms(3) in \<open>auto simp: ntcf_const_components\<close>)
qed 

lemma ntcf_const_is_ntcf'[cat_cs_intros]:
  assumes "category \<alpha> \<JJ>" 
    and "category \<alpha> \<CC>"
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    and "\<AA> = cf_const \<JJ> \<CC> a"
    and "\<BB> = cf_const \<JJ> \<CC> b"
    and "\<JJ>' = \<JJ>"
    and "\<CC>' = \<CC>"
  shows "ntcf_const \<JJ> \<CC> f : \<AA> \<mapsto>\<^sub>C\<^sub>F \<BB> : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
  using assms(1-3) unfolding assms(4-7) by (rule ntcf_const_is_ntcf)


subsubsection\<open>Opposite constant natural transformation\<close>

lemma op_ntcf_ntcf_const[cat_op_simps]: 
  "op_ntcf (ntcf_const \<JJ> \<CC> f) = ntcf_const (op_cat \<JJ>) (op_cat \<CC>) f"
  unfolding 
    nt_field_simps dghm_field_simps dg_field_simps
    dghm_const_def ntcf_const_def op_cat_def op_cf_def op_ntcf_def 
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Further properties\<close>

lemma ntcf_const_ntcf_vcomp[cat_cs_simps]:
  assumes "category \<alpha> \<JJ>" 
    and "category \<alpha> \<CC>" 
    and "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" 
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "ntcf_const \<JJ> \<CC> g \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f = ntcf_const \<JJ> \<CC> (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)"
proof-
  interpret \<JJ>: category \<alpha> \<JJ> by (rule assms(1))
  interpret \<CC>: category \<alpha> \<CC> by (rule assms(2))
  from assms(3,4) have gf: "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c" by (simp add: cat_cs_intros)
  note \<JJ>\<CC>g = ntcf_const_is_ntcf[OF assms(1,2,3)] 
    and \<JJ>\<CC>f = ntcf_const_is_ntcf[OF assms(1,2,4)]
  show ?thesis
  proof(rule ntcf_eqI)
    from ntcf_const_is_ntcf[OF assms(1,2,3)] ntcf_const_is_ntcf[OF assms(1,2,4)]
    show 
      "ntcf_const \<JJ> \<CC> g \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f :
        cf_const \<JJ> \<CC> a \<mapsto>\<^sub>C\<^sub>F cf_const \<JJ> \<CC> c : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (rule ntcf_vcomp_is_ntcf)
    show
      "ntcf_const \<JJ> \<CC> (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) : 
        cf_const \<JJ> \<CC> a \<mapsto>\<^sub>C\<^sub>F cf_const \<JJ> \<CC> c : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (rule ntcf_const_is_ntcf[OF assms(1,2) gf])
    show "(ntcf_const \<JJ> \<CC> g \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f)\<lparr>NTMap\<rparr> = 
      ntcf_const \<JJ> \<CC> (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)\<lparr>NTMap\<rparr>"
      unfolding ntcf_const_components
    proof(rule vsv_eqI, unfold ntcf_vcomp_NTMap_vdomain[OF \<JJ>\<CC>f])
      fix a assume prems: "a \<in>\<^sub>\<circ> \<JJ>\<lparr>Obj\<rparr>"
      then show 
        "(ntcf_const \<JJ> \<CC> g \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_const \<JJ> \<CC> f)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
          vconst_on (\<JJ>\<lparr>Obj\<rparr>) (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)\<lparr>a\<rparr>"
        unfolding ntcf_vcomp_NTMap_app[OF \<JJ>\<CC>g \<JJ>\<CC>f prems]  
        by (simp add: ntcf_const_components)
    qed (simp_all add: ntsmcf_vcomp_components)
  qed auto
qed

lemma ntcf_id_cf_const[cat_cs_simps]: 
  assumes "category \<alpha> \<JJ>" and "category \<alpha> \<CC>" and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "ntcf_id (cf_const \<JJ> \<CC> c) = ntcf_const \<JJ> \<CC> (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>)"
proof(rule ntcf_eqI)
  interpret \<JJ>: category \<alpha> \<JJ> by (rule assms(1))
  interpret \<CC>: category \<alpha> \<CC> by (rule assms(2))
  from assms show "ntcf_const \<JJ> \<CC> (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>) : 
    cf_const \<JJ> \<CC> c \<mapsto>\<^sub>C\<^sub>F cf_const \<JJ> \<CC> c : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (auto intro: ntcf_const_is_ntcf)
  interpret const_c: is_functor \<alpha> \<JJ> \<CC> \<open>cf_const \<JJ> \<CC> c\<close>
    by (rule cf_const_is_functor) (auto simp: assms(3) cat_cs_intros)
  show "ntcf_id (cf_const \<JJ> \<CC> c) : 
    cf_const \<JJ> \<CC> c \<mapsto>\<^sub>C\<^sub>F cf_const \<JJ> \<CC> c : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (rule const_c.cf_ntcf_id_is_ntcf)
  show "ntcf_id (cf_const \<JJ> \<CC> c)\<lparr>NTMap\<rparr> = ntcf_const \<JJ> \<CC> (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>)\<lparr>NTMap\<rparr>"
  proof(rule vsv_eqI, unfold ntcf_const_components)
    show "vsv (ntcf_id (cf_const \<JJ> \<CC> c)\<lparr>NTMap\<rparr>)"
      unfolding ntcf_id_components by (auto simp: cat_cs_simps intro: vsv_vcomp)
  qed (auto simp: cat_cs_simps)
qed simp_all

lemma ntcf_cf_comp_cf_const_right[cat_cs_simps]:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "category \<alpha> \<AA>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F cf_const \<AA> \<BB> b = ntcf_const \<AA> \<CC> (\<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>)"
proof-
  interpret \<NN>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<AA>: category \<alpha> \<AA> by (rule assms(2))
  show ?thesis
  proof(rule ntcf_eqI)
    from assms(3) show "\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F cf_const \<AA> \<BB> b :
      cf_const \<AA> \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) \<mapsto>\<^sub>C\<^sub>F cf_const \<AA> \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) :
      \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from assms(3) show "ntcf_const \<AA> \<CC> (\<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>) :
      cf_const \<AA> \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) \<mapsto>\<^sub>C\<^sub>F cf_const \<AA> \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) :
      \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from assms(3) have dom_lhs: 
      "\<D>\<^sub>\<circ> ((\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F cf_const \<AA> \<BB> b)\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from assms(3) have dom_rhs: 
      "\<D>\<^sub>\<circ> (ntcf_const \<AA> \<CC> (\<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>)\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    show 
      "(\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F cf_const \<AA> \<BB> b)\<lparr>NTMap\<rparr> = ntcf_const \<AA> \<CC> (\<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>)\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
      with assms(3) show 
        "(\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F cf_const \<AA> \<BB> b)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
          ntcf_const \<AA> \<CC> (\<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    qed (auto intro: cat_cs_intros)
  qed simp_all
qed

lemma cf_ntcf_comp_ntcf_id[cat_cs_simps]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF> = ntcf_id \<GG> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF>"
proof-
  interpret \<GG>: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1))
  interpret \<FF>: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
  proof(rule ntcf_eqI)
    show "\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF> : \<GG> \<circ>\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_intro: cat_cs_intros)
    show "ntcf_id \<GG> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF> : \<GG> \<circ>\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_intro: cat_cs_intros)
    have dom_lhs: "\<D>\<^sub>\<circ> ((\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF>)\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    have dom_rhs: "\<D>\<^sub>\<circ> ((ntcf_id \<GG> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF>)\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    show "(\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF>)\<lparr>NTMap\<rparr> = (ntcf_id \<GG> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF>)\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
      then show 
        "(\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
          (ntcf_id \<GG> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    qed (cs_concl cs_intro: cat_cs_intros)
  qed simp_all
qed



subsection\<open>Natural isomorphism\<close>


text\<open>See Chapter I-4 in \cite{mac_lane_categories_2010}.\<close>

locale is_iso_ntcf = is_ntcf +
  assumes iso_ntcf_is_arr_isomorphism[cat_arrow_cs_intros]: 
    "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<Longrightarrow> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"

syntax "_is_iso_ntcf" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ : _ \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o _ : _ \<mapsto>\<mapsto>\<^sub>C\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> 
  "CONST is_iso_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>"

lemma (in is_iso_ntcf) iso_ntcf_is_arr_isomorphism':
  assumes "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "A = \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "B = \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
  shows "\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>\<^esub> B"
  using assms by (auto intro: cat_arrow_cs_intros)

lemmas [cat_arrow_cs_intros] = 
  is_iso_ntcf.iso_ntcf_is_arr_isomorphism'

lemma (in is_iso_ntcf) iso_ntcf_is_arr_isomorphism'':
  assumes "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "A = \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "B = \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "F = \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
    and "\<BB>' = \<BB>"
  shows "F : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>'\<^esub> B"
  using assms by (auto intro: cat_arrow_cs_intros)


text\<open>Rules.\<close>

lemma (in is_iso_ntcf) is_iso_ntcf_axioms'[cat_cs_intros]: 
  assumes "\<alpha>' = \<alpha>" and "\<FF>' = \<FF>" and "\<GG>' = \<GG>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<NN> : \<FF>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_iso_ntcf_axioms)

mk_ide rf is_iso_ntcf_def[unfolded is_iso_ntcf_axioms_def]
  |intro is_iso_ntcfI|
  |dest is_iso_ntcfD[dest]|
  |elim is_iso_ntcfE[elim]|

lemmas [ntcf_cs_intros] = is_iso_ntcfD(1)



subsection\<open>Inverse natural transformation\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition inv_ntcf :: "V \<Rightarrow> V"
  where "inv_ntcf \<NN> =
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<NN>\<lparr>NTDGDom\<rparr>\<lparr>Obj\<rparr>. SOME g. is_inverse (\<NN>\<lparr>NTDGCod\<rparr>) g (\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)),
      \<NN>\<lparr>NTCod\<rparr>,
      \<NN>\<lparr>NTDom\<rparr>,
      \<NN>\<lparr>NTDGDom\<rparr>,
      \<NN>\<lparr>NTDGCod\<rparr>
    ]\<^sub>\<circ>"


text\<open>Slicing.\<close>

lemma inv_ntcf_components:
  shows "inv_ntcf \<NN>\<lparr>NTMap\<rparr> = 
    (\<lambda>a\<in>\<^sub>\<circ>\<NN>\<lparr>NTDGDom\<rparr>\<lparr>Obj\<rparr>. SOME g. is_inverse (\<NN>\<lparr>NTDGCod\<rparr>) g (\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>))" 
    and [cat_cs_simps]: "inv_ntcf \<NN>\<lparr>NTDom\<rparr> = \<NN>\<lparr>NTCod\<rparr>" 
    and [cat_cs_simps]: "inv_ntcf \<NN>\<lparr>NTCod\<rparr> = \<NN>\<lparr>NTDom\<rparr>"
    and [cat_cs_simps]: "inv_ntcf \<NN>\<lparr>NTDGDom\<rparr> = \<NN>\<lparr>NTDGDom\<rparr>" 
    and [cat_cs_simps]: "inv_ntcf \<NN>\<lparr>NTDGCod\<rparr> = \<NN>\<lparr>NTDGCod\<rparr>" 
  unfolding inv_ntcf_def nt_field_simps by (simp_all add: nat_omega_simps)


text\<open>Components.\<close>

lemma (in is_iso_ntcf) is_iso_ntcf_inv_ntcf_components[cat_cs_simps]: 
  "inv_ntcf \<NN>\<lparr>NTDom\<rparr> = \<GG>"
  "inv_ntcf \<NN>\<lparr>NTCod\<rparr> = \<FF>"
  "inv_ntcf \<NN>\<lparr>NTDGDom\<rparr> = \<AA>"
  "inv_ntcf \<NN>\<lparr>NTDGCod\<rparr> = \<BB>"
  unfolding inv_ntcf_components by (simp_all add: cat_cs_simps)


subsubsection\<open>Natural transformation map\<close>

lemma inv_ntcf_NTMap_vsv[cat_cs_intros]: "vsv (inv_ntcf \<NN>\<lparr>NTMap\<rparr>)"
  unfolding inv_ntcf_components by auto

lemma (in is_iso_ntcf) iso_ntcf_inv_ntcf_NTMap_app_is_inverse[cat_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "is_inverse \<BB> (inv_ntcf \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) (\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)"
proof-
  from assms is_iso_ntcf_axioms have "\<exists>g. is_inverse \<BB> g (\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)" by auto
  from assms someI2_ex[OF this] show 
    "is_inverse \<BB> (inv_ntcf \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) (\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)"
    unfolding inv_ntcf_components by (simp add: cat_cs_simps)
qed

lemma (in is_iso_ntcf) iso_ntcf_inv_ntcf_NTMap_app_is_the_inverse[cat_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "inv_ntcf \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)\<inverse>\<^sub>C\<^bsub>\<BB>\<^esub>"
proof- 
  have "is_inverse \<BB> (inv_ntcf \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) (\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)"
    by (rule iso_ntcf_inv_ntcf_NTMap_app_is_inverse[OF assms])
  from NTDom.HomCod.cat_is_inverse_eq_the_inverse[OF this] show ?thesis .
qed

lemmas [cat_cs_simps] = is_iso_ntcf.iso_ntcf_inv_ntcf_NTMap_app_is_the_inverse

lemma (in is_ntcf) inv_ntcf_NTMap_vdomain[cat_cs_simps]: 
  "\<D>\<^sub>\<circ> (inv_ntcf \<NN>\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
  unfolding inv_ntcf_components by (simp add: cat_cs_simps)

lemmas [cat_cs_simps] = is_ntcf.inv_ntcf_NTMap_vdomain

lemma (in is_iso_ntcf) inv_ntcf_NTMap_vrange: 
  "\<R>\<^sub>\<circ> (inv_ntcf \<NN>\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
proof(rule vsubsetI)
  interpret inv_\<NN>: vsv \<open>inv_ntcf \<NN>\<lparr>NTMap\<rparr>\<close> by (rule inv_ntcf_NTMap_vsv)
  fix f assume "f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (inv_ntcf \<NN>\<lparr>NTMap\<rparr>)"
  then obtain a 
    where f_def: "f = inv_ntcf \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>" and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (inv_ntcf \<NN>\<lparr>NTMap\<rparr>)"
    by (blast elim: inv_\<NN>.vrange_atE)
  then have "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" by (simp add: cat_cs_simps)
  then have "is_inverse \<BB> f (\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)" 
    unfolding f_def by (intro iso_ntcf_inv_ntcf_NTMap_app_is_inverse)    
  then show "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" by auto
qed


subsubsection\<open>Opposite natural isomorphism\<close>

lemma (in is_iso_ntcf) is_iso_ntcf_op: 
  "op_ntcf \<NN> : op_cf \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o op_cf \<FF> : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<BB>"
proof-
  from is_iso_ntcf_axioms have 
    "op_ntcf \<NN> : op_cf \<GG> \<mapsto>\<^sub>C\<^sub>F op_cf \<FF> : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat \<BB>"
    by (cs_concl cs_intro: cat_cs_intros cat_op_intros)
  then show ?thesis 
    by (intro is_iso_ntcfI) (auto simp: cat_op_simps cat_arrow_cs_intros)
qed

lemma (in is_iso_ntcf) is_iso_ntcf_op'[cat_op_intros]:
  assumes "\<GG>' = op_cf \<GG>"
    and "\<FF>' = op_cf \<FF>"
    and "\<AA>' = op_cat \<AA>"
    and "\<BB>' = op_cat \<BB>"
  shows "op_ntcf \<NN> : \<GG>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule is_iso_ntcf_op)

lemmas is_iso_ntcf_op[cat_op_intros] = is_iso_ntcf.is_iso_ntcf_op



subsection\<open>A natural isomorphism is an isomorphism in the category \<open>Funct\<close>\<close>

text\<open>
The results that are presented in this subsection can be found in 
nLab (see \cite{noauthor_nlab_nodate}\footnote{\url{
https://ncatlab.org/nlab/show/natural+isomorphism
}}).
\<close>

lemma is_arr_isomorphism_is_iso_ntcf:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<MM> = ntcf_id \<GG>"
    and "\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> = ntcf_id \<FF>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<MM>: is_ntcf \<alpha> \<AA> \<BB> \<GG> \<FF> \<MM> by (rule assms(2))
  show ?thesis
  proof(rule is_iso_ntcfI)
    fix a assume prems: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    show "\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    proof(rule is_arr_isomorphismI)
      show "is_inverse \<BB> (\<MM>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) (\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)"  
      proof(rule is_inverseI)
        from prems have 
          "\<MM>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
          by (simp add: ntcf_vcomp_NTMap_app[OF assms(2,1) prems])
        also have "\<dots> = ntcf_id \<FF>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>" unfolding assms(4) by simp
        also from prems \<NN>.NTDom.ntcf_id_NTMap_app_vdomain have 
          "\<dots> = \<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
          unfolding ntcf_id_components by auto
        finally show "\<MM>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>".
        from prems have 
          "\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<MM>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<MM>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
          by (simp add: ntcf_vcomp_NTMap_app[OF assms(1,2) prems])
        also have "\<dots> = ntcf_id \<GG>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>" unfolding assms(3) by simp
        also from prems \<NN>.NTCod.ntcf_id_NTMap_app_vdomain have 
          "\<dots> = \<BB>\<lparr>CId\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
          unfolding ntcf_id_components by auto
        finally show "\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<MM>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<BB>\<lparr>CId\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>".
      qed (auto simp: prems cat_cs_intros)
    qed (auto simp: prems cat_cs_intros)
  qed (auto simp: cat_cs_intros)
qed

lemma iso_ntcf_is_arr_isomorphism:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows [ntcf_cs_intros]: "inv_ntcf \<NN> : \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<NN> = ntcf_id \<GG>"
    and "inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> = ntcf_id \<FF>"
proof-

  interpret is_iso_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  
  define m where "m a = inv_ntcf \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>" for a
  have is_inverse[intro]: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<Longrightarrow> is_inverse \<BB> (m a) (\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)" 
    for a
    unfolding m_def by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  have [dest, intro, simp]: 
    "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<Longrightarrow> m a : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>" for a
  proof-
    assume prems: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    from prems have "\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>" 
      by (auto intro: cat_cs_intros cat_arrow_cs_intros)
    with is_inverse[OF prems] show "m a : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      by 
        (
          meson 
            NTDom.HomCod.cat_is_inverse_is_arr_isomorphism is_arr_isomorphismD
        )
  qed
  have [intro]: 
    "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b \<Longrightarrow> m b \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> m a"
    for f a b
  proof-
    assume prems: "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
    then have ma: "m a : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>" 
      and mb: "m b : \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      and \<GG>f: "\<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>" 
      and \<NN>a: "\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      and \<FF>f: "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      and \<NN>b: "\<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      by (auto intro: cat_cs_intros)
    then have \<NN>b\<FF>f: 
      "\<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      by (auto intro: cat_cs_intros)
    from prems have inv_ma: "is_inverse \<BB> (m a) (\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>)" 
      and inv_mb: "is_inverse \<BB> (\<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>) (m b)"
      by (auto simp: is_inverse_sym)
    from mb have mb_\<NN>b: "m b \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> = \<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<rparr>"
      by (auto intro: is_inverse_Comp_CId_right[OF inv_mb])
    from prems have \<NN>a_ma: "\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> m a = \<BB>\<lparr>CId\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>" 
      using \<NN>a inv_ma ma by (meson is_inverse_Comp_CId_right)
    from \<GG>f have "m b \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = 
      m b \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> (\<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> (\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> m a))"
      unfolding \<NN>a_ma by (cs_concl cs_simp: cat_cs_simps)
    also have "\<dots> = m b \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> ((\<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> m a)"
      by 
         (
          metis 
            ma \<GG>f \<NN>a NTDom.HomCod.cat_Comp_assoc is_arr_isomorphismD(1)
        )
    also from prems have 
      "\<dots> = m b \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> ((\<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>) \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> m a)"
      by (metis ntcf_Comp_commute)
    also have "\<dots> = (m b \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> (\<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>)) \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> m a"
      by 
        (
          metis 
            \<NN>b\<FF>f ma mb NTDom.HomCod.cat_Comp_assoc is_arr_isomorphismD(1)
        )
    also from \<FF>f \<NN>b mb NTDom.HomCod.cat_Comp_assoc have 
      "\<dots> =  ((m b \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>) \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>) \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> m a"
      by (metis is_arr_isomorphismD(1))
    also from \<FF>f have "\<dots> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> m a" 
      unfolding mb_\<NN>b by (simp add: cat_cs_simps)
    finally show "m b \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> m a" by simp
  qed

  show \<MM>: "inv_ntcf \<NN> : \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  proof(intro is_iso_ntcfI is_ntcfI', unfold m_def[symmetric])
    show "vfsequence (inv_ntcf \<NN>)" unfolding inv_ntcf_def by simp
    show "vcard (inv_ntcf \<NN>) = 5\<^sub>\<nat>"
      unfolding inv_ntcf_def by (simp add: nat_omega_simps)
  qed (auto simp: cat_cs_simps intro: cat_cs_intros)

  interpret \<MM>: is_iso_ntcf \<alpha> \<AA> \<BB> \<GG> \<FF> \<open>inv_ntcf \<NN>\<close> by (rule \<MM>)

  show \<NN>\<MM>: "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<NN> = ntcf_id \<GG>"
  proof(rule ntcf_eqI)
    from NTCod.cf_ntcf_id_is_ntcf show "ntcf_id \<GG> : \<GG> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      by auto
    show "(\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<NN>)\<lparr>NTMap\<rparr> = ntcf_id \<GG>\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI)
      fix a assume "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<NN>)\<lparr>NTMap\<rparr>)"
      then have "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
        unfolding ntcf_vcomp_NTMap_vdomain[OF \<MM>.is_ntcf_axioms] by simp
      then show "(\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = ntcf_id \<GG>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps 
              cs_intro: cat_cs_intros cat_arrow_cs_intros
          )
    qed 
      (
        auto 
          simp: ntsmcf_vcomp_components(1) cat_cs_simps 
          intro: cat_cs_intros
      )
  qed (auto intro: cat_cs_intros)
    
  show \<MM>\<NN>: "inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> = ntcf_id \<FF>"
  proof(rule ntcf_eqI)
    show "(inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr> = ntcf_id \<FF>\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI)
      show "\<D>\<^sub>\<circ> ((inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>) = \<D>\<^sub>\<circ> (ntcf_id \<FF>\<lparr>NTMap\<rparr>)" 
        by (simp add: ntsmcf_vcomp_components(1) cat_cs_simps)
      fix a assume "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>)"
      then have "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
        unfolding ntsmcf_vcomp_components by (simp add: cat_cs_simps)    
      then show "(inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = ntcf_id \<FF>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps 
              cs_intro: cat_cs_intros cat_arrow_cs_intros
          )
    qed 
      (
        auto simp: 
          ntsmcf_vcomp_components(1) 
          ntcf_id_components(1) 
          cat_cs_simps 
          intro: vsv_vcomp
      )
  qed (auto intro: cat_cs_intros)
qed


subsubsection\<open>Vertical composition of natural isomorphisms\<close>

lemma ntcf_vcomp_is_iso_ntcf[cat_cs_intros]:
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
proof(intro is_arr_isomorphism_is_iso_ntcf)
  note inv_ntcf_\<MM> = iso_ntcf_is_arr_isomorphism[OF assms(1)]
    and inv_ntcf_\<NN> = iso_ntcf_is_arr_isomorphism[OF assms(2)]
  note [cat_cs_simps] = inv_ntcf_\<MM>(2,3) inv_ntcf_\<NN>(2,3)
  from assms show "\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: cat_cs_intros ntcf_cs_intros)
  from inv_ntcf_\<MM>(1) inv_ntcf_\<NN>(1) show 
    "inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<MM> : \<HH> \<mapsto>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: cat_cs_intros ntcf_cs_intros)
  from assms inv_ntcf_\<MM>(1) inv_ntcf_\<NN>(1) have 
    "\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<MM>) = 
      \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<NN>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<MM>"
    by 
      (
        cs_concl
          cs_simp: ntcf_vcomp_assoc cs_intro: cat_cs_intros ntcf_cs_intros
      )
  also from assms have "\<dots> = ntcf_id \<HH>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: ntcf_cs_intros)
  finally show "\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<MM>) = ntcf_id \<HH>"
    by simp
  from assms inv_ntcf_\<MM>(1) inv_ntcf_\<NN>(1) have 
    "inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) = 
      inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (inv_ntcf \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<MM>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>"
    by 
      (
        cs_concl 
          cs_simp: ntcf_vcomp_assoc cs_intro: cat_cs_intros ntcf_cs_intros
      )
  also from assms have "\<dots> = ntcf_id \<FF>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: ntcf_cs_intros)
  finally show "inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) = ntcf_id \<FF>"
    by simp
qed


subsubsection\<open>Horizontal composition of natural isomorphisms\<close>

lemma ntcf_hcomp_is_iso_ntcf:
  assumes "\<MM> : \<FF>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<FF>' \<circ>\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG>' \<circ>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_arr_isomorphism_is_iso_ntcf)
  note inv_ntcf_\<MM> = iso_ntcf_is_arr_isomorphism[OF assms(1)]
    and inv_ntcf_\<NN> = iso_ntcf_is_arr_isomorphism[OF assms(2)]
  note [cat_cs_simps] = inv_ntcf_\<MM>(2,3) inv_ntcf_\<NN>(2,3)
  from assms show "\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<FF>' \<circ>\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG>' \<circ>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: cat_cs_intros ntcf_cs_intros)
  from inv_ntcf_\<MM>(1) inv_ntcf_\<NN>(1) show 
    "inv_ntcf \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<NN> : \<GG>' \<circ>\<^sub>C\<^sub>F \<GG> \<mapsto>\<^sub>C\<^sub>F \<FF>' \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: cat_cs_intros ntcf_cs_intros)
  from assms inv_ntcf_\<MM>(1) inv_ntcf_\<NN>(1) have 
    "\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (inv_ntcf \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<NN>) = 
      ntcf_id \<GG>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<GG>"
    by 
      (
        cs_concl 
          cs_simp: ntcf_comp_interchange_law[symmetric] cat_cs_simps 
          cs_intro: ntcf_cs_intros
      )
  also from assms have "\<dots> = ntcf_id (\<GG>' \<circ>\<^sub>C\<^sub>F \<GG>)"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros ntcf_cs_intros)
  finally show 
    "\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (inv_ntcf \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<NN>) = ntcf_id (\<GG>' \<circ>\<^sub>C\<^sub>F \<GG>)"
    by simp
  from assms inv_ntcf_\<MM>(1) inv_ntcf_\<NN>(1) have 
    "inv_ntcf \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) = 
      ntcf_id \<FF>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF>"
    by 
      (
        cs_concl 
          cs_simp: ntcf_comp_interchange_law[symmetric] cat_cs_simps
          cs_intro: ntcf_cs_intros
      )
  also from assms have "\<dots> = ntcf_id (\<FF>' \<circ>\<^sub>C\<^sub>F \<FF>)"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros ntcf_cs_intros)
  finally show 
    "inv_ntcf \<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) = ntcf_id (\<FF>' \<circ>\<^sub>C\<^sub>F \<FF>)"
    by simp
qed

lemma ntcf_hcomp_is_iso_ntcf'[ntcf_cs_intros]:
  assumes "\<MM> : \<FF>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<HH>' = \<FF>' \<circ>\<^sub>C\<^sub>F \<FF>"
    and "\<HH>'' = \<GG>' \<circ>\<^sub>C\<^sub>F \<GG>"
  shows "\<MM> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<HH>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<HH>'' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1,2) unfolding assms(3,4) by (rule ntcf_hcomp_is_iso_ntcf)


subsubsection\<open>An identity natural transformation is a natural isomorphism\<close>

lemma (in is_functor) cf_ntcf_id_is_iso_ntcf:
  "ntcf_id \<FF> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  have "ntcf_id \<FF> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by (auto intro: cat_cs_intros)
  moreover then have "ntcf_id \<FF> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<FF> = ntcf_id \<FF>" 
    by (cs_concl cs_simp: cat_cs_simps)
  ultimately show ?thesis by (auto intro: is_arr_isomorphism_is_iso_ntcf)
qed

lemma (in is_functor) cf_ntcf_id_is_iso_ntcf'[ntcf_cs_intros]:
  assumes "\<GG>' = \<FF>" and "\<HH>' = \<FF>"
  shows "ntcf_id \<FF> : \<GG>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<HH>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  unfolding assms by (rule cf_ntcf_id_is_iso_ntcf)

lemmas [ntcf_cs_intros] = is_functor.cf_ntcf_id_is_iso_ntcf'



subsection\<open>Functor isomorphism\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See subsection 1.5 in \cite{bodo_categories_1970}.\<close>

locale iso_functor =
  fixes \<alpha> \<FF> \<GG>
  assumes iso_cf_is_iso_ntcf: "\<exists>\<AA> \<BB> \<NN>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"

notation iso_functor (infixl "\<approx>\<^sub>C\<^sub>F\<index>" 50)


text\<open>Rules.\<close>

lemma iso_functorI:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<FF> \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> \<GG>"
  using assms unfolding iso_functor_def by auto

lemma iso_functorD[dest]:
  assumes "\<FF> \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> \<GG>"
  shows "\<exists>\<AA> \<BB> \<NN>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms unfolding iso_functor_def by auto

lemma iso_functorE[elim]:
  assumes "\<FF> \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> \<GG>"
  obtains \<AA> \<BB> \<NN> where "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms unfolding iso_functor_def by auto


subsubsection\<open>A functor isomorphism is an equivalence relation\<close>

lemma iso_functor_refl: 
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<FF> \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> \<FF>"
proof(rule iso_functorI)
  from assms show "ntcf_id \<FF> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: ntcf_cs_intros)
qed

lemma iso_functor_sym[sym]:
  assumes "\<FF> \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> \<GG>"
  shows "\<GG> \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> \<FF>"
proof-
  from assms obtain \<AA> \<BB> \<NN> where \<NN>: "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by auto
  from iso_ntcf_is_arr_isomorphism(1)[OF \<NN>] show "\<GG> \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> \<FF>" 
    by (auto simp: iso_functorI)
qed

lemma iso_functor_trans[trans, intro]:
  assumes "\<FF> \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> \<GG>" and "\<GG> \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> \<HH>"
  shows "\<FF> \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> \<HH>"
proof-
  from assms(1) obtain \<AA> \<BB> \<NN> where \<NN>: "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    by auto
  moreover from assms(2) obtain \<AA>' \<BB>' \<MM>
    where \<MM>: "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<HH> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'" 
    by auto
  ultimately have "\<GG> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'" and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by blast+
  then have eq: "\<AA>' = \<AA>" "\<BB>' = \<BB>" by auto
  from \<MM> have \<MM>: "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" unfolding eq .
  from ntcf_vcomp_is_iso_ntcf[OF \<MM> \<NN>] show ?thesis by (rule iso_functorI)
qed


subsubsection\<open>Opposite functor isomorphism\<close>

lemma (in iso_functor) iso_functor_op: "op_cf \<FF> \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> op_cf \<GG>"
proof-
  from iso_functor_axioms obtain \<AA> \<BB> \<NN> where "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by auto
  from is_iso_ntcf_op[OF this] have "op_cf \<GG> \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> op_cf \<FF>" 
    by (auto simp: iso_functorI)
  then show "op_cf \<FF> \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> op_cf \<GG>" by (rule iso_functor_sym)
qed

lemmas iso_functor_op[cat_op_intros] = iso_functor.iso_functor_op

text\<open>\newpage\<close>

end