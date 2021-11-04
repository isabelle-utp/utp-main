(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>Rel\<close>\<close>
theory CZH_ECAT_Rel
  imports 
    CZH_Foundations.CZH_SMC_Rel
    CZH_ECAT_Functor
    CZH_ECAT_Small_Category
begin



subsection\<open>Background\<close>


text\<open>
The methodology chosen for the exposition of \<open>Rel\<close> as a category is analogous 
to the one used in \cite{milehins_category_2021} 
for the exposition of \<open>Rel\<close> as a semicategory. 
The general references for this section are Chapter I-7 in 
\cite{mac_lane_categories_2010} and nLab 
\cite{noauthor_nlab_nodate}\footnote{
\url{https://ncatlab.org/nlab/show/Rel}
}.
\<close>

named_theorems cat_Rel_cs_simps
named_theorems cat_Rel_cs_intros

lemmas (in arr_Rel) [cat_Rel_cs_simps] = 
  dg_Rel_shared_cs_simps

lemmas [cat_Rel_cs_simps] = 
  dg_Rel_shared_cs_simps
  arr_Rel.arr_Rel_length
  arr_Rel_comp_Rel_id_Rel_left
  arr_Rel_comp_Rel_id_Rel_right
  arr_Rel.arr_Rel_converse_Rel_converse_Rel
  arr_Rel_converse_Rel_eq_iff
  arr_Rel_converse_Rel_comp_Rel
  arr_Rel_comp_Rel_converse_Rel_left_if_v11
  arr_Rel_comp_Rel_converse_Rel_right_if_v11

lemmas [cat_Rel_cs_intros] = 
  dg_Rel_shared_cs_intros
  arr_Rel_comp_Rel
  arr_Rel.arr_Rel_converse_Rel



subsection\<open>\<open>Rel\<close> as a category\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition cat_Rel :: "V \<Rightarrow> V"
  where "cat_Rel \<alpha> =
    [
      Vset \<alpha>,
      set {T. arr_Rel \<alpha> T},
      (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Rel \<alpha> T}. T\<lparr>ArrDom\<rparr>),
      (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Rel \<alpha> T}. T\<lparr>ArrCod\<rparr>),
      (\<lambda>ST\<in>\<^sub>\<circ>composable_arrs (dg_Rel \<alpha>). ST\<lparr>0\<rparr> \<circ>\<^sub>R\<^sub>e\<^sub>l ST\<lparr>1\<^sub>\<nat>\<rparr>),
      VLambda (Vset \<alpha>) id_Rel 
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cat_Rel_components:
  shows "cat_Rel \<alpha>\<lparr>Obj\<rparr> = Vset \<alpha>"
    and "cat_Rel \<alpha>\<lparr>Arr\<rparr> = set {T. arr_Rel \<alpha> T}"
    and "cat_Rel \<alpha>\<lparr>Dom\<rparr> = (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Rel \<alpha> T}. T\<lparr>ArrDom\<rparr>)"
    and "cat_Rel \<alpha>\<lparr>Cod\<rparr> = (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Rel \<alpha> T}. T\<lparr>ArrCod\<rparr>)"
    and "cat_Rel \<alpha>\<lparr>Comp\<rparr> = (\<lambda>ST\<in>\<^sub>\<circ>composable_arrs (dg_Rel \<alpha>). ST\<lparr>0\<rparr> \<circ>\<^sub>R\<^sub>e\<^sub>l ST\<lparr>1\<^sub>\<nat>\<rparr>)"
    and "cat_Rel \<alpha>\<lparr>CId\<rparr> = VLambda (Vset \<alpha>) id_Rel"
  unfolding cat_Rel_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma cat_smc_cat_Rel: "cat_smc (cat_Rel \<alpha>) = smc_Rel \<alpha>"
proof(rule vsv_eqI)
  show "vsv (cat_smc (cat_Rel \<alpha>))" unfolding cat_smc_def by auto
  show "vsv (smc_Rel \<alpha>)" unfolding smc_Rel_def by auto
  have dom_lhs: "\<D>\<^sub>\<circ> (cat_smc (cat_Rel \<alpha>)) = 5\<^sub>\<nat>" 
    unfolding cat_smc_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (smc_Rel \<alpha>) = 5\<^sub>\<nat>"
    unfolding smc_Rel_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (cat_smc (cat_Rel \<alpha>)) = \<D>\<^sub>\<circ> (smc_Rel \<alpha>)"
    unfolding dom_lhs dom_rhs by simp
  show 
    "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (cat_smc (cat_Rel \<alpha>)) \<Longrightarrow> cat_smc (cat_Rel \<alpha>)\<lparr>a\<rparr> = smc_Rel \<alpha>\<lparr>a\<rparr>"
    for a
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral, 
        unfold cat_smc_def dg_field_simps cat_Rel_def smc_Rel_def
      )
      (auto simp: nat_omega_simps)
qed

lemmas_with [folded cat_smc_cat_Rel, unfolded slicing_simps]: 
  cat_Rel_Obj_iff = smc_Rel_Obj_iff
  and cat_Rel_Arr_iff[cat_Rel_cs_simps] = smc_Rel_Arr_iff
  and cat_Rel_Dom_vsv[cat_Rel_cs_intros] = smc_Rel_Dom_vsv
  and cat_Rel_Dom_vdomain[cat_Rel_cs_simps] = smc_Rel_Dom_vdomain
  and cat_Rel_Dom_app[cat_Rel_cs_simps] = smc_Rel_Dom_app
  and cat_Rel_Dom_vrange = smc_Rel_Dom_vrange
  and cat_Rel_Cod_vsv[cat_Rel_cs_intros] = smc_Rel_Cod_vsv
  and cat_Rel_Cod_vdomain[cat_Rel_cs_simps] = smc_Rel_Cod_vdomain
  and cat_Rel_Cod_app[cat_Rel_cs_simps] = smc_Rel_Cod_app
  and cat_Rel_Cod_vrange = smc_Rel_Cod_vrange
  and cat_Rel_is_arrI[cat_Rel_cs_intros] = smc_Rel_is_arrI
  and cat_Rel_is_arrD = smc_Rel_is_arrD
  and cat_Rel_is_arrE = smc_Rel_is_arrE

lemmas_with [folded cat_smc_cat_Rel, unfolded slicing_simps, unfolded cat_smc_cat_Rel]: 
  cat_Rel_composable_arrs_dg_Rel = smc_Rel_composable_arrs_dg_Rel
  and cat_Rel_Comp = smc_Rel_Comp
  and cat_Rel_Comp_app[cat_Rel_cs_simps] = smc_Rel_Comp_app
  and cat_Rel_Comp_vdomain[simp] = smc_Rel_Comp_vdomain

lemmas [cat_cs_simps] = cat_Rel_is_arrD(2,3)

lemmas [cat_Rel_cs_intros] = cat_Rel_is_arrI

lemmas_with (in \<Z>) [folded cat_smc_cat_Rel, unfolded slicing_simps]: 
  cat_Rel_Hom_vifunion_in_Vset = smc_Rel_Hom_vifunion_in_Vset
  and cat_Rel_incl_Rel_is_arr = smc_Rel_incl_Rel_is_arr
  and cat_Rel_incl_Rel_is_arr'[cat_Rel_cs_intros] = smc_Rel_incl_Rel_is_arr'
  and cat_CAT_Comp_vrange = smc_CAT_Comp_vrange
  and cat_Rel_is_monic_arrI = smc_Rel_is_monic_arrI
  and cat_Rel_is_monic_arrD = smc_Rel_is_monic_arrD
  and cat_Rel_is_monic_arr = smc_Rel_is_monic_arr
  and cat_Rel_is_monic_arr_is_epic_arr = smc_Rel_is_monic_arr_is_epic_arr
  and cat_Rel_is_epic_arr_is_monic_arr = smc_Rel_is_epic_arr_is_monic_arr
  and cat_Rel_is_epic_arrI = smc_Rel_is_epic_arrI
  and cat_Rel_is_epic_arrD = smc_Rel_is_epic_arrD
  and cat_Rel_is_epic_arr = smc_Rel_is_epic_arr
  and cat_Rel_obj_terminal = smc_Rel_obj_terminal
  and cat_Rel_obj_initial = smc_Rel_obj_initial
  and cat_Rel_obj_terminal_obj_initial = smc_Rel_obj_terminal_obj_initial
  and cat_Rel_obj_null = smc_Rel_obj_null
  and cat_Rel_is_zero_arr = smc_Rel_is_zero_arr

lemmas [cat_Rel_cs_intros] = \<Z>.cat_Rel_incl_Rel_is_arr'


subsubsection\<open>Identity\<close>

lemma (in \<Z>) cat_Rel_CId_app[cat_Rel_cs_simps]:
  assumes "T \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>T\<rparr> = id_Rel T"
  using assms unfolding cat_Rel_components by simp

lemmas [cat_Rel_cs_simps] = \<Z>.cat_Rel_CId_app


subsubsection\<open>\<open>Rel\<close> is a category\<close>

lemma (in \<Z>) category_cat_Rel: "category \<alpha> (cat_Rel \<alpha>)"
proof(rule categoryI, unfold cat_smc_cat_Rel)

  interpret Rel: semicategory \<alpha> \<open>cat_smc (cat_Rel \<alpha>)\<close>
    unfolding cat_smc_cat_Rel by (simp add: semicategory_smc_Rel)

  show "vfsequence (cat_Rel \<alpha>)" unfolding cat_Rel_def by simp
  show "vcard (cat_Rel \<alpha>) = 6\<^sub>\<nat>"
    unfolding cat_Rel_def by (simp add: nat_omega_simps)
  show "cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr> : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> A"
    if "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" for A
    using that 
    unfolding cat_Rel_Obj_iff
    by 
      (
        cs_concl 
          cs_simp: cat_Rel_cs_simps cs_intro: cat_Rel_cs_intros arr_Rel_id_RelI 
      )
  show "cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>B\<rparr> \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> F = F"
    if "F : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B" for F A B
  proof-
    from that have "arr_Rel \<alpha> F" "A \<in>\<^sub>\<circ> Vset \<alpha>" "B \<in>\<^sub>\<circ> Vset \<alpha>"
      by (auto elim: cat_Rel_is_arrE simp: cat_Rel_cs_simps)
    with that show ?thesis
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_Rel_cs_simps 
            cs_intro: cat_Rel_cs_intros arr_Rel_id_RelI
        )
  qed
  
  show "F \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>B\<rparr> = F"
    if "F : B \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> C" for F B C
  proof-
    from that have "arr_Rel \<alpha> F" "B \<in>\<^sub>\<circ> Vset \<alpha>" "C \<in>\<^sub>\<circ> Vset \<alpha>"
      by (auto elim: cat_Rel_is_arrE simp: cat_Rel_cs_simps)
    with that show ?thesis
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_Rel_cs_simps
            cs_intro: cat_Rel_cs_intros arr_Rel_id_RelI
        )
  qed

qed (auto simp: semicategory_smc_Rel cat_Rel_components)

lemma (in \<Z>) category_cat_Rel'[cat_Rel_cs_intros]: 
  assumes "\<alpha>' = \<alpha>" and "\<alpha>'' = \<alpha>"
  shows "category \<alpha>' (cat_Rel \<alpha>'')"
  unfolding assms by (rule category_cat_Rel)

lemmas [cat_Rel_cs_intros] = \<Z>.category_cat_Rel'



subsection\<open>Canonical dagger for \<open>Rel\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition cf_dag_Rel :: "V \<Rightarrow> V" (\<open>\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l\<close>)
  where "\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> = 
    [
      vid_on (cat_Rel \<alpha>\<lparr>Obj\<rparr>), 
      VLambda (cat_Rel \<alpha>\<lparr>Arr\<rparr>) converse_Rel, 
      op_cat (cat_Rel \<alpha>), 
      cat_Rel \<alpha>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_dag_Rel_components:
  shows "\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr> = vid_on (cat_Rel \<alpha>\<lparr>Obj\<rparr>)"
    and "\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr> = VLambda (cat_Rel \<alpha>\<lparr>Arr\<rparr>) converse_Rel"
    and "\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>HomDom\<rparr> = op_cat (cat_Rel \<alpha>)"
    and "\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>HomCod\<rparr> = cat_Rel \<alpha>"
  unfolding cf_dag_Rel_def dghm_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma cf_smcf_cf_dag_Rel: "cf_smcf (\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>) = \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> (cf_smcf (\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)) = 4\<^sub>\<nat>" 
    unfolding cf_smcf_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>) = 4\<^sub>\<nat>"
    unfolding smcf_dag_Rel_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (cf_smcf (\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)) = \<D>\<^sub>\<circ> (\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)"
    unfolding dom_lhs dom_rhs by simp
  show "A \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (cf_smcf (\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)) \<Longrightarrow> cf_smcf (\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)\<lparr>A\<rparr> = \<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>A\<rparr>"
    for A
    by
      (
        unfold dom_lhs,
        elim_in_numeral,
        unfold dghm_field_simps[symmetric],
        unfold 
          cat_smc_cat_Rel
          slicing_commute[symmetric]
          cf_smcf_components 
          smcf_dag_Rel_components
          cf_dag_Rel_components
          smc_Rel_components
          cat_Rel_components
      )
      simp_all
qed (auto simp: cf_smcf_def smcf_dag_Rel_def) 

lemmas_with [folded cat_smc_cat_Rel cf_smcf_cf_dag_Rel, unfolded slicing_simps]: 
  cf_dag_Rel_ObjMap_vsv[cat_Rel_cs_intros] = smcf_dag_Rel_ObjMap_vsv
  and cf_dag_Rel_ObjMap_vdomain[cat_Rel_cs_simps] = smcf_dag_Rel_ObjMap_vdomain
  and cf_dag_Rel_ObjMap_app[cat_Rel_cs_simps] = smcf_dag_Rel_ObjMap_app
  and cf_dag_Rel_ObjMap_vrange[cat_Rel_cs_simps] = smcf_dag_Rel_ObjMap_vrange
  and cf_dag_Rel_ArrMap_vsv[cat_Rel_cs_intros] = smcf_dag_Rel_ArrMap_vsv
  and cf_dag_Rel_ArrMap_vdomain[cat_Rel_cs_simps] = smcf_dag_Rel_ArrMap_vdomain
  and cf_dag_Rel_ArrMap_app[cat_Rel_cs_simps] = smcf_dag_Rel_ArrMap_app
  and cf_dag_Rel_ArrMap_vrange[cat_Rel_cs_simps] = smcf_dag_Rel_ArrMap_vrange

lemmas_with (in \<Z>) [
  folded cat_smc_cat_Rel cf_smcf_cf_dag_Rel, unfolded slicing_simps
  ]: 
  cf_dag_Rel_app_is_arr[cat_Rel_cs_intros] = smcf_dag_Rel_app_is_arr
  and cf_dag_Rel_ArrMap_smc_Rel_Comp[cat_Rel_cs_simps] = 
    smcf_dag_Rel_ArrMap_smc_Rel_Comp


subsubsection\<open>Canonical dagger is a contravariant isomorphism of \<open>Rel\<close>\<close>

lemma (in \<Z>) cf_dag_Rel_is_iso_functor: 
  "\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> : op_cat (cat_Rel \<alpha>) \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> cat_Rel \<alpha>"
proof
  (
    rule is_iso_functorI, 
    unfold 
      cat_smc_cat_Rel 
      cf_smcf_cf_dag_Rel 
      cat_Rel_components 
      cat_op_simps 
      slicing_commute[symmetric]
  )

  interpret is_iso_semifunctor \<alpha> \<open>op_smc (smc_Rel \<alpha>)\<close> \<open>smc_Rel \<alpha>\<close> \<open>\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<close>
    by (rule smcf_dag_Rel_is_iso_semifunctor)
  interpret Rel: category \<alpha> \<open>cat_Rel \<alpha>\<close> by (rule category_cat_Rel)
  
  show "\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> : op_cat (cat_Rel \<alpha>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Rel \<alpha>"
  proof
    (
      rule is_functorI, 
      unfold 
        cat_smc_cat_Rel 
        cf_smcf_cf_dag_Rel 
        cat_op_simps 
        slicing_commute[symmetric] 
        cf_dag_Rel_components(3,4)
    )
    show "vfsequence (\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)"
      unfolding cf_dag_Rel_def by (simp add: nat_omega_simps)
    show "vcard (\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>) = 4\<^sub>\<nat>" 
      unfolding cf_dag_Rel_def by (simp add: nat_omega_simps)
    show "\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>C\<rparr>\<rparr> = cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>\<lparr>C\<rparr>\<rparr>"
      if "C \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" for C
    proof-
      from that have "C \<in>\<^sub>\<circ> Vset \<alpha>" 
        by (auto elim: cat_Rel_is_arrE simp: cat_Rel_Obj_iff)
      with that show ?thesis
        by 
          (
            cs_concl 
              cs_simp: cat_Rel_cs_simps cs_intro: cat_cs_intros arr_Rel_id_RelI
          )
    qed
  qed (auto simp: cat_cs_intros intro: smc_cs_intros)

  show "\<dagger>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> : op_smc (smc_Rel \<alpha>) \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> smc_Rel \<alpha>"
    by (rule smcf_dag_Rel_is_iso_semifunctor)

qed

lemma (in \<Z>) cf_dag_Rel_is_iso_functor'[cat_cs_intros]: 
  assumes "\<AA>' = op_cat (cat_Rel \<alpha>)"
    and "\<BB>' = cat_Rel \<alpha>"
    and "\<alpha>' = \<alpha>"
  shows "\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule cf_dag_Rel_is_iso_functor)

lemmas [cat_cs_intros] = \<Z>.cf_dag_Rel_is_iso_functor'


subsubsection\<open>Further properties of the canonical dagger\<close>

lemma (in \<Z>) cf_cn_comp_cf_dag_Rel_cf_dag_Rel: 
  "\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> \<^sub>C\<^sub>F\<circ> \<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> = cf_id (cat_Rel \<alpha>)"
proof(rule cf_smcf_eqI)
  interpret category \<alpha> \<open>cat_Rel \<alpha>\<close> by (rule category_cat_Rel)
  from cf_dag_Rel_is_iso_functor have dag:
    "\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> : op_cat (cat_Rel \<alpha>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Rel \<alpha>"
    by (simp add: is_iso_functor.axioms(1))
  from cf_cn_comp_is_functorI[OF category_axioms dag dag] show 
    "\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> \<^sub>C\<^sub>F\<circ> \<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> : cat_Rel \<alpha> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Rel \<alpha>" .
  show "cf_id (cat_Rel \<alpha>) : cat_Rel \<alpha> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Rel \<alpha>"
    by (auto simp: category.cat_cf_id_is_functor category_axioms)
  show "cf_smcf (\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> \<^sub>C\<^sub>F\<circ> \<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>) = cf_smcf (smcf_id (cat_Rel \<alpha>))"
    unfolding slicing_commute[symmetric] cat_smc_cat_Rel cf_smcf_cf_dag_Rel
    by (simp add: smcf_cn_comp_smcf_dag_Rel_smcf_dag_Rel)
qed simp_all



subsection\<open>Isomorphism\<close>

context \<Z>
begin

context
begin

private lemma cat_Rel_is_arr_isomorphism_right_vsubset:
  assumes "S : B \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> A"
    and "T : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B"
    and "S \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> T = cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr>"
    and "T \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> S = cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>B\<rparr>"
  shows "S\<lparr>ArrVal\<rparr> \<subseteq>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)\<inverse>\<^sub>\<circ>"
proof(rule vsubset_antisym vsubsetI)

  interpret Rel: category \<alpha> \<open>cat_Rel \<alpha>\<close> by (simp add: category_cat_Rel)

  interpret S: arr_Rel \<alpha> S
    rewrites "S\<lparr>ArrDom\<rparr> = B" and "S\<lparr>ArrCod\<rparr> = A"
    using assms(1)
    by (all\<open>elim Rel.cat_is_arrE\<close>) (simp_all add: cat_Rel_components)
  interpret T: arr_Rel \<alpha> T
    rewrites "T\<lparr>ArrDom\<rparr> = A" and "T\<lparr>ArrCod\<rparr> = B"
    using assms(2)
    by (all\<open>elim Rel.cat_is_arrE\<close>) (simp_all add: cat_Rel_components)
  interpret dag: is_iso_functor \<alpha> \<open>op_cat (cat_Rel \<alpha>)\<close> \<open>cat_Rel \<alpha>\<close> \<open>\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<close>
    by (auto simp: cf_dag_Rel_is_iso_functor)

  from assms(2) have A: "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" by auto
  from assms(3) have "(S \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> T)\<lparr>ArrVal\<rparr> = cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr>\<lparr>ArrVal\<rparr>"
    by simp
  with A have [simp]: "S\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> T\<lparr>ArrVal\<rparr> = vid_on A"
    unfolding cat_Rel_Comp_app[OF assms(1,2)]
    by (simp add: id_Rel_components comp_Rel_components cat_Rel_components)

  from assms(2) have B: "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" by auto
  from assms(4) have "(T \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> S)\<lparr>ArrVal\<rparr> = cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>B\<rparr>\<lparr>ArrVal\<rparr>"
    by simp
  with B have [simp]: "T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> S\<lparr>ArrVal\<rparr> = vid_on B"
    unfolding cat_Rel_Comp_app[OF assms(2,1)]
    by (simp add: id_Rel_components comp_Rel_components cat_Rel_components)

  fix ab assume ab: "ab \<in>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>"
  with S.vbrelation obtain a b where ab_def: "ab = \<langle>a, b\<rangle>" and "a \<in>\<^sub>\<circ> B" 
    by (metis S.arr_Rel_ArrVal_vdomain S.ArrVal.vbrelation_vinE vsubsetE)
  then have "\<langle>a, a\<rangle> \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>" by auto
  then obtain c where "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>" and ca[intro]: "\<langle>c, a\<rangle> \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>" 
    by blast
  have "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>"
  proof(rule ccontr)
    assume "\<langle>b, a\<rangle> \<notin>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>"
    with ca have "c \<noteq> b" by clarsimp
    moreover from ab have "\<langle>c, b\<rangle> \<in>\<^sub>\<circ> S\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>" 
      unfolding ab_def by blast
    ultimately show False by (simp add: vid_on_iff)
  qed
  then show "ab \<in>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)\<inverse>\<^sub>\<circ>" unfolding ab_def by clarsimp

qed

private lemma cat_Rel_is_arr_isomorphism_left_vsubset:
  assumes "S : B \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> A" 
    and "T : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B" 
    and "S \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> T = cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr>"
    and "T \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> S = cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>B\<rparr>"
  shows "(T\<lparr>ArrVal\<rparr>)\<inverse>\<^sub>\<circ> \<subseteq>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>"
  using assms(2,3,4) cat_Rel_is_arr_isomorphism_right_vsubset[OF assms(2,1)] 
  by auto

private lemma is_arr_isomorphism_dag: 
  assumes "S : B \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> A" 
    and "T : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B" 
    and "S \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> T = cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr>"
    and "T \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> S = cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>B\<rparr>"
  shows "S = \<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr>"
proof(rule arr_Rel_eqI[of \<alpha>])
  interpret Rel: category \<alpha> \<open>cat_Rel \<alpha>\<close> by (rule category_cat_Rel)
  interpret dag: is_iso_functor \<alpha> \<open>op_cat (cat_Rel \<alpha>)\<close> \<open>cat_Rel \<alpha>\<close> \<open>\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<close>
    by (auto simp: cf_dag_Rel_is_iso_functor)
  from assms(1) show S: "arr_Rel \<alpha> S" by (fastforce simp: cat_Rel_components(2))
  from cf_dag_Rel_app_is_arr[OF assms(2)] show "arr_Rel \<alpha> (\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr>)"
    by (auto elim!: cat_Rel_is_arrE)
  from assms(2) have T: "arr_Rel \<alpha> T" by (auto simp: cat_Rel_is_arrD(1))
  from S T assms show "S\<lparr>ArrVal\<rparr> = \<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr>\<lparr>ArrVal\<rparr>"
    unfolding cf_dag_Rel_ArrMap_app[OF T] converse_Rel_components
    by (intro vsubset_antisym) 
      (
        simp_all add: 
          cat_Rel_is_arr_isomorphism_left_vsubset 
          cat_Rel_is_arr_isomorphism_right_vsubset
      )
  from T assms show "S\<lparr>ArrDom\<rparr> = \<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr>\<lparr>ArrDom\<rparr>"
    unfolding cf_dag_Rel_components 
    by (auto simp: cat_cs_simps cat_Rel_cs_simps converse_Rel_components(1))
  from S assms show "S\<lparr>ArrCod\<rparr> = \<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr>\<lparr>ArrCod\<rparr>"
    by 
      (
        cs_concl 
          cs_intro: cat_op_intros cat_cs_intros 
          cs_simp: cat_Rel_cs_simps cat_cs_simps
      )
qed

lemma cat_Rel_is_arr_isomorphismI[intro]:
  assumes "T : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B" 
    and "v11 (T\<lparr>ArrVal\<rparr>)"
    and "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A"
    and "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B"
  shows "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Rel \<alpha>\<^esub> B"
proof(rule is_arr_isomorphismI[where ?g = \<open>\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr>\<close>])

  interpret Rel: category \<alpha> \<open>cat_Rel \<alpha>\<close> by (rule category_cat_Rel)
  interpret v11: v11 \<open>T\<lparr>ArrVal\<rparr>\<close> by (rule assms(2))

  interpret T: arr_Rel \<alpha> T
    rewrites [simp]: "T\<lparr>ArrDom\<rparr> = A" and [simp]: "T\<lparr>ArrCod\<rparr> = B"
    using assms(1) 
    by (all\<open>elim cat_Rel_is_arrE\<close>) (simp_all add: cat_Rel_components)
  interpret is_iso_functor \<alpha> \<open>op_cat (cat_Rel \<alpha>)\<close> \<open>cat_Rel \<alpha>\<close> \<open>\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<close>
    by (simp add: cf_dag_Rel_is_iso_functor)

  show "T : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B" by (rule assms(1))

  show "is_inverse (cat_Rel \<alpha>) (\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr>) T"
  proof(intro is_inverseI)
    from assms(1) show dag_T: "\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr> : B \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> A"
      by 
        (
          cs_concl 
            cs_simp: cat_op_simps cat_Rel_cs_simps 
            cs_intro: cat_cs_intros
        )
    show T: "T : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B" by (rule assms(1))
    from T T.arr_Rel_axioms v11.v11_axioms assms(3) show 
      "\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr> \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> T = cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_Rel_cs_simps  
            cs_intro: cat_cs_intros cat_Rel_cs_intros
        )
    from T T.arr_Rel_axioms v11.v11_axioms assms(4) show 
      "T \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> \<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr> = cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>B\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_Rel_cs_simps  
            cs_intro: cat_cs_intros cat_Rel_cs_intros
        )
  qed

qed

lemma cat_Rel_is_arr_isomorphismD[dest]:
  assumes "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Rel \<alpha>\<^esub> B"
  shows "T : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B" 
    and "v11 (T\<lparr>ArrVal\<rparr>)"
    and "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A"
    and "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B"
proof-

  from assms show T: "T : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B" 
    by (simp add: is_arr_isomorphism_def)

  interpret T: arr_Rel \<alpha> T
    rewrites [simp]: "T\<lparr>ArrDom\<rparr> = A" and [simp]: "T\<lparr>ArrCod\<rparr> = B"
    using T
    by (all\<open>elim cat_Rel_is_arrE\<close>) (simp_all add: cat_Rel_components)
  
  interpret is_iso_functor \<alpha> \<open>op_cat (cat_Rel \<alpha>)\<close> \<open>cat_Rel \<alpha>\<close> \<open>\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<close>
    by (simp add: cf_dag_Rel_is_iso_functor)

  from is_arr_isomorphismD[OF assms(1)] obtain S where 
    "is_inverse (cat_Rel \<alpha>) S T"
    by clarsimp
  from is_inverseD[OF this] obtain A' B' where "S : B' \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> A'" 
    and "T : A' \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B'"
    and "S \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> T = cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A'\<rparr>" 
    and "T \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> S = cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>B'\<rparr>"
    by auto
  moreover with T have "A' = A" "B' = B" by auto
  ultimately have S: "S : B \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> A" 
    and ST: "S \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> T = cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr>" 
    and TS: "T \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> S = cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>B\<rparr>"
    by auto
  
  from S T ST TS have S_def: "S = \<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr>"
    by (rule is_arr_isomorphism_dag)

  interpret S: arr_Rel \<alpha> \<open>\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr>\<close>
    rewrites "(\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr>)\<lparr>ArrDom\<rparr> = B" 
      and "(\<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr>)\<lparr>ArrCod\<rparr> = A"
    by (fold S_def, insert S, all\<open>elim cat_Rel_is_arrE\<close>) 
      (simp_all add: cat_Rel_components)

  from T.arr_Rel_axioms S_def have S_T: "S\<lparr>ArrVal\<rparr> = (T\<lparr>ArrVal\<rparr>)\<inverse>\<^sub>\<circ>"
    by (simp add: cf_dag_Rel_ArrMap_app converse_Rel_components(1))

  from S have A: "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" and B: "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" by auto

  from B TS A ST have 
    "(T \<circ>\<^sub>R\<^sub>e\<^sub>l S)\<lparr>ArrVal\<rparr> = id_Rel B\<lparr>ArrVal\<rparr>"
    "(S \<circ>\<^sub>R\<^sub>e\<^sub>l T)\<lparr>ArrVal\<rparr> = id_Rel A\<lparr>ArrVal\<rparr>"
    unfolding cat_Rel_Comp_app[OF S T] cat_Rel_Comp_app[OF T S]
    unfolding cat_Rel_components
    by simp_all

  then have val_ST: "S\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> T\<lparr>ArrVal\<rparr> = vid_on A" 
    and val_TS: "T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> S\<lparr>ArrVal\<rparr> = vid_on B"
    unfolding comp_Rel_components id_Rel_components by simp_all

  show "v11 (T\<lparr>ArrVal\<rparr>)"
  proof(rule v11I)
  
    show "vsv (T\<lparr>ArrVal\<rparr>)"
    proof(rule vsvI)
      fix a b c assume prems: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>" "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>"
      from prems(1) S_T have "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>" by auto
      with prems(2) val_TS have "\<langle>b, c\<rangle> \<in>\<^sub>\<circ> vid_on B" by auto
      then show "b = c" by clarsimp
    qed (auto simp: T.ArrVal.vbrelation_axioms)

    show "vsv ((T\<lparr>ArrVal\<rparr>)\<inverse>\<^sub>\<circ>)"
    proof(rule vsvI)
      fix a b c 
      assume prems: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)\<inverse>\<^sub>\<circ>" "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)\<inverse>\<^sub>\<circ>"
      with S_T have "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>" and "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>" by auto
      moreover from prems have "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>" and "\<langle>c, a\<rangle> \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>" 
        by auto
      ultimately have "\<langle>b, c\<rangle> \<in>\<^sub>\<circ> vid_on A" using val_ST by auto
      then show "b = c" by clarsimp
    qed auto

  qed

  show "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A"
  proof(intro vsubset_antisym vsubsetI)
    fix a assume "a \<in>\<^sub>\<circ> A"
    with val_ST have "\<langle>a, a\<rangle> \<in>\<^sub>\<circ> S\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>" by auto 
    then show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)" by auto
  qed (use T.arr_Rel_ArrVal_vdomain in auto)

  show "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B"
  proof(intro vsubset_antisym vsubsetI)
    fix b assume "b \<in>\<^sub>\<circ> B"
    with val_TS have "\<langle>b, b\<rangle> \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>" by auto
    then show "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)" by auto
  qed (use T.arr_Rel_ArrVal_vrange in auto)

qed

end 

end

lemmas [cat_Rel_cs_simps] = \<Z>.cat_Rel_is_arr_isomorphismD(3,4)

lemma (in \<Z>) cat_Rel_is_arr_isomorphism:
  "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Rel \<alpha>\<^esub> B \<longleftrightarrow>
    T : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B \<and>
    v11 (T\<lparr>ArrVal\<rparr>) \<and>
    \<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A \<and>
    \<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B"
  by auto



subsection\<open>The inverse arrow\<close>

lemma (in \<Z>) cat_Rel_the_inverse:
  assumes "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Rel \<alpha>\<^esub> B"
  shows "T\<inverse>\<^sub>C\<^bsub>cat_Rel \<alpha>\<^esub> = T\<inverse>\<^sub>R\<^sub>e\<^sub>l"
  unfolding the_inverse_def
proof(rule the_equality)

  interpret Rel: category \<alpha> \<open>cat_Rel \<alpha>\<close> by (rule category_cat_Rel)
  from assms have T: "T : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B" by auto
  interpret T: arr_Rel \<alpha> T
    rewrites "T\<lparr>ArrDom\<rparr> = A" and "T\<lparr>ArrCod\<rparr> = B"
    using T by (all\<open>elim cat_Rel_is_arrE\<close>) (simp_all add: cat_Rel_components)
  
  from assms T T.arr_Rel_axioms cat_Rel_is_arr_isomorphismD(2)[OF assms] 
  show inv_T_T: "is_inverse (cat_Rel \<alpha>) (T\<inverse>\<^sub>R\<^sub>e\<^sub>l) T"
    by (intro is_inverseI[where a=A and b=B])
      (
        cs_concl 
          cs_simp: cat_cs_simps cat_Rel_cs_simps
          cs_intro: cat_Rel_cs_intros cat_cs_intros
      )+

  fix S assume prems: "is_inverse (cat_Rel \<alpha>) S T"
  show "S = T\<inverse>\<^sub>R\<^sub>e\<^sub>l"
    by (rule category.cat_is_inverse_eq[OF Rel.category_axioms prems inv_T_T])

qed

lemmas [cat_Rel_cs_simps] = \<Z>.cat_Rel_the_inverse

text\<open>\newpage\<close>

end