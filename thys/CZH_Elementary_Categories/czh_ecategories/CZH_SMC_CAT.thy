(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>CAT\<close> as a semicategory\label{sec:smc_CAT}\<close>
theory CZH_SMC_CAT
  imports 
    CZH_DG_CAT
    CZH_ECAT_Simple
begin



subsection\<open>Background\<close>


text\<open>
The subsection presents the theory of the semicategories of \<open>\<alpha>\<close>-categories.
It continues the development that was initiated in section 
\ref{sec:dg_CAT}.
\<close>

named_theorems smc_CAT_simps
named_theorems smc_CAT_intros



subsection\<open>Definition and elementary properties\<close>

definition smc_CAT :: "V \<Rightarrow> V"
  where "smc_CAT \<alpha> =
    [
      set {\<CC>. category \<alpha> \<CC>}, 
      all_cfs \<alpha>, 
      (\<lambda>\<FF>\<in>\<^sub>\<circ>all_cfs \<alpha>. \<FF>\<lparr>HomDom\<rparr>), 
      (\<lambda>\<FF>\<in>\<^sub>\<circ>all_cfs \<alpha>. \<FF>\<lparr>HomCod\<rparr>),
      (\<lambda>\<GG>\<FF>\<in>\<^sub>\<circ>composable_arrs (dg_CAT \<alpha>). \<GG>\<FF>\<lparr>0\<rparr> \<circ>\<^sub>C\<^sub>F \<GG>\<FF>\<lparr>1\<^sub>\<nat>\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smc_CAT_components:
  shows "smc_CAT \<alpha>\<lparr>Obj\<rparr> = set {\<CC>. category \<alpha> \<CC>}"
    and "smc_CAT \<alpha>\<lparr>Arr\<rparr> = all_cfs \<alpha>"
    and "smc_CAT \<alpha>\<lparr>Dom\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>all_cfs \<alpha>. \<FF>\<lparr>HomDom\<rparr>)"
    and "smc_CAT \<alpha>\<lparr>Cod\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>all_cfs \<alpha>. \<FF>\<lparr>HomCod\<rparr>)"
    and "smc_CAT \<alpha>\<lparr>Comp\<rparr> = (\<lambda>\<GG>\<FF>\<in>\<^sub>\<circ>composable_arrs (dg_CAT \<alpha>). \<GG>\<FF>\<lparr>0\<rparr> \<circ>\<^sub>C\<^sub>F \<GG>\<FF>\<lparr>1\<^sub>\<nat>\<rparr>)"
  unfolding smc_CAT_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smc_dg_CAT: "smc_dg (smc_CAT \<alpha>) = dg_CAT \<alpha>"
proof(rule vsv_eqI)
  show "vsv (smc_dg (smc_CAT \<alpha>))" unfolding smc_dg_def by auto
  show "vsv (dg_CAT \<alpha>)" unfolding dg_CAT_def by auto
  have dom_lhs: "\<D>\<^sub>\<circ> (smc_dg (smc_CAT \<alpha>)) = 4\<^sub>\<nat>" 
    unfolding smc_dg_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (dg_CAT \<alpha>) = 4\<^sub>\<nat>"
    unfolding dg_CAT_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (smc_dg (smc_CAT \<alpha>)) = \<D>\<^sub>\<circ> (dg_CAT \<alpha>)"
    unfolding dom_lhs dom_rhs by simp
  show "\<AA> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_dg (smc_CAT \<alpha>)) \<Longrightarrow> smc_dg (smc_CAT \<alpha>)\<lparr>\<AA>\<rparr> = dg_CAT \<alpha>\<lparr>\<AA>\<rparr>"
    for \<AA>
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral,
        unfold smc_dg_def dg_field_simps smc_CAT_def dg_CAT_def
      )
      (auto simp: nat_omega_simps)
qed

lemmas_with [folded smc_dg_CAT, unfolded slicing_simps]: 
  smc_CAT_ObjI = dg_CAT_ObjI
  and smc_CAT_ObjD = dg_CAT_ObjD
  and smc_CAT_ObjE = dg_CAT_ObjE
  and smc_CAT_Obj_iff[smc_CAT_simps] = dg_CAT_Obj_iff  
  and smc_CAT_Dom_app[smc_CAT_simps] = dg_CAT_Dom_app
  and smc_CAT_Cod_app[smc_CAT_simps] = dg_CAT_Cod_app
  and smc_CAT_is_arrI = dg_CAT_is_arrI
  and smc_CAT_is_arrD = dg_CAT_is_arrD
  and smc_CAT_is_arrE = dg_CAT_is_arrE
  and smc_CAT_is_arr_iff[smc_CAT_simps] = dg_CAT_is_arr_iff


subsection\<open>Composable arrows\<close>

lemma smc_CAT_composable_arrs_dg_CAT: 
  "composable_arrs (dg_CAT \<alpha>) = composable_arrs (smc_CAT \<alpha>)"
  unfolding composable_arrs_def smc_dg_CAT[symmetric] slicing_simps by auto

lemma smc_CAT_Comp: 
  "smc_CAT \<alpha>\<lparr>Comp\<rparr> = (\<lambda>\<GG>\<FF>\<in>\<^sub>\<circ>composable_arrs (smc_CAT \<alpha>). \<GG>\<FF>\<lparr>0\<rparr> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>\<FF>\<lparr>1\<^sub>\<nat>\<rparr>)"
  unfolding smc_CAT_components smc_CAT_composable_arrs_dg_CAT ..



subsection\<open>Composition\<close>

lemma smc_CAT_Comp_app[smc_CAT_simps]:
  assumes "\<GG> : \<BB> \<mapsto>\<^bsub>smc_CAT \<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<^bsub>smc_CAT \<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>A\<^bsub>smc_CAT \<alpha>\<^esub> \<FF> = \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>"
proof-
  from assms have "[\<GG>, \<FF>]\<^sub>\<circ> \<in>\<^sub>\<circ> composable_arrs (smc_CAT \<alpha>)" 
    by (auto simp: smc_cs_intros)
  then show "\<GG> \<circ>\<^sub>A\<^bsub>smc_CAT \<alpha>\<^esub> \<FF> = \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>"
    unfolding smc_CAT_Comp by (simp add: nat_omega_simps)
qed 

lemma smc_CAT_Comp_vdomain: "\<D>\<^sub>\<circ> (smc_CAT \<alpha>\<lparr>Comp\<rparr>) = composable_arrs (smc_CAT \<alpha>)" 
  unfolding smc_CAT_Comp by auto                      

lemma smc_CAT_Comp_vrange: "\<R>\<^sub>\<circ> (smc_CAT \<alpha>\<lparr>Comp\<rparr>) \<subseteq>\<^sub>\<circ> all_cfs \<alpha>"
proof(rule vsubsetI)
  fix \<HH> assume "\<HH> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (smc_CAT \<alpha>\<lparr>Comp\<rparr>)"
  then obtain \<GG>\<FF> 
    where \<HH>_def: "\<HH> = smc_CAT \<alpha>\<lparr>Comp\<rparr>\<lparr>\<GG>\<FF>\<rparr>"
      and "\<GG>\<FF> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_CAT \<alpha>\<lparr>Comp\<rparr>)"
    by (auto simp: smc_CAT_components intro: smc_cs_intros)
  then obtain \<GG> \<FF> \<AA> \<BB> \<CC> 
    where "\<GG>\<FF> = [\<GG>, \<FF>]\<^sub>\<circ>" 
      and \<GG>: "\<GG> : \<BB> \<mapsto>\<^bsub>smc_CAT \<alpha>\<^esub> \<CC>" 
      and \<FF>: "\<FF> : \<AA> \<mapsto>\<^bsub>smc_CAT \<alpha>\<^esub> \<BB>"
    by (auto simp: smc_CAT_Comp_vdomain) 
  with \<HH>_def have \<HH>_def': "\<HH> = \<GG> \<circ>\<^sub>A\<^bsub>smc_CAT \<alpha>\<^esub> \<FF>" by simp
  from \<GG> \<FF> show "\<HH> \<in>\<^sub>\<circ> all_cfs \<alpha>" 
    unfolding \<HH>_def' by (auto simp: smc_CAT_simps intro: cat_cs_intros)
qed



subsection\<open>\<open>CAT\<close> is a category\<close>

lemma (in \<Z>) tiny_semicategory_smc_CAT: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "tiny_semicategory \<beta> (smc_CAT \<alpha>)"
proof(intro tiny_semicategoryI, unfold smc_CAT_is_arr_iff)
  show "vfsequence (smc_CAT \<alpha>)" unfolding smc_CAT_def by auto
  show "vcard (smc_CAT \<alpha>) = 5\<^sub>\<nat>"
    unfolding smc_CAT_def by (simp add: nat_omega_simps)
  show "(\<GG>\<FF> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_CAT \<alpha>\<lparr>Comp\<rparr>)) \<longleftrightarrow>
    (\<exists>\<GG> \<FF> \<BB> \<CC> \<AA>. \<GG>\<FF> = [\<GG>, \<FF>]\<^sub>\<circ> \<and> \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<and> \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>)"
    for \<GG>\<FF>
    unfolding smc_CAT_Comp_vdomain
  proof
    show "\<GG>\<FF> \<in>\<^sub>\<circ> composable_arrs (smc_CAT \<alpha>) \<Longrightarrow> 
      \<exists>\<GG> \<FF> \<BB> \<CC> \<AA>. \<GG>\<FF> = [\<GG>, \<FF>]\<^sub>\<circ> \<and> \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<and> \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      by (elim composable_arrsE) (auto simp: smc_CAT_is_arr_iff)
  next
    assume "\<exists>\<GG> \<FF> \<BB> \<CC> \<AA>. \<GG>\<FF> = [\<GG>, \<FF>]\<^sub>\<circ> \<and> \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<and> \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    with smc_CAT_is_arr_iff show "\<GG>\<FF> \<in>\<^sub>\<circ> composable_arrs (smc_CAT \<alpha>)"
      unfolding smc_CAT_Comp_vdomain by (auto intro: smc_cs_intros)
  qed
  show "\<lbrakk> \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>; \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB> \<rbrakk> \<Longrightarrow> 
    \<GG> \<circ>\<^sub>A\<^bsub>smc_CAT \<alpha>\<^esub> \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    for \<GG> \<BB> \<CC> \<FF> \<AA>
    by (cs_concl cs_simp: smc_CAT_simps cs_intro: cat_cs_intros)

  fix \<HH> \<CC> \<DD> \<GG> \<BB> \<FF> \<AA>
  assume "\<HH> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  moreover then have "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" "\<HH> \<circ>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" 
    by (cs_concl cs_simp: smc_CAT_simps cs_intro: cat_cs_intros)+
  ultimately show 
    "\<HH> \<circ>\<^sub>A\<^bsub>smc_CAT \<alpha>\<^esub> \<GG> \<circ>\<^sub>A\<^bsub>smc_CAT \<alpha>\<^esub> \<FF> = \<HH> \<circ>\<^sub>A\<^bsub>smc_CAT \<alpha>\<^esub> (\<GG> \<circ>\<^sub>A\<^bsub>smc_CAT \<alpha>\<^esub> \<FF>)"
    by (simp add: smc_CAT_is_arr_iff smc_CAT_Comp_app cf_comp_assoc)
qed (auto simp: assms smc_dg_CAT tiny_category_dg_CAT smc_CAT_components)



subsection\<open>Initial object\<close>

lemma (in \<Z>) smc_CAT_obj_initialI: "obj_initial (smc_CAT \<alpha>) cat_0"
  \<comment>\<open>
  See \cite{noauthor_nlab_nodate}\footnote{\url{
  https://ncatlab.org/nlab/show/initial+object
  }}).
  \<close>
  unfolding obj_initial_def
proof(intro obj_terminalI, unfold smc_op_simps smc_CAT_is_arr_iff smc_CAT_Obj_iff)
  show "category \<alpha> cat_0" by (intro category_cat_0)
  fix \<AA> assume "category \<alpha> \<AA>"
  then interpret category \<alpha> \<AA> .
  show "\<exists>!f. f : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  proof
    show cf_0: "cf_0 \<AA> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      by (simp add: cf_0_is_functor category_axioms is_ft_functor.axioms(1))
    fix \<FF> assume prems: "\<FF> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
    interpret \<FF>: is_functor \<alpha> cat_0 \<AA> \<FF> using prems .
    show "\<FF> = cf_0 \<AA>"
    proof(rule cf_eqI)
      show "\<FF> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" by (simp add: prems)
      from cf_0 show "cf_0 \<AA> : cat_0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
        unfolding smc_CAT_is_arr_iff by simp
      have "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = 0" by (auto simp: cat_0_components cat_cs_simps)
      then show "\<FF>\<lparr>ObjMap\<rparr> = cf_0 \<AA>\<lparr>ObjMap\<rparr>"
        using \<FF>.ObjMap.vbrelation_vintersection_vdomain 
        by (auto simp: cf_0_components)
      have "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = 0" by (auto simp: cat_0_components cat_cs_simps)
      with \<FF>.ArrMap.vbrelation_vintersection_vdomain show 
        "\<FF>\<lparr>ArrMap\<rparr> = cf_0 \<AA>\<lparr>ArrMap\<rparr>"
        by (auto simp: cf_0_components)
    qed (simp_all add: cf_0_components)
  qed
qed

lemma (in \<Z>) smc_CAT_obj_initialD:
  assumes "obj_initial (smc_CAT \<alpha>) \<AA>"
  shows "\<AA> = cat_0" 
  using assms unfolding obj_initial_def
proof(elim obj_terminalE, unfold smc_op_simps smc_CAT_is_arr_iff smc_CAT_Obj_iff)
  assume prems: 
    "category \<alpha> \<AA>" 
    "category \<alpha> \<BB> \<Longrightarrow> \<exists>!\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    for \<BB>
  from prems(2)[OF category_cat_0] obtain \<FF> where \<FF>: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_0" 
    by meson
  interpret \<FF>: is_functor \<alpha> \<AA> cat_0 \<FF> by (rule \<FF>) 
  have "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> 0"
    unfolding cat_0_components(1)[symmetric] by (simp add: \<FF>.cf_ObjMap_vrange)
  then have "\<FF>\<lparr>ObjMap\<rparr> = 0" by (auto intro: \<FF>.ObjMap.vsv_vrange_vempty)
  with \<FF>.cf_ObjMap_vdomain have Obj[simp]: "\<AA>\<lparr>Obj\<rparr> = 0" by auto
  have "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> 0"
    unfolding cat_0_components(2)[symmetric] by (simp add: \<FF>.cf_ArrMap_vrange)
  then have "\<FF>\<lparr>ArrMap\<rparr> = 0" by (auto intro: \<FF>.ArrMap.vsv_vrange_vempty)
  with \<FF>.cf_ArrMap_vdomain have Arr[simp]: "\<AA>\<lparr>Arr\<rparr> = 0" by auto
  from \<FF>.HomDom.Dom.vdomain_vrange_is_vempty have [simp]: "\<AA>\<lparr>Dom\<rparr> = 0"  
    by (fastforce simp: \<FF>.HomDom.cat_Dom_vempty_if_Arr_vempty)
  from \<FF>.HomDom.Cod.vdomain_vrange_is_vempty have [simp]: "\<AA>\<lparr>Cod\<rparr> = 0"
    by (fastforce simp: \<FF>.HomDom.cat_Cod_vempty_if_Arr_vempty)
  from Arr have "\<AA>\<lparr>Arr\<rparr> ^\<^sub>\<times> 2\<^sub>\<nat> = 0" by (simp add: vcpower_of_vempty)
  with \<FF>.HomDom.Comp.pnop_vdomain have "\<D>\<^sub>\<circ> (\<AA>\<lparr>Comp\<rparr>) = 0" by simp
  with \<FF>.HomDom.Comp.vdomain_vrange_is_vempty have [simp]: "\<AA>\<lparr>Comp\<rparr> = 0"
    by (auto intro: \<FF>.HomDom.Comp.vsv_vrange_vempty)
  have "\<D>\<^sub>\<circ> (\<AA>\<lparr>CId\<rparr>) = 0"
    by (simp add: \<FF>.HomDom.cat_CId_vdomain)
  with \<FF>.HomDom.CId.vdomain_vrange_is_vempty \<FF>.HomDom.CId.vsv_vrange_vempty 
  have [simp]: "\<AA>\<lparr>CId\<rparr> = 0"
    by simp
  show "\<AA> = cat_0"
    by (rule cat_eqI[of \<alpha>])  
      (simp_all add: prems(1) cat_0_components category_cat_0)
qed

lemma (in \<Z>) smc_CAT_obj_initialE:
  assumes "obj_initial (smc_CAT \<alpha>) \<AA>"
  obtains "\<AA> = cat_0" 
  using assms by (auto dest: smc_CAT_obj_initialD)

lemma (in \<Z>) smc_CAT_obj_initial_iff[smc_CAT_simps]: 
  "obj_initial (smc_CAT \<alpha>) \<AA> \<longleftrightarrow> \<AA> = cat_0"
  using smc_CAT_obj_initialI smc_CAT_obj_initialD by auto



subsection\<open>Terminal object\<close>

lemma (in \<Z>) smc_CAT_obj_terminalI: 
  \<comment>\<open>See \cite{noauthor_nlab_nodate}\footnote{\url{
  https://ncatlab.org/nlab/show/terminal+object
  }}.\<close>
  assumes "a \<in>\<^sub>\<circ> Vset \<alpha>" and "f \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "obj_terminal (smc_CAT \<alpha>) (cat_1 a f)"
proof(intro obj_terminalI, unfold smc_op_simps smc_CAT_is_arr_iff smc_CAT_Obj_iff)
  fix \<AA> assume prems: "category \<alpha> \<AA>"
  then interpret category \<alpha> \<AA> .
  show "\<exists>!\<FF>'. \<FF>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_1 a f"
  proof
    show cf_1: "cf_const \<AA> (cat_1 a f) a : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_1 a f"
      by (rule cf_const_is_functor)
        (auto simp: assms prems category_cat_1 cat_1_components)
    fix \<FF>' assume "\<FF>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_1 a f"
    then interpret \<FF>': is_functor \<alpha> \<AA> \<open>cat_1 a f\<close> \<FF>' .
    show "\<FF>' = cf_const \<AA> (cat_1 a f) a"
    proof(rule cf_eqI, unfold dghm_const_components)
      from cf_1 show "cf_const \<AA> (cat_1 a f) a : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_1 a f" by simp
      show "\<FF>'\<lparr>ObjMap\<rparr> = vconst_on (\<AA>\<lparr>Obj\<rparr>) a"
      proof(cases\<open>\<AA>\<lparr>Obj\<rparr> = 0\<close>)
        case True
        with \<FF>'.ObjMap.vbrelation_vintersection_vdomain have "\<FF>'\<lparr>ObjMap\<rparr> = 0"
          by (auto simp: cat_cs_simps)
        with True show ?thesis by simp
      next
        case False
        then have "\<D>\<^sub>\<circ> (\<FF>'\<lparr>ObjMap\<rparr>) \<noteq> 0" by (auto simp: cat_cs_simps)
        then have "\<R>\<^sub>\<circ> (\<FF>'\<lparr>ObjMap\<rparr>) \<noteq> 0"
          by (simp add: \<FF>'.ObjMap.vsv_vdomain_vempty_vrange_vempty)
        moreover from \<FF>'.cf_ObjMap_vrange have "\<R>\<^sub>\<circ> (\<FF>'\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> set {a}"
          by (simp add: cat_1_components)
        ultimately have "\<R>\<^sub>\<circ> (\<FF>'\<lparr>ObjMap\<rparr>) = set {a}" by auto
        then show ?thesis 
          by (intro vsv.vsv_is_vconst_onI) (auto simp: cat_cs_simps) 
      qed
      show "\<FF>'\<lparr>ArrMap\<rparr> = vconst_on (\<AA>\<lparr>Arr\<rparr>) (cat_1 a f\<lparr>CId\<rparr>\<lparr>a\<rparr>)"
      proof(cases\<open>\<AA>\<lparr>Arr\<rparr> = 0\<close>)
        case True
        with 
          \<FF>'.ArrMap.vdomain_vrange_is_vempty
          vsv.vsv_vrange_vempty[OF \<FF>'.cf_ArrMap_vsv] 
        have "\<FF>'\<lparr>ArrMap\<rparr> = 0"
          by (auto simp: cat_cs_simps)
        with True show ?thesis by simp
      next
        case False
        then have "\<D>\<^sub>\<circ> (\<FF>'\<lparr>ArrMap\<rparr>) \<noteq> 0" by (auto simp: cat_cs_simps)
        then have "\<R>\<^sub>\<circ> (\<FF>'\<lparr>ArrMap\<rparr>) \<noteq> 0" 
          by (simp add: \<FF>'.ArrMap.vsv_vdomain_vempty_vrange_vempty)
        moreover from \<FF>'.cf_ArrMap_vrange have "\<R>\<^sub>\<circ> (\<FF>'\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> set {f}"
          by (simp add: cat_1_components)
        ultimately have "\<R>\<^sub>\<circ> (\<FF>'\<lparr>ArrMap\<rparr>) = set {f}" by auto
        then show ?thesis 
          by 
            (
              cs_concl 
                cs_simp: V_cs_simps cat_cs_simps cat_1_components
                cs_intro: V_cs_intros vsv.vsv_is_vconst_onI
            )+
      qed
    qed (auto intro: cat_cs_intros)
  qed 
qed (simp add: assms category_cat_1)

lemma (in \<Z>) smc_CAT_obj_terminalE: 
  assumes "obj_terminal (smc_CAT \<alpha>) \<BB>"
  obtains a f where "a \<in>\<^sub>\<circ> Vset \<alpha>" and "f \<in>\<^sub>\<circ> Vset \<alpha>" and "\<BB> = cat_1 a f"
  using assms
proof(elim obj_terminalE, unfold cat_op_simps smc_CAT_is_arr_iff smc_CAT_Obj_iff)

  assume prems: "category \<alpha> \<BB>" "category \<alpha> \<AA> \<Longrightarrow> \<exists>!\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" for \<AA>
  interpret \<BB>: category \<alpha> \<BB> by (rule prems(1))

  obtain a where \<BB>_Obj: "\<BB>\<lparr>Obj\<rparr> = set {a}" and a: "a \<in>\<^sub>\<circ> Vset \<alpha>"
  proof-
    have cat_1: "category \<alpha> (cat_1 0 0)" by (rule category_cat_1) auto
    from prems(2)[OF cat_1] obtain \<FF> 
      where \<FF>: "\<FF> : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
        and \<GG>\<FF>: "\<GG> : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB> \<Longrightarrow> \<GG> = \<FF>" for \<GG>
      by fastforce
    interpret \<FF>: is_functor \<alpha> \<open>cat_1 0 0\<close> \<BB> \<FF> by (rule \<FF>)
    have "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = set {0}" by (simp add: cat_1_components cat_cs_simps)
    then obtain a where vrange_\<FF>[simp]: "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = set {a}"
      by (auto intro: \<FF>.ObjMap.vsv_vdomain_vsingleton_vrange_vsingleton)
    with \<BB>.cat_Obj_vsubset_Vset \<FF>.cf_ObjMap_vrange have [simp]: "a \<in>\<^sub>\<circ> Vset \<alpha>"
      by auto
    from \<FF>.cf_ObjMap_vrange have "set {a} \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" by simp
    moreover have "\<BB>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> set {a}"
    proof(rule ccontr)
      assume "\<not>\<BB>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> set {a}"
      then obtain b where ba: "b \<noteq> a" and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" by force
      have "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
        by (rule cf_const_is_functor)
          (simp_all add: \<BB>.category_axioms category_cat_1 b)
      then have \<GG>_def: "cf_const (cat_1 0 0) \<BB> b = \<FF>" by (rule \<GG>\<FF>) 
      have "\<R>\<^sub>\<circ> (cf_const (cat_1 0 0) \<BB> b\<lparr>ObjMap\<rparr>) = set {b}" 
        unfolding dghm_const_components cat_1_components by simp
      with vrange_\<FF> ba show False unfolding \<GG>_def by simp  
    qed
    ultimately have "\<BB>\<lparr>Obj\<rparr> = set {a}" by simp
    with that show ?thesis by simp
  qed

  have \<BB>_Arr: "\<BB>\<lparr>Arr\<rparr> = set {\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>}"
  proof(rule vsubset_antisym)
    from \<BB>_Obj show "set {\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>} \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" 
      by (blast intro: \<BB>.cat_is_arrD(1) cat_cs_intros)
    show "\<BB>\<lparr>Arr\<rparr> \<subseteq>\<^sub>\<circ> set {\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>}"
    proof(intro vsubsetI)
      fix f assume "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" 
      with \<BB>_Obj have f: "f : a \<mapsto>\<^bsub>\<BB>\<^esub> a"
        by (metis \<BB>.cat_is_arrD(2,3) is_arrI vsingleton_iff)
      from f have "cf_const \<BB> \<BB> a : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
        by (intro cf_const_is_functor) (auto simp: \<BB>.category_axioms)
      moreover from f have "cf_id \<BB> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
        by (intro category.cat_cf_id_is_functor)
          (auto simp: \<BB>.category_axioms)
      ultimately have "cf_const \<BB> \<BB> a = cf_id \<BB>"
        by (metis prems(2) \<BB>.category_axioms)
      moreover from f have "cf_const \<BB> \<BB> a\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>" 
        by (simp add: \<open>f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>\<close> dghm_const_ArrMap_app)
      moreover from f have "cf_id \<BB>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = f" 
        unfolding dghm_id_components by (simp add: cat_cs_intros)
      ultimately show "f \<in>\<^sub>\<circ> set {\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>}" by simp
    qed
  qed

  have "\<BB> = cat_1 a (\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>)"
  proof(rule cat_eqI[of \<alpha>], unfold cat_1_components)
    from \<BB>.cat_Arr_vsubset_Vset \<BB>_Arr show "category \<alpha> (cat_1 a (\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>))"
      by (intro category_cat_1) (auto simp: a)
    show "\<BB>\<lparr>Arr\<rparr> = set {\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>}" by (simp add: \<BB>_Arr)
    then have "\<D>\<^sub>\<circ> (\<BB>\<lparr>Dom\<rparr>) = set {\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>}" 
      by (simp add: cat_cs_simps cat_cs_intros)
    moreover have "\<R>\<^sub>\<circ> (\<BB>\<lparr>Dom\<rparr>) = set {a}"
      using \<BB>.cat_Dom_vrange \<BB>.cat_CId_is_arr \<BB>.cat_Dom_vdomain
      by (auto simp: \<BB>_Obj elim: \<BB>.Dom.vbrelation_vinE) (*slow*)
    ultimately show "\<BB>\<lparr>Dom\<rparr> = set {\<langle>\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>, a\<rangle>}"
      using \<BB>.Dom.vsv_vdomain_vrange_vsingleton by simp
    have "\<D>\<^sub>\<circ> (\<BB>\<lparr>Cod\<rparr>) = set {\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>}" 
      by (simp add: \<BB>_Arr cat_cs_simps)
    moreover have "\<R>\<^sub>\<circ> (\<BB>\<lparr>Cod\<rparr>) = set {a}"
      using \<BB>.cat_Cod_vrange \<BB>.cat_CId_is_arr \<BB>.cat_Cod_vdomain 
      by (auto simp: \<BB>_Obj elim: \<BB>.Cod.vbrelation_vinE) (*slow*)
    ultimately show "\<BB>\<lparr>Cod\<rparr> = set {\<langle>\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>, a\<rangle>}"
      by (auto intro: \<BB>.Cod.vsv_vdomain_vrange_vsingleton)
    show "\<BB>\<lparr>Comp\<rparr> = set {\<langle>[\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>, \<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>]\<^sub>\<circ>, \<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>\<rangle>}"
    proof(rule vsv_eqI)
      show dom: 
        "\<D>\<^sub>\<circ> (\<BB>\<lparr>Comp\<rparr>) = \<D>\<^sub>\<circ> (set {\<langle>[\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>, \<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>]\<^sub>\<circ>, \<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>\<rangle>})"
        unfolding vdomain_vsingleton
      proof(rule vsubset_antisym)
         show "\<D>\<^sub>\<circ> (\<BB>\<lparr>Comp\<rparr>) \<subseteq>\<^sub>\<circ> set {[\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>, \<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>]\<^sub>\<circ>}"
           by (intro vsubsetI) 
             (metis \<BB>.cat_Comp_vdomain \<BB>_Arr vsingleton_iff \<BB>.cat_is_arrD(1))
        show "set {[\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>, \<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>]\<^sub>\<circ>} \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<BB>\<lparr>Comp\<rparr>)"
          by
            (
              metis
                \<BB>_Obj vsingleton_iff 
                \<BB>.cat_CId_is_arr
                \<BB>.cat_Comp_vdomainI 
                vsubset_vsingleton_left
            )
      qed
      have "\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr> = \<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>" 
        by (metis \<BB>_Obj \<BB>.cat_CId_is_arr \<BB>.cat_CId_left_left vsingletonI)
      then show "a' \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<BB>\<lparr>Comp\<rparr>) \<Longrightarrow>
        \<BB>\<lparr>Comp\<rparr>\<lparr>a'\<rparr> = set {\<langle>[\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>, \<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>]\<^sub>\<circ>, \<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>\<rangle>}\<lparr>a'\<rparr>"
        for a'
        unfolding dom by simp
    qed (auto simp: \<BB>_Obj \<BB>_Arr)
    have "\<D>\<^sub>\<circ> (\<BB>\<lparr>CId\<rparr>) = set {a}" by (simp add: \<BB>_Obj \<BB>.cat_CId_vdomain)
    moreover then have "\<R>\<^sub>\<circ> (\<BB>\<lparr>CId\<rparr>) = set {\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>}"
      by 
        (
          metis 
            \<BB>.CId.vdomain_atE 
            \<BB>.CId.vsv_vdomain_vsingleton_vrange_vsingleton 
            vsingleton_iff
        )
    ultimately show "\<BB>\<lparr>CId\<rparr> = set {\<langle>a, \<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>\<rangle>}"
      by (blast intro: \<BB>.CId.vsv_vdomain_vrange_vsingleton)
  qed (auto simp: \<BB>_Obj cat_cs_intros)

  with a that \<BB>.cat_Arr_vsubset_Vset \<BB>_Arr show ?thesis by auto

qed

text\<open>\newpage\<close>

end