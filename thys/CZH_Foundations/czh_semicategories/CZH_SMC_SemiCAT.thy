(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>SemiCAT\<close> as a semicategory\<close>
theory CZH_SMC_SemiCAT
  imports 
    CZH_DG_SemiCAT
    CZH_SMC_Simple
    CZH_SMC_Small_Semicategory
begin



subsection\<open>Background\<close>


text\<open>
The subsection presents the theory of the semicategories of 
\<open>\<alpha>\<close>-semicategories.
It continues the development that was initiated in section 
\ref{sec:dg_SemiCAT}.
\<close>

named_theorems smc_SemiCAT_simps
named_theorems smc_SemiCAT_intros



subsection\<open>Definition and elementary properties\<close>

definition smc_SemiCAT :: "V \<Rightarrow> V"
  where "smc_SemiCAT \<alpha> =
    [
      set {\<CC>. semicategory \<alpha> \<CC>},
      all_smcfs \<alpha>,
      (\<lambda>\<FF>\<in>\<^sub>\<circ>all_smcfs \<alpha>. \<FF>\<lparr>HomDom\<rparr>),
      (\<lambda>\<FF>\<in>\<^sub>\<circ>all_smcfs \<alpha>. \<FF>\<lparr>HomCod\<rparr>),
      (\<lambda>\<GG>\<FF>\<in>\<^sub>\<circ>composable_arrs (dg_SemiCAT \<alpha>). \<GG>\<FF>\<lparr>0\<rparr> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>\<FF>\<lparr>1\<^sub>\<nat>\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smc_SemiCAT_components:
  shows "smc_SemiCAT \<alpha>\<lparr>Obj\<rparr> = set {\<CC>. semicategory \<alpha> \<CC>}"
    and "smc_SemiCAT \<alpha>\<lparr>Arr\<rparr> = all_smcfs \<alpha>"
    and "smc_SemiCAT \<alpha>\<lparr>Dom\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>all_smcfs \<alpha>. \<FF>\<lparr>HomDom\<rparr>)"
    and "smc_SemiCAT \<alpha>\<lparr>Cod\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>all_smcfs \<alpha>. \<FF>\<lparr>HomCod\<rparr>)"
    and "smc_SemiCAT \<alpha>\<lparr>Comp\<rparr> =
      (\<lambda>\<GG>\<FF>\<in>\<^sub>\<circ>composable_arrs (dg_SemiCAT \<alpha>). \<GG>\<FF>\<lparr>0\<rparr> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>\<FF>\<lparr>1\<^sub>\<nat>\<rparr>)"
  unfolding smc_SemiCAT_def dg_field_simps 
  by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smc_dg_SemiCAT[smc_SemiCAT_simps]: "smc_dg (smc_SemiCAT \<alpha>) = dg_SemiCAT \<alpha>"
proof(rule vsv_eqI)
  show "vsv (smc_dg (smc_SemiCAT \<alpha>))" unfolding smc_dg_def by auto
  show "vsv (dg_SemiCAT \<alpha>)" unfolding dg_SemiCAT_def by auto
  have dom_lhs: "\<D>\<^sub>\<circ> (smc_dg (smc_SemiCAT \<alpha>)) = 4\<^sub>\<nat>" 
    unfolding smc_dg_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (dg_SemiCAT \<alpha>) = 4\<^sub>\<nat>"
    unfolding dg_SemiCAT_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (smc_dg (smc_SemiCAT \<alpha>)) = \<D>\<^sub>\<circ> (dg_SemiCAT \<alpha>)"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_dg (smc_SemiCAT \<alpha>)) \<Longrightarrow> 
    smc_dg (smc_SemiCAT \<alpha>)\<lparr>a\<rparr> = dg_SemiCAT \<alpha>\<lparr>a\<rparr>"
    for a
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral,
        unfold smc_dg_def dg_field_simps smc_SemiCAT_def dg_SemiCAT_def
      )
      (auto simp: nat_omega_simps)
qed

lemmas_with [folded smc_dg_SemiCAT, unfolded slicing_simps]: 
  smc_SemiCAT_ObjI = dg_SemiCAT_ObjI
  and smc_SemiCAT_ObjD = dg_SemiCAT_ObjD
  and smc_SemiCAT_ObjE = dg_SemiCAT_ObjE
  and smc_SemiCAT_Obj_iff[smc_SemiCAT_simps] = dg_SemiCAT_Obj_iff  
  and smc_SemiCAT_Dom_app[smc_SemiCAT_simps] = dg_SemiCAT_Dom_app
  and smc_SemiCAT_Cod_app[smc_SemiCAT_simps] = dg_SemiCAT_Cod_app
  and smc_SemiCAT_is_arrI = dg_SemiCAT_is_arrI
  and smc_SemiCAT_is_arrD = dg_SemiCAT_is_arrD
  and smc_SemiCAT_is_arrE = dg_SemiCAT_is_arrE
  and smc_SemiCAT_is_arr_iff[smc_SemiCAT_simps] = dg_SemiCAT_is_arr_iff



subsection\<open>Composable arrows\<close>

lemma smc_SemiCAT_composable_arrs_dg_SemiCAT: 
  "composable_arrs (dg_SemiCAT \<alpha>) = composable_arrs (smc_SemiCAT \<alpha>)"
  unfolding composable_arrs_def smc_dg_SemiCAT[symmetric] slicing_simps by auto

lemma smc_SemiCAT_Comp: 
  "smc_SemiCAT \<alpha>\<lparr>Comp\<rparr> = 
    (\<lambda>\<GG>\<FF>\<in>\<^sub>\<circ>composable_arrs (smc_SemiCAT \<alpha>). \<GG>\<FF>\<lparr>0\<rparr> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>\<FF>\<lparr>1\<^sub>\<nat>\<rparr>)"
  unfolding smc_SemiCAT_components smc_SemiCAT_composable_arrs_dg_SemiCAT ..



subsection\<open>Composition\<close>

lemma smc_SemiCAT_Comp_app[smc_SemiCAT_simps]:
  assumes "\<GG> : \<BB> \<mapsto>\<^bsub>smc_SemiCAT \<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<^bsub>smc_SemiCAT \<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>A\<^bsub>smc_SemiCAT \<alpha>\<^esub> \<FF> = \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>"
proof-
  from assms have "[\<GG>, \<FF>]\<^sub>\<circ> \<in>\<^sub>\<circ> composable_arrs (smc_SemiCAT \<alpha>)" 
    by (auto simp: composable_arrsI)
  then show "\<GG> \<circ>\<^sub>A\<^bsub>smc_SemiCAT \<alpha>\<^esub> \<FF> = \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>"
    unfolding smc_SemiCAT_Comp by (simp add: nat_omega_simps)
qed 

lemma smc_SemiCAT_Comp_vdomain[smc_SemiCAT_simps]: 
  "\<D>\<^sub>\<circ> (smc_SemiCAT \<alpha>\<lparr>Comp\<rparr>) = composable_arrs (smc_SemiCAT \<alpha>)" 
  unfolding smc_SemiCAT_Comp by auto                      

lemma smc_SemiCAT_Comp_vrange: "\<R>\<^sub>\<circ> (smc_SemiCAT \<alpha>\<lparr>Comp\<rparr>) \<subseteq>\<^sub>\<circ> all_smcfs \<alpha>"
proof(rule vsubsetI)
  fix \<HH> assume "\<HH> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (smc_SemiCAT \<alpha>\<lparr>Comp\<rparr>)"
  then obtain \<GG>\<FF> 
    where \<HH>_def: "\<HH> = smc_SemiCAT \<alpha>\<lparr>Comp\<rparr>\<lparr>\<GG>\<FF>\<rparr>"
      and "\<GG>\<FF> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_SemiCAT \<alpha>\<lparr>Comp\<rparr>)"
    unfolding smc_SemiCAT_components by (auto intro: composable_arrsI)
  then obtain \<GG> \<FF> \<AA> \<BB> \<CC> 
    where "\<GG>\<FF> = [\<GG>, \<FF>]\<^sub>\<circ>" 
      and \<GG>: "\<GG> : \<BB> \<mapsto>\<^bsub>smc_SemiCAT \<alpha>\<^esub> \<CC>" 
      and \<FF>: "\<FF> : \<AA> \<mapsto>\<^bsub>smc_SemiCAT \<alpha>\<^esub> \<BB>"
    by (auto simp: smc_SemiCAT_Comp_vdomain) 
  with \<HH>_def have \<HH>_def': "\<HH> = \<GG> \<circ>\<^sub>A\<^bsub>smc_SemiCAT \<alpha>\<^esub> \<FF>" by simp
  from \<GG> \<FF> show "\<HH> \<in>\<^sub>\<circ> all_smcfs \<alpha>" 
    unfolding \<HH>_def' by (auto intro: smc_cs_intros simp: smc_SemiCAT_simps)
qed



subsection\<open>\<open>SemiCAT\<close> is a semicategory\<close>

lemma (in \<Z>) tiny_semicategory_smc_SemiCAT: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "tiny_semicategory \<beta> (smc_SemiCAT \<alpha>)"
proof(intro tiny_semicategoryI, unfold smc_SemiCAT_is_arr_iff)
  show "vfsequence (smc_SemiCAT \<alpha>)" unfolding smc_SemiCAT_def by auto
  show "vcard (smc_SemiCAT \<alpha>) = 5\<^sub>\<nat>"
    unfolding smc_SemiCAT_def by (simp add: nat_omega_simps)
  show "(\<GG>\<FF> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (smc_SemiCAT \<alpha>\<lparr>Comp\<rparr>)) \<longleftrightarrow>
    (\<exists>\<GG> \<FF> \<BB> \<CC> \<AA>. \<GG>\<FF> = [\<GG>, \<FF>]\<^sub>\<circ> \<and> \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<and> \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>)"
    for \<GG>\<FF>
    unfolding smc_SemiCAT_Comp_vdomain
  proof
    show "\<GG>\<FF> \<in>\<^sub>\<circ> composable_arrs (smc_SemiCAT \<alpha>) \<Longrightarrow> 
      \<exists>\<GG> \<FF> \<BB> \<CC> \<AA>. \<GG>\<FF> = [\<GG>, \<FF>]\<^sub>\<circ> \<and> \<GG>   : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<and> \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      by (elim composable_arrsE) (auto simp: smc_SemiCAT_is_arr_iff)
  next
    assume "\<exists>\<GG> \<FF> \<BB> \<CC> \<AA>. \<GG>\<FF> = [\<GG>, \<FF>]\<^sub>\<circ> \<and> \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<and> \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    with smc_SemiCAT_is_arr_iff show "\<GG>\<FF> \<in>\<^sub>\<circ> composable_arrs (smc_SemiCAT \<alpha>)"
      unfolding smc_SemiCAT_Comp_vdomain by (auto intro: smc_cs_intros)
  qed
  show "\<lbrakk> \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>; \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB> \<rbrakk> \<Longrightarrow> 
    \<GG> \<circ>\<^sub>A\<^bsub>smc_SemiCAT \<alpha>\<^esub> \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    for \<GG> \<BB> \<CC> \<FF> \<AA>
    by (auto simp: smc_SemiCAT_simps intro: smc_cs_intros)
  fix \<HH> \<CC> \<DD> \<GG> \<BB> \<FF> \<AA>
  assume "\<HH> : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  moreover then have "\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" "\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" 
    by (auto intro: smc_cs_intros)
  ultimately show "\<HH> \<circ>\<^sub>A\<^bsub>smc_SemiCAT \<alpha>\<^esub> \<GG> \<circ>\<^sub>A\<^bsub>smc_SemiCAT \<alpha>\<^esub> \<FF> = 
    \<HH> \<circ>\<^sub>A\<^bsub>smc_SemiCAT \<alpha>\<^esub> (\<GG> \<circ>\<^sub>A\<^bsub>smc_SemiCAT \<alpha>\<^esub> \<FF>)"
    by 
      (
        simp add: 
          smc_SemiCAT_is_arr_iff smc_SemiCAT_Comp_app smcf_comp_assoc
      )
qed 
  (
    auto simp: 
      assms smc_dg_SemiCAT tiny_digraph_dg_SemiCAT smc_SemiCAT_components
  )



subsection\<open>Initial object\<close>

lemma (in \<Z>) smc_SemiCAT_obj_initialI: "obj_initial (smc_SemiCAT \<alpha>) smc_0"
  unfolding obj_initial_def
proof
  (
    intro obj_terminalI, 
    unfold smc_op_simps smc_SemiCAT_is_arr_iff smc_SemiCAT_Obj_iff
  )
  show "semicategory \<alpha> smc_0" by (intro semicategory_smc_0)
  fix \<AA> assume prems: "semicategory \<alpha> \<AA>"
  interpret semicategory \<alpha> \<AA> using prems .
  show "\<exists>!\<FF>. \<FF> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  proof
    show smcf_0: "smcf_0 \<AA> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      by 
        (
          simp add: 
            smcf_0_is_semifunctor semicategory_axioms is_ft_semifunctor.axioms(1)
        )
    fix \<FF> assume prems: "\<FF> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
    then interpret \<FF>: is_semifunctor \<alpha> smc_0 \<AA> \<FF> .
    show "\<FF> = smcf_0 \<AA>"
    proof(rule smcf_eqI)
      show "\<FF> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" by (auto simp: smc_cs_intros)
      from smcf_0 show "smcf_0 \<AA> : smc_0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
        unfolding smc_SemiCAT_is_arr_iff by simp
      have "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = 0" by (auto simp: smc_0_components smc_cs_simps)
      with \<FF>.ObjMap.vdomain_vrange_is_vempty show "\<FF>\<lparr>ObjMap\<rparr> = smcf_0 \<AA>\<lparr>ObjMap\<rparr>"
        unfolding smcf_0_components by (auto intro: \<FF>.ObjMap.vsv_vrange_vempty)
      have "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = 0" by (auto simp: smc_0_components smc_cs_simps)
      with \<FF>.ArrMap.vdomain_vrange_is_vempty show "\<FF>\<lparr>ArrMap\<rparr> = smcf_0 \<AA>\<lparr>ArrMap\<rparr>"
        unfolding smcf_0_components by (auto intro: \<FF>.ArrMap.vsv_vrange_vempty)
    qed (simp_all add: smcf_0_components)
  qed
qed

lemma (in \<Z>) smc_SemiCAT_obj_initialD:
  assumes "obj_initial (smc_SemiCAT \<alpha>) \<AA>"
  shows "\<AA> = smc_0" 
  using assms unfolding obj_initial_def
proof
  (
    elim obj_terminalE,
    unfold smc_op_simps smc_SemiCAT_is_arr_iff smc_SemiCAT_Obj_iff
  )
  assume prems: 
    "semicategory \<alpha> \<AA>" 
    "semicategory \<alpha> \<BB> \<Longrightarrow> \<exists>!\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    for \<BB>
  from prems(2)[OF semicategory_smc_0] obtain \<FF> where "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> smc_0" 
    by meson
  then interpret \<FF>: is_semifunctor \<alpha> \<AA> smc_0 \<FF> .
  have "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> 0"
    unfolding smc_0_components(1)[symmetric]
    by (simp add: \<FF>.smcf_ObjMap_vrange)
  then have "\<FF>\<lparr>ObjMap\<rparr> = 0" by (auto intro: \<FF>.ObjMap.vsv_vrange_vempty)
  with \<FF>.smcf_ObjMap_vdomain have Obj[simp]: "\<AA>\<lparr>Obj\<rparr> = 0" by auto
  have "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> 0"
    unfolding smc_0_components(2)[symmetric]
    by (simp add: \<FF>.smcf_ArrMap_vrange)
  then have "\<FF>\<lparr>ArrMap\<rparr> = 0" by (auto intro: \<FF>.ArrMap.vsv_vrange_vempty)
  with \<FF>.smcf_ArrMap_vdomain have Arr[simp]: "\<AA>\<lparr>Arr\<rparr> = 0" by auto
  from \<FF>.HomDom.Dom.vdomain_vrange_is_vempty have [simp]: "\<AA>\<lparr>Dom\<rparr> = 0"  
    by (auto simp: smc_cs_simps intro: \<FF>.HomDom.Dom.vsv_vrange_vempty)
  from \<FF>.HomDom.Cod.vdomain_vrange_is_vempty have [simp]: "\<AA>\<lparr>Cod\<rparr> = 0"
    by (auto simp: smc_cs_simps intro: \<FF>.HomDom.Cod.vsv_vrange_vempty)
  from Arr have "\<AA>\<lparr>Arr\<rparr> ^\<^sub>\<times> 2\<^sub>\<nat> = 0" by (simp add: vcpower_of_vempty)
  with \<FF>.HomDom.Comp.pnop_vdomain have "\<D>\<^sub>\<circ> (\<AA>\<lparr>Comp\<rparr>) = 0" by simp
  with \<FF>.HomDom.Comp.vdomain_vrange_is_vempty have [simp]: "\<AA>\<lparr>Comp\<rparr> = 0"
    by (auto intro: \<FF>.HomDom.Comp.vsv_vrange_vempty)
  show "\<AA> = smc_0"
    by (rule smc_eqI[of \<alpha>])
      (simp_all add: prems(1) smc_0_components semicategory_smc_0)
qed

lemma (in \<Z>) smc_SemiCAT_obj_initialE:
  assumes "obj_initial (smc_SemiCAT \<alpha>) \<AA>"
  obtains "\<AA> = smc_0" 
  using assms by (auto dest: smc_SemiCAT_obj_initialD)

lemma (in \<Z>) smc_SemiCAT_obj_initial_iff[smc_SemiCAT_simps]:
  "obj_initial (smc_SemiCAT \<alpha>) \<AA> \<longleftrightarrow> \<AA> = smc_0"
  using smc_SemiCAT_obj_initialI smc_SemiCAT_obj_initialD by auto



subsection\<open>Terminal object\<close>

lemma (in \<Z>) smc_SemiCAT_obj_terminalI[smc_SemiCAT_intros]: 
  assumes "a \<in>\<^sub>\<circ> Vset \<alpha>" and "f \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "obj_terminal (smc_SemiCAT \<alpha>) (smc_1 a f)"
proof
  (
    intro obj_terminalI,
    unfold smc_op_simps smc_SemiCAT_is_arr_iff smc_SemiCAT_Obj_iff
  )
  fix \<AA> assume "semicategory \<alpha> \<AA>"
  then interpret semicategory \<alpha> \<AA> .
  show "\<exists>!\<FF>'. \<FF>' : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> smc_1 a f"
  proof
    show smcf_1: "smcf_const \<AA> (smc_1 a f) a f : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> smc_1 a f"
      by 
        (
          auto 
            intro: smc_cs_intros smc_1_is_arrI smcf_const_is_semifunctor
            simp: assms semicategory_smc_1
        )
    fix \<FF>' assume "\<FF>' : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> smc_1 a f"
    then interpret \<FF>': is_semifunctor \<alpha> \<AA> \<open>smc_1 a f\<close> \<FF>' .
    show "\<FF>' = smcf_const \<AA> (smc_1 a f) a f"
    proof(rule smcf_eqI, unfold dghm_const_components)
      show "smcf_const \<AA> (smc_1 a f) a f : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> smc_1 a f" 
        by (rule smcf_1)
      show "\<FF>'\<lparr>ObjMap\<rparr> = vconst_on (\<AA>\<lparr>Obj\<rparr>) a"
      proof(cases\<open>\<AA>\<lparr>Obj\<rparr> = 0\<close>)
        case True
        with \<FF>'.ObjMap.vbrelation_vintersection_vdomain have "\<FF>'\<lparr>ObjMap\<rparr> = 0"
          by (auto simp: smc_cs_simps)
        with True show ?thesis by simp
      next
        case False
        then have "\<D>\<^sub>\<circ> (\<FF>'\<lparr>ObjMap\<rparr>) \<noteq> 0" by (auto simp: smc_cs_simps)
        then have "\<R>\<^sub>\<circ> (\<FF>'\<lparr>ObjMap\<rparr>) \<noteq> 0"
          by (simp add: \<FF>'.ObjMap.vsv_vdomain_vempty_vrange_vempty)
        moreover from \<FF>'.smcf_ObjMap_vrange have "\<R>\<^sub>\<circ> (\<FF>'\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> set {a}"
          by (simp add: smc_1_components)
        ultimately have "\<R>\<^sub>\<circ> (\<FF>'\<lparr>ObjMap\<rparr>) = set {a}" by auto
        then show ?thesis 
          by (intro vsv.vsv_is_vconst_onI) (auto simp: smc_cs_simps) 
      qed
      show "\<FF>'\<lparr>ArrMap\<rparr> = vconst_on (\<AA>\<lparr>Arr\<rparr>) f"
      proof(cases\<open>\<AA>\<lparr>Arr\<rparr> = 0\<close>)
        case True
        with \<FF>'.ArrMap.vdomain_vrange_is_vempty have "\<FF>'\<lparr>ArrMap\<rparr> = 0"
          by (simp add: smc_cs_simps \<FF>'.smcf_ArrMap_vsv vsv.vsv_vrange_vempty)
        with True show ?thesis by simp
      next
        case False
        then have "\<D>\<^sub>\<circ> (\<FF>'\<lparr>ArrMap\<rparr>) \<noteq> 0" by (auto simp: smc_cs_simps)
        then have "\<R>\<^sub>\<circ> (\<FF>'\<lparr>ArrMap\<rparr>) \<noteq> 0" 
          by (simp add: \<FF>'.ArrMap.vsv_vdomain_vempty_vrange_vempty)
        moreover from \<FF>'.smcf_ArrMap_vrange have "\<R>\<^sub>\<circ> (\<FF>'\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> set {f}"
          by (simp add: smc_1_components)
        ultimately have "\<R>\<^sub>\<circ> (\<FF>'\<lparr>ArrMap\<rparr>) = set {f}" by auto
        then show ?thesis 
          by (intro vsv.vsv_is_vconst_onI) (auto simp: smc_cs_simps)
      qed
    qed (auto intro: smc_cs_intros)
  qed 
qed (simp add: assms semicategory_smc_1)

lemma (in \<Z>) smc_SemiCAT_obj_terminalE: 
  assumes "obj_terminal (smc_SemiCAT \<alpha>) \<BB>"
  obtains a f where "a \<in>\<^sub>\<circ> Vset \<alpha>" and "f \<in>\<^sub>\<circ> Vset \<alpha>" and "\<BB> = smc_1 a f"
  using assms
proof
  (
    elim obj_terminalE, 
    unfold smc_op_simps smc_SemiCAT_is_arr_iff smc_SemiCAT_Obj_iff
  )

  assume prems: 
    "semicategory \<alpha> \<BB>" 
    "semicategory \<alpha> \<AA> \<Longrightarrow> \<exists>!\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    for \<AA>
  interpret \<BB>: semicategory \<alpha> \<BB> by (rule prems(1))

  obtain a where \<BB>_Obj: "\<BB>\<lparr>Obj\<rparr> = set {a}" and a: "a \<in>\<^sub>\<circ> Vset \<alpha>"
  proof-
    have semicategory_smc_10: "semicategory \<alpha> (smc_10 0)"
      by (intro semicategory_smc_10) auto
    from prems(2)[OF semicategory_smc_10] obtain \<FF> 
      where \<FF>: "\<FF> : smc_10 0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
        and \<GG>\<FF>: "\<GG> : smc_10 0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB> \<Longrightarrow> \<GG> = \<FF>" for \<GG>
      by fastforce
    interpret \<FF>: is_semifunctor \<alpha> \<open>smc_10 0\<close> \<BB> \<FF> by (rule \<FF>)
    have "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = set {0}" 
      by (auto simp add: smc_10_components smc_cs_simps)
    then obtain a where vrange_\<FF>[simp]: "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = set {a}"
      by (auto intro: \<FF>.ObjMap.vsv_vdomain_vsingleton_vrange_vsingleton)
    with \<BB>.smc_Obj_vsubset_Vset \<FF>.smcf_ObjMap_vrange have [simp]: "a \<in>\<^sub>\<circ> Vset \<alpha>"
      by auto
    from \<FF>.smcf_ObjMap_vrange have "set {a} \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" by simp
    moreover have "\<BB>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> set {a}"
    proof(rule ccontr)
      assume "\<not> \<BB>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> set {a}"
      then obtain b where ba: "b \<noteq> a" and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" by force
      define \<GG> where "\<GG> = [set {\<langle>0, b\<rangle>}, 0, smc_10 0, \<BB>]\<^sub>\<circ>"
      have \<GG>_components: 
        "\<GG>\<lparr>ObjMap\<rparr> = set {\<langle>0, b\<rangle>}"
        "\<GG>\<lparr>ArrMap\<rparr> = 0"
        "\<GG>\<lparr>HomDom\<rparr> = smc_10 0"
        "\<GG>\<lparr>HomCod\<rparr> = \<BB>"
        unfolding \<GG>_def dghm_field_simps by (simp_all add: nat_omega_simps)
      have \<GG>: "\<GG> : smc_10 0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      proof(rule is_semifunctorI, unfold \<GG>_components smc_10_components)
        show "vfsequence \<GG>" unfolding \<GG>_def by auto
        show "vcard \<GG> = 4\<^sub>\<nat>"
          unfolding \<GG>_def by (auto simp: nat_omega_simps)
        show "smcf_dghm \<GG> : smc_dg (smc_10 0) \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg \<BB>"
        proof(intro is_dghmI, unfold \<GG>_components dg_10_components smc_dg_smc_10)
          show "vfsequence (smcf_dghm \<GG>)" unfolding smcf_dghm_def by simp
          show "vcard (smcf_dghm \<GG>) = 4\<^sub>\<nat>"
            unfolding smcf_dghm_def by (simp add: nat_omega_simps)
        qed 
          (
            auto simp: 
              slicing_simps slicing_intros slicing_commute smc_dg_smc_10 
              b \<GG>_components dg_10_is_arr_iff digraph_dg_10 
          )
      qed (auto simp: smc_cs_intros smc_10_is_arr_iff b vsubset_vsingleton_leftI)
      then have \<GG>_def: "\<GG> = \<FF>" by (rule \<GG>\<FF>)
      have "\<R>\<^sub>\<circ> (\<GG>\<lparr>ObjMap\<rparr>) = set {b}" unfolding \<GG>_components by simp
      with vrange_\<FF> ba show False unfolding \<GG>_def by simp  
    qed
    ultimately have "\<BB>\<lparr>Obj\<rparr> = set {a}" by simp
    with that show ?thesis by simp
  qed

  obtain f 
    where \<BB>_Arr: "\<BB>\<lparr>Arr\<rparr> = set {f}" 
      and f: "f \<in>\<^sub>\<circ> Vset \<alpha>"
      and ff_f: "f \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f = f"
  proof-
    from prems(2)[OF semicategory_smc_1, of 0 0] obtain \<FF> 
      where "\<FF> : smc_1 0 0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
        and "\<GG> : smc_1 0 0 \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB> \<Longrightarrow> \<GG> = \<FF>" 
      for \<GG>
      by fastforce
    then interpret \<FF>: is_semifunctor \<alpha> \<open>smc_1 0 0\<close> \<BB> \<FF> by force
    have "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = set {0}" 
      by (simp add: smc_cs_simps smc_1_components)
    then obtain a' where "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = set {a'}"
      by (auto intro: \<FF>.ObjMap.vsv_vdomain_vsingleton_vrange_vsingleton)
    with \<FF>.smcf_ObjMap_vrange have "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = set {a}" 
      by (auto simp: \<BB>_Obj)
    have vdomain_\<FF>: "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = set {0}"
      by (simp add: smc_cs_simps smc_1_components)
    then obtain f where vrange_\<FF>[simp]: "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = set {f}"
      by (auto intro: \<FF>.ArrMap.vsv_vdomain_vsingleton_vrange_vsingleton)
    with \<BB>.smc_Arr_vsubset_Vset \<FF>.smcf_ArrMap_vrange have [simp]: "f \<in>\<^sub>\<circ> Vset \<alpha>"
      by auto
    from \<FF>.smcf_ArrMap_vrange have f_ss_\<BB>: "set {f} \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" by simp
    then have "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" by auto
    then have f: "f : a \<mapsto>\<^bsub>\<BB>\<^esub> a"
      by (metis \<BB>_Obj \<BB>.smc_is_arrD(2,3) is_arrI vsingleton_iff)
    from vdomain_\<FF> \<FF>.ArrMap.vsv_value have [simp]: "\<FF>\<lparr>ArrMap\<rparr>\<lparr>0\<rparr> = f" by auto
    from \<FF>.smcf_is_arr_HomCod(2) have [simp]: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>0\<rparr> = a"
      by (auto simp: smc_1_is_arr_iff \<BB>_Obj)
    have "\<FF>\<lparr>ArrMap\<rparr>\<lparr>0\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>0\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>0\<rparr>"
      by (metis smc_1_Comp_app \<FF>.smcf_ArrMap_Comp smc_1_is_arr_iff)
    then have ff_f[simp]: "f \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f = f" by simp
    have id_\<BB>: "smcf_id \<BB> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      by (simp add: \<BB>.smc_smcf_id_is_semifunctor)
    interpret id_\<BB>: is_semifunctor \<alpha> \<BB> \<BB> \<open>smcf_id \<BB>\<close> by (rule id_\<BB>)
    from prems(2)[OF \<BB>.semicategory_axioms] have 
      "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB> \<Longrightarrow> \<GG> = smcf_id \<BB>" for \<GG>
      by (clarsimp simp: id_\<BB>.is_semifunctor_axioms)
    moreover from f have "smcf_const \<BB> \<BB> a f : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      by (intro smcf_const_is_semifunctor) (auto intro: smc_cs_intros)
    ultimately have const_eq_id: "smcf_const \<BB> \<BB> a f = smcf_id \<BB>" by simp
    have "\<BB>\<lparr>Arr\<rparr> \<subseteq>\<^sub>\<circ> set {f}"
    proof(rule ccontr)
      assume "\<not>\<BB>\<lparr>Arr\<rparr> \<subseteq>\<^sub>\<circ> set {f}"
      then obtain g where gf: "g \<noteq> f" and g: "g \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" by force
      have g: "g : a \<mapsto>\<^bsub>\<BB>\<^esub> a"
      proof(intro is_arrI)
        from g \<BB>_Obj show "\<BB>\<lparr>Dom\<rparr>\<lparr>g\<rparr> = a"
          by (metis \<BB>.smc_is_arrD(2) is_arr_def vsingleton_iff)
        from g \<BB>_Obj show "\<BB>\<lparr>Cod\<rparr>\<lparr>g\<rparr> = a"
          by (metis \<BB>.smc_is_arrD(3) is_arr_def vsingleton_iff)
      qed (auto simp: g)
      then have "smcf_const \<BB> \<BB> a f\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = f" 
        by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)       
      moreover from g have "smcf_id \<BB>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = g"
        by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)       
      ultimately show False using const_eq_id by (simp add: gf)
    qed
    with f_ss_\<BB> have "\<BB>\<lparr>Arr\<rparr> = set {f}" by simp
    with that show ?thesis by simp
  qed

  have "\<BB> = smc_1 a f"
  proof(rule smc_eqI [of \<alpha>], unfold smc_1_components)
    show "\<BB>\<lparr>Obj\<rparr> = set {a}" by (simp add: \<BB>_Obj)
    moreover show "\<BB>\<lparr>Arr\<rparr> = set {f}" by (simp add: \<BB>_Arr)
    ultimately have dom: "\<BB>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = a" and cod: "\<BB>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = a"
      by (metis \<BB>.smc_is_arrE is_arr_def vsingleton_iff)+
    have "\<D>\<^sub>\<circ> (\<BB>\<lparr>Dom\<rparr>) = set {f}" by (simp add: \<BB>_Arr smc_cs_simps)
    moreover from \<BB>.Dom.vsv_vrange_vempty \<BB>.smc_Dom_vdomain \<BB>.smc_Dom_vrange  
    have "\<R>\<^sub>\<circ> (\<BB>\<lparr>Dom\<rparr>) = set {a}" 
      by (fastforce simp: \<BB>_Arr \<BB>_Obj)
    ultimately show "\<BB>\<lparr>Dom\<rparr> = set {\<langle>f, a\<rangle>}"  
      using assms \<BB>.Dom.vsv_vdomain_vrange_vsingleton by simp
    have "\<D>\<^sub>\<circ> (\<BB>\<lparr>Cod\<rparr>) = set {f}" by (simp add: \<BB>_Arr smc_cs_simps)
    moreover from \<BB>.Cod.vsv_vrange_vempty \<BB>.smc_Cod_vdomain \<BB>.smc_Cod_vrange  
    have "\<R>\<^sub>\<circ> (\<BB>\<lparr>Cod\<rparr>) = set {a}" 
      by (fastforce simp: \<BB>_Arr \<BB>_Obj)
    ultimately show "\<BB>\<lparr>Cod\<rparr> = set {\<langle>f, a\<rangle>}"  
      using assms \<BB>.Cod.vsv_vdomain_vrange_vsingleton by simp
    show "\<BB>\<lparr>Comp\<rparr> = set {\<langle>[f, f]\<^sub>\<circ>, f\<rangle>}"
    proof(rule vsv_eqI)
      show [simp]: "\<D>\<^sub>\<circ> (\<BB>\<lparr>Comp\<rparr>) = \<D>\<^sub>\<circ> (set {\<langle>[f, f]\<^sub>\<circ>, f\<rangle>})"
        unfolding vdomain_vsingleton
      proof(rule vsubset_antisym)
        from \<BB>.Comp.pnop_vdomain show "\<D>\<^sub>\<circ> (\<BB>\<lparr>Comp\<rparr>) \<subseteq>\<^sub>\<circ> set {[f, f]\<^sub>\<circ>}"
          by (auto simp: \<BB>_Arr intro: smc_cs_intros) (*slow*)
        from \<BB>_Arr dom cod is_arrI show "set {[f, f]\<^sub>\<circ>} \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<BB>\<lparr>Comp\<rparr>)"
          by (metis \<BB>.smc_Comp_vdomainI vsingletonI vsubset_vsingleton_leftI)
      qed
      from ff_f show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<BB>\<lparr>Comp\<rparr>) \<Longrightarrow> \<BB>\<lparr>Comp\<rparr>\<lparr>a\<rparr> = set {\<langle>[f, f]\<^sub>\<circ>, f\<rangle>}\<lparr>a\<rparr>" 
        for a
        by simp
    qed auto
  qed (auto intro: smc_cs_intros a f semicategory_smc_1)
  with a f that show ?thesis by auto

qed

text\<open>\newpage\<close>

end