(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>SemiCAT\<close>\<close>
theory CZH_ECAT_SemiCAT
  imports 
    CZH_Foundations.CZH_SMC_SemiCAT
    CZH_ECAT_Small_Category
    CZH_ECAT_Simple
begin



subsection\<open>Background\<close>


text\<open>
The methodology for the exposition of \<open>SemiCAT\<close> as a category 
is analogous to the one used in \cite{milehins_category_2021} 
for the exposition of \<open>SemiCAT\<close> as a semicategory.
\<close>

named_theorems cat_SemiCAT_simps
named_theorems cat_SemiCAT_intros



subsection\<open>Definition and elementary properties\<close>

definition cat_SemiCAT :: "V \<Rightarrow> V"
  where "cat_SemiCAT \<alpha> =
    [
      set {\<CC>. semicategory \<alpha> \<CC>}, 
      all_smcfs \<alpha>, 
      (\<lambda>\<FF>\<in>\<^sub>\<circ>all_smcfs \<alpha>. \<FF>\<lparr>HomDom\<rparr>), 
      (\<lambda>\<FF>\<in>\<^sub>\<circ>all_smcfs \<alpha>. \<FF>\<lparr>HomCod\<rparr>),
      (\<lambda>\<GG>\<FF>\<in>\<^sub>\<circ>composable_arrs (dg_SemiCAT \<alpha>). \<GG>\<FF>\<lparr>0\<rparr> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>\<FF>\<lparr>1\<^sub>\<nat>\<rparr>),
      (\<lambda>\<CC>\<in>\<^sub>\<circ>set {\<CC>. semicategory \<alpha> \<CC>}. smcf_id \<CC>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cat_SemiCAT_components:
  shows "cat_SemiCAT \<alpha>\<lparr>Obj\<rparr> = set {\<CC>. semicategory \<alpha> \<CC>}"
    and "cat_SemiCAT \<alpha>\<lparr>Arr\<rparr> = all_smcfs \<alpha>"
    and "cat_SemiCAT \<alpha>\<lparr>Dom\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>all_smcfs \<alpha>. \<FF>\<lparr>HomDom\<rparr>)"
    and "cat_SemiCAT \<alpha>\<lparr>Cod\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>all_smcfs \<alpha>. \<FF>\<lparr>HomCod\<rparr>)"
    and "cat_SemiCAT \<alpha>\<lparr>Comp\<rparr> = 
      (\<lambda>\<GG>\<FF>\<in>\<^sub>\<circ>composable_arrs (dg_SemiCAT \<alpha>). \<GG>\<FF>\<lparr>0\<rparr> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>\<FF>\<lparr>1\<^sub>\<nat>\<rparr>)"
    and "cat_SemiCAT \<alpha>\<lparr>CId\<rparr> = (\<lambda>\<CC>\<in>\<^sub>\<circ>set {\<CC>. semicategory \<alpha> \<CC>}. smcf_id \<CC>)"
  unfolding cat_SemiCAT_def dg_field_simps 
  by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma cat_smc_SemiCAT: "cat_smc (cat_SemiCAT \<alpha>) = smc_SemiCAT \<alpha>"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> (cat_smc (cat_SemiCAT \<alpha>)) = 5\<^sub>\<nat>" 
    unfolding cat_smc_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (smc_SemiCAT \<alpha>) = 5\<^sub>\<nat>"
    unfolding smc_SemiCAT_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (cat_smc (cat_SemiCAT \<alpha>)) = \<D>\<^sub>\<circ> (smc_SemiCAT \<alpha>)"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (cat_smc (cat_SemiCAT \<alpha>)) \<Longrightarrow> 
    cat_smc (cat_SemiCAT \<alpha>)\<lparr>a\<rparr> = smc_SemiCAT \<alpha>\<lparr>a\<rparr>"
    for a
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral, 
        unfold cat_smc_def dg_field_simps cat_SemiCAT_def smc_SemiCAT_def
      )
      (auto simp: nat_omega_simps)
qed (auto simp: cat_smc_def smc_SemiCAT_def)

lemmas_with [folded cat_smc_SemiCAT, unfolded slicing_simps]: 
  \<comment>\<open>Digraph\<close>
  cat_SemiCAT_ObjI = smc_SemiCAT_ObjI
  and cat_SemiCAT_ObjD = smc_SemiCAT_ObjD
  and cat_SemiCAT_ObjE = smc_SemiCAT_ObjE
  and cat_SemiCAT_Obj_iff[cat_SemiCAT_simps] = smc_SemiCAT_Obj_iff  
  and cat_SemiCAT_Dom_app[cat_SemiCAT_simps] = smc_SemiCAT_Dom_app
  and cat_SemiCAT_Cod_app[cat_SemiCAT_simps] = smc_SemiCAT_Cod_app
  and cat_SemiCAT_is_arrI = smc_SemiCAT_is_arrI
  and cat_SemiCAT_is_arrD = smc_SemiCAT_is_arrD
  and cat_SemiCAT_is_arrE = smc_SemiCAT_is_arrE
  and cat_SemiCAT_is_arr_iff[cat_SemiCAT_simps] = smc_SemiCAT_is_arr_iff

lemmas_with [
    folded cat_smc_SemiCAT, unfolded slicing_simps, unfolded cat_smc_SemiCAT
    ]: 
  \<comment>\<open>Semicategory\<close>
  cat_SemiCAT_Comp_vdomain = smc_SemiCAT_Comp_vdomain
  and cat_SemiCAT_composable_arrs_dg_SemiCAT = 
    smc_SemiCAT_composable_arrs_dg_SemiCAT
  and cat_SemiCAT_Comp = smc_SemiCAT_Comp
  and cat_SemiCAT_Comp_app[cat_SemiCAT_simps] = smc_SemiCAT_Comp_app
  and cat_SemiCAT_Comp_vrange = smc_SemiCAT_Comp_vrange

lemmas_with (in \<Z>) [folded cat_smc_SemiCAT, unfolded slicing_simps]: 
  \<comment>\<open>Semicategory\<close>
  cat_SemiCAT_obj_initialI = smc_SemiCAT_obj_initialI
  and cat_SemiCAT_obj_initialD = smc_SemiCAT_obj_initialD
  and cat_SemiCAT_obj_initialE = smc_SemiCAT_obj_initialE
  and cat_SemiCAT_obj_initial_iff[cat_SemiCAT_simps] = 
    smc_SemiCAT_obj_initial_iff
  and cat_SemiCAT_obj_terminalI = smc_SemiCAT_obj_terminalI
  and cat_SemiCAT_obj_terminalE = smc_SemiCAT_obj_terminalE



subsection\<open>Identity\<close>

lemma cat_SemiCAT_CId_app[cat_SemiCAT_simps]: 
  assumes "semicategory \<alpha> \<CC>"
  shows "cat_SemiCAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<CC>\<rparr> = smcf_id \<CC>"
  using assms unfolding cat_SemiCAT_components by simp

lemma cat_SemiCAT_CId_vdomain[cat_SemiCAT_simps]: 
  "\<D>\<^sub>\<circ> (cat_SemiCAT \<alpha>\<lparr>CId\<rparr>) = set {\<CC>. semicategory \<alpha> \<CC>}"
  unfolding cat_SemiCAT_components by auto

lemma cat_SemiCAT_CId_vrange: "\<R>\<^sub>\<circ> (cat_SemiCAT \<alpha>\<lparr>CId\<rparr>) \<subseteq>\<^sub>\<circ> all_smcfs \<alpha>"
proof(rule vsubsetI)
  fix \<HH> assume "\<HH> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (cat_SemiCAT \<alpha>\<lparr>CId\<rparr>)"
  then obtain \<AA> 
    where \<HH>_def: "\<HH> = cat_SemiCAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<AA>\<rparr>" 
      and \<AA>: "\<AA> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (cat_SemiCAT \<alpha>\<lparr>CId\<rparr>)"
    unfolding cat_SemiCAT_components by auto
  from \<AA> have \<HH>_def': "\<HH> = smcf_id \<AA>" 
    unfolding \<HH>_def cat_SemiCAT_CId_vdomain by (auto simp: cat_SemiCAT_CId_app)
  from \<AA> semicategory.smc_smcf_id_is_semifunctor show "\<HH> \<in>\<^sub>\<circ> all_smcfs \<alpha>"
    unfolding \<HH>_def' cat_SemiCAT_CId_vdomain by force
qed



subsection\<open>\<open>SemiCAT\<close> is a category\<close>

lemma (in \<Z>) tiny_category_cat_SemiCAT: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "tiny_category \<beta> (cat_SemiCAT \<alpha>)"
proof(intro tiny_categoryI)
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "vfsequence (cat_SemiCAT \<alpha>)" unfolding cat_SemiCAT_def by simp
  show "vcard (cat_SemiCAT \<alpha>) = 6\<^sub>\<nat>"
    unfolding cat_SemiCAT_def by (simp add: nat_omega_simps)
  show "cat_SemiCAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<BB>\<rparr> \<circ>\<^sub>A\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<FF> = \<FF>"
    if "\<FF> : \<AA> \<mapsto>\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<BB>" for \<FF> \<AA> \<BB>
    using that 
    unfolding cat_SemiCAT_is_arr_iff
    by (cs_concl cs_simp: smc_cs_simps cat_SemiCAT_simps cs_intro: smc_cs_intros)
  show "\<FF> \<circ>\<^sub>A\<^bsub>cat_SemiCAT \<alpha>\<^esub> cat_SemiCAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<BB>\<rparr> = \<FF>"
    if "\<FF> : \<BB> \<mapsto>\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<CC>" for \<FF> \<BB> \<CC>
    using that 
    unfolding cat_SemiCAT_is_arr_iff
    by (cs_concl cs_simp: smc_cs_simps cat_SemiCAT_simps cs_intro: smc_cs_intros)
qed 
  (
    simp_all add: 
      assms
      cat_smc_SemiCAT
      cat_SemiCAT_components
      cat_SemiCAT_is_arr_iff
      tiny_semicategory_smc_SemiCAT
      semicategory.smc_smcf_id_is_semifunctor
  )



subsection\<open>Isomorphism\<close>

lemma cat_SemiCAT_is_arr_isomorphismI: 
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<BB>"
proof(intro is_arr_isomorphismI is_inverseI)
  interpret is_iso_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms)
  from assms show \<FF>: "\<FF> : \<AA> \<mapsto>\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<BB>"
    unfolding cat_SemiCAT_is_arr_iff by auto
  note iso_thms = is_iso_semifunctor_is_arr_isomorphism[OF assms]
  from iso_thms(1) show inv_\<FF>: "inv_smcf \<FF> : \<BB> \<mapsto>\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<AA>"
    unfolding cat_SemiCAT_is_arr_iff by auto
  from assms show "\<FF> : \<AA> \<mapsto>\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<BB>"
    unfolding cat_SemiCAT_is_arr_iff by auto
  from assms have \<AA>: "semicategory \<alpha> \<AA>" and \<BB>: "semicategory \<alpha> \<BB>" by auto
  show "inv_smcf \<FF> \<circ>\<^sub>A\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<FF> = cat_SemiCAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<AA>\<rparr>"
    unfolding cat_SemiCAT_CId_app[OF \<AA>] cat_SemiCAT_Comp_app[OF inv_\<FF> \<FF>]
    by (rule iso_thms(2))
  show "\<FF> \<circ>\<^sub>A\<^bsub>cat_SemiCAT \<alpha>\<^esub> inv_smcf \<FF> = cat_SemiCAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<BB>\<rparr>"
    unfolding cat_SemiCAT_CId_app[OF \<BB>] cat_SemiCAT_Comp_app[OF \<FF> inv_\<FF>]
    by (rule iso_thms(3))
qed

lemma cat_SemiCAT_is_arr_isomorphismD: 
  assumes "\<FF> : \<AA> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  from is_arr_isomorphismD[OF assms] have \<FF>: "\<FF> : \<AA> \<mapsto>\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<BB>" 
    and "(\<exists>\<GG>. is_inverse (cat_SemiCAT \<alpha>) \<GG> \<FF>)"
    by simp_all
  then obtain \<GG> where \<GG>\<FF>: "is_inverse (cat_SemiCAT \<alpha>) \<GG> \<FF>" by clarsimp
  then obtain \<AA>' \<BB>' where \<GG>': "\<GG> : \<BB>' \<mapsto>\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<AA>'"
    and \<FF>': "\<FF> : \<AA>' \<mapsto>\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<BB>'"
    and \<GG>\<FF>: "\<GG> \<circ>\<^sub>A\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<FF> = cat_SemiCAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<AA>'\<rparr>"
    and \<FF>\<GG>: "\<FF> \<circ>\<^sub>A\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<GG> = cat_SemiCAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<BB>'\<rparr>"
    by auto
  from \<FF> \<FF>' have \<AA>': "\<AA>' = \<AA>" and \<BB>': "\<BB>' = \<BB>" by auto  
  from \<FF> have \<FF>: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" unfolding cat_SemiCAT_is_arr_iff by simp
  interpret is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule \<FF>)
  have \<AA>: "semicategory \<alpha> \<AA>" and \<BB>: "semicategory \<alpha> \<BB>" 
    by (cs_concl cs_intro: smc_cs_intros)+
  from \<GG>' have \<GG>: "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
    unfolding \<AA>' \<BB>' cat_SemiCAT_is_arr_iff by simp
  moreover from \<GG>\<FF> have "\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> = smcf_id \<AA>"
    unfolding \<AA>' cat_SemiCAT_Comp_app[OF \<GG>' \<FF>'] cat_SemiCAT_CId_app[OF \<AA>] 
    by simp
  moreover from \<FF>\<GG> have "\<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> = smcf_id \<BB>"
    unfolding \<BB>' cat_SemiCAT_Comp_app[OF \<FF>' \<GG>'] cat_SemiCAT_CId_app[OF \<BB>] 
    by simp
  ultimately show ?thesis 
    using \<FF> by (elim is_arr_isomorphism_is_iso_semifunctor)
qed

lemma cat_SemiCAT_is_arr_isomorphismE: 
  assumes "\<FF> : \<AA> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<BB>"
  obtains "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by (auto dest: cat_SemiCAT_is_arr_isomorphismD)

lemma cat_SemiCAT_is_arr_isomorphism_iff[cat_SemiCAT_simps]: 
  "\<FF> : \<AA> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<BB> \<longleftrightarrow> \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  using cat_SemiCAT_is_arr_isomorphismI cat_SemiCAT_is_arr_isomorphismD by auto



subsection\<open>Isomorphic objects\<close>

lemma cat_SemiCAT_obj_isoI: 
  assumes "\<AA> \<approx>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<AA> \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<BB>"
proof-
  from iso_semicategoryD[OF assms] obtain \<FF> where "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
    by clarsimp
  from cat_SemiCAT_is_arr_isomorphismI[OF this] show ?thesis by (rule obj_isoI)
qed

lemma cat_SemiCAT_obj_isoD: 
  assumes "\<AA> \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<BB>"
  shows "\<AA> \<approx>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  from obj_isoD[OF assms] obtain \<FF> where "\<FF> : \<AA> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<BB>" 
    by clarsimp
  from cat_SemiCAT_is_arr_isomorphismD[OF this] show ?thesis
    by (rule iso_semicategoryI)
qed

lemma cat_SemiCAT_obj_isoE: 
  assumes "\<AA> \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<BB>"
  obtains "\<AA> \<approx>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by (auto simp: cat_SemiCAT_obj_isoD)

lemma cat_SemiCAT_obj_iso_iff[cat_SemiCAT_simps]: 
  "\<AA> \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>cat_SemiCAT \<alpha>\<^esub> \<BB> \<longleftrightarrow> \<AA> \<approx>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  using cat_SemiCAT_obj_isoI cat_SemiCAT_obj_isoD by (intro iffI) auto

text\<open>\newpage\<close>

end