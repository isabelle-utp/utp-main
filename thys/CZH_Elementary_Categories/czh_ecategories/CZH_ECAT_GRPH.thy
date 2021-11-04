(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>GRPH\<close>\<close>
theory CZH_ECAT_GRPH
  imports 
    CZH_ECAT_Small_Category
    CZH_Foundations.CZH_SMC_GRPH
begin



subsection\<open>Background\<close>


text\<open>
The methodology for the exposition of \<open>GRPH\<close> as a category is analogous to
the one used in \cite{milehins_category_2021}
for the exposition of \<open>GRPH\<close> as a semicategory.
\<close>

named_theorems cat_GRPH_simps
named_theorems cat_GRPH_intros



subsection\<open>Definition and elementary properties\<close>

definition cat_GRPH :: "V \<Rightarrow> V"
  where "cat_GRPH \<alpha> =
    [
      set {\<CC>. digraph \<alpha> \<CC>}, 
      all_dghms \<alpha>, 
      (\<lambda>\<FF>\<in>\<^sub>\<circ>all_dghms \<alpha>. \<FF>\<lparr>HomDom\<rparr>), 
      (\<lambda>\<FF>\<in>\<^sub>\<circ>all_dghms \<alpha>. \<FF>\<lparr>HomCod\<rparr>),
      (\<lambda>\<GG>\<FF>\<in>\<^sub>\<circ>composable_arrs (dg_GRPH \<alpha>). \<GG>\<FF>\<lparr>0\<rparr> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>\<FF>\<lparr>1\<^sub>\<nat>\<rparr>),
      (\<lambda>\<CC>\<in>\<^sub>\<circ>set {\<CC>. digraph \<alpha> \<CC>}. dghm_id \<CC>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cat_GRPH_components:
  shows "cat_GRPH \<alpha>\<lparr>Obj\<rparr> = set {\<CC>. digraph \<alpha> \<CC>}"
    and "cat_GRPH \<alpha>\<lparr>Arr\<rparr> = all_dghms \<alpha>"
    and "cat_GRPH \<alpha>\<lparr>Dom\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>all_dghms \<alpha>. \<FF>\<lparr>HomDom\<rparr>)"
    and "cat_GRPH \<alpha>\<lparr>Cod\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>all_dghms \<alpha>. \<FF>\<lparr>HomCod\<rparr>)"
    and "cat_GRPH \<alpha>\<lparr>Comp\<rparr> =
      (\<lambda>\<GG>\<FF>\<in>\<^sub>\<circ>composable_arrs (dg_GRPH \<alpha>). \<GG>\<FF>\<lparr>0\<rparr> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>\<FF>\<lparr>1\<^sub>\<nat>\<rparr>)"
    and "cat_GRPH \<alpha>\<lparr>CId\<rparr> = (\<lambda>\<CC>\<in>\<^sub>\<circ>set {\<CC>. digraph \<alpha> \<CC>}. dghm_id \<CC>)"
  unfolding cat_GRPH_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma cat_smc_GRPH: "cat_smc (cat_GRPH \<alpha>) = smc_GRPH \<alpha>"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> (cat_smc (cat_GRPH \<alpha>)) = 5\<^sub>\<nat>" 
    unfolding cat_smc_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (smc_GRPH \<alpha>) = 5\<^sub>\<nat>"
    unfolding smc_GRPH_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (cat_smc (cat_GRPH \<alpha>)) = \<D>\<^sub>\<circ> (smc_GRPH \<alpha>)"
    unfolding dom_lhs dom_rhs by simp
  show 
    "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (cat_smc (cat_GRPH \<alpha>)) \<Longrightarrow> cat_smc (cat_GRPH \<alpha>)\<lparr>a\<rparr> = smc_GRPH \<alpha>\<lparr>a\<rparr>"
    for a
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral, 
        unfold cat_smc_def dg_field_simps cat_GRPH_def smc_GRPH_def
      )
      (auto simp: nat_omega_simps)
qed (auto simp: cat_smc_def smc_GRPH_def)

lemmas_with [folded cat_smc_GRPH, unfolded slicing_simps]: 
  \<comment>\<open>Digraph\<close>
  cat_GRPH_ObjI = smc_GRPH_ObjI
  and cat_GRPH_ObjD = smc_GRPH_ObjD
  and cat_GRPH_ObjE = smc_GRPH_ObjE
  and cat_GRPH_Obj_iff[cat_GRPH_simps] = smc_GRPH_Obj_iff  
  and cat_GRPH_Dom_app[cat_GRPH_simps] = smc_GRPH_Dom_app
  and cat_GRPH_Cod_app[cat_GRPH_simps] = smc_GRPH_Cod_app
  and cat_GRPH_is_arrI = smc_GRPH_is_arrI
  and cat_GRPH_is_arrD = smc_GRPH_is_arrD
  and cat_GRPH_is_arrE = smc_GRPH_is_arrE
  and cat_GRPH_is_arr_iff[cat_GRPH_simps] = smc_GRPH_is_arr_iff

lemmas_with [folded cat_smc_GRPH, unfolded slicing_simps, unfolded cat_smc_GRPH]: 
  \<comment>\<open>Semicategory\<close>
  cat_GRPH_Comp_vdomain = smc_GRPH_Comp_vdomain
  and cat_GRPH_composable_arrs_dg_GRPH = smc_GRPH_composable_arrs_dg_GRPH
  and cat_GRPH_Comp = smc_GRPH_Comp
  and cat_GRPH_Comp_app[cat_GRPH_simps] = smc_GRPH_Comp_app

lemmas_with (in \<Z>) [folded cat_smc_GRPH, unfolded slicing_simps]: 
  \<comment>\<open>Semicategory\<close>
  cat_GRPH_obj_initialI = smc_GRPH_obj_initialI
  and cat_GRPH_obj_initialD = smc_GRPH_obj_initialD
  and cat_GRPH_obj_initialE = smc_GRPH_obj_initialE
  and cat_GRPH_obj_initial_iff[cat_GRPH_simps] = smc_GRPH_obj_initial_iff
  and cat_GRPH_obj_terminalI = smc_GRPH_obj_terminalI
  and cat_GRPH_obj_terminalE = smc_GRPH_obj_terminalE


subsection\<open>Identity\<close>

lemma cat_GRPH_CId_app[cat_GRPH_simps]: 
  assumes "digraph \<alpha> \<CC>"
  shows "cat_GRPH \<alpha>\<lparr>CId\<rparr>\<lparr>\<CC>\<rparr> = dghm_id \<CC>"
  using assms unfolding cat_GRPH_components by simp

lemma cat_GRPH_CId_vdomain: "\<D>\<^sub>\<circ> (cat_GRPH \<alpha>\<lparr>CId\<rparr>) = set {\<CC>. digraph \<alpha> \<CC>}"
  unfolding cat_GRPH_components by auto

lemma cat_GRPH_CId_vrange: "\<R>\<^sub>\<circ> (cat_GRPH \<alpha>\<lparr>CId\<rparr>) \<subseteq>\<^sub>\<circ> all_dghms \<alpha>"
proof(rule vsubsetI)
  fix \<HH> assume "\<HH> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (cat_GRPH \<alpha>\<lparr>CId\<rparr>)"
  then obtain \<AA> 
    where \<HH>_def: "\<HH> = cat_GRPH \<alpha>\<lparr>CId\<rparr>\<lparr>\<AA>\<rparr>" and \<AA>: "\<AA> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (cat_GRPH \<alpha>\<lparr>CId\<rparr>)"
    unfolding cat_GRPH_components by auto
  from \<AA> have \<HH>_def': "\<HH> = dghm_id \<AA>" 
    unfolding \<HH>_def cat_GRPH_CId_vdomain by (auto simp: cat_GRPH_CId_app)
  from \<AA> digraph.dg_dghm_id_is_dghm show "\<HH> \<in>\<^sub>\<circ> all_dghms \<alpha>" 
    unfolding \<HH>_def' cat_GRPH_CId_vdomain by force
qed



subsection\<open>\<open>GRPH\<close> is a category\<close>

lemma (in \<Z>) tiny_category_cat_GRPH: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "tiny_category \<beta> (cat_GRPH \<alpha>)"
proof(intro tiny_categoryI)
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "vfsequence (cat_GRPH \<alpha>)" unfolding cat_GRPH_def by simp
  show "vcard (cat_GRPH \<alpha>) = 6\<^sub>\<nat>"
    unfolding cat_GRPH_def by (simp add: nat_omega_simps)
  show "cat_GRPH \<alpha>\<lparr>CId\<rparr>\<lparr>\<BB>\<rparr> \<circ>\<^sub>A\<^bsub>cat_GRPH \<alpha>\<^esub> \<FF> = \<FF>"
    if "\<FF> : \<AA> \<mapsto>\<^bsub>cat_GRPH \<alpha>\<^esub> \<BB>" for \<FF> \<AA> \<BB>
    using that
    unfolding cat_GRPH_is_arr_iff
    by (cs_concl cs_simp: dg_cs_simps cat_GRPH_simps cs_intro: dg_cs_intros)
  show "\<FF> \<circ>\<^sub>A\<^bsub>cat_GRPH \<alpha>\<^esub> cat_GRPH \<alpha>\<lparr>CId\<rparr>\<lparr>\<BB>\<rparr> = \<FF>"
    if "\<FF> : \<BB> \<mapsto>\<^bsub>cat_GRPH \<alpha>\<^esub> \<CC>" for \<FF> \<BB> \<CC>
    using that
    unfolding cat_GRPH_is_arr_iff
    by (cs_concl cs_simp: dg_cs_simps cat_GRPH_simps cs_intro: dg_cs_intros)
qed
  (
    simp_all add: 
      assms
      cat_smc_GRPH
      cat_GRPH_components
      digraph.dg_dghm_id_is_dghm
      cat_GRPH_is_arr_iff
      tiny_semicategory_smc_GRPH
  )



subsection\<open>Isomorphism\<close>

lemma (in \<Z>) cat_GRPH_is_arr_isomorphismI: 
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_GRPH \<alpha>\<^esub> \<BB>"
proof(intro is_arr_isomorphismI is_inverseI)
  from assms show \<FF>: "\<FF> : \<AA> \<mapsto>\<^bsub>cat_GRPH \<alpha>\<^esub> \<BB>"
    unfolding cat_GRPH_is_arr_iff by auto
  note iso_thms = is_iso_dghm_is_arr_isomorphism[OF assms]
  from iso_thms(1) show inv_\<FF>: "inv_dghm \<FF> : \<BB> \<mapsto>\<^bsub>cat_GRPH \<alpha>\<^esub> \<AA>"
    unfolding cat_GRPH_is_arr_iff by auto
  from assms show "\<FF> : \<AA> \<mapsto>\<^bsub>cat_GRPH \<alpha>\<^esub> \<BB>"
    unfolding cat_GRPH_is_arr_iff by auto
  from assms have \<AA>: "digraph \<alpha> \<AA>" and \<BB>: "digraph \<alpha> \<BB>" by auto
  show "inv_dghm \<FF> \<circ>\<^sub>A\<^bsub>cat_GRPH \<alpha>\<^esub> \<FF> = cat_GRPH \<alpha>\<lparr>CId\<rparr>\<lparr>\<AA>\<rparr>"
    unfolding cat_GRPH_CId_app[OF \<AA>] cat_GRPH_Comp_app[OF inv_\<FF> \<FF>]
    by (rule iso_thms(2))
  show "\<FF> \<circ>\<^sub>A\<^bsub>cat_GRPH \<alpha>\<^esub> inv_dghm \<FF> = cat_GRPH \<alpha>\<lparr>CId\<rparr>\<lparr>\<BB>\<rparr>"
    unfolding cat_GRPH_CId_app[OF \<BB>] cat_GRPH_Comp_app[OF \<FF> inv_\<FF>]
    by (rule iso_thms(3))
qed

lemma (in \<Z>) cat_GRPH_is_arr_isomorphismD: 
  assumes "\<FF> : \<AA> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_GRPH \<alpha>\<^esub> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  from is_arr_isomorphismD[OF assms] have \<FF>: "\<FF> : \<AA> \<mapsto>\<^bsub>cat_GRPH \<alpha>\<^esub> \<BB>" 
    and "(\<exists>\<GG>. is_inverse (cat_GRPH \<alpha>) \<GG> \<FF>)"
    by simp_all
  then obtain \<GG> where \<GG>\<FF>: "is_inverse (cat_GRPH \<alpha>) \<GG> \<FF>" by clarsimp
  then obtain \<AA>' \<BB>' where \<GG>': "\<GG> : \<BB>' \<mapsto>\<^bsub>cat_GRPH \<alpha>\<^esub> \<AA>'"
    and \<FF>': "\<FF> : \<AA>' \<mapsto>\<^bsub>cat_GRPH \<alpha>\<^esub> \<BB>'"
    and \<GG>\<FF>: "\<GG> \<circ>\<^sub>A\<^bsub>cat_GRPH \<alpha>\<^esub> \<FF> = cat_GRPH \<alpha>\<lparr>CId\<rparr>\<lparr>\<AA>'\<rparr>"
    and \<FF>\<GG>: "\<FF> \<circ>\<^sub>A\<^bsub>cat_GRPH \<alpha>\<^esub> \<GG> = cat_GRPH \<alpha>\<lparr>CId\<rparr>\<lparr>\<BB>'\<rparr>"
    by auto
  from \<FF> \<FF>' have \<AA>': "\<AA>' = \<AA>" and \<BB>': "\<BB>' = \<BB>" by auto  
  from \<FF> have \<FF>: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" unfolding cat_GRPH_is_arr_iff by simp
  then have \<AA>: "digraph \<alpha> \<AA>" and \<BB>: "digraph \<alpha> \<BB>" by auto
  from \<GG>' have "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA>" 
    unfolding \<AA>' \<BB>' cat_GRPH_is_arr_iff by simp
  moreover from \<GG>\<FF> have "\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> = dghm_id \<AA>"
    unfolding \<AA>' cat_GRPH_Comp_app[OF \<GG>' \<FF>'] cat_GRPH_CId_app[OF \<AA>] by simp
  moreover from \<FF>\<GG> have "\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> = dghm_id \<BB>"
    unfolding \<BB>' cat_GRPH_Comp_app[OF \<FF>' \<GG>'] cat_GRPH_CId_app[OF \<BB>] by simp
  ultimately show ?thesis using \<FF> by (elim is_arr_isomorphism_is_iso_dghm)
qed

lemma (in \<Z>) cat_GRPH_is_arr_isomorphismE: 
  assumes "\<FF> : \<AA> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_GRPH \<alpha>\<^esub> \<BB>"
  obtains "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by (auto dest: cat_GRPH_is_arr_isomorphismD)

lemma (in \<Z>) cat_GRPH_is_arr_isomorphism_iff[cat_GRPH_simps]: 
  "\<FF> : \<AA> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_GRPH \<alpha>\<^esub> \<BB> \<longleftrightarrow> \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  using cat_GRPH_is_arr_isomorphismI cat_GRPH_is_arr_isomorphismD by auto



subsection\<open>Isomorphic objects\<close>

lemma (in \<Z>) cat_GRPH_obj_isoI: 
  assumes "\<AA> \<approx>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<AA> \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>cat_GRPH \<alpha>\<^esub> \<BB>"
proof-
  from iso_digraphD[OF assms] obtain \<FF> where "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
    by clarsimp
  from cat_GRPH_is_arr_isomorphismI[OF this] show ?thesis by (rule obj_isoI)
qed

lemma (in \<Z>) cat_GRPH_obj_isoD: 
  assumes "\<AA> \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>cat_GRPH \<alpha>\<^esub> \<BB>"
  shows "\<AA> \<approx>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  from obj_isoD[OF assms] obtain \<FF> where "\<FF> : \<AA> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_GRPH \<alpha>\<^esub> \<BB>" 
    by clarsimp
  from cat_GRPH_is_arr_isomorphismD[OF this] show ?thesis
    by (rule iso_digraphI)
qed

lemma (in \<Z>) cat_GRPH_obj_isoE: 
  assumes "\<AA> \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>cat_GRPH \<alpha>\<^esub> \<BB>"
  obtains "\<AA> \<approx>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by (auto simp: cat_GRPH_obj_isoD)

lemma (in \<Z>) cat_GRPH_obj_iso_iff: "\<AA> \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>cat_GRPH \<alpha>\<^esub> \<BB> \<longleftrightarrow> \<AA> \<approx>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  using cat_GRPH_obj_isoI cat_GRPH_obj_isoD by (intro iffI) auto

text\<open>\newpage\<close>

end