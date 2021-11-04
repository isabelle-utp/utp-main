(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>CAT\<close>\<close>
theory CZH_ECAT_CAT
  imports CZH_SMC_CAT
begin



subsection\<open>Background\<close>


text\<open>
The subsection presents the theory of the categories of \<open>\<alpha>\<close>-categories.
It continues the development that was initiated in sections 
\ref{sec:dg_CAT}-\ref{sec:smc_CAT}.
\<close>

named_theorems cat_CAT_simps
named_theorems cat_CAT_intros



subsection\<open>Definition and elementary properties\<close>

definition cat_CAT :: "V \<Rightarrow> V"
  where "cat_CAT \<alpha> =
    [
      set {\<CC>. category \<alpha> \<CC>},
      all_cfs \<alpha>, 
      (\<lambda>\<FF>\<in>\<^sub>\<circ>all_cfs \<alpha>. \<FF>\<lparr>HomDom\<rparr>),
      (\<lambda>\<FF>\<in>\<^sub>\<circ>all_cfs \<alpha>. \<FF>\<lparr>HomCod\<rparr>),
      (\<lambda>\<GG>\<FF>\<in>\<^sub>\<circ>composable_arrs (dg_CAT \<alpha>). \<GG>\<FF>\<lparr>0\<rparr> \<circ>\<^sub>C\<^sub>F \<GG>\<FF>\<lparr>1\<^sub>\<nat>\<rparr>),
      (\<lambda>\<CC>\<in>\<^sub>\<circ>set {\<CC>. category \<alpha> \<CC>}. cf_id \<CC>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cat_CAT_components:
  shows "cat_CAT \<alpha>\<lparr>Obj\<rparr> = set {\<CC>. category \<alpha> \<CC>}"
    and "cat_CAT \<alpha>\<lparr>Arr\<rparr> = all_cfs \<alpha>"
    and "cat_CAT \<alpha>\<lparr>Dom\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>all_cfs \<alpha>. \<FF>\<lparr>HomDom\<rparr>)"
    and "cat_CAT \<alpha>\<lparr>Cod\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>all_cfs \<alpha>. \<FF>\<lparr>HomCod\<rparr>)"
    and "cat_CAT \<alpha>\<lparr>Comp\<rparr> = 
      (\<lambda>\<GG>\<FF>\<in>\<^sub>\<circ>composable_arrs (dg_CAT \<alpha>). \<GG>\<FF>\<lparr>0\<rparr> \<circ>\<^sub>C\<^sub>F \<GG>\<FF>\<lparr>1\<^sub>\<nat>\<rparr>)"
    and "cat_CAT \<alpha>\<lparr>CId\<rparr> = (\<lambda>\<CC>\<in>\<^sub>\<circ>set {\<CC>. category \<alpha> \<CC>}. cf_id \<CC>)"
  unfolding cat_CAT_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma cat_smc_CAT: "cat_smc (cat_CAT \<alpha>) = smc_CAT \<alpha>"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> (cat_smc (cat_CAT \<alpha>)) = 5\<^sub>\<nat>" 
    unfolding cat_smc_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (smc_CAT \<alpha>) = 5\<^sub>\<nat>"
    unfolding smc_CAT_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (cat_smc (cat_CAT \<alpha>)) = \<D>\<^sub>\<circ> (smc_CAT \<alpha>)"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (cat_smc (cat_CAT \<alpha>)) \<Longrightarrow> cat_smc (cat_CAT \<alpha>)\<lparr>a\<rparr> = smc_CAT \<alpha>\<lparr>a\<rparr>"
    for a
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral,
        unfold cat_smc_def dg_field_simps cat_CAT_def smc_CAT_def
      )
      (auto simp: nat_omega_simps)
qed (auto simp: cat_smc_def smc_CAT_def)

lemmas_with [folded cat_smc_CAT, unfolded slicing_simps]: 
  \<comment>\<open>Digraph\<close>
  cat_CAT_ObjI = smc_CAT_ObjI
  and cat_CAT_ObjD = smc_CAT_ObjD
  and cat_CAT_ObjE = smc_CAT_ObjE
  and cat_CAT_Obj_iff[cat_CAT_simps] = smc_CAT_Obj_iff  
  and cat_CAT_Dom_app[cat_CAT_simps] = smc_CAT_Dom_app
  and cat_CAT_Cod_app[cat_CAT_simps] = smc_CAT_Cod_app
  and cat_CAT_is_arrI = smc_CAT_is_arrI
  and cat_CAT_is_arrD = smc_CAT_is_arrD
  and cat_CAT_is_arrE = smc_CAT_is_arrE
  and cat_CAT_is_arr_iff[cat_CAT_simps] = smc_CAT_is_arr_iff

lemmas_with [folded cat_smc_CAT, unfolded slicing_simps, unfolded cat_smc_CAT]: 
  \<comment>\<open>Semicategory\<close>
  cat_CAT_Comp_vdomain = smc_CAT_Comp_vdomain
  and cat_CAT_composable_arrs_dg_CAT = smc_CAT_composable_arrs_dg_CAT
  and cat_CAT_Comp = smc_CAT_Comp
  and cat_CAT_Comp_app[cat_CAT_simps] = smc_CAT_Comp_app
  and cat_CAT_Comp_vrange = smc_CAT_Comp_vrange

lemmas_with (in \<Z>) [folded cat_smc_CAT, unfolded slicing_simps]: 
  \<comment>\<open>Semicategory\<close>
  cat_CAT_obj_initialI = smc_CAT_obj_initialI
  and cat_CAT_obj_initialD = smc_CAT_obj_initialD
  and cat_CAT_obj_initialE = smc_CAT_obj_initialE
  and cat_CAT_obj_initial_iff[cat_CAT_simps] = smc_CAT_obj_initial_iff
  and cat_CAT_obj_terminalI = smc_CAT_obj_terminalI
  and cat_CAT_obj_terminalE = smc_CAT_obj_terminalE



subsection\<open>Identity\<close>

lemma cat_CAT_CId_app[cat_CAT_simps]: 
  assumes "category \<alpha> \<CC>"
  shows "cat_CAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<CC>\<rparr> = cf_id \<CC>"
  using assms unfolding cat_CAT_components by simp

lemma cat_CAT_CId_vdomain: "\<D>\<^sub>\<circ> (cat_CAT \<alpha>\<lparr>CId\<rparr>) = set {\<CC>. category \<alpha> \<CC>}"
  unfolding cat_CAT_components by auto

lemma cat_CAT_CId_vrange: "\<R>\<^sub>\<circ> (cat_CAT \<alpha>\<lparr>CId\<rparr>) \<subseteq>\<^sub>\<circ> all_cfs \<alpha>"
proof(rule vsubsetI)
  fix \<HH> assume "\<HH> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (cat_CAT \<alpha>\<lparr>CId\<rparr>)"
  then obtain \<AA> 
    where \<HH>_def: "\<HH> = cat_CAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<AA>\<rparr>" 
      and \<AA>: "\<AA> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (cat_CAT \<alpha>\<lparr>CId\<rparr>)"
    unfolding cat_CAT_components by auto
  from \<AA> have \<HH>_def': "\<HH> = cf_id \<AA>" 
    unfolding \<HH>_def cat_CAT_CId_vdomain by (auto simp: cat_CAT_CId_app)
  from \<AA> category.cat_cf_id_is_functor show "\<HH> \<in>\<^sub>\<circ> all_cfs \<alpha>"
    unfolding \<HH>_def' cat_CAT_CId_vdomain by force
qed



subsection\<open>\<open>CAT\<close> is a category\<close>

lemma (in \<Z>) tiny_category_cat_CAT: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "tiny_category \<beta> (cat_CAT \<alpha>)"
proof(intro tiny_categoryI)
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "vfsequence (cat_CAT \<alpha>)" unfolding cat_CAT_def by simp
  show "vcard (cat_CAT \<alpha>) = 6\<^sub>\<nat>"
    unfolding cat_CAT_def by (simp add: nat_omega_simps)
  show "\<FF> : \<AA> \<mapsto>\<^bsub>cat_CAT \<alpha>\<^esub> \<BB> \<Longrightarrow> cat_CAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<BB>\<rparr> \<circ>\<^sub>A\<^bsub>cat_CAT \<alpha>\<^esub> \<FF> = \<FF>" 
    for \<FF> \<AA> \<BB>
  proof-
    assume prems: "\<FF> : \<AA> \<mapsto>\<^bsub>cat_CAT \<alpha>\<^esub> \<BB>"
    then have b: "category \<alpha> \<BB>" unfolding cat_CAT_is_arr_iff by auto
    with digraph.dg_dghm_id_is_dghm have 
      "cat_CAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<BB>\<rparr> : \<BB> \<mapsto>\<^bsub>cat_CAT \<alpha>\<^esub> \<BB>"
      by 
        (
          simp add: 
            cat_CAT_CId_app cat_CAT_is_arrI category.cat_cf_id_is_functor
        )
    with prems b show "cat_CAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<BB>\<rparr> \<circ>\<^sub>A\<^bsub>cat_CAT \<alpha>\<^esub> \<FF> = \<FF>" 
      by
        (
          simp add: 
            cat_CAT_CId_app 
            cat_CAT_Comp_app 
            cat_CAT_is_arr_iff
            is_functor.cf_cf_comp_cf_id_left
        )
  qed
  show "\<FF> : \<BB> \<mapsto>\<^bsub>cat_CAT \<alpha>\<^esub> \<CC> \<Longrightarrow> \<FF> \<circ>\<^sub>A\<^bsub>cat_CAT \<alpha>\<^esub> cat_CAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<BB>\<rparr> = \<FF>" 
    for \<FF> \<BB> \<CC>
  proof-
    assume prems: "\<FF> : \<BB> \<mapsto>\<^bsub>cat_CAT \<alpha>\<^esub> \<CC>"
    then have b: "category \<alpha> \<BB>" unfolding cat_CAT_is_arr_iff by auto
    then have "cat_CAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<BB>\<rparr> : \<BB> \<mapsto>\<^bsub>cat_CAT \<alpha>\<^esub> \<BB>"
      by 
        (
          simp add: 
            cat_CAT_CId_app cat_CAT_is_arrI category.cat_cf_id_is_functor
        )
    with prems b show "\<FF> \<circ>\<^sub>A\<^bsub>cat_CAT \<alpha>\<^esub> cat_CAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<BB>\<rparr> = \<FF>"
      by 
        (
          auto 
            simp: cat_CAT_CId_app cat_CAT_Comp_app cat_CAT_is_arr_iff
            intro: is_functor.cf_cf_comp_cf_id_right 
        )
  qed
qed 
  (
    simp_all add:
      assms
      cat_smc_CAT
      cat_CAT_components 
      \<Z>.intro 
      \<Z>_Limit_\<alpha>\<omega> 
      \<Z>_\<omega>_\<alpha>\<omega>
      cat_CAT_is_arr_iff
      tiny_semicategory_smc_CAT
      category.cat_cf_id_is_functor
  )

lemmas [cat_cs_intros] = \<Z>.tiny_category_cat_CAT



subsection\<open>Isomorphism\<close>

lemma (in \<Z>) cat_CAT_is_arr_isomorphismI: 
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_CAT \<alpha>\<^esub> \<BB>"
proof(intro is_arr_isomorphismI is_inverseI)
  from assms show \<FF>: "\<FF> : \<AA> \<mapsto>\<^bsub>cat_CAT \<alpha>\<^esub> \<BB>"
    unfolding cat_CAT_is_arr_iff by auto
  note iso_thms = is_iso_functor_is_arr_isomorphism[OF assms]
  from iso_thms(1) show inv_\<FF>: "inv_cf \<FF> : \<BB> \<mapsto>\<^bsub>cat_CAT \<alpha>\<^esub> \<AA>"
    unfolding cat_CAT_is_arr_iff by auto
  from assms show "\<FF> : \<AA> \<mapsto>\<^bsub>cat_CAT \<alpha>\<^esub> \<BB>"
    unfolding cat_CAT_is_arr_iff by auto
  from assms have \<AA>: "category \<alpha> \<AA>" and \<BB>: "category \<alpha> \<BB>" by auto
  show "inv_cf \<FF> \<circ>\<^sub>A\<^bsub>cat_CAT \<alpha>\<^esub> \<FF> = cat_CAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<AA>\<rparr>"
    unfolding cat_CAT_CId_app[OF \<AA>] cat_CAT_Comp_app[OF inv_\<FF> \<FF>]
    by (rule iso_thms(2))
  show "\<FF> \<circ>\<^sub>A\<^bsub>cat_CAT \<alpha>\<^esub> inv_cf \<FF> = cat_CAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<BB>\<rparr>"
    unfolding cat_CAT_CId_app[OF \<BB>] cat_CAT_Comp_app[OF \<FF> inv_\<FF>]
    by (rule iso_thms(3))
qed

lemma (in \<Z>) cat_CAT_is_arr_isomorphismD: 
  assumes "\<FF> : \<AA> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_CAT \<alpha>\<^esub> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  from is_arr_isomorphismD[OF assms] have \<FF>: "\<FF> : \<AA> \<mapsto>\<^bsub>cat_CAT \<alpha>\<^esub> \<BB>" 
    and "(\<exists>\<GG>. is_inverse (cat_CAT \<alpha>) \<GG> \<FF>)"
    by simp_all
  then obtain \<GG> where "is_inverse (cat_CAT \<alpha>) \<GG> \<FF>" by clarsimp
  then obtain \<AA>' \<BB>' where \<GG>': "\<GG> : \<BB>' \<mapsto>\<^bsub>cat_CAT \<alpha>\<^esub> \<AA>'"
    and \<FF>': "\<FF> : \<AA>' \<mapsto>\<^bsub>cat_CAT \<alpha>\<^esub> \<BB>'"
    and \<GG>\<FF>: "\<GG> \<circ>\<^sub>A\<^bsub>cat_CAT \<alpha>\<^esub> \<FF> = cat_CAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<AA>'\<rparr>"
    and \<FF>\<GG>: "\<FF> \<circ>\<^sub>A\<^bsub>cat_CAT \<alpha>\<^esub> \<GG> = cat_CAT \<alpha>\<lparr>CId\<rparr>\<lparr>\<BB>'\<rparr>"
    by auto
  from \<FF> \<FF>' have \<AA>': "\<AA>' = \<AA>" and \<BB>': "\<BB>' = \<BB>" by auto  
  from \<FF> have \<FF>: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" unfolding cat_CAT_is_arr_iff by simp
  then have \<AA>: "category \<alpha> \<AA>" and \<BB>: "category \<alpha> \<BB>" by auto
  from \<GG>' have "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
    unfolding \<AA>' \<BB>' cat_CAT_is_arr_iff by simp
  moreover from \<GG>\<FF> have "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> = cf_id \<AA>"
    unfolding \<AA>' cat_CAT_Comp_app[OF \<GG>' \<FF>'] cat_CAT_CId_app[OF \<AA>] 
    by simp
  moreover from \<FF>\<GG> have "\<FF> \<circ>\<^sub>C\<^sub>F \<GG> = cf_id \<BB>"
    unfolding \<BB>' cat_CAT_Comp_app[OF \<FF>' \<GG>'] cat_CAT_CId_app[OF \<BB>] 
    by simp
  ultimately show ?thesis 
    using \<FF> by (elim is_arr_isomorphism_is_iso_functor)
qed

lemma (in \<Z>) cat_CAT_is_arr_isomorphismE: 
  assumes "\<FF> : \<AA> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_CAT \<alpha>\<^esub> \<BB>"
  obtains "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by (auto dest: cat_CAT_is_arr_isomorphismD)

lemma (in \<Z>) cat_CAT_is_arr_isomorphism_iff[cat_CAT_simps]: 
  "\<FF> : \<AA> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_CAT \<alpha>\<^esub> \<BB> \<longleftrightarrow> \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  using cat_CAT_is_arr_isomorphismI cat_CAT_is_arr_isomorphismD by auto



subsection\<open>Isomorphic objects\<close>

lemma (in \<Z>) cat_CAT_obj_isoI: 
  assumes "\<AA> \<approx>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<AA> \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>cat_CAT \<alpha>\<^esub> \<BB>"
proof-
  from iso_categoryD[OF assms] obtain \<FF> where "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
    by clarsimp
  from cat_CAT_is_arr_isomorphismI[OF this] show ?thesis by (rule obj_isoI)
qed

lemma (in \<Z>) cat_CAT_obj_isoD: 
  assumes "\<AA> \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>cat_CAT \<alpha>\<^esub> \<BB>"
  shows "\<AA> \<approx>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  from obj_isoD[OF assms] obtain \<FF> where "\<FF> : \<AA> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_CAT \<alpha>\<^esub> \<BB>" 
    by clarsimp
  from cat_CAT_is_arr_isomorphismD[OF this] show ?thesis by (rule iso_categoryI)
qed

lemma (in \<Z>) cat_CAT_obj_isoE: 
  assumes "\<AA> \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>cat_CAT \<alpha>\<^esub> \<BB>"
  obtains "\<AA> \<approx>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by (auto simp: cat_CAT_obj_isoD)

lemma (in \<Z>) cat_CAT_obj_iso_iff[cat_CAT_simps]: 
  "\<AA> \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>cat_CAT \<alpha>\<^esub> \<BB> \<longleftrightarrow> \<AA> \<approx>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  using cat_CAT_obj_isoI cat_CAT_obj_isoD by (intro iffI) auto

text\<open>\newpage\<close>

end