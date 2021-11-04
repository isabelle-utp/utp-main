(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>FUNCT\<close> and \<open>Funct\<close>\<close>
theory CZH_ECAT_FUNCT
  imports
    CZH_SMC_FUNCT
    CZH_ECAT_Subcategory
    CZH_ECAT_NTCF
begin



subsection\<open>Background\<close>


text\<open>
The subsection presents the theory of the categories of \<open>\<alpha>\<close>-functors
between two \<open>\<alpha>\<close>-categories.
It continues the development that was initiated in sections 
\ref{sec:dg_FUNCT} and \ref{sec:smc_FUNCT}.
A general reference for this section is Chapter II-4 in 
\cite{mac_lane_categories_2010}.
\<close>

named_theorems cat_FUNCT_cs_simps
named_theorems cat_FUNCT_cs_intros

lemmas [cat_FUNCT_cs_simps] = cat_map_cs_simps
lemmas [cat_FUNCT_cs_intros] = cat_map_cs_intros



subsection\<open>\<open>FUNCT\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition cat_FUNCT :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cat_FUNCT \<alpha> \<AA> \<BB> =
    [
      cf_maps \<alpha> \<AA> \<BB>,
      ntcf_arrows \<alpha> \<AA> \<BB>,
      (\<lambda>\<NN>\<in>\<^sub>\<circ>ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTDom\<rparr>),
      (\<lambda>\<NN>\<in>\<^sub>\<circ>ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTCod\<rparr>),
      (\<lambda>\<MM>\<NN>\<in>\<^sub>\<circ>composable_arrs (dg_FUNCT \<alpha> \<AA> \<BB>). \<MM>\<NN>\<lparr>0\<rparr> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>\<AA>,\<BB>\<^esub> \<MM>\<NN>\<lparr>1\<^sub>\<nat>\<rparr>),
      (\<lambda>\<FF>\<in>\<^sub>\<circ>cf_maps \<alpha> \<AA> \<BB>. ntcf_arrow_id \<AA> \<BB> \<FF>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cat_FUNCT_components:
  shows [cat_FUNCT_cs_simps]: "cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr> = cf_maps \<alpha> \<AA> \<BB>"
    and "cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Arr\<rparr> = ntcf_arrows \<alpha> \<AA> \<BB>"
    and "cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Dom\<rparr> = (\<lambda>\<NN>\<in>\<^sub>\<circ>ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTDom\<rparr>)"
    and "cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Cod\<rparr> = (\<lambda>\<NN>\<in>\<^sub>\<circ>ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTCod\<rparr>)"
    and "cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr> =
      (\<lambda>\<MM>\<NN>\<in>\<^sub>\<circ>composable_arrs (dg_FUNCT \<alpha> \<AA> \<BB>). \<MM>\<NN>\<lparr>0\<rparr> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>\<AA>,\<BB>\<^esub> \<MM>\<NN>\<lparr>1\<^sub>\<nat>\<rparr>)"
    and "cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>CId\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>cf_maps \<alpha> \<AA> \<BB>. ntcf_arrow_id \<AA> \<BB> \<FF>)"
  unfolding cat_FUNCT_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma cat_smc_FUNCT: "cat_smc (cat_FUNCT \<alpha> \<AA> \<BB>) = smc_FUNCT \<alpha> \<AA> \<BB>"
proof(rule vsv_eqI)
  show "vsv (cat_smc (cat_FUNCT \<alpha> \<AA> \<BB>))" unfolding cat_smc_def by auto
  show "vsv (smc_FUNCT \<alpha> \<AA> \<BB>)" unfolding smc_FUNCT_def by auto
  have dom_lhs: "\<D>\<^sub>\<circ> (cat_smc (cat_FUNCT \<alpha> \<AA> \<BB>)) = 5\<^sub>\<nat>" 
    unfolding cat_smc_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (smc_FUNCT \<alpha> \<AA> \<BB>) = 5\<^sub>\<nat>"
    unfolding smc_FUNCT_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (cat_smc (cat_FUNCT \<alpha> \<AA> \<BB>)) = \<D>\<^sub>\<circ> (smc_FUNCT \<alpha> \<AA> \<BB>)"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (cat_smc (cat_FUNCT \<alpha> \<AA> \<BB>)) \<Longrightarrow>
    cat_smc (cat_FUNCT \<alpha> \<AA> \<BB>)\<lparr>a\<rparr> = smc_FUNCT \<alpha> \<AA> \<BB>\<lparr>a\<rparr>"
    for a
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral, 
        unfold cat_smc_def dg_field_simps cat_FUNCT_def smc_FUNCT_def
      )
      (auto simp: nat_omega_simps)
qed

context is_ntcf
begin

lemmas_with [folded cat_smc_FUNCT, unfolded slicing_simps]: 
  cat_FUNCT_Dom_app = smc_FUNCT_Dom_app
  and cat_FUNCT_Cod_app = smc_FUNCT_Cod_app

end

lemmas [smc_FUNCT_cs_simps] = 
  is_ntcf.cat_FUNCT_Dom_app
  is_ntcf.cat_FUNCT_Cod_app

lemmas_with [folded cat_smc_FUNCT, unfolded slicing_simps]: 
  cat_FUNCT_Dom_vsv[intro] = smc_FUNCT_Dom_vsv
  and cat_FUNCT_Dom_vdomain[cat_FUNCT_cs_simps] = smc_FUNCT_Dom_vdomain
  and cat_FUNCT_Cod_vsv[intro] = smc_FUNCT_Cod_vsv
  and cat_FUNCT_Cod_vdomain[cat_FUNCT_cs_simps] = smc_FUNCT_Cod_vdomain
  and cat_FUNCT_Dom_vrange = smc_FUNCT_Dom_vrange
  and cat_FUNCT_Cod_vrange = smc_FUNCT_Cod_vrange
  and cat_FUNCT_is_arrI = smc_FUNCT_is_arrI
  and cat_FUNCT_is_arrI'[cat_FUNCT_cs_intros] = smc_FUNCT_is_arrI'
  and cat_FUNCT_is_arrD = smc_FUNCT_is_arrD
  and cat_FUNCT_is_arrE[elim] = smc_FUNCT_is_arrE

lemmas_with [folded cat_smc_FUNCT, unfolded slicing_simps]: 
  cat_FUNCT_Comp_app[cat_FUNCT_cs_simps] = smc_FUNCT_Comp_app


subsubsection\<open>Identity\<close>

mk_VLambda cat_FUNCT_components(6)
  |vsv cat_FUNCT_CId_vsv[cat_FUNCT_cs_intros]|
  |vdomain cat_FUNCT_CId_vdomain[cat_FUNCT_cs_simps]|
  |app cat_FUNCT_CId_app[cat_FUNCT_cs_simps]|

lemma smc_FUNCT_CId_vrange: "\<R>\<^sub>\<circ> (cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>) \<subseteq>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>"
  unfolding cat_FUNCT_components
proof(rule vrange_VLambda_vsubset)
  fix x assume "x \<in>\<^sub>\<circ> cf_maps \<alpha> \<AA> \<BB>"
  then obtain \<FF> where x_def: "x = cf_map \<FF>" and \<FF>: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by clarsimp  
  then show "ntcf_arrow_id \<AA> \<BB> x \<in>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>"
    unfolding x_def
    by 
      (
        cs_concl 
          cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros cat_FUNCT_cs_intros
      )
qed



subsubsection\<open>
The conversion of a natural transformation arrow 
to a natural transformation is a bijection
\<close>

lemma bij_betw_ntcf_of_ntcf_arrow:
  "bij_betw
    (ntcf_of_ntcf_arrow \<AA> \<BB>)
    (elts (ntcf_arrows \<alpha> \<AA> \<BB>))
    (elts (ntcfs \<alpha> \<AA> \<BB>))"
proof(intro bij_betw_imageI inj_onI subset_antisym subsetI)
  fix \<MM> \<NN> assume prems: 
    "\<MM> \<in>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>"
    "\<NN> \<in>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>"
    "ntcf_of_ntcf_arrow \<AA> \<BB> \<MM> = ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>"
  from prems(1) obtain \<MM>' \<FF> \<GG> 
    where \<MM>_def: "\<MM> = ntcf_arrow \<MM>'" and \<MM>': "\<MM>' : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by auto
  from prems(2) obtain \<NN>' \<FF>' \<GG>' 
    where \<NN>_def: "\<NN> = ntcf_arrow \<NN>'" and \<NN>': "\<NN>' : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by auto
  from prems(3) have "\<MM>' = \<NN>'"
    unfolding 
      \<MM>_def 
      \<NN>_def  
      is_ntcf.ntcf_of_ntcf_arrow[OF \<MM>']
      is_ntcf.ntcf_of_ntcf_arrow[OF \<NN>']
    by simp
  then show "\<MM> = \<NN>" unfolding \<MM>_def \<NN>_def by auto
next
  fix \<MM> assume 
    "\<MM> \<in> ntcf_of_ntcf_arrow \<AA> \<BB> ` elts (ntcf_arrows \<alpha> \<AA> \<BB>)"
  then obtain \<MM>' where \<MM>': "\<MM>' \<in>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>"
    and \<MM>_def: "\<MM> = ntcf_of_ntcf_arrow \<AA> \<BB> \<MM>'"
    by auto  
  from \<MM>' obtain \<MM>'' \<FF> \<GG>
    where \<MM>'_def: "\<MM>' = ntcf_arrow \<MM>''" 
      and \<MM>'': "\<MM>'' : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by auto
  from \<MM>'' show "\<MM> \<in>\<^sub>\<circ> ntcfs \<alpha> \<AA> \<BB>"
    unfolding \<MM>_def \<MM>'_def is_ntcf.ntcf_of_ntcf_arrow[OF \<MM>''] by auto
next
  fix \<MM> assume "\<MM> \<in>\<^sub>\<circ> ntcfs \<alpha> \<AA> \<BB>"
  then obtain \<FF> \<GG> where \<MM>: "\<MM> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by clarsimp
  then have "\<MM> = ntcf_of_ntcf_arrow \<AA> \<BB> (ntcf_arrow \<MM>)" 
    by (cs_concl cs_simp: cat_FUNCT_cs_simps)
  moreover from \<MM> have "ntcf_arrow \<MM> \<in>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>"
    by (cs_concl cs_intro: cat_FUNCT_cs_intros)
  ultimately show "\<MM> \<in> ntcf_of_ntcf_arrow \<AA> \<BB> ` elts (ntcf_arrows \<alpha> \<AA> \<BB>)"
    by simp
qed

lemma bij_betw_ntcf_of_ntcf_arrow_Hom:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "bij_betw
    (ntcf_of_ntcf_arrow \<AA> \<BB>)
    (elts (Hom (cat_FUNCT \<alpha> \<AA> \<BB>) (cf_map \<FF>) (cf_map \<GG>)))
    (elts (these_ntcfs \<alpha> \<AA> \<BB> \<FF> \<GG>))"
proof-

  interpret \<FF>: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<AA> \<BB> \<GG>  by (rule assms(2))

  from assms have [cat_cs_simps]:
    "cf_of_cf_map \<AA> \<BB> (cf_map \<FF>) = \<FF>"
    "cf_of_cf_map \<AA> \<BB> (cf_map \<GG>) = \<GG>"
    by (cs_concl cs_simp: cat_FUNCT_cs_simps)+

  show ?thesis
  proof
    (
      rule bij_betw_subset[OF bij_betw_ntcf_of_ntcf_arrow];
      (intro subset_antisym subsetI)?;
      (unfold in_Hom_iff)?
    )
    fix \<NN> assume prems: "\<NN> : cf_map \<FF> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub> cf_map \<GG>"  
    note \<NN> = cat_FUNCT_is_arrD[OF prems, unfolded cat_cs_simps]
    from \<NN>(1) show "\<NN> \<in>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>"
      by (subst \<NN>(2)) (cs_concl cs_intro: cat_FUNCT_cs_intros)  
  next
    fix \<NN> assume 
      "\<NN> \<in> ntcf_of_ntcf_arrow \<AA> \<BB> `
        elts (Hom (cat_FUNCT \<alpha> \<AA> \<BB>) (cf_map \<FF>) (cf_map \<GG>))"
    then obtain \<NN>' 
      where \<NN>': "\<NN>' \<in>\<^sub>\<circ> Hom (cat_FUNCT \<alpha> \<AA> \<BB>) (cf_map \<FF>) (cf_map \<GG>)"
        and \<NN>_def: "\<NN> = ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>'"
      by auto
    note \<NN>' = cat_FUNCT_is_arrD[
        OF \<NN>'[unfolded cat_cs_simps], unfolded cat_cs_simps
        ]
    from \<NN>'(1) show "\<NN> \<in>\<^sub>\<circ> these_ntcfs \<alpha> \<AA> \<BB> \<FF> \<GG>" unfolding \<NN>_def by simp
  next
    fix \<NN> assume "\<NN> \<in>\<^sub>\<circ> these_ntcfs \<alpha> \<AA> \<BB> \<FF> \<GG>"
    then have \<NN>: "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by simp
    then have "\<NN> = ntcf_of_ntcf_arrow \<AA> \<BB> (ntcf_arrow \<NN>)"
      by (cs_concl cs_simp: cat_FUNCT_cs_simps)  
    moreover from \<NN> have
      "ntcf_arrow \<NN> \<in>\<^sub>\<circ> Hom (cat_FUNCT \<alpha> \<AA> \<BB>) (cf_map \<FF>) (cf_map \<GG>)"
      unfolding in_Hom_iff by (cs_concl cs_intro: cat_FUNCT_cs_intros)
    ultimately show 
      "\<NN> \<in> ntcf_of_ntcf_arrow \<AA> \<BB> `
        elts (Hom (cat_FUNCT \<alpha> \<AA> \<BB>) (cf_map \<FF>) (cf_map \<GG>))"
      by simp
  qed

qed


subsubsection\<open>\<open>FUNCT\<close> is a category\<close>

lemma (in \<Z>) tiny_category_cat_FUNCT[cat_FUNCT_cs_intros]: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "tiny_category \<beta> (cat_FUNCT \<alpha> \<AA> \<BB>)" (is \<open>tiny_category \<beta> ?FUNCT\<close>)
proof(intro tiny_categoryI)
  show "vfsequence ?FUNCT" unfolding cat_FUNCT_def by auto
  show "vcard ?FUNCT = 6\<^sub>\<nat>" 
    unfolding cat_FUNCT_def by (simp add: nat_omega_simps)
  from assms show "tiny_semicategory \<beta> (cat_smc ?FUNCT)"
    unfolding cat_smc_FUNCT 
    by (auto simp add: tiny_semicategory_smc_FUNCT)
  show CId_a: "?FUNCT\<lparr>CId\<rparr>\<lparr>\<FF>'\<rparr> : \<FF>' \<mapsto>\<^bsub>?FUNCT\<^esub> \<FF>'" if "\<FF>' \<in>\<^sub>\<circ> ?FUNCT\<lparr>Obj\<rparr>" for \<FF>'
  proof-
    from that obtain \<FF> where \<FF>'_def: "\<FF>' = cf_map \<FF>" and \<FF>: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      unfolding cat_FUNCT_components by clarsimp 
    show ?thesis
      using that \<FF>
      unfolding cat_FUNCT_components(1) \<FF>'_def
      by 
        (
          cs_concl 
            cs_simp: cat_FUNCT_cs_simps 
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
  qed
  show "?FUNCT\<lparr>CId\<rparr>\<lparr>\<GG>\<rparr> \<circ>\<^sub>A\<^bsub>?FUNCT\<^esub> \<NN> = \<NN>" if "\<NN> : \<FF> \<mapsto>\<^bsub>?FUNCT\<^esub> \<GG>" for \<NN> \<FF> \<GG>
  proof-
    from that obtain \<NN>' \<FF>' \<GG>' 
      where \<NN>': "\<NN>' : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
        and \<NN>_def[cat_FUNCT_cs_simps]: "\<NN> = ntcf_arrow \<NN>'"
        and \<FF>_def[cat_FUNCT_cs_simps]: "\<FF> = cf_map \<FF>'"
        and \<GG>_def[cat_FUNCT_cs_simps]: "\<GG> = cf_map \<GG>'"
      by auto
    from \<NN>' show "cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>\<GG>\<rparr> \<circ>\<^sub>A\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<NN> = \<NN>"
      by 
        (
          cs_concl 
            cs_simp: cat_FUNCT_cs_simps cat_cs_simps 
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
  qed 
  show "\<NN> \<circ>\<^sub>A\<^bsub>?FUNCT\<^esub> ?FUNCT\<lparr>CId\<rparr>\<lparr>\<GG>\<rparr> = \<NN>" if "\<NN> : \<GG> \<mapsto>\<^bsub>?FUNCT\<^esub> \<HH>" for \<NN> \<GG> \<HH>
  proof-
    note \<NN> = cat_FUNCT_is_arrD[OF that]
    from \<NN>(1) show "\<NN> \<circ>\<^sub>A\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub> cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>\<GG>\<rparr> = \<NN>"
      by (subst (1 2) \<NN>(2), subst \<NN>(3), remdups) 
        (
          cs_concl 
            cs_simp: cat_FUNCT_cs_simps cat_cs_simps 
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
  qed 
qed (simp_all add: assms cat_FUNCT_components)

lemmas (in \<Z>) [cat_FUNCT_cs_intros] = tiny_category_cat_FUNCT



subsubsection\<open>Isomorphism\<close>

lemma (in \<Z>) cat_FUNCT_is_arr_isomorphismI: 
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "ntcf_arrow \<NN> : cf_map \<FF> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub> cf_map \<GG>"
proof(intro is_arr_isomorphismI is_inverseI)
  interpret \<NN>: is_iso_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms)
  show is_arr_\<NN>: "ntcf_arrow \<NN> : cf_map \<FF> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub> cf_map \<GG>"
    by (simp add: assms cat_FUNCT_is_arrI is_iso_ntcf.axioms(1))
  interpret inv_\<NN>: is_iso_ntcf \<alpha> \<AA> \<BB> \<GG> \<FF> \<open>inv_ntcf \<NN>\<close> 
    using CZH_ECAT_NTCF.iso_ntcf_is_arr_isomorphism(1)[OF assms] by simp
  from assms show is_arr_inv_\<NN>: 
    "ntcf_arrow (inv_ntcf \<NN>) : cf_map \<GG> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub> cf_map \<FF>"
    by 
      (
        cs_concl cs_intro:
          ntcf_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  from assms show "ntcf_arrow \<NN> : cf_map \<FF> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub> cf_map \<GG>" 
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  from assms show 
    "ntcf_arrow (inv_ntcf \<NN>) \<circ>\<^sub>A\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub> ntcf_arrow \<NN> = 
      cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>cf_map \<FF>\<rparr>"
    "ntcf_arrow \<NN> \<circ>\<^sub>A\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub> ntcf_arrow (inv_ntcf \<NN>) = 
      cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>cf_map \<GG>\<rparr>"
    by 
      (
        cs_concl 
          cs_simp: iso_ntcf_is_arr_isomorphism(2,3) cat_FUNCT_cs_simps
          cs_intro: ntcf_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )+
qed

lemma (in \<Z>) cat_FUNCT_is_arr_isomorphismI': 
  assumes "\<NN>' = ntcf_arrow \<NN>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF>' = cf_map \<FF>"
    and "\<GG>' = cf_map \<GG>"
  shows "\<NN>' : \<FF>' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub> cf_map \<GG>"
  using assms(2) unfolding assms(1,3,4) by (rule cat_FUNCT_is_arr_isomorphismI)

lemmas [cat_FUNCT_cs_intros] = \<Z>.cat_FUNCT_is_arr_isomorphismI'[rotated 2]

lemma (in \<Z>) cat_FUNCT_is_arr_isomorphismD:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<GG>" (is \<open>\<NN> : \<FF> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>?FUNCT\<^esub> \<GG>\<close>)
  shows "ntcf_of_ntcf_arrow \<AA> \<BB> \<NN> :
    cf_of_cf_map \<AA> \<BB> \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o cf_of_cf_map \<AA> \<BB> \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN> = ntcf_arrow (ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>)"
    and "\<FF> = cf_map (cf_of_cf_map \<AA> \<BB> \<FF>)"
    and "\<GG> = cf_map (cf_of_cf_map \<AA> \<BB> \<GG>)"
proof-
  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have \<Z>\<beta>: "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    by (simp_all add: \<Z>_\<alpha>_\<alpha>\<omega> \<Z>.intro \<Z>_Limit_\<alpha>\<omega> \<Z>_\<omega>_\<alpha>\<omega> \<beta>_def)
  interpret FUNCT: tiny_category \<beta> ?FUNCT 
    by (rule tiny_category_cat_FUNCT[OF \<Z>\<beta> \<alpha>\<beta>, of \<AA> \<BB>])
  have inv_\<NN>: "\<NN>\<inverse>\<^sub>C\<^bsub>?FUNCT\<^esub> : \<GG> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>?FUNCT\<^esub> \<FF>"
    and inv_\<NN>_\<NN>: "\<NN>\<inverse>\<^sub>C\<^bsub>?FUNCT\<^esub> \<circ>\<^sub>A\<^bsub>?FUNCT\<^esub> \<NN> = ?FUNCT\<lparr>CId\<rparr>\<lparr>\<FF>\<rparr>"
    and \<NN>_inv_\<NN>: "\<NN> \<circ>\<^sub>A\<^bsub>?FUNCT\<^esub> \<NN>\<inverse>\<^sub>C\<^bsub>?FUNCT\<^esub> = ?FUNCT\<lparr>CId\<rparr>\<lparr>\<GG>\<rparr>"
    by 
      (
        intro 
          FUNCT.cat_the_inverse_is_arr_isomorphism[OF assms] 
          FUNCT.cat_the_inverse_Comp_CId[OF assms]
      )+
  from assms is_arr_isomorphismD inv_\<NN> 
  have \<NN>_is_arr: "\<NN> : \<FF> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<GG>" 
    and inv_\<NN>_is_arr: "\<NN>\<inverse>\<^sub>C\<^bsub>?FUNCT\<^esub> : \<GG> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<FF>"
    by auto
  note \<NN>_is_arr = cat_FUNCT_is_arrD[OF \<NN>_is_arr]
  note inv_\<NN>_is_arr = cat_FUNCT_is_arrD[OF inv_\<NN>_is_arr]
  let ?\<NN> = \<open>ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>\<close>
    and ?inv_\<NN> = \<open>ntcf_of_ntcf_arrow \<AA> \<BB> (\<NN>\<inverse>\<^sub>C\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub>)\<close>
  from inv_\<NN>_\<NN> \<NN>_is_arr(1) inv_\<NN>_is_arr(1) have inv_\<NN>_\<NN>:
    "?inv_\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<NN> = ntcf_id (cf_of_cf_map \<AA> \<BB> \<FF>)"
    by  
      (
        subst (asm) inv_\<NN>_is_arr(2), 
        use nothing in \<open>subst (asm) (2) \<NN>_is_arr(2), subst (asm) \<NN>_is_arr(3)\<close>
      )
      (
        cs_prems
          cs_simp: cat_FUNCT_cs_simps
          cs_intro: cat_FUNCT_cs_intros cat_cs_intros
      )
  from \<NN>_inv_\<NN> inv_\<NN>_is_arr(1) \<NN>_is_arr(1) have \<NN>_inv_\<NN>:
    "?\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?inv_\<NN> = ntcf_id (cf_of_cf_map \<AA> \<BB> \<GG>)"
    by  
      (
        subst (asm) inv_\<NN>_is_arr(2), 
        use nothing in \<open>subst (asm) \<NN>_is_arr(2), subst (asm) \<NN>_is_arr(4)\<close>
      )
      (
        cs_prems 
          cs_simp: cat_FUNCT_cs_simps 
          cs_intro: cat_FUNCT_cs_intros cat_cs_intros
      )
  show "ntcf_of_ntcf_arrow \<AA> \<BB> \<NN> :
    cf_of_cf_map \<AA> \<BB> \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o cf_of_cf_map \<AA> \<BB> \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by 
      (
        rule CZH_ECAT_NTCF.is_arr_isomorphism_is_iso_ntcf[
          OF \<NN>_is_arr(1) inv_\<NN>_is_arr(1) \<NN>_inv_\<NN> inv_\<NN>_\<NN> 
          ]
      )
  show "\<NN> = ntcf_arrow (ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>)"
    and "\<FF> = cf_map (cf_of_cf_map \<AA> \<BB> \<FF>)"
    and "\<GG> = cf_map (cf_of_cf_map \<AA> \<BB> \<GG>)"
    by (intro \<NN>_is_arr(2-4))+   
qed



subsection\<open>\<open>Funct\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition cat_Funct :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cat_Funct \<alpha> \<AA> \<BB> =
    [
      tm_cf_maps \<alpha> \<AA> \<BB>,
      tm_ntcf_arrows \<alpha> \<AA> \<BB>,
      (\<lambda>\<NN>\<in>\<^sub>\<circ>tm_ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTDom\<rparr>),
      (\<lambda>\<NN>\<in>\<^sub>\<circ>tm_ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTCod\<rparr>),
      (\<lambda>\<MM>\<NN>\<in>\<^sub>\<circ>composable_arrs (dg_Funct \<alpha> \<AA> \<BB>). \<MM>\<NN>\<lparr>0\<rparr> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>\<AA>,\<BB>\<^esub> \<MM>\<NN>\<lparr>1\<^sub>\<nat>\<rparr>),
      (\<lambda>\<FF>\<in>\<^sub>\<circ>tm_cf_maps \<alpha> \<AA> \<BB>. ntcf_arrow_id \<AA> \<BB> \<FF>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cat_Funct_components: 
  shows "cat_Funct \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr> = tm_cf_maps \<alpha> \<AA> \<BB>"
    and "cat_Funct \<alpha> \<AA> \<BB>\<lparr>Arr\<rparr> = tm_ntcf_arrows \<alpha> \<AA> \<BB>"
    and "cat_Funct \<alpha> \<AA> \<BB>\<lparr>Dom\<rparr> = (\<lambda>\<NN>\<in>\<^sub>\<circ>tm_ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTDom\<rparr>)"
    and "cat_Funct \<alpha> \<AA> \<BB>\<lparr>Cod\<rparr> = (\<lambda>\<NN>\<in>\<^sub>\<circ>tm_ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTCod\<rparr>)"
    and "cat_Funct \<alpha> \<AA> \<BB>\<lparr>Comp\<rparr> =
      (\<lambda>\<MM>\<NN>\<in>\<^sub>\<circ>composable_arrs (dg_Funct \<alpha> \<AA> \<BB>). \<MM>\<NN>\<lparr>0\<rparr> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>\<AA>,\<BB>\<^esub> \<MM>\<NN>\<lparr>1\<^sub>\<nat>\<rparr>)"
    and "cat_Funct \<alpha> \<AA> \<BB>\<lparr>CId\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>tm_cf_maps \<alpha> \<AA> \<BB>. ntcf_arrow_id \<AA> \<BB> \<FF>)"
  unfolding cat_Funct_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma cat_smc_Funct: "cat_smc (cat_Funct \<alpha> \<AA> \<BB>) = smc_Funct \<alpha> \<AA> \<BB>"
proof(rule vsv_eqI)
  show "vsv (cat_smc (cat_Funct \<alpha> \<AA> \<BB>))" unfolding cat_smc_def by auto
  show "vsv (smc_Funct \<alpha> \<AA> \<BB>)" unfolding smc_Funct_def by auto
  have dom_lhs: "\<D>\<^sub>\<circ> (cat_smc (cat_Funct \<alpha> \<AA> \<BB>)) = 5\<^sub>\<nat>" 
    unfolding cat_smc_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (smc_Funct \<alpha> \<AA> \<BB>) = 5\<^sub>\<nat>"
    unfolding smc_Funct_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (cat_smc (cat_Funct \<alpha> \<AA> \<BB>)) = \<D>\<^sub>\<circ> (smc_Funct \<alpha> \<AA> \<BB>)"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (cat_smc (cat_Funct \<alpha> \<AA> \<BB>)) \<Longrightarrow>
    cat_smc (cat_Funct \<alpha> \<AA> \<BB>)\<lparr>a\<rparr> = smc_Funct \<alpha> \<AA> \<BB>\<lparr>a\<rparr>"
    for a
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral,
        unfold cat_smc_def dg_field_simps cat_Funct_def smc_Funct_def
      )
      (auto simp: nat_omega_simps)
qed

context is_tm_ntcf
begin

lemmas_with [folded cat_smc_Funct, unfolded slicing_simps]: 
  cat_Funct_Dom_app = smc_Funct_Dom_app
  and cat_Funct_Cod_app = smc_Funct_Cod_app

end

lemmas [cat_FUNCT_cs_simps] = 
  is_tm_ntcf.cat_Funct_Dom_app
  is_tm_ntcf.cat_Funct_Cod_app

lemmas_with [folded cat_smc_Funct, unfolded slicing_simps]: 
  cat_Funct_Dom_vsv[cat_FUNCT_cs_intros] = smc_Funct_Dom_vsv
  and cat_Funct_Dom_vdomain[cat_FUNCT_cs_simps] = smc_Funct_Dom_vdomain
  and cat_Funct_Cod_vsv[cat_FUNCT_cs_intros] = smc_Funct_Cod_vsv
  and cat_Funct_Cod_vdomain[cat_FUNCT_cs_simps] = smc_Funct_Cod_vdomain
  and cat_Funct_Dom_vrange = smc_Funct_Dom_vrange
  and cat_Funct_Cod_vrange = smc_Funct_Cod_vrange
  and cat_Funct_is_arrI = smc_Funct_is_arrI
  and cat_Funct_is_arrI'[cat_FUNCT_cs_intros] = smc_Funct_is_arrI'
  and cat_Funct_is_arrD = smc_Funct_is_arrD
  and cat_Funct_is_arrE[elim] = smc_Funct_is_arrE

lemmas_with [folded cat_smc_Funct, unfolded slicing_simps]: 
  cat_Funct_Comp_app[cat_FUNCT_cs_simps] = smc_Funct_Comp_app


subsubsection\<open>Identity\<close>

mk_VLambda cat_Funct_components(6)
  |vsv cat_Funct_CId_vsv[intro]|
  |vdomain cat_Funct_CId_vdomain[cat_FUNCT_cs_simps]|
  |app cat_Funct_CId_app[cat_FUNCT_cs_simps]|

lemma smc_Funct_CId_vrange: "\<R>\<^sub>\<circ> (cat_Funct \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>) \<subseteq>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>"
  unfolding cat_Funct_components
proof(rule vrange_VLambda_vsubset)
  fix \<FF>' assume "\<FF>' \<in>\<^sub>\<circ> tm_cf_maps \<alpha> \<AA> \<BB>"
  then obtain \<FF> where \<FF>'_def: "\<FF>' = cf_map \<FF>" and \<FF>: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    by clarsimp  
  then show "ntcf_arrow_id \<AA> \<BB> \<FF>' \<in>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>"
    by 
      (
        cs_concl
          cs_simp: cat_FUNCT_cs_simps \<FF>'_def
          cs_intro: cat_FUNCT_cs_intros cat_small_cs_intros
      )
qed


subsubsection\<open>\<open>Funct\<close> is a category\<close>

lemma category_cat_Funct: 
  assumes "tiny_category \<alpha> \<AA>" and "category \<alpha> \<BB>"
  shows "category \<alpha> (cat_Funct \<alpha> \<AA> \<BB>)" (is \<open>category \<alpha> ?Funct\<close>)
proof-
  interpret tiny_category \<alpha> \<AA> by (rule assms(1))
  show ?thesis
  proof(intro categoryI)
    show "vfsequence ?Funct" by (simp add: cat_Funct_def)
    show "vcard ?Funct = 6\<^sub>\<nat>" 
      unfolding cat_Funct_def by (simp add: nat_omega_simps)
    from assms show "semicategory \<alpha> (cat_smc (cat_Funct \<alpha> \<AA> \<BB>))"
      unfolding cat_smc_Funct by (rule semicategory_smc_Funct)
    show "\<D>\<^sub>\<circ> (cat_Funct \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>) = cat_Funct \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_Funct_components cat_FUNCT_cs_simps)
    show "cat_Funct \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<rparr> : \<FF> \<mapsto>\<^bsub>cat_Funct \<alpha> \<AA> \<BB>\<^esub> \<FF>"
      if "\<FF> \<in>\<^sub>\<circ> cat_Funct \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>" for \<FF>
    proof-
      from that have "\<FF> \<in>\<^sub>\<circ> tm_cf_maps \<alpha> \<AA> \<BB>"
        unfolding cat_Funct_components by simp
      then obtain \<FF>' 
        where \<FF>_def: "\<FF> = cf_map \<FF>'" and \<FF>': "\<FF>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" 
        by auto
      from assms \<FF>' show "cat_Funct \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<rparr> : \<FF> \<mapsto>\<^bsub>cat_Funct \<alpha> \<AA> \<BB>\<^esub> \<FF>"
        by 
          (
            cs_concl 
              cs_simp: cat_FUNCT_cs_simps \<FF>_def
              cs_intro: cat_FUNCT_cs_intros cat_small_cs_intros
          )
    qed
    show "cat_Funct \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>\<GG>\<rparr> \<circ>\<^sub>A\<^bsub>cat_Funct \<alpha> \<AA> \<BB>\<^esub> \<NN> = \<NN>"
      if "\<NN> : \<FF> \<mapsto>\<^bsub>cat_Funct \<alpha> \<AA> \<BB>\<^esub> \<GG>" for \<FF> \<GG> \<NN>
    proof-
      note \<NN> = cat_Funct_is_arrD[OF that]
      from assms \<NN>(1) show
        "cat_Funct \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>\<GG>\<rparr> \<circ>\<^sub>A\<^bsub>cat_Funct \<alpha> \<AA> \<BB>\<^esub> \<NN> = \<NN>"
        by (subst (1 2) \<NN>(2), use nothing in \<open>subst \<NN>(4)\<close>)
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
              cs_intro: cat_FUNCT_cs_intros cat_small_cs_intros
          )
    qed
    show "\<NN> \<circ>\<^sub>A\<^bsub>cat_Funct \<alpha> \<AA> \<BB>\<^esub> cat_Funct \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>\<GG>\<rparr> = \<NN>"
      if "\<NN> : \<GG> \<mapsto>\<^bsub>cat_Funct \<alpha> \<AA> \<BB>\<^esub> \<HH>" for \<GG> \<HH> \<NN>
    proof-
      note \<NN> = cat_Funct_is_arrD[OF that]
      from assms \<NN>(1) show 
        "\<NN> \<circ>\<^sub>A\<^bsub>cat_Funct \<alpha> \<AA> \<BB>\<^esub> cat_Funct \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>\<GG>\<rparr> = \<NN>"
        by (subst (1 2) \<NN>(2), use nothing in \<open>subst \<NN>(3)\<close>)
          (
            cs_concl
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
              cs_intro: cat_FUNCT_cs_intros cat_small_cs_intros
          )
    qed
  qed auto
qed

lemma category_cat_Funct'[cat_FUNCT_cs_intros]:
  assumes "tiny_category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<beta> = \<alpha>"
  shows "category \<alpha> (cat_Funct \<beta> \<AA> \<BB>)"
  using assms(1,2) unfolding assms(3) by (rule category_cat_Funct)


subsubsection\<open>\<open>Funct\<close> is a subcategory of \<open>FUNCT\<close>\<close>

lemma subcategory_cat_Funct_cat_FUNCT:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" and "tiny_category \<alpha> \<AA>" and "category \<alpha> \<BB>"
  shows "cat_Funct \<alpha> \<AA> \<BB> \<subseteq>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<AA> \<BB>"
proof
  (
    intro subcategoryI, 
    unfold cat_smc_FUNCT cat_smc_Funct cat_Funct_components(1)
  )
  interpret category \<alpha> \<BB> by (rule assms(4))
  interpret \<AA>\<BB>: category \<alpha> \<open>cat_Funct \<alpha> \<AA> \<BB>\<close>
    by (rule category_cat_Funct[OF assms(3,4)])
  show "category \<beta> (cat_Funct \<alpha> \<AA> \<BB>)"
    by (rule category.cat_category_if_ge_Limit[OF _ assms(1,2)]) 
      (auto intro: cat_cs_intros)
  from assms show "category \<beta> (cat_FUNCT \<alpha> \<AA> \<BB>)"
    by (cs_concl cs_intro: tiny_category_cat_FUNCT cat_small_cs_intros)
  show "smc_Funct \<alpha> \<AA> \<BB> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<beta>\<^esub> smc_FUNCT \<alpha> \<AA> \<BB>"
    by (rule subsemicategory_smc_Funct_smc_FUNCT[OF assms])
  show "cat_Funct \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<rparr> = cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<rparr>" 
    if \<open>\<FF> \<in>\<^sub>\<circ> tm_cf_maps \<alpha> \<AA> \<BB>\<close> for \<FF>
  proof-
    from that obtain \<FF>' where \<FF>_def: "\<FF> = cf_map \<FF>'" 
      and \<FF>': "\<FF>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
      by auto
    from that show ?thesis
      by 
        (
          cs_concl 
            cs_simp: cat_FUNCT_cs_simps 
            cs_intro: cat_FUNCT_cs_intros tm_cf_maps_in_cf_maps
        )
  qed
qed


subsubsection\<open>Isomorphism\<close>

lemma (in is_tm_iso_ntcf) cat_Funct_is_arr_isomorphismI: 
  assumes "category \<alpha> \<BB>"
  shows "ntcf_arrow \<NN> : cf_map \<FF> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Funct \<alpha> \<AA> \<BB>\<^esub> cf_map \<GG>"
proof(intro is_arr_isomorphismI is_inverseI)
  from is_tm_iso_ntcf_axioms show 
    "ntcf_arrow \<NN> : cf_map \<FF> \<mapsto>\<^bsub>cat_Funct \<alpha> \<AA> \<BB>\<^esub> cf_map \<GG>"
    by (cs_concl cs_intro: ntcf_cs_intros cat_FUNCT_cs_intros)
  interpret inv_\<NN>: is_tm_iso_ntcf \<alpha> \<AA> \<BB> \<GG> \<FF> \<open>inv_ntcf \<NN>\<close> 
    by (rule iso_tm_ntcf_is_arr_isomorphism(1)[OF assms is_tm_iso_ntcf_axioms]) 
  from inv_\<NN>.is_tm_iso_ntcf_axioms show 
    "ntcf_arrow (inv_ntcf \<NN>) : cf_map \<GG> \<mapsto>\<^bsub>cat_Funct \<alpha> \<AA> \<BB>\<^esub> cf_map \<FF>"
    by (cs_concl cs_intro: ntcf_cs_intros cat_FUNCT_cs_intros)
  from is_tm_iso_ntcf_axioms show 
    "ntcf_arrow \<NN> : cf_map \<FF> \<mapsto>\<^bsub>cat_Funct \<alpha> \<AA> \<BB>\<^esub> cf_map \<GG>" 
    by (cs_concl cs_intro: ntcf_cs_intros cat_FUNCT_cs_intros)
  from assms is_tm_iso_ntcf_axioms show 
    "ntcf_arrow (inv_ntcf \<NN>) \<circ>\<^sub>A\<^bsub>cat_Funct \<alpha> \<AA> \<BB>\<^esub> ntcf_arrow \<NN> =
      cat_Funct \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>cf_map \<FF>\<rparr>"
    "ntcf_arrow \<NN> \<circ>\<^sub>A\<^bsub>cat_Funct \<alpha> \<AA> \<BB>\<^esub> ntcf_arrow (inv_ntcf \<NN>) =
      cat_Funct \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>cf_map \<GG>\<rparr>"
    by
      (
        cs_concl
          cs_simp: iso_tm_ntcf_is_arr_isomorphism(2,3) cat_FUNCT_cs_simps
          cs_intro: ntcf_cs_intros cat_FUNCT_cs_intros cat_small_cs_intros
      )+
qed

lemma (in is_tm_iso_ntcf) cat_Funct_is_arr_isomorphismI': 
  assumes "category \<alpha> \<BB>" 
    and "\<NN>' = ntcf_arrow \<NN>" 
    and "\<FF>' = cf_map \<FF>"
    and "\<GG>' = cf_map \<GG>"
  shows "\<NN>' : \<FF>' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Funct \<alpha> \<AA> \<BB>\<^esub> cf_map \<GG>"
  using assms(1) unfolding assms(2-4) by (rule cat_Funct_is_arr_isomorphismI)

lemmas [cat_FUNCT_cs_intros] = 
  is_tm_iso_ntcf.cat_Funct_is_arr_isomorphismI'[rotated 2]

lemma (in \<Z>) cat_Funct_is_arr_isomorphismD:
  assumes "tiny_category \<alpha> \<AA>" 
    and "category \<alpha> \<BB>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Funct \<alpha> \<AA> \<BB>\<^esub> \<GG>" (is \<open>\<NN> : \<FF> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>?Funct\<^esub> \<GG>\<close>)
  shows "ntcf_of_ntcf_arrow \<AA> \<BB> \<NN> :
    cf_of_cf_map \<AA> \<BB> \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>i\<^sub>s\<^sub>o cf_of_cf_map \<AA> \<BB> \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN> = ntcf_arrow (ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>)"
    and "\<FF> = cf_map (cf_of_cf_map \<AA> \<BB> \<FF>)"
    and "\<GG> = cf_map (cf_of_cf_map \<AA> \<BB> \<GG>)"
proof-
  interpret Funct: category \<alpha> ?Funct
    by (rule category_cat_Funct[OF assms(1,2)])
  have inv_\<NN>: "\<NN>\<inverse>\<^sub>C\<^bsub>?Funct\<^esub> : \<GG> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>?Funct\<^esub> \<FF>"
    and inv_\<NN>_\<NN>: "\<NN>\<inverse>\<^sub>C\<^bsub>?Funct\<^esub> \<circ>\<^sub>A\<^bsub>?Funct\<^esub> \<NN> = ?Funct\<lparr>CId\<rparr>\<lparr>\<FF>\<rparr>"
    and \<NN>_inv_\<NN>: "\<NN> \<circ>\<^sub>A\<^bsub>?Funct\<^esub> \<NN>\<inverse>\<^sub>C\<^bsub>?Funct\<^esub> = ?Funct\<lparr>CId\<rparr>\<lparr>\<GG>\<rparr>"
    by 
      (
        intro 
          Funct.cat_the_inverse_is_arr_isomorphism[OF assms(3)] 
          Funct.cat_the_inverse_Comp_CId[OF assms(3)]
      )+
  from assms is_arr_isomorphismD inv_\<NN> 
  have \<NN>_is_arr: "\<NN> : \<FF> \<mapsto>\<^bsub>cat_Funct \<alpha> \<AA> \<BB>\<^esub> \<GG>" 
    and inv_\<NN>_is_arr: "\<NN>\<inverse>\<^sub>C\<^bsub>?Funct\<^esub> : \<GG> \<mapsto>\<^bsub>cat_Funct \<alpha> \<AA> \<BB>\<^esub> \<FF>"
    by auto
  note \<NN>_is_arr = cat_Funct_is_arrD[OF \<NN>_is_arr]
  note inv_\<NN>_is_arr = cat_Funct_is_arrD[OF inv_\<NN>_is_arr]
  let ?\<NN> = \<open>ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>\<close>
    and ?inv_\<NN> = \<open>ntcf_of_ntcf_arrow \<AA> \<BB> (\<NN>\<inverse>\<^sub>C\<^bsub>cat_Funct \<alpha> \<AA> \<BB>\<^esub>)\<close>
  from inv_\<NN>_\<NN> \<NN>_is_arr(1) inv_\<NN>_is_arr(1) have inv_\<NN>_\<NN>:
    "?inv_\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<NN> = ntcf_id (cf_of_cf_map \<AA> \<BB> \<FF>)"
    by  
      (
        subst (asm) inv_\<NN>_is_arr(2), 
        use nothing in \<open>subst (asm) (2) \<NN>_is_arr(2), subst (asm) \<NN>_is_arr(3)\<close>
      )
      (
        cs_prems 
          cs_simp: cat_FUNCT_cs_simps 
          cs_intro: cat_FUNCT_cs_intros cat_small_cs_intros
      )
  from \<NN>_inv_\<NN> inv_\<NN>_is_arr(1) \<NN>_is_arr(1) have \<NN>_inv_\<NN>:
    "?\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?inv_\<NN> = ntcf_id (cf_of_cf_map \<AA> \<BB> \<GG>)"
    by
      (
        subst (asm) inv_\<NN>_is_arr(2), 
        use nothing in \<open>subst (asm) \<NN>_is_arr(2), subst (asm) \<NN>_is_arr(4)\<close>
      )
      (
        cs_prems
          cs_simp: cat_FUNCT_cs_simps
          cs_intro: cat_FUNCT_cs_intros cat_small_cs_intros
      )
  show "ntcf_of_ntcf_arrow \<AA> \<BB> \<NN> : 
    cf_of_cf_map \<AA> \<BB> \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>i\<^sub>s\<^sub>o cf_of_cf_map \<AA> \<BB> \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    by 
      (
        rule is_arr_isomorphism_is_tm_iso_ntcf[
          OF \<NN>_is_arr(1) inv_\<NN>_is_arr(1) \<NN>_inv_\<NN> inv_\<NN>_\<NN> 
          ]
      )
  show "\<NN> = ntcf_arrow (ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>)"
    and "\<FF> = cf_map (cf_of_cf_map \<AA> \<BB> \<FF>)"
    and "\<GG> = cf_map (cf_of_cf_map \<AA> \<BB> \<GG>)"
    by (intro \<NN>_is_arr(2-4))+   
qed



subsection\<open>Diagonal functor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter III-3 in \cite{mac_lane_categories_2010}.\<close>

definition cf_diagonal :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (\<open>\<Delta>\<^sub>C\<close>) 
  where "\<Delta>\<^sub>C \<alpha> \<JJ> \<CC> = 
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. cf_map (cf_const \<JJ> \<CC> a)),
      (\<lambda>f\<in>\<^sub>\<circ>\<CC>\<lparr>Arr\<rparr>. ntcf_arrow (ntcf_const \<JJ> \<CC> f)), 
      \<CC>,
      cat_Funct \<alpha> \<JJ> \<CC>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_diagonal_components:
  shows "\<Delta>\<^sub>C \<alpha> \<JJ> \<CC>\<lparr>ObjMap\<rparr> = (\<lambda>a\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. cf_map (cf_const \<JJ> \<CC> a))"
    and "\<Delta>\<^sub>C \<alpha> \<JJ> \<CC>\<lparr>ArrMap\<rparr> = (\<lambda>f\<in>\<^sub>\<circ>\<CC>\<lparr>Arr\<rparr>. ntcf_arrow (ntcf_const \<JJ> \<CC> f))"
    and "\<Delta>\<^sub>C \<alpha> \<JJ> \<CC>\<lparr>HomDom\<rparr> = \<CC>"
    and "\<Delta>\<^sub>C \<alpha> \<JJ> \<CC>\<lparr>HomCod\<rparr> = cat_Funct \<alpha> \<JJ> \<CC>"
  unfolding cf_diagonal_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

mk_VLambda cf_diagonal_components(1)
  |vsv cf_diagonal_ObjMap_vsv[cat_cs_intros]|
  |vdomain cf_diagonal_ObjMap_vdomain[cat_cs_simps]|
  |app cf_diagonal_ObjMap_app[cat_cs_simps]|

lemma cf_diagonal_ObjMap_vrange:
  assumes "tiny_category \<alpha> \<JJ>" and "category \<alpha> \<CC>"
  shows "\<R>\<^sub>\<circ> (\<Delta>\<^sub>C \<alpha> \<JJ> \<CC>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Funct \<alpha> \<JJ> \<CC>\<lparr>Obj\<rparr>"
  unfolding cf_diagonal_components 
proof(rule vrange_VLambda_vsubset)
  fix x assume "x \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
  with assms category_cat_Funct[OF assms] show 
    "cf_map (cf_const \<JJ> \<CC> x) \<in>\<^sub>\<circ> cat_Funct \<alpha> \<JJ> \<CC>\<lparr>Obj\<rparr>"
    unfolding cat_Funct_components(1)
    by (cs_concl cs_intro: cat_small_cs_intros cat_FUNCT_cs_intros)
qed


subsubsection\<open>Arrow map\<close>

mk_VLambda cf_diagonal_components(2)
  |vsv cf_diagonal_ArrMap_vsv[cat_cs_intros]|
  |vdomain cf_diagonal_ArrMap_vdomain[cat_cs_simps]|
  |app cf_diagonal_ArrMap_app[cat_cs_simps]|


subsubsection\<open>Diagonal functor is a functor\<close>

lemma cf_diagonal_is_functor[cat_cs_intros]:
  assumes "tiny_category \<alpha> \<JJ>" and "category \<alpha> \<CC>"
  shows "\<Delta>\<^sub>C \<alpha> \<JJ> \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Funct \<alpha> \<JJ> \<CC>" (is \<open>?\<Delta> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> ?Funct\<close>)
proof-

  interpret \<JJ>: tiny_category \<alpha> \<JJ> by (rule assms(1))
  interpret \<CC>: category \<alpha> \<CC> by (rule assms(2))

  show ?thesis
  proof(intro is_functorI')
    show "vfsequence ?\<Delta>"
      unfolding cf_diagonal_def by (simp add: nat_omega_simps)
    from assms(2) show "category \<alpha> \<CC>" 
      by (cs_concl cs_intro: cat_cs_intros)
    from assms show "category \<alpha> ?Funct" 
      by (cs_concl cs_intro: cat_cs_intros category_cat_Funct)
    show "vcard ?\<Delta> = 4\<^sub>\<nat>"
      unfolding cf_diagonal_def by (simp add: nat_omega_simps)
    show "vsv (?\<Delta>\<lparr>ObjMap\<rparr>)" unfolding cf_diagonal_components by simp
    from assms show "\<R>\<^sub>\<circ> (?\<Delta>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> ?Funct\<lparr>Obj\<rparr>"
      by (rule cf_diagonal_ObjMap_vrange)
    show "?\<Delta>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : ?\<Delta>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>?Funct\<^esub> ?\<Delta>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      if "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" for f a b
      using that
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps 
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros cat_small_cs_intros
        )
    show "?\<Delta>\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<rparr> = ?\<Delta>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>?Funct\<^esub> ?\<Delta>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      if "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" for g b c f a
      using that \<JJ>.category_axioms \<CC>.category_axioms
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    fix c assume "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    with \<JJ>.category_axioms \<CC>.category_axioms show 
      "?\<Delta>\<lparr>ArrMap\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = ?Funct\<lparr>CId\<rparr>\<lparr>?\<Delta>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
      by 
        (
          cs_concl
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
  qed (auto simp: cf_diagonal_components cat_smc_FUNCT)

qed

lemma cf_diagonal_is_functor'[cat_cs_intros]:
  assumes "tiny_category \<alpha> \<JJ>" 
    and "category \<alpha> \<CC>"
    and "\<alpha>' = \<alpha>"
    and "\<AA> = \<CC>"
    and "\<BB> = cat_Funct \<alpha> \<JJ> \<CC>"
  shows "\<Delta>\<^sub>C \<alpha> \<JJ> \<CC> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<BB>"
  using assms(1-2) unfolding assms(3-5) by (rule cf_diagonal_is_functor)



subsection\<open>Functor raised to the power of a category\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
Most of the definitions and the results presented in this 
and the remaining subsections
can be found in \cite{mac_lane_categories_2010} and 
\cite{riehl_category_2016} (e.g., see Chapter X-3 
in \cite{mac_lane_categories_2010}).
\<close>

definition exp_cf_cat :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "exp_cf_cat \<alpha> \<KK> \<AA> =
    [
      (
        \<lambda>\<SS>\<in>\<^sub>\<circ>cat_FUNCT \<alpha> \<AA> (\<KK>\<lparr>HomDom\<rparr>)\<lparr>Obj\<rparr>.
          cf_map (\<KK> \<circ>\<^sub>C\<^sub>F cf_of_cf_map \<AA> (\<KK>\<lparr>HomDom\<rparr>) \<SS>)
      ),
      (
        \<lambda>\<sigma>\<in>\<^sub>\<circ>cat_FUNCT \<alpha> \<AA> (\<KK>\<lparr>HomDom\<rparr>)\<lparr>Arr\<rparr>.
          ntcf_arrow (\<KK> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_of_ntcf_arrow \<AA> (\<KK>\<lparr>HomDom\<rparr>) \<sigma>)
      ),
      cat_FUNCT \<alpha> \<AA> (\<KK>\<lparr>HomDom\<rparr>),
      cat_FUNCT \<alpha> \<AA> (\<KK>\<lparr>HomCod\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma exp_cf_cat_components:
  shows "exp_cf_cat \<alpha> \<KK> \<AA>\<lparr>ObjMap\<rparr> = 
    (
      \<lambda>\<SS>\<in>\<^sub>\<circ>cat_FUNCT \<alpha> \<AA> (\<KK>\<lparr>HomDom\<rparr>)\<lparr>Obj\<rparr>.
        cf_map (\<KK> \<circ>\<^sub>C\<^sub>F cf_of_cf_map \<AA> (\<KK>\<lparr>HomDom\<rparr>) \<SS>)
    )"
    and 
    "exp_cf_cat \<alpha> \<KK> \<AA>\<lparr>ArrMap\<rparr> =
      (
        \<lambda>\<sigma>\<in>\<^sub>\<circ>cat_FUNCT \<alpha> \<AA> (\<KK>\<lparr>HomDom\<rparr>)\<lparr>Arr\<rparr>.
          ntcf_arrow  (\<KK> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F (ntcf_of_ntcf_arrow \<AA> (\<KK>\<lparr>HomDom\<rparr>) \<sigma>))
      )"
    and "exp_cf_cat \<alpha> \<KK> \<AA>\<lparr>HomDom\<rparr> = cat_FUNCT \<alpha> \<AA> (\<KK>\<lparr>HomDom\<rparr>)"
    and "exp_cf_cat \<alpha> \<KK> \<AA>\<lparr>HomCod\<rparr> = cat_FUNCT \<alpha> \<AA> (\<KK>\<lparr>HomCod\<rparr>)"
  unfolding exp_cf_cat_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

mk_VLambda exp_cf_cat_components(1)
  |vsv exp_cf_cat_components_ObjMap_vsv[cat_FUNCT_cs_intros]|

context 
  fixes \<alpha> \<KK> \<BB> \<CC>
  assumes \<KK>: "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
begin

interpretation \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule \<KK>)

mk_VLambda exp_cf_cat_components(1)[where \<KK>=\<KK> and \<alpha>=\<alpha>, unfolded cat_cs_simps]
  |vdomain exp_cf_cat_components_ObjMap_vdomain[cat_FUNCT_cs_simps]|
  |app exp_cf_cat_components_ObjMap_app[cat_FUNCT_cs_simps]|

end


subsubsection\<open>Arrow map\<close>

mk_VLambda exp_cf_cat_components(2)
  |vsv exp_cf_cat_components_ArrMap_vsv[cat_FUNCT_cs_intros]|

context 
  fixes \<alpha> \<KK> \<BB> \<CC>
  assumes \<KK>: "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
begin

interpretation \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule \<KK>)

mk_VLambda exp_cf_cat_components(2)[where \<KK>=\<KK> and \<alpha>=\<alpha>, unfolded cat_cs_simps]
  |vdomain exp_cf_cat_components_ArrMap_vdomain[cat_FUNCT_cs_simps]|
  |app exp_cf_cat_components_ArrMap_app[cat_FUNCT_cs_simps]|

end


subsubsection\<open>Domain and codomain\<close>

context 
  fixes \<alpha> \<KK> \<BB> \<CC>
  assumes \<KK>: "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
begin

interpretation \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule \<KK>)

lemmas exp_cf_cat_HomDom[cat_FUNCT_cs_simps] = 
    exp_cf_cat_components(3)[where \<KK>=\<KK> and \<alpha>=\<alpha>, unfolded cat_cs_simps]
  and exp_cf_cat_HomCod[cat_FUNCT_cs_simps] = 
    exp_cf_cat_components(4)[where \<KK>=\<KK> and \<alpha>=\<alpha>, unfolded cat_cs_simps]

end


subsubsection\<open>Functor raised to the power of a category is a functor\<close>

lemma exp_cf_cat_is_tiny_functor: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" and "category \<alpha> \<AA>" and "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "exp_cf_cat \<alpha> \<KK> \<AA> : cat_FUNCT \<alpha> \<AA> \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<AA> \<CC>"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<AA>: category \<alpha> \<AA> by (rule assms(3))
  interpret \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(4))
  from assms(2-4) interpret \<AA>\<BB>: tiny_category \<beta> \<open>cat_FUNCT \<alpha> \<AA> \<BB>\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  from assms(2-4) interpret \<AA>\<CC>: tiny_category \<beta> \<open>cat_FUNCT \<alpha> \<AA> \<CC>\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  show ?thesis
  proof(intro is_tiny_functorI' is_functorI')
    show "vfsequence (exp_cf_cat \<alpha> \<KK> \<AA>)" unfolding exp_cf_cat_def by simp
    show "vcard (exp_cf_cat \<alpha> \<KK> \<AA>) = 4\<^sub>\<nat>"
      unfolding exp_cf_cat_def by (simp add: nat_omega_simps)
    show "\<R>\<^sub>\<circ> (exp_cf_cat \<alpha> \<KK> \<AA>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_FUNCT \<alpha> \<AA> \<CC>\<lparr>Obj\<rparr>"
    proof
      (
        unfold cat_FUNCT_components exp_cf_cat_components, 
        intro vrange_VLambda_vsubset, 
        unfold cat_cs_simps
      )
      fix \<FF> assume "\<FF> \<in>\<^sub>\<circ> cf_maps \<alpha> \<AA> \<BB>"
      then obtain \<FF>' where \<FF>_def: "\<FF> = cf_map \<FF>'" and \<FF>': "\<FF>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
        by auto
      from assms(2-4) \<FF>' show 
        "cf_map (\<KK> \<circ>\<^sub>C\<^sub>F cf_of_cf_map \<AA> \<BB> \<FF>) \<in>\<^sub>\<circ> cf_maps \<alpha> \<AA> \<CC>"
        by (cs_concl cs_simp: \<FF>_def cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
    qed
    show "exp_cf_cat \<alpha> \<KK> \<AA>\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<rparr> :
      exp_cf_cat \<alpha> \<KK> \<AA>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<rparr> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<AA> \<CC>\<^esub>
      exp_cf_cat \<alpha> \<KK> \<AA>\<lparr>ObjMap\<rparr>\<lparr>\<GG>\<rparr>"
      if "\<NN> : \<FF> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<GG>" for \<FF> \<GG> \<NN>
    proof-
      note \<NN> = cat_FUNCT_is_arrD[OF that]
      from \<NN>(1,3,4) assms(2-4) show ?thesis
      by (subst \<NN>(2), use nothing in \<open>subst \<NN>(3), subst \<NN>(4)\<close>) 
        (
          cs_concl 
            cs_simp: cat_FUNCT_cs_simps 
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
    qed
    show 
      "exp_cf_cat \<alpha> \<KK> \<AA>\<lparr>ArrMap\<rparr>\<lparr>\<MM> \<circ>\<^sub>A\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<NN>\<rparr> =
        exp_cf_cat \<alpha> \<KK> \<AA>\<lparr>ArrMap\<rparr>\<lparr>\<MM>\<rparr> \<circ>\<^sub>A\<^bsub>cat_FUNCT \<alpha> \<AA> \<CC>\<^esub>
        exp_cf_cat \<alpha> \<KK> \<AA>\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<rparr>"
      if "\<MM> : \<GG> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<HH>" and "\<NN> : \<FF> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<GG>"
      for \<GG> \<HH> \<MM> \<FF> \<NN>
    proof-
      note \<MM> = cat_FUNCT_is_arrD[OF that(1)]
        and \<NN> = cat_FUNCT_is_arrD[OF that(2)]  
      from \<MM>(1,3,4) \<NN>(1,3,4) assms(2-4) show ?thesis  
        by (subst (1 2) \<MM>(2), use nothing in \<open>subst (1 2) \<NN>(2)\<close>)
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps cf_ntcf_comp_ntcf_vcomp 
              cs_intro: cat_cs_intros cat_FUNCT_cs_intros
          )
    qed
    show 
      "exp_cf_cat \<alpha> \<KK> \<AA>\<lparr>ArrMap\<rparr>\<lparr>cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<rparr>\<rparr> =
        cat_FUNCT \<alpha> \<AA> \<CC>\<lparr>CId\<rparr>\<lparr>exp_cf_cat \<alpha> \<KK> \<AA>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<rparr>\<rparr>"
      if "\<FF> \<in>\<^sub>\<circ> cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>" for \<FF>
    proof-
      from that[unfolded cat_FUNCT_components] obtain \<GG> 
        where \<FF>_def: "\<FF> = cf_map \<GG>" and \<GG>: "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
        by auto
      from \<GG> show
        "exp_cf_cat \<alpha> \<KK> \<AA>\<lparr>ArrMap\<rparr>\<lparr>cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<rparr>\<rparr> =
          cat_FUNCT \<alpha> \<AA> \<CC>\<lparr>CId\<rparr>\<lparr>exp_cf_cat \<alpha> \<KK> \<AA>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<rparr>\<rparr>" 
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps \<FF>_def
              cs_intro: cat_cs_intros cat_FUNCT_cs_intros
          )
    qed
  qed 
    (
      use assms(1,2) in
        \<open>
          cs_concl
            cs_simp: cat_FUNCT_cs_simps 
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        \<close>
    )+
qed

lemma exp_cf_cat_is_tiny_functor'[cat_FUNCT_cs_intros]:
  assumes "\<Z> \<beta>" 
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    and "category \<alpha> \<AA>" 
    and "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<AA>' = cat_FUNCT \<alpha> \<AA> \<BB>"
    and "\<BB>' = cat_FUNCT \<alpha> \<AA> \<CC>"
  shows "exp_cf_cat \<alpha> \<KK> \<AA> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> \<BB>'"
  using assms(1-4) unfolding assms(5,6) by (rule exp_cf_cat_is_tiny_functor)


subsubsection\<open>Further properties\<close>

lemma exp_cf_cat_cf_comp:
  assumes "category \<alpha> \<DD>" and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "exp_cf_cat \<alpha> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) \<DD> = exp_cf_cat \<alpha> \<GG> \<DD> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<DD>"
proof(rule cf_eqI)

  interpret \<DD>: category \<alpha> \<DD> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(2))
  interpret \<FF>: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(3))

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    by (simp_all add: \<beta>_def \<DD>.\<Z>_Limit_\<alpha>\<omega> \<DD>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<DD>.\<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 

  from \<alpha>\<beta> show 
    "exp_cf_cat \<alpha> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) \<DD> : cat_FUNCT \<alpha> \<DD> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<DD> \<CC>"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps 
          cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  from \<alpha>\<beta> show 
    "exp_cf_cat \<alpha> \<GG> \<DD> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<DD> : 
      cat_FUNCT \<alpha> \<DD> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<DD> \<CC>"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps 
          cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  from \<alpha>\<beta> have dom_lhs:
    "\<D>\<^sub>\<circ> (exp_cf_cat \<alpha> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) \<DD>\<lparr>ObjMap\<rparr>) = cat_FUNCT \<alpha> \<DD> \<AA>\<lparr>Obj\<rparr>"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps 
          cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  from \<alpha>\<beta> have dom_rhs: 
    "\<D>\<^sub>\<circ> ((exp_cf_cat \<alpha> \<GG> \<DD> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<DD>)\<lparr>ObjMap\<rparr>) = 
      cat_FUNCT \<alpha> \<DD> \<AA>\<lparr>Obj\<rparr>"
    by
      (
        cs_concl
          cs_simp: cat_cs_simps 
          cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  show 
    "exp_cf_cat \<alpha> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) \<DD>\<lparr>ObjMap\<rparr> =
      (exp_cf_cat \<alpha> \<GG> \<DD> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<DD>)\<lparr>ObjMap\<rparr>"
  proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
    show "vsv (exp_cf_cat \<alpha> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) \<DD>\<lparr>ObjMap\<rparr>)"
      by (cs_concl cs_intro: cat_FUNCT_cs_intros)
    from \<alpha>\<beta> show "vsv ((exp_cf_cat \<alpha> \<GG> \<DD> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<DD>)\<lparr>ObjMap\<rparr>)"
      by 
        (
          cs_concl cs_intro: 
            cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    fix \<HH> assume "\<HH> \<in>\<^sub>\<circ> cat_FUNCT \<alpha> \<DD> \<AA>\<lparr>Obj\<rparr>"
    then have "\<HH> \<in>\<^sub>\<circ> cf_maps \<alpha> \<DD> \<AA>" unfolding cat_FUNCT_components by simp
    then obtain \<HH>' where \<HH>_def: "\<HH> = cf_map \<HH>'" and \<HH>': "\<HH>' : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
      by auto
    from assms \<alpha>\<beta> \<HH>' show 
      "exp_cf_cat \<alpha> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) \<DD>\<lparr>ObjMap\<rparr>\<lparr>\<HH>\<rparr> =
        (exp_cf_cat \<alpha> \<GG> \<DD> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<DD>)\<lparr>ObjMap\<rparr>\<lparr>\<HH>\<rparr>"
      by (subst (1 2) \<HH>_def)
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
  qed simp
  from \<alpha>\<beta> have dom_lhs:
    "\<D>\<^sub>\<circ> (exp_cf_cat \<alpha> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) \<DD>\<lparr>ArrMap\<rparr>) = cat_FUNCT \<alpha> \<DD> \<AA>\<lparr>Arr\<rparr>"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps 
          cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  from \<alpha>\<beta> have dom_rhs: 
    "\<D>\<^sub>\<circ> ((exp_cf_cat \<alpha> \<GG> \<DD> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<DD>)\<lparr>ArrMap\<rparr>) =
      cat_FUNCT \<alpha> \<DD> \<AA>\<lparr>Arr\<rparr>"
    by
      (
        cs_concl 
          cs_simp: cat_cs_simps 
          cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  show 
    "exp_cf_cat \<alpha> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) \<DD>\<lparr>ArrMap\<rparr> =
      (exp_cf_cat \<alpha> \<GG> \<DD> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<DD>)\<lparr>ArrMap\<rparr>"
  proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
    show "vsv (exp_cf_cat \<alpha> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) \<DD>\<lparr>ArrMap\<rparr>)"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_FUNCT_cs_intros)
    from \<alpha>\<beta> show "vsv ((exp_cf_cat \<alpha> \<GG> \<DD> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<DD>)\<lparr>ArrMap\<rparr>)"
      by 
        (
          cs_concl cs_intro:
            cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )                           
    fix \<NN> assume "\<NN> \<in>\<^sub>\<circ> cat_FUNCT \<alpha> \<DD> \<AA>\<lparr>Arr\<rparr>"
    then obtain \<HH> \<HH>' where \<NN>: "\<NN> : \<HH> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<DD> \<AA>\<^esub> \<HH>'" 
      by (auto intro: is_arrI)
    note \<NN> = cat_FUNCT_is_arrD[OF \<NN>]
    from \<alpha>\<beta> assms \<NN>(1,3,4) show 
      "exp_cf_cat \<alpha> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) \<DD>\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<rparr> =
        (exp_cf_cat \<alpha> \<GG> \<DD> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<DD>)\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<rparr>"
      by (subst (1 2) \<NN>(2))
        (
          cs_concl
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps cf_comp_cf_ntcf_comp_assoc
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
  qed simp
qed simp_all

lemma exp_cf_cat_cf_id_cat:
  assumes "category \<alpha> \<CC>" and "category \<alpha> \<DD>"
  shows "exp_cf_cat \<alpha> (cf_id \<CC>) \<DD> = cf_id (cat_FUNCT \<alpha> \<DD> \<CC>)"
proof(rule cf_eqI)

  interpret \<CC>: category \<alpha> \<CC> by (rule assms)
  interpret \<DD>: category \<alpha> \<DD> by (rule assms)

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    by (simp_all add: \<beta>_def \<CC>.\<Z>_Limit_\<alpha>\<omega> \<CC>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<CC>.\<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 

  from \<alpha>\<beta> show
    "cf_id (cat_FUNCT \<alpha> \<DD> \<CC>) : cat_FUNCT \<alpha> \<DD> \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<DD> \<CC>"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps 
          cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
      )
  from \<alpha>\<beta> show
    "exp_cf_cat \<alpha> (cf_id \<CC>) \<DD> : cat_FUNCT \<alpha> \<DD> \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<DD> \<CC>"
    by 
      (
        cs_concl
          cs_simp: cat_cs_simps 
          cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
      )
  from \<alpha>\<beta> have ObjMap_dom_lhs:
    "\<D>\<^sub>\<circ> (exp_cf_cat \<alpha> (cf_id \<CC>) \<DD>\<lparr>ObjMap\<rparr>) = cat_FUNCT \<alpha> \<DD> \<CC>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros)
  from \<alpha>\<beta> have ObjMap_dom_rhs:
    "\<D>\<^sub>\<circ> (cf_id (cat_FUNCT \<alpha> \<DD> \<CC>)\<lparr>ObjMap\<rparr>) = cat_FUNCT \<alpha> \<DD> \<CC>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)
  show "exp_cf_cat \<alpha> (cf_id \<CC>) \<DD>\<lparr>ObjMap\<rparr> = cf_id (cat_FUNCT \<alpha> \<DD> \<CC>)\<lparr>ObjMap\<rparr>"
  proof
    (
      rule vsv_eqI, 
      unfold ObjMap_dom_lhs ObjMap_dom_rhs cat_FUNCT_components(1)
    )
    fix \<HH> assume prems: "\<HH> \<in>\<^sub>\<circ> cf_maps \<alpha> \<DD> \<CC>"
    then obtain \<HH>' where \<HH>_def: "\<HH> = cf_map \<HH>'" and \<HH>': "\<HH>' : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by clarsimp
    from prems \<HH>' show 
      "exp_cf_cat \<alpha> (cf_id \<CC>) \<DD>\<lparr>ObjMap\<rparr>\<lparr>\<HH>\<rparr> = cf_id (cat_FUNCT \<alpha> \<DD> \<CC>)\<lparr>ObjMap\<rparr>\<lparr>\<HH>\<rparr>"
      by (subst (1 2) \<HH>_def)
        (
          cs_concl
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
  qed (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)+
  from \<alpha>\<beta> have ArrMap_dom_lhs:
    "\<D>\<^sub>\<circ> (cf_id (cat_FUNCT \<alpha> \<DD> \<CC>)\<lparr>ArrMap\<rparr>) = cat_FUNCT \<alpha> \<DD> \<CC>\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)
  from \<alpha>\<beta> have ArrMap_dom_rhs:
    "\<D>\<^sub>\<circ> (exp_cf_cat \<alpha> (cf_id \<CC>) \<DD>\<lparr>ArrMap\<rparr>) = cat_FUNCT \<alpha> \<DD> \<CC>\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros)
  show "exp_cf_cat \<alpha> (cf_id \<CC>) \<DD>\<lparr>ArrMap\<rparr> = cf_id (cat_FUNCT \<alpha> \<DD> \<CC>)\<lparr>ArrMap\<rparr>"
  proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
    fix \<NN> assume "\<NN> \<in>\<^sub>\<circ> cat_FUNCT \<alpha> \<DD> \<CC>\<lparr>Arr\<rparr>"
    then obtain \<FF> \<GG> where \<NN>: "\<NN> : \<FF> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<DD> \<CC>\<^esub> \<GG>" 
      by (auto intro: is_arrI)
    note \<NN> = cat_FUNCT_is_arrD[OF \<NN>]
    from \<NN>(1,3,4) \<alpha>\<beta> show 
      "exp_cf_cat \<alpha> (cf_id \<CC>) \<DD>\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<rparr> =
        cf_id (cat_FUNCT \<alpha> \<DD> \<CC>)\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<rparr>"
      by (subst (1 2) \<NN>(2))
        (
          cs_concl
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
  qed (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)

qed simp_all


lemma cf_comp_exp_cf_cat_exp_cf_cat_cf_id[cat_FUNCT_cs_simps]:
  assumes "category \<alpha> \<AA>" and "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "exp_cf_cat \<alpha> \<FF> \<AA> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> (cf_id \<BB>) \<AA> = exp_cf_cat \<alpha> \<FF> \<AA>"
proof-

  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<FF>: is_functor \<alpha> \<BB> \<CC> \<FF> by (rule assms(2))

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have \<beta>: "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    by (simp_all add: \<beta>_def \<AA>.\<Z>_Limit_\<alpha>\<omega> \<AA>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<AA>.\<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 

  show ?thesis
  proof(rule cf_eqI)
    from assms \<alpha>\<beta> \<beta> show \<FF>\<AA>:
      "exp_cf_cat \<alpha> \<FF> \<AA> : cat_FUNCT \<alpha> \<AA> \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<AA> \<CC>"
      by (cs_concl cs_intro: cat_small_cs_intros cat_FUNCT_cs_intros)
    with assms \<alpha>\<beta> show 
      "exp_cf_cat \<alpha> \<FF> \<AA> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> (cf_id \<BB>) \<AA> :
        cat_FUNCT \<alpha> \<AA> \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<AA> \<CC>"
      by 
        (
          cs_concl cs_intro: 
            cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        )
    from assms \<alpha>\<beta> have ObjMap_dom_lhs:
      "\<D>\<^sub>\<circ> ((exp_cf_cat \<alpha> \<FF> \<AA> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> (cf_id \<BB>) \<AA>)\<lparr>ObjMap\<rparr>) =
        cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps
            cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        )
    from assms have ObjMap_dom_rhs: 
      "\<D>\<^sub>\<circ> (exp_cf_cat \<alpha> \<FF> \<AA>\<lparr>ObjMap\<rparr>) = cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_FUNCT_cs_simps)
    from assms \<alpha>\<beta> have ArrMap_dom_lhs:
      "\<D>\<^sub>\<circ> ((exp_cf_cat \<alpha> \<FF> \<AA> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> (cf_id \<BB>) \<AA>)\<lparr>ArrMap\<rparr>) =
        cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Arr\<rparr>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps
            cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        )
    from assms have ArrMap_dom_rhs: 
      "\<D>\<^sub>\<circ> (exp_cf_cat \<alpha> \<FF> \<AA>\<lparr>ArrMap\<rparr>) = cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Arr\<rparr>"
      by (cs_concl cs_simp: cat_FUNCT_cs_simps)
    show 
      "(exp_cf_cat \<alpha> \<FF> \<AA> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> (cf_id \<BB>) \<AA>)\<lparr>ObjMap\<rparr> =
        exp_cf_cat \<alpha> \<FF> \<AA>\<lparr>ObjMap\<rparr>"
    proof
      (
        rule vsv_eqI,
        unfold ObjMap_dom_lhs ObjMap_dom_rhs cat_FUNCT_components(1)
      )
      fix \<HH> assume prems: "\<HH> \<in>\<^sub>\<circ> cf_maps \<alpha> \<AA> \<BB>"
      then obtain \<HH>' where \<HH>_def: "\<HH> = cf_map \<HH>'" and \<HH>': "\<HH>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
        by clarsimp
      from prems \<HH>' assms \<FF>\<AA> \<alpha>\<beta> show 
        "(exp_cf_cat \<alpha> \<FF> \<AA> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> (cf_id \<BB>) \<AA>)\<lparr>ObjMap\<rparr>\<lparr>\<HH>\<rparr> =
          exp_cf_cat \<alpha> \<FF> \<AA>\<lparr>ObjMap\<rparr>\<lparr>\<HH>\<rparr>"
        unfolding \<HH>_def
        by 
          (
            cs_concl
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps
              cs_intro: cat_FUNCT_cs_intros cat_small_cs_intros cat_cs_intros
          )
    qed 
      (
        use assms \<FF>\<AA> \<alpha>\<beta> in
          \<open>
            cs_concl
              cs_intro: cat_FUNCT_cs_intros cat_small_cs_intros cat_cs_intros
          \<close>
      )
    show 
      "(exp_cf_cat \<alpha> \<FF> \<AA> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> (cf_id \<BB>) \<AA>)\<lparr>ArrMap\<rparr> =
        exp_cf_cat \<alpha> \<FF> \<AA>\<lparr>ArrMap\<rparr>"
    proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
      fix \<MM> assume "\<MM> \<in>\<^sub>\<circ> cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Arr\<rparr>"
      then obtain \<FF>' \<GG>' where \<MM>: "\<MM> : \<FF>' \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<GG>'"
        by (auto intro: is_arrI)
      note \<MM> = cat_FUNCT_is_arrD[OF \<MM>]
      from \<MM>(1) assms \<FF>\<AA> \<alpha>\<beta> show 
        "(exp_cf_cat \<alpha> \<FF> \<AA> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> (cf_id \<BB>) \<AA>)\<lparr>ArrMap\<rparr>\<lparr>\<MM>\<rparr> =
          exp_cf_cat \<alpha> \<FF> \<AA>\<lparr>ArrMap\<rparr>\<lparr>\<MM>\<rparr>"
        by (subst (1 2) \<MM>(2))
          (
            cs_concl
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps
              cs_intro: cat_FUNCT_cs_intros cat_small_cs_intros cat_cs_intros
          )
    qed
      (
        use assms \<alpha>\<beta> in 
          \<open>
            cs_concl cs_intro:
              cat_FUNCT_cs_intros cat_small_cs_intros cat_cs_intros
          \<close>
      )
  qed simp_all

qed

lemma cf_comp_exp_cf_cat_cf_id_exp_cf_cat[cat_FUNCT_cs_simps]:
  assumes "category \<alpha> \<AA>" and "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "exp_cf_cat \<alpha> (cf_id \<CC>) \<AA> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<AA> = exp_cf_cat \<alpha> \<FF> \<AA>"
proof-

  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<FF>: is_functor \<alpha> \<BB> \<CC> \<FF> by (rule assms(2))

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have \<beta>: "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    by (simp_all add: \<beta>_def \<AA>.\<Z>_Limit_\<alpha>\<omega> \<AA>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<AA>.\<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 

  show ?thesis
  proof(rule cf_eqI)
    from assms \<alpha>\<beta> \<beta> show \<FF>\<AA>:
      "exp_cf_cat \<alpha> \<FF> \<AA> : cat_FUNCT \<alpha> \<AA> \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<AA> \<CC>"
      by (cs_concl cs_simp: cs_intro: cat_small_cs_intros cat_FUNCT_cs_intros)
    with assms \<alpha>\<beta> show 
      "exp_cf_cat \<alpha> (cf_id \<CC>) \<AA> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<AA> :
        cat_FUNCT \<alpha> \<AA> \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<AA> \<CC>"
      by 
        (
          cs_concl cs_intro: 
            cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        )
    from assms \<alpha>\<beta> have ObjMap_dom_lhs:
      "\<D>\<^sub>\<circ> ((exp_cf_cat \<alpha> (cf_id \<CC>) \<AA> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<AA>)\<lparr>ObjMap\<rparr>) =
        cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps
            cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        )
    from assms have ObjMap_dom_rhs: 
      "\<D>\<^sub>\<circ> (exp_cf_cat \<alpha> \<FF> \<AA>\<lparr>ObjMap\<rparr>) = cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_FUNCT_cs_simps)
    from assms \<alpha>\<beta> have ArrMap_dom_lhs:
      "\<D>\<^sub>\<circ> ((exp_cf_cat \<alpha> (cf_id \<CC>) \<AA> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<AA>)\<lparr>ArrMap\<rparr>) =
        cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Arr\<rparr>"
      by
        (
          cs_concl 
            cs_simp: cat_cs_simps
            cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        )
    from assms have ArrMap_dom_rhs: 
      "\<D>\<^sub>\<circ> (exp_cf_cat \<alpha> \<FF> \<AA>\<lparr>ArrMap\<rparr>) = cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Arr\<rparr>"
      by (cs_concl cs_simp: cat_FUNCT_cs_simps)
    show 
      "(exp_cf_cat \<alpha> (cf_id \<CC>) \<AA> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<AA>)\<lparr>ObjMap\<rparr> =
        exp_cf_cat \<alpha> \<FF> \<AA>\<lparr>ObjMap\<rparr>"
    proof
      (
        rule vsv_eqI, 
        unfold ObjMap_dom_lhs ObjMap_dom_rhs cat_FUNCT_components(1)
      )
      fix \<HH> assume prems: "\<HH> \<in>\<^sub>\<circ> cf_maps \<alpha> \<AA> \<BB>"
      then obtain \<HH>' where \<HH>_def: "\<HH> = cf_map \<HH>'" and \<HH>': "\<HH>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
        by clarsimp
      from prems \<HH>' assms \<alpha>\<beta> \<FF>\<AA> show 
        "(exp_cf_cat \<alpha> (cf_id \<CC>) \<AA> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<AA>)\<lparr>ObjMap\<rparr>\<lparr>\<HH>\<rparr> =
          exp_cf_cat \<alpha> \<FF> \<AA>\<lparr>ObjMap\<rparr>\<lparr>\<HH>\<rparr>"
        unfolding \<HH>_def
        by 
          (
            cs_concl
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
              cs_intro: cat_FUNCT_cs_intros cat_small_cs_intros cat_cs_intros
          )
    qed 
      (
        use assms \<alpha>\<beta> \<FF>\<AA> in 
          \<open>
            cs_concl
              cs_intro: cat_FUNCT_cs_intros cat_small_cs_intros cat_cs_intros
          \<close>
      )
    show 
      "(exp_cf_cat \<alpha> (cf_id \<CC>) \<AA> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<AA>)\<lparr>ArrMap\<rparr> =
        exp_cf_cat \<alpha> \<FF> \<AA>\<lparr>ArrMap\<rparr>"
    proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
      fix \<MM> assume "\<MM> \<in>\<^sub>\<circ> cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Arr\<rparr>"
      then obtain \<FF>' \<GG>' where \<MM>: "\<MM> : \<FF>' \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<GG>'"
        by (auto intro: is_arrI)
      note \<MM> = cat_FUNCT_is_arrD[OF \<MM>]
      from \<MM>(1) assms \<alpha>\<beta> \<FF>\<AA> show 
        "(exp_cf_cat \<alpha> (cf_id \<CC>) \<AA> \<circ>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<AA>)\<lparr>ArrMap\<rparr>\<lparr>\<MM>\<rparr> =
          exp_cf_cat \<alpha> \<FF> \<AA>\<lparr>ArrMap\<rparr>\<lparr>\<MM>\<rparr>"
        by (subst (1 2) \<MM>(2))
          (
            cs_concl
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps
              cs_intro: cat_FUNCT_cs_intros cat_small_cs_intros cat_cs_intros
          )
    qed
      (
        use assms \<alpha>\<beta> in
          \<open>
            cs_concl
              cs_intro: cat_FUNCT_cs_intros cat_small_cs_intros cat_cs_intros
          \<close>
      )
  qed simp_all

qed



subsection\<open>Category raised to the power of a functor\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition exp_cat_cf :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "exp_cat_cf \<alpha> \<AA> \<KK> =
    [
      (
        \<lambda>\<SS>\<in>\<^sub>\<circ>cat_FUNCT \<alpha> (\<KK>\<lparr>HomCod\<rparr>) \<AA>\<lparr>Obj\<rparr>.
          cf_map (cf_of_cf_map (\<KK>\<lparr>HomCod\<rparr>) \<AA> \<SS> \<circ>\<^sub>C\<^sub>F \<KK>)
      ),
      (
        \<lambda>\<sigma>\<in>\<^sub>\<circ>cat_FUNCT \<alpha> (\<KK>\<lparr>HomCod\<rparr>) \<AA>\<lparr>Arr\<rparr>.
          ntcf_arrow (ntcf_of_ntcf_arrow (\<KK>\<lparr>HomCod\<rparr>) \<AA> \<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)
      ),
      cat_FUNCT \<alpha> (\<KK>\<lparr>HomCod\<rparr>) \<AA>,
      cat_FUNCT \<alpha> (\<KK>\<lparr>HomDom\<rparr>) \<AA> 
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma exp_cat_cf_components:
  shows "exp_cat_cf \<alpha> \<AA> \<KK>\<lparr>ObjMap\<rparr> =
    (
      \<lambda>\<SS>\<in>\<^sub>\<circ>cat_FUNCT \<alpha> (\<KK>\<lparr>HomCod\<rparr>) \<AA>\<lparr>Obj\<rparr>.
        cf_map (cf_of_cf_map (\<KK>\<lparr>HomCod\<rparr>) \<AA> \<SS> \<circ>\<^sub>C\<^sub>F \<KK>)
    )"
    and "exp_cat_cf \<alpha> \<AA> \<KK>\<lparr>ArrMap\<rparr> = 
    (
      \<lambda>\<sigma>\<in>\<^sub>\<circ>cat_FUNCT \<alpha> (\<KK>\<lparr>HomCod\<rparr>) \<AA>\<lparr>Arr\<rparr>.
        ntcf_arrow (ntcf_of_ntcf_arrow (\<KK>\<lparr>HomCod\<rparr>) \<AA> \<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>)
    )"
    and "exp_cat_cf \<alpha> \<AA> \<KK>\<lparr>HomDom\<rparr> = cat_FUNCT \<alpha> (\<KK>\<lparr>HomCod\<rparr>) \<AA>"
    and "exp_cat_cf \<alpha> \<AA> \<KK>\<lparr>HomCod\<rparr> = cat_FUNCT \<alpha> (\<KK>\<lparr>HomDom\<rparr>) \<AA>"
  unfolding exp_cat_cf_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

context 
  fixes \<alpha> \<KK> \<BB> \<CC>
  assumes \<KK>: "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
begin

interpretation \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule \<KK>)

mk_VLambda exp_cat_cf_components(1)[where \<KK>=\<KK> and \<alpha>=\<alpha>, unfolded cat_cs_simps]
  |vsv exp_cat_cf_components_ObjMap_vsv[cat_FUNCT_cs_intros]|
  |vdomain exp_cat_cf_components_ObjMap_vdomain[cat_FUNCT_cs_simps]|
  |app exp_cat_cf_components_ObjMap_app[cat_FUNCT_cs_simps]|

end


subsubsection\<open>Arrow map\<close>

context 
  fixes \<alpha> \<KK> \<BB> \<CC>
  assumes \<KK>: "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
begin

interpretation \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule \<KK>)

mk_VLambda exp_cat_cf_components(2)[where \<KK>=\<KK> and \<alpha>=\<alpha>, unfolded cat_cs_simps]
  |vsv exp_cat_cf_components_ArrMap_vsv[cat_FUNCT_cs_intros]|
  |vdomain exp_cat_cf_components_ArrMap_vdomain[cat_FUNCT_cs_simps]|
  |app exp_cat_cf_components_ArrMap_app[cat_FUNCT_cs_simps]|

end


subsubsection\<open>Domain and codomain\<close>

context 
  fixes \<alpha> \<KK> \<BB> \<CC>
  assumes \<KK>: "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
begin

interpretation \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule \<KK>)

lemmas exp_cat_cf_HomDom[cat_FUNCT_cs_simps] = 
    exp_cat_cf_components(3)[where \<KK>=\<KK> and \<alpha>=\<alpha>, unfolded cat_cs_simps]
  and exp_cat_cf_HomCod[cat_FUNCT_cs_simps] = 
    exp_cat_cf_components(4)[where \<KK>=\<KK> and \<alpha>=\<alpha>, unfolded cat_cs_simps]

end


subsubsection\<open>Category raised to the power of a functor is a functor\<close>

lemma exp_cat_cf_is_tiny_functor: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" and "category \<alpha> \<AA>" and "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "exp_cat_cf \<alpha> \<AA> \<KK> : cat_FUNCT \<alpha> \<CC> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<BB> \<AA>"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<AA>: category \<alpha> \<AA> by (rule assms(3))
  interpret \<KK>: is_functor \<alpha> \<BB> \<CC> \<KK> by (rule assms(4))
  from assms(2-4) interpret \<CC>\<AA>: tiny_category \<beta> \<open>cat_FUNCT \<alpha> \<CC> \<AA>\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  from assms(2-4) interpret \<BB>\<AA>: tiny_category \<beta> \<open>cat_FUNCT \<alpha> \<BB> \<AA>\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  show ?thesis
  proof(intro is_tiny_functorI' is_functorI')
    show "vfsequence (exp_cat_cf \<alpha> \<AA> \<KK>)" unfolding exp_cat_cf_def by auto
    show "vcard (exp_cat_cf \<alpha> \<AA> \<KK>) = 4\<^sub>\<nat>"
      unfolding exp_cat_cf_def by (simp_all add: nat_omega_simps)
    show "\<R>\<^sub>\<circ> (exp_cat_cf \<alpha> \<AA> \<KK>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_FUNCT \<alpha> \<BB> \<AA>\<lparr>Obj\<rparr>"
    proof
      (
        unfold cat_FUNCT_components exp_cat_cf_components, 
        intro vrange_VLambda_vsubset, 
        unfold cat_cs_simps
      )
      fix \<FF> assume "\<FF> \<in>\<^sub>\<circ> cf_maps \<alpha> \<CC> \<AA>"
      then obtain \<FF>' where \<FF>_def: "\<FF> = cf_map \<FF>'" and \<FF>': "\<FF>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
        by auto
      from assms(2-4) \<FF>' show 
        "cf_map (cf_of_cf_map \<CC> \<AA> \<FF> \<circ>\<^sub>C\<^sub>F \<KK>) \<in>\<^sub>\<circ> cf_maps \<alpha> \<BB> \<AA>"
        unfolding \<FF>_def
        by 
          ( 
            cs_concl 
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
              cs_intro: cat_cs_intros cat_FUNCT_cs_intros
          )
    qed
    show "exp_cat_cf \<alpha> \<AA> \<KK>\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<rparr> :
      exp_cat_cf \<alpha> \<AA> \<KK>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<rparr> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<BB> \<AA>\<^esub>
      exp_cat_cf \<alpha> \<AA> \<KK>\<lparr>ObjMap\<rparr>\<lparr>\<GG>\<rparr>"
      if "\<NN> : \<FF> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> \<AA>\<^esub> \<GG>" for \<FF> \<GG> \<NN> 
    proof-
      note \<NN> = cat_FUNCT_is_arrD[OF that]
      from \<NN>(1) assms(2-4) show ?thesis
        by (subst \<NN>(2), use nothing in \<open>subst \<NN>(3), subst \<NN>(4)\<close>) 
          (
            cs_concl
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
              cs_intro: cat_cs_intros  cat_FUNCT_cs_intros
          )
    qed
    show
      "exp_cat_cf \<alpha> \<AA> \<KK>\<lparr>ArrMap\<rparr>\<lparr>\<MM> \<circ>\<^sub>A\<^bsub>cat_FUNCT \<alpha> \<CC> \<AA>\<^esub> \<NN>\<rparr> =
        exp_cat_cf \<alpha> \<AA> \<KK>\<lparr>ArrMap\<rparr>\<lparr>\<MM>\<rparr> \<circ>\<^sub>A\<^bsub>cat_FUNCT \<alpha> \<BB> \<AA>\<^esub>
        exp_cat_cf \<alpha> \<AA> \<KK>\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<rparr>"
      if "\<MM> : \<GG> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> \<AA>\<^esub> \<HH>" and "\<NN> : \<FF> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> \<AA>\<^esub> \<GG>" 
      for \<GG> \<HH> \<MM> \<FF> \<NN>
    proof-
      note \<MM> = cat_FUNCT_is_arrD[OF that(1)]
        and \<NN> = cat_FUNCT_is_arrD[OF that(2)]  
      from \<MM>(1) \<NN>(1) assms(2-4) show ?thesis  
        by (subst (1 2) \<MM>(2), use nothing in \<open>subst (1 2) \<NN>(2)\<close>)
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps  
              cs_intro: cat_cs_intros cat_FUNCT_cs_intros
          )
    qed
    show
      "exp_cat_cf \<alpha> \<AA> \<KK>\<lparr>ArrMap\<rparr>\<lparr>cat_FUNCT \<alpha> \<CC> \<AA>\<lparr>CId\<rparr>\<lparr>\<FF>\<rparr>\<rparr> =
        cat_FUNCT \<alpha> \<BB> \<AA>\<lparr>CId\<rparr>\<lparr>exp_cat_cf \<alpha> \<AA> \<KK>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<rparr>\<rparr>"
      if "\<FF> \<in>\<^sub>\<circ> cat_FUNCT \<alpha> \<CC> \<AA>\<lparr>Obj\<rparr>" for \<FF>
    proof-
      from that have \<FF>: "\<FF> \<in>\<^sub>\<circ> cf_maps \<alpha> \<CC> \<AA>" 
        unfolding cat_FUNCT_components by simp
      then obtain \<FF>' where \<FF>_def: "\<FF> = cf_map \<FF>'" and \<FF>': "\<FF>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
        by auto
      from assms(2-4) \<FF> \<FF>' show ?thesis
        by 
          (
            cs_concl
              cs_simp: 
                cat_cs_simps cat_FUNCT_cs_simps cat_FUNCT_components(1) \<FF>_def
              cs_intro: cat_cs_intros cat_FUNCT_cs_intros
          )
    qed
  qed 
    (
      cs_concl 
        cs_simp: cat_FUNCT_cs_simps
        cs_intro: cat_small_cs_intros cat_FUNCT_cs_intros cat_cs_intros
    )+
qed

lemma exp_cat_cf_is_tiny_functor'[cat_FUNCT_cs_intros]: 
  assumes "\<Z> \<beta>" 
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    and "category \<alpha> \<AA>" 
    and "\<KK> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<AA>' = cat_FUNCT \<alpha> \<CC> \<AA>"
    and "\<BB>' = cat_FUNCT \<alpha> \<BB> \<AA>"
  shows "exp_cat_cf \<alpha> \<AA> \<KK> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> \<BB>'"
  using assms(1-4) unfolding assms(5,6) by (rule exp_cat_cf_is_tiny_functor)


subsubsection\<open>Further properties\<close>

lemma exp_cat_cf_cat_cf_id:
  assumes "category \<alpha> \<AA>" and "category \<alpha> \<CC>"
  shows "exp_cat_cf \<alpha> \<AA> (cf_id \<CC>) = cf_id (cat_FUNCT \<alpha> \<CC> \<AA>)"
proof-

  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<CC>: category \<alpha> \<CC> by (rule assms(2))

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have \<beta>: "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    by (simp_all add: \<beta>_def \<AA>.\<Z>_Limit_\<alpha>\<omega> \<AA>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<AA>.\<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 

  show ?thesis
  proof(rule cf_eqI)

    from \<alpha>\<beta> show "exp_cat_cf \<alpha> \<AA> (cf_id \<CC>) :
      cat_FUNCT \<alpha> \<CC> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<CC> \<AA>"
      by 
        (
          cs_concl
            cs_simp: cat_cs_simps
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from \<alpha>\<beta> show 
      "cf_id (cat_FUNCT \<alpha> \<CC> \<AA>) : cat_FUNCT \<alpha> \<CC> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<CC> \<AA>"
      by
        (
          cs_concl
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from \<alpha>\<beta> have ObjMap_dom_lhs:
      "\<D>\<^sub>\<circ> (exp_cat_cf \<alpha> \<AA> (cf_id \<CC>)\<lparr>ObjMap\<rparr>) = cat_FUNCT \<alpha> \<CC> \<AA>\<lparr>Obj\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps
            cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        )
    from \<alpha>\<beta> have ObjMap_dom_rhs:
      "\<D>\<^sub>\<circ> (cf_id (cat_FUNCT \<alpha> \<CC> \<AA>)\<lparr>ObjMap\<rparr>) = cat_FUNCT \<alpha> \<CC> \<AA>\<lparr>Obj\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps 
            cs_intro: cat_small_cs_intros cat_FUNCT_cs_intros
        )
    show "exp_cat_cf \<alpha> \<AA> (cf_id \<CC>)\<lparr>ObjMap\<rparr> = cf_id (cat_FUNCT \<alpha> \<CC> \<AA>)\<lparr>ObjMap\<rparr>"
    proof(rule vsv_eqI, unfold ObjMap_dom_lhs ObjMap_dom_rhs cat_FUNCT_components(1))
      fix \<FF> assume "\<FF> \<in>\<^sub>\<circ> cf_maps \<alpha> \<CC> \<AA>"
      then obtain \<FF>' where \<FF>_def: "\<FF> = cf_map \<FF>'" and \<FF>': "\<FF>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
        by clarsimp
      from \<FF>' show 
        "exp_cat_cf \<alpha> \<AA> (cf_id \<CC>)\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<rparr> =
          cf_id (cat_FUNCT \<alpha> \<CC> \<AA>)\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<rparr>"
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps \<FF>_def 
              cs_intro: cat_cs_intros cat_FUNCT_cs_intros
          )
    qed (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)+

    from \<alpha>\<beta> have ArrMap_dom_lhs: 
      "\<D>\<^sub>\<circ> (exp_cat_cf \<alpha> \<AA> (cf_id \<CC>)\<lparr>ArrMap\<rparr>) = cat_FUNCT \<alpha> \<CC> \<AA>\<lparr>Arr\<rparr>"
      by
        (
          cs_concl 
            cs_simp: cat_cs_simps 
            cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        )
    from \<alpha>\<beta> have ArrMap_dom_rhs:
      "\<D>\<^sub>\<circ> (cf_id (cat_FUNCT \<alpha> \<CC> \<AA>)\<lparr>ArrMap\<rparr>) = cat_FUNCT \<alpha> \<CC> \<AA>\<lparr>Arr\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps 
            cs_intro: cat_small_cs_intros cat_FUNCT_cs_intros
        )
    show "exp_cat_cf \<alpha> \<AA> (cf_id \<CC>)\<lparr>ArrMap\<rparr> = cf_id (cat_FUNCT \<alpha> \<CC> \<AA>)\<lparr>ArrMap\<rparr>"
    proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
      fix \<NN> assume "\<NN> \<in>\<^sub>\<circ> cat_FUNCT \<alpha> \<CC> \<AA>\<lparr>Arr\<rparr>"
      then obtain \<HH> \<HH>' where \<NN>: "\<NN> : \<HH> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> \<AA>\<^esub> \<HH>'" 
        by (auto intro: is_arrI)
      note \<NN> = cat_FUNCT_is_arrD[OF \<NN>]
      from \<NN>(1) show 
        "exp_cat_cf \<alpha> \<AA> (cf_id \<CC>)\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<rparr> =
          cf_id (cat_FUNCT \<alpha> \<CC> \<AA>)\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<rparr>"
        by (subst (1 2) \<NN>(2))
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
              cs_intro: cat_cs_intros cat_FUNCT_cs_intros
          )
    qed (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)+

  qed simp_all

qed

lemma exp_cat_cf_cf_comp:
  assumes "category \<alpha> \<AA>" and "\<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "exp_cat_cf \<alpha> \<AA> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) = exp_cat_cf \<alpha> \<AA> \<FF> \<circ>\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<AA> \<GG>"
proof-

  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<CC> \<DD> \<GG> by (rule assms(2))
  interpret \<FF>: is_functor \<alpha> \<BB> \<CC> \<FF> by (rule assms(3))
 
  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have \<beta>: "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    by (simp_all add: \<beta>_def \<AA>.\<Z>_Limit_\<alpha>\<omega> \<AA>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<AA>.\<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 

  show ?thesis
  proof(rule cf_eqI)  
    from \<beta> \<alpha>\<beta> show "exp_cat_cf \<alpha> \<AA> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) :
      cat_FUNCT \<alpha> \<DD> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<BB> \<AA>"
      by
        (
          cs_concl 
            cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        )
    from \<beta> \<alpha>\<beta> show "exp_cat_cf \<alpha> \<AA> \<FF> \<circ>\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<AA> \<GG> :
      cat_FUNCT \<alpha> \<DD> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<BB> \<AA>"
      by 
        (
          cs_concl
            cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        )
    from \<beta> \<alpha>\<beta> have ObjMap_dom_lhs: 
      "\<D>\<^sub>\<circ> (exp_cat_cf \<alpha> \<AA> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>) = cat_FUNCT \<alpha> \<DD> \<AA>\<lparr>Obj\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_FUNCT_cs_simps 
            cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        )
    from \<beta> \<alpha>\<beta> have ObjMap_dom_rhs: 
      "\<D>\<^sub>\<circ> ((exp_cat_cf \<alpha> \<AA> \<FF> \<circ>\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<AA> \<GG>)\<lparr>ObjMap\<rparr>) =
        cat_FUNCT \<alpha> \<DD> \<AA>\<lparr>Obj\<rparr>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
            cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        )
    from \<beta> \<alpha>\<beta> have ArrMap_dom_lhs: 
      "\<D>\<^sub>\<circ> (exp_cat_cf \<alpha> \<AA> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>) = cat_FUNCT \<alpha> \<DD> \<AA>\<lparr>Arr\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_FUNCT_cs_simps 
            cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        )
    from \<beta> \<alpha>\<beta> have ArrMap_dom_rhs: 
      "\<D>\<^sub>\<circ> ((exp_cat_cf \<alpha> \<AA> \<FF> \<circ>\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<AA> \<GG>)\<lparr>ArrMap\<rparr>) =
        cat_FUNCT \<alpha> \<DD> \<AA>\<lparr>Arr\<rparr>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
            cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        )
    show 
      "exp_cat_cf \<alpha> \<AA> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr> =
        (exp_cat_cf \<alpha> \<AA> \<FF> \<circ>\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<AA> \<GG>)\<lparr>ObjMap\<rparr>"
    proof
      (
        rule vsv_eqI, 
        unfold ObjMap_dom_lhs ObjMap_dom_rhs cat_FUNCT_components(1)
      )
      fix \<HH> assume "\<HH> \<in>\<^sub>\<circ> cf_maps \<alpha> \<DD> \<AA>"
      then obtain \<HH>' where \<HH>_def: "\<HH> = cf_map \<HH>'" and \<HH>': "\<HH>' : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
        by clarsimp
      from \<beta> \<alpha>\<beta>  \<HH>' assms show 
        "exp_cat_cf \<alpha> \<AA> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>\<lparr>\<HH>\<rparr> =
          (exp_cat_cf \<alpha> \<AA> \<FF> \<circ>\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<AA> \<GG>)\<lparr>ObjMap\<rparr>\<lparr>\<HH>\<rparr>"
        unfolding \<HH>_def (*slow*)
        by 
          (
            cs_concl
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps
              cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros 
          )
    qed 
      (
        use \<beta> \<alpha>\<beta> in
          \<open>
            cs_concl
              cs_simp: cat_FUNCT_cs_simps
              cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
          \<close>
      )+
    show "exp_cat_cf \<alpha> \<AA> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr> =
      (exp_cat_cf \<alpha> \<AA> \<FF> \<circ>\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<AA> \<GG>)\<lparr>ArrMap\<rparr>"
    proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
      fix \<NN> assume "\<NN> \<in>\<^sub>\<circ> cat_FUNCT \<alpha> \<DD> \<AA>\<lparr>Arr\<rparr>"
      then obtain \<HH> \<HH>' where \<NN>: "\<NN> : \<HH> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<DD> \<AA>\<^esub> \<HH>'" 
        by (auto intro: is_arrI)
      note \<NN> = cat_FUNCT_is_arrD[OF \<NN>]
      from assms \<NN>(1) \<beta> \<alpha>\<beta> show 
        "exp_cat_cf \<alpha> \<AA> (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<rparr> =
          (exp_cat_cf \<alpha> \<AA> \<FF> \<circ>\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<AA> \<GG>)\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<rparr>"
        by (subst (1 2) \<NN>(2))
          (
            cs_concl
              cs_simp:
                cat_FUNCT_cs_simps cat_cs_simps ntcf_cf_comp_ntcf_cf_comp_assoc
              cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
          )
    qed 
      (
        use \<beta> \<alpha>\<beta> in
          \<open>
            cs_concl
              cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
          \<close>
      )+
  qed simp_all

qed



subsection\<open>Natural transformation raised to the power of a category\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition exp_ntcf_cat :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "exp_ntcf_cat \<alpha> \<NN> \<DD> =
    [
      (
        \<lambda>\<SS>\<in>\<^sub>\<circ>cat_FUNCT \<alpha> \<DD> (\<NN>\<lparr>NTDGDom\<rparr>)\<lparr>Obj\<rparr>.
          ntcf_arrow (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F cf_of_cf_map \<DD> (\<NN>\<lparr>NTDGDom\<rparr>) \<SS>)
      ),
      exp_cf_cat \<alpha> (\<NN>\<lparr>NTDom\<rparr>) \<DD>,
      exp_cf_cat \<alpha> (\<NN>\<lparr>NTCod\<rparr>) \<DD>,
      cat_FUNCT \<alpha> \<DD> (\<NN>\<lparr>NTDGDom\<rparr>),
      cat_FUNCT \<alpha> \<DD> (\<NN>\<lparr>NTDGCod\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma exp_ntcf_cat_components:
  shows "exp_ntcf_cat \<alpha> \<NN> \<DD>\<lparr>NTMap\<rparr> =
    (
      \<lambda>\<SS>\<in>\<^sub>\<circ>cat_FUNCT \<alpha> \<DD> (\<NN>\<lparr>NTDGDom\<rparr>)\<lparr>Obj\<rparr>.
        ntcf_arrow (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F cf_of_cf_map \<DD> (\<NN>\<lparr>NTDGDom\<rparr>) \<SS>)
    )"
    and "exp_ntcf_cat \<alpha> \<NN> \<DD>\<lparr>NTDom\<rparr> = exp_cf_cat \<alpha> (\<NN>\<lparr>NTDom\<rparr>) \<DD>"
    and "exp_ntcf_cat \<alpha> \<NN> \<DD>\<lparr>NTCod\<rparr> = exp_cf_cat \<alpha> (\<NN>\<lparr>NTCod\<rparr>) \<DD>"
    and "exp_ntcf_cat \<alpha> \<NN> \<DD>\<lparr>NTDGDom\<rparr> = cat_FUNCT \<alpha> \<DD> (\<NN>\<lparr>NTDGDom\<rparr>)"
    and "exp_ntcf_cat \<alpha> \<NN> \<DD>\<lparr>NTDGCod\<rparr> = cat_FUNCT \<alpha> \<DD> (\<NN>\<lparr>NTDGCod\<rparr>)"
  unfolding exp_ntcf_cat_def nt_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Natural transformation map\<close>

mk_VLambda exp_ntcf_cat_components(1)
  |vsv exp_ntcf_cat_components_NTMap_vsv[cat_FUNCT_cs_intros]|

context is_ntcf
begin

lemmas exp_ntcf_cat_components' = 
  exp_ntcf_cat_components[where \<alpha>=\<alpha> and \<NN>=\<NN>, unfolded cat_cs_simps]

lemmas [cat_FUNCT_cs_simps] = exp_ntcf_cat_components'(2-5)

mk_VLambda exp_ntcf_cat_components(1)[where \<NN>=\<NN>, unfolded cat_cs_simps]
  |vdomain exp_ntcf_cat_components_NTMap_vdomain[cat_FUNCT_cs_simps]|
  |app exp_ntcf_cat_components_NTMap_app[cat_FUNCT_cs_simps]|

end

lemmas [cat_FUNCT_cs_simps] = 
  is_ntcf.exp_ntcf_cat_components'(2-5)
  is_ntcf.exp_ntcf_cat_components_NTMap_vdomain
  is_ntcf.exp_ntcf_cat_components_NTMap_app


subsubsection\<open>
Natural transformation raised to the power of a category 
is a natural transformation
\<close>

lemma exp_ntcf_cat_is_tiny_ntcf:
  assumes "\<Z> \<beta>" 
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "category \<alpha> \<DD>"
  shows "exp_ntcf_cat \<alpha> \<NN> \<DD> :
    exp_cf_cat \<alpha> \<FF> \<DD> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y exp_cf_cat \<alpha> \<GG> \<DD> :
    cat_FUNCT \<alpha> \<DD> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<DD> \<BB>"
proof(rule is_tiny_ntcfI')

  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(3))
  interpret \<DD>: category \<alpha> \<DD> by (rule assms(4))

  let ?exp_\<NN> = \<open>exp_ntcf_cat \<alpha> \<NN> \<DD>\<close>
  let ?exp_\<FF> = \<open>exp_cf_cat \<alpha> \<FF> \<DD>\<close>
  let ?exp_\<GG> = \<open>exp_cf_cat \<alpha> \<GG> \<DD>\<close>

  from assms(1,2) show 
    "exp_cf_cat \<alpha> \<FF> \<DD> : cat_FUNCT \<alpha> \<DD> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<DD> \<BB>"
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  from assms(1,2) show 
    "exp_cf_cat \<alpha> \<GG> \<DD> : cat_FUNCT \<alpha> \<DD> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<DD> \<BB>"
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)

  show "?exp_\<NN> : 
    ?exp_\<FF> \<mapsto>\<^sub>C\<^sub>F ?exp_\<GG> : cat_FUNCT \<alpha> \<DD> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<DD> \<BB>"
  proof(rule is_ntcfI')

    show "vfsequence (?exp_\<NN>)" unfolding exp_ntcf_cat_def by auto
    show "vcard (?exp_\<NN>) = 5\<^sub>\<nat>"
      unfolding exp_ntcf_cat_def by (simp add: nat_omega_simps)

    from assms(1,2) show "?exp_\<FF> : cat_FUNCT \<alpha> \<DD> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<DD> \<BB>"
      by 
        (
          cs_concl cs_intro: 
            cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from assms(1,2) show "?exp_\<GG> : cat_FUNCT \<alpha> \<DD> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<DD> \<BB>"
      by 
        (
          cs_concl cs_intro:
            cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )

    show "?exp_\<NN>\<lparr>NTMap\<rparr>\<lparr>\<HH>\<rparr> : 
      ?exp_\<FF>\<lparr>ObjMap\<rparr>\<lparr>\<HH>\<rparr> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<DD> \<BB>\<^esub> ?exp_\<GG>\<lparr>ObjMap\<rparr>\<lparr>\<HH>\<rparr>"
      if "\<HH> \<in>\<^sub>\<circ> cat_FUNCT \<alpha> \<DD> \<AA>\<lparr>Obj\<rparr>" for \<HH>
    proof-
      from that[unfolded cat_FUNCT_cs_simps] have "\<HH> \<in>\<^sub>\<circ> cf_maps \<alpha> \<DD> \<AA>" by simp
      then obtain \<HH>' where \<HH>_def: "\<HH> = cf_map \<HH>'" and \<HH>': "\<HH>' : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
        by auto
      from \<HH>' show ?thesis
        by 
          (
            cs_concl 
              cs_simp: cat_FUNCT_cs_simps \<HH>_def 
              cs_intro: cat_cs_intros cat_FUNCT_cs_intros
          )
    qed
    
    show 
      "?exp_\<NN>\<lparr>NTMap\<rparr>\<lparr>\<TT>\<rparr> \<circ>\<^sub>A\<^bsub>cat_FUNCT \<alpha> \<DD> \<BB>\<^esub> ?exp_\<FF>\<lparr>ArrMap\<rparr>\<lparr>\<LL>\<rparr> =
        ?exp_\<GG>\<lparr>ArrMap\<rparr>\<lparr>\<LL>\<rparr> \<circ>\<^sub>A\<^bsub>cat_FUNCT \<alpha> \<DD> \<BB>\<^esub> ?exp_\<NN>\<lparr>NTMap\<rparr>\<lparr>\<SS>\<rparr>"
      if "\<LL> : \<SS> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<DD> \<AA>\<^esub> \<TT>" for \<SS> \<TT> \<LL>
    proof-
      note \<LL> = cat_FUNCT_is_arrD[OF that]
      let ?\<SS> = \<open>cf_of_cf_map \<DD> \<AA> \<SS>\<close>
        and ?\<TT> = \<open>cf_of_cf_map \<DD> \<AA> \<TT>\<close>
        and ?\<LL> = \<open>ntcf_of_ntcf_arrow \<DD> \<AA> \<LL>\<close>
      have [cat_cs_simps]:
        "(\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F ?\<TT>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<LL>) =
          (\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<LL>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F ?\<SS>)"
      proof(rule ntcf_eqI)
        from \<LL>(1) show
          "(\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F ?\<TT>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<LL>) :
            \<FF> \<circ>\<^sub>C\<^sub>F ?\<SS> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F ?\<TT> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
          by (cs_concl cs_intro: cat_cs_intros)
        from \<LL>(1) show
          "(\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<LL>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F ?\<SS>) :
            \<FF> \<circ>\<^sub>C\<^sub>F ?\<SS> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F ?\<TT> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
          by (cs_concl cs_intro: cat_cs_intros)
        from \<LL>(1) have dom_lhs:
          "\<D>\<^sub>\<circ> (((\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F ?\<TT>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<LL>))\<lparr>NTMap\<rparr>) = \<DD>\<lparr>Obj\<rparr>"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        from \<LL>(1) have dom_rhs:
          "\<D>\<^sub>\<circ> (((\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<LL>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F ?\<SS>))\<lparr>NTMap\<rparr>) = \<DD>\<lparr>Obj\<rparr>"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        show 
          "((\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F ?\<TT>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<LL>))\<lparr>NTMap\<rparr> =
            ((\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<LL>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F ?\<SS>))\<lparr>NTMap\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
          fix d assume "d \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
          with \<LL>(1) show
            "((\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F ?\<TT>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<FF> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<LL>))\<lparr>NTMap\<rparr>\<lparr>d\<rparr> =
              ((\<GG> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?\<LL>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F ?\<SS>))\<lparr>NTMap\<rparr>\<lparr>d\<rparr>"
            by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        qed (cs_concl cs_intro: cat_cs_intros)
      qed simp_all
      from \<LL>(1,3,4) that show ?thesis
        by (subst (1 2) \<LL>(2), use nothing in \<open>subst \<LL>(3), subst \<LL>(4)\<close>)
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
              cs_intro: cat_cs_intros cat_FUNCT_cs_intros
          )
    qed
  qed 
    (
      cs_concl 
        cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros cat_FUNCT_cs_intros
    )+

qed

lemma exp_ntcf_cat_is_tiny_ntcf'[cat_FUNCT_cs_intros]:
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "category \<alpha> \<DD>"
    and "\<FF>' = exp_cf_cat \<alpha> \<FF> \<DD>"
    and "\<GG>' = exp_cf_cat \<alpha> \<GG> \<DD>"
    and "\<AA>' = cat_FUNCT \<alpha> \<DD> \<AA>"
    and "\<BB>' = cat_FUNCT \<alpha> \<DD> \<BB>"
  shows "exp_ntcf_cat \<alpha> \<NN> \<DD> : \<FF>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> \<BB>'"
  using assms(1-4) unfolding assms(5-8) by (rule exp_ntcf_cat_is_tiny_ntcf)


subsubsection\<open>Further properties\<close>

lemma exp_ntcf_cat_cf_ntcf_comp: 
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "category \<alpha> \<DD>"
  shows 
    "exp_ntcf_cat \<alpha> (\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) \<DD> =
      exp_cf_cat \<alpha> \<HH> \<DD> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_ntcf_cat \<alpha> \<NN> \<DD>"
proof-

  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<HH>: is_functor \<alpha> \<BB> \<CC> \<HH> by (rule assms(2))
  interpret \<DD>: category \<alpha> \<DD> by (rule assms(3))

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    by (simp_all add: \<beta>_def \<NN>.\<Z>_Limit_\<alpha>\<omega> \<NN>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<NN>.\<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 

  show ?thesis
  proof(rule ntcf_eqI)
    from \<alpha>\<beta> have dom_lhs:
      "\<D>\<^sub>\<circ> (exp_ntcf_cat \<alpha> (\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) \<DD>\<lparr>NTMap\<rparr>) = cat_FUNCT \<alpha> \<DD> \<AA>\<lparr>Obj\<rparr>"
      by 
        (
          cs_concl
            cs_simp: cat_cs_simps
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from \<alpha>\<beta> have dom_rhs: 
      "\<D>\<^sub>\<circ> ((exp_cf_cat \<alpha> \<HH> \<DD> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_ntcf_cat \<alpha> \<NN> \<DD>)\<lparr>NTMap\<rparr>) =
        cat_FUNCT \<alpha> \<DD> \<AA>\<lparr>Obj\<rparr>"
      by 
        (
          cs_concl
            cs_simp: cat_cs_simps
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    show
      "exp_ntcf_cat \<alpha> (\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) \<DD>\<lparr>NTMap\<rparr> =
        (exp_cf_cat \<alpha> \<HH> \<DD> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_ntcf_cat \<alpha> \<NN> \<DD>)\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs cat_FUNCT_components(1))
      fix \<KK> assume prems: "\<KK> \<in>\<^sub>\<circ> cf_maps \<alpha> \<DD> \<AA>"
      then obtain \<KK>' where \<KK>_def: "\<KK> = cf_map \<KK>'" and \<KK>': "\<KK>' : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
        by (auto intro: is_arrI)
      from \<alpha>\<beta> prems \<KK>' show 
        "exp_ntcf_cat \<alpha> (\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) \<DD>\<lparr>NTMap\<rparr>\<lparr>\<KK>\<rparr> =
          (exp_cf_cat \<alpha> \<HH> \<DD> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_ntcf_cat \<alpha> \<NN> \<DD>)\<lparr>NTMap\<rparr>\<lparr>\<KK>\<rparr>"
        by 
          (
            cs_concl
              cs_simp:
                cf_ntcf_comp_ntcf_cf_comp_assoc 
                cat_cs_simps cat_FUNCT_cs_simps
                \<KK>_def
              cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
          )
    qed (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  qed
    (
      cs_concl
        cs_simp: exp_cf_cat_cf_comp cat_cs_simps cat_FUNCT_cs_simps
        cs_intro: \<alpha>\<beta> cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
    )+

qed

lemma exp_ntcf_cat_ntcf_cf_comp: 
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "category \<alpha> \<DD>"
  shows 
    "exp_ntcf_cat \<alpha> (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<HH>) \<DD> =
      exp_ntcf_cat \<alpha> \<NN> \<DD> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<HH> \<DD>"
proof-

  interpret \<NN>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<HH>: is_functor \<alpha> \<AA> \<BB> \<HH> by (rule assms(2))
  interpret \<DD>: category \<alpha> \<DD> by (rule assms(3))

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    by (simp_all add: \<beta>_def \<NN>.\<Z>_Limit_\<alpha>\<omega> \<NN>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<NN>.\<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 

  show ?thesis
  proof(rule ntcf_eqI)
    from \<alpha>\<beta> have dom_lhs:
      "\<D>\<^sub>\<circ> (exp_ntcf_cat \<alpha> (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<HH>) \<DD>\<lparr>NTMap\<rparr>) = cat_FUNCT \<alpha> \<DD> \<AA>\<lparr>Obj\<rparr>"
      by 
        (
          cs_concl
            cs_simp: cat_cs_simps
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from \<alpha>\<beta> have dom_rhs: 
      "\<D>\<^sub>\<circ> ((exp_ntcf_cat \<alpha> \<NN> \<DD> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<HH> \<DD>)\<lparr>NTMap\<rparr>) =
        cat_FUNCT \<alpha> \<DD> \<AA>\<lparr>Obj\<rparr>"
      by 
        (
          cs_concl
            cs_simp: cat_cs_simps
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    show
      "exp_ntcf_cat \<alpha> (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<HH>) \<DD>\<lparr>NTMap\<rparr> =
        (exp_ntcf_cat \<alpha> \<NN> \<DD> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<HH> \<DD>)\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs cat_FUNCT_components(1))
      fix \<KK> assume prems: "\<KK> \<in>\<^sub>\<circ> cf_maps \<alpha> \<DD> \<AA>"
      then obtain \<KK>' where \<KK>_def: "\<KK> = cf_map \<KK>'" and \<KK>': "\<KK>' : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
        by (auto intro: is_arrI)
      from \<alpha>\<beta> assms prems \<KK>' show
        "exp_ntcf_cat \<alpha> (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<HH>) \<DD>\<lparr>NTMap\<rparr>\<lparr>\<KK>\<rparr> = 
          (exp_ntcf_cat \<alpha> \<NN> \<DD> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<HH> \<DD>)\<lparr>NTMap\<rparr>\<lparr>\<KK>\<rparr>"
        by 
          (
            cs_concl 
              cs_simp: 
                ntcf_cf_comp_ntcf_cf_comp_assoc 
                cat_cs_simps cat_FUNCT_cs_simps 
                \<KK>_def
              cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
          )
    qed (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  qed
    (
      cs_concl
        cs_simp: exp_cf_cat_cf_comp cat_cs_simps cat_FUNCT_cs_simps
        cs_intro: \<alpha>\<beta> cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
    )+
qed

lemma exp_ntcf_cat_ntcf_vcomp: 
  assumes "category \<alpha> \<AA>" 
    and "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows 
    "exp_ntcf_cat \<alpha> (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) \<AA> =
      exp_ntcf_cat \<alpha> \<MM> \<AA> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_ntcf_cat \<alpha> \<NN> \<AA>"
proof-

  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<MM>: is_ntcf \<alpha> \<BB> \<CC> \<GG> \<HH> \<MM> by (rule assms(2))
  interpret \<NN>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<NN> by (rule assms(3))

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have \<beta>: "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    by (simp_all add: \<beta>_def \<AA>.\<Z>_Limit_\<alpha>\<omega> \<AA>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<AA>.\<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 

  show ?thesis
  proof(rule ntcf_eqI)
    from \<alpha>\<beta> show
      "exp_ntcf_cat \<alpha> (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) \<AA> :
        exp_cf_cat \<alpha> \<FF> \<AA> \<mapsto>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<HH> \<AA> :
        cat_FUNCT \<alpha> \<AA> \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<AA> \<CC>"
      by 
        (
          cs_concl 
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from \<alpha>\<beta> show
      "exp_ntcf_cat \<alpha> \<MM> \<AA> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_ntcf_cat \<alpha> \<NN> \<AA> :
        exp_cf_cat \<alpha> \<FF> \<AA> \<mapsto>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<HH> \<AA> :
        cat_FUNCT \<alpha> \<AA> \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<AA> \<CC>"
      by 
        (
          cs_concl 
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from \<alpha>\<beta> have dom_lhs: 
      "\<D>\<^sub>\<circ> ((exp_ntcf_cat \<alpha> \<MM> \<AA> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_ntcf_cat \<alpha> \<NN> \<AA>)\<lparr>NTMap\<rparr>) = 
        cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
      by 
        (
          cs_concl
            cs_simp: cat_cs_simps
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    have dom_rhs: 
      "\<D>\<^sub>\<circ> (exp_ntcf_cat \<alpha> (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) \<AA>\<lparr>NTMap\<rparr>) = cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros)
    show 
      "exp_ntcf_cat \<alpha> (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) \<AA>\<lparr>NTMap\<rparr> = 
        (exp_ntcf_cat \<alpha> \<MM> \<AA> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_ntcf_cat \<alpha> \<NN> \<AA>)\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs cat_FUNCT_components(1))
      fix \<FF>' assume "\<FF>' \<in>\<^sub>\<circ> cf_maps \<alpha> \<AA> \<BB>"
      then obtain \<FF>'' 
        where \<FF>'_def: "\<FF>' = cf_map \<FF>''" and \<FF>'': "\<FF>'' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
        by auto
      from \<FF>'' \<alpha>\<beta> show 
        "exp_ntcf_cat \<alpha> (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) \<AA>\<lparr>NTMap\<rparr>\<lparr>\<FF>'\<rparr> =
          (exp_ntcf_cat \<alpha> \<MM> \<AA> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_ntcf_cat \<alpha> \<NN> \<AA>)\<lparr>NTMap\<rparr>\<lparr>\<FF>'\<rparr>"
        unfolding \<FF>'_def
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps
              cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
          )
    qed (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)+
  qed simp_all

qed

lemma ntcf_id_exp_cf_cat:
  assumes "category \<alpha> \<AA>" and "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "ntcf_id (exp_cf_cat \<alpha> \<FF> \<AA>) = exp_ntcf_cat \<alpha> (ntcf_id \<FF>) \<AA>"
proof-

  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<FF>: is_functor \<alpha> \<BB> \<CC> \<FF> by (rule assms(2))

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have \<beta>: "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    by (simp_all add: \<beta>_def \<AA>.\<Z>_Limit_\<alpha>\<omega> \<AA>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<AA>.\<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 

  show ?thesis
  proof(rule ntcf_eqI)
    from \<alpha>\<beta> show "exp_ntcf_cat \<alpha> (ntcf_id \<FF>) \<AA> :
      exp_cf_cat \<alpha> \<FF> \<AA> \<mapsto>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<AA> :
      cat_FUNCT \<alpha> \<AA> \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<AA> \<CC>"
      by 
        (
          cs_concl 
            cs_simp: cat_FUNCT_cs_simps 
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from \<alpha>\<beta> show "ntcf_id (exp_cf_cat \<alpha> \<FF> \<AA>) :
      exp_cf_cat \<alpha> \<FF> \<AA> \<mapsto>\<^sub>C\<^sub>F exp_cf_cat \<alpha> \<FF> \<AA> :
      cat_FUNCT \<alpha> \<AA> \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<AA> \<CC>"
      by 
        (
          cs_concl 
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from \<alpha>\<beta> assms have dom_lhs: 
      "\<D>\<^sub>\<circ> (ntcf_id (exp_cf_cat \<alpha> \<FF> \<AA>)\<lparr>NTMap\<rparr>) = cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps 
            cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        )
    from \<alpha>\<beta> assms have dom_rhs:
      "\<D>\<^sub>\<circ> (exp_ntcf_cat \<alpha> (ntcf_id \<FF>) \<AA>\<lparr>NTMap\<rparr>) = cat_FUNCT \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps 
            cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        )
    show
      "ntcf_id (exp_cf_cat \<alpha> \<FF> \<AA>)\<lparr>NTMap\<rparr> = exp_ntcf_cat \<alpha> (ntcf_id \<FF>) \<AA>\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs cat_FUNCT_components(1))
      fix \<GG> assume "\<GG> \<in>\<^sub>\<circ> cf_maps \<alpha> \<AA> \<BB>"
      then obtain \<GG>' 
        where \<GG>_def: "\<GG> = cf_map \<GG>'" and \<GG>': "\<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
        by auto  
      from \<GG>' \<alpha>\<beta> show 
        "ntcf_id (exp_cf_cat \<alpha> \<FF> \<AA>)\<lparr>NTMap\<rparr>\<lparr>\<GG>\<rparr> =
          exp_ntcf_cat \<alpha> (ntcf_id \<FF>) \<AA>\<lparr>NTMap\<rparr>\<lparr>\<GG>\<rparr>"
        unfolding \<GG>_def
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
              cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
          )
    qed 
      (
        cs_concl 
          cs_intro: \<alpha>\<beta> cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )+
  qed simp_all
qed



subsection\<open>Category raised to the power of the natural transformation\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition exp_cat_ntcf :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "exp_cat_ntcf \<alpha> \<CC> \<NN> =
    [
      (
        \<lambda>\<SS>\<in>\<^sub>\<circ>cat_FUNCT \<alpha> (\<NN>\<lparr>NTDGCod\<rparr>) \<CC>\<lparr>Obj\<rparr>.
          ntcf_arrow (cf_of_cf_map (\<NN>\<lparr>NTDGCod\<rparr>) \<CC> \<SS> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)
      ),
      exp_cat_cf \<alpha> \<CC> (\<NN>\<lparr>NTDom\<rparr>),
      exp_cat_cf \<alpha> \<CC> (\<NN>\<lparr>NTCod\<rparr>),
      cat_FUNCT \<alpha> (\<NN>\<lparr>NTDGCod\<rparr>) \<CC>,
      cat_FUNCT \<alpha> (\<NN>\<lparr>NTDGDom\<rparr>) \<CC>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma exp_cat_ntcf_components:
  shows "exp_cat_ntcf \<alpha> \<CC> \<NN>\<lparr>NTMap\<rparr> =
    (
      \<lambda>\<SS>\<in>\<^sub>\<circ>cat_FUNCT \<alpha> (\<NN>\<lparr>NTDGCod\<rparr>) \<CC>\<lparr>Obj\<rparr>.
        ntcf_arrow (cf_of_cf_map (\<NN>\<lparr>NTDGCod\<rparr>) \<CC> \<SS> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)
    )"
    and "exp_cat_ntcf \<alpha> \<CC> \<NN>\<lparr>NTDom\<rparr> = exp_cat_cf \<alpha> \<CC> (\<NN>\<lparr>NTDom\<rparr>)"
    and "exp_cat_ntcf \<alpha> \<CC> \<NN>\<lparr>NTCod\<rparr> = exp_cat_cf \<alpha> \<CC> (\<NN>\<lparr>NTCod\<rparr>)"
    and "exp_cat_ntcf \<alpha> \<CC> \<NN>\<lparr>NTDGDom\<rparr> = cat_FUNCT \<alpha> (\<NN>\<lparr>NTDGCod\<rparr>) \<CC>"
    and "exp_cat_ntcf \<alpha> \<CC> \<NN>\<lparr>NTDGCod\<rparr> = cat_FUNCT \<alpha> (\<NN>\<lparr>NTDGDom\<rparr>) \<CC>"
  unfolding exp_cat_ntcf_def nt_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Natural transformation map\<close>

mk_VLambda exp_cat_ntcf_components(1)
  |vsv exp_cat_ntcf_components_NTMap_vsv[cat_FUNCT_cs_intros]|

context is_ntcf
begin

lemmas exp_cat_ntcf_components' = 
  exp_cat_ntcf_components[where \<alpha>=\<alpha> and \<NN>=\<NN>, unfolded cat_cs_simps]

lemmas [cat_FUNCT_cs_simps] = exp_cat_ntcf_components'(2-5)

mk_VLambda exp_cat_ntcf_components(1)[where \<NN>=\<NN>, unfolded cat_cs_simps]
  |vdomain exp_cat_ntcf_components_NTMap_vdomain[cat_FUNCT_cs_simps]|
  |app exp_cat_ntcf_components_NTMap_app[cat_FUNCT_cs_simps]|

end

lemmas exp_cat_ntcf_components' = is_ntcf.exp_cat_ntcf_components'

lemmas [cat_FUNCT_cs_simps] = 
  is_ntcf.exp_cat_ntcf_components'(2-5)
  is_ntcf.exp_cat_ntcf_components_NTMap_vdomain
  is_ntcf.exp_cat_ntcf_components_NTMap_app


subsubsection\<open>
Category raised to the power of a natural transformation
is a natural transformation
\<close>

lemma exp_cat_ntcf_is_tiny_ntcf:
  assumes "\<Z> \<beta>" 
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "category \<alpha> \<CC>"
  shows "exp_cat_ntcf \<alpha> \<CC> \<NN> :
    exp_cat_cf \<alpha> \<CC> \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y exp_cat_cf \<alpha> \<CC> \<GG> :
    cat_FUNCT \<alpha> \<BB> \<CC> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<AA> \<CC>"
proof(rule is_tiny_ntcfI')

  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(3))
  interpret \<CC>: category \<alpha> \<CC> by (rule assms(4))

  let ?exp_\<NN> = \<open>exp_cat_ntcf \<alpha> \<CC> \<NN>\<close>
  let ?exp_\<FF> = \<open>exp_cat_cf \<alpha> \<CC> \<FF>\<close>
  let ?exp_\<GG> = \<open>exp_cat_cf \<alpha> \<CC> \<GG>\<close>

  from assms(1,2) show
    "exp_cat_cf \<alpha> \<CC> \<GG> : cat_FUNCT \<alpha> \<BB> \<CC> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<AA> \<CC>"
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  from assms(1,2) show
    "exp_cat_cf \<alpha> \<CC> \<FF> : cat_FUNCT \<alpha> \<BB> \<CC> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<AA> \<CC>"
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)

  show "?exp_\<NN> : ?exp_\<FF> \<mapsto>\<^sub>C\<^sub>F ?exp_\<GG> : cat_FUNCT \<alpha> \<BB> \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<AA> \<CC>"
  proof(rule is_ntcfI')

    show "vfsequence (?exp_\<NN>)" unfolding exp_cat_ntcf_def by auto
    show "vcard (?exp_\<NN>) = 5\<^sub>\<nat>"
      unfolding exp_cat_ntcf_def by (simp add: nat_omega_simps)
  
    from assms(1,2) show
      "exp_cat_cf \<alpha> \<CC> \<GG> : cat_FUNCT \<alpha> \<BB> \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<AA> \<CC>"
      by 
        (
          cs_concl cs_intro:
            cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )

    from assms(1,2) show 
      "exp_cat_cf \<alpha> \<CC> \<FF> : cat_FUNCT \<alpha> \<BB> \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<AA> \<CC>"
      by 
        (
          cs_concl cs_intro: 
            cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
  
    show "exp_cat_ntcf \<alpha> \<CC> \<NN>\<lparr>NTMap\<rparr>\<lparr>\<HH>\<rparr> : 
      exp_cat_cf \<alpha> \<CC> \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<HH>\<rparr> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<AA> \<CC>\<^esub> 
      exp_cat_cf \<alpha> \<CC> \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<HH>\<rparr>"
      if "\<HH> \<in>\<^sub>\<circ> cat_FUNCT \<alpha> \<BB> \<CC>\<lparr>Obj\<rparr>" for \<HH>
    proof-
      from that[unfolded cat_FUNCT_cs_simps] have "\<HH> \<in>\<^sub>\<circ> cf_maps \<alpha> \<BB> \<CC>" by simp
      then obtain \<HH>' where \<HH>_def: "\<HH> = cf_map \<HH>'" and \<HH>': "\<HH>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
        by auto
      from \<HH>' show ?thesis
        unfolding \<HH>_def
        by
          (
            cs_concl
              cs_simp: cat_FUNCT_cs_simps \<HH>_def
              cs_intro: cat_cs_intros cat_FUNCT_cs_intros
          )
    qed
  
    show 
      "?exp_\<NN>\<lparr>NTMap\<rparr>\<lparr>\<TT>\<rparr> \<circ>\<^sub>A\<^bsub>cat_FUNCT \<alpha> \<AA> \<CC>\<^esub> ?exp_\<FF>\<lparr>ArrMap\<rparr>\<lparr>\<LL>\<rparr> =
        ?exp_\<GG>\<lparr>ArrMap\<rparr>\<lparr>\<LL>\<rparr> \<circ>\<^sub>A\<^bsub>cat_FUNCT \<alpha> \<AA> \<CC>\<^esub> ?exp_\<NN>\<lparr>NTMap\<rparr>\<lparr>\<SS>\<rparr>"
      if "\<LL> : \<SS> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<BB> \<CC>\<^esub> \<TT>" for \<SS> \<TT> \<LL>
    proof-
      note \<LL> = cat_FUNCT_is_arrD[OF that]
      let ?\<SS> = \<open>cf_of_cf_map \<BB> \<CC> \<SS>\<close>
        and ?\<TT> = \<open>cf_of_cf_map \<BB> \<CC> \<TT>\<close>
        and ?\<LL> = \<open>ntcf_of_ntcf_arrow \<BB> \<CC> \<LL>\<close>
      have [cat_cs_simps]:
        "(?\<TT> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (?\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF>) =
          (?\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (?\<SS> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)"
      proof(rule ntcf_eqI)
        from \<LL>(1) show
          "(?\<TT> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (?\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF>) :
            ?\<SS> \<circ>\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>C\<^sub>F ?\<TT> \<circ>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
          by (cs_concl cs_intro: cat_cs_intros)
        from \<LL>(1) show
          "(?\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (?\<SS> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) :
            ?\<SS> \<circ>\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>C\<^sub>F ?\<TT> \<circ>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
          by (cs_concl cs_intro: cat_cs_intros)
        from \<LL>(1) have dom_lhs:
          "\<D>\<^sub>\<circ> (((?\<TT> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (?\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF>))\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        from \<LL>(1) have dom_rhs:
          "\<D>\<^sub>\<circ> (((?\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (?\<SS> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
          by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
        show 
          "((?\<TT> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (?\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF>))\<lparr>NTMap\<rparr> =
            ((?\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (?\<SS> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
          fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
          with \<LL>(1) show
            "((?\<TT> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (?\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF>))\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
              ((?\<LL> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<GG>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (?\<SS> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
            by 
              (
                cs_concl 
                  cs_simp: cat_cs_simps is_ntcf.ntcf_Comp_commute 
                  cs_intro: cat_cs_intros
              )
        qed (cs_concl cs_intro: cat_cs_intros)
      qed simp_all
      from \<LL>(1,3,4) that show ?thesis
        by (subst (1 2) \<LL>(2), use nothing in \<open>subst \<LL>(3), subst \<LL>(4)\<close>)
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
              cs_intro: cat_cs_intros cat_FUNCT_cs_intros
          )
    qed

  qed
    (
      cs_concl 
        cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros cat_FUNCT_cs_intros
    )+

qed

lemma exp_cat_ntcf_is_tiny_ntcf'[cat_FUNCT_cs_intros]:
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "category \<alpha> \<CC>"
    and "\<FF>' = exp_cat_cf \<alpha> \<CC> \<FF>"
    and "\<GG>' = exp_cat_cf \<alpha> \<CC> \<GG>"
    and "\<AA>' = cat_FUNCT \<alpha> \<BB> \<CC>"
    and "\<BB>' = cat_FUNCT \<alpha> \<AA> \<CC>"
  shows "exp_cat_ntcf \<alpha> \<CC> \<NN> : \<FF>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> \<BB>'"
  using assms(1-4) unfolding assms(5-8) by (rule exp_cat_ntcf_is_tiny_ntcf)


subsubsection\<open>Further properties\<close>

lemma ntcf_id_exp_cat_cf:
  assumes "category \<alpha> \<AA>" and "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "ntcf_id (exp_cat_cf \<alpha> \<AA> \<FF>) = exp_cat_ntcf \<alpha> \<AA> (ntcf_id \<FF>)"
proof-

  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<FF>: is_functor \<alpha> \<BB> \<CC> \<FF> by (rule assms(2))

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have \<beta>: "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    by (simp_all add: \<beta>_def \<AA>.\<Z>_Limit_\<alpha>\<omega> \<AA>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<AA>.\<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 

  show ?thesis
  proof(rule ntcf_eqI)
    from \<alpha>\<beta> show "exp_cat_ntcf \<alpha> \<AA> (ntcf_id \<FF>) :
      exp_cat_cf \<alpha> \<AA> \<FF> \<mapsto>\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<AA> \<FF> :
      cat_FUNCT \<alpha> \<CC> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<BB> \<AA>"
      by 
        (
          cs_concl 
            cs_simp: cat_FUNCT_cs_simps 
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from assms \<beta> \<alpha>\<beta> show "ntcf_id (exp_cat_cf \<alpha> \<AA> \<FF>) :
      exp_cat_cf \<alpha> \<AA> \<FF> \<mapsto>\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<AA> \<FF> :
      cat_FUNCT \<alpha> \<CC> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<BB> \<AA>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps 
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from \<alpha>\<beta> assms have dom_lhs: 
      "\<D>\<^sub>\<circ> (exp_cat_ntcf \<alpha> \<AA> (ntcf_id \<FF>)\<lparr>NTMap\<rparr>) = cat_FUNCT \<alpha> \<CC> \<AA>\<lparr>Obj\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps 
            cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        )
    from \<alpha>\<beta> assms have dom_rhs:
      "\<D>\<^sub>\<circ> (ntcf_id (exp_cat_cf \<alpha> \<AA> \<FF>)\<lparr>NTMap\<rparr>) = cat_FUNCT \<alpha> \<CC> \<AA>\<lparr>Obj\<rparr>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps
            cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
        )
    show
      "ntcf_id (exp_cat_cf \<alpha> \<AA> \<FF>)\<lparr>NTMap\<rparr> = exp_cat_ntcf \<alpha> \<AA> (ntcf_id \<FF>)\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs cat_FUNCT_components(1))
      fix \<GG> assume "\<GG> \<in>\<^sub>\<circ> cf_maps \<alpha> \<CC> \<AA>"
      then obtain \<GG>' 
        where \<GG>_def: "\<GG> = cf_map \<GG>'" and \<GG>': "\<GG>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
        by auto  
      from \<GG>' \<alpha>\<beta> show 
        "ntcf_id (exp_cat_cf \<alpha> \<AA> \<FF>)\<lparr>NTMap\<rparr>\<lparr>\<GG>\<rparr> =
          exp_cat_ntcf \<alpha> \<AA> (ntcf_id \<FF>)\<lparr>NTMap\<rparr>\<lparr>\<GG>\<rparr>"
        unfolding \<GG>_def
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cat_FUNCT_cs_simps
              cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
          )
    qed 
      (
        cs_concl 
          cs_intro: \<alpha>\<beta> cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )+
  qed simp_all

qed

lemma exp_cat_ntcf_ntcf_cf_comp:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "category \<alpha> \<DD>"
  shows 
    "exp_cat_ntcf \<alpha> \<DD> (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<HH>) =
      exp_cat_cf \<alpha> \<DD> \<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_cat_ntcf \<alpha> \<DD> \<NN>"
proof-

  interpret \<NN>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<HH>: is_functor \<alpha> \<AA> \<BB> \<HH> by (rule assms(2))
  interpret \<DD>: category \<alpha> \<DD> by (rule assms(3))

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    by (simp_all add: \<beta>_def \<NN>.\<Z>_Limit_\<alpha>\<omega> \<NN>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<NN>.\<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 

  show ?thesis
  proof(rule ntcf_eqI)
    from \<alpha>\<beta> have dom_lhs:
      "\<D>\<^sub>\<circ> (exp_cat_ntcf \<alpha> \<DD> (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<HH>)\<lparr>NTMap\<rparr>) = cat_FUNCT \<alpha> \<CC> \<DD>\<lparr>Obj\<rparr>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from \<alpha>\<beta> have dom_rhs: 
      "\<D>\<^sub>\<circ> ((exp_cat_cf \<alpha> \<DD> \<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_cat_ntcf \<alpha> \<DD> \<NN>)\<lparr>NTMap\<rparr>) =
        cat_FUNCT \<alpha> \<CC> \<DD>\<lparr>Obj\<rparr>"
      by 
        (
          cs_concl
            cs_simp: cat_cs_simps
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )

    show
      "exp_cat_ntcf \<alpha> \<DD> (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<HH>)\<lparr>NTMap\<rparr> =
        (exp_cat_cf \<alpha> \<DD> \<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_cat_ntcf \<alpha> \<DD> \<NN>)\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs cat_FUNCT_components(1))
      fix \<KK> assume prems: "\<KK> \<in>\<^sub>\<circ> cf_maps \<alpha> \<CC> \<DD>"
      then obtain \<KK>' where \<KK>_def: "\<KK> = cf_map \<KK>'" and \<KK>': "\<KK>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
        by (auto intro: is_arrI)
      from \<alpha>\<beta> assms prems \<KK>' show
        "exp_cat_ntcf \<alpha> \<DD> (\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<HH>)\<lparr>NTMap\<rparr>\<lparr>\<KK>\<rparr> = 
          (exp_cat_cf \<alpha> \<DD> \<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_cat_ntcf \<alpha> \<DD> \<NN>)\<lparr>NTMap\<rparr>\<lparr>\<KK>\<rparr>"
        unfolding \<KK>_def
        by
          (
            cs_concl
              cs_simp:
                cf_ntcf_comp_ntcf_cf_comp_assoc cat_cs_simps cat_FUNCT_cs_simps 
              cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
          )
    qed (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
  qed
    (
      cs_concl
        cs_simp: exp_cat_cf_cf_comp cat_cs_simps cat_FUNCT_cs_simps
        cs_intro: \<alpha>\<beta> cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
    )+

qed

lemma exp_cat_ntcf_cf_ntcf_comp: 
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "category \<alpha> \<DD>"
  shows
    "exp_cat_ntcf \<alpha> \<DD> (\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) =
      exp_cat_ntcf \<alpha> \<DD> \<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<DD> \<HH>"
proof-

  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<HH>: is_functor \<alpha> \<BB> \<CC> \<HH> by (rule assms(2))
  interpret \<DD>: category \<alpha> \<DD> by (rule assms(3))

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    by (simp_all add: \<beta>_def \<NN>.\<Z>_Limit_\<alpha>\<omega> \<NN>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<NN>.\<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 

  show ?thesis
  proof(rule ntcf_eqI)

    from \<alpha>\<beta> have dom_lhs:
      "\<D>\<^sub>\<circ> (exp_cat_ntcf \<alpha> \<DD> (\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>) = cat_FUNCT \<alpha> \<CC> \<DD>\<lparr>Obj\<rparr>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from \<alpha>\<beta> have dom_rhs: 
      "\<D>\<^sub>\<circ> ((exp_cat_ntcf \<alpha> \<DD> \<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<DD> \<HH>)\<lparr>NTMap\<rparr>) =
        cat_FUNCT \<alpha> \<CC> \<DD>\<lparr>Obj\<rparr>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )

    show
      "exp_cat_ntcf \<alpha> \<DD> (\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr> =
        (exp_cat_ntcf \<alpha> \<DD> \<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<DD> \<HH>)\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs cat_FUNCT_components(1))
      fix \<KK> assume prems: "\<KK> \<in>\<^sub>\<circ> cf_maps \<alpha> \<CC> \<DD>"
      then obtain \<KK>' where \<KK>_def: "\<KK> = cf_map \<KK>'" and \<KK>': "\<KK>' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
        by (auto intro: is_arrI)
      from assms \<alpha>\<beta> prems \<KK>' show
        "exp_cat_ntcf \<alpha> \<DD> (\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>\<KK>\<rparr> =
          (exp_cat_ntcf \<alpha> \<DD> \<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<DD> \<HH>)\<lparr>NTMap\<rparr>\<lparr>\<KK>\<rparr>"
        by 
          (
            cs_concl 
              cs_simp: 
                cf_comp_cf_ntcf_comp_assoc cat_cs_simps cat_FUNCT_cs_simps \<KK>_def
              cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
          )
    qed (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)

  qed
    (
      cs_concl
        cs_simp: exp_cat_cf_cf_comp cat_cs_simps cat_FUNCT_cs_simps
        cs_intro: \<alpha>\<beta> cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
    )+

qed

lemma exp_cat_ntcf_ntcf_vcomp:
  assumes "category \<alpha> \<AA>" 
    and "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows
    "exp_cat_ntcf \<alpha> \<AA> (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) =
      exp_cat_ntcf \<alpha> \<AA> \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_cat_ntcf \<alpha> \<AA> \<NN>"
proof-

  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<MM>: is_ntcf \<alpha> \<BB> \<CC> \<GG> \<HH> \<MM> by (rule assms(2))
  interpret \<NN>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<NN> by (rule assms(3))

  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have \<beta>: "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    by (simp_all add: \<beta>_def \<AA>.\<Z>_Limit_\<alpha>\<omega> \<AA>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<AA>.\<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 

  show ?thesis
  proof(rule ntcf_eqI)
    from \<beta> \<alpha>\<beta> show
      "exp_cat_ntcf \<alpha> \<AA> (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>) :
        exp_cat_cf \<alpha> \<AA> \<FF> \<mapsto>\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<AA> \<HH> :
        cat_FUNCT \<alpha> \<CC> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<BB> \<AA>"
      by
        (
          cs_concl cs_intro: 
            cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from \<alpha>\<beta> show
      "exp_cat_ntcf \<alpha> \<AA> \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_cat_ntcf \<alpha> \<AA> \<NN> :
        exp_cat_cf \<alpha> \<AA> \<FF> \<mapsto>\<^sub>C\<^sub>F exp_cat_cf \<alpha> \<AA> \<HH> :
        cat_FUNCT \<alpha> \<CC> \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<BB> \<AA>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from \<alpha>\<beta> have dom_lhs: 
      "\<D>\<^sub>\<circ> ((exp_cat_ntcf \<alpha> \<AA> (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>))\<lparr>NTMap\<rparr>) = cat_FUNCT \<alpha> \<CC> \<AA>\<lparr>Obj\<rparr>"
      by 
        (
          cs_concl
            cs_simp: cat_cs_simps
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )
    from \<alpha>\<beta> have dom_rhs:
      "\<D>\<^sub>\<circ> ((exp_cat_ntcf \<alpha> \<AA> \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_cat_ntcf \<alpha> \<AA> \<NN>)\<lparr>NTMap\<rparr>) =
        cat_FUNCT \<alpha> \<CC> \<AA>\<lparr>Obj\<rparr>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        )

    show 
      "exp_cat_ntcf \<alpha> \<AA> (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr> =
        (exp_cat_ntcf \<alpha> \<AA> \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_cat_ntcf \<alpha> \<AA> \<NN>)\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs cat_FUNCT_components(1))
      fix \<FF>' assume "\<FF>' \<in>\<^sub>\<circ> cf_maps \<alpha> \<CC> \<AA>"
      then obtain \<FF>'' 
        where \<FF>'_def: "\<FF>' = cf_map \<FF>''" and \<FF>'': "\<FF>'' : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
        by clarsimp
      from \<FF>'' \<alpha>\<beta> show
        "exp_cat_ntcf \<alpha> \<AA> (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>\<lparr>\<FF>'\<rparr> =
          (exp_cat_ntcf \<alpha> \<AA> \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F exp_cat_ntcf \<alpha> \<AA> \<NN>)\<lparr>NTMap\<rparr>\<lparr>\<FF>'\<rparr>"
        by
          (
            cs_concl
              cs_simp:
                cat_cs_simps cat_FUNCT_cs_simps cf_ntcf_comp_ntcf_vcomp \<FF>'_def
              cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
          )
    qed (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)+

  qed simp_all

qed

text\<open>\newpage\<close>

end