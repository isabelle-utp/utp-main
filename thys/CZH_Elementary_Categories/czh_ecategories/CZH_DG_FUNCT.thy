(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>FUNCT\<close> and \<open>Funct\<close> as digraphs\label{sec:dg_FUNCT}\<close>
theory CZH_DG_FUNCT
  imports 
    CZH_ECAT_Small_NTCF
    CZH_Foundations.CZH_DG_Subdigraph
begin



subsection\<open>Background\<close>


text\<open>
A general reference for this section is Chapter II-4 in 
\cite{mac_lane_categories_2010}.
\<close>

named_theorems dg_FUNCT_cs_simps
named_theorems dg_FUNCT_cs_intros
named_theorems cat_map_cs_simps
named_theorems cat_map_cs_intros



subsection\<open>Functor map\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition cf_map :: "V \<Rightarrow> V"
  where "cf_map \<FF> = [\<FF>\<lparr>ObjMap\<rparr>, \<FF>\<lparr>ArrMap\<rparr>]\<^sub>\<circ>"

abbreviation cf_maps :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_maps \<alpha> \<AA> \<BB> \<equiv> set {cf_map \<FF> | \<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation tm_cf_maps :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "tm_cf_maps \<alpha> \<AA> \<BB> \<equiv> set {cf_map \<FF> | \<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"

lemma tm_cf_maps_subset_cf_maps:
  "{cf_map \<FF> | \<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq> {cf_map \<FF> | \<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"
  by auto


text\<open>Components.\<close>

lemma cf_map_components[cat_map_cs_simps]:
  shows "cf_map \<FF>\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>"
    and "cf_map \<FF>\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
  unfolding cf_map_def dghm_field_simps by (simp_all add: nat_omega_simps)


text\<open>Sequence characterization.\<close>

lemma dg_FUNCT_Obj_components:
  shows "[FOM, FAM]\<^sub>\<circ>\<lparr>ObjMap\<rparr> = FOM"
    and "[FOM, FAM]\<^sub>\<circ>\<lparr>ArrMap\<rparr> = FAM"
  unfolding dghm_field_simps by (simp_all add: nat_omega_simps)

lemma cf_map_vfsequence[cat_map_cs_intros]: "vfsequence (cf_map \<FF>)"
  unfolding cf_map_def by auto

lemma cf_map_vdomain[cat_map_cs_simps]: "\<D>\<^sub>\<circ> (cf_map \<FF>) = 2\<^sub>\<nat>"
  unfolding cf_map_def by (simp add: nat_omega_simps)

lemma (in is_functor) cf_map_vsubset_cf: "cf_map \<FF> \<subseteq>\<^sub>\<circ> \<FF>"
  by (unfold cf_map_def, subst (3) cf_def)
    (cs_concl cs_intro: vcons_vsubset' V_cs_intros)


text\<open>Size.\<close>

lemma (in is_functor) cf_map_ObjMap_in_Vset:
  assumes "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "cf_map \<FF>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
  using assms unfolding cf_map_components by (intro cf_ObjMap_in_Vset)

lemma (in is_tm_functor) tm_cf_map_ObjMap_in_Vset: "cf_map \<FF>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  unfolding cf_map_components by (rule tm_cf_ObjMap_in_Vset)

lemma (in is_functor) cf_map_ArrMap_in_Vset:
  assumes "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "cf_map \<FF>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
  using assms unfolding cf_map_components by (intro cf_ArrMap_in_Vset)

lemma (in is_tm_functor) tm_cf_map_ArrMap_in_Vset: "cf_map \<FF>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  unfolding cf_map_components by (rule tm_cf_ArrMap_in_Vset)

lemma (in is_functor) cf_map_in_Vset_4: "cf_map \<FF> \<in>\<^sub>\<circ> Vset (\<alpha> + 4\<^sub>\<nat>)"
proof-
  note [folded VPow_iff, folded Vset_succ[OF Ord_\<alpha>], cat_cs_intros] =
    cf_ObjMap_vsubset_Vset 
    cf_ArrMap_vsubset_Vset
  show ?thesis
    by (subst cf_map_def, succ_of_numeral)
      (
        cs_concl 
          cs_simp: plus_V_succ_right V_cs_simps 
          cs_intro: cat_cs_intros V_cs_intros
      )
qed

lemma (in is_tm_functor) tm_cf_map_in_Vset: "cf_map \<FF> \<in>\<^sub>\<circ> Vset \<alpha>"
  using tm_cf_ObjMap_in_Vset tm_cf_ArrMap_in_Vset unfolding cf_map_def
  by (cs_concl cs_intro: V_cs_intros)

lemma (in is_functor) cf_map_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"  
  shows "cf_map \<FF> \<in>\<^sub>\<circ> Vset \<beta>"
  using assms cf_map_in_Vset_4 cf_map_vsubset_cf  
  by (auto intro!: cf_in_Vset)

lemma cf_maps_subset_Vset:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "{cf_map \<FF> | \<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq> elts (Vset \<beta>)"
proof(intro subsetI, unfold mem_Collect_eq, elim exE conjE)
  fix x \<FF> assume x_def: "x = cf_map \<FF>" and \<FF>: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  interpret is_functor \<alpha> \<AA> \<BB> \<FF> by (rule \<FF>)
  show "x \<in>\<^sub>\<circ> Vset \<beta>" unfolding x_def by (rule cf_map_in_Vset[OF assms])
qed

lemma small_cf_maps[simp]: "small {cf_map \<FF> | \<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(cases \<open>\<Z> \<alpha>\<close>)
  case True
  from is_functor.cf_map_in_Vset show ?thesis
    by (intro down[of _ \<open>Vset (\<alpha> + \<omega>)\<close>])
      (auto simp: True \<Z>.\<Z>_Limit_\<alpha>\<omega> \<Z>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>.intro \<Z>.\<Z>_\<alpha>_\<alpha>\<omega>)
next
  case False
  then have "{cf_map \<FF> | \<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>} = {}" by auto
  then show ?thesis by simp
qed

lemma small_tm_cf_maps[simp]: "small {cf_map \<FF> | \<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"
  by (rule smaller_than_small[OF small_cf_maps tm_cf_maps_subset_cf_maps])

lemma (in \<Z>) cf_maps_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "cf_maps \<alpha> \<AA> \<BB> \<in>\<^sub>\<circ> Vset \<beta>"
proof(rule vsubset_in_VsetI)
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "cf_maps \<alpha> \<AA> \<BB> \<subseteq>\<^sub>\<circ> Vset (\<alpha> + 4\<^sub>\<nat>)"
  proof(intro vsubsetI)
    fix \<FF> assume "\<FF> \<in>\<^sub>\<circ> cf_maps \<alpha> \<AA> \<BB>"
    then obtain \<AA> \<BB> \<FF>' where \<FF>_def: "\<FF> = cf_map \<FF>'" and \<FF>: "\<FF>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
      by auto
    interpret is_functor \<alpha> \<AA> \<BB> \<FF>' using \<FF> by simp
    show "\<FF> \<in>\<^sub>\<circ> Vset (\<alpha> + 4\<^sub>\<nat>)" unfolding \<FF>_def by (rule cf_map_in_Vset_4)
  qed
  from assms(2) show "Vset (\<alpha> + 4\<^sub>\<nat>) \<in>\<^sub>\<circ> Vset \<beta>"
    by (cs_concl cs_intro: V_cs_intros Ord_cs_intros)
qed

lemma (in \<Z>) tm_cf_maps_vsubset_Vset: "tm_cf_maps \<alpha> \<AA> \<BB> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
proof(intro vsubsetI)
  fix \<FF> assume "\<FF> \<in>\<^sub>\<circ> tm_cf_maps \<alpha> \<AA> \<BB>"
  then obtain \<AA> \<BB> \<FF>' 
    where \<FF>_def: "\<FF> = cf_map \<FF>'" and \<FF>: "\<FF>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    by auto
  then show "\<FF> \<in>\<^sub>\<circ> Vset \<alpha>" by (force simp: is_tm_functor.tm_cf_map_in_Vset)
qed


text\<open>Rules.\<close>

lemma (in is_functor) cf_mapsI: "cf_map \<FF> \<in>\<^sub>\<circ> cf_maps \<alpha> \<AA> \<BB>" 
  by (auto intro: cat_cs_intros)

lemma (in is_tm_functor) tm_cf_mapsI: "cf_map \<FF> \<in>\<^sub>\<circ> tm_cf_maps \<alpha> \<AA> \<BB>"
  by (auto intro: cat_small_cs_intros)

lemma (in is_functor) cf_mapsI':
  assumes "\<FF>' = cf_map \<FF>"
  shows "\<FF>' \<in>\<^sub>\<circ> cf_maps \<alpha> \<AA> \<BB>" 
  unfolding assms by (rule cf_mapsI)

lemma (in is_tm_functor) tm_cf_mapsI':
  assumes "\<FF>' = cf_map \<FF>"
  shows "\<FF>' \<in>\<^sub>\<circ> tm_cf_maps \<alpha> \<AA> \<BB>" 
  unfolding assms by (rule tm_cf_mapsI)

lemmas [cat_map_cs_intros] = 
  is_functor.cf_mapsI

lemmas cf_mapsI'[cat_map_cs_intros] = 
  is_functor.cf_mapsI'[rotated]

lemmas [cat_map_cs_intros] = 
  is_tm_functor.tm_cf_mapsI

lemmas tm_cf_mapsI'[cat_map_cs_intros] = 
  is_tm_functor.tm_cf_mapsI'[rotated]

lemma cf_mapsE[elim]:
  assumes "\<FF> \<in>\<^sub>\<circ> cf_maps \<alpha> \<AA> \<BB>"
  obtains \<GG> where "\<FF> = cf_map \<GG>" and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by force

lemma tm_cf_mapsE[elim]:
  assumes "\<FF> \<in>\<^sub>\<circ> tm_cf_maps \<alpha> \<AA> \<BB>"
  obtains \<GG> where "\<FF> = cf_map \<GG>" and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by force


text\<open>The opposite functor map.\<close>

lemma (in is_functor) cf_map_op_cf[cat_op_simps]: "cf_map (op_cf \<FF>) = cf_map \<FF>"
proof(rule vsv_eqI, unfold cat_map_cs_simps)
  show "a \<in>\<^sub>\<circ> 2\<^sub>\<nat> \<Longrightarrow> cf_map (op_cf \<FF>)\<lparr>a\<rparr> = cf_map \<FF>\<lparr>a\<rparr>" for a
    by 
      (
        elim_in_numeral, 
        unfold dghm_field_simps[symmetric] cf_map_components cat_op_simps
      )
      simp_all
qed (auto intro: cat_map_cs_intros)

lemmas [cat_op_simps] = is_functor.cf_map_op_cf


text\<open>Elementary properties.\<close>

lemma tm_cf_maps_vsubset_cf_maps: "tm_cf_maps \<alpha> \<AA> \<BB> \<subseteq>\<^sub>\<circ> cf_maps \<alpha> \<AA> \<BB>"
  using tm_cf_maps_subset_cf_maps by simp

lemma tm_cf_maps_in_cf_maps:
  assumes "\<FF> \<in>\<^sub>\<circ> tm_cf_maps \<alpha> \<AA> \<BB>"
  shows "\<FF> \<in>\<^sub>\<circ> cf_maps \<alpha> \<AA> \<BB>"
  using assms tm_cf_maps_vsubset_cf_maps[of \<alpha> \<AA> \<BB>] by blast

lemma cf_map_inj:
  assumes "cf_map \<FF> = cf_map \<GG>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<FF> = \<GG>"
proof(rule cf_eqI)
  from assms(1) have ObjMap: "cf_map \<FF>\<lparr>ObjMap\<rparr> = cf_map \<GG>\<lparr>ObjMap\<rparr>" 
    and ArrMap: "cf_map \<FF>\<lparr>ArrMap\<rparr> = cf_map \<GG>\<lparr>ArrMap\<rparr>" 
    by auto
  from ObjMap show "\<FF>\<lparr>ObjMap\<rparr> = \<GG>\<lparr>ObjMap\<rparr>" unfolding cf_map_components by simp
  from ArrMap show "\<FF>\<lparr>ArrMap\<rparr> = \<GG>\<lparr>ArrMap\<rparr>" unfolding cf_map_components by simp
qed (auto intro: assms(2,3))

lemma cf_map_eq_iff[cat_map_cs_simps]: 
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "cf_map \<FF> = cf_map \<GG> \<longleftrightarrow> \<FF> = \<GG>"
  using cf_map_inj[OF _ assms] by auto

lemma cf_map_eqI:
  assumes "\<FF> \<in>\<^sub>\<circ> cf_maps \<alpha> \<AA> \<BB>" 
    and "\<GG> \<in>\<^sub>\<circ> cf_maps \<alpha> \<AA> \<BB>"
    and "\<FF>\<lparr>ObjMap\<rparr> = \<GG>\<lparr>ObjMap\<rparr>"
    and "\<FF>\<lparr>ArrMap\<rparr> = \<GG>\<lparr>ArrMap\<rparr>"
  shows "\<FF> = \<GG>"
proof-
  from assms(1) obtain \<FF>' 
    where \<FF>_def: "\<FF> = cf_map \<FF>'" and \<FF>': "\<FF>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by auto
  from assms(2) obtain \<GG>'
    where \<GG>_def: "\<GG> = cf_map \<GG>'" and \<GG>': "\<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by auto
  show ?thesis
  proof(rule vsv_eqI, unfold \<FF>_def \<GG>_def)
    show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (cf_map \<FF>') \<Longrightarrow> cf_map \<FF>'\<lparr>a\<rparr> = cf_map \<GG>'\<lparr>a\<rparr>" for a
      by 
        (
          unfold cf_map_vdomain,
          elim_in_numeral,
          insert assms(3,4),
          unfold \<FF>_def \<GG>_def
        )
        (auto simp: dghm_field_simps)
  qed (auto simp: cat_map_cs_simps intro: cat_map_cs_intros)
qed



subsection\<open>Conversion of a functor map to a functor\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition cf_of_cf_map :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_of_cf_map \<AA> \<BB> \<FF> = [\<FF>\<lparr>ObjMap\<rparr>, \<FF>\<lparr>ArrMap\<rparr>, \<AA>, \<BB>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_of_cf_map_components[cat_map_cs_simps]:
  shows "cf_of_cf_map \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>"
    and "cf_of_cf_map \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
    and "cf_of_cf_map \<AA> \<BB> \<FF>\<lparr>HomDom\<rparr> = \<AA>"
    and "cf_of_cf_map \<AA> \<BB> \<FF>\<lparr>HomCod\<rparr> = \<BB>"
  unfolding cf_of_cf_map_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>The conversion of a functor map to a functor is a functor\<close>

lemma (in is_functor) cf_of_cf_map_is_functor: 
  "cf_of_cf_map \<AA> \<BB> (cf_map \<FF>) : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
proof(rule is_functorI')
  show "vfsequence (cf_of_cf_map \<AA> \<BB> (cf_map \<FF>))"
    unfolding cf_of_cf_map_def by simp
  show "vcard (cf_of_cf_map \<AA> \<BB> (cf_map \<FF>)) = 4\<^sub>\<nat>"
    unfolding cf_of_cf_map_def by (simp add: nat_omega_simps)
  show
    "cf_of_cf_map \<AA> \<BB> (cf_map \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> :
      cf_of_cf_map \<AA> \<BB> (cf_map \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub>
      cf_of_cf_map \<AA> \<BB> (cf_map \<FF>)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    if "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" for a b f 
    unfolding cf_of_cf_map_components cf_map_components
    using is_functor_axioms that 
    by (cs_concl cs_intro: cat_cs_intros)
  show 
    "cf_of_cf_map \<AA> \<BB> (cf_map \<FF>)\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f\<rparr> =
      cf_of_cf_map \<AA> \<BB> (cf_map \<FF>)\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub>
      cf_of_cf_map \<AA> \<BB> (cf_map \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
    if "g : b \<mapsto>\<^bsub>\<AA>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" for b c g a f
    using is_functor_axioms that 
    unfolding cf_of_cf_map_components cf_map_components
    by (cs_concl cs_simp: cat_cs_simps)
  show 
    "cf_of_cf_map \<AA> \<BB> (cf_map \<FF>)\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = 
      \<BB>\<lparr>CId\<rparr>\<lparr>cf_of_cf_map \<AA> \<BB> (cf_map \<FF>)\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
    if "c \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" for c
    using is_functor_axioms that 
    unfolding cf_of_cf_map_components cf_map_components
    by (cs_concl cs_simp: cat_cs_simps)
qed 
  (
    auto simp: 
      cat_cs_simps 
      cf_of_cf_map_components 
      cf_map_components 
      cf_ObjMap_vrange
      intro: cat_cs_intros
  )

lemma (in is_functor) cf_of_cf_map_is_functor': 
  assumes "\<FF>' = cf_map \<FF>"
    and "\<AA>' = \<AA>"
    and "\<BB>' = \<BB>"
  shows "cf_of_cf_map \<AA> \<BB> \<FF>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule cf_of_cf_map_is_functor)

lemmas [cat_map_cs_intros] = is_functor.cf_of_cf_map_is_functor'


subsubsection\<open>The value of the conversion of a functor map to a functor\<close>

lemma (in is_functor) cf_of_cf_map_of_cf_map[cat_map_cs_simps]:
  "cf_of_cf_map \<AA> \<BB> (cf_map \<FF>) = \<FF>"
proof(rule cf_eqI)
  show "cf_of_cf_map \<AA> \<BB> (cf_map \<FF>) : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  proof(rule is_functorI')
    show "vfsequence (cf_of_cf_map \<AA> \<BB> (cf_map \<FF>))"
      unfolding cf_of_cf_map_def by auto
    show "vcard (cf_of_cf_map \<AA> \<BB> (cf_map \<FF>)) = 4\<^sub>\<nat>"
      unfolding cf_of_cf_map_def by (simp add: nat_omega_simps)
    show
      "cf_of_cf_map \<AA> \<BB> (cf_map \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> :
        cf_of_cf_map \<AA> \<BB> (cf_map \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub>
        cf_of_cf_map \<AA> \<BB> (cf_map \<FF>)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      if "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" for a b f 
      unfolding cf_of_cf_map_components cf_map_components
      using is_functor_axioms that 
      by (cs_concl cs_intro: cat_cs_intros)
    show 
      "cf_of_cf_map \<AA> \<BB> (cf_map \<FF>)\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f\<rparr> =
        cf_of_cf_map \<AA> \<BB> (cf_map \<FF>)\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub>
        cf_of_cf_map \<AA> \<BB> (cf_map \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      if "g : b \<mapsto>\<^bsub>\<AA>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" for b c g a f
      unfolding cf_of_cf_map_components cf_map_components
      using is_functor_axioms that 
      by (cs_concl cs_simp: cat_cs_simps)
    show 
      "cf_of_cf_map \<AA> \<BB> (cf_map \<FF>)\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> =
        \<BB>\<lparr>CId\<rparr>\<lparr>cf_of_cf_map \<AA> \<BB> (cf_map \<FF>)\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
      if "c \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" for c
      unfolding cf_of_cf_map_components cf_map_components
      using is_functor_axioms that 
      by (cs_concl cs_simp: cat_cs_simps)
  qed 
    (
      auto simp: 
        cat_cs_simps 
        cf_of_cf_map_components 
        cf_map_components 
        cf_ObjMap_vrange 
        intro: cat_cs_intros
    )
qed (auto simp: cf_of_cf_map_components cf_map_components intro: cat_cs_intros)

lemmas [cat_map_cs_simps] = is_functor.cf_of_cf_map_of_cf_map



subsection\<open>Natural transformation arrow\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition ntcf_arrow :: "V \<Rightarrow> V"
  where "ntcf_arrow \<NN> = [\<NN>\<lparr>NTMap\<rparr>, cf_map (\<NN>\<lparr>NTDom\<rparr>), cf_map (\<NN>\<lparr>NTCod\<rparr>)]\<^sub>\<circ>"

abbreviation ntcf_arrows :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_arrows \<alpha> \<AA> \<BB> \<equiv>
    set {ntcf_arrow \<NN> | \<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation tm_ntcf_arrows :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "tm_ntcf_arrows \<alpha> \<AA> \<BB> \<equiv>
    set {ntcf_arrow \<NN> | \<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"

lemma tm_ntcf_arrows_subset_ntcf_arrows:
  "{ntcf_arrow \<NN> | \<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq>
    {ntcf_arrow \<NN> | \<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"
  by auto


text\<open>Components.\<close>

lemma ntcf_arrow_components:
  shows [cat_map_cs_simps]: "ntcf_arrow \<NN>\<lparr>NTMap\<rparr> = \<NN>\<lparr>NTMap\<rparr>"
    and "ntcf_arrow \<NN>\<lparr>NTDom\<rparr> = cf_map (\<NN>\<lparr>NTDom\<rparr>)"
    and "ntcf_arrow \<NN>\<lparr>NTCod\<rparr> = cf_map (\<NN>\<lparr>NTCod\<rparr>)"
  unfolding ntcf_arrow_def nt_field_simps by (simp_all add: nat_omega_simps)

lemma (in is_ntcf) ntcf_arrow_components':
  shows "ntcf_arrow \<NN>\<lparr>NTMap\<rparr> = \<NN>\<lparr>NTMap\<rparr>"
    and "ntcf_arrow \<NN>\<lparr>NTDom\<rparr> = cf_map \<FF>"
    and "ntcf_arrow \<NN>\<lparr>NTCod\<rparr> = cf_map \<GG>"
  unfolding ntcf_arrow_components ntcf_NTDom ntcf_NTCod by simp_all

lemmas [cat_map_cs_simps] = is_ntcf.ntcf_arrow_components'(2,3)


text\<open>Elementary properties.\<close>

lemma dg_FUNCT_Arr_components:
  shows "[NTM, NTD, NTC]\<^sub>\<circ>\<lparr>NTMap\<rparr> = NTM"
    and "[NTM, NTD, NTC]\<^sub>\<circ>\<lparr>NTDom\<rparr> = NTD"
    and "[NTM, NTD, NTC]\<^sub>\<circ>\<lparr>NTCod\<rparr> = NTC"
  unfolding nt_field_simps by (simp_all add: nat_omega_simps)

lemma ntcf_arrow_vfsequence[cat_map_cs_intros]: "vfsequence (ntcf_arrow \<NN>)"
  unfolding ntcf_arrow_def by simp

lemma ntcf_arrow_vdomain[cat_map_cs_simps]: "\<D>\<^sub>\<circ> (ntcf_arrow \<NN>) = 3\<^sub>\<nat>"
  unfolding ntcf_arrow_def by (simp add: nat_omega_simps)


text\<open>Size.\<close>

lemma (in is_ntcf) ntcf_arrow_NTMap_in_Vset:
  assumes "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "ntcf_arrow \<NN>\<lparr>NTMap\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
  using assms unfolding ntcf_arrow_components by (intro ntcf_NTMap_in_Vset)

lemma (in is_tm_ntcf) tm_ntcf_arrow_NTMap_in_Vset:
  "ntcf_arrow \<NN>\<lparr>NTMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  unfolding ntcf_arrow_components by (rule tm_ntcf_NTMap_in_Vset)

lemma (in is_ntcf) ntcf_arrow_NTDom_in_Vset:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "ntcf_arrow \<NN>\<lparr>NTDom\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
  using assms unfolding ntcf_arrow_components' by (rule NTDom.cf_map_in_Vset)

lemma (in is_tm_ntcf) tm_ntcf_arrow_NTDom_in_Vset: 
  "ntcf_arrow \<NN>\<lparr>NTDom\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  unfolding ntcf_arrow_components' by (rule NTDom.tm_cf_map_in_Vset)

lemma (in is_ntcf) ntcf_arrow_NTCod_in_Vset:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "ntcf_arrow \<NN>\<lparr>NTCod\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
  using assms unfolding ntcf_arrow_components' by (rule NTCod.cf_map_in_Vset)

lemma (in is_tm_ntcf) tm_ntcf_arrow_NTCod_in_Vset: 
  "ntcf_arrow \<NN>\<lparr>NTCod\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  unfolding ntcf_arrow_components' by (rule NTCod.tm_cf_map_in_Vset)

lemma (in is_ntcf) ntcf_arrow_in_Vset:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "ntcf_arrow \<NN> \<in>\<^sub>\<circ> Vset \<beta>"
proof-
  interpret ntcf_arrow: vfsequence \<open>ntcf_arrow \<NN>\<close> 
    by (auto intro: cat_map_cs_intros)
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show ?thesis
  proof(rule vsv.vsv_Limit_vsv_in_VsetI)
    from assms show "\<D>\<^sub>\<circ> (ntcf_arrow \<NN>) \<in>\<^sub>\<circ> Vset \<beta>" 
      by (auto simp: cat_map_cs_simps)
    have "n \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (ntcf_arrow \<NN>) \<Longrightarrow> ntcf_arrow \<NN>\<lparr>n\<rparr> \<in>\<^sub>\<circ> Vset \<beta>" for n
      by
        (
          unfold ntcf_arrow_vdomain,
          elim_in_numeral, 
          all\<open>rewrite in "\<hole> \<in>\<^sub>\<circ> _" nt_field_simps[symmetric]\<close>, 
          insert assms,
          unfold ntcf_arrow_components'
        )
        (
          auto intro: 
            ntcf_NTMap_in_Vset NTDom.cf_map_in_Vset NTCod.cf_map_in_Vset
        )
    with ntcf_arrow.vsv_vrange_vsubset show "\<R>\<^sub>\<circ> (ntcf_arrow \<NN>) \<subseteq>\<^sub>\<circ> Vset \<beta>"  
      by simp
  qed (auto simp: cat_map_cs_simps)
qed

lemma (in is_tm_ntcf) tm_ntcf_arrow_in_Vset: "ntcf_arrow \<NN> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  interpret tm_ntcf_arrow: vfsequence \<open>ntcf_arrow \<NN>\<close> 
    by (auto intro: cat_map_cs_intros)
  show ?thesis
  proof(rule vsv.vsv_Limit_vsv_in_VsetI)
    have "n \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (ntcf_arrow \<NN>) \<Longrightarrow> ntcf_arrow \<NN>\<lparr>n\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" for n
      by 
        (
          unfold ntcf_arrow_vdomain,
          elim_in_numeral, 
          all\<open>rewrite in "\<hole> \<in>\<^sub>\<circ> _" nt_field_simps[symmetric]\<close>
        )
        (
          intro tm_ntcf_arrow_NTMap_in_Vset
          tm_ntcf_arrow_NTDom_in_Vset
          tm_ntcf_arrow_NTCod_in_Vset
        )+
    with tm_ntcf_arrow.vsv_vrange_vsubset show "\<R>\<^sub>\<circ> (ntcf_arrow \<NN>) \<subseteq>\<^sub>\<circ> Vset \<alpha>"  
      by auto
  qed (auto simp: cat_map_cs_simps)
qed

lemma ntcf_arrows_subset_Vset:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows 
    "{ntcf_arrow \<NN> | \<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq> elts (Vset \<beta>)"
proof(intro subsetI, unfold mem_Collect_eq, elim exE conjE)
  fix x \<NN> \<FF> \<GG> assume x_def: "x = ntcf_arrow \<NN>" 
    and \<NN>: "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  interpret is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>  by (rule \<NN>)
  show "x \<in>\<^sub>\<circ> Vset \<beta>" unfolding x_def by (rule ntcf_arrow_in_Vset[OF assms])
qed

lemma tm_ntcf_arrows_subset_Vset:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows 
    "{ntcf_arrow \<NN> | \<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq>
      elts (Vset \<beta>)"
proof(intro subsetI, unfold mem_Collect_eq, elim exE conjE)
  fix x \<NN> \<FF> \<GG> assume x_def: "x = ntcf_arrow \<NN>" 
    and \<NN>: "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  interpret is_tm_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>  by (rule \<NN>)
  show "x \<in>\<^sub>\<circ> Vset \<beta>" unfolding x_def by (rule ntcf_arrow_in_Vset[OF assms])
qed

lemma small_ntcf_arrows[simp]: 
  "small {ntcf_arrow \<NN> | \<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(cases \<open>\<Z> \<alpha>\<close>)
  case True
  from is_ntcf.ntcf_arrow_in_Vset show ?thesis
    by (intro down[of _ \<open>Vset (\<alpha> + \<omega>)\<close>])
      (auto simp: True \<Z>.\<Z>_Limit_\<alpha>\<omega> \<Z>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>.intro \<Z>.\<Z>_\<alpha>_\<alpha>\<omega>)
next
  case False
  then have "{ntcf_arrow \<NN> | \<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>} = {}" 
    by auto
  then show ?thesis by simp
qed

lemma small_tm_ntcf_arrows[simp]: 
  "small {ntcf_arrow \<NN> | \<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"
  by 
    ( 
      rule smaller_than_small[
        OF small_ntcf_arrows tm_ntcf_arrows_subset_ntcf_arrows
        ]
    )

lemma (in is_ntcf) ntcf_arrow_in_Vset_7: "ntcf_arrow \<NN> \<in>\<^sub>\<circ> Vset (\<alpha> + 7\<^sub>\<nat>)"
proof-
  note [folded VPow_iff, folded Vset_succ[OF Ord_\<alpha>], cat_cs_intros] =
    ntcf_NTMap_vsubset_Vset 
  from NTDom.cf_map_in_Vset_4 have [cat_cs_intros]:
    "cf_map \<FF> \<in>\<^sub>\<circ> Vset (succ (succ (succ (succ \<alpha>))))"
    by succ_of_numeral (cs_prems cs_simp: plus_V_succ_right V_cs_simps)
  from NTCod.cf_map_in_Vset_4 have [cat_cs_intros]:
    "cf_map \<GG> \<in>\<^sub>\<circ> Vset (succ (succ (succ (succ \<alpha>))))"
    by succ_of_numeral (cs_prems cs_simp: plus_V_succ_right V_cs_simps)
  show ?thesis
    by (subst ntcf_arrow_def, succ_of_numeral, unfold cat_cs_simps)
      (
        cs_concl 
          cs_simp: plus_V_succ_right V_cs_simps 
          cs_intro: V_cs_intros cat_cs_intros
      )
qed

lemma (in \<Z>) ntcf_arrows_in_Vset:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "ntcf_arrows \<alpha> \<AA> \<BB> \<in>\<^sub>\<circ> Vset \<beta>"
proof(rule vsubset_in_VsetI)
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "ntcf_arrows \<alpha> \<AA> \<BB> \<subseteq>\<^sub>\<circ> Vset (\<alpha> + 7\<^sub>\<nat>)"
  proof(intro vsubsetI)
    fix \<NN> assume "\<NN> \<in>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>"
    then obtain \<NN>' \<FF> \<GG> 
      where \<NN>_def: "\<NN> = ntcf_arrow \<NN>'" 
        and \<NN>': "\<NN>' : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      by clarsimp
    interpret is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>' using \<NN>' by simp
    show "\<NN> \<in>\<^sub>\<circ> Vset (\<alpha> + 7\<^sub>\<nat>)" unfolding \<NN>_def by (rule ntcf_arrow_in_Vset_7)
  qed
  from assms(2) show "Vset (\<alpha> + 7\<^sub>\<nat>) \<in>\<^sub>\<circ> Vset \<beta>"
    by (cs_concl cs_intro: V_cs_intros Ord_cs_intros)
qed
  
lemma (in \<Z>) tm_ntcf_arrows_vsubset_Vset: "tm_ntcf_arrows \<alpha> \<AA> \<BB> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  by (clarsimp simp: is_tm_ntcf.tm_ntcf_arrow_in_Vset)


text\<open>Rules.\<close>

lemma (in is_ntcf) ntcf_arrowsI: "ntcf_arrow \<NN> \<in>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>"
  using is_ntcf_axioms by auto

lemma (in is_tm_ntcf) tm_ntcf_arrowsI: "ntcf_arrow \<NN> \<in>\<^sub>\<circ> tm_ntcf_arrows \<alpha> \<AA> \<BB>"
  using is_ntcf_axioms by (auto intro: cat_small_cs_intros)

lemma (in is_ntcf) ntcf_arrowsI': 
  assumes "\<NN>' = ntcf_arrow \<NN>"
  shows "\<NN>' \<in>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>"
  unfolding assms(1) by (rule ntcf_arrowsI)

lemma (in is_tm_ntcf) tm_ntcf_arrowsI': 
  assumes "\<NN>' = ntcf_arrow \<NN>"
  shows "\<NN>' \<in>\<^sub>\<circ> tm_ntcf_arrows \<alpha> \<AA> \<BB>"
  unfolding assms(1) by (rule tm_ntcf_arrowsI)

lemmas [cat_map_cs_intros] =
  is_ntcf.ntcf_arrowsI

lemmas ntcf_arrowsI'[cat_map_cs_intros] =
  is_ntcf.ntcf_arrowsI'[rotated]

lemmas [cat_map_cs_intros] =
  is_tm_ntcf.tm_ntcf_arrowsI

lemmas tm_ntcf_arrowsI'[cat_map_cs_intros] =
  is_tm_ntcf.tm_ntcf_arrowsI'[rotated]

lemma ntcf_arrowsE[elim]:
  assumes "\<NN> \<in>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>"
  obtains \<MM> \<FF> \<GG> where "\<NN> = ntcf_arrow \<MM>" and "\<MM> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by auto

lemma tm_ntcf_arrowsE[elim]:
  assumes "\<NN> \<in>\<^sub>\<circ> tm_ntcf_arrows \<alpha> \<AA> \<BB>"
  obtains \<MM> \<FF> \<GG> where "\<NN> = ntcf_arrow \<MM>" 
    and "\<MM> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by auto


text\<open>Elementary properties.\<close>

lemma tm_ntcf_arrows_vsubset_ntcf_arrows: 
  "tm_ntcf_arrows \<alpha> \<AA> \<BB> \<subseteq>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>"
  using tm_ntcf_arrows_subset_ntcf_arrows by auto

lemma tm_ntcf_arrows_in_cf_arrows[cat_map_cs_intros]:
  assumes "\<NN> \<in>\<^sub>\<circ> tm_ntcf_arrows \<alpha> \<AA> \<BB>"
  shows "\<NN> \<in>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>"
  using assms tm_ntcf_arrows_vsubset_ntcf_arrows[of \<alpha> \<AA> \<BB>] by blast

lemma ntcf_arrow_inj:
  assumes "ntcf_arrow \<MM> = ntcf_arrow \<NN>"
    and "\<MM> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<MM> = \<NN>"
proof(rule ntcf_eqI)
  interpret \<MM>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<MM> by (rule assms(2))
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF>' \<GG>' \<NN> by (rule assms(3))
  from assms(1) have NTMap: "ntcf_arrow \<MM>\<lparr>NTMap\<rparr> = ntcf_arrow \<NN>\<lparr>NTMap\<rparr>" 
    and NTDom: "ntcf_arrow \<MM>\<lparr>NTDom\<rparr> = ntcf_arrow \<NN>\<lparr>NTDom\<rparr>"
    and NTCod: "ntcf_arrow \<MM>\<lparr>NTCod\<rparr> = ntcf_arrow \<NN>\<lparr>NTCod\<rparr>"
    by auto
  from NTMap show "\<MM>\<lparr>NTMap\<rparr> = \<NN>\<lparr>NTMap\<rparr>" unfolding ntcf_arrow_components by simp
  from NTDom NTCod show "\<MM>\<lparr>NTDom\<rparr> = \<NN>\<lparr>NTDom\<rparr>" "\<MM>\<lparr>NTCod\<rparr> = \<NN>\<lparr>NTCod\<rparr>" 
    unfolding ntcf_arrow_components cf_map_components
    by 
      (
        auto simp: 
          cat_cs_simps 
          cf_map_eq_iff[OF \<MM>.NTDom.is_functor_axioms \<NN>.NTDom.is_functor_axioms]
          cf_map_eq_iff[OF \<MM>.NTCod.is_functor_axioms \<NN>.NTCod.is_functor_axioms]
      )
  from assms(2,3) show 
    "\<MM> : \<MM>\<lparr>NTDom\<rparr> \<mapsto>\<^sub>C\<^sub>F \<MM>\<lparr>NTCod\<rparr> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    "\<NN> : \<NN>\<lparr>NTDom\<rparr> \<mapsto>\<^sub>C\<^sub>F \<NN>\<lparr>NTCod\<rparr> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (auto simp: cat_cs_simps)
qed auto

lemma ntcf_arrow_eq_iff[cat_map_cs_simps]:
  assumes "\<MM> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<NN> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "ntcf_arrow \<MM> = ntcf_arrow \<NN> \<longleftrightarrow> \<MM> = \<NN>"
  using ntcf_arrow_inj[OF _ assms] by auto

lemma ntcf_arrow_eqI:
  assumes "\<MM> \<in>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>" 
    and "\<NN> \<in>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>"
    and "\<MM>\<lparr>NTMap\<rparr> = \<NN>\<lparr>NTMap\<rparr>"
    and "\<MM>\<lparr>NTDom\<rparr> = \<NN>\<lparr>NTDom\<rparr>"
    and "\<MM>\<lparr>NTCod\<rparr> = \<NN>\<lparr>NTCod\<rparr>"
  shows "\<MM> = \<NN>"
proof-
  from assms(1) obtain \<MM>' \<FF> \<GG>
    where \<MM>_def: "\<MM> = ntcf_arrow \<MM>'" and \<MM>': "\<MM>' : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by auto
  from assms(2) obtain \<NN>' \<FF>' \<GG>'
    where \<NN>_def: "\<NN> = ntcf_arrow \<NN>'" and \<NN>': "\<NN>' : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by auto
  show ?thesis
  proof(rule vsv_eqI, unfold \<MM>_def \<NN>_def)
    show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (ntcf_arrow \<MM>') \<Longrightarrow> ntcf_arrow \<MM>'\<lparr>a\<rparr> = ntcf_arrow \<NN>'\<lparr>a\<rparr>" 
      for a
      by  
        (
          unfold ntcf_arrow_vdomain, 
          elim_in_numeral, 
          insert assms(3-5), 
          unfold \<MM>_def \<NN>_def,
          fold nt_field_simps
        )
        simp_all
  qed (auto intro: cat_map_cs_intros simp: cat_map_cs_simps)
qed



subsection\<open>
Conversion of a natural transformation arrow to a natural transformation
\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition ntcf_of_ntcf_arrow :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_of_ntcf_arrow \<AA> \<BB> \<NN> =
    [
      \<NN>\<lparr>NTMap\<rparr>,
      cf_of_cf_map \<AA> \<BB> (\<NN>\<lparr>NTDom\<rparr>),
      cf_of_cf_map \<AA> \<BB> (\<NN>\<lparr>NTCod\<rparr>),
      \<AA>,
      \<BB>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma ntcf_of_ntcf_arrow_components[cat_map_cs_simps]:
  shows "ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>\<lparr>NTMap\<rparr> = \<NN>\<lparr>NTMap\<rparr>"
    and "ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>\<lparr>NTDom\<rparr> = cf_of_cf_map \<AA> \<BB> (\<NN>\<lparr>NTDom\<rparr>)"
    and "ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>\<lparr>NTCod\<rparr> = cf_of_cf_map \<AA> \<BB> (\<NN>\<lparr>NTCod\<rparr>)"
    and "ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>\<lparr>NTDGDom\<rparr> = \<AA>"
    and "ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>\<lparr>NTDGCod\<rparr> = \<BB>"
  unfolding ntcf_of_ntcf_arrow_def nt_field_simps 
  by (simp_all add: nat_omega_simps)


subsubsection\<open>
The conversion of a natural transformation arrow 
to a natural transformation is a natural transformation
\<close>

lemma (in is_ntcf) ntcf_of_ntcf_arrow_is_ntcf: 
  "ntcf_of_ntcf_arrow \<AA> \<BB> (ntcf_arrow \<NN>) : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
proof(rule is_ntcfI')
  show "vfsequence (ntcf_of_ntcf_arrow \<AA> \<BB> (ntcf_arrow \<NN>))"
    unfolding ntcf_of_ntcf_arrow_def by auto
  show "vcard (ntcf_of_ntcf_arrow \<AA> \<BB> (ntcf_arrow \<NN>)) = 5\<^sub>\<nat>"
    unfolding ntcf_of_ntcf_arrow_def by (simp add: nat_omega_simps)
  show "ntcf_of_ntcf_arrow \<AA> \<BB> (ntcf_arrow \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> :
    \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    if "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" for a
    using is_ntcf_axioms that
    by (cs_concl cs_simp: cat_map_cs_simps cs_intro: cat_cs_intros)
  show "ntcf_of_ntcf_arrow \<AA> \<BB> (ntcf_arrow \<NN>)\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
    \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> ntcf_of_ntcf_arrow \<AA> \<BB> (ntcf_arrow \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
    if "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" for a b f
    using is_ntcf_axioms that
    by 
      (
        cs_concl 
          cs_simp: ntcf_Comp_commute cat_map_cs_simps cs_intro: cat_cs_intros
      )
qed (use is_ntcf_axioms in \<open>auto simp: cat_cs_simps cat_map_cs_simps\<close>)

lemma (in is_ntcf) ntcf_of_ntcf_arrow_is_ntcf': 
  assumes "\<NN>' = ntcf_arrow \<NN>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>' : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule ntcf_of_ntcf_arrow_is_ntcf)

lemmas [cat_map_cs_intros] = is_ntcf.ntcf_of_ntcf_arrow_is_ntcf'


subsubsection\<open>
The composition of the conversion of a natural transformation arrow 
to a natural transformation
\<close>

lemma (in is_ntcf) ntcf_of_ntcf_arrow[cat_map_cs_simps]:
  "ntcf_of_ntcf_arrow \<AA> \<BB> (ntcf_arrow \<NN>) = \<NN>"
  by (rule ntcf_eqI) 
    (auto simp: cat_map_cs_simps intro: cat_cs_intros ntcf_of_ntcf_arrow_is_ntcf)

lemmas [cat_map_cs_simps] = is_ntcf.ntcf_of_ntcf_arrow



subsection\<open>Composition of the natural transformation arrows\<close>

definition ntcf_arrow_vcomp :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_arrow_vcomp \<AA> \<BB> \<MM> \<NN> =
    ntcf_arrow (ntcf_of_ntcf_arrow \<AA> \<BB> \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>)"

syntax "_ntcf_arrow_vcomp" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" 
  (\<open>(_/ \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>_,_\<^esub> _)\<close> [55, 56, 57, 58] 55)
translations "\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>\<AA>,\<BB>\<^esub> \<NN>" \<rightleftharpoons> "CONST ntcf_arrow_vcomp \<AA> \<BB> \<MM> \<NN>"


text\<open>Components.\<close>

lemma (in is_ntcf) ntcf_arrow_vcomp_components:
  "(ntcf_arrow \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>\<AA>,\<BB>\<^esub> ntcf_arrow \<NN>)\<lparr>NTMap\<rparr> = (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTMap\<rparr>"
  "(ntcf_arrow \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>\<AA>,\<BB>\<^esub> ntcf_arrow \<NN>)\<lparr>NTDom\<rparr> = cf_map ((\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)\<lparr>NTDom\<rparr>)"
  "(ntcf_arrow \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>\<AA>,\<BB>\<^esub> ntcf_arrow \<MM>)\<lparr>NTCod\<rparr> = cf_map ((\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<MM>)\<lparr>NTCod\<rparr>)"
  unfolding 
    ntcf_arrow_vcomp_def
    ntsmcf_vcomp_components 
    ntcf_arrow_components 
    ntcf_of_ntcf_arrow_components
  by (simp_all add: cat_cs_simps cat_map_cs_simps)

lemmas [cat_map_cs_simps] = is_ntcf.ntcf_arrow_vcomp_components


text\<open>Elementary properties.\<close>

lemma ntcf_arrow_vcomp_ntcf_vcomp[cat_map_cs_simps]:
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "ntcf_arrow \<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^bsub>\<AA>,\<BB>\<^esub> ntcf_arrow \<NN> = ntcf_arrow (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)"
  by (rule ntcf_arrow_eqI, insert assms)
    (
      cs_concl
        cs_simp: ntcf_arrow_vcomp_def cat_map_cs_simps cat_cs_simps
        cs_intro: cat_map_cs_intros cat_cs_intros
    )+


subsection\<open>Identity natural transformation arrow\<close>

definition ntcf_arrow_id :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_arrow_id \<AA> \<BB> \<FF> = ntcf_arrow (ntcf_id (cf_of_cf_map \<AA> \<BB> \<FF>))"


text\<open>Components.\<close>

lemma (in is_functor) ntcf_arrow_id_components:
  "(ntcf_arrow_id \<AA> \<BB> (cf_map \<FF>))\<lparr>NTMap\<rparr> = ntcf_id \<FF>\<lparr>NTMap\<rparr>"
  "(ntcf_arrow_id \<AA> \<BB> (cf_map \<FF>))\<lparr>NTDom\<rparr> = cf_map (ntcf_id \<FF>\<lparr>NTDom\<rparr>)"
  "(ntcf_arrow_id \<AA> \<BB> (cf_map \<FF>))\<lparr>NTCod\<rparr> = cf_map (ntcf_id \<FF>\<lparr>NTCod\<rparr>)"
  unfolding ntcf_arrow_id_def ntcf_arrow_components 
  by (simp_all add: cat_map_cs_simps)

lemmas [cat_map_cs_simps] = is_functor.ntcf_arrow_id_components


text\<open>Identity natural transformation arrow is a natural transformation arrow.\<close>

lemma ntcf_arrow_id_ntcf_id[cat_map_cs_simps]:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "ntcf_arrow_id \<AA> \<BB> (cf_map \<FF>) = ntcf_arrow (ntcf_id \<FF>)"
  by (rule ntcf_arrow_eqI, insert assms, unfold ntcf_arrow_id_def)
    (
      cs_concl 
        cs_simp: cat_map_cs_simps cat_cs_simps 
        cs_intro: cat_map_cs_intros cat_cs_intros
    )



subsection\<open>\<open>FUNCT\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition dg_FUNCT :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "dg_FUNCT \<alpha> \<AA> \<BB> =
    [
      cf_maps \<alpha> \<AA> \<BB>,
      ntcf_arrows \<alpha> \<AA> \<BB>,
      (\<lambda>\<NN>\<in>\<^sub>\<circ>ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTDom\<rparr>),
      (\<lambda>\<NN>\<in>\<^sub>\<circ>ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTCod\<rparr>)
    ]\<^sub>\<circ>"

lemmas [dg_FUNCT_cs_simps] = cat_map_cs_simps
lemmas [dg_FUNCT_cs_intros] = cat_map_cs_intros


text\<open>Components.\<close>

lemma dg_FUNCT_components: 
  shows "dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr> = cf_maps \<alpha> \<AA> \<BB>"
    and "dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Arr\<rparr> = ntcf_arrows \<alpha> \<AA> \<BB>"
    and "dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Dom\<rparr> = (\<lambda>\<NN>\<in>\<^sub>\<circ>ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTDom\<rparr>)"
    and "dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Cod\<rparr> = (\<lambda>\<NN>\<in>\<^sub>\<circ>ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTCod\<rparr>)"
  unfolding dg_FUNCT_def dg_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Objects\<close>

lemma (in is_functor) dg_FUNCT_ObjI: "cf_map \<FF> \<in>\<^sub>\<circ> dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
  unfolding dg_FUNCT_components by (auto intro: cat_cs_intros)


subsubsection\<open>Domain and codomain\<close>

mk_VLambda dg_FUNCT_components(3)
  |vsv dg_FUNCT_Dom_vsv[dg_FUNCT_cs_intros]|
  |vdomain dg_FUNCT_Dom_vdomain[dg_FUNCT_cs_simps]|

mk_VLambda dg_FUNCT_components(4)
  |vsv dg_FUNCT_Cod_vsv[dg_FUNCT_cs_intros]|
  |vdomain dg_FUNCT_Cod_vdomain[dg_FUNCT_cs_simps]|

lemma (in is_ntcf)
  shows dg_FUNCT_Dom_app: "dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Dom\<rparr>\<lparr>ntcf_arrow \<NN>\<rparr> = cf_map \<FF>"
    and dg_FUNCT_Cod_app: "dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Cod\<rparr>\<lparr>ntcf_arrow \<NN>\<rparr> = cf_map \<GG>"
proof-
  from is_ntcf_axioms show 
    "dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Dom\<rparr>\<lparr>ntcf_arrow \<NN>\<rparr> = cf_map \<FF>"  
    "dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Cod\<rparr>\<lparr>ntcf_arrow \<NN>\<rparr> = cf_map \<GG>"
    unfolding dg_FUNCT_components 
    by (cs_concl cs_simp: dg_FUNCT_cs_simps V_cs_simps cs_intro: dg_FUNCT_cs_intros)+
qed

lemma (in is_ntcf)
  assumes "\<NN>' = ntcf_arrow \<NN>"
  shows dg_FUNCT_Dom_app': "dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Dom\<rparr>\<lparr>\<NN>'\<rparr> = cf_map \<FF>"
    and dg_FUNCT_Cod_app': "dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Cod\<rparr>\<lparr>\<NN>'\<rparr> = cf_map \<GG>"
  unfolding assms by (intro dg_FUNCT_Dom_app dg_FUNCT_Cod_app)+

lemmas [dg_FUNCT_cs_simps] = 
  is_ntcf.dg_FUNCT_Dom_app'
  is_ntcf.dg_FUNCT_Cod_app'

lemma 
  shows dg_FUNCT_Dom_vrange: "\<R>\<^sub>\<circ> (dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
    and dg_FUNCT_Cod_vrange: "\<R>\<^sub>\<circ> (dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
  unfolding dg_FUNCT_components
proof(all\<open>intro vrange_VLambda_vsubset\<close>)
  fix \<NN> assume "\<NN> \<in>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>"
  then obtain \<MM> \<FF> \<GG> where \<NN>_def[dg_FUNCT_cs_simps]: "\<NN> = ntcf_arrow \<MM>" 
    and \<MM>: "\<MM> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by auto
  from \<MM> show "\<NN>\<lparr>NTDom\<rparr> \<in>\<^sub>\<circ> cf_maps \<alpha> \<AA> \<BB>"
    by (cs_concl cs_simp: dg_FUNCT_cs_simps cs_intro: dg_FUNCT_cs_intros cat_cs_intros)
  from \<MM> show "\<NN>\<lparr>NTCod\<rparr> \<in>\<^sub>\<circ> cf_maps \<alpha> \<AA> \<BB>"
    by (cs_concl cs_simp: dg_FUNCT_cs_simps cs_intro: dg_FUNCT_cs_intros cat_cs_intros)
qed


subsubsection\<open>\<open>FUNCT\<close> is a tiny digraph\<close>

lemma (in \<Z>) tiny_digraph_dg_FUNCT:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "tiny_digraph \<beta> (dg_FUNCT \<alpha> \<AA> \<BB>)"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show ?thesis
  proof(intro tiny_digraphI)
    show "vfsequence (dg_FUNCT \<alpha> \<AA> \<BB>)" unfolding dg_FUNCT_def by simp
    show "vcard (dg_FUNCT \<alpha> \<AA> \<BB>) = 4\<^sub>\<nat>"
      unfolding dg_FUNCT_def by (simp add: nat_omega_simps)
    show "\<R>\<^sub>\<circ> (dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
      by (simp add: dg_FUNCT_Dom_vrange dg_FUNCT_Cod_vrange)
    show "\<R>\<^sub>\<circ> (dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
      by (simp add: dg_FUNCT_Dom_vrange dg_FUNCT_Cod_vrange)
    from assms show "dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
      unfolding dg_FUNCT_components(1) by (rule cf_maps_in_Vset)
    show "dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
      unfolding dg_FUNCT_components(2) by (rule ntcf_arrows_in_Vset[OF assms])
  qed (auto simp: dg_FUNCT_cs_simps dg_FUNCT_components(1,2) intro: dg_FUNCT_cs_intros)
qed


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma dg_FUNCT_is_arrI:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "ntcf_arrow \<NN> : cf_map \<FF> \<mapsto>\<^bsub>dg_FUNCT \<alpha> \<AA> \<BB>\<^esub> cf_map \<GG>"
proof(intro is_arrI, unfold dg_FUNCT_components(1,2))
  interpret is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms)
  from assms show "ntcf_arrow \<NN> \<in>\<^sub>\<circ> ntcf_arrows \<alpha> \<AA> \<BB>" by auto
  from assms show 
    "dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Dom\<rparr>\<lparr>ntcf_arrow \<NN>\<rparr> = cf_map \<FF>"
    "dg_FUNCT \<alpha> \<AA> \<BB>\<lparr>Cod\<rparr>\<lparr>ntcf_arrow \<NN>\<rparr> = cf_map \<GG>"
    by (cs_concl cs_simp: dg_FUNCT_cs_simps)+
qed

lemma dg_FUNCT_is_arrI':
  assumes "\<NN>' = ntcf_arrow \<NN>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<FF>' = cf_map \<FF>"
    and "\<GG>' = cf_map \<GG>"
  shows "\<NN>' : \<FF>' \<mapsto>\<^bsub>dg_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<GG>'"
  using assms(2) unfolding assms(1,3,4) by (rule dg_FUNCT_is_arrI)

lemmas [dg_FUNCT_cs_intros] = dg_FUNCT_is_arrI'

lemma dg_FUNCT_is_arrD[dest]:
  assumes "\<NN> : \<FF> \<mapsto>\<^bsub>dg_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<GG>"
  shows "ntcf_of_ntcf_arrow \<AA> \<BB> \<NN> :
    cf_of_cf_map \<AA> \<BB> \<FF> \<mapsto>\<^sub>C\<^sub>F cf_of_cf_map \<AA> \<BB> \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN> = ntcf_arrow (ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>)"
    and "\<FF> = cf_map (cf_of_cf_map \<AA> \<BB> \<FF>)"
    and "\<GG> = cf_map (cf_of_cf_map \<AA> \<BB> \<GG>)"
proof-
  note \<NN> = is_arrD[OF assms, unfolded dg_FUNCT_components(2)]
  obtain \<NN>' \<FF>' \<GG>' where \<NN>_def: "\<NN> = ntcf_arrow \<NN>'"
    and \<NN>': "\<NN>' : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (elim ntcf_arrowsE[OF \<NN>(1)])
  from \<NN>(2) \<NN>' have \<FF>_def: "\<FF> = cf_map \<FF>'"
    by (cs_prems cs_simp: \<NN>_def dg_FUNCT_cs_simps) simp
  from \<NN>(3) \<NN>' have \<GG>_def: "\<GG> = cf_map \<GG>'"
    by (cs_prems cs_simp: \<NN>_def dg_FUNCT_cs_simps) simp
  from \<NN>' have \<NN>'_def: "\<NN>' = ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>"
    unfolding \<NN>_def by (cs_concl cs_simp: dg_FUNCT_cs_simps)
  from \<NN>' have \<FF>'_def: "\<FF>' = cf_of_cf_map \<AA> \<BB> \<FF>"
    and \<GG>'_def: "\<GG>' = cf_of_cf_map \<AA> \<BB> \<GG>"
    unfolding \<FF>_def \<GG>_def 
    by (cs_concl cs_simp: dg_FUNCT_cs_simps cs_intro: cat_cs_intros)+
  from \<NN>' show "ntcf_of_ntcf_arrow \<AA> \<BB> \<NN> :
    cf_of_cf_map \<AA> \<BB> \<FF> \<mapsto>\<^sub>C\<^sub>F cf_of_cf_map \<AA> \<BB> \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN> = ntcf_arrow (ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>)"
    and "\<FF> = cf_map (cf_of_cf_map \<AA> \<BB> \<FF>)"
    and "\<GG> = cf_map (cf_of_cf_map \<AA> \<BB> \<GG>)"
    by (fold \<FF>'_def \<GG>'_def \<NN>'_def \<FF>_def \<GG>_def \<NN>_def) simp_all
qed

lemma dg_FUNCT_is_arrE[elim]:
  assumes "\<NN> : \<FF> \<mapsto>\<^bsub>dg_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<GG>"
  obtains \<NN>' \<FF>' \<GG>' 
    where "\<NN>' : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
      and "\<NN> = ntcf_arrow \<NN>'"
      and "\<FF> = cf_map \<FF>'" 
      and "\<GG> = cf_map \<GG>'"
  using dg_FUNCT_is_arrD[OF assms] by auto



subsection\<open>\<open>Funct\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition dg_Funct :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "dg_Funct \<alpha> \<AA> \<BB> =
    [
      tm_cf_maps \<alpha> \<AA> \<BB>,
      tm_ntcf_arrows \<alpha> \<AA> \<BB>,
      (\<lambda>\<NN>\<in>\<^sub>\<circ>tm_ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTDom\<rparr>),
      (\<lambda>\<NN>\<in>\<^sub>\<circ>tm_ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTCod\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dg_Funct_components: 
  shows "dg_Funct \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr> = tm_cf_maps \<alpha> \<AA> \<BB>"
    and "dg_Funct \<alpha> \<AA> \<BB>\<lparr>Arr\<rparr> = tm_ntcf_arrows \<alpha> \<AA> \<BB>"
    and "dg_Funct \<alpha> \<AA> \<BB>\<lparr>Dom\<rparr> = (\<lambda>\<NN>\<in>\<^sub>\<circ>tm_ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTDom\<rparr>)"
    and "dg_Funct \<alpha> \<AA> \<BB>\<lparr>Cod\<rparr> = (\<lambda>\<NN>\<in>\<^sub>\<circ>tm_ntcf_arrows \<alpha> \<AA> \<BB>. \<NN>\<lparr>NTCod\<rparr>)"
  unfolding dg_Funct_def dg_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Objects\<close>

lemma (in is_tm_functor) dg_Funct_ObjI: "cf_map \<FF> \<in>\<^sub>\<circ> dg_Funct \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
  unfolding dg_Funct_components by (auto simp: cat_small_cs_intros)


subsubsection\<open>Domain and codomain\<close>

mk_VLambda dg_Funct_components(3)
  |vsv dg_Funct_Dom_vsv[dg_FUNCT_cs_intros]|
  |vdomain dg_Funct_Dom_vdomain[dg_FUNCT_cs_simps]|

mk_VLambda dg_Funct_components(4)
  |vsv dg_Funct_Cod_vsv[dg_FUNCT_cs_intros]|
  |vdomain dg_Funct_Cod_vdomain[dg_FUNCT_cs_simps]|

lemma (in is_tm_ntcf)
  shows dg_Funct_Dom_app: "dg_Funct \<alpha> \<AA> \<BB>\<lparr>Dom\<rparr>\<lparr>ntcf_arrow \<NN>\<rparr> = cf_map \<FF>"
    and dg_Funct_Cod_app: "dg_Funct \<alpha> \<AA> \<BB>\<lparr>Cod\<rparr>\<lparr>ntcf_arrow \<NN>\<rparr> = cf_map \<GG>"
proof-
  from is_tm_ntcf_axioms show 
    "dg_Funct \<alpha> \<AA> \<BB>\<lparr>Dom\<rparr>\<lparr>ntcf_arrow \<NN>\<rparr> = cf_map \<FF>"  
    "dg_Funct \<alpha> \<AA> \<BB>\<lparr>Cod\<rparr>\<lparr>ntcf_arrow \<NN>\<rparr> = cf_map \<GG>"
    unfolding dg_Funct_components 
    by 
      (
        cs_concl 
          cs_simp: dg_FUNCT_cs_simps V_cs_simps 
          cs_intro: dg_FUNCT_cs_intros cat_cs_intros
      )+
qed

lemma (in is_tm_ntcf)
  assumes "\<NN>' = ntcf_arrow \<NN>"
  shows dg_Funct_Dom_app': "dg_Funct \<alpha> \<AA> \<BB>\<lparr>Dom\<rparr>\<lparr>\<NN>'\<rparr> = cf_map \<FF>"
    and dg_Funct_Cod_app': "dg_Funct \<alpha> \<AA> \<BB>\<lparr>Cod\<rparr>\<lparr>\<NN>'\<rparr> = cf_map \<GG>"
  unfolding assms by (intro dg_Funct_Dom_app dg_Funct_Cod_app)+

lemmas [dg_FUNCT_cs_simps] = 
  is_tm_ntcf.dg_Funct_Dom_app'
  is_tm_ntcf.dg_Funct_Cod_app'

lemma 
  shows dg_Funct_Dom_vrange: "\<R>\<^sub>\<circ> (dg_Funct \<alpha> \<AA> \<BB>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> dg_Funct \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
    and dg_Funct_Cod_vrange: "\<R>\<^sub>\<circ> (dg_Funct \<alpha> \<AA> \<BB>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> dg_Funct \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
  unfolding dg_Funct_components
proof(all\<open>intro vrange_VLambda_vsubset\<close>)
  fix \<NN> assume "\<NN> \<in>\<^sub>\<circ> tm_ntcf_arrows \<alpha> \<AA> \<BB>"
  then obtain \<MM> \<FF> \<GG> where \<NN>_def[dg_FUNCT_cs_simps]: "\<NN> = ntcf_arrow \<MM>" 
    and \<MM>: "\<MM> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    by auto
  from \<MM> show "\<NN>\<lparr>NTDom\<rparr> \<in>\<^sub>\<circ> tm_cf_maps \<alpha> \<AA> \<BB>"
    by 
      ( 
        cs_concl 
          cs_simp: dg_FUNCT_cs_simps 
          cs_intro: dg_FUNCT_cs_intros cat_small_cs_intros
      )
  from \<MM> show "\<NN>\<lparr>NTCod\<rparr> \<in>\<^sub>\<circ> tm_cf_maps \<alpha> \<AA> \<BB>"
    by 
      (
        cs_concl 
          cs_simp: dg_FUNCT_cs_simps 
          cs_intro: dg_FUNCT_cs_intros cat_small_cs_intros
      )
qed


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma dg_Funct_is_arrI:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "ntcf_arrow \<NN> : cf_map \<FF> \<mapsto>\<^bsub>dg_Funct \<alpha> \<AA> \<BB>\<^esub> cf_map \<GG>"
proof(intro is_arrI, unfold dg_Funct_components(1,2))
  interpret is_tm_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms)
  from assms show "ntcf_arrow \<NN> \<in>\<^sub>\<circ> tm_ntcf_arrows \<alpha> \<AA> \<BB>" by auto
  from assms show 
    "dg_Funct \<alpha> \<AA> \<BB>\<lparr>Dom\<rparr>\<lparr>ntcf_arrow \<NN>\<rparr> = cf_map \<FF>"
    "dg_Funct \<alpha> \<AA> \<BB>\<lparr>Cod\<rparr>\<lparr>ntcf_arrow \<NN>\<rparr> = cf_map \<GG>"
    by (cs_concl cs_simp: dg_FUNCT_cs_simps)+
qed

lemma dg_Funct_is_arrI':
  assumes "\<NN>' = ntcf_arrow \<NN>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<FF>' = cf_map \<FF>"
    and "\<GG>' = cf_map \<GG>"
  shows "\<NN>' : \<FF>' \<mapsto>\<^bsub>dg_Funct \<alpha> \<AA> \<BB>\<^esub> \<GG>'"
  using assms(2) unfolding assms(1,3,4) by (rule dg_Funct_is_arrI)

lemmas [dg_FUNCT_cs_intros] = dg_Funct_is_arrI'

lemma dg_Funct_is_arrD[dest]:
  assumes "\<NN> : \<FF> \<mapsto>\<^bsub>dg_Funct \<alpha> \<AA> \<BB>\<^esub> \<GG>"
  shows "ntcf_of_ntcf_arrow \<AA> \<BB> \<NN> :
    cf_of_cf_map \<AA> \<BB> \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m cf_of_cf_map \<AA> \<BB> \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN> = ntcf_arrow (ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>)"
    and "\<FF> = cf_map (cf_of_cf_map \<AA> \<BB> \<FF>)"
    and "\<GG> = cf_map (cf_of_cf_map \<AA> \<BB> \<GG>)"
proof-
  note \<NN> = is_arrD[OF assms, unfolded dg_Funct_components(2)]
  obtain \<NN>' \<FF>' \<GG>' where \<NN>_def: "\<NN> = ntcf_arrow \<NN>'"
    and \<NN>': "\<NN>' : \<FF>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    by (elim tm_ntcf_arrowsE[OF \<NN>(1)])
  from \<NN>(2) \<NN>' have \<FF>_def: "\<FF> = cf_map \<FF>'"
    by (cs_prems cs_simp: \<NN>_def dg_FUNCT_cs_simps) simp
  from \<NN>(3) \<NN>' have \<GG>_def: "\<GG> = cf_map \<GG>'"
    by (cs_prems cs_simp: \<NN>_def dg_FUNCT_cs_simps) simp
  from \<NN>' have \<NN>'_def: "\<NN>' = ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>"
    unfolding \<NN>_def 
    by 
      (
        cs_concl
          cs_simp: dg_FUNCT_cs_simps cs_intro: cat_small_cs_intros cat_cs_intros
      )
  from \<NN>' have \<FF>'_def: "\<FF>' = cf_of_cf_map \<AA> \<BB> \<FF>"
    and \<GG>'_def: "\<GG>' = cf_of_cf_map \<AA> \<BB> \<GG>"
    unfolding \<FF>_def \<GG>_def 
    by 
      (
        cs_concl 
          cs_simp: dg_FUNCT_cs_simps cs_intro: cat_small_cs_intros cat_cs_intros
      )+
  from \<NN>' show "ntcf_of_ntcf_arrow \<AA> \<BB> \<NN> :
    cf_of_cf_map \<AA> \<BB> \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m cf_of_cf_map \<AA> \<BB> \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN> = ntcf_arrow (ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>)"
    and "\<FF> = cf_map (cf_of_cf_map \<AA> \<BB> \<FF>)"
    and "\<GG> = cf_map (cf_of_cf_map \<AA> \<BB> \<GG>)"
    by (fold \<FF>'_def \<GG>'_def \<NN>'_def \<FF>_def \<GG>_def \<NN>_def) simp_all
qed

lemma dg_Funct_is_arrE[elim]:
  assumes "\<NN> : \<FF> \<mapsto>\<^bsub>dg_Funct \<alpha> \<AA> \<BB>\<^esub> \<GG>"
  obtains \<NN>' \<FF>' \<GG>' where "\<NN>' : \<FF>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN> = ntcf_arrow \<NN>'"
    and "\<FF> = cf_map \<FF>'" 
    and "\<GG> = cf_map \<GG>'"
  using dg_Funct_is_arrD[OF assms] by auto


subsubsection\<open>\<open>Funct\<close> is a digraph\<close>

lemma (in \<Z>) digraph_dg_Funct: 
  assumes "tiny_category \<alpha> \<AA>" and "category \<alpha> \<BB>"
  shows "digraph \<alpha> (dg_Funct \<alpha> \<AA> \<BB>)"
proof(intro digraphI)

  interpret tiny_category \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(2))

  show "vfsequence (dg_Funct \<alpha> \<AA> \<BB>)" unfolding dg_Funct_def by simp
  show "vcard (dg_Funct \<alpha> \<AA> \<BB>) = 4\<^sub>\<nat>"
    unfolding dg_Funct_def by (simp add: nat_omega_simps)
  show "\<R>\<^sub>\<circ> (dg_Funct \<alpha> \<AA> \<BB>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> dg_Funct \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
    by (simp add: dg_Funct_Dom_vrange dg_Funct_Cod_vrange)
  show "\<R>\<^sub>\<circ> (dg_Funct \<alpha> \<AA> \<BB>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> dg_Funct \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
    by (simp add: dg_Funct_Dom_vrange dg_Funct_Cod_vrange)
  show "dg_Funct \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    unfolding dg_Funct_components(1,2) by (rule tm_cf_maps_vsubset_Vset)
  
  have RA: 
    "(\<Union>\<^sub>\<circ>\<FF>\<in>\<^sub>\<circ>A. \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>)) \<in>\<^sub>\<circ> Vset \<alpha>"
    "(\<Union>\<^sub>\<circ>\<FF>\<in>\<^sub>\<circ>A. \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>)) \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    if "A \<subseteq>\<^sub>\<circ> dg_Funct \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>" and "A \<in>\<^sub>\<circ> Vset \<alpha>" for A
  proof-
    have "(\<Union>\<^sub>\<circ>\<FF>\<in>\<^sub>\<circ>A. \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>)) \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
      and "(\<Union>\<^sub>\<circ>\<FF>\<in>\<^sub>\<circ>A. \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>)) \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>A)))))"
    proof(all\<open>intro vsubsetI\<close>)
      fix f assume "f \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>\<FF>\<in>\<^sub>\<circ>A. \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>))"
      then obtain \<FF> where \<FF>: "\<FF> \<in>\<^sub>\<circ> A" and f: "f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>)" by auto
      with that(1) have "\<FF> \<in>\<^sub>\<circ> dg_Funct \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>" by (elim vsubsetE)
      then obtain \<FF>'
        where \<FF>_def: "\<FF> = cf_map \<FF>'" and \<FF>': "\<FF>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
        unfolding dg_Funct_components by auto
      interpret \<FF>': is_tm_functor \<alpha> \<AA> \<BB> \<FF>' by (rule \<FF>')
      from f obtain a where "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<FF>'\<lparr>ObjMap\<rparr>)" and af: "\<langle>a, f\<rangle> \<in>\<^sub>\<circ> \<FF>'\<lparr>ObjMap\<rparr>"
        unfolding \<FF>_def cf_map_components vdomain_iff by force
      then show "f \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
        using \<FF>'.cf_ObjMap_vrange \<FF>_def cf_map_components(1) f vsubsetE by auto
      show "f \<in>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>A)))))"
      proof(intro VUnionI)
        show "\<FF> \<in>\<^sub>\<circ> A" by (rule \<FF>)
        show "set {0, \<FF>\<lparr>ObjMap\<rparr>} \<in>\<^sub>\<circ> \<langle>[]\<^sub>\<circ>, \<FF>\<lparr>ObjMap\<rparr>\<rangle>" unfolding vpair_def by simp
        show "\<langle>a, f\<rangle> \<in>\<^sub>\<circ> \<FF>\<lparr>ObjMap\<rparr>"
          unfolding \<FF>_def cf_map_components by (intro af)
        show "set {a, f} \<in>\<^sub>\<circ> \<langle>a, f\<rangle>" unfolding vpair_def by clarsimp
      qed (clarsimp simp: \<FF>_def cf_map_def dg_FUNCT_Obj_components)+
    qed
    moreover have "\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>A))))) \<in>\<^sub>\<circ> Vset \<alpha>"
      by (intro VUnion_in_VsetI that(2))
    ultimately show 
      "(\<Union>\<^sub>\<circ>\<FF>\<in>\<^sub>\<circ>A. \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>)) \<in>\<^sub>\<circ> Vset \<alpha>" 
      "(\<Union>\<^sub>\<circ>\<FF>\<in>\<^sub>\<circ>A. \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>)) \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
      by blast+
  qed

  fix A B assume prems:
    "A \<subseteq>\<^sub>\<circ> dg_Funct \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
    "B \<subseteq>\<^sub>\<circ> dg_Funct \<alpha> \<AA> \<BB>\<lparr>Obj\<rparr>"
    "A \<in>\<^sub>\<circ> Vset \<alpha>"
    "B \<in>\<^sub>\<circ> Vset \<alpha>"

  define ARs where "ARs = (\<Union>\<^sub>\<circ>\<FF>\<in>\<^sub>\<circ>A. \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>))"
  define BRs where "BRs = (\<Union>\<^sub>\<circ>\<GG>\<in>\<^sub>\<circ>B. \<R>\<^sub>\<circ> (\<GG>\<lparr>ObjMap\<rparr>))"
  define Hom_AB where "Hom_AB = (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>ARs. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>BRs. Hom \<BB> a b)"

  define Q where
    "Q i = (if i = 0 then VPow (\<AA>\<lparr>Obj\<rparr> \<times>\<^sub>\<circ> Hom_AB) else if i = 1\<^sub>\<nat> then A else B)" 
    for i
  have 
    "{[\<NN>, \<FF>, \<GG>]\<^sub>\<circ> |\<NN> \<FF> \<GG>. \<NN> \<subseteq>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<times>\<^sub>\<circ> Hom_AB \<and> \<FF> \<in>\<^sub>\<circ> A \<and> \<GG> \<in>\<^sub>\<circ> B} \<subseteq>
      elts (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i)"
  proof(intro subsetI, unfold mem_Collect_eq, elim exE conjE)
    fix \<NN>\<FF>\<GG> \<NN> \<FF> \<GG> assume prems': 
      "\<NN>\<FF>\<GG> = [\<NN>, \<FF>, \<GG>]\<^sub>\<circ>" "\<NN> \<subseteq>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<times>\<^sub>\<circ> Hom_AB" "\<FF> \<in>\<^sub>\<circ> A" "\<GG> \<in>\<^sub>\<circ> B"
    show "\<NN>\<FF>\<GG> \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i)"
    proof(intro vproductI, unfold Ball_def; (intro allI impI)?)
      show "\<D>\<^sub>\<circ> \<NN>\<FF>\<GG> = set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}"
        by (simp add: three prems'(1) nat_omega_simps)
      fix i assume "i \<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}"
      then consider \<open>i = 0\<close> | \<open>i = 1\<^sub>\<nat>\<close> | \<open>i = 2\<^sub>\<nat>\<close> by auto
      then show "\<NN>\<FF>\<GG>\<lparr>i\<rparr> \<in>\<^sub>\<circ> Q i"
        by cases (auto simp: Q_def prems' nat_omega_simps)
    qed (auto simp: prems'(1))
  qed
  moreover then have small[simp]: 
    "small {[r, a, b]\<^sub>\<circ> | r a b. r \<subseteq>\<^sub>\<circ>\<AA>\<lparr>Obj\<rparr> \<times>\<^sub>\<circ> Hom_AB \<and> a \<in>\<^sub>\<circ> A \<and> b \<in>\<^sub>\<circ> B}"
    by (rule down)
  ultimately have
    "set {[r, a, b]\<^sub>\<circ> |r a b. r \<subseteq>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<times>\<^sub>\<circ> Hom_AB \<and> a \<in>\<^sub>\<circ> A \<and> b \<in>\<^sub>\<circ> B} \<subseteq>\<^sub>\<circ>
      (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i)"
    by auto
  moreover have "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i) \<in>\<^sub>\<circ> Vset \<alpha>"
  proof(rule Limit_vproduct_in_VsetI)
    show "set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>} \<in>\<^sub>\<circ> Vset \<alpha>"
      by (cs_concl cs_intro: V_cs_intros cat_cs_intros cs_simp: V_cs_simps)
    have "Hom_AB \<in>\<^sub>\<circ> Vset \<alpha>"
      unfolding Hom_AB_def
      by 
        (
          intro \<BB>.cat_Hom_vifunion_in_Vset prems(3,4), 
          unfold ARs_def BRs_def; 
          intro RA prems
        )
    moreover have "\<AA>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" by (intro tiny_cat_Obj_in_Vset)
    ultimately have "VPow (\<AA>\<lparr>Obj\<rparr> \<times>\<^sub>\<circ> Hom_AB) \<in>\<^sub>\<circ> Vset \<alpha>"
      by (cs_concl cs_intro: V_cs_intros)
    with prems(3,4) show "Q i \<in>\<^sub>\<circ> Vset \<alpha>" if "i \<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}" for i
      unfolding Q_def by (simp_all add: nat_omega_simps)
  qed auto
  moreover have
    "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom (dg_Funct \<alpha> \<AA> \<BB>) a b) \<subseteq>\<^sub>\<circ>
      set {[r, a, b]\<^sub>\<circ> | r a b. r \<subseteq>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<times>\<^sub>\<circ> Hom_AB \<and> a \<in>\<^sub>\<circ> A \<and> b \<in>\<^sub>\<circ> B}"
  proof(rule vsubsetI)
    fix \<NN> assume "\<NN> \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom (dg_Funct \<alpha> \<AA> \<BB>) a b)"
    then obtain \<FF> \<GG> 
      where \<FF>: "\<FF> \<in>\<^sub>\<circ> A"
        and \<GG>: "\<GG> \<in>\<^sub>\<circ> B"
        and \<NN>_ab: "\<NN> \<in>\<^sub>\<circ> Hom (dg_Funct \<alpha> \<AA> \<BB>) \<FF> \<GG>"
      by auto
    then have "\<NN> : \<FF> \<mapsto>\<^bsub>dg_Funct \<alpha> \<AA> \<BB>\<^esub> \<GG>" by simp
    note \<NN> = dg_Funct_is_arrD[OF this]
    show 
      "\<NN> \<in>\<^sub>\<circ> set {[r, a, b]\<^sub>\<circ> | r a b. r \<subseteq>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<times>\<^sub>\<circ> Hom_AB \<and> a \<in>\<^sub>\<circ> A \<and> b \<in>\<^sub>\<circ> B}"
    proof(intro in_set_CollectI small exI conjI)
      show "\<NN> =
        [
          ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>\<lparr>NTMap\<rparr>,
          cf_map (ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>\<lparr>NTDom\<rparr>),
          cf_map (ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>\<lparr>NTCod\<rparr>)
        ]\<^sub>\<circ>"
        by (rule \<NN>(2)[unfolded ntcf_arrow_def])
      interpret \<NN>: is_tm_ntcf \<alpha> 
        \<AA> \<BB> 
        \<open>cf_of_cf_map \<AA> \<BB> \<FF>\<close> \<open>cf_of_cf_map \<AA> \<BB> \<GG>\<close> 
        \<open>ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>\<close>
        rewrites "ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>\<lparr>NTMap\<rparr> = \<NN>\<lparr>NTMap\<rparr>"
          and "cf_of_cf_map \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>"
          and "cf_of_cf_map \<AA> \<BB> \<GG>\<lparr>ObjMap\<rparr> = \<GG>\<lparr>ObjMap\<rparr>"
        by
          (
            rule \<NN>(1), 
            unfold ntcf_of_ntcf_arrow_components cf_of_cf_map_components
          ) 
          simp_all
      show "ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>\<lparr>NTMap\<rparr> \<subseteq>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<times>\<^sub>\<circ> Hom_AB"
      proof(intro vsubsetI, unfold ntcf_of_ntcf_arrow_components)
        fix af assume prems'': "af \<in>\<^sub>\<circ> \<NN>\<lparr>NTMap\<rparr>"
        then obtain a f where af_def: "af = \<langle>a, f\<rangle>" 
          and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
          and f: "f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>)" 
          by (elim \<NN>.NTMap.vbrelation_vinE)
        from prems'' have f_def: "f = \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>" 
          unfolding af_def \<NN>.NTMap.vsv_ex1_app1[OF a] .
        have \<NN>a: "\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
          by (rule \<NN>.ntcf_NTMap_is_arr[OF a])
        have "f \<in>\<^sub>\<circ> Hom_AB"
          unfolding f_def Hom_AB_def ARs_def BRs_def
        proof(intro vifunionI, unfold in_Hom_iff)
          show "\<FF> \<in>\<^sub>\<circ> A" by (intro \<FF>)
          from a show "\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>)" 
            by (metis \<NN>.NTDom.ObjMap.vdomain_atD \<NN>.NTDom.cf_ObjMap_vdomain)
          show "\<GG> \<in>\<^sub>\<circ> B" by (intro \<GG>)
          from a show "\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<GG>\<lparr>ObjMap\<rparr>)" 
            by (metis \<NN>.NTCod.ObjMap.vdomain_atD \<NN>.NTCod.cf_ObjMap_vdomain)
          show "\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>" by (intro \<NN>a)
        qed
        with a show "af \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<times>\<^sub>\<circ> Hom_AB" unfolding af_def f_def by simp
      qed
      show "cf_map (ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>\<lparr>NTDom\<rparr>) \<in>\<^sub>\<circ> A"
        unfolding \<NN>.ntcf_NTDom \<NN>(3)[symmetric] by (rule \<FF>)
      show "cf_map (ntcf_of_ntcf_arrow \<AA> \<BB> \<NN>\<lparr>NTCod\<rparr>) \<in>\<^sub>\<circ> B"
        unfolding \<NN>.ntcf_NTCod \<NN>(4)[symmetric] by (rule \<GG>)
    qed
  qed
  ultimately show "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom (dg_Funct \<alpha> \<AA> \<BB>) a b) \<in>\<^sub>\<circ> Vset \<alpha>"
    by blast
qed (unfold dg_Funct_components, auto)


subsubsection\<open>\<open>Funct\<close> is a subdigraph of \<open>FUNCT\<close>\<close>

lemma (in \<Z>) subdigraph_dg_Funct_dg_FUNCT:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" and "tiny_category \<alpha> \<AA>" and "category \<alpha> \<BB>"
  shows "dg_Funct \<alpha> \<AA> \<BB> \<subseteq>\<^sub>D\<^sub>G\<^bsub>\<beta>\<^esub> dg_FUNCT \<alpha> \<AA> \<BB>"
proof(intro subdigraphI, unfold dg_FUNCT_components(1) dg_Funct_components(1))
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "digraph \<beta> (dg_Funct \<alpha> \<AA> \<BB>)"
    by (intro digraph.dg_digraph_if_ge_Limit[OF digraph_dg_Funct] assms)
  from assms show "digraph \<beta> (dg_FUNCT \<alpha> \<AA> \<BB>)"    
    by (cs_concl cs_intro: dg_small_cs_intros tiny_digraph_dg_FUNCT)
  show "\<FF> \<in>\<^sub>\<circ> cf_maps \<alpha> \<AA> \<BB>" if "\<FF> \<in>\<^sub>\<circ> tm_cf_maps \<alpha> \<AA> \<BB>" for \<FF>
    using that by (cs_concl cs_intro: dg_FUNCT_cs_intros tm_cf_maps_in_cf_maps)
  show "\<NN> : \<FF> \<mapsto>\<^bsub>dg_FUNCT \<alpha> \<AA> \<BB>\<^esub> \<GG>" if "\<NN> : \<FF> \<mapsto>\<^bsub>dg_Funct \<alpha> \<AA> \<BB>\<^esub> \<GG>" 
    for \<NN> \<FF> \<GG>
  proof-
    note f = dg_Funct_is_arrD[OF that]
    from f(1) show ?thesis
      by (subst f(2), use nothing in \<open>subst f(3), subst f(4)\<close>)
        (cs_concl cs_intro: dg_FUNCT_cs_intros cat_small_cs_intros)
  qed
qed

text\<open>\newpage\<close>

end