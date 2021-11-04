(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Homomorphism of digraphs\<close>
theory CZH_DG_DGHM
  imports CZH_DG_Digraph
begin



subsection\<open>Background\<close>

named_theorems dghm_cs_simps
named_theorems dghm_cs_intros

named_theorems dg_cn_cs_simps
named_theorems dg_cn_cs_intros

named_theorems dghm_field_simps

definition ObjMap :: V where [dghm_field_simps]: "ObjMap = 0"
definition ArrMap :: V where [dghm_field_simps]: "ArrMap = 1\<^sub>\<nat>"
definition HomDom :: V where [dghm_field_simps]: "HomDom = 2\<^sub>\<nat>"
definition HomCod :: V where [dghm_field_simps]: "HomCod = 3\<^sub>\<nat>"



subsection\<open>Definition and elementary properties\<close>


text\<open>
A homomorphism of digraphs, as presented in this work, can be seen as a
generalization of the concept of a functor between categories, as presented in
Chapter I-3 in \cite{mac_lane_categories_2010}, to digraphs. 
The generalization is performed by removing the axioms (1) from the definition.
It is expected that the resulting definition is consistent with the conventional
notion of a homomorphism of digraphs in graph theory, but further details 
are considered to be outside of the scope of this work.

The definition of a digraph homomorphism is parameterized by a limit ordinal
\<open>\<alpha>\<close> such that \<open>\<omega> < \<alpha>\<close>. Such digraph homomorphisms are referred to either as
\<open>\<alpha>\<close>-digraph homomorphisms or homomorphisms of \<open>\<alpha>\<close>-digraphs.

Following \cite{mac_lane_categories_2010}, all digraph homomorphisms are 
covariant (see Chapter II-2). However, a special notation is adapted for the 
digraph homomorphisms from an opposite digraph. Normally, such 
digraph homomorphisms will be referred to as the contravariant digraph 
homomorphisms, but this convention will not be enforced.
\<close>

locale is_dghm = 
  \<Z> \<alpha> + vfsequence \<FF> + HomDom: digraph \<alpha> \<AA> + HomCod: digraph \<alpha> \<BB> 
  for \<alpha> \<AA> \<BB> \<FF> +
  assumes dghm_length[dg_cs_simps]: "vcard \<FF> = 4\<^sub>\<nat>"  
    and dghm_HomDom[dg_cs_simps]: "\<FF>\<lparr>HomDom\<rparr> = \<AA>"
    and dghm_HomCod[dg_cs_simps]: "\<FF>\<lparr>HomCod\<rparr> = \<BB>"
    and dghm_ObjMap_vsv: "vsv (\<FF>\<lparr>ObjMap\<rparr>)"
    and dghm_ArrMap_vsv: "vsv (\<FF>\<lparr>ArrMap\<rparr>)"
    and dghm_ObjMap_vdomain[dg_cs_simps]: "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    and dghm_ObjMap_vrange: "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    and dghm_ArrMap_vdomain[dg_cs_simps]: "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
    and dghm_ArrMap_is_arr: 
      "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b \<Longrightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"

syntax "_is_dghm" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_dghm \<alpha> \<AA> \<BB> \<FF>"

abbreviation (input) is_cn_dghm :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "is_cn_dghm \<alpha> \<AA> \<BB> \<FF> \<equiv> \<FF> : op_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"

syntax "_is_cn_dghm" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool" 
  (\<open>(_ :/ _ \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>" \<rightharpoonup> "CONST is_cn_dghm \<alpha> \<AA> \<BB> \<FF>"

abbreviation all_dghms :: "V \<Rightarrow> V"
  where "all_dghms \<alpha> \<equiv> set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation dghms :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "dghms \<alpha> \<AA> \<BB> \<equiv> set {\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>}"

sublocale is_dghm \<subseteq> ObjMap: vsv \<open>\<FF>\<lparr>ObjMap\<rparr>\<close>
  rewrites "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
  by (rule dghm_ObjMap_vsv) (simp add: dg_cs_simps)

sublocale is_dghm \<subseteq> ArrMap: vsv \<open>\<FF>\<lparr>ArrMap\<rparr>\<close>
  rewrites "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
  by (rule dghm_ArrMap_vsv) (simp add: dg_cs_simps)

lemmas [dg_cs_simps] =
  is_dghm.dghm_HomDom
  is_dghm.dghm_HomCod
  is_dghm.dghm_ObjMap_vdomain
  is_dghm.dghm_ArrMap_vdomain

lemma (in is_dghm) dghm_ArrMap_is_arr''[dg_cs_intros]:
  assumes "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" and "\<FF>f = \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
  shows "\<FF>f : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
  using assms(1) unfolding assms(2) by (rule dghm_ArrMap_is_arr)

lemma (in is_dghm) dghm_ArrMap_is_arr'[dg_cs_intros]:
  assumes "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
    and "A = \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "B = \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
  shows "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : A \<mapsto>\<^bsub>\<BB>\<^esub> B"
  using assms(1) unfolding assms(2,3) by (rule dghm_ArrMap_is_arr) 

lemmas [dg_cs_intros] = is_dghm.dghm_ArrMap_is_arr'


text\<open>Rules.\<close>

lemma (in is_dghm) is_dghm_axioms'[dg_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_dghm_axioms)

mk_ide rf is_dghm_def[unfolded is_dghm_axioms_def]
  |intro is_dghmI|
  |dest is_dghmD[dest]|
  |elim is_dghmE[elim]|

lemmas [dg_cs_intros] = is_dghmD(3,4)


text\<open>Elementary properties.\<close>

lemma dghm_eqI:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<GG>\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>"
    and "\<GG>\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
    and "\<AA> = \<CC>"
    and "\<BB> = \<DD>"
  shows "\<GG> = \<FF>"
proof-
  interpret L: is_dghm \<alpha> \<AA> \<BB> \<GG> by (rule assms(1))
  interpret R: is_dghm \<alpha> \<CC> \<DD> \<FF> by (rule assms(2))
  show ?thesis
  proof(rule vsv_eqI)
    have dom: "\<D>\<^sub>\<circ> \<GG> = 4\<^sub>\<nat>" by (cs_concl cs_simp: dg_cs_simps V_cs_simps)
    from assms(5,6) have sup: "\<GG>\<lparr>HomDom\<rparr> = \<FF>\<lparr>HomDom\<rparr>" "\<GG>\<lparr>HomCod\<rparr> = \<FF>\<lparr>HomCod\<rparr>" 
      by (simp_all add: dg_cs_simps)
    show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<GG> \<Longrightarrow> \<GG>\<lparr>a\<rparr> = \<FF>\<lparr>a\<rparr>" for a 
      by (unfold dom, elim_in_numeral, insert assms(3,4) sup)
        (auto simp: dghm_field_simps)
  qed (cs_concl cs_simp: dg_cs_simps V_cs_simps cs_intro: V_cs_intros)+
qed

lemma (in is_dghm) dghm_def: "\<FF> = [\<FF>\<lparr>ObjMap\<rparr>, \<FF>\<lparr>ArrMap\<rparr>, \<FF>\<lparr>HomDom\<rparr>, \<FF>\<lparr>HomCod\<rparr>]\<^sub>\<circ>"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> \<FF> = 4\<^sub>\<nat>" by (cs_concl cs_simp: dg_cs_simps V_cs_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> [\<FF>\<lparr>ObjMap\<rparr>, \<FF>\<lparr>ArrMap\<rparr>, \<FF>\<lparr>HomDom\<rparr>, \<FF>\<lparr>HomCod\<rparr>]\<^sub>\<circ> = 4\<^sub>\<nat>"
    by (simp add: nat_omega_simps)
  then show "\<D>\<^sub>\<circ> \<FF> = \<D>\<^sub>\<circ> [\<FF>\<lparr>ObjMap\<rparr>, \<FF>\<lparr>ArrMap\<rparr>, \<FF>\<lparr>HomDom\<rparr>, \<FF>\<lparr>HomCod\<rparr>]\<^sub>\<circ>"
    unfolding dom_lhs dom_rhs by (simp add: nat_omega_simps)
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<FF> \<Longrightarrow> \<FF>\<lparr>a\<rparr> = [\<FF>\<lparr>ObjMap\<rparr>, \<FF>\<lparr>ArrMap\<rparr>, \<FF>\<lparr>HomDom\<rparr>, \<FF>\<lparr>HomCod\<rparr>]\<^sub>\<circ>\<lparr>a\<rparr>" 
    for a
    by (unfold dom_lhs, elim_in_numeral, unfold dghm_field_simps)
      (simp_all add: nat_omega_simps)
qed (auto simp: vsv_axioms)

lemma (in is_dghm) dghm_ObjMap_app_in_HomCod_Obj[dg_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  using assms dghm_ObjMap_vrange by (blast dest: ObjMap.vsv_vimageI2)

lemmas [dg_cs_intros] = is_dghm.dghm_ObjMap_app_in_HomCod_Obj

lemma (in is_dghm) dghm_ArrMap_vrange: "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
proof(rule vsv.vsv_vrange_vsubset, unfold dg_cs_simps)
  fix f assume "f \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
  then obtain a b where "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" by auto
  then have "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>" 
    by (cs_concl cs_intro: dg_cs_intros)
  then show "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" by auto
qed auto

lemma (in is_dghm) dghm_ArrMap_app_in_HomCod_Arr[dg_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
  shows "\<FF>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
  using assms dghm_ArrMap_vrange by (blast dest: ArrMap.vsv_vimageI2)

lemmas [dg_cs_intros] = is_dghm.dghm_ArrMap_app_in_HomCod_Arr


text\<open>Size.\<close>

lemma (in is_dghm) dghm_ObjMap_vsubset_Vset: "\<FF>\<lparr>ObjMap\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  by 
    (
      rule ObjMap.vbrelation_Limit_vsubset_VsetI, 
      insert dghm_ObjMap_vrange HomCod.dg_Obj_vsubset_Vset
    )
    (auto intro!: HomDom.dg_Obj_vsubset_Vset)

lemma (in is_dghm) dghm_ArrMap_vsubset_Vset: "\<FF>\<lparr>ArrMap\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  by 
    (
      rule ArrMap.vbrelation_Limit_vsubset_VsetI, 
      insert dghm_ArrMap_vrange HomCod.dg_Arr_vsubset_Vset
    )
    (auto intro!: HomDom.dg_Arr_vsubset_Vset)

lemma (in is_dghm) dghm_ObjMap_in_Vset: 
  assumes "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<FF>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<beta>" 
  by (meson assms dghm_ObjMap_vsubset_Vset Vset_in_mono vsubset_in_VsetI)

lemma (in is_dghm) dghm_ArrMap_in_Vset:
  assumes  "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<FF>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
  by (meson assms dghm_ArrMap_vsubset_Vset Vset_in_mono vsubset_in_VsetI)

lemma (in is_dghm) dghm_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<FF> \<in>\<^sub>\<circ> Vset \<beta>"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  note [dg_cs_intros] = 
    dghm_ObjMap_in_Vset dghm_ArrMap_in_Vset HomDom.dg_in_Vset HomCod.dg_in_Vset
  from assms(2) show ?thesis
    by (subst dghm_def) 
      (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros V_cs_intros)
qed

lemma (in is_dghm) dghm_is_dghm_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<beta>\<^esub> \<BB>"
proof(rule is_dghmI)
  from is_dghm_axioms assms show "digraph \<beta> \<AA>"
    by (cs_concl cs_intro: digraph.dg_digraph_if_ge_Limit dg_cs_intros)
  from is_dghm_axioms assms show "digraph \<beta> \<BB>"
    by (cs_concl cs_intro: digraph.dg_digraph_if_ge_Limit dg_cs_intros)
qed (cs_concl cs_simp: dg_cs_simps cs_intro: assms(1) dg_cs_intros V_cs_intros dghm_ObjMap_vrange)+

lemma small_all_dghms[simp]: "small {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(cases \<open>\<Z> \<alpha>\<close>)
  case True
  from is_dghm.dghm_in_Vset show ?thesis
    by (intro down[of _ \<open>Vset (\<alpha> + \<omega>)\<close>] subsetI)
      (auto simp: True \<Z>.\<Z>_Limit_\<alpha>\<omega> \<Z>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>.intro \<Z>.\<Z>_\<alpha>_\<alpha>\<omega>)
next
  case False
  then have "{\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>} = {}" by auto
  then show ?thesis by simp
qed

lemma (in is_dghm) dghm_in_Vset_7: "\<FF> \<in>\<^sub>\<circ> Vset (\<alpha> + 7\<^sub>\<nat>)"
proof-
  note [folded VPow_iff, folded Vset_succ[OF Ord_\<alpha>], dg_cs_intros] =
    dghm_ObjMap_vsubset_Vset 
    dghm_ArrMap_vsubset_Vset 
  from HomDom.dg_digraph_in_Vset_4 have [dg_cs_intros]:
    "\<AA> \<in>\<^sub>\<circ> Vset (succ (succ (succ (succ \<alpha>))))"
    by (succ_of_numeral) (cs_prems cs_simp: plus_V_succ_right V_cs_simps)
  from HomCod.dg_digraph_in_Vset_4 have [dg_cs_intros]:
    "\<BB> \<in>\<^sub>\<circ> Vset (succ (succ (succ (succ \<alpha>))))"
    by (succ_of_numeral) (cs_prems cs_simp: plus_V_succ_right V_cs_simps)
  show ?thesis
    by (subst dghm_def, succ_of_numeral)
      (
        cs_concl 
          cs_simp: plus_V_succ_right V_cs_simps dg_cs_simps 
          cs_intro: dg_cs_intros V_cs_intros
      )
qed

lemma (in \<Z>) all_dghms_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "all_dghms \<alpha> \<in>\<^sub>\<circ> Vset \<beta>"
proof(rule vsubset_in_VsetI)
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "all_dghms \<alpha> \<subseteq>\<^sub>\<circ> Vset (\<alpha> + 7\<^sub>\<nat>)"
  proof(intro vsubsetI)
    fix \<FF> assume "\<FF> \<in>\<^sub>\<circ> all_dghms \<alpha>"
    then obtain \<AA> \<BB> where \<FF>: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" by clarsimp
    interpret is_dghm \<alpha> \<AA> \<BB> \<FF> using \<FF> by simp
    show "\<FF> \<in>\<^sub>\<circ> Vset (\<alpha> + 7\<^sub>\<nat>)" by (rule dghm_in_Vset_7)
  qed
  from assms(2) show "Vset (\<alpha> + 7\<^sub>\<nat>) \<in>\<^sub>\<circ> Vset \<beta>"
    by (cs_concl cs_intro: V_cs_intros Ord_cs_intros)
qed

lemma small_dghms[simp]: "small {\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>}"
  by (rule down[of _ \<open>set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>}\<close>]) auto


text\<open>Further elementary properties.\<close>

lemma (in is_dghm) dghm_is_arr_HomCod: 
  assumes "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
  shows "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" "\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" "\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
  using assms by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)+ 

lemma (in is_dghm) dghm_vimage_dghm_ArrMap_vsubset_Hom:
  assumes "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "\<FF>\<lparr>ArrMap\<rparr> `\<^sub>\<circ> Hom \<AA> a b \<subseteq>\<^sub>\<circ> Hom \<BB> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
proof(intro vsubsetI)
  fix g assume "g \<in>\<^sub>\<circ> \<FF>\<lparr>ArrMap\<rparr> `\<^sub>\<circ> Hom \<AA> a b"
  then obtain f where "f \<in>\<^sub>\<circ> Hom (\<FF>\<lparr>HomDom\<rparr>) a b" and "g = \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>" 
    by (auto simp: dg_cs_simps)
  then show "g \<in>\<^sub>\<circ> Hom \<BB> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    by (simp add: dghm_ArrMap_is_arr dg_cs_simps)
qed



subsection\<open>Opposite digraph homomorphism\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter II-2 in \cite{mac_lane_categories_2010}.\<close>

definition op_dghm :: "V \<Rightarrow> V"
  where "op_dghm \<FF> =
    [\<FF>\<lparr>ObjMap\<rparr>, \<FF>\<lparr>ArrMap\<rparr>, op_dg (\<FF>\<lparr>HomDom\<rparr>), op_dg (\<FF>\<lparr>HomCod\<rparr>)]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma op_dghm_components[dg_op_simps]:
  shows "op_dghm \<FF>\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>"
    and "op_dghm \<FF>\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
    and "op_dghm \<FF>\<lparr>HomDom\<rparr> = op_dg (\<FF>\<lparr>HomDom\<rparr>)"
    and "op_dghm \<FF>\<lparr>HomCod\<rparr> = op_dg (\<FF>\<lparr>HomCod\<rparr>)"
  unfolding op_dghm_def dghm_field_simps by (auto simp: nat_omega_simps)


subsubsection\<open>Further properties\<close>

lemma (in is_dghm) is_dghm_op: "op_dghm \<FF> : op_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> op_dg \<BB>"
proof(intro is_dghmI, unfold dg_op_simps)
  show "vfsequence (op_dghm \<FF>)" unfolding op_dghm_def by simp
  show "vcard (op_dghm \<FF>) = 4\<^sub>\<nat>"
    unfolding op_dghm_def by (auto simp: nat_omega_simps)
qed 
  (
    cs_concl 
      cs_intro: dghm_ObjMap_vrange dg_cs_intros dg_op_intros V_cs_intros 
      cs_simp: dg_cs_simps dg_op_simps
  )+

lemma (in is_dghm) is_dghm_op'[dg_op_intros]:  
  assumes "\<AA>' = op_dg \<AA>" and "\<BB>' = op_dg \<BB>" and "\<alpha>' = \<alpha>"
  shows "op_dghm \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_dghm_op)

lemmas is_dghm_op[dg_op_intros] = is_dghm.is_dghm_op'

lemma (in is_dghm) dghm_op_dghm_op_dghm[dg_op_simps]: "op_dghm (op_dghm \<FF>) = \<FF>" 
  using is_dghm_axioms
  by 
    (
      cs_concl 
        cs_simp: dg_op_simps 
        cs_intro: dg_op_intros dghm_eqI[where \<FF>=\<FF>]
    )

lemmas dghm_op_dghm_op_dghm[dg_op_simps] = is_dghm.dghm_op_dghm_op_dghm

lemma eq_op_dghm_iff[dg_op_simps]: 
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "op_dghm \<GG> = op_dghm \<FF> \<longleftrightarrow> \<GG> = \<FF>"
proof
  interpret L: is_dghm \<alpha> \<AA> \<BB> \<GG> by (rule assms(1))
  interpret R: is_dghm \<alpha> \<CC> \<DD> \<FF> by (rule assms(2))
  assume prems: "op_dghm \<GG> = op_dghm \<FF>"
  show "\<GG> = \<FF>"
  proof(rule dghm_eqI[OF assms])
    from prems R.dghm_op_dghm_op_dghm L.dghm_op_dghm_op_dghm show 
      "\<GG>\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>" and "\<GG>\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
      by metis+
    from prems R.dghm_op_dghm_op_dghm L.dghm_op_dghm_op_dghm have 
      "\<GG>\<lparr>HomDom\<rparr> = \<FF>\<lparr>HomDom\<rparr>" "\<GG>\<lparr>HomCod\<rparr> = \<FF>\<lparr>HomCod\<rparr>"
      by auto
    then show "\<AA> = \<CC>" "\<BB> = \<DD>" by (auto simp: dg_cs_simps)
  qed
qed auto



subsection\<open>Composition of covariant digraph homomorphisms\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>

definition dghm_comp :: "V \<Rightarrow> V \<Rightarrow> V" (infixl \<open>\<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<close> 55)
  where "\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> =
    [\<GG>\<lparr>ObjMap\<rparr> \<circ>\<^sub>\<circ> \<FF>\<lparr>ObjMap\<rparr>, \<GG>\<lparr>ArrMap\<rparr> \<circ>\<^sub>\<circ> \<FF>\<lparr>ArrMap\<rparr>, \<FF>\<lparr>HomDom\<rparr>, \<GG>\<lparr>HomCod\<rparr>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dghm_comp_components:
  shows "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr> = \<GG>\<lparr>ObjMap\<rparr> \<circ>\<^sub>\<circ> \<FF>\<lparr>ObjMap\<rparr>"
    and "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr> = \<GG>\<lparr>ArrMap\<rparr> \<circ>\<^sub>\<circ> \<FF>\<lparr>ArrMap\<rparr>"
    and [dg_shared_cs_simps, dg_cs_simps]: "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>HomDom\<rparr> = \<FF>\<lparr>HomDom\<rparr>"
    and [dg_shared_cs_simps, dg_cs_simps]: "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>HomCod\<rparr> = \<GG>\<lparr>HomCod\<rparr>"
  unfolding dghm_comp_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

lemma dghm_comp_ObjMap_vsv[dg_cs_intros]: 
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "vsv ((\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>)"
proof-
  interpret L: is_dghm \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_dghm \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis by (cs_concl cs_simp: dghm_comp_components cs_intro: V_cs_intros)
qed

lemma dghm_comp_ObjMap_vdomain[dg_cs_simps]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
  using assms 
  by 
    (
      cs_concl 
        cs_simp: dghm_comp_components dg_cs_simps V_cs_simps
        cs_intro: is_dghm.dghm_ObjMap_vrange
    )

lemma dghm_comp_ObjMap_vrange:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  using assms 
  by 
    (
      cs_concl 
        cs_simp: dghm_comp_components 
        cs_intro: is_dghm.dghm_ObjMap_vrange V_cs_intros
    )

lemma dghm_comp_ObjMap_app[dg_cs_simps]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
proof-
  interpret L: is_dghm \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_dghm \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  from assms(3) show "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>" 
    by 
      (
        cs_concl 
          cs_simp: dghm_comp_components dg_cs_simps V_cs_simps 
          cs_intro: V_cs_intros dg_cs_intros
      )
qed


subsubsection\<open>Arrow map\<close>

lemma dghm_comp_ArrMap_vsv[dg_cs_intros]: 
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "vsv ((\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr>)"
proof-
  interpret L: is_dghm \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_dghm \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis by (cs_concl cs_simp: dghm_comp_components cs_intro: V_cs_intros)
qed

lemma dghm_comp_ArrMap_vdomain[dg_cs_simps]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
  using assms 
  by 
    (
      cs_concl 
        cs_simp: dghm_comp_components dg_cs_simps V_cs_simps
        cs_intro: is_dghm.dghm_ArrMap_vrange
    )

lemma dghm_comp_ArrMap_vrange[dg_cs_intros]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  using assms 
  by 
    (
      cs_concl 
        cs_simp: dghm_comp_components 
        cs_intro: is_dghm.dghm_ArrMap_vrange V_cs_intros
    )

lemma dghm_comp_ArrMap_app[dg_cs_simps]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" and "f \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
  shows "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr>"
proof-
  interpret L: is_dghm \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_dghm \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  from assms(3) show "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr>"
    by 
      (
        cs_concl 
          cs_simp: dghm_comp_components dg_cs_simps V_cs_simps 
          cs_intro: V_cs_intros dg_cs_intros
      )
qed


subsubsection\<open>Opposite of the composition of covariant digraph homomorphisms\<close>

lemma op_dghm_dghm_comp[dg_op_simps]: 
  "op_dghm (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>) = op_dghm \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M op_dghm \<FF>"
  unfolding dghm_comp_def op_dghm_def dghm_field_simps
  by (simp add: nat_omega_simps)


subsubsection\<open>Further properties\<close>

lemma dghm_comp_is_dghm[dg_cs_intros]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret L: is_dghm \<alpha> \<BB> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_dghm \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis 
  proof(intro is_dghmI is_dghmI, unfold dg_cs_simps)  
    show "vfsequence (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)" unfolding dghm_comp_def by simp
    show "vcard (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>) = 4\<^sub>\<nat>" 
      unfolding dghm_comp_def by (simp add: nat_omega_simps)
    fix f a b assume "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
    with assms show "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : 
      (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  qed 
    (
      use assms in 
        \<open>
          cs_concl
            cs_intro: dg_cs_intros dghm_comp_ObjMap_vrange 
            cs_simp: dg_cs_simps
        \<close>
    )+
qed

lemma dghm_comp_assoc[dg_cs_simps]:
  assumes "\<HH> : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<DD>" and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "(\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>) \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> = \<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)"
proof(rule dghm_eqI [of \<alpha> \<AA> \<DD> _ \<AA> \<DD>])
  show "(\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr> = (\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>))\<lparr>ObjMap\<rparr>"
  proof(rule vsv_eqI)
    show "(\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = (\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>))\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>)" for a 
      using that assms
      by 
        (cs_prems cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
        (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  qed (use assms in \<open>cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros\<close>)+
  show "(\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr> = (\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>))\<lparr>ArrMap\<rparr>"
  proof(rule vsv_eqI)
    show "(\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> = (\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>))\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr>)" for a 
      using that assms
      by 
        (cs_prems cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
        (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  qed (use assms in \<open>cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros\<close>)+
qed (use assms in \<open>cs_concl cs_intro: dg_cs_intros\<close>)+



subsection\<open>Composition of contravariant digraph homomorphisms\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See section 1.2 in \cite{bodo_categories_1970}.\<close>

definition dghm_cn_comp :: "V \<Rightarrow> V \<Rightarrow> V" (infixl \<open>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ>\<close> 55)
  where "\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF> =
    [
      \<GG>\<lparr>ObjMap\<rparr> \<circ>\<^sub>\<circ> \<FF>\<lparr>ObjMap\<rparr>,
      \<GG>\<lparr>ArrMap\<rparr> \<circ>\<^sub>\<circ> \<FF>\<lparr>ArrMap\<rparr>,
      op_dg (\<FF>\<lparr>HomDom\<rparr>), 
      \<GG>\<lparr>HomCod\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dghm_cn_comp_components:
  shows "(\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ObjMap\<rparr> = \<GG>\<lparr>ObjMap\<rparr> \<circ>\<^sub>\<circ> \<FF>\<lparr>ObjMap\<rparr>"
    and "(\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ArrMap\<rparr> = \<GG>\<lparr>ArrMap\<rparr> \<circ>\<^sub>\<circ> \<FF>\<lparr>ArrMap\<rparr>"
    and [dg_cn_cs_simps]: "(\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>HomDom\<rparr> = op_dg (\<FF>\<lparr>HomDom\<rparr>)"
    and [dg_cn_cs_simps]: "(\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>HomCod\<rparr> = \<GG>\<lparr>HomCod\<rparr>"
  unfolding dghm_cn_comp_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map: two contravariant digraph homomorphisms\<close>

lemma dghm_cn_comp_ObjMap_vsv[dg_cn_cs_intros]: 
  assumes "\<GG> : \<BB> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "vsv ((\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ObjMap\<rparr>)"
proof-
  interpret L: is_dghm \<alpha> \<open>op_dg \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_dghm \<alpha> \<open>op_dg \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  show ?thesis 
    by (cs_concl cs_simp: dghm_cn_comp_components cs_intro: V_cs_intros)
qed

lemma dghm_cn_comp_ObjMap_vdomain[dg_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
  using assms 
  by 
    (
      cs_concl 
        cs_simp: dghm_cn_comp_components dg_cs_simps dg_op_simps V_cs_simps
        cs_intro: is_dghm.dghm_ObjMap_vrange 
    )

lemma dghm_cn_comp_ObjMap_vrange:
  assumes "\<GG> : \<BB> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  using assms 
  by 
    (
      cs_concl 
        cs_simp: dghm_cn_comp_components
        cs_intro: is_dghm.dghm_ObjMap_vrange V_cs_intros 
    )

lemma dghm_cn_comp_ObjMap_app[dg_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "(\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
proof-
  interpret L: is_dghm \<alpha> \<open>op_dg \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_dghm \<alpha> \<open>op_dg \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  from assms(3) show "(\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
    by 
      (
        cs_concl 
          cs_simp: dghm_cn_comp_components dg_cs_simps dg_op_simps V_cs_simps 
          cs_intro: V_cs_intros dg_cs_intros
      )
qed


subsubsection\<open>Arrow map: two contravariant digraph homomorphisms\<close>

lemma dghm_cn_comp_ArrMap_vsv[dg_cn_cs_intros]: 
  assumes "\<GG> : \<BB> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "vsv ((\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ArrMap\<rparr>)"
proof-
  interpret L: is_dghm \<alpha> \<open>op_dg \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_dghm \<alpha> \<open>op_dg \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  show ?thesis 
    by (cs_concl cs_simp: dghm_cn_comp_components cs_intro: V_cs_intros)
qed

lemma dghm_cn_comp_ArrMap_vdomain[dg_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
  using assms 
  by 
    (
      cs_concl 
        cs_simp: dghm_cn_comp_components dg_cs_simps dg_op_simps V_cs_simps
        cs_intro: is_dghm.dghm_ArrMap_vrange 
    )

lemma dghm_cn_comp_ArrMap_vrange:
  assumes "\<GG> : \<BB> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  using assms 
  by 
    (
      cs_concl 
        cs_simp: dghm_cn_comp_components
        cs_intro: is_dghm.dghm_ArrMap_vrange V_cs_intros 
    )

lemma dghm_cn_comp_ArrMap_app[dg_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
  shows "(\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>\<rparr>"
proof-
  interpret L: is_dghm \<alpha> \<open>op_dg \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_dghm \<alpha> \<open>op_dg \<AA>\<close> \<BB> \<FF> by (rule assms(2))
  from assms(3) show "(\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>\<rparr>"
    by 
      (
        cs_concl 
          cs_simp: dghm_cn_comp_components dg_cs_simps dg_op_simps V_cs_simps 
          cs_intro: V_cs_intros dg_cs_intros
      )
qed


subsubsection\<open>Object map: contravariant and covariant digraph homomorphisms\<close>

lemma dghm_cn_cov_comp_ObjMap_vsv[dg_cn_cs_intros]: 
  assumes "\<GG> : \<BB> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "vsv ((\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ObjMap\<rparr>)"
proof-
  interpret L: is_dghm \<alpha> \<open>op_dg \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_dghm \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis 
    by (cs_concl cs_simp: dghm_cn_comp_components cs_intro: V_cs_intros)
qed

lemma dghm_cn_cov_comp_ObjMap_vdomain[dg_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
  using assms 
  by 
    (
      cs_concl 
        cs_simp: dghm_cn_comp_components dg_cs_simps dg_op_simps V_cs_simps
        cs_intro: is_dghm.dghm_ObjMap_vrange 
    )

lemma dghm_cn_cov_comp_ObjMap_vrange:
  assumes "\<GG> : \<BB> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  using assms
  by
    (
      cs_concl
        cs_simp: dghm_cn_comp_components
        cs_intro: is_dghm.dghm_ObjMap_vrange V_cs_intros 
    )

lemma dghm_cn_cov_comp_ObjMap_app[dg_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "(\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
proof-
  interpret L: is_dghm \<alpha> \<open>op_dg \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_dghm \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  from assms show "(\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>" 
    by 
      (
        cs_concl 
          cs_simp: dghm_cn_comp_components dg_cs_simps V_cs_simps 
          cs_intro: V_cs_intros dg_op_intros dg_cs_intros
      )
qed


subsubsection\<open>Arrow map: contravariant and covariant digraph homomorphisms\<close>

lemma dghm_cn_cov_comp_ArrMap_vsv[dg_cn_cs_intros]:
  assumes "\<GG> : \<BB> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "vsv ((\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ArrMap\<rparr>)"
proof-
  interpret L: is_dghm \<alpha> \<open>op_dg \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_dghm \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis 
    by (cs_concl cs_simp: dghm_cn_comp_components cs_intro: V_cs_intros)
qed

lemma dghm_cn_cov_comp_ArrMap_vdomain[dg_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> ((\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
  using assms 
  by 
    (
      cs_concl 
        cs_simp: dghm_cn_comp_components dg_cs_simps dg_op_simps V_cs_simps
        cs_intro: is_dghm.dghm_ArrMap_vrange 
    )

lemma dghm_cn_cov_comp_ArrMap_vrange:
  assumes "\<GG> : \<BB> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  using assms 
  by 
    (
      cs_concl 
        cs_simp: dghm_cn_comp_components
        cs_intro: is_dghm.dghm_ArrMap_vrange V_cs_intros 
    )

lemma dghm_cn_cov_comp_ArrMap_app[dg_cn_cs_simps]:
  assumes "\<GG> : \<BB> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
  shows "(\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>\<rparr>"
proof-
  interpret L: is_dghm \<alpha> \<open>op_dg \<BB>\<close> \<CC> \<GG> by (rule assms(1)) 
  interpret R: is_dghm \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  from assms(3) show "(\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>\<rparr>" 
    by 
      (
        cs_concl 
          cs_simp: dghm_cn_comp_components dg_cs_simps V_cs_simps 
          cs_intro: V_cs_intros dg_op_intros dg_cs_intros
      )
qed


subsubsection\<open>
Opposite of the contravariant composition of the digraph homomorphisms
\<close>

lemma op_dghm_dghm_cn_comp[dg_op_simps]: 
  "op_dghm (\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>) = op_dghm \<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> op_dghm \<FF>"
  unfolding op_dghm_def dghm_cn_comp_def dghm_field_simps
  by (auto simp: nat_omega_simps)


subsubsection\<open>Further properties\<close>

lemma dghm_cn_comp_is_dghm[dg_cn_cs_intros]:
  \<comment>\<open>See section 1.2 in \cite{bodo_categories_1970}.\<close>
  assumes "digraph \<alpha> \<AA>" and "\<GG> : \<BB> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<AA>: digraph \<alpha> \<AA> by (rule assms(1))
  interpret L: is_dghm \<alpha> \<open>op_dg \<BB>\<close> \<CC> \<GG> using assms(2) by auto
  interpret R: is_dghm \<alpha> \<open>op_dg \<AA>\<close> \<BB> \<FF> using assms(3) by auto
  show ?thesis
  proof(intro is_dghmI, unfold dg_op_simps dg_cs_simps dg_cn_cs_simps)
    show "vfsequence (\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)" unfolding dghm_cn_comp_def by auto
    show "vcard (\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>) = 4\<^sub>\<nat>"
      unfolding dghm_cn_comp_def by (simp add: nat_omega_simps)
    fix f a b assume "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
    with assms show "(\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> :
      (\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> (\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: dg_cn_cs_simps  
            cs_intro: dg_cs_intros dg_op_intros
        )
  qed 
    ( 
      cs_concl 
        cs_simp: dg_cs_simps dg_cn_cs_simps 
        cs_intro: dghm_cn_comp_ObjMap_vrange dg_cs_intros dg_cn_cs_intros
    )+
qed

lemma dghm_cn_cov_comp_is_dghm[dg_cn_cs_intros]:
  \<comment>\<open>See section 1.2 in \cite{bodo_categories_1970}.\<close>
  assumes "\<GG> : \<BB> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF> : \<AA> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret L: is_dghm \<alpha> \<open>op_dg \<BB>\<close> \<CC> \<GG> by (rule assms(1))
  interpret R: is_dghm \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  show ?thesis
  proof(intro is_dghmI, unfold dg_op_simps dg_cs_simps)
    show "vfsequence (\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)" unfolding dghm_cn_comp_def by simp
    show "vcard (\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>) = 4\<^sub>\<nat>" 
      unfolding dghm_cn_comp_def by (auto simp: nat_omega_simps)
    fix f b a assume "f : b \<mapsto>\<^bsub>\<AA>\<^esub> a"
    with assms show "(\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : 
      (\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> (\<GG> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<FF>)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      by (cs_concl cs_simp: dg_cn_cs_simps dg_op_simps cs_intro: dg_cs_intros)
  qed
    ( 
      cs_concl 
        cs_simp: dg_cs_simps dg_cn_cs_simps
        cs_intro:
          dghm_cn_cov_comp_ObjMap_vrange 
          dg_cs_intros dg_cn_cs_intros dg_op_intros 
    )+
qed

lemma dghm_cov_cn_comp_is_dghm:
  \<comment>\<open>See section 1.2 in \cite{bodo_categories_1970}\<close>
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> : \<AA> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms by (rule dghm_comp_is_dghm)



subsection\<open>Identity digraph homomorphism\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>

definition dghm_id :: "V \<Rightarrow> V"
  where "dghm_id \<CC> = [vid_on (\<CC>\<lparr>Obj\<rparr>), vid_on (\<CC>\<lparr>Arr\<rparr>), \<CC>, \<CC>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dghm_id_components:
  shows "dghm_id \<CC>\<lparr>ObjMap\<rparr> = vid_on (\<CC>\<lparr>Obj\<rparr>)" 
    and "dghm_id \<CC>\<lparr>ArrMap\<rparr> = vid_on (\<CC>\<lparr>Arr\<rparr>)" 
    and [dg_shared_cs_simps, dg_cs_simps]: "dghm_id \<CC>\<lparr>HomDom\<rparr> = \<CC>"
    and [dg_shared_cs_simps, dg_cs_simps]: "dghm_id \<CC>\<lparr>HomCod\<rparr> = \<CC>" 
  unfolding dghm_id_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

mk_VLambda dghm_id_components(1)[folded VLambda_vid_on]
  |vsv dghm_id_ObjMap_vsv[dg_shared_cs_intros, dg_cs_intros]|
  |vdomain dghm_id_ObjMap_vdomain[dg_shared_cs_simps, dg_cs_simps]|
  |app dghm_id_ObjMap_app[dg_shared_cs_simps, dg_cs_simps]|

lemma dghm_id_ObjMap_vrange[dg_shared_cs_simps, dg_cs_simps]: 
  "\<R>\<^sub>\<circ> (dghm_id \<CC>\<lparr>ObjMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
  unfolding dghm_id_components by simp


subsubsection\<open>Arrow map\<close>

mk_VLambda dghm_id_components(2)[folded VLambda_vid_on]
  |vsv dghm_id_ArrMap_vsv[dg_shared_cs_intros, dg_cs_intros]|
  |vdomain dghm_id_ArrMap_vdomain[dg_shared_cs_simps, dg_cs_simps]|
  |app dghm_id_ArrMap_app[dg_shared_cs_simps, dg_cs_simps]|

lemma dghm_id_ArrMap_vrange[dg_shared_cs_simps, dg_cs_simps]: 
  "\<R>\<^sub>\<circ> (dghm_id \<CC>\<lparr>ArrMap\<rparr>) = \<CC>\<lparr>Arr\<rparr>"
  unfolding dghm_id_components by simp


subsubsection\<open>Opposite identity digraph homomorphism\<close>

lemma op_dghm_dghm_id[dg_op_simps]: "op_dghm (dghm_id \<CC>) = dghm_id (op_dg \<CC>)"
  unfolding dghm_id_def op_dg_def op_dghm_def dghm_field_simps dg_field_simps
  by (auto simp: nat_omega_simps)


subsubsection\<open>An identity digraph homomorphism is a digraph homomorphism\<close>

lemma (in digraph) dg_dghm_id_is_dghm: "dghm_id \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_dghmI, unfold dg_cs_simps)
  show "vfsequence (dghm_id \<CC>)" unfolding dghm_id_def by simp
  show "vcard (dghm_id \<CC>) = 4\<^sub>\<nat>"
    unfolding dghm_id_def by (simp add: nat_omega_simps)
qed (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros V_cs_intros)+

lemma (in digraph) dg_dghm_id_is_dghm': 
  assumes "\<AA> = \<CC>" and "\<BB> = \<CC>"
  shows "dghm_id \<CC> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  unfolding assms by (rule dg_dghm_id_is_dghm)

lemmas [dg_cs_intros] = digraph.dg_dghm_id_is_dghm'


subsubsection\<open>Further properties\<close>

lemma (in is_dghm) dghm_dghm_comp_dghm_id_left: "dghm_id \<BB> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> = \<FF>"
  \<comment>\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}).\<close>
proof(rule dghm_eqI [of \<alpha> \<AA> \<BB> _ \<AA> \<BB>])
  show "(dghm_id \<BB> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>"
  proof(rule vsv_eqI)
    show "(dghm_id \<BB> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((dghm_id \<BB> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>)" for a 
      using that 
      by 
        (cs_prems cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
        (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  qed (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros V_cs_intros)+
  show "(dghm_id \<BB> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
  proof(rule vsv_eqI)
    show "(dghm_id \<BB> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((dghm_id \<BB> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr>)" for a 
      using that 
      by 
        (cs_prems cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
        (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  qed (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros V_cs_intros)+
qed (cs_concl cs_simp: cs_intro: dg_cs_intros)+

lemmas [dg_cs_simps] = is_dghm.dghm_dghm_comp_dghm_id_left

lemma (in is_dghm) dghm_dghm_comp_dghm_id_right: "\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_id \<AA> = \<FF>"
  \<comment>\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}).\<close>
proof(rule dghm_eqI [of \<alpha> \<AA> \<BB> _ \<AA> \<BB>])
  show "(\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_id \<AA>)\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>"
  proof(rule vsv_eqI)
    show "(\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_id \<AA>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_id \<AA>)\<lparr>ObjMap\<rparr>)" for a 
      using that 
      by 
        (cs_prems cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
        (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  qed (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros V_cs_intros)+
  show "(\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_id \<AA>)\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
  proof(rule vsv_eqI)
    show "(\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_id \<AA>)\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_id \<AA>)\<lparr>ArrMap\<rparr>)" for a 
      using that 
      by 
        (cs_prems cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
        (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  qed (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros V_cs_intros)+
qed (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)+

lemmas [dg_cs_simps] = is_dghm.dghm_dghm_comp_dghm_id_right



subsection\<open>Constant digraph homomorphism\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter III-3 in \cite{mac_lane_categories_2010}.\<close>

definition dghm_const :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "dghm_const \<CC> \<DD> a f =
    [vconst_on (\<CC>\<lparr>Obj\<rparr>) a, vconst_on (\<CC>\<lparr>Arr\<rparr>) f, \<CC>, \<DD>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dghm_const_components:
  shows "dghm_const \<CC> \<DD> a f\<lparr>ObjMap\<rparr> = vconst_on (\<CC>\<lparr>Obj\<rparr>) a" 
    and "dghm_const \<CC> \<DD> a f\<lparr>ArrMap\<rparr> = vconst_on (\<CC>\<lparr>Arr\<rparr>) f" 
    and [dg_shared_cs_simps, dg_cs_simps]: "dghm_const \<CC> \<DD> a f\<lparr>HomDom\<rparr> = \<CC>"
    and [dg_shared_cs_simps, dg_cs_simps]: "dghm_const \<CC> \<DD> a f\<lparr>HomCod\<rparr> = \<DD>" 
  unfolding dghm_const_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

mk_VLambda dghm_const_components(1)[folded VLambda_vconst_on]
  |vsv dghm_const_ObjMap_vsv[dg_shared_cs_intros, dg_cs_intros]|
  |vdomain dghm_const_ObjMap_vdomain[dg_shared_cs_simps, dg_cs_simps]|
  |app dghm_const_ObjMap_app[dg_shared_cs_simps, dg_cs_simps]|


subsubsection\<open>Arrow map\<close>

mk_VLambda dghm_const_components(2)[folded VLambda_vconst_on]
  |vsv dghm_const_ArrMap_vsv[dg_shared_cs_intros, dg_cs_intros]|
  |vdomain dghm_const_ArrMap_vdomain[dg_shared_cs_simps, dg_cs_simps]|
  |app dghm_const_ArrMap_app[dg_shared_cs_simps, dg_cs_simps]|


subsubsection\<open>Opposite constant digraph homomorphism\<close>

lemma op_dghm_dghm_const[dg_op_simps]:
  "op_dghm (dghm_const \<CC> \<DD> a f) = dghm_const (op_dg \<CC>) (op_dg \<DD>) a f"
  unfolding dghm_const_def op_dg_def op_dghm_def dghm_field_simps dg_field_simps
  by (auto simp: nat_omega_simps)


subsubsection\<open>A constant digraph homomorphism is a digraph homomorphism\<close>

lemma dghm_const_is_dghm: 
  assumes "digraph \<alpha> \<CC>" and "digraph \<alpha> \<DD>" and "f : a \<mapsto>\<^bsub>\<DD>\<^esub> a"
  shows "dghm_const \<CC> \<DD> a f : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<DD>"
proof-
  interpret \<DD>: digraph \<alpha> \<DD> by (rule assms(2))
  show ?thesis
  proof(intro is_dghmI)
    show "vfsequence (dghm_const \<CC> \<DD> a f)"
      unfolding dghm_const_def by simp
    show "vcard (dghm_const \<CC> \<DD> a f) = 4\<^sub>\<nat>"
      unfolding dghm_const_def by (simp add: nat_omega_simps)
  qed 
    (
      use assms in 
        \<open>
          cs_concl 
            cs_simp: dghm_const_components(1) dg_cs_simps
            cs_intro: V_cs_intros dg_cs_intros
        \<close>
    )+
qed

lemma dghm_const_is_dghm'[dg_cs_intros]: 
  assumes "digraph \<alpha> \<CC>" 
    and "digraph \<alpha> \<DD>" 
    and "f : a \<mapsto>\<^bsub>\<DD>\<^esub> a"
    and "\<AA> = \<CC>"
    and "\<BB> = \<DD>"
  shows "dghm_const \<CC> \<DD> a f : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms(1-3) unfolding assms(4,5) by (rule dghm_const_is_dghm)



subsection\<open>Faithful digraph homomorphism\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}).\<close>

locale is_ft_dghm = is_dghm \<alpha> \<AA> \<BB> \<FF> for \<alpha> \<AA> \<BB> \<FF> +
  assumes ft_dghm_v11_on_Hom: 
    "\<lbrakk> a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow> v11 (\<FF>\<lparr>ArrMap\<rparr> \<restriction>\<^sup>l\<^sub>\<circ> Hom \<AA> a b)"

syntax "_is_ft_dghm" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_ft_dghm \<alpha> \<AA> \<BB> \<FF>"


text\<open>Rules.\<close>

lemma (in is_ft_dghm) is_ft_dghm_axioms'[dghm_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_ft_dghm_axioms)

mk_ide rf is_ft_dghm_def[unfolded is_ft_dghm_axioms_def]
  |intro is_ft_dghmI|
  |dest is_ft_dghmD[dest]|
  |elim is_ft_dghmE[elim]|

lemmas [dghm_cs_intros] = is_ft_dghmD(1)


subsubsection\<open>Opposite faithful digraph homomorphism\<close>

lemma (in is_ft_dghm) ft_dghm_op_dghm_is_ft_dghm: 
  "op_dghm \<FF> : op_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> op_dg \<BB>"
  by 
    (
      rule is_ft_dghmI, 
      unfold dg_op_simps, 
      cs_concl cs_simp: cs_intro: dg_cs_intros dg_op_intros
    )
    (auto simp: ft_dghm_v11_on_Hom)

lemma (in is_ft_dghm) ft_dghm_op_dghm_is_ft_dghm'[dg_op_intros]: 
  assumes "\<AA>' = op_dg \<AA>" and "\<BB>' = op_dg \<BB>"
  shows "op_dghm \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule ft_dghm_op_dghm_is_ft_dghm)

lemmas ft_dghm_op_dghm_is_ft_dghm[dg_op_intros] = 
  is_ft_dghm.ft_dghm_op_dghm_is_ft_dghm'


subsubsection\<open>
The composition of faithful digraph homomorphisms is a faithful
digraph homomorphism.
\<close>

lemma dghm_comp_is_ft_dghm[dghm_cs_intros]:
  \<comment>\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<CC>"
proof- 
  interpret L: is_ft_dghm \<alpha> \<BB> \<CC> \<GG> using assms(1) by auto
  interpret R: is_ft_dghm \<alpha> \<AA> \<BB> \<FF> using assms(2) by auto 
  have inj: 
    "\<lbrakk> a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> ; b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow> v11 ((\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr> \<restriction>\<^sup>l\<^sub>\<circ> Hom \<AA> a b)"
    for a b
  proof-
    assume prems: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" "b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    then have \<GG>_hom_\<BB>: 
      "v11 (\<GG>\<lparr>ArrMap\<rparr> \<restriction>\<^sup>l\<^sub>\<circ> Hom \<BB> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>))" 
      by (intro L.ft_dghm_v11_on_Hom) 
        (cs_concl cs_intro: dg_cs_intros)+
    have "v11 (\<GG>\<lparr>ArrMap\<rparr> \<restriction>\<^sup>l\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr> `\<^sub>\<circ> Hom \<AA> a b))"
    proof(intro v11_vlrestriction_vsubset[OF \<GG>_hom_\<BB>] vsubsetI)
      fix g assume "g \<in>\<^sub>\<circ> \<FF>\<lparr>ArrMap\<rparr> `\<^sub>\<circ> Hom \<AA> a b" 
      then obtain f where f: "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" and g_def: "g = \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>" 
        by auto
      from f show "g \<in>\<^sub>\<circ> Hom \<BB> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
        by (cs_concl cs_simp: g_def cs_intro: dg_cs_intros)
    qed
    then show "v11 ((\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr> \<restriction>\<^sup>l\<^sub>\<circ> Hom \<AA> a b)"
      unfolding dghm_comp_components
      by (intro v11_vlrestriction_vcomp) (auto simp: R.ft_dghm_v11_on_Hom prems)
  qed
  then show "\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> \<CC>"
    by (intro is_ft_dghmI, cs_concl cs_intro: dg_cs_intros) auto
qed



subsection\<open>Full digraph homomorphism\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>

locale is_fl_dghm = is_dghm \<alpha> \<AA> \<BB> \<FF> for \<alpha> \<AA> \<BB> \<FF> +
  assumes fl_dghm_surj_on_Hom: 
    "\<lbrakk> a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow>
      \<FF>\<lparr>ArrMap\<rparr> `\<^sub>\<circ> (Hom \<AA> a b) = Hom \<BB> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"

syntax "_is_fl_dghm" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_fl_dghm \<alpha> \<AA> \<BB> \<FF>"


text\<open>Rules.\<close>

lemma (in is_fl_dghm) is_fl_dghm_axioms'[dghm_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_fl_dghm_axioms)

mk_ide rf is_fl_dghm_def[unfolded is_fl_dghm_axioms_def]
  |intro is_fl_dghmI|
  |dest is_fl_dghmD[dest]|
  |elim is_fl_dghmE[elim]|

lemmas [dghm_cs_intros] = is_fl_dghmD(1)


subsubsection\<open>Opposite full digraph homomorphism\<close>

lemma (in is_fl_dghm) fl_dghm_op_dghm_is_fl_dghm:
  "op_dghm \<FF> : op_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> op_dg \<BB>"  
  by 
    (
      rule is_fl_dghmI,
      unfold dg_op_simps, 
      cs_concl cs_intro: dg_cs_intros dg_op_intros
    )
    (auto simp: fl_dghm_surj_on_Hom)

lemma (in is_fl_dghm) fl_dghm_op_dghm_is_fl_dghm'[dg_op_intros]:
  assumes "\<AA>' = op_dg \<AA>" and "\<BB>' = op_dg \<BB>"
  shows "op_dghm \<FF> : op_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> op_dg \<BB>"
  unfolding assms by (rule fl_dghm_op_dghm_is_fl_dghm)

lemmas fl_dghm_op_dghm_is_fl_dghm[dg_op_intros] = 
  is_fl_dghm.fl_dghm_op_dghm_is_fl_dghm'


subsubsection\<open>
The composition of full digraph homomorphisms is a full digraph homomorphism
\<close>

lemma dghm_comp_is_fl_dghm[dghm_cs_intros]:
  \<comment>\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<CC>"
proof- 
  interpret L: is_fl_dghm \<alpha> \<BB> \<CC> \<GG> by (rule assms(1))
  interpret R: is_fl_dghm \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  have surj: 
    "\<lbrakk> a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow> 
      (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr> `\<^sub>\<circ> (Hom \<AA> a b) = 
        Hom \<CC> ((\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) ((\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    for a b
  proof-
    assume prems: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" "b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    have surj_\<FF>: "\<FF>\<lparr>ArrMap\<rparr> `\<^sub>\<circ> Hom \<AA> a b = Hom \<BB> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)" 
      by (rule R.fl_dghm_surj_on_Hom[OF prems])
    from prems L.is_dghm_axioms R.is_dghm_axioms have comp_Obj:
      "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
      "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> = \<GG>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<rparr>"
      by (auto simp: dg_cs_simps)
    have "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr> `\<^sub>\<circ> Hom \<AA> a b = \<GG>\<lparr>ArrMap\<rparr> `\<^sub>\<circ> \<FF>\<lparr>ArrMap\<rparr> `\<^sub>\<circ> Hom \<AA> a b"
      unfolding dghm_comp_components by (simp add: vcomp_vimage)
    also from prems have 
      "\<dots> = Hom \<CC> ((\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) ((\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
      unfolding surj_\<FF> comp_Obj
      by 
        (
          simp add: 
            prems(2) L.fl_dghm_surj_on_Hom R.dghm_ObjMap_app_in_HomCod_Obj
        )
    finally show "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr> `\<^sub>\<circ> (Hom \<AA> a b) =
      Hom \<CC> ((\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) ((\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
      by simp
  qed
  show ?thesis  
    by (rule is_fl_dghmI, cs_concl cs_intro: dg_cs_intros)
      (auto simp: surj)
qed



subsection\<open>Fully faithful digraph homomorphism\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>

locale is_ff_dghm = is_ft_dghm \<alpha> \<AA> \<BB> \<FF> + is_fl_dghm \<alpha> \<AA> \<BB> \<FF> for \<alpha> \<AA> \<BB> \<FF>

syntax "_is_ff_dghm" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>f\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_ff_dghm \<alpha> \<AA> \<BB> \<FF>"


text\<open>Rules.\<close>

lemma (in is_ff_dghm) is_ff_dghm_axioms'[dghm_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_ff_dghm_axioms)

mk_ide rf is_ff_dghm_def
  |intro is_ff_dghmI|
  |dest is_ff_dghmD[dest]|
  |elim is_ff_dghmE[elim]|

lemmas [dghm_cs_intros] = is_ff_dghmD


subsubsection\<open>Opposite fully faithful digraph homomorphism.\<close>

lemma (in is_ff_dghm) ff_dghm_op_dghm_is_ff_dghm: 
  "op_dghm \<FF> : op_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> op_dg \<BB>"  
  by (rule is_ff_dghmI) (cs_concl cs_intro: dg_op_intros)+

lemma (in is_ff_dghm) ff_dghm_op_dghm_is_ff_dghm'[dg_op_intros]: 
  assumes "\<AA>' = op_dg \<AA>" and "\<BB>' = op_dg \<BB>"
  shows "op_dghm \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> \<BB>'" 
  unfolding assms by (rule ff_dghm_op_dghm_is_ff_dghm)

lemmas ff_dghm_op_dghm_is_ff_dghm[dg_op_intros] = 
  is_ff_dghm.ff_dghm_op_dghm_is_ff_dghm


subsubsection\<open>
The composition of fully faithful digraph homomorphisms is 
a fully faithful digraph homomorphism.
\<close>

lemma dghm_comp_is_ff_dghm[dghm_cs_intros]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms 
  by (intro is_ff_dghmI, elim is_ff_dghmE) (cs_concl cs_intro: dghm_cs_intros)



subsection\<open>Isomorphism of digraphs\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>

locale is_iso_dghm = is_dghm \<alpha> \<AA> \<BB> \<FF> for \<alpha> \<AA> \<BB> \<FF> +
  assumes iso_dghm_ObjMap_v11: "v11 (\<FF>\<lparr>ObjMap\<rparr>)"
    and iso_dghm_ArrMap_v11: "v11 (\<FF>\<lparr>ArrMap\<rparr>)"
    and iso_dghm_ObjMap_vrange[dghm_cs_simps]: "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
    and iso_dghm_ArrMap_vrange[dghm_cs_simps]: "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>"

syntax "_is_iso_dghm" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_iso_dghm \<alpha> \<AA> \<BB> \<FF>"

sublocale is_iso_dghm \<subseteq> ObjMap: v11 \<open>\<FF>\<lparr>ObjMap\<rparr>\<close>
  rewrites "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>" and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
  by (cs_concl cs_simp: dghm_cs_simps dg_cs_simps cs_intro: iso_dghm_ObjMap_v11)+

sublocale is_iso_dghm \<subseteq> ArrMap: v11 \<open>\<FF>\<lparr>ArrMap\<rparr>\<close>
  rewrites "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>" and "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>"
  by (cs_concl cs_simp: dghm_cs_simps dg_cs_simps cs_intro: iso_dghm_ArrMap_v11)+

lemmas [dghm_cs_simps] = 
  is_iso_dghm.iso_dghm_ObjMap_vrange
  is_iso_dghm.iso_dghm_ArrMap_vrange


text\<open>Rules.\<close>

lemma (in is_iso_dghm) is_iso_dghm_axioms'[dghm_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_iso_dghm_axioms)

mk_ide rf is_iso_dghm_def[unfolded is_iso_dghm_axioms_def]
  |intro is_iso_dghmI|
  |dest is_iso_dghmD[dest]|
  |elim is_iso_dghmE[elim]|


text\<open>Elementary properties.\<close>

lemma (in is_iso_dghm) iso_dghm_Obj_HomDom_if_Obj_HomCod[elim]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  obtains a where "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and "b = \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
  using assms ObjMap.vrange_atD iso_dghm_ObjMap_vrange by blast

lemma (in is_iso_dghm) iso_dghm_Arr_HomDom_if_Arr_HomCod[elim]:
  assumes "g \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
  obtains f where "f \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" and "g = \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
  using assms ArrMap.vrange_atD iso_dghm_ArrMap_vrange by blast

lemma (in is_iso_dghm) iso_dghm_ObjMap_eqE[elim]:
  assumes "\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>" 
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "a = b \<Longrightarrow> P"
  shows P
  using assms ObjMap.v11_eq_iff by auto

lemma (in is_iso_dghm) iso_dghm_ArrMap_eqE[elim]:
  assumes "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>"
    and "f \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
    and "g \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
    and "f = g \<Longrightarrow> P"
  shows P
  using assms ArrMap.v11_eq_iff by auto

sublocale is_iso_dghm \<subseteq> is_ft_dghm 
  by (intro is_ft_dghmI, cs_concl cs_intro: dg_cs_intros) auto

sublocale is_iso_dghm \<subseteq> is_fl_dghm
proof
  fix a b assume [intro]: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" "b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
  show "\<FF>\<lparr>ArrMap\<rparr> `\<^sub>\<circ> Hom \<AA> a b = Hom \<BB> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
  proof(intro vsubset_antisym vsubsetI)
    fix g assume prems: "g \<in>\<^sub>\<circ> Hom \<BB> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    then have g: "g : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>" by auto
    then have dom_g: "\<BB>\<lparr>Dom\<rparr>\<lparr>g\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>" 
      and cod_g: "\<BB>\<lparr>Cod\<rparr>\<lparr>g\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>" 
      by blast+
    from prems obtain f 
      where [intro, simp]: "f \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" and g_def: "g = \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>" 
      by auto
    then obtain a' b' where f: "f : a' \<mapsto>\<^bsub>\<AA>\<^esub> b'"  by blast
    then have "g : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>" 
      by (cs_concl cs_simp: g_def dg_cs_simps cs_intro: dg_cs_intros)
    with g have "\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>" and "\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
      by (metis HomCod.dg_is_arrE cod_g)+
    with f have "a = \<AA>\<lparr>Dom\<rparr>\<lparr>f\<rparr>" "b = \<AA>\<lparr>Cod\<rparr>\<lparr>f\<rparr>" by auto (*slow*)
    with f show "g \<in>\<^sub>\<circ> \<FF>\<lparr>ArrMap\<rparr> `\<^sub>\<circ> Hom \<AA> a b"  
      by (auto simp: g_def HomDom.dg_is_arrD(4,5) ArrMap.vsv_vimageI1)
  qed (metis ArrMap.vsv_vimageE dghm_ArrMap_is_arr' in_Hom_iff)
qed

sublocale is_iso_dghm \<subseteq> is_ff_dghm by unfold_locales

lemmas (in is_iso_dghm) iso_dghm_is_ff_dghm = is_ff_dghm_axioms
lemmas [dghm_cs_intros] = is_iso_dghm.iso_dghm_is_ff_dghm


subsubsection\<open>Opposite digraph isomorphisms\<close>

lemma (in is_iso_dghm) is_iso_dghm_op: 
  "op_dghm \<FF> : op_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> op_dg \<BB>"
  by (intro is_iso_dghmI, unfold dg_op_simps)
    (
      cs_concl 
        cs_simp: dghm_cs_simps cs_intro: V_cs_intros dg_cs_intros dg_op_intros
    )+

lemma (in is_iso_dghm) is_iso_dghm_op': 
  assumes "\<AA>' = op_dg \<AA>" and "\<BB>' = op_dg \<BB>"
  shows "op_dghm \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule is_iso_dghm_op)
  
lemmas is_iso_dghm_op[dg_op_intros] = is_iso_dghm.is_iso_dghm_op'


subsubsection\<open>
The composition of isomorphisms of digraphs is an isomorphism of digraphs
\<close>
 
lemma dghm_comp_is_iso_dghm[dghm_cs_intros]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<CC>"
proof- 
  interpret \<FF>: is_iso_dghm \<alpha> \<AA> \<BB> \<FF> using assms by auto
  interpret \<GG>: is_iso_dghm \<alpha> \<BB> \<CC> \<GG> using assms by auto
  show ?thesis
    by (intro is_iso_dghmI, unfold dghm_comp_components)
      (
        cs_concl 
          cs_simp: V_cs_simps dg_cs_simps dghm_cs_simps 
          cs_intro: dg_cs_intros V_cs_intros
      )+
qed


subsubsection\<open>An identity digraph homomorphism is an isomorphism of digraphs.\<close>

lemma (in digraph) dg_dghm_id_is_iso_dghm: "dghm_id \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<CC>"
  by (rule is_iso_dghmI) (simp_all add: dg_dghm_id_is_dghm dghm_id_components)

lemma (in digraph) dg_dghm_id_is_iso_dghm'[dghm_cs_intros]:
  assumes "\<AA>' = \<CC>" and "\<BB>' = \<CC>"
  shows "dghm_id \<CC> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule dg_dghm_id_is_iso_dghm)

lemmas [dghm_cs_intros] = digraph.dg_dghm_id_is_iso_dghm'



subsection\<open>Inverse digraph homomorphism\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition inv_dghm :: "V \<Rightarrow> V"
  where "inv_dghm \<FF> = [(\<FF>\<lparr>ObjMap\<rparr>)\<inverse>\<^sub>\<circ>, (\<FF>\<lparr>ArrMap\<rparr>)\<inverse>\<^sub>\<circ>, \<FF>\<lparr>HomCod\<rparr>, \<FF>\<lparr>HomDom\<rparr>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma inv_dghm_components:
  shows "inv_dghm \<FF>\<lparr>ObjMap\<rparr> = (\<FF>\<lparr>ObjMap\<rparr>)\<inverse>\<^sub>\<circ>" 
    and "inv_dghm \<FF>\<lparr>ArrMap\<rparr> = (\<FF>\<lparr>ArrMap\<rparr>)\<inverse>\<^sub>\<circ>" 
    and [dghm_cs_simps]: "inv_dghm \<FF>\<lparr>HomDom\<rparr> = \<FF>\<lparr>HomCod\<rparr>"
    and [dghm_cs_simps]: "inv_dghm \<FF>\<lparr>HomCod\<rparr> = \<FF>\<lparr>HomDom\<rparr>" 
  unfolding inv_dghm_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

lemma (in is_iso_dghm) inv_dghm_ObjMap_v11[dghm_cs_intros]:
  "v11 (inv_dghm \<FF>\<lparr>ObjMap\<rparr>)"
  unfolding inv_dghm_components by (cs_concl cs_intro: V_cs_intros)

lemmas [dghm_cs_intros] = is_iso_dghm.inv_dghm_ObjMap_v11

lemma (in is_iso_dghm) inv_dghm_ObjMap_vdomain[dghm_cs_simps]:
  "\<D>\<^sub>\<circ> (inv_dghm \<FF>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
  unfolding inv_dghm_components by (cs_concl cs_simp: dghm_cs_simps V_cs_simps)

lemmas [dghm_cs_simps] = is_iso_dghm.inv_dghm_ObjMap_vdomain

lemma (in is_iso_dghm) inv_dghm_ObjMap_app[dghm_cs_simps]:
  assumes "a' = \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "inv_dghm \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> = a" 
  unfolding inv_dghm_components
  by (metis assms ObjMap.vconverse_atI ObjMap.vsv_vconverse vsv.vsv_appI)

lemmas [dghm_cs_simps] = is_iso_dghm.inv_dghm_ObjMap_app

lemma (in is_iso_dghm) inv_dghm_ObjMap_vrange[dghm_cs_simps]: 
  "\<R>\<^sub>\<circ> (inv_dghm \<FF>\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
  unfolding inv_dghm_components by (cs_concl cs_simp: dg_cs_simps V_cs_simps)

lemmas [dghm_cs_simps] = is_iso_dghm.inv_dghm_ObjMap_vrange


subsubsection\<open>Arrow map\<close>

lemma (in is_iso_dghm) inv_dghm_ArrMap_v11[dghm_cs_intros]:
  "v11 (inv_dghm \<FF>\<lparr>ArrMap\<rparr>)"
  unfolding inv_dghm_components by (cs_concl cs_intro: V_cs_intros)

lemmas [dghm_cs_intros] = is_iso_dghm.inv_dghm_ArrMap_v11

lemma (in is_iso_dghm) inv_dghm_ArrMap_vdomain[dghm_cs_simps]:
  "\<D>\<^sub>\<circ> (inv_dghm \<FF>\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>"
  unfolding inv_dghm_components by (cs_concl cs_simp: dghm_cs_simps V_cs_simps)

lemmas [dghm_cs_simps] = is_iso_dghm.inv_dghm_ArrMap_vdomain

lemma (in is_iso_dghm) inv_dghm_ArrMap_app[dghm_cs_simps]:
  assumes "a' = \<FF>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
  shows "inv_dghm \<FF>\<lparr>ArrMap\<rparr>\<lparr>a'\<rparr> = a" 
  unfolding inv_dghm_components
  by (metis assms ArrMap.vconverse_atI ArrMap.vsv_vconverse vsv.vsv_appI)

lemmas [dghm_cs_simps] = is_iso_dghm.inv_dghm_ArrMap_app

lemma (in is_iso_dghm) inv_dghm_ArrMap_vrange[dghm_cs_simps]: 
  "\<R>\<^sub>\<circ> (inv_dghm \<FF>\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
  unfolding inv_dghm_components by (cs_concl cs_simp: dg_cs_simps V_cs_simps)

lemmas [dghm_cs_simps] = is_iso_dghm.inv_dghm_ArrMap_vrange


subsubsection\<open>Further properties\<close>

lemma (in is_iso_dghm) iso_dghm_ObjMap_inv_dghm_ObjMap_app[dghm_cs_simps]: 
  assumes "a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<FF>\<lparr>ObjMap\<rparr>\<lparr>inv_dghm \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr> = a"
  using assms by (cs_concl cs_simp: inv_dghm_components V_cs_simps)

lemmas [dghm_cs_simps] = is_iso_dghm.iso_dghm_ObjMap_inv_dghm_ObjMap_app

lemma (in is_iso_dghm) iso_dghm_ArrMap_inv_dghm_ArrMap_app[dghm_cs_simps]:
  assumes "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
  shows "\<FF>\<lparr>ArrMap\<rparr>\<lparr>inv_dghm \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr> = f"
  using assms
  by (cs_concl cs_simp: inv_dghm_components V_cs_simps cs_intro: dg_cs_intros)

lemmas [dghm_cs_simps] = is_iso_dghm.iso_dghm_ArrMap_inv_dghm_ArrMap_app

lemma (in is_iso_dghm) iso_dghm_HomDom_is_arr_conv:
  assumes "f \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" 
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
  shows "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" 
  by 
    (
      metis 
        assms
        HomDom.dg_is_arrE 
        is_arr_def 
        dghm_ArrMap_is_arr 
        iso_dghm_ObjMap_eqE
    )

lemma (in is_iso_dghm) iso_dghm_HomCod_is_arr_conv:
  assumes "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" 
    and "a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
    and "inv_dghm \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : inv_dghm \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> inv_dghm \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
  shows "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b" 
  by 
    (
      metis 
        assms 
        dghm_ArrMap_is_arr' 
        is_arrI 
        iso_dghm_ArrMap_inv_dghm_ArrMap_app 
        iso_dghm_ObjMap_inv_dghm_ObjMap_app
    )



subsection\<open>An isomorphism of digraphs is an isomorphism in the category \<open>GRPH\<close>\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}).\<close>

lemma is_arr_isomorphism_is_iso_dghm: 
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> = dghm_id \<AA>"
    and "\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> = dghm_id \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
proof(intro is_iso_dghmI)

  interpret L: is_dghm \<alpha> \<BB> \<AA> \<GG> by (rule assms(2))
  interpret R: is_dghm \<alpha> \<AA> \<BB> \<FF> by (rule assms(1))

  show "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" by (cs_concl cs_intro: dg_cs_intros)

  show "v11 (\<FF>\<lparr>ObjMap\<rparr>)" 
  proof(rule R.ObjMap.vsv_valeq_v11I)
    fix a b assume prems[simp]: 
      "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" "b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" "\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    from assms(1,2) have "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>" 
      by (simp add: dg_cs_simps)
    then show "a = b" by (simp add: assms(3) dghm_id_components)
  qed

  show "v11 (\<FF>\<lparr>ArrMap\<rparr>)"
  proof(rule R.ArrMap.vsv_valeq_v11I)
    fix a b 
    assume prems[simp]: 
      "a \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" "b \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" "\<FF>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>b\<rparr>"
    then have "\<FF>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" 
      by (cs_concl cs_intro: dg_cs_intros)
    with R.dghm_ArrMap_vsv L.dghm_ArrMap_vsv R.dghm_ArrMap_vrange have 
      "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> = (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr>\<lparr>b\<rparr>" 
      unfolding dghm_comp_components by (simp add: dg_cs_simps)
    then show "a = b" by (simp add: assms(3) dghm_id_components)
  qed

  show "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
  proof(intro vsubset_antisym vsubsetI)
    from R.dghm_ObjMap_vrange show "a \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) \<Longrightarrow> a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" for a
      by auto
  next
    fix a assume prems: "a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
    then have a_def[symmetric]: "(\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = a" 
      unfolding assms(4) dghm_id_components by simp
    from prems show "a \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>)"
      by (subst a_def)
        (cs_concl cs_intro: V_cs_intros dg_cs_intros cs_simp: dg_cs_simps)
  qed

  show "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>"
  proof(intro vsubset_antisym vsubsetI)
    from R.dghm_ArrMap_vrange show "a \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) \<Longrightarrow> a \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" for a
      by auto
  next
    fix a assume prems: "a \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" 
    then have a_def[symmetric]: "(\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>)\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> = a" 
      unfolding assms(4) dghm_id_components by simp
    with prems show "a \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>)" 
      by (subst a_def)
        (cs_concl cs_intro: V_cs_intros dg_cs_intros cs_simp: dg_cs_simps)
  qed

qed

lemma is_iso_dghm_is_arr_isomorphism:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  shows [dghm_cs_intros]: "inv_dghm \<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<AA>"
    and "inv_dghm \<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> = dghm_id \<AA>"
    and "\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M inv_dghm \<FF> = dghm_id \<BB>"
proof-

  let ?\<GG> = \<open>inv_dghm \<FF>\<close>

  interpret is_iso_dghm \<alpha> \<AA> \<BB> \<FF> by (rule assms(1))

  show \<GG>: "?\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<AA>"
  proof(intro is_iso_dghmI is_dghmI, unfold dghm_cs_simps)
    show "vfsequence (inv_dghm \<FF>)" unfolding inv_dghm_def by auto
    show "vcard (inv_dghm \<FF>) = 4\<^sub>\<nat>"
      unfolding inv_dghm_def by (simp add: nat_omega_simps)
    show "inv_dghm \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : inv_dghm \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> inv_dghm \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      if "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b" for a b f
      using that 
      by 
        (
          intro iso_dghm_HomDom_is_arr_conv, 
          use nothing in \<open>unfold inv_dghm_components\<close>
        )
        (
          cs_concl 
            cs_simp: V_cs_simps dghm_cs_simps dg_cs_simps 
            cs_intro: dg_cs_intros V_cs_intros 
        )+
  qed 
    (
      cs_concl 
        cs_simp: dg_cs_simps 
        cs_intro: dg_cs_intros V_cs_intros dghm_cs_intros
    )+

  show "inv_dghm \<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> = dghm_id \<AA>"
  proof(rule dghm_eqI[of \<alpha> \<AA> \<AA> _ \<AA> \<AA>])
    show "(inv_dghm \<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr> = dghm_id \<AA>\<lparr>ObjMap\<rparr>"
      unfolding inv_dghm_components dghm_comp_components dghm_id_components
      by (rule ObjMap.v11_vcomp_vconverse)    
    show "(inv_dghm \<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr> = dghm_id \<AA>\<lparr>ArrMap\<rparr>"
      unfolding inv_dghm_components dghm_comp_components dghm_id_components
      by (rule ArrMap.v11_vcomp_vconverse)    
  qed (use \<GG> in \<open>cs_concl cs_intro: dghm_cs_intros\<close>)

  show "\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M inv_dghm \<FF> = dghm_id \<BB>"
  proof(rule dghm_eqI[of \<alpha> \<BB> \<BB> _ \<BB> \<BB>])
    show "(\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M inv_dghm \<FF>)\<lparr>ObjMap\<rparr> = dghm_id \<BB>\<lparr>ObjMap\<rparr>"
      unfolding inv_dghm_components dghm_comp_components dghm_id_components
      by (rule ObjMap.v11_vcomp_vconverse')
    show "(\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M inv_dghm \<FF>)\<lparr>ArrMap\<rparr> = dghm_id \<BB>\<lparr>ArrMap\<rparr>"
      unfolding inv_dghm_components dghm_comp_components dghm_id_components
      by (rule ArrMap.v11_vcomp_vconverse')
  qed (use \<GG> in \<open>cs_concl cs_intro: dghm_cs_intros\<close>)

qed



subsection\<open>Isomorphic digraphs\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}).\<close>

locale iso_digraph = 
  fixes \<alpha> \<AA> \<BB> :: V
  assumes iso_digraph_is_iso_dghm: "\<exists>\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"

notation iso_digraph (infixl "\<approx>\<^sub>D\<^sub>G\<index>" 50)

sublocale iso_digraph \<subseteq> HomDom: digraph \<alpha> \<AA> + HomCod: digraph \<alpha> \<BB>
  using iso_digraph_is_iso_dghm by auto


text\<open>Rules.\<close>

lemma iso_digraphI':
  assumes "\<exists>\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "\<AA> \<approx>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms iso_digraph.intro by auto

lemma iso_digraphI:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "\<AA> \<approx>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms unfolding iso_digraph_def by auto

lemma iso_digraphD[dest]:
  assumes "\<AA> \<approx>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "\<exists>\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>" 
  using assms unfolding iso_digraph_def by simp_all

lemma iso_digraphE[elim]:
  assumes "\<AA> \<approx>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" 
  obtains \<FF> where "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by auto


subsubsection\<open>A digraph isomorphism is an equivalence relation\<close>

lemma iso_digraph_refl: 
  assumes "digraph \<alpha> \<AA>" 
  shows "\<AA> \<approx>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA>"
proof(rule iso_digraphI[of _ _ _ \<open>dghm_id \<AA>\<close>])
  interpret digraph \<alpha> \<AA> by (rule assms)
  show "dghm_id \<AA> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<AA>" by (rule dg_dghm_id_is_iso_dghm)
qed

lemma iso_digraph_sym[sym]:
  assumes "\<AA> \<approx>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "\<BB> \<approx>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA>"
proof-
  interpret iso_digraph \<alpha> \<AA> \<BB> by (rule assms)
  from iso_digraph_is_iso_dghm obtain \<FF> where "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<BB>" 
    by clarsimp
  then have "inv_dghm \<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<AA>" 
    by (simp add: is_iso_dghm_is_arr_isomorphism(1))
  then show ?thesis by (cs_concl cs_intro: dghm_cs_intros iso_digraphI)
qed

lemma iso_digraph_trans[trans]:
  assumes "\<AA> \<approx>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" and "\<BB> \<approx>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" 
  shows "\<AA> \<approx>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret L: iso_digraph \<alpha> \<AA> \<BB> by (rule assms(1))
  interpret R: iso_digraph \<alpha> \<BB> \<CC> by (rule assms(2))
  from L.iso_digraph_is_iso_dghm R.iso_digraph_is_iso_dghm show ?thesis 
    by (meson dghm_comp_is_iso_dghm iso_digraph.intro)
qed

text\<open>\newpage\<close>

end