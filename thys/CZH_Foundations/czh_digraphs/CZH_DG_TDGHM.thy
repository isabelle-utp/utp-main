(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Transformation of digraph homomorphisms\<close>
theory CZH_DG_TDGHM
  imports CZH_DG_DGHM
begin



subsection\<open>Background\<close>

named_theorems tdghm_cs_simps
named_theorems tdghm_cs_intros
named_theorems nt_field_simps

definition NTMap :: V where [nt_field_simps]: "NTMap = 0"
definition NTDom :: V where [nt_field_simps]: "NTDom = 1\<^sub>\<nat>"
definition NTCod :: V where [nt_field_simps]: "NTCod = 2\<^sub>\<nat>"
definition NTDGDom :: V where [nt_field_simps]: "NTDGDom = 3\<^sub>\<nat>"
definition NTDGCod :: V where [nt_field_simps]: "NTDGCod = 4\<^sub>\<nat>"



subsection\<open>Definition and elementary properties\<close>


text\<open>
A transformation of digraph homomorphisms, as presented in this work, 
is a generalization of the concept of a natural transformation, as presented in
Chapter I-4 in \cite{mac_lane_categories_2010}, to digraphs and digraph
homomorphisms. The generalization is performed by excluding the commutativity 
axiom from the definition. 

The definition of a transformation of digraph homomorphisms is 
parameterized by a limit ordinal \<open>\<alpha>\<close> such that \<open>\<omega> < \<alpha>\<close>. 
Such transformations of digraph homomorphisms are referred to either as
\<open>\<alpha>\<close>-transformations of digraph homomorphisms or 
transformations of \<open>\<alpha>\<close>-digraph homomorphisms.
\<close>

locale is_tdghm = 
  \<Z> \<alpha> + 
  vfsequence \<NN> + 
  NTDom: is_dghm \<alpha> \<AA> \<BB> \<FF> +
  NTCod: is_dghm \<alpha> \<AA> \<BB> \<GG> 
  for \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> +
  assumes tdghm_length[dg_cs_simps]: "vcard \<NN> = 5\<^sub>\<nat>"
    and tdghm_NTMap_vsv: "vsv (\<NN>\<lparr>NTMap\<rparr>)"
    and tdghm_NTMap_vdomain[dg_cs_simps]: "\<D>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    and tdghm_NTDom[dg_cs_simps]: "\<NN>\<lparr>NTDom\<rparr> = \<FF>"
    and tdghm_NTCod[dg_cs_simps]: "\<NN>\<lparr>NTCod\<rparr> = \<GG>"
    and tdghm_NTDGDom[dg_cs_simps]: "\<NN>\<lparr>NTDGDom\<rparr> = \<AA>"
    and tdghm_NTDGCod[dg_cs_simps]: "\<NN>\<lparr>NTDGCod\<rparr> = \<BB>"
    and tdghm_NTMap_is_arr: 
      "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<Longrightarrow> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"

syntax "_is_tdghm" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M _ :/ _ \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons>
  "CONST is_tdghm \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>"

abbreviation all_tdghms :: "V \<Rightarrow> V"
  where "all_tdghms \<alpha> \<equiv> set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation tdghms :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "tdghms \<alpha> \<AA> \<BB> \<equiv> set {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation these_tdghms :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "these_tdghms \<alpha> \<AA> \<BB> \<FF> \<GG> \<equiv> set {\<NN>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>}"

sublocale is_tdghm \<subseteq> NTMap: vsv \<open>\<NN>\<lparr>NTMap\<rparr>\<close>
  rewrites "\<D>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
  by (rule tdghm_NTMap_vsv) (simp add: dg_cs_simps)

lemmas [dg_cs_simps] =  
  is_tdghm.tdghm_length
  is_tdghm.tdghm_NTMap_vdomain
  is_tdghm.tdghm_NTDom
  is_tdghm.tdghm_NTCod
  is_tdghm.tdghm_NTDGDom
  is_tdghm.tdghm_NTDGCod

lemma (in is_tdghm) tdghm_NTMap_is_arr'[dg_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "A = \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "B = \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
  shows "\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : A \<mapsto>\<^bsub>\<BB>\<^esub> B"
  using assms(1) unfolding assms(2,3) by (rule tdghm_NTMap_is_arr)

lemmas [dg_cs_intros] = is_tdghm.tdghm_NTMap_is_arr'


text\<open>Rules.\<close>

lemma (in is_tdghm) is_tdghm_axioms'[dg_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>" and "\<FF>' = \<FF>" and "\<GG>' = \<GG>"
  shows "\<NN> : \<FF>' \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_tdghm_axioms)

mk_ide rf is_tdghm_def[unfolded is_tdghm_axioms_def]
  |intro is_tdghmI|
  |dest is_tdghmD[dest]|
  |elim is_tdghmE[elim]|

lemmas [dg_cs_intros] =
  is_tdghmD(3,4)


text\<open>Elementary properties.\<close>

lemma tdghm_eqI:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN>' : \<FF>' \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>'"
    and "\<NN>\<lparr>NTMap\<rparr> = \<NN>'\<lparr>NTMap\<rparr>"
    and "\<FF> = \<FF>'"
    and "\<GG> = \<GG>'"
    and "\<AA> = \<AA>'"
    and "\<BB> = \<BB>'"
  shows "\<NN> = \<NN>'"
proof-
  interpret L: is_tdghm \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret R: is_tdghm \<alpha> \<AA>' \<BB>' \<FF>' \<GG>' \<NN>' by (rule assms(2))
  show ?thesis
  proof(rule vsv_eqI)
    have dom: "\<D>\<^sub>\<circ> \<NN> = 5\<^sub>\<nat>" by (cs_concl cs_simp: dg_cs_simps V_cs_simps)
    show "\<D>\<^sub>\<circ> \<NN> = \<D>\<^sub>\<circ> \<NN>'" by (cs_concl cs_simp: dg_cs_simps V_cs_simps)
    from assms(4-7) have sup: 
      "\<NN>\<lparr>NTDom\<rparr> = \<NN>'\<lparr>NTDom\<rparr>" "\<NN>\<lparr>NTCod\<rparr> = \<NN>'\<lparr>NTCod\<rparr>" 
      "\<NN>\<lparr>NTDGDom\<rparr> = \<NN>'\<lparr>NTDGDom\<rparr>" "\<NN>\<lparr>NTDGCod\<rparr> = \<NN>'\<lparr>NTDGCod\<rparr>" 
      by (simp_all add: dg_cs_simps)
    show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<NN> \<Longrightarrow> \<NN>\<lparr>a\<rparr> = \<NN>'\<lparr>a\<rparr>" for a 
      by (unfold dom, elim_in_numeral, insert assms(3) sup)
        (auto simp: nt_field_simps)
  qed (auto simp: L.vsv_axioms R.vsv_axioms)
qed

lemma (in is_tdghm) tdghm_def:
  "\<NN> = [\<NN>\<lparr>NTMap\<rparr>, \<NN>\<lparr>NTDom\<rparr>, \<NN>\<lparr>NTCod\<rparr>, \<NN>\<lparr>NTDGDom\<rparr>, \<NN>\<lparr>NTDGCod\<rparr>]\<^sub>\<circ>"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> \<NN> = 5\<^sub>\<nat>" by (cs_concl cs_simp: dg_cs_simps V_cs_simps)
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

lemma (in is_tdghm) tdghm_NTMap_app_in_Arr[dg_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
  using assms using tdghm_NTMap_is_arr by auto

lemmas [dg_cs_intros] = is_tdghm.tdghm_NTMap_app_in_Arr

lemma (in is_tdghm) tdghm_NTMap_vrange_vifunion:
  "\<R>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>). \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> (\<GG>\<lparr>ObjMap\<rparr>). Hom \<BB> a b)"
proof(intro NTMap.vsv_vrange_vsubset)
  fix x assume prems: "x \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  note \<NN>x = tdghm_NTMap_is_arr[OF prems]
  from prems show 
    "\<NN>\<lparr>NTMap\<rparr>\<lparr>x\<rparr> \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>). \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> (\<GG>\<lparr>ObjMap\<rparr>). Hom \<BB> a b)"
    by (intro vifunionI, unfold in_Hom_iff) 
      (
        auto intro: 
          dg_cs_intros NTDom.ObjMap.vsv_vimageI2' NTCod.ObjMap.vsv_vimageI2' 
      )
qed

lemma (in is_tdghm) tdghm_NTMap_vrange: "\<R>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
proof(intro NTMap.vsv_vrange_vsubset)
  fix x assume "x \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  with is_tdghm_axioms show "\<NN>\<lparr>NTMap\<rparr>\<lparr>x\<rparr> \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
qed


text\<open>Size.\<close>

lemma (in is_tdghm) tdghm_NTMap_vsubset_Vset: "\<NN>\<lparr>NTMap\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
proof(intro NTMap.vbrelation_Limit_vsubset_VsetI)
  show "\<R>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    by 
      (
        rule vsubset_transitive, 
        rule tdghm_NTMap_vrange,
        rule NTDom.HomCod.dg_Arr_vsubset_Vset
      )
qed (simp_all add: NTDom.HomDom.dg_Obj_vsubset_Vset)

lemma (in is_tdghm) tdghm_NTMap_in_Vset: 
  assumes "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<NN>\<lparr>NTMap\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
  by (meson assms tdghm_NTMap_vsubset_Vset Vset_in_mono vsubset_in_VsetI)

lemma (in is_tdghm) tdghm_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<NN> \<in>\<^sub>\<circ> Vset \<beta>"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  note [dg_cs_intros] = 
    tdghm_NTMap_in_Vset
    NTDom.dghm_in_Vset
    NTCod.dghm_in_Vset
    NTDom.HomDom.dg_in_Vset
    NTDom.HomCod.dg_in_Vset
  from assms(2) show ?thesis
    by (subst tdghm_def) 
      (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros V_cs_intros)
qed

lemma (in is_tdghm) tdghm_is_tdghm_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<beta>\<^esub> \<BB>"
proof(rule is_tdghmI)
  show "\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>" if "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" for a
    using that by (cs_concl cs_intro: dg_cs_intros)
qed 
  (
    cs_concl 
      cs_simp: dg_cs_simps 
      cs_intro:
        V_cs_intros
        assms 
        NTDom.dghm_is_dghm_if_ge_Limit 
        NTCod.dghm_is_dghm_if_ge_Limit  
   )+

lemma small_all_tdghms[simp]: 
  "small {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(cases \<open>\<Z> \<alpha>\<close>)
  case True
  from is_tdghm.tdghm_in_Vset show ?thesis
    by (intro down[of _ \<open>Vset (\<alpha> + \<omega>)\<close>]) 
      (auto simp: True \<Z>.\<Z>_Limit_\<alpha>\<omega> \<Z>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>.intro \<Z>.\<Z>_\<alpha>_\<alpha>\<omega>)
next
  case False
  then have "{\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>} = {}" by auto
  then show ?thesis by simp
qed

lemma small_tdghms[simp]: "small {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>}"
  by (rule down[of _ \<open>set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>}\<close>])
    auto

lemma small_these_tdghms[simp]: "small {\<NN>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>}"
  by (rule down[of _ \<open>set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>}\<close>]) 
    auto


text\<open>Further elementary results.\<close>

lemma these_tdghms_iff(*not simp*): 
  "\<NN> \<in>\<^sub>\<circ> these_tdghms \<alpha> \<AA> \<BB> \<FF> \<GG> \<longleftrightarrow> \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  by auto



subsection\<open>Opposite transformation of digraph homomorphisms\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See section 1.5 in \cite{bodo_categories_1970}.\<close>

definition op_tdghm :: "V \<Rightarrow> V"
  where "op_tdghm \<NN> =
    [
      \<NN>\<lparr>NTMap\<rparr>,
      op_dghm (\<NN>\<lparr>NTCod\<rparr>),
      op_dghm (\<NN>\<lparr>NTDom\<rparr>),
      op_dg (\<NN>\<lparr>NTDGDom\<rparr>),
      op_dg (\<NN>\<lparr>NTDGCod\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma op_tdghm_components[dg_op_simps]:
  shows "op_tdghm \<NN>\<lparr>NTMap\<rparr> = \<NN>\<lparr>NTMap\<rparr>"
    and "op_tdghm \<NN>\<lparr>NTDom\<rparr> = op_dghm (\<NN>\<lparr>NTCod\<rparr>)"
    and "op_tdghm \<NN>\<lparr>NTCod\<rparr> = op_dghm (\<NN>\<lparr>NTDom\<rparr>)"
    and "op_tdghm \<NN>\<lparr>NTDGDom\<rparr> = op_dg (\<NN>\<lparr>NTDGDom\<rparr>)"
    and "op_tdghm \<NN>\<lparr>NTDGCod\<rparr> = op_dg (\<NN>\<lparr>NTDGCod\<rparr>)"
  unfolding op_tdghm_def nt_field_simps by (auto simp: nat_omega_simps)


subsubsection\<open>Further properties\<close>

lemma (in is_tdghm) is_tdghm_op: 
  "op_tdghm \<NN> : op_dghm \<GG> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M op_dghm \<FF> : op_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> op_dg \<BB>"
proof(rule is_tdghmI, unfold dg_op_simps)
  show "vfsequence (op_tdghm \<NN>)" by (simp add: op_tdghm_def)
  show "vcard (op_tdghm \<NN>) = 5\<^sub>\<nat>" by (simp add: op_tdghm_def nat_omega_simps)
  show "\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>" if "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" for a
    using that by (cs_concl cs_intro: dg_cs_intros)
qed 
  (
    cs_concl 
      cs_simp: dg_cs_simps cs_intro: dg_cs_intros dg_op_intros V_cs_intros
  )+

lemma (in is_tdghm) is_tdghm_op'[dg_op_intros]: 
  assumes "\<GG>' = op_dghm \<GG>"
    and "\<FF>' = op_dghm \<FF>"
    and "\<AA>' = op_dg \<AA>"
    and "\<BB>' = op_dg \<BB>"
  shows "op_tdghm \<NN> : \<GG>' \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>' : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule is_tdghm_op)

lemmas is_tdghm_op[dg_op_intros] = is_tdghm.is_tdghm_op'

lemma (in is_tdghm) tdghm_op_tdghm_op_tdghm[dg_op_simps]: 
  "op_tdghm (op_tdghm \<NN>) = \<NN>"
proof(rule tdghm_eqI[of \<alpha> \<AA> \<BB> \<FF> \<GG> _ \<AA> \<BB> \<FF> \<GG>], unfold dg_op_simps)
  interpret op: 
    is_tdghm \<alpha> \<open>op_dg \<AA>\<close> \<open>op_dg \<BB>\<close> \<open>op_dghm \<GG>\<close> \<open>op_dghm \<FF>\<close> \<open>op_tdghm \<NN>\<close>
    by (rule is_tdghm_op)
  from op.is_tdghm_op show 
    "op_tdghm (op_tdghm \<NN>) : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
    by (simp add: dg_op_simps)
qed (auto simp: dg_cs_intros)

lemmas tdghm_op_tdghm_op_tdghm[dg_op_simps] = 
  is_tdghm.tdghm_op_tdghm_op_tdghm

lemma eq_op_tdghm_iff: 
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<NN>' : \<FF>' \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>'"
  shows "op_tdghm \<NN> = op_tdghm \<NN>' \<longleftrightarrow> \<NN> = \<NN>'"
proof
  interpret L: is_tdghm \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret R: is_tdghm \<alpha> \<AA>' \<BB>' \<FF>' \<GG>' \<NN>' by (rule assms(2))
  assume prems: "op_tdghm \<NN> = op_tdghm \<NN>'"
  show "\<NN> = \<NN>'"
  proof(rule tdghm_eqI[OF assms])
    from prems L.tdghm_op_tdghm_op_tdghm R.tdghm_op_tdghm_op_tdghm show 
      "\<NN>\<lparr>NTMap\<rparr> = \<NN>'\<lparr>NTMap\<rparr>"
      by metis+
    from prems L.tdghm_op_tdghm_op_tdghm R.tdghm_op_tdghm_op_tdghm 
    have "\<NN>\<lparr>NTDom\<rparr> = \<NN>'\<lparr>NTDom\<rparr>" 
      and "\<NN>\<lparr>NTCod\<rparr> = \<NN>'\<lparr>NTCod\<rparr>" 
      and "\<NN>\<lparr>NTDGDom\<rparr> = \<NN>'\<lparr>NTDGDom\<rparr>" 
      and "\<NN>\<lparr>NTDGCod\<rparr> = \<NN>'\<lparr>NTDGCod\<rparr>" 
      by metis+
    then show "\<FF> = \<FF>'" "\<GG> = \<GG>'" "\<AA> = \<AA>'" "\<BB> = \<BB>'" by (auto simp: dg_cs_simps)
  qed
qed auto



subsection\<open>
Composition of a transformation of digraph homomorphisms 
and a digraph homomorphism
\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition tdghm_dghm_comp :: "V \<Rightarrow> V \<Rightarrow> V" (infixl \<open>\<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<close> 55)
  where "\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH> =
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<HH>\<lparr>HomDom\<rparr>\<lparr>Obj\<rparr>. \<NN>\<lparr>NTMap\<rparr>\<lparr>\<HH>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>),
      \<NN>\<lparr>NTDom\<rparr> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>,
      \<NN>\<lparr>NTCod\<rparr> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>,
      \<HH>\<lparr>HomDom\<rparr>,
      \<NN>\<lparr>NTDGCod\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma tdghm_dghm_comp_components:
  shows "(\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>)\<lparr>NTMap\<rparr> =
    (\<lambda>a\<in>\<^sub>\<circ>\<HH>\<lparr>HomDom\<rparr>\<lparr>Obj\<rparr>. \<NN>\<lparr>NTMap\<rparr>\<lparr>\<HH>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>)"
    and [dg_shared_cs_simps, dg_cs_simps]: 
      "(\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>)\<lparr>NTDom\<rparr> = \<NN>\<lparr>NTDom\<rparr> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>"
    and [dg_shared_cs_simps, dg_cs_simps]: 
      "(\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>)\<lparr>NTCod\<rparr> = \<NN>\<lparr>NTCod\<rparr> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>"
    and [dg_shared_cs_simps, dg_cs_simps]: 
      "(\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>)\<lparr>NTDGDom\<rparr> = \<HH>\<lparr>HomDom\<rparr>"
    and [dg_shared_cs_simps, dg_cs_simps]: 
      "(\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>)\<lparr>NTDGCod\<rparr> = \<NN>\<lparr>NTDGCod\<rparr>"
  unfolding tdghm_dghm_comp_def nt_field_simps 
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Transformation map\<close>

mk_VLambda tdghm_dghm_comp_components(1)
  |vsv tdghm_dghm_comp_NTMap_vsv[dg_shared_cs_intros, dg_cs_intros]|

mk_VLambda (in is_dghm) 
  tdghm_dghm_comp_components(1)[where \<HH>=\<FF>, unfolded dghm_HomDom]
  |vdomain tdghm_dghm_comp_NTMap_vdomain|
  |app tdghm_dghm_comp_NTMap_app|

lemmas [dg_cs_simps] = 
  is_dghm.tdghm_dghm_comp_NTMap_vdomain
  is_dghm.tdghm_dghm_comp_NTMap_app

lemma tdghm_dghm_comp_NTMap_vrange: 
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>)\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof-
  interpret \<NN>: is_tdghm \<alpha> \<BB> \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<HH>: is_dghm \<alpha> \<AA> \<BB> \<HH> by (rule assms(2))
  show ?thesis 
    unfolding tdghm_dghm_comp_components
  proof(rule vrange_VLambda_vsubset, unfold dg_cs_simps)
    fix x assume "x \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    then show "\<NN>\<lparr>NTMap\<rparr>\<lparr>\<HH>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr>\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
      by (cs_concl cs_intro: dg_cs_intros)
  qed
qed


subsubsection\<open>
Opposite of the composition of a transformation of 
digraph homomorphisms and a digraph homomorphism
\<close>

lemma op_tdghm_tdghm_dghm_comp[dg_op_simps]: 
  "op_tdghm (\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>) = op_tdghm \<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M op_dghm \<HH>"
  unfolding 
    tdghm_dghm_comp_def 
    dghm_comp_def 
    op_tdghm_def 
    op_dghm_def 
    op_dg_def
    dg_field_simps
    dghm_field_simps
    nt_field_simps
  by (simp add: nat_omega_simps) (*slow*)


subsubsection\<open>
Composition of a transformation of digraph homomorphisms and a digraph
homomorphism is a transformation of digraph homomorphisms
\<close>

lemma tdghm_dghm_comp_is_tdghm:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH> : \<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<NN>: is_tdghm \<alpha> \<BB> \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<HH>: is_dghm \<alpha> \<AA> \<BB> \<HH> by (rule assms(2))
  show ?thesis
  proof(rule is_tdghmI)
    show "vfsequence (\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>)" unfolding tdghm_dghm_comp_def by simp
    show "vcard (\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>) = 5\<^sub>\<nat>"
      unfolding tdghm_dghm_comp_def by (simp add: nat_omega_simps)
    show "(\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> :
      (\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" for a
      using that by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  qed (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)+
qed

lemma tdghm_dghm_comp_is_tdghm'[dg_cs_intros]:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF>' = \<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>"
    and "\<GG>' = \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>"
  shows "\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH> : \<FF>' \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1,2) unfolding assms(3,4) by (rule tdghm_dghm_comp_is_tdghm)


subsubsection\<open>Further properties\<close>

lemma tdghm_dghm_comp_tdghm_dghm_comp_assoc:
  assumes "\<NN> : \<HH> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>' : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<DD>" 
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "(\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>) \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> = \<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)"
proof-
  interpret \<NN>: is_tdghm \<alpha> \<CC> \<DD> \<HH> \<HH>' \<NN> by (rule assms(1))
  interpret \<GG>: is_dghm \<alpha> \<BB> \<CC> \<GG> by (rule assms(2))
  interpret \<FF>: is_dghm \<alpha> \<AA> \<BB> \<FF> by (rule assms(3))
  show ?thesis  
  proof(rule tdghm_eqI)
    from assms show 
      "(\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>) \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> :
        \<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>' \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> :
        \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<DD>"
      by (cs_concl cs_intro: dg_cs_intros)
    then have dom_lhs: "\<D>\<^sub>\<circ> (((\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>) \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: dg_cs_simps)
    show "\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>) :
      \<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>' \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> :
      \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<DD>"
      by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
    then have dom_rhs: "\<D>\<^sub>\<circ> ((\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>))\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: dg_cs_simps)
    show 
      "((\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>) \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>NTMap\<rparr> = 
        (\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>))\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
      with assms show 
        "((\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>) \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
          (\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>))\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
    qed (cs_concl cs_intro: dg_cs_intros)
  qed simp_all
qed

lemma (in is_tdghm) tdghm_tdghm_dghm_comp_dghm_id[dg_cs_simps]:
  "\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_id \<AA> = \<NN>"
proof(rule tdghm_eqI)
  show "\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_id \<AA> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  show "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  have dom_lhs: "\<D>\<^sub>\<circ> ((\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_id \<AA>)\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  show "(\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_id \<AA>)\<lparr>NTMap\<rparr> = \<NN>\<lparr>NTMap\<rparr>"
  proof(rule vsv_eqI, unfold dom_lhs dg_cs_simps)
    fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    then show "(\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_id \<AA>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  qed (cs_concl cs_intro: dg_cs_intros V_cs_intros)+
qed simp_all

lemmas [dg_cs_simps] = is_tdghm.tdghm_tdghm_dghm_comp_dghm_id



subsection\<open>
Composition of a digraph homomorphism and a transformation of
digraph homomorphisms
\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition dghm_tdghm_comp :: "V \<Rightarrow> V \<Rightarrow> V" (infixl \<open>\<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<close> 55)
  where "\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN> =
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<NN>\<lparr>NTDGDom\<rparr>\<lparr>Obj\<rparr>. \<HH>\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr>),
      \<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>\<lparr>NTDom\<rparr>,
      \<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>\<lparr>NTCod\<rparr>,
      \<NN>\<lparr>NTDGDom\<rparr>,
      \<HH>\<lparr>HomCod\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dghm_tdghm_comp_components:
  shows "(\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>)\<lparr>NTMap\<rparr> =
    (\<lambda>a\<in>\<^sub>\<circ>\<NN>\<lparr>NTDGDom\<rparr>\<lparr>Obj\<rparr>. \<HH>\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<rparr>)"
    and [dg_shared_cs_simps, dg_cs_simps]: 
      "(\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>)\<lparr>NTDom\<rparr> = \<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>\<lparr>NTDom\<rparr>"
    and [dg_shared_cs_simps, dg_cs_simps]: 
      "(\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>)\<lparr>NTCod\<rparr> = \<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>\<lparr>NTCod\<rparr>"
    and [dg_shared_cs_simps, dg_cs_simps]: 
      "(\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>)\<lparr>NTDGDom\<rparr> = \<NN>\<lparr>NTDGDom\<rparr>"
    and [dg_shared_cs_simps, dg_cs_simps]: 
      "(\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>)\<lparr>NTDGCod\<rparr> = \<HH>\<lparr>HomCod\<rparr>"
  unfolding dghm_tdghm_comp_def nt_field_simps 
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Transformation map\<close>

mk_VLambda dghm_tdghm_comp_components(1)
  |vsv dghm_tdghm_comp_NTMap_vsv[dg_shared_cs_intros, dg_cs_intros]|

mk_VLambda (in is_tdghm) 
  dghm_tdghm_comp_components(1)[where \<NN>=\<NN>, unfolded tdghm_NTDGDom]
  |vdomain dghm_tdghm_comp_NTMap_vdomain|
  |app dghm_tdghm_comp_NTMap_app|

lemmas [dg_cs_simps] = 
  is_tdghm.dghm_tdghm_comp_NTMap_vdomain
  is_tdghm.dghm_tdghm_comp_NTMap_app

lemma dghm_tdghm_comp_NTMap_vrange: 
  assumes "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" and "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<R>\<^sub>\<circ> ((\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>)\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof-
  interpret \<HH>: is_dghm \<alpha> \<BB> \<CC> \<HH> by (rule assms(1))
  interpret \<NN>: is_tdghm \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  show ?thesis 
    unfolding dghm_tdghm_comp_components
  proof(rule vrange_VLambda_vsubset, unfold dg_cs_simps)
    fix x assume "x \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    then show "\<HH>\<lparr>ArrMap\<rparr>\<lparr>\<NN>\<lparr>NTMap\<rparr>\<lparr>x\<rparr>\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
      by (cs_concl cs_intro: dg_cs_intros)
  qed
qed


subsubsection\<open>
Opposite of the composition of a digraph homomorphism 
and a transformation of digraph homomorphisms
\<close>

lemma op_tdghm_dghm_tdghm_comp[dg_op_simps]: 
  "op_tdghm (\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>) = op_dghm \<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M op_tdghm \<NN>"
  unfolding 
    dghm_tdghm_comp_def
    dghm_comp_def
    op_tdghm_def
    op_dghm_def
    op_dg_def
    dg_field_simps
    dghm_field_simps
    nt_field_simps
  by (simp add: nat_omega_simps) (*slow*)


subsubsection\<open>
Composition of a digraph homomorphism and a transformation of
digraph homomorphisms is a transformation of digraph homomorphisms
\<close>

lemma dghm_tdghm_comp_is_tdghm:
  assumes "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>" and "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN> : \<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<HH>: is_dghm \<alpha> \<BB> \<CC> \<HH> by (rule assms(1))
  interpret \<NN>: is_tdghm \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  show ?thesis
  proof(rule is_tdghmI)
    show "vfsequence (\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>)"
      unfolding dghm_tdghm_comp_def by simp
    show "vcard (\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>) = 5\<^sub>\<nat>"
      unfolding dghm_tdghm_comp_def  by (simp add: nat_omega_simps)
    show "(\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : 
      (\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> (\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" for a
      using that by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  qed (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)+
qed

lemma dghm_tdghm_comp_is_tdghm'[dg_cs_intros]:
  assumes "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF>' = \<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>"
    and "\<GG>' = \<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>"
  shows "\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN> : \<FF>' \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1,2) unfolding assms(3,4) by (rule dghm_tdghm_comp_is_tdghm)


subsubsection\<open>Further properties\<close>

lemma dghm_comp_dghm_tdghm_comp_assoc:
  assumes "\<NN> : \<HH> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>' : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>) \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN> = \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M (\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>)"
proof(rule tdghm_eqI)
  interpret \<NN>: is_tdghm \<alpha> \<AA> \<BB> \<HH> \<HH>' \<NN> by (rule assms(1))
  interpret \<FF>: is_dghm \<alpha> \<BB> \<CC> \<FF> by (rule assms(2))
  interpret \<GG>: is_dghm \<alpha> \<CC> \<DD> \<GG> by (rule assms(3))
  from assms show "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>) \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN> :
    \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>' : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<DD>"
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  then have dom_lhs: "\<D>\<^sub>\<circ> ((\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>)\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: dg_cs_simps)
  from assms show "\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M (\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>) :
    \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>' : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<DD>"
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  then have dom_rhs: 
    "\<D>\<^sub>\<circ> ((\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M (\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>))\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: dg_cs_simps)
  show 
    "((\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>) \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>)\<lparr>NTMap\<rparr> = 
      (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M (\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>))\<lparr>NTMap\<rparr>"
  proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
    fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    then show 
      "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
        (\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M (\<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>))\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  qed (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)+
qed simp_all

lemma (in is_tdghm) tdghm_dghm_tdghm_comp_dghm_id[dg_cs_simps]:
  "dghm_id \<BB> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN> = \<NN>"
proof(rule tdghm_eqI)
  show "dghm_id \<BB> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  then have dom_lhs: "\<D>\<^sub>\<circ> ((dghm_id \<BB> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>)\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: dg_cs_simps)
  show "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  show "(dghm_id \<BB> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>)\<lparr>NTMap\<rparr> = \<NN>\<lparr>NTMap\<rparr>"
  proof(rule vsv_eqI, unfold dom_lhs dg_cs_simps)
    show "vsv (\<NN>\<lparr>NTMap\<rparr>)" by auto
    fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    then show "(dghm_id \<BB> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  qed (cs_concl cs_intro: dg_cs_intros)+
qed simp_all

lemmas [dg_cs_simps] = is_tdghm.tdghm_dghm_tdghm_comp_dghm_id

lemma dghm_tdghm_comp_tdghm_dghm_comp_assoc:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<KK> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "(\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>) \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<KK> = \<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M (\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<KK>)"
proof-
  interpret \<NN>: is_tdghm \<alpha> \<BB> \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<HH>: is_dghm \<alpha> \<CC> \<DD> \<HH> by (rule assms(2))
  interpret \<KK>: is_dghm \<alpha> \<AA> \<BB> \<KK> by (rule assms(3))
  show ?thesis
  proof(rule tdghm_eqI)
    from assms have dom_lhs: 
      "\<D>\<^sub>\<circ> (((\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>) \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<KK>)\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: dg_cs_simps)
    from assms have dom_rhs: 
      "\<D>\<^sub>\<circ> ((\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M (\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<KK>))\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
    show 
      "((\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>) \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<KK>)\<lparr>NTMap\<rparr> =
        (\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M (\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<KK>))\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
      then show 
        "((\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN>) \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<KK>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
          ((\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M (\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<KK>)))\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
    qed (cs_concl cs_intro: dg_cs_intros)
  qed (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)+
qed

text\<open>\newpage\<close>

end