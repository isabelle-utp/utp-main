(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Universal arrow\<close>
theory CZH_UCAT_Universal
  imports 
    CZH_UCAT_Introduction
    CZH_Elementary_Categories.CZH_ECAT_FUNCT
    CZH_Elementary_Categories.CZH_ECAT_Set
    CZH_Elementary_Categories.CZH_ECAT_Hom
begin



subsection\<open>Background\<close>


text\<open>
The following section is based, primarily, on the elements of the content 
of Chapter III-1 in \cite{mac_lane_categories_2010}.
\<close>



subsection\<open>Universal map\<close>


text\<open>
The universal map is a convenience utility that allows treating 
a part of the definition of the universal arrow as an arrow in the
category \<open>Set\<close>.
\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition umap_of :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "umap_of \<FF> c r u d =
    [
      (\<lambda>f'\<in>\<^sub>\<circ>Hom (\<FF>\<lparr>HomDom\<rparr>) r d. \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>\<FF>\<lparr>HomCod\<rparr>\<^esub> u),
      Hom (\<FF>\<lparr>HomDom\<rparr>) r d,
      Hom (\<FF>\<lparr>HomCod\<rparr>) c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>)
    ]\<^sub>\<circ>"

definition umap_fo :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "umap_fo \<FF> c r u d = umap_of (op_cf \<FF>) c r u d"


text\<open>Components.\<close>

lemma (in is_functor) umap_of_components:
  assumes "u : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>" (*do not remove*)
  shows "umap_of \<FF> c r u d\<lparr>ArrVal\<rparr> = (\<lambda>f'\<in>\<^sub>\<circ>Hom \<AA> r d. \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> u)"
    and "umap_of \<FF> c r u d\<lparr>ArrDom\<rparr> = Hom \<AA> r d"
    and "umap_of \<FF> c r u d\<lparr>ArrCod\<rparr> = Hom \<BB> c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>)"
  unfolding umap_of_def arr_field_simps
  by (simp_all add: cat_cs_simps nat_omega_simps)

lemma (in is_functor) umap_fo_components:
  assumes "u : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> c"
  shows "umap_fo \<FF> c r u d\<lparr>ArrVal\<rparr> = (\<lambda>f'\<in>\<^sub>\<circ>Hom \<AA> d r. u \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>)"
    and "umap_fo \<FF> c r u d\<lparr>ArrDom\<rparr> = Hom \<AA> d r"
    and "umap_fo \<FF> c r u d\<lparr>ArrCod\<rparr> = Hom \<BB> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>) c"
  unfolding 
    umap_fo_def 
    is_functor.umap_of_components[
      OF is_functor_op, unfolded cat_op_simps, OF assms
      ] 
proof(rule vsv_eqI)
  fix f' assume "f' \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<lambda>f'\<in>\<^sub>\<circ>Hom \<AA> d r. \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<BB>\<^esub> u)"
  then have f': "f' : d \<mapsto>\<^bsub>\<AA>\<^esub> r" by simp
  then have \<FF>f': "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>" 
    by (auto intro: cat_cs_intros)
  from f' show 
    "(\<lambda>f'\<in>\<^sub>\<circ>Hom \<AA> d r. \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<BB>\<^esub> u)\<lparr>f'\<rparr> = 
      (\<lambda>f'\<in>\<^sub>\<circ>Hom \<AA> d r. u \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>)\<lparr>f'\<rparr>"
    by (simp add: HomCod.op_cat_Comp[OF assms \<FF>f'])
qed simp_all


text\<open>Universal maps for the opposite functor.\<close>

lemma (in is_functor) op_umap_of[cat_op_simps]: "umap_of (op_cf \<FF>) = umap_fo \<FF>"
  unfolding umap_fo_def by simp 

lemma (in is_functor) op_umap_fo[cat_op_simps]: "umap_fo (op_cf \<FF>) = umap_of \<FF>"
  unfolding umap_fo_def by (simp add: cat_op_simps)

lemmas [cat_op_simps] = 
  is_functor.op_umap_of
  is_functor.op_umap_fo


subsubsection\<open>Arrow value\<close>

lemma umap_of_ArrVal_vsv[cat_cs_intros]: "vsv (umap_of \<FF> c r u d\<lparr>ArrVal\<rparr>)"
  unfolding umap_of_def arr_field_simps by (simp add: nat_omega_simps)

lemma umap_fo_ArrVal_vsv[cat_cs_intros]: "vsv (umap_fo \<FF> c r u d\<lparr>ArrVal\<rparr>)"
  unfolding umap_fo_def by (rule umap_of_ArrVal_vsv)

lemma (in is_functor) umap_of_ArrVal_vdomain: 
  assumes "u : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
  shows "\<D>\<^sub>\<circ> (umap_of \<FF> c r u d\<lparr>ArrVal\<rparr>) = Hom \<AA> r d"
  unfolding umap_of_components[OF assms] by simp

lemmas [cat_cs_simps] = is_functor.umap_of_ArrVal_vdomain

lemma (in is_functor) umap_fo_ArrVal_vdomain:
  assumes "u : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> c"
  shows "\<D>\<^sub>\<circ> (umap_fo \<FF> c r u d\<lparr>ArrVal\<rparr>) = Hom \<AA> d r"
  unfolding umap_fo_components[OF assms] by simp

lemmas [cat_cs_simps] = is_functor.umap_fo_ArrVal_vdomain

lemma (in is_functor) umap_of_ArrVal_app: 
  assumes "f' : r \<mapsto>\<^bsub>\<AA>\<^esub> d" and "u : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
  shows "umap_of \<FF> c r u d\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> u"
  using assms(1) unfolding umap_of_components[OF assms(2)] by simp

lemmas [cat_cs_simps] = is_functor.umap_of_ArrVal_app

lemma (in is_functor) umap_fo_ArrVal_app: 
  assumes "f' : d \<mapsto>\<^bsub>\<AA>\<^esub> r" and "u : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> c"
  shows "umap_fo \<FF> c r u d\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr> = u \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>"
proof-
  from assms have "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>" 
    by (auto intro: cat_cs_intros)
  from this assms(2) have \<FF>f'[simp]:
    "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<BB>\<^esub> u = u \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>"
    by (simp add: cat_op_simps)
  from
    is_functor_axioms
    is_functor.umap_of_ArrVal_app[
      OF is_functor_op, unfolded cat_op_simps, 
      OF assms
      ] 
  show ?thesis
    by (simp add: cat_op_simps cat_cs_simps)
qed

lemmas [cat_cs_simps] = is_functor.umap_fo_ArrVal_app

lemma (in is_functor) umap_of_ArrVal_vrange: 
  assumes "u : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
  shows "\<R>\<^sub>\<circ> (umap_of \<FF> c r u d\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> Hom \<BB> c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>)"
proof(intro vsubset_antisym vsubsetI)
  interpret vsv \<open>umap_of \<FF> c r u d\<lparr>ArrVal\<rparr>\<close> 
    unfolding umap_of_components[OF assms] by simp
  fix g assume "g \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (umap_of \<FF> c r u d\<lparr>ArrVal\<rparr>)"
  then obtain f' 
    where g_def: "g = umap_of \<FF> c r u d\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>" 
      and f': "f' \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (umap_of \<FF> c r u d\<lparr>ArrVal\<rparr>)"
    unfolding umap_of_components[OF assms] by auto
  then have f': "f' : r \<mapsto>\<^bsub>\<AA>\<^esub> d" 
    unfolding umap_of_ArrVal_vdomain[OF assms] by simp
  then have \<FF>f': "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>" 
    by (auto intro!: cat_cs_intros)
  have g_def: "g = \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> u"
    unfolding g_def umap_of_ArrVal_app[OF f' assms]..
  from \<FF>f' assms show "g \<in>\<^sub>\<circ> Hom \<BB> c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>)" 
    unfolding g_def by (auto intro: cat_cs_intros)
qed

lemma (in is_functor) umap_fo_ArrVal_vrange: 
  assumes "u : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> c"
  shows "\<R>\<^sub>\<circ> (umap_fo \<FF> c r u d\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> Hom \<BB> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>) c"
  by 
    (
      rule is_functor.umap_of_ArrVal_vrange[
        OF is_functor_op, unfolded cat_op_simps, OF assms, folded umap_fo_def
        ]
    )


subsubsection\<open>Universal map is an arrow in the category \<open>Set\<close>\<close>

lemma (in is_functor) cf_arr_Set_umap_of: 
  assumes "category \<alpha> \<AA>" 
    and "category \<alpha> \<BB>" 
    and r: "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and d: "d \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and u: "u : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
  shows "arr_Set \<alpha> (umap_of \<FF> c r u d)"
proof(intro arr_SetI)
  interpret HomDom: category \<alpha> \<AA> by (rule assms(1))
  interpret HomCod: category \<alpha> \<BB> by (rule assms(2))
  note umap_of_components = umap_of_components[OF u]
  from u d have c: "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and \<FF>d: "(\<FF>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>) \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
    by (auto intro: cat_cs_intros)
  show "vfsequence (umap_of \<FF> c r u d)" unfolding umap_of_def by simp
  show "vcard (umap_of \<FF> c r u d) = 3\<^sub>\<nat>"
    unfolding umap_of_def by (simp add: nat_omega_simps)
  from umap_of_ArrVal_vrange[OF u] show 
    "\<R>\<^sub>\<circ> (umap_of \<FF> c r u d\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> umap_of \<FF> c r u d\<lparr>ArrCod\<rparr>"
    unfolding umap_of_components by simp
  from r d show "umap_of \<FF> c r u d\<lparr>ArrDom\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    unfolding umap_of_components by (intro HomDom.cat_Hom_in_Vset)
  from c \<FF>d show "umap_of \<FF> c r u d\<lparr>ArrCod\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    unfolding umap_of_components by (intro HomCod.cat_Hom_in_Vset)
qed (auto simp: umap_of_components[OF u])

lemma (in is_functor) cf_arr_Set_umap_fo: 
  assumes "category \<alpha> \<AA>" 
    and "category \<alpha> \<BB>" 
    and r: "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and d: "d \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and u: "u : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> c"
  shows "arr_Set \<alpha> (umap_fo \<FF> c r u d)"
proof-
  from assms(1) have \<AA>: "category \<alpha> (op_cat \<AA>)" 
    by (auto intro: cat_cs_intros)
  from assms(2) have \<BB>: "category \<alpha> (op_cat \<BB>)" 
    by (auto intro: cat_cs_intros)
  show ?thesis
    by 
      (
        rule 
          is_functor.cf_arr_Set_umap_of[
            OF is_functor_op, unfolded cat_op_simps, OF \<AA> \<BB> r d u
            ]
      )
qed

lemma (in is_functor) cf_umap_of_is_arr:
  assumes "category \<alpha> \<AA>" 
    and "category \<alpha> \<BB>" 
    and "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "d \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "u : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
  shows "umap_of \<FF> c r u d : Hom \<AA> r d \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<BB> c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>)"
proof(intro cat_Set_is_arrI)
  show "arr_Set \<alpha> (umap_of \<FF> c r u d)" 
    by (rule cf_arr_Set_umap_of[OF assms])
qed (simp_all add: umap_of_components[OF assms(5)])

lemma (in is_functor) cf_umap_of_is_arr':
  assumes "category \<alpha> \<AA>" 
    and "category \<alpha> \<BB>" 
    and "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "d \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "u : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
    and "A = Hom \<AA> r d"
    and "B = Hom \<BB> c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>)"
    and "\<CC> = cat_Set \<alpha>"
  shows "umap_of \<FF> c r u d : A \<mapsto>\<^bsub>\<CC>\<^esub> B"
  using assms(1-5) unfolding assms(6-8) by (rule cf_umap_of_is_arr)

lemmas [cat_cs_intros] = is_functor.cf_umap_of_is_arr'

lemma (in is_functor) cf_umap_fo_is_arr:
  assumes "category \<alpha> \<AA>" 
    and "category \<alpha> \<BB>" 
    and "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "d \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "u : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> c"
  shows "umap_fo \<FF> c r u d : Hom \<AA> d r \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<BB> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>) c"
proof(intro cat_Set_is_arrI)
  show "arr_Set \<alpha> (umap_fo \<FF> c r u d)" 
    by (rule cf_arr_Set_umap_fo[OF assms])
qed (simp_all add: umap_fo_components[OF assms(5)])

lemma (in is_functor) cf_umap_fo_is_arr':
  assumes "category \<alpha> \<AA>" 
    and "category \<alpha> \<BB>" 
    and "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "d \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "u : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> c"
    and "A = Hom \<AA> d r"
    and "B = Hom \<BB> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>) c"
    and "\<CC> = cat_Set \<alpha>"
  shows "umap_fo \<FF> c r u d : A \<mapsto>\<^bsub>\<CC>\<^esub> B"
  using assms(1-5) unfolding assms(6-8) by (rule cf_umap_fo_is_arr)

lemmas [cat_cs_intros] = is_functor.cf_umap_fo_is_arr'



subsection\<open>Universal arrow: definition and elementary properties\<close>


text\<open>See Chapter III-1 in \cite{mac_lane_categories_2010}.\<close>

definition universal_arrow_of :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "universal_arrow_of \<FF> c r u \<longleftrightarrow>
    (
      r \<in>\<^sub>\<circ> \<FF>\<lparr>HomDom\<rparr>\<lparr>Obj\<rparr> \<and>
      u : c \<mapsto>\<^bsub>\<FF>\<lparr>HomCod\<rparr>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<and>
      (
        \<forall>r' u'.
          r' \<in>\<^sub>\<circ> \<FF>\<lparr>HomDom\<rparr>\<lparr>Obj\<rparr> \<longrightarrow>
          u' : c \<mapsto>\<^bsub>\<FF>\<lparr>HomCod\<rparr>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr> \<longrightarrow>
          (\<exists>!f'. f' : r \<mapsto>\<^bsub>\<FF>\<lparr>HomDom\<rparr>\<^esub> r' \<and> u' = umap_of \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>)
      )
    )"

definition universal_arrow_fo :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "universal_arrow_fo \<FF> c r u \<equiv> universal_arrow_of (op_cf \<FF>) c r u"


text\<open>Rules.\<close>

mk_ide (in is_functor) rf 
  universal_arrow_of_def[where \<FF>=\<FF>, unfolded cf_HomDom cf_HomCod]
  |intro universal_arrow_ofI|
  |dest universal_arrow_ofD[dest]|
  |elim universal_arrow_ofE[elim]|

lemma (in is_functor) universal_arrow_foI:
  assumes "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "u : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> c" 
    and "\<And>r' u'. \<lbrakk> r' \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; u' : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> c \<rbrakk> \<Longrightarrow> 
      \<exists>!f'. f' : r' \<mapsto>\<^bsub>\<AA>\<^esub> r \<and> u' = umap_fo \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
  shows "universal_arrow_fo \<FF> c r u"
  by 
    (
      simp add: 
        is_functor.universal_arrow_ofI
          [
            OF is_functor_op, 
            folded universal_arrow_fo_def, 
            unfolded cat_op_simps, 
            OF assms
          ]
    )

lemma (in is_functor) universal_arrow_foD[dest]:
  assumes "universal_arrow_fo \<FF> c r u"
  shows "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "u : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> c" 
    and "\<And>r' u'. \<lbrakk> r' \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; u' : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> c \<rbrakk> \<Longrightarrow> 
      \<exists>!f'. f' : r' \<mapsto>\<^bsub>\<AA>\<^esub> r \<and> u' = umap_fo \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
  by
    (
      auto simp: 
        is_functor.universal_arrow_ofD
          [
            OF is_functor_op, 
            folded universal_arrow_fo_def, 
            unfolded cat_op_simps,
            OF assms
          ]
    )

lemma (in is_functor) universal_arrow_foE[elim]:
  assumes "universal_arrow_fo \<FF> c r u"
  obtains "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "u : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> c" 
    and "\<And>r' u'. \<lbrakk> r' \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; u' : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> c \<rbrakk> \<Longrightarrow> 
      \<exists>!f'. f' : r' \<mapsto>\<^bsub>\<AA>\<^esub> r \<and> u' = umap_fo \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
  using assms by (auto simp: universal_arrow_foD)


text\<open>Elementary properties.\<close>

lemma (in is_functor) op_cf_universal_arrow_of[cat_op_simps]: 
  "universal_arrow_of (op_cf \<FF>) c r u \<longleftrightarrow> universal_arrow_fo \<FF> c r u"
  unfolding universal_arrow_fo_def ..

lemma (in is_functor) op_cf_universal_arrow_fo[cat_op_simps]: 
  "universal_arrow_fo (op_cf \<FF>) c r u \<longleftrightarrow> universal_arrow_of \<FF> c r u"
  unfolding universal_arrow_fo_def cat_op_simps ..

lemmas (in is_functor) [cat_op_simps] = 
  is_functor.op_cf_universal_arrow_of
  is_functor.op_cf_universal_arrow_fo



subsection\<open>Uniqueness\<close>


text\<open>
The following properties are related to the uniqueness of the 
universal arrow. These properties can be inferred from the content of
Chapter III-1 in \cite{mac_lane_categories_2010}.
\<close>

lemma (in is_functor) cf_universal_arrow_of_ex_is_arr_isomorphism:
  \<comment>\<open>The proof is based on the ideas expressed in the proof of Theorem 5.2 
  in Chapter Introduction in \cite{hungerford_algebra_2003}.\<close>
  assumes "universal_arrow_of \<FF> c r u" and "universal_arrow_of \<FF> c r' u'"
  obtains f where "f : r \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<AA>\<^esub> r'" and "u' = umap_of \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
proof-

  note ua1 = universal_arrow_ofD[OF assms(1)]
  note ua2 = universal_arrow_ofD[OF assms(2)]

  from ua1(1) have \<AA>r: "\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr> : r \<mapsto>\<^bsub>\<AA>\<^esub> r" by (auto intro: cat_cs_intros)
  from ua1(1) have "\<FF>\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr> = \<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>\<rparr>"
    by (auto intro: cat_cs_intros)
  with ua1(1,2) have u_def: "u = umap_of \<FF> c r u r\<lparr>ArrVal\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>"
    unfolding umap_of_ArrVal_app[OF \<AA>r ua1(2)] by (auto simp: cat_cs_simps)

  from ua2(1) have \<AA>r': "\<AA>\<lparr>CId\<rparr>\<lparr>r'\<rparr> : r' \<mapsto>\<^bsub>\<AA>\<^esub> r'" by (auto intro: cat_cs_intros)
  from ua2(1) have "\<FF>\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>r'\<rparr>\<rparr> = \<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr>\<rparr>" 
    by (auto intro: cat_cs_intros)
  with ua2(1,2) have u'_def: "u' = umap_of \<FF> c r' u' r'\<lparr>ArrVal\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>r'\<rparr>\<rparr>"
    unfolding umap_of_ArrVal_app[OF \<AA>r' ua2(2)] by (auto simp: cat_cs_simps)

  from \<AA>r u_def universal_arrow_ofD(3)[OF assms(1) ua1(1,2)] have eq_CId_rI: 
    "\<lbrakk> f' : r \<mapsto>\<^bsub>\<AA>\<^esub> r; u = umap_of \<FF> c r u r\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr> \<rbrakk> \<Longrightarrow> f' = \<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>" 
    for f'
    by blast
  from \<AA>r' u'_def universal_arrow_ofD(3)[OF assms(2) ua2(1,2)] have eq_CId_r'I: 
    "\<lbrakk> f' : r' \<mapsto>\<^bsub>\<AA>\<^esub> r'; u' = umap_of \<FF> c r' u' r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr> \<rbrakk> \<Longrightarrow>
      f' = \<AA>\<lparr>CId\<rparr>\<lparr>r'\<rparr>" 
    for f'
    by blast

  from ua1(3)[OF ua2(1,2)] obtain f 
    where f: "f : r \<mapsto>\<^bsub>\<AA>\<^esub> r'" 
      and u'_def: "u' = umap_of \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
      and "g : r \<mapsto>\<^bsub>\<AA>\<^esub> r' \<Longrightarrow> u' = umap_of \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>g\<rparr> \<Longrightarrow> f = g" 
    for g
    by metis
  from ua2(3)[OF ua1(1,2)] obtain f' 
    where f': "f' : r' \<mapsto>\<^bsub>\<AA>\<^esub> r" 
      and u_def: "u = umap_of \<FF> c r' u' r\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
      and "g : r' \<mapsto>\<^bsub>\<AA>\<^esub> r \<Longrightarrow> u = umap_of \<FF> c r' u' r\<lparr>ArrVal\<rparr>\<lparr>g\<rparr> \<Longrightarrow> f' = g" 
    for g
    by metis

  have "f : r \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<AA>\<^esub> r'"
  proof(intro is_arr_isomorphismI is_inverseI)
    show f: "f : r \<mapsto>\<^bsub>\<AA>\<^esub> r'" by (rule f)
    show f': "f' : r' \<mapsto>\<^bsub>\<AA>\<^esub> r" by (rule f')
    show "f : r \<mapsto>\<^bsub>\<AA>\<^esub> r'" by (rule f)
    from f' have \<FF>f': "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>" 
      by (auto intro: cat_cs_intros)
    from f have \<FF>f: "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr>" 
      by (auto intro: cat_cs_intros)
    note u'_def' = u'_def[symmetric, unfolded umap_of_ArrVal_app[OF f ua1(2)]] 
      and u_def' = u_def[symmetric, unfolded umap_of_ArrVal_app[OF f' ua2(2)]]
    show "f' \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f = \<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>"
    proof(rule eq_CId_rI)
      from f f' show f'f: "f' \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f : r \<mapsto>\<^bsub>\<AA>\<^esub> r" 
        by (auto intro: cat_cs_intros)
      from ua1(2) \<FF>f' \<FF>f show "u = umap_of \<FF> c r u r\<lparr>ArrVal\<rparr>\<lparr>f' \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f\<rparr>"
        unfolding umap_of_ArrVal_app[OF f'f ua1(2)] cf_ArrMap_Comp[OF f' f]
        by (simp add: HomCod.cat_Comp_assoc u'_def' u_def')
    qed
    show "f \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f' = \<AA>\<lparr>CId\<rparr>\<lparr>r'\<rparr>"
    proof(rule eq_CId_r'I)
      from f f' show ff': "f \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f' : r' \<mapsto>\<^bsub>\<AA>\<^esub> r'" 
        by (auto intro: cat_cs_intros)
      from ua2(2) \<FF>f' \<FF>f show "u' = umap_of \<FF> c r' u' r'\<lparr>ArrVal\<rparr>\<lparr>f \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f'\<rparr>"
        unfolding umap_of_ArrVal_app[OF ff' ua2(2)] cf_ArrMap_Comp[OF f f']
        by (simp add: HomCod.cat_Comp_assoc u'_def' u_def')
    qed
  qed
  
  with u'_def that show ?thesis by auto

qed

lemma (in is_functor) cf_universal_arrow_fo_ex_is_arr_isomorphism:
  assumes "universal_arrow_fo \<FF> c r u"
    and "universal_arrow_fo \<FF> c r' u'"
  obtains f where "f : r' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<AA>\<^esub> r" and "u' = umap_fo \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
  by 
    (
      elim 
        is_functor.cf_universal_arrow_of_ex_is_arr_isomorphism[
          OF is_functor_op, unfolded cat_op_simps, OF assms
          ]
    )

lemma (in is_functor) cf_universal_arrow_of_unique:
  assumes "universal_arrow_of \<FF> c r u"
    and "universal_arrow_of \<FF> c r' u'"
  shows "\<exists>!f'. f' : r \<mapsto>\<^bsub>\<AA>\<^esub> r' \<and> u' = umap_of \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
proof-
  note ua1 = universal_arrow_ofD[OF assms(1)]
  note ua2 = universal_arrow_ofD[OF assms(2)]
  from ua1(3)[OF ua2(1,2)] show ?thesis .
qed

lemma (in is_functor) cf_universal_arrow_fo_unique:
  assumes "universal_arrow_fo \<FF> c r u"
    and "universal_arrow_fo \<FF> c r' u'"
  shows "\<exists>!f'. f' : r' \<mapsto>\<^bsub>\<AA>\<^esub> r \<and> u' = umap_fo \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
proof-
  note ua1 = universal_arrow_foD[OF assms(1)]
  note ua2 = universal_arrow_foD[OF assms(2)]
  from ua1(3)[OF ua2(1,2)] show ?thesis .
qed

lemma (in is_functor) cf_universal_arrow_of_is_arr_isomorphism:
  assumes "universal_arrow_of \<FF> c r u"
    and "universal_arrow_of \<FF> c r' u'"
    and "f : r \<mapsto>\<^bsub>\<AA>\<^esub> r'" 
    and "u' = umap_of \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
  shows "f : r \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<AA>\<^esub> r'"
proof-
  from assms(3,4) cf_universal_arrow_of_unique[OF assms(1,2)] have eq: 
    "g : r \<mapsto>\<^bsub>\<AA>\<^esub> r' \<Longrightarrow> u' = umap_of \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>g\<rparr> \<Longrightarrow> f = g" for g
    by blast
  from assms(1,2) obtain f' 
    where iso_f': "f' : r \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<AA>\<^esub> r'" 
      and u'_def: "u' = umap_of \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
    by (auto elim: cf_universal_arrow_of_ex_is_arr_isomorphism)
  then have f': "f' : r \<mapsto>\<^bsub>\<AA>\<^esub> r'" by auto
  from iso_f' show ?thesis unfolding eq[OF f' u'_def, symmetric].
qed

lemma (in is_functor) cf_universal_arrow_fo_is_arr_isomorphism:
  assumes "universal_arrow_fo \<FF> c r u"
    and "universal_arrow_fo \<FF> c r' u'"
    and "f : r' \<mapsto>\<^bsub>\<AA>\<^esub> r" 
    and "u' = umap_fo \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
  shows "f : r' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<AA>\<^esub> r"
  by 
    (
      rule 
        is_functor.cf_universal_arrow_of_is_arr_isomorphism[
          OF is_functor_op, unfolded cat_op_simps, OF assms
          ]
    )



subsection\<open>Universal natural transformation\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The concept of the universal natural transformation is introduced for the 
statement of the elements of a variant of Proposition 1 in Chapter III-2
in \cite{mac_lane_categories_2010}.
\<close>

definition ntcf_ua_of :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_ua_of \<alpha> \<FF> c r u =
    [
      (\<lambda>d\<in>\<^sub>\<circ>\<FF>\<lparr>HomDom\<rparr>\<lparr>Obj\<rparr>. umap_of \<FF> c r u d),
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<FF>\<lparr>HomDom\<rparr>(r,-),
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<FF>\<lparr>HomCod\<rparr>(c,-) \<circ>\<^sub>C\<^sub>F \<FF>,
      \<FF>\<lparr>HomDom\<rparr>,
      cat_Set \<alpha>
    ]\<^sub>\<circ>"

definition ntcf_ua_fo :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_ua_fo \<alpha> \<FF> c r u = ntcf_ua_of \<alpha> (op_cf \<FF>) c r u"


text\<open>Components.\<close>

lemma ntcf_ua_of_components:
  shows "ntcf_ua_of \<alpha> \<FF> c r u\<lparr>NTMap\<rparr> = (\<lambda>d\<in>\<^sub>\<circ>\<FF>\<lparr>HomDom\<rparr>\<lparr>Obj\<rparr>. umap_of \<FF> c r u d)"
    and "ntcf_ua_of \<alpha> \<FF> c r u\<lparr>NTDom\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<FF>\<lparr>HomDom\<rparr>(r,-)"
    and "ntcf_ua_of \<alpha> \<FF> c r u\<lparr>NTCod\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<FF>\<lparr>HomCod\<rparr>(c,-) \<circ>\<^sub>C\<^sub>F \<FF>"
    and "ntcf_ua_of \<alpha> \<FF> c r u\<lparr>NTDGDom\<rparr> = \<FF>\<lparr>HomDom\<rparr>"
    and "ntcf_ua_of \<alpha> \<FF> c r u\<lparr>NTDGCod\<rparr> = cat_Set \<alpha>"
  unfolding ntcf_ua_of_def nt_field_simps by (simp_all add: nat_omega_simps) 

lemma ntcf_ua_fo_components:
  shows "ntcf_ua_fo \<alpha> \<FF> c r u\<lparr>NTMap\<rparr> = (\<lambda>d\<in>\<^sub>\<circ>\<FF>\<lparr>HomDom\<rparr>\<lparr>Obj\<rparr>. umap_fo \<FF> c r u d)"
    and "ntcf_ua_fo \<alpha> \<FF> c r u\<lparr>NTDom\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat (\<FF>\<lparr>HomDom\<rparr>)(r,-)"
    and "ntcf_ua_fo \<alpha> \<FF> c r u\<lparr>NTCod\<rparr> =
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat (\<FF>\<lparr>HomCod\<rparr>)(c,-) \<circ>\<^sub>C\<^sub>F op_cf \<FF>"
    and "ntcf_ua_fo \<alpha> \<FF> c r u\<lparr>NTDGDom\<rparr> = op_cat (\<FF>\<lparr>HomDom\<rparr>)"
    and "ntcf_ua_fo \<alpha> \<FF> c r u\<lparr>NTDGCod\<rparr> = cat_Set \<alpha>"
  unfolding ntcf_ua_fo_def ntcf_ua_of_components umap_fo_def cat_op_simps 
  by simp_all

context is_functor
begin

lemmas ntcf_ua_of_components' = 
  ntcf_ua_of_components[where \<alpha>=\<alpha> and \<FF>=\<FF>, unfolded cat_cs_simps]

lemmas [cat_cs_simps] = ntcf_ua_of_components'(2-5)

lemma ntcf_ua_fo_components':
  assumes "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
  shows "ntcf_ua_fo \<alpha> \<FF> c r u\<lparr>NTMap\<rparr> = (\<lambda>d\<in>\<^sub>\<circ>\<AA>\<lparr>Obj\<rparr>. umap_fo \<FF> c r u d)"
    and [cat_cs_simps]: 
      "ntcf_ua_fo \<alpha> \<FF> c r u\<lparr>NTDom\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,r)"
    and [cat_cs_simps]: 
      "ntcf_ua_fo \<alpha> \<FF> c r u\<lparr>NTCod\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(-,c) \<circ>\<^sub>C\<^sub>F op_cf \<FF>"
    and [cat_cs_simps]: "ntcf_ua_fo \<alpha> \<FF> c r u\<lparr>NTDGDom\<rparr> = op_cat \<AA>"
    and [cat_cs_simps]: "ntcf_ua_fo \<alpha> \<FF> c r u\<lparr>NTDGCod\<rparr> = cat_Set \<alpha>"
  unfolding
    ntcf_ua_fo_components cat_cs_simps
    HomDom.cat_op_cat_cf_Hom_snd[OF assms(2)] 
    HomCod.cat_op_cat_cf_Hom_snd[OF assms(1)]
  by simp_all

end

lemmas [cat_cs_simps] = 
  is_functor.ntcf_ua_of_components'(2-5)
  is_functor.ntcf_ua_fo_components'(2-5)


subsubsection\<open>Natural transformation map\<close>

mk_VLambda (in is_functor) 
  ntcf_ua_of_components(1)[where \<alpha>=\<alpha> and \<FF>=\<FF>, unfolded cf_HomDom]
  |vsv ntcf_ua_of_NTMap_vsv|
  |vdomain ntcf_ua_of_NTMap_vdomain|
  |app ntcf_ua_of_NTMap_app|

context is_functor
begin

context
  fixes c r
  assumes r: "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and c: "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
begin

mk_VLambda ntcf_ua_fo_components'(1)[OF c r]
  |vsv ntcf_ua_fo_NTMap_vsv|
  |vdomain ntcf_ua_fo_NTMap_vdomain|
  |app ntcf_ua_fo_NTMap_app|

end

end

lemmas [cat_cs_intros] = 
  is_functor.ntcf_ua_fo_NTMap_vsv
  is_functor.ntcf_ua_of_NTMap_vsv

lemmas [cat_cs_simps] = 
  is_functor.ntcf_ua_fo_NTMap_vdomain
  is_functor.ntcf_ua_fo_NTMap_app
  is_functor.ntcf_ua_of_NTMap_vdomain
  is_functor.ntcf_ua_of_NTMap_app

lemma (in is_functor) ntcf_ua_of_NTMap_vrange:
  assumes "category \<alpha> \<AA>" 
    and "category \<alpha> \<BB>" 
    and "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "u : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
  shows "\<R>\<^sub>\<circ> (ntcf_ua_of \<alpha> \<FF> c r u\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Arr\<rparr>"
proof(rule vsv.vsv_vrange_vsubset, unfold ntcf_ua_of_NTMap_vdomain)
  show "vsv (ntcf_ua_of \<alpha> \<FF> c r u\<lparr>NTMap\<rparr>)" by (rule ntcf_ua_of_NTMap_vsv)
  fix d assume prems: "d \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  with category_cat_Set is_functor_axioms assms show 
    "ntcf_ua_of \<alpha> \<FF> c r u\<lparr>NTMap\<rparr>\<lparr>d\<rparr> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed


subsubsection\<open>Commutativity of the universal maps and \<open>hom\<close>-functions\<close>

lemma (in is_functor) cf_umap_of_cf_hom_commute: 
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    and "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "u : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
    and "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
  shows 
    "umap_of \<FF> c r u b \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<AA> [\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>, f]\<^sub>\<circ> =
      cf_hom \<BB> [\<BB>\<lparr>CId\<rparr>\<lparr>c\<rparr>, \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> umap_of \<FF> c r u a"
  (is \<open>?uof_b \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?rf = ?cf \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?uof_a\<close>)
proof-

  from is_functor_axioms category_cat_Set assms(1,2,4-6) have b_rf: 
    "?uof_b \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?rf : Hom \<AA> r a \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<BB> c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    by (cs_concl cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros)
  from is_functor_axioms category_cat_Set assms(1,2,4-6) have cf_a: 
    "?cf \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?uof_a : Hom \<AA> r a \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<BB> c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    by (cs_concl cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros)

  show ?thesis
  proof(rule arr_Set_eqI[of \<alpha>])
    from b_rf show arr_Set_b_rf: "arr_Set \<alpha> (?uof_b \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?rf)"
      by (auto dest: cat_Set_is_arrD(1))
    from b_rf have dom_lhs: 
      "\<D>\<^sub>\<circ> ((?uof_b \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?rf)\<lparr>ArrVal\<rparr>) = Hom \<AA> r a"
      by (cs_concl cs_simp: cat_cs_simps)+
    from cf_a show arr_Set_cf_a: "arr_Set \<alpha> (?cf \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?uof_a)"
      by (auto dest: cat_Set_is_arrD(1))
    from cf_a have dom_rhs: 
      "\<D>\<^sub>\<circ> ((?cf \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?uof_a)\<lparr>ArrVal\<rparr>) = Hom \<AA> r a"
      by (cs_concl cs_simp: cat_cs_simps)
    show "(?uof_b \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?rf)\<lparr>ArrVal\<rparr> = (?cf \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?uof_a)\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs in_Hom_iff)
      fix q assume "q : r \<mapsto>\<^bsub>\<AA>\<^esub> a"
      with is_functor_axioms category_cat_Set assms show 
        "(?uof_b \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?rf)\<lparr>ArrVal\<rparr>\<lparr>q\<rparr> =
          (?cf \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?uof_a)\<lparr>ArrVal\<rparr>\<lparr>q\<rparr>"
        by (*slow*)
          (
            cs_concl
              cs_simp: cat_cs_simps cat_op_simps
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
         )
    qed (use arr_Set_b_rf arr_Set_cf_a in auto)
  
  qed (use b_rf cf_a in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+

qed

lemma cf_umap_of_cf_hom_unit_commute:
  assumes "category \<alpha> \<CC>"
    and "category \<alpha> \<DD>"
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<eta> : cf_id \<CC> \<mapsto>\<^sub>C\<^sub>F \<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "g : c' \<mapsto>\<^bsub>\<CC>\<^esub> c" 
    and "f : d \<mapsto>\<^bsub>\<DD>\<^esub> d'"
  shows 
    "umap_of \<GG> c' (\<FF>\<lparr>ObjMap\<rparr>\<lparr>c'\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>c'\<rparr>) d' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
      cf_hom \<DD> [\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>, f]\<^sub>\<circ> =
        cf_hom \<CC> [g, \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
          umap_of \<GG> c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>) (\<eta>\<lparr>NTMap\<rparr>\<lparr>c\<rparr>) d"
  (is \<open>?uof_c'd' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<FF>gf = ?g\<GG>f \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?uof_cd\<close>)
proof-

  interpret \<eta>: is_ntcf \<alpha> \<CC> \<CC> \<open>cf_id \<CC>\<close> \<open>\<GG> \<circ>\<^sub>C\<^sub>F \<FF>\<close> \<eta> by (rule assms(5))

  from assms have c'd'_\<FF>gf: "?uof_c'd' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<FF>gf :
    Hom \<DD> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>) d \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> c' (\<GG>\<lparr>ObjMap\<rparr>\<lparr>d'\<rparr>)"
    by
      (
        cs_concl
          cs_simp: cat_cs_simps 
          cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
      )
  then have dom_lhs:
    "\<D>\<^sub>\<circ> ((?uof_c'd' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<FF>gf)\<lparr>ArrVal\<rparr>) = Hom \<DD> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>) d"
    by (cs_concl cs_simp: cat_cs_simps)
  from assms have g\<GG>f_cd: "?g\<GG>f \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?uof_cd :
    Hom \<DD> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>) d \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> c' (\<GG>\<lparr>ObjMap\<rparr>\<lparr>d'\<rparr>)"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps 
          cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
      )
  then have dom_rhs: 
    "\<D>\<^sub>\<circ> ((?g\<GG>f \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?uof_cd)\<lparr>ArrVal\<rparr>) = Hom \<DD> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>) d"
    by (cs_concl cs_simp: cat_cs_simps)

  show ?thesis
  proof(rule arr_Set_eqI[of \<alpha>])
    from c'd'_\<FF>gf show arr_Set_c'd'_\<FF>gf: 
      "arr_Set \<alpha> (?uof_c'd' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<FF>gf)"
      by (auto dest: cat_Set_is_arrD(1))
    from g\<GG>f_cd show arr_Set_g\<GG>f_cd:
      "arr_Set \<alpha> (?g\<GG>f \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?uof_cd)"
      by (auto dest: cat_Set_is_arrD(1))
    show 
      "(?uof_c'd' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<FF>gf)\<lparr>ArrVal\<rparr> =
        (?g\<GG>f \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?uof_cd)\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs in_Hom_iff)
      fix h assume prems: "h : \<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> d"
      from \<eta>.ntcf_Comp_commute[OF assms(6)] assms have [cat_cs_simps]:
        "\<eta>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g = \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<eta>\<lparr>NTMap\<rparr>\<lparr>c'\<rparr>"
        by (cs_prems cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
      from assms prems show 
        "(?uof_c'd' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<FF>gf)\<lparr>ArrVal\<rparr>\<lparr>h\<rparr> =
          (?g\<GG>f \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?uof_cd)\<lparr>ArrVal\<rparr>\<lparr>h\<rparr>"
        by 
          (
            cs_concl
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros  
              cs_simp: cat_cs_simps
          )
    qed (use arr_Set_c'd'_\<FF>gf arr_Set_g\<GG>f_cd in auto)
 
  qed (use c'd'_\<FF>gf g\<GG>f_cd in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+

qed


subsubsection\<open>Universal natural transformation is a natural transformation\<close>

lemma (in is_functor) cf_ntcf_ua_of_is_ntcf:
  assumes "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "u : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
  shows "ntcf_ua_of \<alpha> \<FF> c r u :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(r,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(c,-) \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof(intro is_ntcfI')
  let ?ua = \<open>ntcf_ua_of \<alpha> \<FF> c r u\<close>
  show "vfsequence (ntcf_ua_of \<alpha> \<FF> c r u)" unfolding ntcf_ua_of_def by simp
  show "vcard ?ua = 5\<^sub>\<nat>" unfolding ntcf_ua_of_def by (simp add: nat_omega_simps)
  from assms(1) show "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(r,-) : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_intro: cat_cs_intros)
  from is_functor_axioms assms(2) show 
    "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(c,-) \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_intro: cat_cs_intros)
  from is_functor_axioms assms show "\<D>\<^sub>\<circ> (?ua\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)
  show "?ua\<lparr>NTMap\<rparr>\<lparr>a\<rparr> :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(r,-)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(c,-) \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    if "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" for a
    using is_functor_axioms assms that 
    by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
  show "?ua\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(r,-)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
    (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(c,-) \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?ua\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
    if "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" for a b f
    using is_functor_axioms assms that 
    by 
      ( 
        cs_concl 
          cs_simp: cf_umap_of_cf_hom_commute cat_cs_simps cat_op_simps 
          cs_intro: cat_cs_intros cat_op_intros
      )
qed (auto simp: ntcf_ua_of_components cat_cs_simps)

lemma (in is_functor) cf_ntcf_ua_fo_is_ntcf:
  assumes "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and "u : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> c"
  shows "ntcf_ua_fo \<alpha> \<FF> c r u :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,r) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(-,c) \<circ>\<^sub>C\<^sub>F op_cf \<FF> :
    op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-
  from assms(2) have c: "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" by auto
  show ?thesis
    by 
      (
        rule is_functor.cf_ntcf_ua_of_is_ntcf
          [
            OF is_functor_op, 
            unfolded cat_op_simps, 
            OF assms(1,2),
            unfolded 
              HomDom.cat_op_cat_cf_Hom_snd[OF assms(1)] 
              HomCod.cat_op_cat_cf_Hom_snd[OF c]
              ntcf_ua_fo_def[symmetric]
          ]
      )
qed


subsubsection\<open>Universal natural transformation and universal arrow\<close>


text\<open>
The lemmas in this subsection correspond to 
variants of elements of Proposition 1 in Chapter III-2 in 
\cite{mac_lane_categories_2010}.
\<close>

lemma (in is_functor) cf_ntcf_ua_of_is_iso_ntcf:
  assumes "universal_arrow_of \<FF> c r u"
  shows "ntcf_ua_of \<alpha> \<FF> c r u :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(r,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(c,-) \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-

  have r: "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and u: "u : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
    and bij: "\<And>r' u'.
      \<lbrakk>
        r' \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; 
        u' : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr>
      \<rbrakk> \<Longrightarrow> \<exists>!f'. f' : r \<mapsto>\<^bsub>\<AA>\<^esub> r' \<and> u' = umap_of \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
    by (auto intro!: universal_arrow_ofD[OF assms(1)])

  show ?thesis
  proof(intro is_iso_ntcfI)
    show "ntcf_ua_of \<alpha> \<FF> c r u :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(r,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(c,-) \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      by (rule cf_ntcf_ua_of_is_ntcf[OF r u])
    fix a assume prems: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    from is_functor_axioms prems r u have [simp]:
      "umap_of \<FF> c r u a : Hom \<AA> r a \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<BB> c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)"
      by (cs_concl cs_intro: cat_cs_intros)
    then have dom: "\<D>\<^sub>\<circ> (umap_of \<FF> c r u a\<lparr>ArrVal\<rparr>) = Hom \<AA> r a"
      by (cs_concl cs_simp: cat_cs_simps)
    have "umap_of \<FF> c r u a : Hom \<AA> r a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> Hom \<BB> c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)"
    proof(intro cat_Set_is_arr_isomorphismI, unfold dom)
 
      show umof_a: "v11 (umap_of \<FF> c r u a\<lparr>ArrVal\<rparr>)"
      proof(intro vsv.vsv_valeq_v11I, unfold dom in_Hom_iff)
        fix g f assume prems': 
          "g : r \<mapsto>\<^bsub>\<AA>\<^esub> a"
          "f : r \<mapsto>\<^bsub>\<AA>\<^esub> a" 
          "umap_of \<FF> c r u a\<lparr>ArrVal\<rparr>\<lparr>g\<rparr> = umap_of \<FF> c r u a\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
        from is_functor_axioms r u prems'(1) have \<FF>g:
          "\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> u : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
          by (cs_concl cs_intro: cat_cs_intros)
        from bij[OF prems \<FF>g] have unique:
          "\<lbrakk>
            f' : r \<mapsto>\<^bsub>\<AA>\<^esub> a;
            \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> u = umap_of \<FF> c r u a\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr> 
           \<rbrakk> \<Longrightarrow> g = f'"
          for f' by (metis prems'(1) u umap_of_ArrVal_app)
        from is_functor_axioms prems'(1,2) u have \<FF>g_u:
          "\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> u = umap_of \<FF> c r u a\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
          by (cs_concl cs_simp: prems'(3)[symmetric] cat_cs_simps)
        show "g = f" by (rule unique[OF prems'(2) \<FF>g_u])
      qed (auto simp: cat_cs_simps cat_cs_intros)

      interpret umof_a: v11 \<open>umap_of \<FF> c r u a\<lparr>ArrVal\<rparr>\<close> by (rule umof_a)

      show "\<R>\<^sub>\<circ> (umap_of \<FF> c r u a\<lparr>ArrVal\<rparr>) = Hom \<BB> c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)"
      proof(intro vsubset_antisym)
        from u show "\<R>\<^sub>\<circ> (umap_of \<FF> c r u a\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> Hom \<BB> c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)"
          by (rule umap_of_ArrVal_vrange)
        show "Hom \<BB> c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (umap_of \<FF> c r u a\<lparr>ArrVal\<rparr>)"
        proof(rule vsubsetI, unfold in_Hom_iff )
          fix f assume prems': "f : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
          from bij[OF prems prems'] obtain f' 
            where f': "f' : r \<mapsto>\<^bsub>\<AA>\<^esub> a" 
              and f_def: "f = umap_of \<FF> c r u a\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
            by auto
          from is_functor_axioms prems prems' u f' have 
            "f' \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (umap_of \<FF> c r u a\<lparr>ArrVal\<rparr>)"
            by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
          from this show "f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (umap_of \<FF> c r u a\<lparr>ArrVal\<rparr>)"
            unfolding f_def by (rule umof_a.vsv_vimageI2)
        qed

      qed

    qed simp_all

    from is_functor_axioms prems r u this show 
      "ntcf_ua_of \<alpha> \<FF> c r u\<lparr>NTMap\<rparr>\<lparr>a\<rparr> :
        Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(r,-)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub>
        (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(c,-) \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_op_simps 
            cs_intro: cat_cs_intros cat_op_intros
        )
  qed

qed

lemmas [cat_cs_intros] = is_functor.cf_ntcf_ua_of_is_iso_ntcf

lemma (in is_functor) cf_ntcf_ua_fo_is_iso_ntcf:
  assumes "universal_arrow_fo \<FF> c r u"
  shows "ntcf_ua_fo \<alpha> \<FF> c r u :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,r) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(-,c) \<circ>\<^sub>C\<^sub>F op_cf \<FF> :
    op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-
  from universal_arrow_foD[OF assms] have r: "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and c: "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    by auto
  show ?thesis
    by 
      (
        rule is_functor.cf_ntcf_ua_of_is_iso_ntcf
          [
            OF is_functor_op, 
            unfolded cat_op_simps, 
            OF assms,
            unfolded 
              HomDom.cat_op_cat_cf_Hom_snd[OF r] 
              HomCod.cat_op_cat_cf_Hom_snd[OF c]
              ntcf_ua_fo_def[symmetric]
          ]
      ) 
qed

lemmas [cat_cs_intros] = is_functor.cf_ntcf_ua_fo_is_iso_ntcf

lemma (in is_functor) cf_ua_of_if_ntcf_ua_of_is_iso_ntcf:
  assumes "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "u : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
    and "ntcf_ua_of \<alpha> \<FF> c r u :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(r,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(c,-) \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "universal_arrow_of \<FF> c r u"
proof(rule universal_arrow_ofI)
  interpret ua_of_u: is_iso_ntcf 
    \<alpha> 
    \<AA> 
    \<open>cat_Set \<alpha>\<close>
    \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(r,-)\<close> 
    \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(c,-) \<circ>\<^sub>C\<^sub>F \<FF>\<close> 
    \<open>ntcf_ua_of \<alpha> \<FF> c r u\<close>
    by (rule assms(3))
  fix r' u' assume prems: "r' \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" "u' : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr>"  
  have "ntcf_ua_of \<alpha> \<FF> c r u\<lparr>NTMap\<rparr>\<lparr>r'\<rparr> :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(r,-)\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub>
    (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(c,-) \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr>"
    by (rule is_iso_ntcf.iso_ntcf_is_arr_isomorphism[OF assms(3) prems(1)])
  from this is_functor_axioms assms(1-2) prems have uof_r':
    "umap_of \<FF> c r u r' : Hom \<AA> r r' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> Hom \<BB> c (\<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr>)"
    by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)
  note uof_r' = cat_Set_is_arr_isomorphismD[OF uof_r']  
  interpret uof_r': v11 \<open>umap_of \<FF> c r u r'\<lparr>ArrVal\<rparr>\<close> by (rule uof_r'(2))  
  from 
    uof_r'.v11_vrange_ex1_eq[
      THEN iffD1, unfolded uof_r'(3,4) in_Hom_iff, OF prems(2)
      ] 
  show "\<exists>!f'. f' : r \<mapsto>\<^bsub>\<AA>\<^esub> r' \<and> u' = umap_of \<FF> c r u r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
    by metis
qed (intro assms)+

lemma (in is_functor) cf_ua_fo_if_ntcf_ua_fo_is_iso_ntcf:
  assumes "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "u : \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> c"
    and "ntcf_ua_fo \<alpha> \<FF> c r u :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,r) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(-,c) \<circ>\<^sub>C\<^sub>F op_cf \<FF> :
      op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "universal_arrow_fo \<FF> c r u"
proof-
  from assms(2) have c: "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" by auto
  show ?thesis
    by 
      (
        rule is_functor.cf_ua_of_if_ntcf_ua_of_is_iso_ntcf
          [
            OF is_functor_op, 
            unfolded cat_op_simps,
            OF assms(1,2),
            unfolded 
              HomDom.cat_op_cat_cf_Hom_snd[OF assms(1)] 
              HomCod.cat_op_cat_cf_Hom_snd[OF c]
              ntcf_ua_fo_def[symmetric],
            OF assms(3)
          ]
      )
qed

lemma (in is_functor) cf_universal_arrow_of_if_is_iso_ntcf:
  assumes "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    and "\<phi> :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(r,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(c,-) \<circ>\<^sub>C\<^sub>F \<FF> :
      \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "universal_arrow_of \<FF> c r (\<phi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>)"
    (is \<open>universal_arrow_of \<FF> c r ?u\<close>)
proof-

  interpret \<phi>: is_iso_ntcf 
    \<alpha> \<AA> \<open>cat_Set \<alpha>\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(r,-)\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(c,-) \<circ>\<^sub>C\<^sub>F \<FF>\<close> \<phi>
    by (rule assms(3))

  show ?thesis
  proof(intro universal_arrow_ofI assms)
 
    from assms(1,2) show u: "?u : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
    fix r' u' assume prems: "r' \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" "u' : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr>"
    have \<phi>r'_ArrVal_app[symmetric, cat_cs_simps]:
      "\<phi>\<lparr>NTMap\<rparr>\<lparr>r'\<rparr>\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr> =
        \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<phi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>"
      if "f' : r \<mapsto>\<^bsub>\<AA>\<^esub> r'" for f'
    proof-
      have "\<phi>\<lparr>NTMap\<rparr>\<lparr>r'\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(r,-)\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> =
        (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(c,-) \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> \<phi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>"
        using that by (intro \<phi>.ntcf_Comp_commute)
      then have 
        "\<phi>\<lparr>NTMap\<rparr>\<lparr>r'\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<AA> [\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>, f']\<^sub>\<circ> =
          cf_hom \<BB> [\<BB>\<lparr>CId\<rparr>\<lparr>c\<rparr>, \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> \<phi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>" 
        using assms(1,2) that prems
        by (cs_prems cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
      then have
        "(\<phi>\<lparr>NTMap\<rparr>\<lparr>r'\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
        cf_hom \<AA> [\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>, f']\<^sub>\<circ>)\<lparr>ArrVal\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr> =
          (cf_hom \<BB> [\<BB>\<lparr>CId\<rparr>\<lparr>c\<rparr>, \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
          \<phi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>)\<lparr>ArrVal\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>"
         by simp
      from this assms(1,2) u that show ?thesis
        by
          (
            cs_prems
              cs_simp: cat_cs_simps cat_op_simps 
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
    qed 
    
    show "\<exists>!f'. f' : r \<mapsto>\<^bsub>\<AA>\<^esub> r' \<and> u' = umap_of \<FF> c r ?u r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
    proof(intro ex1I conjI; (elim conjE)?)
      from assms prems show 
        "(\<phi>\<lparr>NTMap\<rparr>\<lparr>r'\<rparr>)\<inverse>\<^sub>C\<^bsub>cat_Set \<alpha>\<^esub>\<lparr>ArrVal\<rparr>\<lparr>u'\<rparr> : r \<mapsto>\<^bsub>\<AA>\<^esub> r'"
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cat_op_simps
              cs_intro: cat_cs_intros cat_arrow_cs_intros
          )
      with assms(1,2) prems show "u' =
        umap_of \<FF> c r ?u r'\<lparr>ArrVal\<rparr>\<lparr>(\<phi>\<lparr>NTMap\<rparr>\<lparr>r'\<rparr>)\<inverse>\<^sub>C\<^bsub>cat_Set \<alpha>\<^esub>\<lparr>ArrVal\<rparr>\<lparr>u'\<rparr>\<rparr>"
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cat_op_simps
              cs_intro: cat_arrow_cs_intros cat_cs_intros cat_op_intros
          )
      fix f' assume prems': 
        "f' : r \<mapsto>\<^bsub>\<AA>\<^esub> r'"
        "u' = umap_of \<FF> c r (\<phi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>) r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
      from prems'(2,1) assms(1,2) have u'_def: 
        "u' = \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<phi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>"
        by
          (
            cs_prems
              cs_simp: cat_cs_simps cat_op_simps
              cs_intro: cat_cs_intros cat_op_intros
          )
      from prems' show "f' = (\<phi>\<lparr>NTMap\<rparr>\<lparr>r'\<rparr>)\<inverse>\<^sub>C\<^bsub>cat_Set \<alpha>\<^esub>\<lparr>ArrVal\<rparr>\<lparr>u'\<rparr>"
        unfolding u'_def \<phi>r'_ArrVal_app[OF prems'(1)]
        by
          (
            cs_concl
              cs_simp: cat_cs_simps
              cs_intro: cat_arrow_cs_intros cat_cs_intros cat_op_intros
          )

    qed

  qed

qed

lemma (in is_functor) cf_universal_arrow_fo_if_is_iso_ntcf:
  assumes "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    and "\<phi> :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,r) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(-,c) \<circ>\<^sub>C\<^sub>F op_cf \<FF> :
      op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "universal_arrow_fo \<FF> c r (\<phi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>)"
  by
    (
      rule is_functor.cf_universal_arrow_of_if_is_iso_ntcf
        [
          OF is_functor_op,
          unfolded cat_op_simps,
          OF assms(1,2),
          unfolded 
            HomDom.cat_op_cat_cf_Hom_snd[OF assms(1)] 
            HomCod.cat_op_cat_cf_Hom_snd[OF assms(2)]
            ntcf_ua_fo_def[symmetric],
          OF assms(3)
        ]
  )

lemma (in is_functor) cf_universal_arrow_of_if_is_iso_ntcf_if_ge_Limit:
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    and "\<phi> :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<AA>(r,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<BB>(c,-) \<circ>\<^sub>C\<^sub>F \<FF> :
      \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
  shows "universal_arrow_of \<FF> c r (\<phi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>)"
    (is \<open>universal_arrow_of \<FF> c r ?u\<close>)
proof-

  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret cat_Set_\<alpha>\<beta>: subcategory \<beta> \<open>cat_Set \<alpha>\<close> \<open>cat_Set \<beta>\<close>
    by (rule subcategory_cat_Set_cat_Set[OF assms(1,2)])
  interpret \<phi>: is_iso_ntcf 
    \<beta> \<AA> \<open>cat_Set \<beta>\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<AA>(r,-)\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<BB>(c,-) \<circ>\<^sub>C\<^sub>F \<FF>\<close> \<phi>
    by (rule assms(5))
  interpret \<beta>\<AA>: category \<beta> \<AA>
    by (rule category.cat_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_simp: cs_intro: cat_cs_intros\<close>)+
  interpret \<beta>\<BB>: category \<beta> \<BB>
    by (rule category.cat_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_simp: cs_intro: cat_cs_intros\<close>)+
  interpret \<beta>\<FF>: is_functor \<beta> \<AA> \<BB> \<FF>
    by (rule cf_is_functor_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_simp: cs_intro: cat_cs_intros\<close>)+

  show ?thesis
  proof(intro universal_arrow_ofI assms)
 
    from assms(3,4) show u: "?u : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
    fix r' u' assume prems: "r' \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" "u' : c \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r'\<rparr>"
    have \<phi>r'_ArrVal_app[symmetric, cat_cs_simps]:
      "\<phi>\<lparr>NTMap\<rparr>\<lparr>r'\<rparr>\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr> =
        \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<phi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>"
      if "f' : r \<mapsto>\<^bsub>\<AA>\<^esub> r'" for f'
    proof-
      have "\<phi>\<lparr>NTMap\<rparr>\<lparr>r'\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<AA>(r,-)\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> =
        (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<BB>(c,-) \<circ>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> \<phi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>"
        using that by (intro \<phi>.ntcf_Comp_commute)
      then have 
        "\<phi>\<lparr>NTMap\<rparr>\<lparr>r'\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> cf_hom \<AA> [\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>, f']\<^sub>\<circ> =
          cf_hom \<BB> [\<BB>\<lparr>CId\<rparr>\<lparr>c\<rparr>, \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> \<phi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>" 
        using assms(3,4) assms(1,2) that prems
        by (cs_prems cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
      then have
        "(\<phi>\<lparr>NTMap\<rparr>\<lparr>r'\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub>
        cf_hom \<AA> [\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>, f']\<^sub>\<circ>)\<lparr>ArrVal\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr> =
          (cf_hom \<BB> [\<BB>\<lparr>CId\<rparr>\<lparr>c\<rparr>, \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub>
          \<phi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>)\<lparr>ArrVal\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>"
        by simp
      from 
        this assms(3,4,2) u that HomDom.category_axioms HomCod.category_axioms
      show ?thesis
        by
          (
            cs_prems
              cs_simp: cat_cs_simps cat_op_simps 
              cs_intro:
                cat_cs_intros
                cat_op_intros
                cat_prod_cs_intros
                cat_Set_\<alpha>\<beta>.subcat_is_arrD
          )
    qed 
    
    show "\<exists>!f'. f' : r \<mapsto>\<^bsub>\<AA>\<^esub> r' \<and> u' = umap_of \<FF> c r ?u r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
    proof(intro ex1I conjI; (elim conjE)?)
      from assms prems HomDom.category_axioms show 
        "(\<phi>\<lparr>NTMap\<rparr>\<lparr>r'\<rparr>)\<inverse>\<^sub>C\<^bsub>cat_Set \<beta>\<^esub>\<lparr>ArrVal\<rparr>\<lparr>u'\<rparr> : r \<mapsto>\<^bsub>\<AA>\<^esub> r'"
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cat_op_simps
              cs_intro: cat_cs_intros cat_arrow_cs_intros
          )
      with assms(3,4) prems show "u' =
        umap_of \<FF> c r ?u r'\<lparr>ArrVal\<rparr>\<lparr>(\<phi>\<lparr>NTMap\<rparr>\<lparr>r'\<rparr>)\<inverse>\<^sub>C\<^bsub>cat_Set \<beta>\<^esub>\<lparr>ArrVal\<rparr>\<lparr>u'\<rparr>\<rparr>"
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cat_op_simps
              cs_intro: cat_arrow_cs_intros cat_cs_intros cat_op_intros
          )
      fix f' assume prems': 
        "f' : r \<mapsto>\<^bsub>\<AA>\<^esub> r'"
        "u' = umap_of \<FF> c r (\<phi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>) r'\<lparr>ArrVal\<rparr>\<lparr>f'\<rparr>"
      from prems'(2,1) assms(3,4) have u'_def: 
        "u' = \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<phi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>"
        by
          (
            cs_prems
              cs_simp: cat_cs_simps cat_op_simps
              cs_intro: cat_cs_intros cat_op_intros
          )
      from prems' show "f' = (\<phi>\<lparr>NTMap\<rparr>\<lparr>r'\<rparr>)\<inverse>\<^sub>C\<^bsub>cat_Set \<beta>\<^esub>\<lparr>ArrVal\<rparr>\<lparr>u'\<rparr>"
        unfolding u'_def \<phi>r'_ArrVal_app[OF prems'(1)]
        by
          (
            cs_concl
              cs_simp: cat_cs_simps
              cs_intro: cat_arrow_cs_intros cat_cs_intros cat_op_intros
          )

    qed

  qed

qed

lemma (in is_functor) cf_universal_arrow_fo_if_is_iso_ntcf_if_ge_Limit:
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and  "r \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    and "\<phi> :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<AA>(-,r) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>\<BB>(-,c) \<circ>\<^sub>C\<^sub>F op_cf \<FF> :
      op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
  shows "universal_arrow_fo \<FF> c r (\<phi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>)"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<beta>\<FF>: is_functor \<beta> \<AA> \<BB> \<FF>
    by (rule cf_is_functor_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  show ?thesis 
    by 
      (
        rule is_functor.cf_universal_arrow_of_if_is_iso_ntcf_if_ge_Limit
          [
            OF is_functor_op,
            OF assms(1,2),
            unfolded cat_op_simps,
            OF assms(3,4),
            unfolded 
              \<beta>\<FF>.HomDom.cat_op_cat_cf_Hom_snd[OF assms(3)] 
              \<beta>\<FF>.HomCod.cat_op_cat_cf_Hom_snd[OF assms(4)]
              ntcf_ua_fo_def[symmetric],
            OF assms(5)
          ]
      )
qed

text\<open>\newpage\<close>

end