(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Yoneda Lemma\<close>
theory CZH_ECAT_Yoneda
  imports 
    CZH_ECAT_FUNCT
    CZH_ECAT_Hom
begin



subsection\<open>Yoneda map\<close>


text\<open>
The Yoneda map is the bijection that is used in the statement of the
Yoneda Lemma, as presented, for example, in Chapter III-2 in 
\cite{mac_lane_categories_2010} or in subsection 1.15 
in \cite{bodo_categories_1970}.
\<close>

definition Yoneda_map :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "Yoneda_map \<alpha> \<KK> r =
    (
      \<lambda>\<psi>\<in>\<^sub>\<circ>these_ntcfs \<alpha> (\<KK>\<lparr>HomDom\<rparr>) (cat_Set \<alpha>) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<KK>\<lparr>HomDom\<rparr>(r,-) \<KK>.
        \<psi>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<KK>\<lparr>HomDom\<rparr>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>
    )"


text\<open>Elementary properties.\<close>

mk_VLambda Yoneda_map_def
  |vsv Yoneda_map_vsv[cat_cs_intros]|

mk_VLambda (in is_functor) Yoneda_map_def[where \<alpha>=\<alpha> and \<KK>=\<FF>, unfolded cf_HomDom]
  |vdomain Yoneda_map_vdomain|
  |app Yoneda_map_app[unfolded these_ntcfs_iff]|

lemmas [cat_cs_simps] = is_functor.Yoneda_map_vdomain

lemmas Yoneda_map_app[cat_cs_simps] = 
  is_functor.Yoneda_map_app[unfolded these_ntcfs_iff]



subsection\<open>Yoneda component\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The Yoneda components are the components of the natural transformations
that appear in the statement of the Yoneda Lemma (e.g., see 
Chapter III-2 in \cite{mac_lane_categories_2010} or subsection 1.15 
in \cite{bodo_categories_1970}).
\<close>

definition Yoneda_component :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "Yoneda_component \<KK> r u d =
    [
      (\<lambda>f\<in>\<^sub>\<circ>Hom (\<KK>\<lparr>HomDom\<rparr>) r d. \<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<lparr>ArrVal\<rparr>\<lparr>u\<rparr>),
      Hom (\<KK>\<lparr>HomDom\<rparr>) r d,
      \<KK>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma (in is_functor) Yoneda_component_components: 
  shows "Yoneda_component \<FF> r u d\<lparr>ArrVal\<rparr> =
    (\<lambda>f\<in>\<^sub>\<circ>Hom \<AA> r d. \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<lparr>ArrVal\<rparr>\<lparr>u\<rparr>)"
    and "Yoneda_component \<FF> r u d\<lparr>ArrDom\<rparr> = Hom \<AA> r d"
    and "Yoneda_component \<FF> r u d\<lparr>ArrCod\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>"
  unfolding Yoneda_component_def arr_field_simps 
  by (simp_all add: nat_omega_simps cat_cs_simps)


subsubsection\<open>Arrow value\<close>

mk_VLambda (in is_functor) Yoneda_component_components(1)
  |vsv Yoneda_component_ArrVal_vsv|
  |vdomain Yoneda_component_ArrVal_vdomain|
  |app Yoneda_component_ArrVal_app[unfolded in_Hom_iff]|

lemmas [cat_cs_simps] = is_functor.Yoneda_component_ArrVal_vdomain

lemmas Yoneda_component_ArrVal_app[cat_cs_simps] = 
  is_functor.Yoneda_component_ArrVal_app[unfolded in_Hom_iff]


subsubsection\<open>Yoneda component is an arrow in the category \<open>Set\<close>\<close>

lemma (in category) cat_Yoneda_component_is_arr:
  assumes "\<KK> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "u \<in>\<^sub>\<circ> \<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
    and "d \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "Yoneda_component \<KK> r u d : Hom \<CC> r d \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>"   
proof-
  interpret \<KK>: is_functor \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<KK> by (rule assms(1)) 
  show ?thesis
  proof(intro cat_Set_is_arrI arr_SetI, unfold \<KK>.Yoneda_component_components)
    show "vfsequence (Yoneda_component \<KK> r u d)" 
      unfolding Yoneda_component_def by simp
    show "vcard (Yoneda_component \<KK> r u d) = 3\<^sub>\<nat>"
      unfolding Yoneda_component_def by (simp add: nat_omega_simps)
    show "\<R>\<^sub>\<circ> (\<lambda>f\<in>\<^sub>\<circ>Hom \<CC> r d. \<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<lparr>ArrVal\<rparr>\<lparr>u\<rparr>) \<subseteq>\<^sub>\<circ> \<KK>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>"
    proof(rule vrange_VLambda_vsubset)
      fix f assume "f \<in>\<^sub>\<circ> Hom \<CC> r d"
      then have \<KK>f: "\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : \<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>" 
        by (auto simp: cat_cs_intros)
      note \<KK>f_simps = cat_Set_is_arrD[OF \<KK>f]
      interpret \<KK>f: arr_Set \<alpha> \<open>\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<close> by (rule \<KK>f_simps(1))          
      have "u \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<lparr>ArrVal\<rparr>)" 
        by (simp add: \<KK>f_simps assms cat_Set_cs_simps)
      with \<KK>f.arr_Set_ArrVal_vrange[unfolded \<KK>f_simps] show 
        "\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<lparr>ArrVal\<rparr>\<lparr>u\<rparr> \<in>\<^sub>\<circ> \<KK>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>"
        by (blast elim: \<KK>f.ArrVal.vsv_value)
    qed 
    from assms \<KK>.HomCod.cat_Obj_vsubset_Vset show "\<KK>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
      by (auto dest: \<KK>.cf_ObjMap_app_in_HomCod_Obj)
  qed (auto simp: assms cat_cs_intros)
qed

lemma (in category) cat_Yoneda_component_is_arr':
  assumes "\<KK> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>" 
    and "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "u \<in>\<^sub>\<circ> \<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
    and "d \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "s = Hom \<CC> r d"
    and "t = \<KK>\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>"
    and "\<DD> = cat_Set \<alpha>"
  shows "Yoneda_component \<KK> r u d : s \<mapsto>\<^bsub>\<DD>\<^esub> t"   
  unfolding assms(5-7) using assms(1-4) by (rule cat_Yoneda_component_is_arr)

lemmas [cat_cs_intros] = category.cat_Yoneda_component_is_arr'[rotated 1]



subsection\<open>Yoneda arrow\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The Yoneda arrows are the natural transformations that 
appear in the statement of the Yoneda Lemma in Chapter III-2 in 
\cite{mac_lane_categories_2010} and subsection 1.15 
in \cite{bodo_categories_1970}.
\<close>

definition Yoneda_arrow :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" 
  where "Yoneda_arrow \<alpha> \<KK> r u =
    [
      (\<lambda>d\<in>\<^sub>\<circ>\<KK>\<lparr>HomDom\<rparr>\<lparr>Obj\<rparr>. Yoneda_component \<KK> r u d),
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<KK>\<lparr>HomDom\<rparr>(r,-),
      \<KK>,
      \<KK>\<lparr>HomDom\<rparr>,
      cat_Set \<alpha>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma (in is_functor) Yoneda_arrow_components:
  shows "Yoneda_arrow \<alpha> \<FF> r u\<lparr>NTMap\<rparr> = 
    (\<lambda>d\<in>\<^sub>\<circ>\<AA>\<lparr>Obj\<rparr>. Yoneda_component \<FF> r u d)"
    and "Yoneda_arrow \<alpha> \<FF> r u\<lparr>NTDom\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(r,-)"
    and "Yoneda_arrow \<alpha> \<FF> r u\<lparr>NTCod\<rparr> = \<FF>"
    and "Yoneda_arrow \<alpha> \<FF> r u\<lparr>NTDGDom\<rparr> = \<AA>"
    and "Yoneda_arrow \<alpha> \<FF> r u\<lparr>NTDGCod\<rparr> = cat_Set \<alpha>"
  unfolding Yoneda_arrow_def nt_field_simps 
  by (simp_all add: nat_omega_simps cat_cs_simps)


subsubsection\<open>Natural transformation map\<close>

mk_VLambda (in is_functor) Yoneda_arrow_components(1)
  |vsv Yoneda_arrow_NTMap_vsv|
  |vdomain Yoneda_arrow_NTMap_vdomain|
  |app Yoneda_arrow_NTMap_app|

lemmas [cat_cs_simps] = is_functor.Yoneda_arrow_NTMap_vdomain

lemmas Yoneda_arrow_NTMap_app[cat_cs_simps] = 
  is_functor.Yoneda_arrow_NTMap_app


subsubsection\<open>Yoneda arrow is a natural transformation\<close>

lemma (in category) cat_Yoneda_arrow_is_ntcf:
  assumes "\<KK> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>" 
    and "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and "u \<in>\<^sub>\<circ> \<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
  shows "Yoneda_arrow \<alpha> \<KK> r u : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-) \<mapsto>\<^sub>C\<^sub>F \<KK> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-

  interpret \<KK>: is_functor \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<KK> by (rule assms(1)) 
  note \<KK>ru = cat_Yoneda_component_is_arr[OF assms]
  let ?\<KK>ru = \<open>Yoneda_component \<KK> r u\<close>

  show ?thesis
  proof(intro is_ntcfI', unfold \<KK>.Yoneda_arrow_components)

    show "vfsequence (Yoneda_arrow \<alpha> \<KK> r u)"
      unfolding Yoneda_arrow_def by simp
    show "vcard (Yoneda_arrow \<alpha> \<KK> r u) = 5\<^sub>\<nat>" 
      unfolding Yoneda_arrow_def by (simp add: nat_omega_simps)

    show
      "(\<lambda>d\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. ?\<KK>ru d)\<lparr>a\<rparr> :
        Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for a
      using that assms category_axioms
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_op_simps V_cs_simps 
            cs_intro: cat_cs_intros
        )
    show 
      "(\<lambda>d\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. ?\<KK>ru d)\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
        \<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> (\<lambda>d\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. ?\<KK>ru d)\<lparr>a\<rparr>"
      if "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" for a b f
    proof-

      note \<MM>a = \<KK>ru[OF cat_is_arrD(2)[OF that]]
      note \<MM>b = \<KK>ru[OF cat_is_arrD(3)[OF that]]

      from category_axioms assms that \<MM>b have b_f:
        "?\<KK>ru b \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<CC> [\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>, f]\<^sub>\<circ> :
          Hom \<CC> r a \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
        by
          (
            cs_concl cs_intro:
              cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
      then have dom_lhs: 
        "\<D>\<^sub>\<circ> ((?\<KK>ru b \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<CC> [\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>, f]\<^sub>\<circ>)\<lparr>ArrVal\<rparr>) =
          Hom \<CC> r a"
          by (cs_concl cs_simp: cat_cs_simps)
      from assms that \<MM>a have f_a: 
        "\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<KK>ru a :
          Hom \<CC> r a \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<KK>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
        by (cs_concl cs_intro: cat_cs_intros)
      then have dom_rhs: 
        "\<D>\<^sub>\<circ> ((\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<KK>ru a)\<lparr>ArrVal\<rparr>) = Hom \<CC> r a"
        by (cs_concl cs_simp: cat_cs_simps)

      have [cat_cs_simps]:
        "?\<KK>ru b \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<CC> [\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>, f]\<^sub>\<circ> =
          \<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<KK>ru a"
      proof(rule arr_Set_eqI[of \<alpha>])

        from b_f show arr_Set_b_f:
          "arr_Set \<alpha> (?\<KK>ru b \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<CC> [\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>, f]\<^sub>\<circ>)"
          by (auto simp: cat_Set_is_arrD(1))
        interpret b_f: arr_Set \<alpha> \<open>?\<KK>ru b \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<CC> [\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>, f]\<^sub>\<circ>\<close>
          by (rule arr_Set_b_f)
        from f_a show arr_Set_f_a:
          "arr_Set \<alpha> (\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<KK>ru a)"
          by (auto simp: cat_Set_is_arrD(1))
        interpret f_a: arr_Set \<alpha> \<open>\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<KK>ru a\<close>
          by (rule arr_Set_f_a)

        show 
          "(?\<KK>ru b \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<CC> [\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>, f]\<^sub>\<circ>)\<lparr>ArrVal\<rparr> =
            (\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<KK>ru a)\<lparr>ArrVal\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs in_Hom_iff)
          fix q assume "q : r \<mapsto>\<^bsub>\<CC>\<^esub> a"
          from category_axioms assms that this \<MM>a \<MM>b show 
            "(?\<KK>ru b \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<CC> [\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>, f]\<^sub>\<circ>)\<lparr>ArrVal\<rparr>\<lparr>q\<rparr> =
              (\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<KK>ru a)\<lparr>ArrVal\<rparr>\<lparr>q\<rparr>"
            by 
              (
                cs_concl
                  cs_simp: cat_cs_simps cat_op_simps
                  cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
              )
        qed (use arr_Set_b_f arr_Set_f_a in auto)

      qed (use b_f f_a in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+
  
      from that category_axioms assms \<MM>a \<MM>b show ?thesis
        by
          (
            cs_concl
              cs_simp: V_cs_simps cat_cs_simps cat_op_simps 
              cs_intro: cat_cs_intros
          )
    
    qed

  qed (auto simp: assms(2) cat_cs_intros)

qed



subsection\<open>Yoneda Lemma\<close>

text\<open>
The following lemma is approximately equivalent to the Yoneda Lemma 
stated in subsection 1.15 in \cite{bodo_categories_1970} 
(the first two conclusions correspond to the statement of the 
Yoneda lemma in Chapter III-2 in \cite{mac_lane_categories_2010}).
\<close>

lemma (in category) cat_Yoneda_Lemma: 
  assumes "\<KK> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>" and "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "v11 (Yoneda_map \<alpha> \<KK> r)" 
    and "\<R>\<^sub>\<circ> (Yoneda_map \<alpha> \<KK> r) = \<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
    and "(Yoneda_map \<alpha> \<KK> r)\<inverse>\<^sub>\<circ> = (\<lambda>u\<in>\<^sub>\<circ>\<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>. Yoneda_arrow \<alpha> \<KK> r u)"
proof-

  interpret \<KK>: is_functor \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<KK> by (rule assms(1)) 

  from assms(2) \<KK>.HomCod.cat_Obj_vsubset_Vset \<KK>.cf_ObjMap_app_in_HomCod_Obj 
  have \<KK>r_in_Vset: "\<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by auto

  show Ym: "v11 (Yoneda_map \<alpha> \<KK> r)"
  proof(intro vsv.vsv_valeq_v11I, unfold \<KK>.Yoneda_map_vdomain these_ntcfs_iff)

    fix \<MM> \<NN>
    assume prems: 
      "\<MM> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-) \<mapsto>\<^sub>C\<^sub>F \<KK> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      "\<NN> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-) \<mapsto>\<^sub>C\<^sub>F \<KK> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      "Yoneda_map \<alpha> \<KK> r\<lparr>\<MM>\<rparr> = Yoneda_map \<alpha> \<KK> r\<lparr>\<NN>\<rparr>"
    from prems(3) have \<MM>r_\<NN>r:
      "\<MM>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>"
      unfolding 
        Yoneda_map_app[OF assms(1) prems(1)] 
        Yoneda_map_app[OF assms(1) prems(2)]
      by simp

    interpret \<MM>: is_ntcf \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)\<close> \<KK> \<MM>  
      by (rule prems(1))
    interpret \<NN>: is_ntcf \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)\<close> \<KK> \<NN> 
      by (rule prems(2))

    show "\<MM> = \<NN>"
    proof
      (
        rule ntcf_eqI[OF prems(1,2)]; 
        (rule refl)?;
        rule vsv_eqI, 
        unfold \<MM>.ntcf_NTMap_vdomain \<NN>.ntcf_NTMap_vdomain
      )

      fix d assume prems': "d \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"

      note \<MM>d_simps = cat_Set_is_arrD[OF \<MM>.ntcf_NTMap_is_arr[OF prems']]
      interpret \<MM>d: arr_Set \<alpha> \<open>\<MM>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>\<close> by (rule \<MM>d_simps(1))

      note \<NN>d_simps = cat_Set_is_arrD[OF \<NN>.ntcf_NTMap_is_arr[OF prems']]
      interpret \<NN>d: arr_Set \<alpha> \<open>\<NN>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>\<close> by (rule \<NN>d_simps(1))

      show "\<MM>\<lparr>NTMap\<rparr>\<lparr>d\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>"
      proof(rule arr_Set_eqI[of \<alpha>])
        show "\<MM>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>\<lparr>ArrVal\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>\<lparr>ArrVal\<rparr>"
        proof
          (
            rule vsv_eqI, 
            unfold 
              \<NN>d.arr_Set_ArrVal_vdomain 
              \<MM>d.arr_Set_ArrVal_vdomain  
              \<MM>d_simps
              \<NN>d_simps
          )
          fix f assume prems'': "f \<in>\<^sub>\<circ> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)\<lparr>ObjMap\<rparr>\<lparr>d\<rparr>"
          from prems'' prems' category_axioms assms(2) have f: "f : r \<mapsto>\<^bsub>\<CC>\<^esub> d"
            by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_op_intros)
          from \<MM>.ntcf_Comp_commute[OF f] have 
            "(
              \<MM>\<lparr>NTMap\<rparr>\<lparr>d\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>
            )\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr> =
              (\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> \<MM>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>)\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>"
            by simp
          from this category_axioms assms(2) f prems prems' have \<MM>df:
            "\<MM>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> =
              \<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<MM>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>\<rparr>"
            by 
              (
                cs_prems
                  cs_simp: cat_cs_simps cat_op_simps 
                  cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
              )
          from \<NN>.ntcf_Comp_commute[OF f] have
            "(
              \<NN>\<lparr>NTMap\<rparr>\<lparr>d\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> 
              Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>
            )\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr> = 
              (\<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>)\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>"
            by simp
          from this category_axioms assms(2) f prems prems' have \<NN>df:
            "\<NN>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> =
              \<KK>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<NN>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr>\<rparr>"
            by
              (
                cs_prems
                  cs_simp: cat_cs_simps cat_op_simps 
                  cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
              )
          show "\<MM>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>d\<rparr>\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
            unfolding \<MM>df \<NN>df \<MM>r_\<NN>r by simp
        qed auto

      qed (simp_all add: \<MM>d_simps \<NN>d_simps)

    qed auto

  qed (auto simp: Yoneda_map_vsv)

  interpret Ym: v11 \<open>Yoneda_map \<alpha> \<KK> r\<close> by (rule Ym)

  have YY: "Yoneda_map \<alpha> \<KK> r\<lparr>Yoneda_arrow \<alpha> \<KK> r a\<rparr> = a" 
    if "a \<in>\<^sub>\<circ> \<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>" for a
  proof-
    note cat_Yoneda_arrow_is_ntcf[OF assms that]
    moreover with assms have Ya: "Yoneda_arrow \<alpha> \<KK> r a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (Yoneda_map \<alpha> \<KK> r)" 
      by (cs_concl cs_simp: these_ntcfs_iff cat_cs_simps cs_intro: cat_cs_intros)
    ultimately show "Yoneda_map \<alpha> \<KK> r\<lparr>Yoneda_arrow \<alpha> \<KK> r a\<rparr> = a"
      using assms that \<KK>r_in_Vset
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed        

  show [simp]: "\<R>\<^sub>\<circ> (Yoneda_map \<alpha> \<KK> r) = \<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
  proof(intro vsubset_antisym)

    show "\<R>\<^sub>\<circ> (Yoneda_map \<alpha> \<KK> r) \<subseteq>\<^sub>\<circ> \<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
      unfolding Yoneda_map_def
    proof(intro vrange_VLambda_vsubset, unfold these_ntcfs_iff \<KK>.cf_HomDom)
      fix \<MM> assume prems: "\<MM> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-) \<mapsto>\<^sub>C\<^sub>F \<KK> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      then interpret \<MM>: is_ntcf \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)\<close> \<KK> \<MM> .
      note \<MM>r_simps = cat_Set_is_arrD[OF \<MM>.ntcf_NTMap_is_arr[OF assms(2)]]
      interpret \<MM>r: arr_Set \<alpha> \<open>\<MM>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<close> by (rule \<MM>r_simps(1))
      from prems category_axioms assms(2) have 
        "\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<MM>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>)"
        unfolding \<MM>r.arr_Set_ArrVal_vdomain \<MM>r_simps
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)
      then have "\<MM>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<MM>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>)"
        by (blast elim: \<MM>r.ArrVal.vsv_value)
      then show "\<MM>\<lparr>NTMap\<rparr>\<lparr>r\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>\<rparr> \<in>\<^sub>\<circ> \<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
        by (auto simp: \<MM>r_simps dest!: vsubsetD[OF \<MM>r.arr_Set_ArrVal_vrange])
    qed
    
    show "\<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (Yoneda_map \<alpha> \<KK> r)"
    proof(intro vsubsetI)
      fix u assume prems: "u \<in>\<^sub>\<circ> \<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
      from cat_Yoneda_arrow_is_ntcf[OF assms prems] have 
        "Yoneda_arrow \<alpha> \<KK> r u \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (Yoneda_map \<alpha> \<KK> r)" 
        by (cs_concl cs_simp: these_ntcfs_iff cat_cs_simps cs_intro: cat_cs_intros)
      with YY[OF prems] show "u \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (Yoneda_map \<alpha> \<KK> r)" 
        by (force dest!: vdomain_atD)
    qed

  qed

  show "(Yoneda_map \<alpha> \<KK> r)\<inverse>\<^sub>\<circ> = (\<lambda>u\<in>\<^sub>\<circ>\<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>. Yoneda_arrow \<alpha> \<KK> r u)"
  proof(rule vsv_eqI, unfold vdomain_vconverse vdomain_VLambda)
    from Ym show "vsv ((Yoneda_map \<alpha> \<KK> r)\<inverse>\<^sub>\<circ>)" by auto
    show "(Yoneda_map \<alpha> \<KK> r)\<inverse>\<^sub>\<circ>\<lparr>a\<rparr> = (\<lambda>u\<in>\<^sub>\<circ>\<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>. Yoneda_arrow \<alpha> \<KK> r u)\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (Yoneda_map \<alpha> \<KK> r)" for a
    proof-
      from that have a: "a \<in>\<^sub>\<circ> \<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>" by simp
      note Ya = cat_Yoneda_arrow_is_ntcf[OF assms a]
      then have "Yoneda_arrow \<alpha> \<KK> r a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (Yoneda_map \<alpha> \<KK> r)"
        by 
          (
            cs_concl 
              cs_simp: these_ntcfs_iff cat_cs_simps cs_intro: cat_cs_intros
          )
      with Ya YY[OF a] a show ?thesis
        by 
          (
            intro Ym.v11_vconverse_app[
              unfolded \<KK>.Yoneda_map_vdomain these_ntcfs_iff
              ]
          )
          (simp_all add: these_ntcfs_iff cat_cs_simps)
    qed
  qed auto

qed



subsection\<open>Inverse of the Yoneda map\<close>

lemma (in category) inv_Yoneda_map_v11: 
  assumes "\<KK> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>" and "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "v11 ((Yoneda_map \<alpha> \<KK> r)\<inverse>\<^sub>\<circ>)"
  using cat_Yoneda_Lemma(1)[OF assms] by (simp add: v11.v11_vconverse)

lemma (in category) inv_Yoneda_map_vdomain: 
  assumes "\<KK> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>" and "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> ((Yoneda_map \<alpha> \<KK> r)\<inverse>\<^sub>\<circ>) = \<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
  unfolding cat_Yoneda_Lemma(3)[OF assms] by simp

lemmas [cat_cs_simps] = category.inv_Yoneda_map_vdomain

lemma (in category) inv_Yoneda_map_app: 
  assumes "\<KK> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>" and "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "u \<in>\<^sub>\<circ> \<KK>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
  shows "(Yoneda_map \<alpha> \<KK> r)\<inverse>\<^sub>\<circ>\<lparr>u\<rparr> = Yoneda_arrow \<alpha> \<KK> r u"
  using assms(3) unfolding cat_Yoneda_Lemma(3)[OF assms(1,2)] by simp

lemmas [cat_cs_simps] = category.inv_Yoneda_map_app

lemma (in category) inv_Yoneda_map_vrange: 
  assumes "\<KK> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "\<R>\<^sub>\<circ> ((Yoneda_map \<alpha> \<KK> r)\<inverse>\<^sub>\<circ>) =
    these_ntcfs \<alpha> \<CC> (cat_Set \<alpha>) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-) \<KK>"
proof-
  interpret \<KK>: is_functor \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<KK> by (rule assms(1)) 
  show ?thesis unfolding Yoneda_map_def by (simp add: cat_cs_simps)
qed



subsection\<open>
Component of a composition of a \<open>Hom\<close>-natural transformation 
with natural transformations
\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The following definition is merely a technical generalization
that is used in the context of the description of the 
composition of a \<open>Hom\<close>-natural transformation with a natural transformation
later in this section
(also see subsection 1.15 in \cite{bodo_categories_1970}).
\<close>

definition ntcf_Hom_component :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_Hom_component \<phi> \<psi> a b =
    [
      (
        \<lambda>f\<in>\<^sub>\<circ>Hom (\<phi>\<lparr>NTDGCod\<rparr>) (\<phi>\<lparr>NTCod\<rparr>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<psi>\<lparr>NTDom\<rparr>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>).
          \<psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<psi>\<lparr>NTDGCod\<rparr>\<^esub> f \<circ>\<^sub>A\<^bsub>\<psi>\<lparr>NTDGCod\<rparr>\<^esub> \<phi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>
      ),
      Hom (\<phi>\<lparr>NTDGCod\<rparr>) (\<phi>\<lparr>NTCod\<rparr>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<psi>\<lparr>NTDom\<rparr>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>),
      Hom (\<phi>\<lparr>NTDGCod\<rparr>) (\<phi>\<lparr>NTDom\<rparr>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<psi>\<lparr>NTCod\<rparr>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma ntcf_Hom_component_components: 
  shows "ntcf_Hom_component \<phi> \<psi> a b\<lparr>ArrVal\<rparr> =
    (
      \<lambda>f\<in>\<^sub>\<circ>Hom (\<phi>\<lparr>NTDGCod\<rparr>) (\<phi>\<lparr>NTCod\<rparr>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<psi>\<lparr>NTDom\<rparr>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>).
        \<psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<psi>\<lparr>NTDGCod\<rparr>\<^esub> f \<circ>\<^sub>A\<^bsub>\<psi>\<lparr>NTDGCod\<rparr>\<^esub> \<phi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>
    )"
    and "ntcf_Hom_component \<phi> \<psi> a b\<lparr>ArrDom\<rparr> =
      Hom (\<phi>\<lparr>NTDGCod\<rparr>) (\<phi>\<lparr>NTCod\<rparr>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<psi>\<lparr>NTDom\<rparr>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    and "ntcf_Hom_component \<phi> \<psi> a b\<lparr>ArrCod\<rparr> =
      Hom (\<phi>\<lparr>NTDGCod\<rparr>) (\<phi>\<lparr>NTDom\<rparr>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<psi>\<lparr>NTCod\<rparr>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
  unfolding ntcf_Hom_component_def arr_field_simps 
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Arrow value\<close>

mk_VLambda ntcf_Hom_component_components(1)
  |vsv ntcf_Hom_component_ArrVal_vsv[intro]|

context
  fixes \<alpha> \<phi> \<psi> \<FF> \<GG> \<FF>' \<GG>' \<AA> \<BB> \<CC>
  assumes \<phi>: "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and \<psi>: "\<psi> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
begin

interpretation \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule \<phi>)
interpretation \<psi>: is_ntcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<psi> by (rule \<psi>)

mk_VLambda 
  ntcf_Hom_component_components(1)
    [
      of \<phi> \<psi>, 
      unfolded 
        \<phi>.ntcf_NTDom \<psi>.ntcf_NTDom 
        \<phi>.ntcf_NTCod \<psi>.ntcf_NTCod 
        \<phi>.ntcf_NTDGDom \<psi>.ntcf_NTDGDom
        \<phi>.ntcf_NTDGCod \<psi>.ntcf_NTDGCod
    ]
  |vdomain ntcf_Hom_component_ArrVal_vdomain|
  |app ntcf_Hom_component_ArrVal_app[unfolded in_Hom_iff]|

lemmas [cat_cs_simps] = 
  ntcf_Hom_component_ArrVal_vdomain
  ntcf_Hom_component_ArrVal_app

lemma ntcf_Hom_component_ArrVal_vrange:
  assumes "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows 
    "\<R>\<^sub>\<circ> (ntcf_Hom_component \<phi> \<psi> a b\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ>
      Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<GG>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
proof
  (
    rule vsv.vsv_vrange_vsubset, 
    unfold ntcf_Hom_component_ArrVal_vdomain in_Hom_iff
  )
  fix f assume "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
  with assms \<phi> \<psi> show 
    "ntcf_Hom_component \<phi> \<psi> a b\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed (rule ntcf_Hom_component_ArrVal_vsv)

end


subsubsection\<open>Arrow domain and codomain\<close>

context
  fixes \<alpha> \<phi> \<psi> \<FF> \<GG> \<FF>' \<GG>' \<AA> \<BB> \<CC>
  assumes \<phi>: "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and \<psi>: "\<psi> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
begin

interpretation \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule \<phi>)
interpretation \<psi>: is_ntcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<psi> by (rule \<psi>)

lemma ntcf_Hom_component_ArrDom[cat_cs_simps]:
  "ntcf_Hom_component \<phi> \<psi> a b\<lparr>ArrDom\<rparr> = Hom \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
  unfolding ntcf_Hom_component_components by (simp add: cat_cs_simps)

lemma ntcf_Hom_component_ArrCod[cat_cs_simps]:
  "ntcf_Hom_component \<phi> \<psi> a b\<lparr>ArrCod\<rparr> = Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<GG>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
  unfolding ntcf_Hom_component_components by (simp add: cat_cs_simps)

end


subsubsection\<open>
Component of a composition of a \<open>Hom\<close>-natural transformation 
with natural transformations is an arrow in the category \<open>Set\<close>
\<close>

lemma (in category) cat_ntcf_Hom_component_is_arr:
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<psi> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "a \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows 
    "ntcf_Hom_component \<phi> \<psi> a b :
      Hom \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub>
      Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<GG>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
proof-
  
  interpret \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))
  interpret \<psi>: is_ntcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<psi> by (rule assms(2))

  from assms have a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" unfolding cat_op_simps by simp

  show ?thesis
  proof(intro cat_Set_is_arrI arr_SetI)
    show "vfsequence (ntcf_Hom_component \<phi> \<psi> a b)"
      unfolding ntcf_Hom_component_def by (simp add: nat_omega_simps)
    show "vcard (ntcf_Hom_component \<phi> \<psi> a b) = 3\<^sub>\<nat>"
      unfolding ntcf_Hom_component_def by (simp add: nat_omega_simps)
    from assms ntcf_Hom_component_ArrVal_vrange[OF assms(1,2) a assms(4)] show 
      "\<R>\<^sub>\<circ> (ntcf_Hom_component \<phi> \<psi> a b\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> 
        ntcf_Hom_component \<phi> \<psi> a b\<lparr>ArrCod\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps)
    from assms(1,2,4) a show "ntcf_Hom_component \<phi> \<psi> a b\<lparr>ArrDom\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from assms(1,2,4) a show "ntcf_Hom_component \<phi> \<psi> a b\<lparr>ArrCod\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed (use assms in \<open>auto simp: ntcf_Hom_component_components cat_cs_simps\<close>)

qed

lemma (in category) cat_ntcf_Hom_component_is_arr':
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<psi> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "a \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    and "\<AA>' = Hom \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    and "\<BB>' = Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<GG>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    and "\<CC>' = cat_Set \<alpha>"
  shows "ntcf_Hom_component \<phi> \<psi> a b : \<AA>' \<mapsto>\<^bsub>\<CC>'\<^esub> \<BB>'"
  using assms(1-4) unfolding assms(5-7) by (rule cat_ntcf_Hom_component_is_arr)
  
lemmas [cat_cs_intros] = category.cat_ntcf_Hom_component_is_arr'


subsubsection\<open>
Naturality of the components of a composition of 
a \<open>Hom\<close>-natural transformation with natural transformations
\<close>

lemma (in category) cat_ntcf_Hom_component_nat:
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<psi> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "g : a \<mapsto>\<^bsub>op_cat \<AA>\<^esub> a'"
    and "f : b \<mapsto>\<^bsub>\<BB>\<^esub> b'" 
  shows
    "ntcf_Hom_component \<phi> \<psi> a' b' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
     cf_hom \<CC> [\<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>, \<FF>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>]\<^sub>\<circ> =
      cf_hom \<CC> [\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>, \<GG>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
      ntcf_Hom_component \<phi> \<psi> a b"
proof-

  let ?Y_ab = \<open>ntcf_Hom_component \<phi> \<psi> a b\<close>
    and ?Y_a'b' = \<open>ntcf_Hom_component \<phi> \<psi> a' b'\<close>
    and ?\<GG>g = \<open>\<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>\<close>
    and ?\<FF>'f = \<open>\<FF>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<close>
    and ?\<FF>g = \<open>\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>\<close>
    and ?\<GG>'f = \<open>\<GG>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<close>
    and ?\<GG>a = \<open>\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<close>
    and ?\<FF>'b = \<open>\<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<close>
    and ?\<FF>a' = \<open>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>\<close>
    and ?\<GG>'b' = \<open>\<GG>'\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>\<close>

  interpret \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))
  interpret \<psi>: is_ntcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<psi> by (rule assms(2))
  interpret Set: category \<alpha> \<open>cat_Set \<alpha>\<close> by (rule category_cat_Set)

  from assms(3) have g: "g : a' \<mapsto>\<^bsub>\<AA>\<^esub> a" unfolding cat_op_simps by simp

  from Set.category_axioms category_axioms assms g have a'b_Gg\<FF>'f:
    "?Y_a'b' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<CC> [?\<GG>g, ?\<FF>'f]\<^sub>\<circ> :
      Hom \<CC> ?\<GG>a ?\<FF>'b \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> ?\<FF>a' ?\<GG>'b'"
    by 
      (
        cs_concl
          cs_simp: cat_cs_simps cat_op_simps 
          cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
      )
  then have dom_lhs: 
    "\<D>\<^sub>\<circ> ((?Y_a'b' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<CC> [?\<GG>g, ?\<FF>'f]\<^sub>\<circ>)\<lparr>ArrVal\<rparr>) = 
      Hom \<CC> ?\<GG>a ?\<FF>'b"
    by (cs_concl cs_simp: cat_cs_simps)
  from Set.category_axioms category_axioms assms g have \<FF>g\<GG>'f_ab: 
    "cf_hom \<CC> [?\<FF>g, ?\<GG>'f]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?Y_ab : 
      Hom \<CC> ?\<GG>a ?\<FF>'b \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> ?\<FF>a' ?\<GG>'b'"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps cat_op_simps 
          cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
      )
  then have dom_rhs: 
    "\<D>\<^sub>\<circ> ((cf_hom \<CC> [?\<FF>g, ?\<GG>'f]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?Y_ab)\<lparr>ArrVal\<rparr>) =
      Hom \<CC> ?\<GG>a ?\<FF>'b"
    by (cs_concl cs_simp: cat_cs_simps)

  show ?thesis
  proof(rule arr_Set_eqI[of \<alpha>])
    from a'b_Gg\<FF>'f show arr_Set_a'b_Gg\<FF>'f:
      "arr_Set \<alpha> (?Y_a'b' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<CC> [?\<GG>g, ?\<FF>'f]\<^sub>\<circ>)"
      by (auto dest: cat_Set_is_arrD(1))
    from \<FF>g\<GG>'f_ab show arr_Set_\<FF>g\<GG>'f_ab: 
      "arr_Set \<alpha> (cf_hom \<CC> [?\<FF>g, ?\<GG>'f]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?Y_ab)"
      by (auto dest: cat_Set_is_arrD(1))
    show 
      "(?Y_a'b' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<CC> [?\<GG>g, ?\<FF>'f]\<^sub>\<circ>)\<lparr>ArrVal\<rparr> =
        (cf_hom \<CC> [?\<FF>g, ?\<GG>'f]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?Y_ab)\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs in_Hom_iff)
      fix h assume prems: "h : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      from assms(1,2) g have [cat_cs_simps]:
        "\<psi>\<lparr>NTMap\<rparr>\<lparr>b'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (?\<FF>'f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (?\<GG>g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<phi>\<lparr>NTMap\<rparr>\<lparr>a'\<rparr>))) =
          \<psi>\<lparr>NTMap\<rparr>\<lparr>b'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (?\<FF>'f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<phi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<FF>g)))"
        by (cs_concl cs_simp: is_ntcf.ntcf_Comp_commute cs_intro: cat_cs_intros)
      also from assms(1,2,4) prems g have "\<dots> =
        (((\<psi>\<lparr>NTMap\<rparr>\<lparr>b'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<FF>'f) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<phi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<FF>g"
        by (cs_concl cs_simp: cat_Comp_assoc cs_intro: cat_cs_intros) (*slow*)
      also from assms(1,2,4) have "\<dots> =
        (((?\<GG>'f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<phi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<FF>g"
        by (cs_concl cs_simp: is_ntcf.ntcf_Comp_commute cs_intro: cat_cs_intros)
      also from assms(1,2,4) prems g have "\<dots> =
        ?\<GG>'f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<phi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<FF>g)))"
        by (cs_concl cs_simp: cat_Comp_assoc cs_intro: cat_cs_intros) (*slow*)
      finally have nat:
        "\<psi>\<lparr>NTMap\<rparr>\<lparr>b'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (?\<FF>'f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (?\<GG>g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<phi>\<lparr>NTMap\<rparr>\<lparr>a'\<rparr>))) =
          ?\<GG>'f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<phi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?\<FF>g)))".
      from prems Set.category_axioms category_axioms assms(1,2,4) g show 
        "(?Y_a'b' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cf_hom \<CC> [?\<GG>g, ?\<FF>'f]\<^sub>\<circ>)\<lparr>ArrVal\<rparr>\<lparr>h\<rparr> =
          (cf_hom \<CC> [?\<FF>g, ?\<GG>'f]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?Y_ab)\<lparr>ArrVal\<rparr>\<lparr>h\<rparr>"
        by (*slow*)
          (
            cs_concl
              cs_simp: nat cat_cs_simps cat_op_simps 
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
    qed (use arr_Set_a'b_Gg\<FF>'f arr_Set_\<FF>g\<GG>'f_ab in auto)

  qed (use a'b_Gg\<FF>'f \<FF>g\<GG>'f_ab in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+

qed


subsubsection\<open>
Composition of the components of a composition of a \<open>Hom\<close>-natural 
transformation with natural transformations
\<close>

lemma (in category) cat_ntcf_Hom_component_Comp:
  assumes "\<phi>' : \<GG> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<psi>' : \<GG>' \<mapsto>\<^sub>C\<^sub>F \<HH>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<psi> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows 
    "ntcf_Hom_component \<phi> \<psi>' a b \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ntcf_Hom_component \<phi>' \<psi> a b =
      ntcf_Hom_component (\<phi>' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<phi>) (\<psi>' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<psi>) a b"
    (is \<open>?\<phi>\<psi>' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<phi>'\<psi> = ?\<phi>'\<phi>\<psi>'\<psi>\<close>)
proof-

  interpret Set: category \<alpha> \<open>cat_Set \<alpha>\<close> by (rule category_cat_Set)

  from assms Set.category_axioms category_axioms have \<phi>\<psi>'_\<phi>'\<psi>: 
    "?\<phi>\<psi>' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<phi>'\<psi> :
      Hom \<CC> (\<HH>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub>
      Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<HH>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"    
    by (cs_concl cs_intro: cat_cs_intros cat_op_intros)
  then have dom_lhs: 
    "\<D>\<^sub>\<circ> ((?\<phi>\<psi>' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<phi>'\<psi>)\<lparr>ArrVal\<rparr>) = 
      Hom \<CC> (\<HH>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    by (cs_concl cs_simp: cat_cs_simps)
  from assms Set.category_axioms category_axioms have \<phi>'\<phi>\<psi>'\<psi>: 
    "?\<phi>'\<phi>\<psi>'\<psi> :
      Hom \<CC> (\<HH>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub>
      Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<HH>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"    
    by (cs_concl cs_intro: cat_cs_intros cat_op_intros)
  then have dom_rhs: 
    "\<D>\<^sub>\<circ> (?\<phi>'\<phi>\<psi>'\<psi>\<lparr>ArrVal\<rparr>) = Hom \<CC> (\<HH>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)" 
    by (cs_concl cs_simp: cat_cs_simps)

  show ?thesis
  proof(rule arr_Set_eqI[of \<alpha>])
    from \<phi>\<psi>'_\<phi>'\<psi> show arr_Set_\<phi>\<psi>'_\<phi>'\<psi>: "arr_Set \<alpha> (?\<phi>\<psi>' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<phi>'\<psi>)"
      by (auto dest: cat_Set_is_arrD(1))
    from \<phi>'\<phi>\<psi>'\<psi> show arr_Set_\<phi>'\<phi>\<psi>'\<psi>: "arr_Set \<alpha> ?\<phi>'\<phi>\<psi>'\<psi>"
      by (auto dest: cat_Set_is_arrD(1))
    show "(?\<phi>\<psi>' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<phi>'\<psi>)\<lparr>ArrVal\<rparr> = ?\<phi>'\<phi>\<psi>'\<psi>\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs in_Hom_iff)
      fix f assume "f : \<HH>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      with category_axioms assms Set.category_axioms show 
        "(?\<phi>\<psi>' \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<phi>'\<psi>)\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> = ?\<phi>'\<phi>\<psi>'\<psi>\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
        by 
          (
            cs_concl
              cs_simp: cat_cs_simps 
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
    qed (use arr_Set_\<phi>'\<phi>\<psi>'\<psi> arr_Set_\<phi>\<psi>'_\<phi>'\<psi> in auto)
    
  qed (use \<phi>\<psi>'_\<phi>'\<psi> \<phi>'\<phi>\<psi>'\<psi> in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+

qed

lemmas [cat_cs_simps] = category.cat_ntcf_Hom_component_Comp


subsubsection\<open>
Component of a composition of \<open>Hom\<close>-natural 
transformation with the identity natural transformations
\<close>

lemma (in category) cat_ntcf_Hom_component_ntcf_id:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<FF>': \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows 
    "ntcf_Hom_component (ntcf_id \<FF>) (ntcf_id \<FF>') a b =
      cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)\<rparr>"
    (is \<open>?\<FF>\<FF>' = cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>?\<FF>a\<FF>'b\<rparr>\<close>)
proof-

  interpret \<FF>: is_functor \<alpha> \<AA> \<CC> \<FF> by (rule assms(1))
  interpret \<FF>': is_functor \<alpha> \<BB> \<CC> \<FF>' by (rule assms(2))
  interpret Set: category \<alpha> \<open>cat_Set \<alpha>\<close> by (rule category_cat_Set)

  from assms Set.category_axioms category_axioms have \<FF>\<FF>': 
    "?\<FF>\<FF>' :
      Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub>
      Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"    
    by (cs_concl cs_intro: cat_cs_intros cat_op_intros)
  then have dom_lhs: "\<D>\<^sub>\<circ> (?\<FF>\<FF>'\<lparr>ArrVal\<rparr>) = Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    by (cs_concl cs_simp: cat_cs_simps)

  from category_axioms assms Set.category_axioms have \<FF>a\<FF>'b: 
    "cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>?\<FF>a\<FF>'b\<rparr> :
      Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub>
      Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    by 
      (
        cs_concl cs_full 
          cs_simp: cat_Set_cs_simps cat_Set_components(1) 
          cs_intro: cat_cs_intros
      )
  then have dom_rhs: 
    "\<D>\<^sub>\<circ> (cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>?\<FF>a\<FF>'b\<rparr>\<lparr>ArrVal\<rparr>) = Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    by (cs_concl cs_simp: cat_cs_simps)

  show ?thesis
  proof(rule arr_Set_eqI[of \<alpha>])
    from \<FF>\<FF>' show arr_Set_\<FF>\<psi>: "arr_Set \<alpha> ?\<FF>\<FF>'" 
      by (auto dest: cat_Set_is_arrD(1))
    from \<FF>a\<FF>'b show arr_Set_\<FF>a\<FF>'b: "arr_Set \<alpha> (cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>?\<FF>a\<FF>'b\<rparr>)" 
      by (auto dest: cat_Set_is_arrD(1))
    show "?\<FF>\<FF>'\<lparr>ArrVal\<rparr> = cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>?\<FF>a\<FF>'b\<rparr>\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs in_Hom_iff)  
      fix f assume "f : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<FF>'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      with category_axioms Set.category_axioms assms show 
        "?\<FF>\<FF>'\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> = cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>?\<FF>a\<FF>'b\<rparr>\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros) 
    qed (use arr_Set_\<FF>a\<FF>'b in auto)
      
  qed (use \<FF>\<FF>' \<FF>a\<FF>'b in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+

qed

lemmas [cat_cs_simps] = category.cat_ntcf_Hom_component_ntcf_id



subsection\<open>
Component of a composition of a \<open>Hom\<close>-natural transformation 
with a natural transformation
\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition ntcf_lcomp_Hom_component :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_lcomp_Hom_component \<phi> a b =
    ntcf_Hom_component \<phi> (ntcf_id (cf_id (\<phi>\<lparr>NTDGCod\<rparr>))) a b"

definition ntcf_rcomp_Hom_component :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_rcomp_Hom_component \<psi> a b =
    ntcf_Hom_component (ntcf_id (cf_id (\<psi>\<lparr>NTDGCod\<rparr>))) \<psi> a b"


subsubsection\<open>Arrow value\<close>

lemma ntcf_lcomp_Hom_component_ArrVal_vsv: 
  "vsv (ntcf_lcomp_Hom_component \<phi> a b\<lparr>ArrVal\<rparr>)"
  unfolding ntcf_lcomp_Hom_component_def by (rule ntcf_Hom_component_ArrVal_vsv)

lemma ntcf_rcomp_Hom_component_ArrVal_vsv: 
  "vsv (ntcf_rcomp_Hom_component \<psi> a b\<lparr>ArrVal\<rparr>)"
  unfolding ntcf_rcomp_Hom_component_def by (rule ntcf_Hom_component_ArrVal_vsv)

lemma ntcf_lcomp_Hom_component_ArrVal_vdomain[cat_cs_simps]: 
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (ntcf_lcomp_Hom_component \<phi> a b\<lparr>ArrVal\<rparr>) = Hom \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) b"
proof-
  interpret \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))
  show ?thesis
    using assms
    unfolding ntcf_lcomp_Hom_component_def \<phi>.ntcf_NTDGCod
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed

lemma ntcf_rcomp_Hom_component_ArrVal_vdomain[cat_cs_simps]: 
  assumes "\<psi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (ntcf_rcomp_Hom_component \<psi> a b\<lparr>ArrVal\<rparr>) = Hom \<CC> a (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
proof-
  interpret \<psi>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<psi> by (rule assms(1))
  show ?thesis
    using assms
    unfolding cat_op_simps ntcf_rcomp_Hom_component_def \<psi>.ntcf_NTDGCod
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed

lemma ntcf_lcomp_Hom_component_ArrVal_app[cat_cs_simps]: 
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "a \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "h : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "ntcf_lcomp_Hom_component \<phi> a b\<lparr>ArrVal\<rparr>\<lparr>h\<rparr> = h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<phi>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
proof-
  interpret \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))
  show ?thesis
    using assms
    unfolding cat_op_simps ntcf_lcomp_Hom_component_def \<phi>.ntcf_NTDGCod
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed

lemma ntcf_rcomp_Hom_component_ArrVal_app[cat_cs_simps]: 
  assumes "\<psi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    and "h : a \<mapsto>\<^bsub>\<CC>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
  shows "ntcf_rcomp_Hom_component \<psi> a b\<lparr>ArrVal\<rparr>\<lparr>h\<rparr> = \<psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h"
proof-
  interpret \<psi>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<psi> by (rule assms(1))
  show ?thesis
    using assms
    unfolding cat_op_simps ntcf_rcomp_Hom_component_def \<psi>.ntcf_NTDGCod
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed

lemma ntcf_lcomp_Hom_component_ArrVal_vrange: 
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "a \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr>" 
    and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "\<R>\<^sub>\<circ> (ntcf_lcomp_Hom_component \<phi> a b\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) b"
proof-
  interpret \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))
  from assms(2) have a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" unfolding cat_op_simps by simp
  from assms(1,3) a have 
    "\<R>\<^sub>\<circ> (ntcf_lcomp_Hom_component \<phi> a b\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ>
      Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (cf_id \<CC>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    by 
      (
        unfold cat_op_simps ntcf_lcomp_Hom_component_def \<phi>.ntcf_NTDGCod, 
        intro ntcf_Hom_component_ArrVal_vrange
      ) 
      (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)+
  from this assms(3) show ?thesis by (cs_prems cs_simp: cat_cs_simps)
qed

lemma ntcf_rcomp_Hom_component_ArrVal_vrange: 
  assumes "\<psi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<R>\<^sub>\<circ> (ntcf_rcomp_Hom_component \<psi> a b\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> Hom \<CC> a (\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
proof-
  interpret \<psi>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<psi> by (rule assms(1))
  from assms(2) have a: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" unfolding cat_op_simps by simp
  from assms(1,3) a have 
    "\<R>\<^sub>\<circ> (ntcf_rcomp_Hom_component \<psi> a b\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ>
      Hom \<CC> (cf_id \<CC>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    by 
      (
        unfold ntcf_rcomp_Hom_component_def \<psi>.ntcf_NTDGCod, 
        intro ntcf_Hom_component_ArrVal_vrange
      ) 
      (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from this a show ?thesis by (cs_prems cs_simp: cat_cs_simps)
qed


subsubsection\<open>Arrow domain and codomain\<close>

lemma ntcf_lcomp_Hom_component_ArrDom[cat_cs_simps]:
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "ntcf_lcomp_Hom_component \<phi> a b\<lparr>ArrDom\<rparr> = Hom \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) b"
proof-
  interpret \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))
  from assms show ?thesis
    unfolding ntcf_lcomp_Hom_component_def \<phi>.ntcf_NTDGCod
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed

lemma ntcf_rcomp_Hom_component_ArrDom[cat_cs_simps]:
  assumes "\<psi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>"
  shows "ntcf_rcomp_Hom_component \<psi> a b\<lparr>ArrDom\<rparr> = Hom \<CC> a (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
proof-
  interpret \<psi>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<psi> by (rule assms(1))
  from assms show ?thesis
    unfolding cat_op_simps ntcf_rcomp_Hom_component_def \<psi>.ntcf_NTDGCod
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed

lemma ntcf_lcomp_Hom_component_ArrCod[cat_cs_simps]:
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "ntcf_lcomp_Hom_component \<phi> a b\<lparr>ArrCod\<rparr> = Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) b"
proof-
  interpret \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))
  from assms show ?thesis
    unfolding ntcf_lcomp_Hom_component_def \<phi>.ntcf_NTDGCod
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed

lemma ntcf_rcomp_Hom_component_ArrCod[cat_cs_simps]:
  assumes "\<psi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>"
  shows "ntcf_rcomp_Hom_component \<psi> a b\<lparr>ArrCod\<rparr> = Hom \<CC> a (\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)" 
proof-
  interpret \<psi>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<psi> by (rule assms(1))
  from assms show ?thesis
    unfolding cat_op_simps ntcf_rcomp_Hom_component_def \<psi>.ntcf_NTDGCod
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed


subsubsection\<open>
Component of a composition of a \<open>Hom\<close>-natural transformation 
with a natural transformation is an arrow in the category \<open>Set\<close>
\<close>

lemma (in category) cat_ntcf_lcomp_Hom_component_is_arr:
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "a \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr>" 
    and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "ntcf_lcomp_Hom_component \<phi> a b :
    Hom \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) b \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) b"
proof-
  interpret \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))
  from assms have a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" unfolding cat_op_simps by simp
  from assms(1,3) a have 
    "ntcf_lcomp_Hom_component \<phi> a b :
      Hom \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (cf_id \<CC>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> 
      Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (cf_id \<CC>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    unfolding ntcf_lcomp_Hom_component_def \<phi>.ntcf_NTDGCod
    by (intro cat_ntcf_Hom_component_is_arr)
      (cs_concl cs_intro: cat_cs_intros cat_op_intros)+
  from this assms(1,3) a show ?thesis by (cs_prems cs_simp: cat_cs_simps)
qed

lemma (in category) cat_ntcf_lcomp_Hom_component_is_arr':
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "a \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr>" 
    and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<AA>' = Hom \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) b"
    and "\<BB>' = Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) b"
    and "\<CC>' = cat_Set \<alpha>"
  shows "ntcf_lcomp_Hom_component \<phi> a b : \<AA>' \<mapsto>\<^bsub>\<CC>'\<^esub> \<BB>'"
  using assms(1-3) 
  unfolding assms(4-6) 
  by (rule cat_ntcf_lcomp_Hom_component_is_arr)

lemmas [cat_cs_intros] = category.cat_ntcf_lcomp_Hom_component_is_arr'

lemma (in category) cat_ntcf_rcomp_Hom_component_is_arr:
  assumes "\<psi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>" 
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "ntcf_rcomp_Hom_component \<psi> a b :
    Hom \<CC> a (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> a (\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
proof-
  interpret \<psi>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<psi> by (rule assms(1))
  from assms have a: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" unfolding cat_op_simps by simp
  from assms(1,3) a have 
    "ntcf_rcomp_Hom_component \<psi> a b :
      Hom \<CC> (cf_id \<CC>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub>
      Hom \<CC> (cf_id \<CC>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) (\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    unfolding ntcf_rcomp_Hom_component_def \<psi>.ntcf_NTDGCod
    by (intro cat_ntcf_Hom_component_is_arr)
      (cs_concl cs_intro: cat_cs_intros cat_op_intros)
  from this assms(1,3) a show ?thesis by (cs_prems cs_simp: cat_cs_simps)
qed

lemma (in category) cat_ntcf_rcomp_Hom_component_is_arr':
  assumes "\<psi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>" 
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    and "\<AA>' = Hom \<CC> a (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    and "\<BB>' = Hom \<CC> a (\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)"
    and "\<CC>' = cat_Set \<alpha>"
  shows "ntcf_rcomp_Hom_component \<psi> a b : \<AA>' \<mapsto>\<^bsub>\<CC>'\<^esub> \<BB>'"
  using assms(1-3) 
  unfolding assms(4-6)
  by (rule cat_ntcf_rcomp_Hom_component_is_arr)

lemmas [cat_cs_intros] = category.cat_ntcf_rcomp_Hom_component_is_arr'



subsection\<open>
Composition of a \<open>Hom\<close>-natural transformation with two natural transformations
\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See subsection 1.15 in \cite{bodo_categories_1970}.\<close>

definition ntcf_Hom :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (\<open>Hom\<^sub>A\<^sub>.\<^sub>C\<index>'(/_-,_-/')\<close>)
  where "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>-) =
    [
      (
        \<lambda>ab\<in>\<^sub>\<circ>(op_cat (\<phi>\<lparr>NTDGDom\<rparr>) \<times>\<^sub>C \<psi>\<lparr>NTDGDom\<rparr>)\<lparr>Obj\<rparr>.
          ntcf_Hom_component \<phi> \<psi> (vpfst ab) (vpsnd ab)
      ),
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<psi>\<lparr>NTDGCod\<rparr>(\<phi>\<lparr>NTCod\<rparr>-,\<psi>\<lparr>NTDom\<rparr>-),
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<psi>\<lparr>NTDGCod\<rparr>(\<phi>\<lparr>NTDom\<rparr>-,\<psi>\<lparr>NTCod\<rparr>-),
      op_cat (\<phi>\<lparr>NTDGDom\<rparr>) \<times>\<^sub>C \<psi>\<lparr>NTDGDom\<rparr>,
      cat_Set \<alpha>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma ntcf_Hom_components:
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>-)\<lparr>NTMap\<rparr> =
    (
      \<lambda>ab\<in>\<^sub>\<circ>(op_cat (\<phi>\<lparr>NTDGDom\<rparr>) \<times>\<^sub>C \<psi>\<lparr>NTDGDom\<rparr>)\<lparr>Obj\<rparr>.
        ntcf_Hom_component \<phi> \<psi> (vpfst ab) (vpsnd ab)
    )"
    and "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>-)\<lparr>NTDom\<rparr> =
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<psi>\<lparr>NTDGCod\<rparr>(\<phi>\<lparr>NTCod\<rparr>-,\<psi>\<lparr>NTDom\<rparr>-)"
    and "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>-)\<lparr>NTCod\<rparr> =
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<psi>\<lparr>NTDGCod\<rparr>(\<phi>\<lparr>NTDom\<rparr>-,\<psi>\<lparr>NTCod\<rparr>-)"
    and "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>-)\<lparr>NTDGDom\<rparr> = op_cat (\<phi>\<lparr>NTDGDom\<rparr>) \<times>\<^sub>C \<psi>\<lparr>NTDGDom\<rparr>"
    and "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>-)\<lparr>NTDGCod\<rparr> = cat_Set \<alpha>"
  unfolding ntcf_Hom_def nt_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Natural transformation map\<close>

mk_VLambda ntcf_Hom_components(1)
  |vsv ntcf_Hom_NTMap_vsv|

context
  fixes \<alpha> \<phi> \<psi> \<FF> \<GG> \<FF>' \<GG>' \<AA> \<BB> \<CC>
  assumes \<phi>: "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and \<psi>: "\<psi> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
begin

interpretation \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule \<phi>)
interpretation \<psi>: is_ntcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<psi> by (rule \<psi>)

mk_VLambda ntcf_Hom_components(1)[of _ \<phi> \<psi>, simplified]
  |vdomain ntcf_Hom_NTMap_vdomain[unfolded in_Hom_iff]|

lemmas [cat_cs_simps] = ntcf_Hom_NTMap_vdomain

lemma ntcf_Hom_NTMap_app[cat_cs_simps]:
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (op_cat \<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>-)\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> = ntcf_Hom_component \<phi> \<psi> a b"
  using assms
  unfolding ntcf_Hom_components
  by (simp add: nat_omega_simps cat_cs_simps)

end

lemma (in category) ntcf_Hom_NTMap_vrange: 
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<psi> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<R>\<^sub>\<circ> (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>-)\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Arr\<rparr>"
proof-
  interpret \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))
  interpret \<psi>: is_ntcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<psi> by (rule assms(2))
  show ?thesis
  proof
    (
      rule vsv.vsv_vrange_vsubset, 
      unfold ntcf_Hom_NTMap_vdomain[OF assms] cat_cs_simps
    )
    fix ab assume "ab \<in>\<^sub>\<circ> (op_cat \<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
    then obtain a b
      where ab_def: "ab = [a, b]\<^sub>\<circ>" 
        and a: "a \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr>" 
        and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
      by 
        (
          rule cat_prod_2_ObjE[
            OF \<phi>.NTDom.HomDom.category_op \<psi>.NTDom.HomDom.category_axioms
            ]
        )
    from assms a b category_cat_Set category_axioms show 
      "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>-)\<lparr>NTMap\<rparr>\<lparr>ab\<rparr> \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Arr\<rparr>"
      unfolding ab_def cat_op_simps
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps 
            cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
        )
  qed (simp add: ntcf_Hom_NTMap_vsv)
qed


subsubsection\<open>
Composition of a \<open>Hom\<close>-natural transformation with 
two natural transformations is a natural transformation
\<close>

lemma (in category) cat_ntcf_Hom_is_ntcf: 
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<psi> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>-) :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,\<FF>'-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<GG>'-) :
    op_cat \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-

  interpret \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))
  interpret \<psi>: is_ntcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<psi> by (rule assms(2))

  show ?thesis
  proof(intro is_ntcfI')
    show "vfsequence (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>-))" unfolding ntcf_Hom_def by simp
    show "vcard (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>-)) = 5\<^sub>\<nat>"
      unfolding ntcf_Hom_def by (simp add: nat_omega_simps)
    from assms category_axioms show 
      "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,\<FF>'-) : op_cat \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      by (cs_concl cs_intro: cat_cs_intros)
    from assms category_axioms show 
      "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<GG>'-) : op_cat \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      by (cs_concl cs_intro: cat_cs_intros)
    from assms show "\<D>\<^sub>\<circ> (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>-)\<lparr>NTMap\<rparr>) = (op_cat \<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    show "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>-)\<lparr>NTMap\<rparr>\<lparr>ab\<rparr> :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,\<FF>'-)\<lparr>ObjMap\<rparr>\<lparr>ab\<rparr> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub>
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<GG>'-)\<lparr>ObjMap\<rparr>\<lparr>ab\<rparr>"
      if "ab \<in>\<^sub>\<circ> (op_cat \<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>" for ab 
    proof-
      from that obtain a b
        where ab_def: "ab = [a, b]\<^sub>\<circ>" 
          and a: "a \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr>" 
          and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
        by 
          (
            rule cat_prod_2_ObjE[
              OF \<phi>.NTDom.HomDom.category_op \<psi>.NTDom.HomDom.category_axioms
              ]
          )
      from category_axioms assms a b show 
        "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>-)\<lparr>NTMap\<rparr>\<lparr>ab\<rparr> :
          Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,\<FF>'-)\<lparr>ObjMap\<rparr>\<lparr>ab\<rparr> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub>
          Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<GG>'-)\<lparr>ObjMap\<rparr>\<lparr>ab\<rparr>"
        unfolding ab_def cat_op_simps
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps 
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
    qed
    show 
      "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>-)\<lparr>NTMap\<rparr>\<lparr>a'b'\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
       Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,\<FF>'-)\<lparr>ArrMap\<rparr>\<lparr>gf\<rparr> =
        Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<GG>'-)\<lparr>ArrMap\<rparr>\<lparr>gf\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
        Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>-)\<lparr>NTMap\<rparr>\<lparr>ab\<rparr>"
      if "gf : ab \<mapsto>\<^bsub>op_cat \<AA> \<times>\<^sub>C \<BB>\<^esub> a'b'" for ab a'b' gf
    proof-
      from that obtain g f a b a' b'
        where gf_def: "gf = [g, f]\<^sub>\<circ>" 
          and ab_def: "ab = [a, b]\<^sub>\<circ>" 
          and a'b'_def: "a'b' = [a', b']\<^sub>\<circ>"
          and g: "g : a \<mapsto>\<^bsub>op_cat \<AA>\<^esub> a'"
          and f: "f : b \<mapsto>\<^bsub>\<BB>\<^esub> b'" 
        by 
          (
            elim 
              cat_prod_2_is_arrE[
                OF \<phi>.NTDom.HomDom.category_op \<psi>.NTDom.HomDom.category_axioms
                ]
          )
      from assms category_axioms that g f show ?thesis
        unfolding gf_def ab_def a'b'_def cat_op_simps
        by (*slow*)
          (
            cs_concl
              cs_simp: cat_ntcf_Hom_component_nat cat_cs_simps cat_op_simps
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
    qed
  qed (auto simp: ntcf_Hom_components cat_cs_simps)

qed

lemma (in category) cat_ntcf_Hom_is_ntcf': 
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<psi> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<beta> = \<alpha>"
    and "\<AA>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,\<FF>'-)"
    and "\<BB>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<GG>'-)"
    and "\<CC>' = op_cat \<AA> \<times>\<^sub>C \<BB>"
    and "\<DD>' = cat_Set \<alpha>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>-) : \<AA>' \<mapsto>\<^sub>C\<^sub>F \<BB>' : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> \<DD>'"
  using assms(1-2) unfolding assms(3-7) by (rule cat_ntcf_Hom_is_ntcf)

lemmas [cat_cs_intros] = category.cat_ntcf_Hom_is_ntcf'


subsubsection\<open>
Composition of a \<open>Hom\<close>-natural transformation with 
two vertical compositions of natural transformations
\<close>

lemma (in category) cat_ntcf_Hom_vcomp:
  assumes "\<phi>' : \<GG> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<psi>' : \<GG>' \<mapsto>\<^sub>C\<^sub>F \<HH>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<psi> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows 
    "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<phi>-,\<psi>' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<psi>-) =
      Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>'-) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>'-,\<psi>-)"
proof(rule ntcf_eqI[of \<alpha>])

  interpret \<phi>': is_ntcf \<alpha> \<AA> \<CC> \<GG> \<HH> \<phi>' by (rule assms(1))
  interpret \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule assms(2))
  interpret \<psi>': is_ntcf \<alpha> \<BB> \<CC> \<GG>' \<HH>' \<psi>' by (rule assms(3))
  interpret \<psi>: is_ntcf \<alpha> \<BB> \<CC> \<FF>' \<GG>' \<psi> by (rule assms(4))

  from category_axioms assms show H_vcomp:
    "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<phi>-,\<psi>' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<psi>-) :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<HH>-,\<FF>'-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<HH>'-) :
      op_cat \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from category_axioms assms show vcomp_H:
    "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>'-) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>'-,\<psi>-) :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<HH>-,\<FF>'-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<HH>'-) :
      op_cat \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from category_axioms assms H_vcomp have dom_H_vcomp:
    "\<D>\<^sub>\<circ> (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<phi>-,\<psi>' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<psi>-)\<lparr>NTMap\<rparr>) = (op_cat \<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from category_axioms assms H_vcomp have dom_vcomp_H:
    "\<D>\<^sub>\<circ> ((Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>'-) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>'-,\<psi>-))\<lparr>NTMap\<rparr>) =
      (op_cat \<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

  show "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<phi>-,\<psi>' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<psi>-)\<lparr>NTMap\<rparr> =
    (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>'-) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>'-,\<psi>-))\<lparr>NTMap\<rparr>"
  proof(rule vsv_eqI, unfold dom_H_vcomp dom_vcomp_H)
    fix ab assume prems: "ab \<in>\<^sub>\<circ> (op_cat \<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
    then obtain a b
      where ab_def: "ab = [a, b]\<^sub>\<circ>" 
        and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
        and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
      by 
        ( 
          auto 
            elim: 
              cat_prod_2_ObjE[
                OF \<phi>'.NTDom.HomDom.category_op \<psi>'.NTDom.HomDom.category_axioms
                ]
            simp: cat_op_simps
        )
    from 
      assms a b
      category_axioms 
      \<phi>'.NTDom.HomDom.category_axioms
      \<psi>'.NTDom.HomDom.category_axioms 
    show
      "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<phi>-,\<psi>' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<psi>-)\<lparr>NTMap\<rparr>\<lparr>ab\<rparr> =
        (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,\<psi>'-) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>'-,\<psi>-))\<lparr>NTMap\<rparr>\<lparr>ab\<rparr>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps ab_def
            cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
        )
  qed (auto simp: ntcf_Hom_NTMap_vsv cat_cs_intros)

qed simp_all

lemmas [cat_cs_simps] = category.cat_ntcf_Hom_vcomp

lemma (in category) cat_ntcf_Hom_ntcf_id:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF>': \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(ntcf_id \<FF>-,ntcf_id \<FF>'-) = ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<FF>'-)"
proof(rule ntcf_eqI[of \<alpha>])

  interpret \<FF>: is_functor \<alpha> \<AA> \<CC> \<FF> by (rule assms(1))
  interpret \<FF>': is_functor \<alpha> \<BB> \<CC> \<FF>' by (rule assms(2))

  from category_axioms assms show H_id:
    "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(ntcf_id \<FF>-,ntcf_id \<FF>'-) :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<FF>'-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<FF>'-) :
      op_cat \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from category_axioms assms show id_H:
    "ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<FF>'-) :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<FF>'-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<FF>'-) :
      op_cat \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

  from category_axioms assms H_id have dom_H_id:
    "\<D>\<^sub>\<circ> (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(ntcf_id \<FF>-,ntcf_id \<FF>'-)\<lparr>NTMap\<rparr>) = (op_cat \<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from category_axioms assms H_id have dom_id_H:
    "\<D>\<^sub>\<circ> (ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<FF>'-)\<lparr>NTMap\<rparr>) = (op_cat \<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

  show 
    "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(ntcf_id \<FF>-,ntcf_id \<FF>'-)\<lparr>NTMap\<rparr> =
      ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<FF>'-)\<lparr>NTMap\<rparr>"
  proof(rule vsv_eqI, unfold dom_H_id dom_id_H)
    show "vsv (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(ntcf_id \<FF>-,ntcf_id \<FF>'-)\<lparr>NTMap\<rparr>)" 
      by (rule ntcf_Hom_NTMap_vsv)
    from id_H show "vsv (ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<FF>'-)\<lparr>NTMap\<rparr>)"
      by (intro is_functor.ntcf_id_NTMap_vsv) 
        (cs_concl cs_simp: cs_intro: cat_cs_intros)
    fix ab assume "ab \<in>\<^sub>\<circ> (op_cat \<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
    then obtain a b
      where ab_def: "ab = [a, b]\<^sub>\<circ>" 
        and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
        and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
      by 
        ( 
          auto 
            elim: 
              cat_prod_2_ObjE[OF \<FF>.HomDom.category_op \<FF>'.HomDom.category_axioms]
            simp: cat_op_simps
        )
    from category_axioms assms a b H_id id_H show
      "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(ntcf_id \<FF>-,ntcf_id \<FF>'-)\<lparr>NTMap\<rparr>\<lparr>ab\<rparr> = 
        ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,\<FF>'-)\<lparr>NTMap\<rparr>\<lparr>ab\<rparr>"
      unfolding ab_def
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_op_simps 
            cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
        )
  qed simp

qed simp_all

lemmas [cat_cs_simps] = category.cat_ntcf_Hom_ntcf_id



subsection\<open>
Composition of a \<open>Hom\<close>-natural transformation with a natural transformation
\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See subsection 1.15 in \cite{bodo_categories_1970}.\<close>

definition ntcf_lcomp_Hom :: "V \<Rightarrow> V \<Rightarrow> V" (\<open>Hom\<^sub>A\<^sub>.\<^sub>C\<index>'(/_-,-/')\<close>)
  where "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-) = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,ntcf_id (cf_id (\<phi>\<lparr>NTDGCod\<rparr>))-)"

definition ntcf_rcomp_Hom :: "V \<Rightarrow> V \<Rightarrow> V" (\<open>Hom\<^sub>A\<^sub>.\<^sub>C\<index>'(/-,_-/')\<close>)
  where "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(-,\<psi>-) = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(ntcf_id (cf_id (\<psi>\<lparr>NTDGCod\<rparr>))-,\<psi>-)"


subsubsection\<open>Natural transformation map\<close>

lemma ntcf_lcomp_Hom_NTMap_vsv: "vsv (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-)\<lparr>NTMap\<rparr>)"
  unfolding ntcf_lcomp_Hom_def by (rule ntcf_Hom_NTMap_vsv)

lemma ntcf_rcomp_Hom_NTMap_vsv: "vsv (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(-,\<psi>-)\<lparr>NTMap\<rparr>)"
  unfolding ntcf_rcomp_Hom_def by (rule ntcf_Hom_NTMap_vsv)

lemma ntcf_lcomp_Hom_NTMap_vdomain[cat_cs_simps]:
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
  shows "\<D>\<^sub>\<circ> (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-)\<lparr>NTMap\<rparr>) = (op_cat \<AA> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
proof-
  interpret \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))
  from assms show ?thesis
    unfolding ntcf_lcomp_Hom_def \<phi>.ntcf_NTDGCod
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed

lemma ntcf_rcomp_Hom_NTMap_vdomain[cat_cs_simps]:
  assumes "\<psi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
  shows "\<D>\<^sub>\<circ> (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(-,\<psi>-)\<lparr>NTMap\<rparr>) = (op_cat \<CC> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
proof-
  interpret \<psi>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<psi> by (rule assms(1))
  from assms show ?thesis
    unfolding ntcf_rcomp_Hom_def \<psi>.ntcf_NTDGCod
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed

lemma ntcf_lcomp_Hom_NTMap_app[cat_cs_simps]:
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "a \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-)\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> = ntcf_lcomp_Hom_component \<phi> a b"
proof-
  interpret \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))
  show ?thesis
    unfolding ntcf_lcomp_Hom_def ntcf_lcomp_Hom_component_def \<phi>.ntcf_NTDGCod
    using assms unfolding cat_op_simps
    by
      (
        cs_concl
          cs_simp: cat_cs_simps cat_op_simps
          cs_intro: cat_cs_intros cat_prod_cs_intros
      )
qed

lemma ntcf_rcomp_Hom_NTMap_app[cat_cs_simps]:
  assumes "\<psi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(-,\<psi>-)\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> = ntcf_rcomp_Hom_component \<psi> a b"
proof-
  interpret \<psi>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<psi> by (rule assms(1))
  show ?thesis
    unfolding ntcf_rcomp_Hom_def ntcf_rcomp_Hom_component_def \<psi>.ntcf_NTDGCod
    using assms unfolding cat_op_simps
    by
      (
        cs_concl
          cs_simp: cat_cs_simps cat_op_simps 
          cs_intro: cat_cs_intros cat_prod_cs_intros
      )
qed

lemma (in category) ntcf_lcomp_Hom_NTMap_vrange:
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<R>\<^sub>\<circ> (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-)\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Arr\<rparr>"
proof-
  interpret \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))
  from assms show ?thesis
    unfolding ntcf_lcomp_Hom_def ntcf_lcomp_Hom_component_def \<phi>.ntcf_NTDGCod
    by (intro ntcf_Hom_NTMap_vrange) (cs_concl cs_intro: cat_cs_intros)+
qed

lemma (in category) ntcf_rcomp_Hom_NTMap_vrange:
  assumes "\<psi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<R>\<^sub>\<circ> (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(-,\<psi>-)\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Arr\<rparr>"
proof-
  interpret \<psi>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<psi> by (rule assms(1))
  from assms show ?thesis
    unfolding ntcf_rcomp_Hom_def ntcf_rcomp_Hom_component_def \<psi>.ntcf_NTDGCod
    by (intro ntcf_Hom_NTMap_vrange) (cs_concl cs_intro: cat_cs_intros)+
qed


subsubsection\<open>
Composition of a \<open>Hom\<close>-natural transformation with 
a natural transformation is a natural transformation
\<close>

lemma (in category) cat_ntcf_lcomp_Hom_is_ntcf: 
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-) :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-) : op_cat \<AA> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-
  interpret \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))
  from assms category_axioms show ?thesis
    unfolding 
      ntcf_lcomp_Hom_def cf_bcomp_Hom_cf_lcomp_Hom[symmetric] \<phi>.ntcf_NTDGCod
    by (intro category.cat_ntcf_Hom_is_ntcf)
      (cs_concl cs_intro: cat_cs_intros)+
qed

lemma (in category) cat_ntcf_lcomp_Hom_is_ntcf': 
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<beta> = \<alpha>"
    and "\<AA>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-)"
    and "\<BB>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)"
    and "\<CC>' = op_cat \<AA> \<times>\<^sub>C \<CC>"
    and "\<DD>' = cat_Set \<alpha>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-) : \<AA>' \<mapsto>\<^sub>C\<^sub>F \<BB>' : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> \<DD>'"
  using assms(1) unfolding assms(2-6) by (rule cat_ntcf_lcomp_Hom_is_ntcf)

lemmas [cat_cs_intros] = category.cat_ntcf_lcomp_Hom_is_ntcf'

lemma (in category) cat_ntcf_rcomp_Hom_is_ntcf:
  assumes "\<psi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(-,\<psi>-) :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-) : op_cat \<CC> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-
  interpret \<psi>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<psi> by (rule assms(1))
  from assms category_axioms show ?thesis
    unfolding 
      ntcf_rcomp_Hom_def cf_bcomp_Hom_cf_rcomp_Hom[symmetric] \<psi>.ntcf_NTDGCod
    by (intro category.cat_ntcf_Hom_is_ntcf)
      (cs_concl cs_intro: cat_cs_intros)+
qed

lemma (in category) cat_ntcf_rcomp_Hom_is_ntcf':
  assumes "\<psi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<beta> = \<alpha>"
    and "\<AA>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>-)"
    and "\<BB>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<GG>-)"
    and "\<CC>' = op_cat \<CC> \<times>\<^sub>C \<BB>"  
    and "\<DD>' = cat_Set \<alpha>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(-,\<psi>-) : \<AA>' \<mapsto>\<^sub>C\<^sub>F \<BB>' : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>'"
  using assms(1) unfolding assms(2-6) by (rule cat_ntcf_rcomp_Hom_is_ntcf)

lemmas [cat_cs_intros] = category.cat_ntcf_rcomp_Hom_is_ntcf'


subsubsection\<open>
Component of a composition of a \<open>Hom\<close>-natural transformation 
with a natural transformation and the Yoneda component
\<close>

lemma (in category) cat_ntcf_lcomp_Hom_component_is_Yoneda_component:
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "b \<in>\<^sub>\<circ> op_cat \<BB>\<lparr>Obj\<rparr>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows 
    "ntcf_lcomp_Hom_component \<phi> b c =
      Yoneda_component Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) (\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) (\<phi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>) c"
  (is \<open>?lcomp = ?Yc\<close>)
proof-

  interpret \<phi>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))

  from assms(2) have b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" unfolding cat_op_simps by clarsimp
  from b have \<FF>b: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and \<GG>b: "\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    by (auto intro: cat_cs_intros)
  from assms(1,3) b category_axioms have \<phi>b:
    "\<phi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<in>\<^sub>\<circ> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-)\<lparr>ObjMap\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)

  have lcomp:
    "?lcomp : Hom \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) c \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) c"
    by (rule cat_ntcf_lcomp_Hom_component_is_arr[OF assms])
  then have dom_lhs: "\<D>\<^sub>\<circ> (?lcomp\<lparr>ArrVal\<rparr>) = Hom \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) c"
    by (cs_concl cs_simp: cat_cs_simps)  

  have Yc: "?Yc :
    Hom \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) c \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-)\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
    by 
      (
        rule cat_Yoneda_component_is_arr[
          OF cat_cf_Hom_snd_is_functor[OF \<FF>b] \<GG>b \<phi>b assms(3)
          ]
      )
  then have dom_rhs: "\<D>\<^sub>\<circ> (?Yc\<lparr>ArrVal\<rparr>) = Hom \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) c"
    by (cs_concl cs_simp: cat_cs_simps)

  show ?thesis
  proof(rule arr_Set_eqI[of \<alpha>])
  
    from lcomp show "arr_Set \<alpha> ?lcomp" by (auto dest: cat_Set_is_arrD(1))
    from Yc show "arr_Set \<alpha> ?Yc" by (auto dest: cat_Set_is_arrD(1))
  
    show "?lcomp\<lparr>ArrVal\<rparr> = ?Yc\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      from assms(1) b category_axioms show "vsv (?Yc\<lparr>ArrVal\<rparr>)"
        by (intro is_functor.Yoneda_component_ArrVal_vsv)
          (cs_concl cs_intro: cat_cs_intros)
      show "?lcomp\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> = ?Yc\<lparr>ArrVal\<rparr>\<lparr>f\<rparr>"
        if "f \<in>\<^sub>\<circ> Hom \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) c" for f
      proof-
        from that have "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> c" by simp
        with category_axioms assms(1,3) b show ?thesis
          by 
            (
              cs_concl 
                cs_simp: cat_cs_simps cat_op_simps 
                cs_intro: cat_cs_intros cat_op_intros
            )
      qed
    qed (simp_all add: ntcf_lcomp_Hom_component_ArrVal_vsv)
    
    from Yc category_axioms assms(1,3) b have
      "?Yc : Hom \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) c \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>) c"
      by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros) 
    with lcomp show "?lcomp\<lparr>ArrCod\<rparr> = ?Yc\<lparr>ArrCod\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps)
  
  qed (use lcomp Yc in \<open>cs_concl cs_simp: cat_cs_simps\<close>)

qed


subsubsection\<open>
Composition of a \<open>Hom\<close>-natural transformation with 
a vertical composition of natural transformations
\<close>

lemma (in category) cat_ntcf_lcomp_Hom_vcomp:
  assumes "\<phi>' : \<GG> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<phi>-,-) = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>'-,-)"
proof-
  interpret \<phi>': is_ntcf \<alpha> \<AA> \<CC> \<GG> \<HH> \<phi>' by (rule assms(1))
  interpret \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule assms(2))
  from category_axioms have ntcf_id_cf_id:
    "ntcf_id (cf_id \<CC>) = ntcf_id (cf_id \<CC>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id (cf_id \<CC>)"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from category_axioms assms show ?thesis
    unfolding 
      ntcf_lcomp_Hom_def
      ntsmcf_vcomp_components 
      dghm_id_components 
      \<phi>'.ntcf_NTDGCod
      \<phi>.ntcf_NTDGCod
    by (subst ntcf_id_cf_id) 
      (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed

lemmas [cat_cs_simps] = category.cat_ntcf_lcomp_Hom_vcomp

lemma (in category) cat_ntcf_rcomp_Hom_vcomp:
  assumes "\<phi>' : \<GG> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(-,\<phi>' \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<phi>-) = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(-,\<phi>'-) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(-,\<phi>-)"
proof-
  interpret \<phi>': is_ntcf \<alpha> \<AA> \<CC> \<GG> \<HH> \<phi>' by (rule assms(1))
  interpret \<phi>: is_ntcf \<alpha> \<AA> \<CC> \<FF> \<GG> \<phi> by (rule assms(2))
  from category_axioms have ntcf_id_cf_id:
    "ntcf_id (cf_id \<CC>) = ntcf_id (cf_id \<CC>) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id (cf_id \<CC>)"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from category_axioms assms show ?thesis
    unfolding 
      ntcf_rcomp_Hom_def
      ntsmcf_vcomp_components 
      dghm_id_components 
      \<phi>'.ntcf_NTDGCod
      \<phi>.ntcf_NTDGCod
    by (subst ntcf_id_cf_id) 
      (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed

lemmas [cat_cs_simps] = category.cat_ntcf_rcomp_Hom_vcomp


subsubsection\<open>
Composition of a \<open>Hom\<close>-natural transformation with an identity natural 
transformation
\<close>

lemma (in category) cat_ntcf_lcomp_Hom_ntcf_id:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(ntcf_id \<FF>-,-) = ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)"
proof-
  interpret \<FF>: is_functor \<alpha> \<AA> \<CC> \<FF> by (rule assms(1))
  from category_axioms assms show ?thesis
    unfolding ntcf_lcomp_Hom_def ntcf_id_components \<FF>.cf_HomCod
    by
      (
        cs_concl
          cs_simp: ntcf_lcomp_Hom_def cat_cs_simps 
          cs_intro: cat_cs_intros
      )
qed

lemmas [cat_cs_simps] = category.cat_ntcf_lcomp_Hom_ntcf_id

lemma (in category) cat_ntcf_rcomp_Hom_ntcf_id:
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(-,ntcf_id \<FF>-) = ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<FF>-)"
proof-
  interpret \<FF>: is_functor \<alpha> \<BB> \<CC> \<FF> by (rule assms(1))
  from category_axioms assms show ?thesis
    unfolding ntcf_rcomp_Hom_def ntcf_id_components \<FF>.cf_HomCod
    by (cs_concl cs_simp: ntcf_rcomp_Hom_def cat_cs_simps cs_intro: cat_cs_intros)
qed

lemmas [cat_cs_simps] = category.cat_ntcf_rcomp_Hom_ntcf_id



subsection\<open>Projections of a \<open>Hom\<close>-natural transformation\<close>


text\<open>
The concept of a projection of a \<open>Hom\<close>-natural transformation appears 
in the corollary to the Yoneda Lemma in Chapter III-2 in 
\cite{mac_lane_categories_2010} (although the concept has not been given
any specific name in the aforementioned reference).
\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition ntcf_Hom_snd :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (\<open>Hom\<^sub>A\<^sub>.\<^sub>C\<index>_'(/_,-/')\<close>)
  where "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-) =
    Yoneda_arrow \<alpha> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr>,-)) (\<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr>) f"

definition ntcf_Hom_fst :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (\<open>Hom\<^sub>A\<^sub>.\<^sub>C\<index>_'(/-,_/')\<close>)
  where "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,f) = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(f,-)"


text\<open>Components.\<close>

lemma (in category) cat_ntcf_Hom_snd_components:
  assumes "f : s \<mapsto>\<^bsub>\<CC>\<^esub> r"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)\<lparr>NTMap\<rparr> = 
    (\<lambda>d\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. Yoneda_component Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) r f d)"
    and "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)\<lparr>NTDom\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)"
    and "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)\<lparr>NTCod\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-)"
    and "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)\<lparr>NTDGDom\<rparr> = \<CC>"
    and "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)\<lparr>NTDGCod\<rparr> = cat_Set \<alpha>"
proof-
  interpret is_functor \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-)\<close>
    using assms category_axioms by (cs_concl cs_simp: cs_intro: cat_cs_intros)
  show "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)\<lparr>NTMap\<rparr> =
    (\<lambda>d\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. Yoneda_component Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) r f d)"
    and "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)\<lparr>NTDom\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)"
    and "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)\<lparr>NTCod\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-)"
    and "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)\<lparr>NTDGDom\<rparr> = \<CC>"
    and "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)\<lparr>NTDGCod\<rparr> = cat_Set \<alpha>"
    unfolding ntcf_Hom_snd_def cat_is_arrD[OF assms] Yoneda_arrow_components
    by simp_all
qed

lemma (in category) cat_ntcf_Hom_fst_components:
  assumes "f : r \<mapsto>\<^bsub>\<CC>\<^esub> s"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,f)\<lparr>NTMap\<rparr> =
    (\<lambda>d\<in>\<^sub>\<circ>op_cat \<CC>\<lparr>Obj\<rparr>. Yoneda_component Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,s) r f d)"
    and "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,f)\<lparr>NTDom\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,r)"
    and "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,f)\<lparr>NTCod\<rparr> = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,s)"
    and "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,f)\<lparr>NTDGDom\<rparr> = op_cat \<CC>"
    and "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,f)\<lparr>NTDGCod\<rparr> = cat_Set \<alpha>"
  using category_axioms assms
  unfolding 
    ntcf_Hom_fst_def
    category.cat_ntcf_Hom_snd_components[
      OF category_op, unfolded cat_op_simps, OF assms
      ]
    cat_op_simps
  by (cs_concl cs_simp: cat_op_simps cs_intro: cat_cs_intros)+


text\<open>Alternative definition.\<close>

lemma (in category) ntcf_Hom_snd_def':
  assumes "f : r \<mapsto>\<^bsub>\<CC>\<^esub> s"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-) = Yoneda_arrow \<alpha> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)) s f"
  using assms unfolding ntcf_Hom_snd_def by (simp add: cat_cs_simps) 

lemma (in category) ntcf_Hom_fst_def':
  assumes "f : r \<mapsto>\<^bsub>\<CC>\<^esub> s"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,f) = Yoneda_arrow \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,s) r f"
proof-
  from assms category_axioms show ?thesis
    unfolding ntcf_Hom_fst_def ntcf_Hom_snd_def cat_op_simps
    by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
qed


subsubsection\<open>Natural transformation map\<close>

context category
begin

context
  fixes s r f
  assumes f: "f : s \<mapsto>\<^bsub>\<CC>\<^esub> r"
begin

mk_VLambda cat_ntcf_Hom_snd_components(1)[OF f]
  |vsv ntcf_Hom_snd_NTMap_vsv[intro]|
  |vdomain ntcf_Hom_snd_NTMap_vdomain|
  |app ntcf_Hom_snd_NTMap_app|

end

context
  fixes s r f
  assumes f: "f : r \<mapsto>\<^bsub>\<CC>\<^esub> s"
begin

mk_VLambda cat_ntcf_Hom_fst_components(1)[OF f]
  |vsv ntcf_Hom_fst_NTMap_vsv[intro]|
  |vdomain ntcf_Hom_fst_NTMap_vdomain|
  |app ntcf_Hom_fst_NTMap_app|

end

end

lemmas [cat_cs_simps] = 
  category.ntcf_Hom_snd_NTMap_vdomain
  category.ntcf_Hom_fst_NTMap_vdomain

lemmas ntcf_Hom_snd_NTMap_app[cat_cs_simps] = 
  category.ntcf_Hom_snd_NTMap_app
  category.ntcf_Hom_fst_NTMap_app


subsubsection\<open>
\<open>Hom\<close>-natural transformation projections are natural transformations
\<close>

lemma (in category) cat_ntcf_Hom_snd_is_ntcf:
  assumes "f : s \<mapsto>\<^bsub>\<CC>\<^esub> r"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-) :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-
  note f = cat_is_arrD[OF assms]
  show ?thesis
    unfolding ntcf_Hom_snd_def f
  proof(rule category.cat_Yoneda_arrow_is_ntcf)
    from assms category_axioms show "f \<in>\<^sub>\<circ> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-)\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
  qed (intro category_axioms cat_cf_Hom_snd_is_functor f)+
qed

lemma (in category) cat_ntcf_Hom_snd_is_ntcf':
  assumes "f : s \<mapsto>\<^bsub>\<CC>\<^esub> r"
    and "\<beta> = \<alpha>"
    and "\<AA>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)"
    and "\<BB>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-)"
    and "\<CC>' = \<CC>"
    and "\<DD>' = cat_Set \<alpha>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-) : \<AA>' \<mapsto>\<^sub>C\<^sub>F \<BB>' : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> \<DD>'"
  using assms(1) unfolding assms(2-6) by (rule cat_ntcf_Hom_snd_is_ntcf)

lemmas [cat_cs_intros] = category.cat_ntcf_Hom_snd_is_ntcf'

lemma (in category) cat_ntcf_Hom_fst_is_ntcf:
  assumes "f : r \<mapsto>\<^bsub>\<CC>\<^esub> s"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,f) :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,r) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,s) : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-
  from assms have r: "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and s: "s \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
  from 
    category.cat_ntcf_Hom_snd_is_ntcf[
      OF category_op, 
      unfolded cat_op_simps, 
      OF assms, 
      unfolded cat_op_cat_cf_Hom_snd[OF r] cat_op_cat_cf_Hom_snd[OF s],
      folded ntcf_Hom_fst_def
      ]
  show ?thesis .
qed

lemma (in category) cat_ntcf_Hom_fst_is_ntcf':
  assumes "f : r \<mapsto>\<^bsub>\<CC>\<^esub> s"
    and "\<beta> = \<alpha>"
    and "\<AA>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,r)"
    and "\<BB>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,s)"
    and "\<CC>' = op_cat \<CC>"
    and "\<DD>' = cat_Set \<alpha>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,f) : \<AA>' \<mapsto>\<^sub>C\<^sub>F \<BB>' : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> \<DD>'"
  using assms(1) unfolding assms(2-6) by (rule cat_ntcf_Hom_fst_is_ntcf)

lemmas [cat_cs_intros] = category.cat_ntcf_Hom_fst_is_ntcf'


subsubsection\<open>Opposite \<open>Hom\<close>-natural transformation projections\<close>

lemma (in category) cat_op_cat_ntcf_Hom_snd: 
  "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(f,-) = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,f)"
  unfolding ntcf_Hom_fst_def by simp

lemmas [cat_op_simps] = category.cat_op_cat_ntcf_Hom_snd

lemma (in category) cat_op_cat_ntcf_Hom_fst:
  "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>op_cat \<CC>(-,f) = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)"
  unfolding ntcf_Hom_fst_def cat_op_simps by simp

lemmas [cat_op_simps] = category.cat_op_cat_ntcf_Hom_fst


subsubsection\<open>
\<open>Hom\<close>-natural transformation projections and the Yoneda component
\<close>

lemma (in category) cat_Yoneda_component_cf_Hom_snd_Comp:
  assumes "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" and "d \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows 
    "Yoneda_component Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) b f d \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
      Yoneda_component Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-) c g d =
      Yoneda_component Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) c (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) d"
    (is \<open>?Ya b f d \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?Yb c g d = ?Ya c (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) d\<close>)
proof-

  interpret Set: category \<alpha> \<open>cat_Set \<alpha>\<close> by (rule category_cat_Set)

  note gD = cat_is_arrD[OF assms(1)]
  note fD = cat_is_arrD[OF assms(2)]

  from assms category_axioms have Y_f:
    "?Ya b f d : Hom \<CC> b d \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> a d"
    by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
  moreover from assms category_axioms have Y_g: 
    "?Yb c g d : Hom \<CC> c d \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> b d"
    by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
  ultimately have Yf_Yg: 
    "?Ya b f d \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?Yb c g d : Hom \<CC> c d \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> a d"
    by (auto intro: cat_cs_intros)
  from assms category_axioms have Y_gf: 
    "?Ya c (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) d : Hom \<CC> c d \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> a d"
    by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
  from Yf_Yg have dom_rhs: 
    "\<D>\<^sub>\<circ> ((?Ya b f d \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?Yb c g d)\<lparr>ArrVal\<rparr>) = Hom \<CC> c d"
    by (cs_concl cs_simp: cat_cs_simps)
  from Y_gf have dom_lhs: "\<D>\<^sub>\<circ> (?Ya c (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) d\<lparr>ArrVal\<rparr>) = Hom \<CC> c d"  
    by (cs_concl cs_simp: cat_cs_simps)

  show ?thesis
  proof(rule arr_Set_eqI[of \<alpha>])
    from Yf_Yg show arr_Set_Yf_Yg: 
      "arr_Set \<alpha> (?Ya b f d \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?Yb c g d)"
      by (auto dest: cat_Set_is_arrD(1))
    interpret Yf_Yg: arr_Set \<alpha> \<open>?Ya b f d \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?Yb c g d\<close>
      by (rule arr_Set_Yf_Yg)
    from Y_gf show arr_Set_Y_gf: "arr_Set \<alpha> (?Ya c (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) d)"
      by (auto dest: cat_Set_is_arrD(1))
    interpret Yf_Yg: arr_Set \<alpha> \<open>?Ya c (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) d\<close> by (rule arr_Set_Y_gf)
    show
      "(?Ya b f d \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?Yb c g d)\<lparr>ArrVal\<rparr> =
        ?Ya c (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) d\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs in_Hom_iff)
      fix h assume "h : c \<mapsto>\<^bsub>\<CC>\<^esub> d"
      with Y_gf Y_g Y_f category_axioms assms show 
        "(?Ya b f d \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?Yb c g d)\<lparr>ArrVal\<rparr>\<lparr>h\<rparr> =
          ?Ya c (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) d\<lparr>ArrVal\<rparr>\<lparr>h\<rparr>"
        (*slow*)
        by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
    qed auto
  
  qed (use Y_gf Yf_Yg in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+

qed

lemmas [cat_cs_simps] = 
  category.cat_Yoneda_component_cf_Hom_snd_Comp[symmetric]

lemma (in category) cat_Yoneda_component_cf_Hom_snd_CId:
  assumes "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "d \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows 
    "Yoneda_component Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) c (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>) d = 
      cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>Hom \<CC> c d\<rparr>"
  (is \<open>?Ycd = cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>Hom \<CC> c d\<rparr>\<close>)
proof-

  interpret Set: category \<alpha> \<open>cat_Set \<alpha>\<close> by (rule category_cat_Set)

  from assms category_axioms have Y_CId_c: 
    "?Ycd : Hom \<CC> c d \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> c d"
    by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
  from Y_CId_c Set.category_axioms assms category_axioms have CId_cd:
    "cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>Hom \<CC> c d\<rparr> : Hom \<CC> c d \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> c d"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from Y_CId_c have dom_lhs: "\<D>\<^sub>\<circ> (?Ycd\<lparr>ArrVal\<rparr>) = Hom \<CC> c d"  
    by (cs_concl cs_simp: cat_cs_simps)
  from CId_cd have dom_rhs: "\<D>\<^sub>\<circ> (cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>Hom \<CC> c d\<rparr>\<lparr>ArrVal\<rparr>) = Hom \<CC> c d"
    by (cs_concl cs_simp: cat_cs_simps)

  show ?thesis
  proof(rule arr_Set_eqI[of \<alpha>])
    from Y_CId_c show arr_Set_Y_CId_c: "arr_Set \<alpha> ?Ycd"
      by (auto dest: cat_Set_is_arrD(1))
    interpret Yf_Yg: arr_Set \<alpha> ?Ycd by (rule arr_Set_Y_CId_c)
    from CId_cd show arr_Set_CId_cd: "arr_Set \<alpha> (cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>Hom \<CC> c d\<rparr>)"
      by (auto dest: cat_Set_is_arrD(1))
    interpret CId_cd: arr_Set \<alpha> \<open>cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>Hom \<CC> c d\<rparr>\<close>
      by (rule arr_Set_CId_cd)
    show "?Ycd\<lparr>ArrVal\<rparr> = cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>Hom \<CC> c d\<rparr>\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs in_Hom_iff)
      fix h assume "h : c \<mapsto>\<^bsub>\<CC>\<^esub> d"
      with CId_cd Y_CId_c category_axioms assms show 
        "?Ycd\<lparr>ArrVal\<rparr>\<lparr>h\<rparr> = cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>Hom \<CC> c d\<rparr>\<lparr>ArrVal\<rparr>\<lparr>h\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
    qed auto
  qed (use Y_CId_c CId_cd in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+

qed

lemmas [cat_cs_simps] = category.cat_Yoneda_component_cf_Hom_snd_CId


subsubsection\<open>\<open>Hom\<close>-natural transformation projection of a composition\<close>

lemma (in category) cat_ntcf_Hom_snd_Comp:
  assumes "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f,-) = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(g,-)"
  (is \<open>?H_gf = ?H_f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?H_g\<close>)
proof(rule ntcf_eqI[of \<alpha>])
  from assms category_axioms show 
    "?H_gf : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms category_axioms show "?H_f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?H_g :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms category_axioms have lhs_dom: "\<D>\<^sub>\<circ> (?H_gf\<lparr>NTMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms category_axioms have rhs_dom:
    "\<D>\<^sub>\<circ> ((?H_f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?H_g)\<lparr>NTMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  show "?H_gf\<lparr>NTMap\<rparr> = (?H_f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?H_g)\<lparr>NTMap\<rparr>"
  proof(rule vsv_eqI, unfold lhs_dom rhs_dom)
    fix d assume "d \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    with assms category_axioms show 
      "?H_gf\<lparr>NTMap\<rparr>\<lparr>d\<rparr> = (?H_f \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ?H_g)\<lparr>NTMap\<rparr>\<lparr>d\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed (use assms in \<open>auto intro: cat_cs_intros\<close>)
qed auto

lemmas [cat_cs_simps] = category.cat_ntcf_Hom_snd_Comp

lemma (in category) cat_ntcf_Hom_fst_Comp:
  assumes "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,g) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,f)"
proof-
  note category.cat_ntcf_Hom_snd_Comp[
      OF category_op, unfolded cat_op_simps, OF assms(2,1)
      ]
  from this category_axioms assms show ?thesis
    by (cs_prems cs_simp: cat_op_simps cs_intro: cat_cs_intros) simp
qed

lemmas [cat_cs_simps] = category.cat_ntcf_Hom_fst_Comp


subsubsection\<open>\<open>Hom\<close>-natural transformation projection of an identity\<close>

lemma (in category) cat_ntcf_Hom_snd_CId:
  assumes "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>,-) = ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-)"
  (is \<open>?H_c = ?id_H_c\<close>)
proof(rule ntcf_eqI[of \<alpha>])
  from assms have "\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr> : c \<mapsto>\<^bsub>\<CC>\<^esub> c" by (auto simp: cat_cs_intros)
  from assms category_axioms show 
    "?H_c : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms category_axioms show 
    "?id_H_c : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms category_axioms have lhs_dom: "\<D>\<^sub>\<circ> (?H_c\<lparr>NTMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms category_axioms have rhs_dom: "\<D>\<^sub>\<circ> (?id_H_c\<lparr>NTMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  show "?H_c\<lparr>NTMap\<rparr> = ?id_H_c\<lparr>NTMap\<rparr>"
  proof(rule vsv_eqI, unfold lhs_dom rhs_dom)
    from assms category_axioms show "vsv (?id_H_c\<lparr>NTMap\<rparr>)"
      by (intro is_functor.ntcf_id_NTMap_vsv) 
        (cs_concl cs_simp: cs_intro: cat_cs_intros)
    fix d assume "d \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    with assms category_axioms show "?H_c\<lparr>NTMap\<rparr>\<lparr>d\<rparr> = ?id_H_c\<lparr>NTMap\<rparr>\<lparr>d\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)
  qed (use assms in \<open>auto intro: cat_cs_intros\<close>)
qed auto

lemmas [cat_cs_simps] = category.cat_ntcf_Hom_snd_CId

lemma (in category) cat_ntcf_Hom_fst_CId:
  assumes "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>) = ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,c)"
proof-
  note category.cat_ntcf_Hom_snd_CId[
      OF category_op, unfolded cat_op_simps, OF assms
      ]
  from this category_axioms assms show ?thesis
    by (cs_prems cs_simp: cat_op_simps cs_intro: cat_cs_intros) simp
qed

lemmas [cat_cs_simps] = category.cat_ntcf_Hom_fst_CId


subsubsection\<open>\<open>Hom\<close>-natural transformation and the Yoneda map\<close>

lemma (in category) cat_Yoneda_map_of_ntcf_Hom_snd:
  assumes "f : s \<mapsto>\<^bsub>\<CC>\<^esub> r"
  shows "Yoneda_map \<alpha> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-)) r\<lparr>Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)\<rparr> = f"
  using category_axioms assms (*slow*)
  by
    (
      cs_concl
        cs_simp: cat_cs_simps cat_op_simps 
        cs_intro: cat_cs_intros cat_prod_cs_intros
    ) 

lemmas [cat_cs_simps] = category.cat_Yoneda_map_of_ntcf_Hom_snd

lemma (in category) cat_Yoneda_map_of_ntcf_Hom_fst:
  assumes "f : r \<mapsto>\<^bsub>\<CC>\<^esub> s"
  shows "Yoneda_map \<alpha> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,s)) r\<lparr>Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,f)\<rparr> = f"
proof-
  note category.cat_Yoneda_map_of_ntcf_Hom_snd[
      OF category_op, unfolded cat_op_simps, OF assms
      ]
  from this category_axioms assms show ?thesis
    by (cs_prems cs_simp: cat_op_simps cs_intro: cat_cs_intros) simp
qed

lemmas [cat_cs_simps] = category.cat_Yoneda_map_of_ntcf_Hom_fst



subsection\<open>Evaluation arrow\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The evaluation arrow is a part of the definition of the evaluation functor.
The evaluation functor appears in Chapter III-2 in
\cite{mac_lane_categories_2010}.
\<close>

definition cf_eval_arrow :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_eval_arrow \<CC> \<NN> f =
    [
      (
        \<lambda>x\<in>\<^sub>\<circ>\<NN>\<lparr>NTDom\<rparr>\<lparr>ObjMap\<rparr>\<lparr>\<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr>\<rparr>.
          \<NN>\<lparr>NTCod\<rparr>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<NN>\<lparr>NTMap\<rparr>\<lparr>\<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr>\<rparr>\<lparr>ArrVal\<rparr>\<lparr>x\<rparr>\<rparr>
      ),
      \<NN>\<lparr>NTDom\<rparr>\<lparr>ObjMap\<rparr>\<lparr>\<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr>\<rparr>,
      \<NN>\<lparr>NTCod\<rparr>\<lparr>ObjMap\<rparr>\<lparr>\<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_eval_arrow_components:
  shows "cf_eval_arrow \<CC> \<NN> f\<lparr>ArrVal\<rparr> =
    (
      \<lambda>x\<in>\<^sub>\<circ>\<NN>\<lparr>NTDom\<rparr>\<lparr>ObjMap\<rparr>\<lparr>\<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr>\<rparr>.
        \<NN>\<lparr>NTCod\<rparr>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<NN>\<lparr>NTMap\<rparr>\<lparr>\<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr>\<rparr>\<lparr>ArrVal\<rparr>\<lparr>x\<rparr>\<rparr>
    )"
    and "cf_eval_arrow \<CC> \<NN> f\<lparr>ArrDom\<rparr> = \<NN>\<lparr>NTDom\<rparr>\<lparr>ObjMap\<rparr>\<lparr>\<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr>\<rparr>"
    and "cf_eval_arrow \<CC> \<NN> f\<lparr>ArrCod\<rparr> = \<NN>\<lparr>NTCod\<rparr>\<lparr>ObjMap\<rparr>\<lparr>\<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<rparr>"
  unfolding cf_eval_arrow_def arr_field_simps by (simp_all add: nat_omega_simps)

context
  fixes \<alpha> \<NN> \<CC> \<FF> \<GG> a b f  
  assumes \<NN>: "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and f: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
begin

interpretation \<NN>: is_ntcf \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<FF> \<GG> \<NN> by (rule \<NN>)

lemmas cf_eval_arrow_components' = cf_eval_arrow_components[
    where \<CC>=\<CC> and \<NN>=\<open>ntcf_arrow \<NN>\<close> and f=f, 
    unfolded 
      ntcf_arrow_components 
      cf_map_components 
      \<NN>.NTDom.HomDom.cat_is_arrD[OF f]
      cat_cs_simps
    ]

lemmas [cat_cs_simps] = cf_eval_arrow_components'(2,3)

end


subsubsection\<open>Arrow value\<close>

context
  fixes \<alpha> \<NN> \<CC> \<FF> \<GG> a b f  
  assumes \<NN>: "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and f: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
begin

mk_VLambda cf_eval_arrow_components'(1)[OF \<NN> f]
  |vsv cf_eval_arrow_ArrVal_vsv[cat_cs_intros]|
  |vdomain cf_eval_arrow_ArrVal_vdomain[cat_cs_simps]|
  |app cf_eval_arrow_ArrVal_app[cat_cs_simps]|

end


subsubsection\<open>Evaluation arrow is an arrow in the category \<open>Set\<close>\<close>

lemma cf_eval_arrow_is_arr:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "cf_eval_arrow \<CC> (ntcf_arrow \<NN>) f :
    \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
proof-
  interpret \<NN>: is_ntcf \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<FF> \<GG> \<NN> by (rule assms)
  show ?thesis
  proof
    (
      intro cat_Set_is_arrI arr_SetI, 
      unfold cf_eval_arrow_components'(2,3)[OF assms]
    )
    show "vfsequence (cf_eval_arrow \<CC> (ntcf_arrow \<NN>) f)"
      unfolding cf_eval_arrow_def by simp
    show "vcard (cf_eval_arrow \<CC> (ntcf_arrow \<NN>) f) = 3\<^sub>\<nat>"
      unfolding cf_eval_arrow_def by (simp add: nat_omega_simps)
    show "\<R>\<^sub>\<circ> (cf_eval_arrow \<CC> (ntcf_arrow \<NN>) f\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      by 
      (
        unfold cf_eval_arrow_components'[OF assms], 
        intro vrange_VLambda_vsubset
      ) 
      (
        use assms in 
          \<open>cs_concl cs_intro: cat_cs_intros cat_Set_cs_intros\<close>
      )+
  qed
    (
      use assms(2) in
        \<open>cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros\<close>
    )+
qed

lemma cf_eval_arrow_is_arr'[cat_cs_intros]:
  assumes "\<NN>' = ntcf_arrow \<NN>"
    and "\<FF>a = \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "\<GG>b = \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>" 
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "cf_eval_arrow \<CC> \<NN>' f : \<FF>a \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<GG>b"
  using assms(4,5) unfolding assms(1-3) by (rule cf_eval_arrow_is_arr)

lemma (in category) cat_cf_eval_arrow_ntcf_vcomp[cat_cs_simps]:
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c"
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows 
    "cf_eval_arrow \<CC> (ntcf_arrow (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)) (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) =
      cf_eval_arrow \<CC> (ntcf_arrow \<MM>) g \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
      cf_eval_arrow \<CC> (ntcf_arrow \<NN>) f"
proof-

  interpret \<MM>: is_ntcf \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<GG> \<HH> \<MM> by (rule assms(1))
  interpret \<NN>: is_ntcf \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<FF> \<GG> \<NN> by (rule assms(2))

  have \<MM>\<NN>: "\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms(3,4) have gf: "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from \<MM>\<NN> gf have cf_eval_gf:
    "cf_eval_arrow \<CC> (ntcf_arrow (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)) (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) :
      \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms(3,4) have cf_eval_g_cf_eval_f:
    "cf_eval_arrow \<CC> (ntcf_arrow \<MM>) g \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
      cf_eval_arrow \<CC> (ntcf_arrow \<NN>) f :
      \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  note cf_eval_gf = cf_eval_gf cat_Set_is_arrD[OF cf_eval_gf]
  note cf_eval_g_cf_eval_f = 
    cf_eval_g_cf_eval_f cat_Set_is_arrD[OF cf_eval_g_cf_eval_f]

  interpret arr_Set_cf_eval_gf:
    arr_Set \<alpha> \<open>cf_eval_arrow \<CC> (ntcf_arrow (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)) (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)\<close>
    by (rule cf_eval_gf(2))
  interpret arr_Set_cf_eval_g_cf_eval_f:
    arr_Set 
      \<alpha> 
      \<open>
        cf_eval_arrow \<CC> (ntcf_arrow \<MM>) g \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
        cf_eval_arrow \<CC> (ntcf_arrow \<NN>) f
      \<close>
    by (rule cf_eval_g_cf_eval_f(2))

  show ?thesis
  proof(rule arr_Set_eqI)
    from \<MM>\<NN> gf have dom_lhs:
      "\<D>\<^sub>\<circ> (cf_eval_arrow \<CC> (ntcf_arrow (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)) (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)\<lparr>ArrVal\<rparr>) = 
        \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps)
    from cf_eval_g_cf_eval_f(1) have dom_rhs: 
      "\<D>\<^sub>\<circ>
        (
          (
            cf_eval_arrow \<CC> (ntcf_arrow \<MM>) g \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
            cf_eval_arrow \<CC> (ntcf_arrow \<NN>) f
          )\<lparr>ArrVal\<rparr>
        ) = \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps)
    show
      "cf_eval_arrow \<CC> (ntcf_arrow (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)) (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)\<lparr>ArrVal\<rparr> =
        (
          cf_eval_arrow \<CC> (ntcf_arrow \<MM>) g \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
          cf_eval_arrow \<CC> (ntcf_arrow \<NN>) f
        )\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix \<FF>a assume prems: "\<FF>a \<in>\<^sub>\<circ> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      from 
        ArrVal_eq_helper
          [
            OF \<MM>.ntcf_Comp_commute[OF assms(4), symmetric], 
            where a=\<open>\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<FF>a\<rparr>\<close>
          ] 
        prems 
        assms(3,4) 
      have [cat_cs_simps]:
        "\<HH>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<MM>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<FF>a\<rparr>\<rparr>\<rparr> =
          \<MM>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<FF>a\<rparr>\<rparr>\<rparr>"
        by
          (
            cs_prems
              cs_simp: cat_cs_simps cs_intro: cat_Set_cs_intros cat_cs_intros
          )
      from prems assms(3,4) show 
        "cf_eval_arrow \<CC> (ntcf_arrow (\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>)) (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)\<lparr>ArrVal\<rparr>\<lparr>\<FF>a\<rparr> =
          (
            cf_eval_arrow \<CC> (ntcf_arrow \<MM>) g \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
            cf_eval_arrow \<CC> (ntcf_arrow \<NN>) f
          )\<lparr>ArrVal\<rparr>\<lparr>\<FF>a\<rparr>"
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cs_intro: cat_Set_cs_intros cat_cs_intros
          )
    qed (cs_concl cs_intro: V_cs_intros)
  qed
    (
      auto
        simp: cf_eval_gf cf_eval_g_cf_eval_f 
        intro: cf_eval_gf(2) cf_eval_g_cf_eval_f(2)
    )

qed

lemmas [cat_cs_simps] = category.cat_cf_eval_arrow_ntcf_vcomp

lemma (in category) cat_cf_eval_arrow_ntcf_id[cat_cs_simps]:
  assumes "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>" and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows 
    "cf_eval_arrow \<CC> (ntcf_arrow (ntcf_id \<FF>)) (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>) =
      cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
proof-

  interpret \<FF>: is_functor \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<FF> by (rule assms)

  from assms(2) have ntcf_id_CId_c: 
    "cf_eval_arrow \<CC> (ntcf_arrow (ntcf_id \<FF>)) (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>) :
      \<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
    by (cs_concl cs_intro: cat_cs_intros)
  from assms(2) have CId_\<FF>c:
    "cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
    by (cs_concl cs_intro: cat_cs_intros)

  show ?thesis
  proof(rule arr_Set_eqI[of \<alpha>])

    from ntcf_id_CId_c show arr_Set_ntcf_id_CId_c:
      "arr_Set \<alpha> (cf_eval_arrow \<CC> (ntcf_arrow (ntcf_id \<FF>)) (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>))"
      by (auto dest: cat_Set_is_arrD(1))
    from ntcf_id_CId_c have dom_lhs:
      "\<D>\<^sub>\<circ> (cf_eval_arrow \<CC> (ntcf_arrow (ntcf_id \<FF>)) (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>)\<lparr>ArrVal\<rparr>) =
        \<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps)+
    interpret ntcf_id_CId_c: 
      arr_Set \<alpha> \<open>cf_eval_arrow \<CC> (ntcf_arrow (ntcf_id \<FF>)) (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>)\<close>
      by (rule arr_Set_ntcf_id_CId_c)
  
    from CId_\<FF>c show arr_Set_CId_\<FF>c: "arr_Set \<alpha> (cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>)"
      by (auto dest: cat_Set_is_arrD(1))
    from CId_\<FF>c assms(2) have dom_rhs: 
      "\<D>\<^sub>\<circ> ((cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>)\<lparr>ArrVal\<rparr>) = \<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>" 
      by (cs_concl cs_simp: cat_cs_simps)

    show 
      "cf_eval_arrow \<CC> (ntcf_arrow (ntcf_id \<FF>)) (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>)\<lparr>ArrVal\<rparr> =
        cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix a assume "a \<in>\<^sub>\<circ> \<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
      with category_axioms assms(2) show 
        "cf_eval_arrow \<CC> (ntcf_arrow (ntcf_id \<FF>)) (\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>)\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> =
          cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    qed (use arr_Set_ntcf_id_CId_c arr_Set_CId_\<FF>c in auto)

  qed (use ntcf_id_CId_c CId_\<FF>c in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+

qed

lemmas [cat_cs_simps] = category.cat_cf_eval_arrow_ntcf_id



subsection\<open>\<open>HOM\<close>-functor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The following definition is a technical generalization that is used
later in this section.
\<close>

definition cf_HOM_snd :: "V \<Rightarrow> V \<Rightarrow> V" (\<open>HOM\<^sub>C\<index>'(/,_-/')\<close>)
  where "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-) =
    [
      (\<lambda>a\<in>\<^sub>\<circ>op_cat (\<FF>\<lparr>HomCod\<rparr>)\<lparr>Obj\<rparr>. cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>\<lparr>HomCod\<rparr>)(a,-) \<circ>\<^sub>C\<^sub>F \<FF>)),
      (
        \<lambda>f\<in>\<^sub>\<circ>op_cat (\<FF>\<lparr>HomCod\<rparr>)\<lparr>Arr\<rparr>.
          ntcf_arrow (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>\<lparr>HomCod\<rparr>)(f,-) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF>)
      ),
      op_cat (\<FF>\<lparr>HomCod\<rparr>),
      cat_FUNCT \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (cat_Set \<alpha>)
    ]\<^sub>\<circ>"

definition cf_HOM_fst :: "V \<Rightarrow> V \<Rightarrow> V" (\<open>HOM\<^sub>C\<index>'(/_-,/')\<close>)
  where "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>-,) =
    [
      (\<lambda>a\<in>\<^sub>\<circ>(\<FF>\<lparr>HomCod\<rparr>)\<lparr>Obj\<rparr>. cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>\<lparr>HomCod\<rparr>)(-,a) \<circ>\<^sub>C\<^sub>F op_cf \<FF>)),
      (
        \<lambda>f\<in>\<^sub>\<circ>(\<FF>\<lparr>HomCod\<rparr>)\<lparr>Arr\<rparr>.
          ntcf_arrow (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>\<lparr>HomCod\<rparr>)(-,f) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F op_cf \<FF>)
      ),
      \<FF>\<lparr>HomCod\<rparr>,
      cat_FUNCT \<alpha> (op_cat (\<FF>\<lparr>HomDom\<rparr>)) (cat_Set \<alpha>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_HOM_snd_components:
  shows "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)\<lparr>ObjMap\<rparr> =
      (\<lambda>a\<in>\<^sub>\<circ>op_cat (\<FF>\<lparr>HomCod\<rparr>)\<lparr>Obj\<rparr>. cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>\<lparr>HomCod\<rparr>)(a,-) \<circ>\<^sub>C\<^sub>F \<FF>))"
    and "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)\<lparr>ArrMap\<rparr> =
      (
        \<lambda>f\<in>\<^sub>\<circ>op_cat (\<FF>\<lparr>HomCod\<rparr>)\<lparr>Arr\<rparr>.
          ntcf_arrow (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>\<lparr>HomCod\<rparr>)(f,-) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF>)
      )"
    and [cat_cs_simps]: "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)\<lparr>HomDom\<rparr> = op_cat (\<FF>\<lparr>HomCod\<rparr>)"
    and [cat_cs_simps]: 
      "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)\<lparr>HomCod\<rparr> = cat_FUNCT \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (cat_Set \<alpha>)"
  unfolding cf_HOM_snd_def dghm_field_simps by (simp_all add: nat_omega_simps)

lemma cf_HOM_fst_components:
  shows "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>-,)\<lparr>ObjMap\<rparr> = 
      (\<lambda>a\<in>\<^sub>\<circ>(\<FF>\<lparr>HomCod\<rparr>)\<lparr>Obj\<rparr>. cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>\<lparr>HomCod\<rparr>)(-,a) \<circ>\<^sub>C\<^sub>F op_cf \<FF>))"
    and "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>-,)\<lparr>ArrMap\<rparr> = 
      (
        \<lambda>f\<in>\<^sub>\<circ>(\<FF>\<lparr>HomCod\<rparr>)\<lparr>Arr\<rparr>.
          ntcf_arrow (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>\<lparr>HomCod\<rparr>)(-,f) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F op_cf \<FF>)
      )"
    and "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>-,)\<lparr>HomDom\<rparr> = \<FF>\<lparr>HomCod\<rparr>"
    and "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>-,)\<lparr>HomCod\<rparr> = cat_FUNCT \<alpha> (op_cat (\<FF>\<lparr>HomDom\<rparr>)) (cat_Set \<alpha>)"
  unfolding cf_HOM_fst_def dghm_field_simps by (simp_all add: nat_omega_simps)

context is_functor
begin

lemmas cf_HOM_snd_components' = 
  cf_HOM_snd_components[where \<FF>=\<FF>, unfolded cf_HomDom cf_HomCod]

lemmas [cat_cs_simps] = cf_HOM_snd_components'(3,4)

lemmas cf_HOM_fst_components' = 
  cf_HOM_fst_components[where \<FF>=\<FF>, unfolded cf_HomDom cf_HomCod]

lemmas [cat_cs_simps] = cf_HOM_snd_components'(3,4)

end


subsubsection\<open>Object map\<close>

mk_VLambda cf_HOM_snd_components(1)
  |vsv cf_HOM_snd_ObjMap_vsv[cat_cs_intros]|

mk_VLambda (in is_functor) cf_HOM_snd_components'(1)[unfolded cat_op_simps]
  |vdomain cf_HOM_snd_ObjMap_vdomain[cat_cs_simps]|
  |app cf_HOM_snd_ObjMap_app[cat_cs_simps]|

mk_VLambda cf_HOM_snd_components(1)
  |vsv cf_HOM_fst_ObjMap_vsv[cat_cs_intros]|

mk_VLambda (in is_functor) cf_HOM_fst_components'(1)[unfolded cat_op_simps]
  |vdomain cf_HOM_fst_ObjMap_vdomain[cat_cs_simps]|
  |app cf_HOM_fst_ObjMap_app[cat_cs_simps]|


subsubsection\<open>Arrow map\<close>

mk_VLambda cf_HOM_snd_components(2)
  |vsv cf_HOM_snd_ArrMap_vsv[cat_cs_intros]|

mk_VLambda (in is_functor) cf_HOM_snd_components'(2)[unfolded cat_op_simps]
  |vdomain cf_HOM_snd_ArrMap_vdomain[cat_cs_simps]|
  |app cf_HOM_snd_ArrMap_app[cat_cs_simps]|

mk_VLambda cf_HOM_fst_components(2)
  |vsv cf_HOM_fst_ArrMap_vsv[cat_cs_intros]|

mk_VLambda (in is_functor) cf_HOM_fst_components'(2)[unfolded cat_op_simps]
  |vdomain cf_HOM_fst_ArrMap_vdomain[cat_cs_simps]|
  |app cf_HOM_fst_ArrMap_app[cat_cs_simps]|


subsubsection\<open>Opposite \<open>HOM\<close>-functor\<close>

lemma (in is_functor) cf_HOM_snd_op[cat_op_simps]: 
  "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,op_cf \<FF>-) = HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>-,)"
proof-
  have dom_lhs: "\<D>\<^sub>\<circ> HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,op_cf \<FF>-) = 4\<^sub>\<nat>"
    unfolding cf_HOM_snd_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>-,) = 4\<^sub>\<nat>"
    unfolding cf_HOM_fst_def by (simp add: nat_omega_simps)
  show ?thesis
  proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
    fix a assume "a \<in>\<^sub>\<circ> 4\<^sub>\<nat>"
    then show "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,op_cf \<FF>-)\<lparr>a\<rparr> = HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>-,)\<lparr>a\<rparr>"
    proof
      (
        elim_in_numeral, 
        use nothing in \<open>fold dghm_field_simps, unfold cat_cs_simps\<close>
      )
      show "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,op_cf \<FF>-)\<lparr>ObjMap\<rparr> = HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>-,)\<lparr>ObjMap\<rparr>"
        unfolding 
          cf_HOM_fst_components' 
          is_functor.cf_HOM_snd_components'[OF is_functor_op]
        by (rule VLambda_eqI, unfold cat_op_simps)
         (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)+
      show "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,op_cf \<FF>-)\<lparr>ArrMap\<rparr> = HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>-,)\<lparr>ArrMap\<rparr>"
        unfolding 
          cf_HOM_fst_components' 
          is_functor.cf_HOM_snd_components'[OF is_functor_op]
        by (rule VLambda_eqI, unfold cat_op_simps)
          (cs_concl cs_simp: cat_op_simps cs_intro: cat_cs_intros)+ 
    qed 
      (
        auto simp:
          cf_HOM_fst_components' cat_cs_simps cat_op_simps cat_op_intros
      )
  qed (auto simp: cf_HOM_snd_def cf_HOM_fst_def)
qed

lemmas [cat_op_simps] = is_functor.cf_HOM_snd_op

context is_functor
begin

lemmas cf_HOM_fst_op[cat_op_simps] = 
  is_functor.cf_HOM_snd_op[OF is_functor_op, unfolded cat_op_simps, symmetric]

end

lemmas [cat_op_simps] = is_functor.cf_HOM_fst_op


subsubsection\<open>\<open>HOM\<close>-functor is a functor\<close>

lemma (in is_functor) cf_HOM_snd_is_functor: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-) : op_cat \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>)"
proof-

  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<beta>\<CC>: category \<beta> \<BB>
    by (rule category.cat_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+

  show ?thesis
  proof(intro is_functorI', unfold cat_op_simps)
    show "vfsequence HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)" unfolding cf_HOM_snd_def by auto
    show "vcard HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-) = 4\<^sub>\<nat>"
      unfolding cf_HOM_snd_def by (simp add: nat_omega_simps)
    show "\<R>\<^sub>\<circ> (HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>)\<lparr>Obj\<rparr>"
      unfolding cf_HOM_snd_components'
    proof(rule vrange_VLambda_vsubset, unfold cat_op_simps)
      fix b assume prems: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
      with assms(2) show 
        "cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(b,-) \<circ>\<^sub>C\<^sub>F \<FF>) \<in>\<^sub>\<circ> cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>)\<lparr>Obj\<rparr>"
        by
          (
            cs_concl
              cs_simp: cat_FUNCT_cs_simps 
              cs_intro: cat_cs_intros cat_FUNCT_cs_intros
          )
    qed
    show 
      "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)\<lparr>ArrMap\<rparr>\<lparr>f \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> g\<rparr> = 
        HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>)\<^esub>
        HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      if "g : c \<mapsto>\<^bsub>\<BB>\<^esub> b" and "f : b \<mapsto>\<^bsub>\<BB>\<^esub> a" for b c g a f
      using that 
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_op_simps cat_FUNCT_cs_simps 
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
    show 
      "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)\<lparr>ArrMap\<rparr>\<lparr>\<BB>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> =
        cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>)\<lparr>CId\<rparr>\<lparr>HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
      if "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" for c 
      using that
      by
        (
          cs_concl
            cs_simp: cat_cs_simps cat_op_simps cat_FUNCT_cs_simps
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
  qed 
    (
      use assms(2) in
        \<open>
          cs_concl
            cs_simp: cat_cs_simps cat_op_simps cat_FUNCT_cs_simps
            cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
        \<close>
    )+

qed

lemma (in is_functor) cf_HOM_snd_is_functor'[cat_cs_intros]: 
  assumes "\<Z> \<beta>" 
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<CC>' = op_cat \<BB>"
    and "\<DD> = cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>)"
  shows "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-) : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> \<DD>"
  using assms(1,2) unfolding assms(3,4) by (rule cf_HOM_snd_is_functor)

lemmas [cat_cs_intros] = is_functor.cf_HOM_snd_is_functor'

lemma (in is_functor) cf_HOM_fst_is_functor: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>-,) : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> (op_cat \<AA>) (cat_Set \<alpha>)"
  by 
    (
      rule is_functor.cf_HOM_snd_is_functor[
        OF is_functor_op assms, unfolded cat_op_simps
        ]
   )

lemma (in is_functor) cf_HOM_fst_is_functor'[cat_cs_intros]: 
  assumes "\<Z> \<beta>" 
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<CC>' = \<BB>"
    and "\<DD> = cat_FUNCT \<alpha> (op_cat \<AA>) (cat_Set \<alpha>)"
  shows "HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(\<FF>-,) : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> \<DD>"
  using assms(1,2) unfolding assms(3,4) by (rule cf_HOM_fst_is_functor)

lemmas [cat_cs_intros] = is_functor.cf_HOM_fst_is_functor'



subsection\<open>Evaluation functor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter III-2 in \cite{mac_lane_categories_2010}.\<close>

definition cf_eval :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_eval \<alpha> \<beta> \<CC> =
    [
      (\<lambda>\<FF>d\<in>\<^sub>\<circ>(cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>. \<FF>d\<lparr>0\<rparr>\<lparr>ObjMap\<rparr>\<lparr>\<FF>d\<lparr>1\<^sub>\<nat>\<rparr>\<rparr>),
      (
        \<lambda>\<NN>f\<in>\<^sub>\<circ>(cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>)\<lparr>Arr\<rparr>.
          cf_eval_arrow \<CC> (\<NN>f\<lparr>0\<rparr>) (\<NN>f\<lparr>1\<^sub>\<nat>\<rparr>)
      ),
      cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>,
      cat_Set \<beta>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_eval_components:
  shows "cf_eval \<alpha> \<beta> \<CC>\<lparr>ObjMap\<rparr> =
    (\<lambda>\<FF>d\<in>\<^sub>\<circ>(cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>. \<FF>d\<lparr>0\<rparr>\<lparr>ObjMap\<rparr>\<lparr>\<FF>d\<lparr>1\<^sub>\<nat>\<rparr>\<rparr>)"
    and "cf_eval \<alpha> \<beta> \<CC>\<lparr>ArrMap\<rparr> =
      (
        \<lambda>\<NN>f\<in>\<^sub>\<circ>(cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>)\<lparr>Arr\<rparr>.
          cf_eval_arrow \<CC> (\<NN>f\<lparr>0\<rparr>) (\<NN>f\<lparr>1\<^sub>\<nat>\<rparr>)
      )"
    and [cat_cs_simps]: 
      "cf_eval \<alpha> \<beta> \<CC>\<lparr>HomDom\<rparr> = cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>"
    and [cat_cs_simps]: "cf_eval \<alpha> \<beta> \<CC>\<lparr>HomCod\<rparr> = cat_Set \<beta>"
  unfolding cf_eval_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

lemma cf_eval_ObjMap_vsv[cat_cs_intros]: "vsv (cf_eval \<alpha> \<beta> \<CC>\<lparr>ObjMap\<rparr>)"
  unfolding cf_eval_components by simp

lemma cf_eval_ObjMap_vdomain[cat_cs_simps]: 
  "\<D>\<^sub>\<circ> (cf_eval \<alpha> \<beta> \<CC>\<lparr>ObjMap\<rparr>) = (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
  unfolding cf_eval_components by simp

lemma (in category) cf_eval_ObjMap_app[cat_cs_simps]: 
  assumes "\<FF>c = [cf_map \<FF>, c]\<^sub>\<circ>"
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>" (*the order of premises is important*)
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "cf_eval \<alpha> \<beta> \<CC>\<lparr>ObjMap\<rparr>\<lparr>\<FF>c\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
proof-
  interpret \<FF>: is_functor \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<FF> by (rule assms(2))
  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    by (simp_all add: \<beta>_def \<Z>_Limit_\<alpha>\<omega> \<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 
  note [cat_small_cs_intros] = cat_category_if_ge_Limit
  from assms(2,3) \<alpha>\<beta> have "\<FF>c \<in>\<^sub>\<circ> (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
    by 
      (
        cs_concl 
          cs_simp: assms(1) cat_FUNCT_components(1)
          cs_intro: 
            cat_cs_intros 
            cat_small_cs_intros 
            cat_prod_cs_intros 
            cat_FUNCT_cs_intros
      )
  then show ?thesis
    by (simp add: assms(1) cf_map_components cf_eval_components nat_omega_simps)
qed

lemmas [cat_cs_simps] = category.cf_eval_ObjMap_app


subsubsection\<open>Arrow map\<close>

lemma cf_eval_ArrMap_vsv[cat_cs_intros]: "vsv (cf_eval \<alpha> \<beta> \<CC>\<lparr>ArrMap\<rparr>)"
  unfolding cf_eval_components by simp

lemma cf_eval_ArrMap_vdomain[cat_cs_simps]: 
  "\<D>\<^sub>\<circ> (cf_eval \<alpha> \<beta> \<CC>\<lparr>ArrMap\<rparr>) = (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>)\<lparr>Arr\<rparr>"
  unfolding cf_eval_components by simp

lemma (in category) cf_eval_ArrMap_app[cat_cs_simps]: 
  assumes "\<NN>f = [ntcf_arrow \<NN>, f]\<^sub>\<circ>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "cf_eval \<alpha> \<beta> \<CC>\<lparr>ArrMap\<rparr>\<lparr>\<NN>f\<rparr> = cf_eval_arrow \<CC> (ntcf_arrow \<NN>) f"
proof-
  interpret \<FF>: is_ntcf \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<FF> \<GG> \<NN> by (rule assms(2))
  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    by (simp_all add: \<beta>_def \<Z>_Limit_\<alpha>\<omega> \<Z>_\<omega>_\<alpha>\<omega> \<Z>_def \<Z>_\<alpha>_\<alpha>\<omega>)
  then interpret \<beta>: \<Z> \<beta> by simp 
  note [cat_small_cs_intros] = cat_category_if_ge_Limit
  from assms(1,3) \<alpha>\<beta> have "\<NN>f \<in>\<^sub>\<circ> (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>)\<lparr>Arr\<rparr>"
    by 
      (
        cs_concl
          cs_simp: assms(1) cat_FUNCT_components(1)
          cs_intro: 
            cat_cs_intros 
            cat_small_cs_intros 
            cat_prod_cs_intros 
            cat_FUNCT_cs_intros
      )
  then show ?thesis
    by (simp add: assms(1) cf_map_components cf_eval_components nat_omega_simps)
qed

lemmas [cat_cs_simps] = category.cf_eval_ArrMap_app


subsubsection\<open>Evaluation functor is a functor\<close>

lemma (in category) cat_cf_eval_is_functor:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "cf_eval \<alpha> \<beta> \<CC> : cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
proof-

  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  from assms(2) cat_category_if_ge_Limit[OF assms] interpret FUNCT: 
    category \<beta> \<open>(cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>))\<close>
    by 
      (
        cs_concl cs_intro:
          cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )
  interpret \<beta>\<CC>: category \<beta> \<CC>
    by (rule category.cat_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  interpret cat_Set_\<alpha>\<beta>: subcategory \<beta> \<open>cat_Set \<alpha>\<close> \<open>cat_Set \<beta>\<close>
    by (rule subcategory_cat_Set_cat_Set[OF assms])
  
  show ?thesis
  proof(intro is_functorI')
    show "vfsequence (cf_eval \<alpha> \<beta> \<CC>)" unfolding cf_eval_def by simp
    from cat_category_if_ge_Limit[OF assms] show 
      "category \<beta> ((cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)) \<times>\<^sub>C \<CC>)"
      by (cs_concl cs_simp: cs_intro: cat_small_cs_intros cat_cs_intros)
    show "vcard (cf_eval \<alpha> \<beta> \<CC>) = 4\<^sub>\<nat>" 
      unfolding cf_eval_def by (simp add: nat_omega_simps)
    show "\<R>\<^sub>\<circ> (cf_eval \<alpha> \<beta> \<CC>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Set \<beta>\<lparr>Obj\<rparr>"
    proof(intro vsv.vsv_vrange_vsubset, unfold cat_cs_simps)
      fix \<FF>c assume prems: "\<FF>c \<in>\<^sub>\<circ> (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
      then obtain \<FF> c 
        where \<FF>c_def: "\<FF>c = [\<FF>, c]\<^sub>\<circ>"
          and \<FF>: "\<FF> \<in>\<^sub>\<circ> cf_maps \<alpha> \<CC> (cat_Set \<alpha>)"
          and c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
        by 
          (
            auto 
              elim: cat_prod_2_ObjE[rotated 2] 
              intro: FUNCT.category_axioms \<beta>\<CC>.category_axioms
              simp: cat_FUNCT_components(1)
          )
      from \<FF> obtain \<GG> where \<FF>_def: "\<FF> = cf_map \<GG>"
        and \<GG>: "\<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
        by (elim cf_mapsE)        
      interpret \<GG>: is_functor \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<GG> by (rule \<GG>)
      from \<GG> c show "cf_eval \<alpha> \<beta> \<CC>\<lparr>ObjMap\<rparr>\<lparr>\<FF>c\<rparr> \<in>\<^sub>\<circ> cat_Set \<beta>\<lparr>Obj\<rparr>"
        unfolding \<FF>c_def \<FF>_def 
        by 
          (
            cs_concl
              cs_simp: cat_cs_simps 
              cs_intro: cat_cs_intros cat_Set_\<alpha>\<beta>.subcat_Obj_vsubset
          )
    qed (cs_concl cs_intro: cat_cs_intros)
    show "cf_eval \<alpha> \<beta> \<CC>\<lparr>ArrMap\<rparr>\<lparr>\<NN>f\<rparr> :
      cf_eval \<alpha> \<beta> \<CC>\<lparr>ObjMap\<rparr>\<lparr>\<FF>a\<rparr> \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> cf_eval \<alpha> \<beta> \<CC>\<lparr>ObjMap\<rparr>\<lparr>\<GG>b\<rparr>"
      if \<NN>f: "\<NN>f : \<FF>a \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>\<^esub> \<GG>b" for \<FF>a \<GG>b \<NN>f
    proof-
      obtain \<NN> f \<FF> a \<GG> b
        where \<NN>f_def: "\<NN>f = [\<NN>, f]\<^sub>\<circ>" 
          and \<FF>a_def: "\<FF>a = [\<FF>, a]\<^sub>\<circ>"
          and \<GG>b_def: "\<GG>b = [\<GG>, b]\<^sub>\<circ>" 
          and \<NN>: "\<NN> : \<FF> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)\<^esub> \<GG>" 
          and f: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
        by 
          (
            auto intro: 
              cat_prod_2_is_arrE[rotated 2, OF \<NN>f] 
              FUNCT.category_axioms 
              \<beta>\<CC>.category_axioms
          )
      note \<NN> = cat_FUNCT_is_arrD[OF \<NN>]
      from \<NN>(1) f assms(2) show "cf_eval \<alpha> \<beta> \<CC>\<lparr>ArrMap\<rparr>\<lparr>\<NN>f\<rparr> :
        cf_eval \<alpha> \<beta> \<CC>\<lparr>ObjMap\<rparr>\<lparr>\<FF>a\<rparr> \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> cf_eval \<alpha> \<beta> \<CC>\<lparr>ObjMap\<rparr>\<lparr>\<GG>b\<rparr>"
        unfolding \<NN>f_def \<FF>a_def \<GG>b_def
        by
          (
            intro cat_Set_\<alpha>\<beta>.subcat_is_arrD,
            use nothing in \<open>subst \<NN>(2), subst \<NN>(3), subst \<NN>(4)\<close>
          )
          (
            cs_concl
              cs_simp: cat_FUNCT_cs_simps cat_cs_simps cs_intro: cat_cs_intros 
          ) (*slow*)
    qed
    show 
      "cf_eval \<alpha> \<beta> \<CC>\<lparr>ArrMap\<rparr>\<lparr>\<MM>g \<circ>\<^sub>A\<^bsub>cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>\<^esub> \<NN>f\<rparr> =
        cf_eval \<alpha> \<beta> \<CC>\<lparr>ArrMap\<rparr>\<lparr>\<MM>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> cf_eval \<alpha> \<beta> \<CC>\<lparr>ArrMap\<rparr>\<lparr>\<NN>f\<rparr>"
      if \<MM>g: "\<MM>g : \<GG>b \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>\<^esub> \<HH>c"
        and \<NN>f: "\<NN>f : \<FF>a \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>\<^esub> \<GG>b"
      for \<NN>f \<MM>g \<FF>a \<GG>b \<HH>c
    proof-
      obtain \<NN> f \<FF> a \<GG> b
        where \<NN>f_def: "\<NN>f = [\<NN>, f]\<^sub>\<circ>" 
          and \<FF>a_def: "\<FF>a = [\<FF>, a]\<^sub>\<circ>"
          and \<GG>b_def: "\<GG>b = [\<GG>, b]\<^sub>\<circ>" 
          and \<NN>: "\<NN> : \<FF> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)\<^esub> \<GG>" 
          and f: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
        by 
          (
            auto intro: 
              cat_prod_2_is_arrE[rotated 2, OF \<NN>f] 
              FUNCT.category_axioms 
              \<beta>\<CC>.category_axioms
          )
      then obtain \<MM> g \<HH> c
        where \<MM>g_def: "\<MM>g = [\<MM>, g]\<^sub>\<circ>" 
          and \<HH>c_def: "\<HH>c = [\<HH>, c]\<^sub>\<circ>" 
          and \<MM>: "\<MM> : \<GG> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)\<^esub> \<HH>"
          and g: "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c"
        by 
          (
            auto intro: 
              cat_prod_2_is_arrE[rotated 2, OF \<MM>g] 
              FUNCT.category_axioms
              \<beta>\<CC>.category_axioms
          )
      note \<NN> = cat_FUNCT_is_arrD[OF \<NN>]
        and \<MM> = cat_FUNCT_is_arrD[OF \<MM>]
      from \<NN>(1) \<MM>(1) f g show
        "cf_eval \<alpha> \<beta> \<CC>\<lparr>ArrMap\<rparr>\<lparr>\<MM>g \<circ>\<^sub>A\<^bsub>cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>\<^esub> \<NN>f\<rparr> =
          cf_eval \<alpha> \<beta> \<CC>\<lparr>ArrMap\<rparr>\<lparr>\<MM>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> cf_eval \<alpha> \<beta> \<CC>\<lparr>ArrMap\<rparr>\<lparr>\<NN>f\<rparr>"
        unfolding \<MM>g_def \<NN>f_def \<FF>a_def \<GG>b_def \<HH>c_def
        by 
          (
            subst (1 2) \<MM>(2), use nothing in \<open>subst (1 2) \<NN>(2)\<close>, 
            cs_concl_step cat_Set_\<alpha>\<beta>.subcat_Comp_simp[symmetric]
          )
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_prod_cs_simps cat_FUNCT_cs_simps 
              cs_intro: cat_cs_intros cat_prod_cs_intros cat_FUNCT_cs_intros
          )
    qed
    show
      "cf_eval \<alpha> \<beta> \<CC>\<lparr>ArrMap\<rparr>\<lparr>(cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>)\<lparr>CId\<rparr>\<lparr>\<FF>c\<rparr>\<rparr> =
        cat_Set \<beta>\<lparr>CId\<rparr>\<lparr>cf_eval \<alpha> \<beta> \<CC>\<lparr>ObjMap\<rparr>\<lparr>\<FF>c\<rparr>\<rparr>"
      if "\<FF>c \<in>\<^sub>\<circ> (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>" for \<FF>c
    proof-
      from that obtain \<FF> c where \<FF>c_def: "\<FF>c = [\<FF>, c]\<^sub>\<circ>"
        and \<FF>: "\<FF> \<in>\<^sub>\<circ> cf_maps \<alpha> \<CC> (cat_Set \<alpha>)"
        and c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
        by 
          (
            auto 
              elim: cat_prod_2_ObjE[rotated 2] 
              intro: FUNCT.category_axioms \<beta>\<CC>.category_axioms
              simp: cat_FUNCT_components(1)
          )
      from \<FF> obtain \<GG> where \<FF>_def: "\<FF> = cf_map \<GG>"
        and \<GG>: "\<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
        by (elim cf_mapsE)
      interpret \<GG>: is_functor \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<GG> by (rule \<GG>)
      from \<GG> c show 
        "cf_eval \<alpha> \<beta> \<CC>\<lparr>ArrMap\<rparr>\<lparr>(cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>)\<lparr>CId\<rparr>\<lparr>\<FF>c\<rparr>\<rparr> =
          cat_Set \<beta>\<lparr>CId\<rparr>\<lparr>cf_eval \<alpha> \<beta> \<CC>\<lparr>ObjMap\<rparr>\<lparr>\<FF>c\<rparr>\<rparr>"
        unfolding \<FF>c_def \<FF>_def
        by (cs_concl_step cat_Set_\<alpha>\<beta>.subcat_CId[symmetric])
          (
            cs_concl
              cs_simp: cat_cs_simps cat_prod_cs_simps cat_FUNCT_cs_simps 
              cs_intro: cat_cs_intros cat_prod_cs_intros cat_FUNCT_cs_intros
          )
    qed

  qed (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)+

qed

lemma (in category) cat_cf_eval_is_functor':
  assumes "\<Z> \<beta>" 
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<AA>' = cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>"
    and "\<BB>' = cat_Set \<beta>"
    and "\<beta>' = \<beta>"
  shows "cf_eval \<alpha> \<beta> \<CC> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>'\<^esub> \<BB>'"
  using assms(1,2) unfolding assms(3-5) by (rule cat_cf_eval_is_functor) 

lemmas [cat_cs_intros] = category.cat_cf_eval_is_functor'



subsection\<open>\<open>N\<close>-functor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter III-2 in \cite{mac_lane_categories_2010}.\<close>

definition cf_nt :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_nt \<alpha> \<beta> \<FF> =
    bifunctor_flip (\<FF>\<lparr>HomCod\<rparr>) (cat_FUNCT \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (cat_Set \<alpha>))
      (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_FUNCT \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (cat_Set \<alpha>)(HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)-,-))"


text\<open>Alternative definition.\<close>

lemma (in is_functor) cf_nt_def':
  "cf_nt \<alpha> \<beta> \<FF> =
    bifunctor_flip \<BB> (cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>))
      (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>)(HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)-,-))"
  unfolding cf_nt_def cf_HomDom cf_HomCod by simp


text\<open>Components.\<close>

lemma cf_nt_components:
  shows "cf_nt \<alpha> \<beta> \<FF>\<lparr>ObjMap\<rparr> =
    (
      bifunctor_flip (\<FF>\<lparr>HomCod\<rparr>) (cat_FUNCT \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (cat_Set \<alpha>))
        (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_FUNCT \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (cat_Set \<alpha>)(HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)-,-))
    )\<lparr>ObjMap\<rparr>"
    and "cf_nt \<alpha> \<beta> \<FF>\<lparr>ArrMap\<rparr> =
      (
        bifunctor_flip (\<FF>\<lparr>HomCod\<rparr>) (cat_FUNCT \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (cat_Set \<alpha>))
          (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_FUNCT \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (cat_Set \<alpha>)(HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)-,-))
      )\<lparr>ArrMap\<rparr>"
    and "cf_nt \<alpha> \<beta> \<FF>\<lparr>HomDom\<rparr> =
      (
        bifunctor_flip (\<FF>\<lparr>HomCod\<rparr>) (cat_FUNCT \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (cat_Set \<alpha>))
          (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_FUNCT \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (cat_Set \<alpha>)(HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)-,-))
      )\<lparr>HomDom\<rparr>"
    and "cf_nt \<alpha> \<beta> \<FF>\<lparr>HomCod\<rparr> =
      (
        bifunctor_flip (\<FF>\<lparr>HomCod\<rparr>) (cat_FUNCT \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (cat_Set \<alpha>))
          (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_FUNCT \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (cat_Set \<alpha>)(HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)-,-))
      )\<lparr>HomCod\<rparr>"
  unfolding cf_nt_def by simp_all

lemma (in is_functor) cf_nt_components':
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "cf_nt \<alpha> \<beta> \<FF>\<lparr>ObjMap\<rparr> =
      (
        bifunctor_flip \<BB> (cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>))
          (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>)(HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)-,-))
      )\<lparr>ObjMap\<rparr>"
    and "cf_nt \<alpha> \<beta> \<FF>\<lparr>ArrMap\<rparr> =
      (
        bifunctor_flip \<BB> (cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>))
          (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>)(HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)-,-))
      )\<lparr>ArrMap\<rparr>"
    and [cat_cs_simps]: 
      "cf_nt \<alpha> \<beta> \<FF>\<lparr>HomDom\<rparr> = cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>) \<times>\<^sub>C \<BB>"
    and [cat_cs_simps]: 
      "cf_nt \<alpha> \<beta> \<FF>\<lparr>HomCod\<rparr> = cat_Set \<beta>"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<beta>\<AA>: category \<beta> \<AA>
    by (rule category.cat_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  interpret \<beta>\<BB>: category \<beta> \<BB>
    by (rule category.cat_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  show 
    "cf_nt \<alpha> \<beta> \<FF>\<lparr>ObjMap\<rparr> =
      (
        bifunctor_flip \<BB> (cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>))
          (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>)(HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)-,-))
      )\<lparr>ObjMap\<rparr>"
    "cf_nt \<alpha> \<beta> \<FF>\<lparr>ArrMap\<rparr> =
      (
        bifunctor_flip \<BB> (cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>))
          (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<beta>\<^esub>cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>)(HOM\<^sub>C\<^bsub>\<alpha>\<^esub>(,\<FF>-)-,-))
      )\<lparr>ArrMap\<rparr>"
    "cf_nt \<alpha> \<beta> \<FF>\<lparr>HomDom\<rparr> = cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>) \<times>\<^sub>C \<BB>"
    "cf_nt \<alpha> \<beta> \<FF>\<lparr>HomCod\<rparr> = cat_Set \<beta>"
    unfolding cf_nt_def 
    using assms(2)
    by
      (
        cs_concl
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps cat_op_simps
          cs_intro: cat_small_cs_intros cat_cs_intros cat_FUNCT_cs_intros
      )+
qed

lemmas [cat_cs_simps] = is_functor.cf_nt_components'(3,4)


subsubsection\<open>Object map\<close>

lemma cf_nt_ObjMap_vsv[cat_cs_intros]: "vsv (cf_nt \<alpha> \<beta> \<CC>\<lparr>ObjMap\<rparr>)"
  unfolding cf_nt_components by (cs_intro_step cat_cs_intros)

lemma (in is_functor) cf_nt_ObjMap_vdomain[cat_cs_simps]: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<D>\<^sub>\<circ> (cf_nt \<alpha> \<beta> \<FF>\<lparr>ObjMap\<rparr>) = (cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>) \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<beta>\<AA>: category \<beta> \<AA>
    by (rule category.cat_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  interpret \<beta>\<BB>: category \<beta> \<BB>
    by (rule category.cat_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  from assms(2) show ?thesis
    unfolding cf_nt_components
    by
      (
        cs_concl
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps cat_op_simps
          cs_intro: 
            cat_small_cs_intros
            cat_cs_intros
            cat_FUNCT_cs_intros
            cat_prod_cs_intros
      )
qed

lemmas [cat_cs_simps] = is_functor.cf_nt_ObjMap_vdomain

lemma (in is_functor) cf_nt_ObjMap_app[cat_cs_simps]: 
  assumes "\<Z> \<beta>" 
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<GG>b = [cf_map \<GG>, b]\<^sub>\<circ>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "cf_nt \<alpha> \<beta> \<FF>\<lparr>ObjMap\<rparr>\<lparr>\<GG>b\<rparr> = Hom
    (cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>))
    (cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(b,-) \<circ>\<^sub>C\<^sub>F \<FF>))
    (cf_map \<GG>)"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<beta>\<AA>: category \<beta> \<AA>
    by (rule category.cat_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  interpret \<beta>\<BB>: category \<beta> \<BB>
    by (rule category.cat_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  interpret \<GG>: is_functor \<alpha> \<AA> \<open>cat_Set \<alpha>\<close> \<GG> by (rule assms(4))
  from assms(2,5) show ?thesis
    unfolding assms(3) cf_nt_def
    by
      (
        cs_concl
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps cat_op_simps 
          cs_intro:
            cat_cs_intros
            cat_small_cs_intros
            cat_FUNCT_cs_intros
            cat_prod_cs_intros 
            cat_op_intros
      )
qed

lemmas [cat_cs_simps] = is_functor.cf_nt_ObjMap_app


subsubsection\<open>Arrow map\<close>

lemma cf_nt_ArrMap_vsv[cat_cs_intros]: "vsv (cf_nt \<alpha> \<beta> \<CC>\<lparr>ArrMap\<rparr>)"
  unfolding cf_nt_components by (cs_intro_step cat_cs_intros)

lemma (in is_functor) cf_nt_ArrMap_vdomain[cat_cs_simps]: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<D>\<^sub>\<circ> (cf_nt \<alpha> \<beta> \<FF>\<lparr>ArrMap\<rparr>) = (cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>) \<times>\<^sub>C \<BB>)\<lparr>Arr\<rparr>"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<beta>\<AA>: category \<beta> \<AA>
    by (rule category.cat_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  interpret \<beta>\<BB>: category \<beta> \<BB>
    by (rule category.cat_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  from assms(2) show ?thesis
    unfolding cf_nt_components
    by
      (
        cs_concl
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps cat_op_simps
          cs_intro: 
            cat_small_cs_intros
            cat_cs_intros
            cat_FUNCT_cs_intros
            cat_prod_cs_intros
      )
qed

lemmas [cat_cs_simps] = is_functor.cf_nt_ArrMap_vdomain

lemma (in is_functor) cf_nt_ArrMap_app[cat_cs_simps]: 
  assumes "\<Z> \<beta>" 
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<NN>f = [ntcf_arrow \<NN>, f]\<^sub>\<circ>"
    and "\<NN> : \<GG> \<mapsto>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
  shows "cf_nt \<alpha> \<beta> \<FF>\<lparr>ArrMap\<rparr>\<lparr>\<NN>f\<rparr> = cf_hom
    (cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>))
    [ntcf_arrow (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<BB>(f,-) \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<FF>), ntcf_arrow \<NN>]\<^sub>\<circ>"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<beta>\<AA>: category \<beta> \<AA>
    by (rule category.cat_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  interpret \<beta>\<BB>: category \<beta> \<BB>
    by (rule category.cat_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<open>cat_Set \<alpha>\<close> \<GG> \<HH> \<NN> by (rule assms(4))
  from assms(2,5) show ?thesis
    unfolding assms(3) cf_nt_def
    by
      (
        cs_concl
          cs_simp: cat_cs_simps cat_FUNCT_cs_simps cat_op_simps
          cs_intro:
            cat_cs_intros
            cat_small_cs_intros
            cat_FUNCT_cs_intros
            cat_prod_cs_intros
            cat_op_intros
      )
qed

lemmas [cat_cs_simps] = is_functor.cf_nt_ArrMap_app


subsubsection\<open>\<open>N\<close>-functor is a functor\<close>

lemma (in is_functor) cf_nt_is_functor:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "cf_nt \<alpha> \<beta> \<FF> : cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>) \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<beta>\<AA>: category \<beta> \<AA>
    by (rule category.cat_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  interpret \<beta>\<BB>: category \<beta> \<BB>
    by (rule category.cat_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  from assms(2) show ?thesis
    unfolding cf_nt_def'
    by 
      (
        cs_concl 
          cs_simp: cat_op_simps 
          cs_intro: cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
      )
qed

lemma (in is_functor) cf_nt_is_functor':
  assumes "\<Z> \<beta>" 
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<AA>' = cat_FUNCT \<alpha> \<AA> (cat_Set \<alpha>) \<times>\<^sub>C \<BB>"
    and "\<BB>' = cat_Set \<beta>"
    and "\<beta>' = \<beta>"
  shows "cf_nt \<alpha> \<beta> \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>'\<^esub> \<BB>'"
  using assms(1,2) unfolding assms(3-5) by (rule cf_nt_is_functor) 

lemmas [cat_cs_intros] = is_functor.cf_nt_is_functor'



subsection\<open>Yoneda natural transformation arrow\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The following subsection is based on the elements of the content
of Chapter III-2 in \cite{mac_lane_categories_2010}. 
\<close>

definition ntcf_Yoneda_arrow :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_Yoneda_arrow \<alpha> \<CC> \<FF> r =
    [
      (
        \<lambda>\<psi>\<in>\<^sub>\<circ>Hom (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)) (cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-))) \<FF>.
          Yoneda_map \<alpha> (cf_of_cf_map \<CC> (cat_Set \<alpha>) \<FF>) r\<lparr>
            ntcf_of_ntcf_arrow \<CC> (cat_Set \<alpha>) \<psi>
            \<rparr>
      ),
      Hom (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)) (cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-))) \<FF>,
      \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components\<close>

lemma ntcf_Yoneda_arrow_components:
  shows "ntcf_Yoneda_arrow \<alpha> \<CC> \<FF> r\<lparr>ArrVal\<rparr> = 
    (
      \<lambda>\<psi>\<in>\<^sub>\<circ>Hom (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)) (cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-))) \<FF>.
        Yoneda_map \<alpha> (cf_of_cf_map \<CC> (cat_Set \<alpha>) \<FF>) r\<lparr>
          ntcf_of_ntcf_arrow \<CC> (cat_Set \<alpha>) \<psi>
          \<rparr>
    )"
    and [cat_cs_simps]: "ntcf_Yoneda_arrow \<alpha> \<CC> \<FF> r\<lparr>ArrDom\<rparr> = 
      Hom (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)) (cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-))) \<FF>"
    and [cat_cs_simps]: "ntcf_Yoneda_arrow \<alpha> \<CC> \<FF> r\<lparr>ArrCod\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
  unfolding ntcf_Yoneda_arrow_def arr_field_simps
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Arrow map\<close>

mk_VLambda ntcf_Yoneda_arrow_components(1)
  |vsv ntcf_Yoneda_arrow_vsv[cat_cs_intros]|
  |vdomain ntcf_Yoneda_arrow_vdomain[cat_cs_simps]|

context category
begin

context
  fixes \<FF> :: V
begin

mk_VLambda ntcf_Yoneda_arrow_components(1)[where \<alpha>=\<alpha> and \<CC>=\<CC> and \<FF>=\<open>cf_map \<FF>\<close>]
  |app ntcf_Yoneda_arrow_app'|

lemmas ntcf_Yoneda_arrow_app =
  ntcf_Yoneda_arrow_app'[unfolded in_Hom_iff, cat_cs_simps]

end

end

lemmas [cat_cs_simps] = category.ntcf_Yoneda_arrow_app


subsubsection\<open>Several technical lemmas\<close>

lemma (in vsv) vsv_vrange_VLambda_app:
  assumes "g ` elts A = elts (\<D>\<^sub>\<circ> r)"
  shows "\<R>\<^sub>\<circ> (\<lambda>x\<in>\<^sub>\<circ>A. r\<lparr>g x\<rparr>) = \<R>\<^sub>\<circ> r"
proof(intro vsubset_antisym vsv.vsv_vrange_vsubset, unfold vdomain_VLambda)
  show "(\<lambda>x\<in>\<^sub>\<circ>A. r\<lparr>g x\<rparr>)\<lparr>x\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r" if "x \<in>\<^sub>\<circ> A" for x
  proof-
    from assms that have "g x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" by auto
    then have "r\<lparr>g x\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r" by force
    with that show ?thesis by simp
  qed
  show "r\<lparr>x\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<lambda>x\<in>\<^sub>\<circ>A. r\<lparr>g x\<rparr>)" if "x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" for x
  proof-
    from that assms have "x \<in> g ` elts A" by simp
    then obtain c where c: "c \<in>\<^sub>\<circ> A" and x_def: "x = g c" by clarsimp
    from c show ?thesis unfolding x_def by auto
  qed
qed auto

lemma (in vsv) vsv_vrange_VLambda_app':
  assumes "g ` elts A = elts (\<D>\<^sub>\<circ> r)"
    and "R = \<R>\<^sub>\<circ> r"
  shows "\<R>\<^sub>\<circ> (\<lambda>x\<in>\<^sub>\<circ>A. r\<lparr>g x\<rparr>) = R"
  using assms(1) unfolding assms(2) by (rule vsv_vrange_VLambda_app)

lemma (in v11) v11_VLambda_v11_bij_betw_comp:
  assumes "bij_betw g (elts A) (elts (\<D>\<^sub>\<circ> r))"
  shows "v11 (\<lambda>x\<in>\<^sub>\<circ>A. r\<lparr>g x\<rparr>)"
proof(rule vsv.vsv_valeq_v11I, unfold vdomain_VLambda beta)
  fix x y assume prems: "x \<in>\<^sub>\<circ> A" "y \<in>\<^sub>\<circ> A" "r\<lparr>g x\<rparr> = r\<lparr>g y\<rparr>"
  from assms prems(1,2) have "g x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" and "g y \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> r" by auto
  from v11_injective[OF this prems(3)] have "g x = g y".
  with assms prems(1,2) show "x = y" unfolding bij_betw_def inj_on_def by simp
qed simp


subsubsection\<open>
Yoneda natural transformation arrow is an arrow in the category \<open>Set\<close>
\<close>

lemma (in category) cat_ntcf_Yoneda_arrow_is_arr_isomoprhism:
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<FF>) r :
    Hom 
      (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>))
      (cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)))
      (cf_map \<FF>) \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<beta>\<^esub>
    \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
proof-

  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<FF>: is_functor \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<FF> by (rule assms)

  from assms(2) interpret FUNCT: tiny_category \<beta> \<open>cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)

  let ?Hom_r = \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)\<close>

  from assms have [cat_cs_simps]: "cf_of_cf_map \<CC> (cat_Set \<alpha>) (cf_map \<FF>) = \<FF>"
    by (cs_concl cs_simp: cat_FUNCT_cs_simps)

  note Yoneda = cat_Yoneda_Lemma[OF assms(3,4)]

  show ?thesis
  proof
    (
      intro cat_Set_is_arr_isomorphismI cat_Set_is_arrI arr_SetI,
      unfold cat_cs_simps cf_map_components
    )
    show "vfsequence (ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<FF>) r)"
      unfolding ntcf_Yoneda_arrow_def by simp
    show "vcard (ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<FF>) r) = 3\<^sub>\<nat>"
      unfolding ntcf_Yoneda_arrow_def by (simp add: nat_omega_simps)
    show "\<R>\<^sub>\<circ> (ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<FF>) r\<lparr>ArrVal\<rparr>) = \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
      unfolding cat_cs_simps cf_map_components ntcf_Yoneda_arrow_components 
      by (intro vsv.vsv_vrange_VLambda_app', unfold Yoneda(2))
        (
          use assms(4) in
            \<open>
              cs_concl
                cs_simp:
                  cat_cs_simps bij_betwD(2)[OF bij_betw_ntcf_of_ntcf_arrow_Hom]
                cs_intro: cat_cs_intros
            \<close>
        )+
    then show "\<R>\<^sub>\<circ> (ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<FF>) r\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
      by auto
    from assms(4) show "v11 (ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<FF>) r\<lparr>ArrVal\<rparr>)"
      unfolding ntcf_Yoneda_arrow_components
      by 
        (
          intro v11.v11_VLambda_v11_bij_betw_comp, 
          unfold cat_cs_simps \<FF>.Yoneda_map_vdomain; 
          intro Yoneda bij_betw_ntcf_of_ntcf_arrow_Hom
        )
        (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from assms(4) show 
      "Hom (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)) (cf_map ?Hom_r) (cf_map \<FF>) \<in>\<^sub>\<circ> Vset \<beta>"
      by (intro FUNCT.cat_Hom_in_Vset)
        (
          cs_concl 
            cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
    from assms(4) have "\<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" 
      by (cs_concl cs_intro: cat_cs_intros)
    then show "\<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
      by (auto simp: assms(2) Vset_trans Vset_in_mono)
  qed (auto intro: cat_cs_intros)

qed

lemma (in category) cat_ntcf_Yoneda_arrow_is_arr_isomoprhism':
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<FF>' = cf_map \<FF>"
    and "B = \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
    and "A = Hom 
      (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>))
      (cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)))
      (cf_map \<FF>)"
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "ntcf_Yoneda_arrow \<alpha> \<CC> \<FF>' r : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<beta>\<^esub> B"
  using assms(1,2,6,7) 
  unfolding assms(3-5)
  by (rule cat_ntcf_Yoneda_arrow_is_arr_isomoprhism)

lemmas [cat_arrow_cs_intros] = 
  category.cat_ntcf_Yoneda_arrow_is_arr_isomoprhism'

lemma (in category) cat_ntcf_Yoneda_arrow_is_arr:
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<FF>) r :
    Hom
      (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>))
      (cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)))
      (cf_map \<FF>) \<mapsto>\<^bsub>cat_Set \<beta>\<^esub>
    \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
  by 
    (
      rule cat_Set_is_arr_isomorphismD[
        OF cat_ntcf_Yoneda_arrow_is_arr_isomoprhism[OF assms]
        ]
    )

lemma (in category) cat_ntcf_Yoneda_arrow_is_arr'[cat_cs_intros]:
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<FF>' = cf_map \<FF>"
    and "B = \<FF>\<lparr>ObjMap\<rparr>\<lparr>r\<rparr>"
    and "A = Hom 
      (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>))
      (cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)))
      (cf_map \<FF>)"
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "ntcf_Yoneda_arrow \<alpha> \<CC> \<FF>' r : A \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> B"
  using assms(1,2,6,7) 
  unfolding assms(3-5)
  by (rule cat_ntcf_Yoneda_arrow_is_arr)

lemmas [cat_arrow_cs_intros] = category.cat_ntcf_Yoneda_arrow_is_arr'


subsection\<open>Commutativity law for the Yoneda natural transformation arrow\<close>

lemma (in category) cat_ntcf_Yoneda_arrow_commutativity:
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" 
  shows 
    "ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<GG>) b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub>
      cf_hom
        (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)) 
        [ntcf_arrow Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-), ntcf_arrow \<NN>]\<^sub>\<circ> =
          cf_eval_arrow \<CC> (ntcf_arrow \<NN>) f \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub>
            ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<FF>) a"
proof-

  let ?hom = 
    \<open>
      cf_hom
        (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)) 
        [ntcf_arrow Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-), ntcf_arrow \<NN>]\<^sub>\<circ>
    \<close>

  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<NN>: is_ntcf \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<FF> \<GG> \<NN> by (rule assms(3))
  interpret Set: category \<alpha> \<open>cat_Set \<alpha>\<close> by (rule category_cat_Set)
  interpret \<beta>\<CC>: category \<beta> \<CC>
    by (rule category.cat_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  interpret cat_Set_\<alpha>\<beta>: subcategory \<beta> \<open>cat_Set \<alpha>\<close> \<open>cat_Set \<beta>\<close>
    by (rule subcategory_cat_Set_cat_Set[OF assms(1,2)])

  from assms(2,4) have \<GG>b_\<NN>f:
    "ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<GG>) b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?hom :
      Hom
        (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>))
        (cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)))
        (cf_map \<FF>) \<mapsto>\<^bsub>cat_Set \<beta>\<^esub>
      \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    by
      (
        cs_concl
          cs_intro:
            cat_small_cs_intros
            cat_cs_intros
            cat_prod_cs_intros
            cat_op_intros
            cat_FUNCT_cs_intros
      )

  from assms(2,4) have \<NN>f_\<FF>a:
    "cf_eval_arrow \<CC> (ntcf_arrow \<NN>) f \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub>
      ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<FF>) a :
      Hom
        (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>))
        (cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)))
        (cf_map \<FF>) \<mapsto>\<^bsub>cat_Set \<beta>\<^esub>
      \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    by (cs_concl cs_intro: cat_cs_intros cat_Set_\<alpha>\<beta>.subcat_is_arrD)

  show ?thesis
  proof(rule arr_Set_eqI[of \<beta>])

    from \<GG>b_\<NN>f show arr_Set_\<GG>b_\<NN>f:
      "arr_Set \<beta> (ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<GG>) b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?hom)"
      by (auto dest: cat_Set_is_arrD(1))
    from \<GG>b_\<NN>f have dom_lhs: 
      "\<D>\<^sub>\<circ> ((ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<GG>) b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?hom)\<lparr>ArrVal\<rparr>) = 
        Hom
          (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>))
          (cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)))
          (cf_map \<FF>)"
      by (cs_concl cs_simp: cat_cs_simps)+
    interpret \<NN>f_\<FF>a: arr_Set 
      \<beta> \<open>ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<GG>) b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?hom\<close>
      by (rule arr_Set_\<GG>b_\<NN>f)
  
    from \<NN>f_\<FF>a show arr_Set_\<NN>f_\<FF>a:
      "arr_Set 
        \<beta> 
        (
          cf_eval_arrow \<CC> (ntcf_arrow \<NN>) f \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub>
          ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<FF>) a
        )"
      by (auto dest: cat_Set_is_arrD(1))
    from \<NN>f_\<FF>a have dom_rhs: 
      "\<D>\<^sub>\<circ> 
        (
          (
            cf_eval_arrow \<CC> (ntcf_arrow \<NN>) f \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub>
            ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<FF>) a
          )\<lparr>ArrVal\<rparr>
        ) = Hom
          (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>))
          (cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)))
          (cf_map \<FF>)" 
      by (cs_concl cs_simp: cat_cs_simps)

    show 
      "(ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<GG>) b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?hom)\<lparr>ArrVal\<rparr> =
        (
          cf_eval_arrow \<CC> (ntcf_arrow \<NN>) f \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub>
          ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<FF>) a
        )\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs in_Hom_iff)

      fix \<MM> assume prems: 
        "\<MM> : cf_map Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)\<^esub> cf_map \<FF>"

      from assms(4) have [cat_cs_simps]:
        "cf_of_cf_map \<CC> (cat_Set \<alpha>) (cf_map Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)) = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)"
        "cf_of_cf_map \<CC> (cat_Set \<alpha>) (cf_map \<FF>) = \<FF>"
        by (cs_concl cs_simp: cat_FUNCT_cs_simps cs_intro: cat_cs_intros)

      note \<MM> = cat_FUNCT_is_arrD[OF prems, unfolded cat_cs_simps]

      interpret \<MM>: is_ntcf 
        \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)\<close> \<FF> \<open>ntcf_of_ntcf_arrow \<CC> (cat_Set \<alpha>) \<MM>\<close>
        by (rule \<MM>(1))

      have \<GG>\<NN>_eq_\<NN>\<FF>:
        "\<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<lparr>ArrVal\<rparr>\<lparr>A\<rparr>\<rparr> =
          \<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<lparr>ArrVal\<rparr>\<lparr>A\<rparr>\<rparr>"
        if "A \<in>\<^sub>\<circ> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>" for A      
        using 
          ArrVal_eq_helper[
            OF \<NN>.ntcf_Comp_commute[OF assms(4), symmetric], where a=A
            ]
          assms(4)
          that
        by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

      from \<MM>(1) assms(2,3,4) have \<MM>a_CId_a: 
        "\<MM>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>\<rparr> \<in>\<^sub>\<circ> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        by (subst \<MM>)
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_op_simps cat_FUNCT_cs_simps 
              cs_intro: cat_Set_cs_intros cat_cs_intros
          )

      have \<FF>f_\<MM>a_eq_\<MM>b:
        "\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<lparr>ArrVal\<rparr>\<lparr>\<MM>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>\<lparr>ArrVal\<rparr>\<lparr>h\<rparr>\<rparr> =
          \<MM>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>\<lparr>ArrVal\<rparr>\<lparr>f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h\<rparr>"
        if "h : a \<mapsto>\<^bsub>\<CC>\<^esub> a" for h
        using 
          ArrVal_eq_helper[
            OF \<MM>.ntcf_Comp_commute[OF assms(4), symmetric], where a=h
            ]
          that
          assms(4)
          category_axioms
        by
          (
            cs_prems
              cs_simp: cat_FUNCT_cs_simps cat_cs_simps cat_op_simps
              cs_intro: cat_cs_intros cat_prod_cs_intros cat_op_intros
          )
    
      from \<MM>(1) assms(2,3,4) \<MM>a_CId_a category_axioms show 
        "(ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<GG>) b \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> ?hom)\<lparr>ArrVal\<rparr>\<lparr>\<MM>\<rparr> =
          (
            cf_eval_arrow \<CC> (ntcf_arrow \<NN>) f \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub>
            ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<FF>) a
          )\<lparr>ArrVal\<rparr>\<lparr>\<MM>\<rparr>" 
        by (subst (1 2) \<MM>(2)) (*very slow*)
          (
            cs_concl
              cs_simp:
                \<FF>f_\<MM>a_eq_\<MM>b \<GG>\<NN>_eq_\<NN>\<FF>
                cat_FUNCT_cs_simps 
                cat_cs_simps 
                cat_op_simps
              cs_intro: 
                cat_Set_\<alpha>\<beta>.subcat_is_arrD 
                cat_small_cs_intros
                cat_cs_intros 
                cat_FUNCT_cs_intros
                cat_prod_cs_intros
                cat_op_intros
          )+

    qed (use arr_Set_\<GG>b_\<NN>f arr_Set_\<NN>f_\<FF>a in auto)

  qed (use \<GG>b_\<NN>f \<NN>f_\<FF>a in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+

qed



subsection\<open>Yoneda Lemma: naturality\<close>


subsubsection\<open>
The Yoneda natural transformation: definition and elementary properties
\<close>


text\<open>
The main result of this subsection corresponds to the corollary to the 
Yoneda Lemma on page 61 in \cite{mac_lane_categories_2010}.
\<close>

definition ntcf_Yoneda :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_Yoneda \<alpha> \<beta> \<CC> =
    [
      (
        \<lambda>\<FF>r\<in>\<^sub>\<circ>(cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>. 
          ntcf_Yoneda_arrow \<alpha> \<CC> (\<FF>r\<lparr>0\<rparr>) (\<FF>r\<lparr>1\<^sub>\<nat>\<rparr>)
      ),
      cf_nt \<alpha> \<beta> (cf_id \<CC>),
      cf_eval \<alpha> \<beta> \<CC>,
      cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>,
      cat_Set \<beta>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma ntcf_Yoneda_components:
  shows "ntcf_Yoneda \<alpha> \<beta> \<CC>\<lparr>NTMap\<rparr> =
    (
      \<lambda>\<FF>r\<in>\<^sub>\<circ>(cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>.
        ntcf_Yoneda_arrow \<alpha> \<CC> (\<FF>r\<lparr>0\<rparr>) (\<FF>r\<lparr>1\<^sub>\<nat>\<rparr>)
    )"
    and [cat_cs_simps]: "ntcf_Yoneda \<alpha> \<beta> \<CC>\<lparr>NTDom\<rparr> = cf_nt \<alpha> \<beta> (cf_id \<CC>)"
    and [cat_cs_simps]: "ntcf_Yoneda \<alpha> \<beta> \<CC>\<lparr>NTCod\<rparr> = cf_eval \<alpha> \<beta> \<CC>"
    and [cat_cs_simps]: 
      "ntcf_Yoneda \<alpha> \<beta> \<CC>\<lparr>NTDGDom\<rparr> = cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>"
    and [cat_cs_simps]: "ntcf_Yoneda \<alpha> \<beta> \<CC>\<lparr>NTDGCod\<rparr> = cat_Set \<beta>"
  unfolding ntcf_Yoneda_def nt_field_simps by (simp_all add: nat_omega_simps)
    

subsubsection\<open>Natural transformation map\<close>

mk_VLambda ntcf_Yoneda_components(1)
  |vsv ntcf_Yoneda_NTMap_vsv[cat_cs_intros]|
  |vdomain ntcf_Yoneda_NTMap_vdomain[cat_cs_intros]|

lemma (in category) ntcf_Yoneda_NTMap_app[cat_cs_simps]:
  assumes "\<Z> \<beta>"
    and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
    and "\<FF>r = [cf_map \<FF>, r]\<^sub>\<circ>"
    and "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "ntcf_Yoneda \<alpha> \<beta> \<CC>\<lparr>NTMap\<rparr>\<lparr>\<FF>r\<rparr> = ntcf_Yoneda_arrow \<alpha> \<CC> (cf_map \<FF>) r"
proof-            
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<FF>: is_functor \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<FF> by (rule assms(4))
  interpret \<beta>\<CC>: category \<beta> \<CC>
    by (rule category.cat_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  from assms(2) interpret FUNCT: category \<beta> \<open>cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)\<close>
    by
      (
        cs_concl cs_intro: 
          cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
      )
  from assms(5) have "[cf_map \<FF>, r]\<^sub>\<circ> \<in>\<^sub>\<circ> (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
    by
      (
        cs_concl 
          cs_simp: cat_FUNCT_cs_simps
          cs_intro: cat_cs_intros cat_prod_cs_intros cat_FUNCT_cs_intros
      )
  then show ?thesis
    unfolding assms(3) ntcf_Yoneda_components by (simp add: nat_omega_simps)
qed

lemmas [cat_cs_simps] = category.ntcf_Yoneda_NTMap_app


subsubsection\<open>The Yoneda natural transformation is a natural transformation\<close>

lemma (in category) cat_ntcf_Yoneda_is_ntcf:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
  shows "ntcf_Yoneda \<alpha> \<beta> \<CC> :
    cf_nt \<alpha> \<beta> (cf_id \<CC>) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o cf_eval \<alpha> \<beta> \<CC> :
    cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
proof-

  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  interpret \<beta>\<CC>: category \<beta> \<CC>
    by (rule category.cat_category_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: cat_cs_intros\<close>)+
  from assms(2) interpret FUNCT: category \<beta> \<open>cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)\<close>
    by 
      (
        cs_concl cs_intro: 
          cat_cs_intros cat_small_cs_intros cat_FUNCT_cs_intros
      )

  show ?thesis
  proof(intro is_iso_ntcfI is_ntcfI')
    show "vfsequence (ntcf_Yoneda \<alpha> \<beta> \<CC>)" unfolding ntcf_Yoneda_def by simp
    show "vcard (ntcf_Yoneda \<alpha> \<beta> \<CC>) = 5\<^sub>\<nat>"
      unfolding ntcf_Yoneda_def by (simp add: nat_omega_simps)
    show ntcf_Yoneda_\<FF>r: "ntcf_Yoneda \<alpha> \<beta> \<CC>\<lparr>NTMap\<rparr>\<lparr>\<FF>r\<rparr> :
      cf_nt \<alpha> \<beta> (cf_id \<CC>)\<lparr>ObjMap\<rparr>\<lparr>\<FF>r\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<beta>\<^esub> cf_eval \<alpha> \<beta> \<CC>\<lparr>ObjMap\<rparr>\<lparr>\<FF>r\<rparr>"
      if "\<FF>r \<in>\<^sub>\<circ> (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>" for \<FF>r
    proof-
      from that obtain \<FF> r 
        where \<FF>r_def: "\<FF>r = [\<FF>, r]\<^sub>\<circ>" 
          and \<FF>: "\<FF> \<in>\<^sub>\<circ> cf_maps \<alpha> \<CC> (cat_Set \<alpha>)"
          and r: "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
        by
          (
            auto 
              elim: cat_prod_2_ObjE[rotated 2] 
              simp: cat_FUNCT_cs_simps
              intro: cat_cs_intros
           )
      from \<FF> obtain \<GG>
        where \<FF>_def: "\<FF> = cf_map \<GG>" and \<GG>: "\<GG> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
        by clarsimp
      from assms(2) \<GG> r show ?thesis
        unfolding \<FF>r_def \<FF>_def 
        by
          (
            cs_concl! 
              cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_arrow_cs_intros
           )      
    qed
    show "ntcf_Yoneda \<alpha> \<beta> \<CC>\<lparr>NTMap\<rparr>\<lparr>\<FF>r\<rparr> :
      cf_nt \<alpha> \<beta> (cf_id \<CC>)\<lparr>ObjMap\<rparr>\<lparr>\<FF>r\<rparr> \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> cf_eval \<alpha> \<beta> \<CC>\<lparr>ObjMap\<rparr>\<lparr>\<FF>r\<rparr>"
      if "\<FF>r \<in>\<^sub>\<circ> (cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>" for \<FF>r
      by (rule is_arr_isomorphismD[OF ntcf_Yoneda_\<FF>r[OF that]])
    show 
      "ntcf_Yoneda \<alpha> \<beta> \<CC>\<lparr>NTMap\<rparr>\<lparr>\<GG>b\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> 
        cf_nt \<alpha> \<beta> (cf_id \<CC>)\<lparr>ArrMap\<rparr>\<lparr>\<NN>f\<rparr> =
          cf_eval \<alpha> \<beta> \<CC>\<lparr>ArrMap\<rparr>\<lparr>\<NN>f\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> 
            ntcf_Yoneda \<alpha> \<beta> \<CC>\<lparr>NTMap\<rparr>\<lparr>\<FF>a\<rparr>"
      if \<NN>f: "\<NN>f : \<FF>a \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>) \<times>\<^sub>C \<CC>\<^esub> \<GG>b" for \<FF>a \<GG>b \<NN>f
    proof-
      obtain \<NN> f \<FF> a \<GG> b
        where \<NN>f_def: "\<NN>f = [\<NN>, f]\<^sub>\<circ>" 
          and \<FF>a_def: "\<FF>a = [\<FF>, a]\<^sub>\<circ>"
          and \<GG>b_def: "\<GG>b = [\<GG>, b]\<^sub>\<circ>" 
          and \<NN>: "\<NN> : \<FF> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)\<^esub> \<GG>" 
          and f: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
        by 
          (
            auto intro: 
              cat_prod_2_is_arrE[rotated 2, OF \<NN>f] 
              FUNCT.category_axioms 
              \<beta>\<CC>.category_axioms
          )
      note \<NN> = cat_FUNCT_is_arrD[OF \<NN>]
      note [cat_cs_simps] = 
        cat_ntcf_Yoneda_arrow_commutativity[OF assms \<NN>(1) f, folded \<NN>(2,3,4)]
      from \<NN>(1) assms(2) f show ?thesis
        unfolding \<NN>f_def \<FF>a_def \<GG>b_def
        by (subst (1 2) \<NN>(2), use nothing in \<open>subst \<NN>(3), subst \<NN>(4)\<close>)
          (
            cs_concl
              cs_simp: \<NN>(2,3,4)[symmetric] cat_cs_simps cs_intro: cat_cs_intros
          )+
    qed

  qed (use assms(2) in \<open>cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros\<close>)+

qed



subsection\<open>\<open>Hom\<close>-map\<close>

text\<open>
This subsection presents some of the results stated as Corollary 2 
in subsection 1.15 in \cite{bodo_categories_1970} and the corollary 
following the statement of the Yoneda Lemma on 
page 61 in \cite{mac_lane_categories_2010} in a variety of forms.
\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The following function makes an explicit appearance in subsection 1.15 in 
\cite{bodo_categories_1970}.
\<close>

definition ntcf_Hom_map :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "ntcf_Hom_map \<alpha> \<CC> a b = (\<lambda>f\<in>\<^sub>\<circ>Hom \<CC> a b. Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-))"


text\<open>Elementary properties.\<close>

mk_VLambda ntcf_Hom_map_def
  |vsv ntcf_Hom_map_vsv|
  |vdomain ntcf_Hom_map_vdomain[cat_cs_simps]|
  |app ntcf_Hom_map_app[unfolded in_Hom_iff, cat_cs_simps]|


subsubsection\<open>\<open>Hom\<close>-map is a bijection\<close>

lemma (in category) cat_ntcf_Hom_snd_is_ntcf_Hom_snd_unique:
  \<comment>\<open>The following lemma approximately corresponds to the corollary on 
page 61 in \cite{mac_lane_categories_2010}.\<close>
  assumes "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and "s \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<NN> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) r\<lparr>\<NN>\<rparr> : s \<mapsto>\<^bsub>\<CC>\<^esub> r"
    and "\<NN> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) r\<lparr>\<NN>\<rparr>,-)"
    and "\<And>f. \<lbrakk> f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>; \<NN> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-) \<rbrakk> \<Longrightarrow>
      f = Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) r\<lparr>\<NN>\<rparr>"
proof-

  interpret \<NN>: is_ntcf \<alpha> \<CC> \<open>cat_Set \<alpha>\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-)\<close> \<NN>
    by (rule assms(3))
  let ?Y_Hom_s = \<open>Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) r\<close>
  note Yoneda = 
    cat_Yoneda_Lemma[OF cat_cf_Hom_snd_is_functor[OF assms(2)] assms(1)]
  interpret Y: v11 \<open>?Y_Hom_s\<close> by (rule Yoneda(1))

  from category_axioms assms have \<NN>_in_vdomain: "\<NN> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (?Y_Hom_s)" 
    by (cs_concl cs_simp: these_ntcfs_iff cat_cs_simps cs_intro: cat_cs_intros) 
  then have "?Y_Hom_s\<lparr>\<NN>\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (?Y_Hom_s)" by (simp add: Y.vsv_vimageI2)
  from this category_axioms assms show Ym_\<NN>: "?Y_Hom_s\<lparr>\<NN>\<rparr> : s \<mapsto>\<^bsub>\<CC>\<^esub> r"
    unfolding Yoneda(2) 
    by (cs_prems_step cs_simp: cat_cs_simps cat_op_simps)+ simp
  then have "?Y_Hom_s\<lparr>\<NN>\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" by (simp add: cat_cs_intros)

  have "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(?Y_Hom_s\<lparr>\<NN>\<rparr>,-) :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (intro cat_ntcf_Hom_snd_is_ntcf Ym_\<NN>)

  from assms Ym_\<NN> this category_axioms assms have 
    "(?Y_Hom_s)\<inverse>\<^sub>\<circ>\<lparr>?Y_Hom_s\<lparr>\<NN>\<rparr>\<rparr> =
      Yoneda_arrow \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) r (?Y_Hom_s\<lparr>\<NN>\<rparr>)"
    by (intro category.inv_Yoneda_map_app)
      (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros) 
  then have "(?Y_Hom_s)\<inverse>\<^sub>\<circ>\<lparr>?Y_Hom_s\<lparr>\<NN>\<rparr>\<rparr> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(?Y_Hom_s\<lparr>\<NN>\<rparr>,-)"
    by (simp add: ntcf_Hom_snd_def'[OF Ym_\<NN>])
  with \<NN>_in_vdomain show "\<NN> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(?Y_Hom_s\<lparr>\<NN>\<rparr>,-)" by auto

  fix f assume prems: "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" "\<NN> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)"
  then obtain a b where f: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" by auto

  have "\<NN> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (rule cat_ntcf_Hom_snd_is_ntcf[OF f, folded prems(2)])
  with f \<NN>.ntcf_NTDom \<NN>.ntcf_NTCod assms cat_is_arrD(2,3)[OF f] 
  have ba_simps: "b = r" "a = s"
    by 
      (
        simp_all add: 
          prems(2) cat_cf_Hom_snd_inj cat_ntcf_Hom_snd_components(2,3)
      )
  from f have "f : s \<mapsto>\<^bsub>\<CC>\<^esub> r" unfolding ba_simps .

  with category_axioms show "f = ?Y_Hom_s\<lparr>\<NN>\<rparr>"
    unfolding prems(2) by (cs_concl cs_simp: cat_cs_simps cat_op_simps)

qed

lemma (in category) cat_ntcf_Hom_fst_is_ntcf_Hom_fst_unique:
  assumes "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and "s \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<NN> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,r) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,s) : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,s) r\<lparr>\<NN>\<rparr> : r \<mapsto>\<^bsub>\<CC>\<^esub> s"
    and "\<NN> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,s) r\<lparr>\<NN>\<rparr>)"
    and "\<And>f. \<lbrakk> f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>; \<NN> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,f) \<rbrakk> \<Longrightarrow>
      f = Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,s) r\<lparr>\<NN>\<rparr>"
  by 
    (
      intro  
        category.cat_ntcf_Hom_snd_is_ntcf_Hom_snd_unique[
          OF category_op, 
          unfolded cat_op_simps cat_op_cat_ntcf_Hom_snd, 
          OF assms(1,2), 
          unfolded assms(1,2)[THEN cat_op_cat_cf_Hom_snd],
          OF assms(3)
          ]
    )+

lemma (in category) cat_ntcf_Hom_snd_is_ntcf_Hom_snd_unique':
  assumes "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and "s \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<NN> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "\<exists>!f. f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> \<and> \<NN> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)"
  using cat_ntcf_Hom_snd_is_ntcf_Hom_snd_unique[OF assms] by blast

lemma (in category) cat_ntcf_Hom_fst_is_ntcf_Hom_fst_unique':
  assumes "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "s \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<NN> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,r) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,s) : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "\<exists>!f. f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> \<and> \<NN> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,f)"
  using cat_ntcf_Hom_fst_is_ntcf_Hom_fst_unique[OF assms] by blast

lemma (in category) cat_ntcf_Hom_snd_inj:
  assumes "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(g,-) = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)" 
    and "g : a \<mapsto>\<^bsub>\<CC>\<^esub> b" 
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" 
  shows "g = f"
proof-
  from assms have 
    "Yoneda_map \<alpha> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)) b\<lparr>Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(g,-)\<rparr> =
      Yoneda_map \<alpha> (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)) b\<lparr>Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)\<rparr>"
    by simp
  from this assms category_axioms show "g = f"
    by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros) 
      simp (*slow*)
qed

lemma (in category) cat_ntcf_Hom_fst_inj:
  assumes "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,g) = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,f)" 
    and "g : a \<mapsto>\<^bsub>\<CC>\<^esub> b" 
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" 
  shows "g = f"
proof-
  from category.cat_ntcf_Hom_snd_inj
    [
      OF category_op, 
      unfolded cat_op_simps,
      unfolded cat_op_cat_ntcf_Hom_snd,
      OF assms
    ]
  show ?thesis .
qed

lemma (in category) cat_ntcf_Hom_map: 
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "v11 (ntcf_Hom_map \<alpha> \<CC> a b)" 
    and "\<R>\<^sub>\<circ> (ntcf_Hom_map \<alpha> \<CC> a b) =
      these_ntcfs \<alpha> \<CC> (cat_Set \<alpha>) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)"
    and "(ntcf_Hom_map \<alpha> \<CC> a b)\<inverse>\<^sub>\<circ> =
      (\<lambda>\<NN>\<in>\<^sub>\<circ>these_ntcfs \<alpha> \<CC> (cat_Set \<alpha>) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-).
        Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) b\<lparr>\<NN>\<rparr>)"
proof-

  show "v11 (ntcf_Hom_map \<alpha> \<CC> a b)"
  proof(rule vsv.vsv_valeq_v11I, unfold ntcf_Hom_map_vdomain in_Hom_iff)
    show "vsv (ntcf_Hom_map \<alpha> \<CC> a b)" unfolding ntcf_Hom_map_def by simp
    fix g f assume prems: 
      "g : a \<mapsto>\<^bsub>\<CC>\<^esub> b" 
      "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
      "ntcf_Hom_map \<alpha> \<CC> a b\<lparr>g\<rparr> = ntcf_Hom_map \<alpha> \<CC> a b\<lparr>f\<rparr>"
    from prems(3,1,2) have "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(g,-) = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)"
      by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    with prems(1,2) show "g = f" by (intro cat_ntcf_Hom_snd_inj[of g f])
  qed
  then interpret Hm: v11 \<open>ntcf_Hom_map \<alpha> \<CC> a b\<close> .

  show Hm_vrange: "\<R>\<^sub>\<circ> (ntcf_Hom_map \<alpha> \<CC> a b) =
    these_ntcfs \<alpha> \<CC> (cat_Set \<alpha>) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)"
  proof(intro vsubset_antisym)
    show "\<R>\<^sub>\<circ> (ntcf_Hom_map \<alpha> \<CC> a b) \<subseteq>\<^sub>\<circ>
      these_ntcfs \<alpha> \<CC> (cat_Set \<alpha>) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)"
      by 
        (
          unfold ntcf_Hom_map_def,
          intro vrange_VLambda_vsubset, 
          unfold these_ntcfs_iff in_Hom_iff, 
          intro cat_ntcf_Hom_snd_is_ntcf
        )
    show "these_ntcfs \<alpha> \<CC> (cat_Set \<alpha>) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) \<subseteq>\<^sub>\<circ>
      \<R>\<^sub>\<circ> (ntcf_Hom_map \<alpha> \<CC> a b)"
    proof(intro vsubsetI, unfold these_ntcfs_iff)
      fix \<NN> assume prems: 
        "\<NN> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      note unique = 
        cat_ntcf_Hom_snd_is_ntcf_Hom_snd_unique[OF assms(2,1) prems]
      from unique(1) have 
        "Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) b\<lparr>\<NN>\<rparr> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (ntcf_Hom_map \<alpha> \<CC> a b)"
        by (cs_concl cs_simp: cat_cs_simps)
      moreover from 
        cat_ntcf_Hom_snd_is_ntcf_Hom_snd_unique(1,2)[OF assms(2,1) prems] 
      have \<NN>_def: "\<NN> = ntcf_Hom_map \<alpha> \<CC> a b\<lparr>Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) b\<lparr>\<NN>\<rparr>\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps)
      ultimately show "\<NN> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (ntcf_Hom_map \<alpha> \<CC> a b)" by force
    qed 
  qed

  show "(ntcf_Hom_map \<alpha> \<CC> a b)\<inverse>\<^sub>\<circ> =
    (
      \<lambda>\<NN>\<in>\<^sub>\<circ>these_ntcfs \<alpha> \<CC> (cat_Set \<alpha>) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-).
        Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) b\<lparr>\<NN>\<rparr>
    )"
  proof
    (
      rule vsv_eqI, 
      unfold vdomain_vconverse vdomain_VLambda Hm_vrange these_ntcfs_iff
    )

    from Hm.v11_axioms show "vsv ((ntcf_Hom_map \<alpha> \<CC> a b)\<inverse>\<^sub>\<circ>)" by auto
    show "vsv 
      (
        \<lambda>\<NN>\<in>\<^sub>\<circ>these_ntcfs \<alpha> \<CC> (cat_Set \<alpha>) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-).
          Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) b\<lparr>\<NN>\<rparr>
      )"
      by simp

    fix \<NN> assume prems: 
      "\<NN> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    then have \<NN>: 
      "\<NN> \<in>\<^sub>\<circ> these_ntcfs \<alpha> \<CC> (cat_Set \<alpha>) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)"
      unfolding these_ntcfs_iff by simp
    show "(ntcf_Hom_map \<alpha> \<CC> a b)\<inverse>\<^sub>\<circ>\<lparr>\<NN>\<rparr> =
      (
        \<lambda>\<NN>\<in>\<^sub>\<circ>these_ntcfs \<alpha> \<CC> (cat_Set \<alpha>) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-).
          Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) b\<lparr>\<NN>\<rparr>
      )\<lparr>\<NN>\<rparr>"
    proof
      (
        intro Hm.v11_vconverse_app, 
        unfold ntcf_Hom_map_vdomain in_Hom_iff beta[OF \<NN>]
      )
      note unique = 
        cat_ntcf_Hom_snd_is_ntcf_Hom_snd_unique[OF assms(2,1) prems]
      show "Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) b\<lparr>\<NN>\<rparr> : a \<mapsto>\<^bsub>\<CC>\<^esub> b" by (rule unique(1))
      then show 
        "ntcf_Hom_map \<alpha> \<CC> a b\<lparr>Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) b\<lparr>\<NN>\<rparr>\<rparr> = \<NN>"
        by (cs_concl cs_simp: unique(2)[symmetric] cat_cs_simps)
    qed

  qed simp

qed


subsubsection\<open>Inverse of a \<open>Hom\<close>-map\<close>

lemma (in category) inv_ntcf_Hom_map_v11: 
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "v11 ((ntcf_Hom_map \<alpha> \<CC> a b)\<inverse>\<^sub>\<circ>)"
  using cat_ntcf_Hom_map(1)[OF assms] by (simp add: v11.v11_vconverse)

lemma (in category) inv_ntcf_Hom_map_vdomain: 
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> ((ntcf_Hom_map \<alpha> \<CC> a b)\<inverse>\<^sub>\<circ>) =
    these_ntcfs \<alpha> \<CC> (cat_Set \<alpha>) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-)"
  unfolding cat_ntcf_Hom_map(3)[OF assms] by simp

lemmas [cat_cs_simps] = category.inv_ntcf_Hom_map_vdomain

lemma (in category) inv_ntcf_Hom_map_app: 
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<NN> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "(ntcf_Hom_map \<alpha> \<CC> a b)\<inverse>\<^sub>\<circ>\<lparr>\<NN>\<rparr> = Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) b\<lparr>\<NN>\<rparr>"
  using assms(3) unfolding cat_ntcf_Hom_map(3)[OF assms(1,2)] by simp

lemmas [cat_cs_simps] = category.inv_ntcf_Hom_map_app

lemma inv_ntcf_Hom_map_vrange: "\<R>\<^sub>\<circ> ((ntcf_Hom_map \<alpha> \<CC> a b)\<inverse>\<^sub>\<circ>) = Hom \<CC> a b"
  unfolding ntcf_Hom_map_def by simp


subsubsection\<open>\<open>Hom\<close>-natural transformation and isomorphisms\<close>


text\<open>
This subsection presents further results that were stated 
as Corollary 2 in subsection 1.15 in \cite{bodo_categories_1970}.
\<close>

lemma (in category) cat_is_arr_isomorphism_ntcf_Hom_snd_is_iso_ntcf:
  assumes "f : s \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-) :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-
  from assms obtain g 
    where iso_g: "g : r \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> s" 
      and gf: "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>s\<rparr>"
      and fg: "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g = \<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>"
    by 
      (
        auto intro:
          cat_the_inverse_Comp_CId_left 
          cat_the_inverse_Comp_CId_right 
          cat_the_inverse_is_arr_isomorphism'
      )
  then have g: "g : r \<mapsto>\<^bsub>\<CC>\<^esub> s" by auto
  show ?thesis
  proof(intro is_arr_isomorphism_is_iso_ntcf)
    from assms have f: "f : s \<mapsto>\<^bsub>\<CC>\<^esub> r" by auto
    with category_axioms show "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-) :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros) 
    from category_axioms g show "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(g,-) :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)    
    from category_axioms f g have 
      "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(g,-) = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f,-)"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    also from category_axioms f g have "\<dots> = ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-)"
      by (cs_concl cs_simp: gf cat_cs_simps cs_intro: cat_cs_intros)
    finally show 
      "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(g,-) = ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-)"
      by simp
    from category_axioms f g have 
      "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(g,-) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-) = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g,-)"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    also from category_axioms f g have "\<dots> = ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)"
      by (cs_concl cs_simp: fg cat_cs_simps cs_intro: cat_cs_intros)
    finally show 
      "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(g,-) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-) = ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)"
      by simp
  qed
qed

lemma (in category) cat_is_arr_isomorphism_ntcf_Hom_fst_is_iso_ntcf:
  assumes "f : r \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> s"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,f) :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,r) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,s) : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-
  from assms have r: "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and s: "s \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
  from 
    category.cat_is_arr_isomorphism_ntcf_Hom_snd_is_iso_ntcf
      [
        OF category_op, 
        unfolded cat_op_simps,
        OF assms,
        unfolded
          category.cat_op_cat_cf_Hom_snd[OF category_axioms r]
          category.cat_op_cat_cf_Hom_snd[OF category_axioms s]
          category.cat_op_cat_ntcf_Hom_snd[OF category_axioms]
      ]
  show ?thesis.
qed

lemma (in category) cat_ntcf_Hom_snd_is_iso_ntcf_Hom_snd_unique:
  assumes "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and "s \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<NN> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) r\<lparr>\<NN>\<rparr> : s \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r"
    and "\<NN> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) r\<lparr>\<NN>\<rparr>,-)"
    and "\<And>f. \<lbrakk> f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>; \<NN> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-) \<rbrakk> \<Longrightarrow>
      f = Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) r\<lparr>\<NN>\<rparr>"
proof-

  let ?Ym_\<NN> = \<open>Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) r\<lparr>\<NN>\<rparr>\<close>
    and ?Ym_inv_\<NN> = \<open>Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-) s\<lparr>inv_ntcf \<NN>\<rparr>\<close>

  from assms(3) have \<NN>:
    "\<NN> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by auto
  from iso_ntcf_is_arr_isomorphism[OF assms(3)] 
  have iso_inv_\<NN>: "inv_ntcf \<NN> : 
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and [simp]: "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<NN> = ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-)"
    and [simp]: "inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> = ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)"
    by auto
  from iso_inv_\<NN> have inv_\<NN>: 
    "inv_ntcf \<NN> : Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by auto 
  note unique = cat_ntcf_Hom_snd_is_ntcf_Hom_snd_unique[OF assms(1,2) \<NN>]
    and inv_unique = 
    cat_ntcf_Hom_snd_is_ntcf_Hom_snd_unique[OF assms(2,1) inv_\<NN>]
  have Ym_\<NN>: "?Ym_\<NN> : s \<mapsto>\<^bsub>\<CC>\<^esub> r" by (rule unique(1))

  show "\<NN> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) r\<lparr>\<NN>\<rparr>,-)"
    and "\<And>f. \<lbrakk> f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>; \<NN> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-) \<rbrakk> \<Longrightarrow>
      f = Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) r\<lparr>\<NN>\<rparr>"
    by (intro unique)+

  show "Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) r\<lparr>\<NN>\<rparr> : s \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r"
  proof(intro is_arr_isomorphismI[OF Ym_\<NN>, of \<open>?Ym_inv_\<NN>\<close>] is_inverseI)

    show Ym_inv_\<NN>: "?Ym_inv_\<NN> : r \<mapsto>\<^bsub>\<CC>\<^esub> s" by (rule inv_unique(1))
    
    have "ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) = \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<NN>" by simp
    also have "\<dots> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(?Ym_\<NN>,-) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(?Ym_inv_\<NN>,-)"
      by (subst unique(2), subst inv_unique(2)) simp
    also from category_axioms Ym_\<NN> inv_unique(1) assms(3) have 
      "\<dots> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(?Ym_inv_\<NN> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?Ym_\<NN>,-)"
      by (cs_concl cs_simp: cat_cs_simps)
    finally have "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(?Ym_inv_\<NN> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?Ym_\<NN>,-) = ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-)"
      by simp
    also from category_axioms assms(1,2) have "\<dots> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<CC>\<lparr>CId\<rparr>\<lparr>s\<rparr>,-)"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    finally have "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(?Ym_inv_\<NN> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?Ym_\<NN>,-) = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<CC>\<lparr>CId\<rparr>\<lparr>s\<rparr>,-)"
      by simp
    then show "?Ym_inv_\<NN> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?Ym_\<NN> = \<CC>\<lparr>CId\<rparr>\<lparr>s\<rparr>"
      by (rule cat_ntcf_Hom_snd_inj)
        (
          all\<open>
            use category_axioms Ym_\<NN> Ym_inv_\<NN> assms in 
              \<open>cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros\<close>
            \<close>
        )
    have "ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-) = inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN>" by simp
    also have "\<dots> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(?Ym_inv_\<NN>,-) \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(?Ym_\<NN>,-)"
      by (subst unique(2), subst inv_unique(2)) simp
    also from category_axioms Ym_\<NN> inv_unique(1) have 
      "\<dots> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(?Ym_\<NN> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?Ym_inv_\<NN>,-)"
      by (cs_concl cs_simp: cat_cs_simps)
    finally have 
      "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(?Ym_\<NN> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?Ym_inv_\<NN>,-) = ntcf_id Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-)"
      by simp
    also from category_axioms assms(1,2) have "\<dots> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>,-)"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    finally have 
      "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(?Ym_\<NN> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?Ym_inv_\<NN>,-) = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>,-)"
      by simp
    then show "?Ym_\<NN> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ?Ym_inv_\<NN> = \<CC>\<lparr>CId\<rparr>\<lparr>r\<rparr>"
      by (rule cat_ntcf_Hom_snd_inj)
        (
          all\<open>
            use category_axioms Ym_\<NN> Ym_inv_\<NN> assms in 
              \<open>cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros\<close>
            \<close>
        )

  qed (intro Ym_\<NN>)

qed

lemma (in category) cat_ntcf_Hom_fst_is_iso_ntcf_Hom_fst_unique:
  assumes "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and "s \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<NN> : 
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,r) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,s) : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,s) r\<lparr>\<NN>\<rparr> : r \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> s"
    and "\<NN> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,s) r\<lparr>\<NN>\<rparr>)"
    and "\<And>f. \<lbrakk> f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>; \<NN> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,f) \<rbrakk> \<Longrightarrow>
      f = Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,s) r\<lparr>\<NN>\<rparr>"
  by 
    (
      intro  
        category.cat_ntcf_Hom_snd_is_iso_ntcf_Hom_snd_unique[
          OF category_op, 
          unfolded cat_op_simps cat_op_cat_ntcf_Hom_snd, 
          OF assms(1,2), 
          unfolded assms(1,2)[THEN cat_op_cat_cf_Hom_snd],
          OF assms(3)
          ]
    )+

lemma (in category) cat_is_arr_isomorphism_if_ntcf_Hom_snd_is_iso_ntcf:
  assumes "f : s \<mapsto>\<^bsub>\<CC>\<^esub> r"
    and "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-) :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(r,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "f : s \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> r"
proof-
  from assms(1) have r: "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and s: "s \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
  note unique = cat_ntcf_Hom_snd_is_iso_ntcf_Hom_snd_unique[OF r s assms(2)]
  from unique(1) have Ym_Hf: 
    "Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(s,-) r\<lparr>Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)\<rparr> : s \<mapsto>\<^bsub>\<CC>\<^esub> r"
    by auto
  from unique(1) show ?thesis
    unfolding cat_ntcf_Hom_snd_inj[OF unique(2) assms(1) Ym_Hf, symmetric]
    by simp
qed

lemma (in category) cat_is_arr_isomorphism_if_ntcf_Hom_fst_is_iso_ntcf:
  assumes "f : r \<mapsto>\<^bsub>\<CC>\<^esub> s"
    and "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,f) :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,r) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,s) : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "f : r \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> s"
proof-
  from assms(1) have r: "r \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and s: "s \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
  note unique = cat_ntcf_Hom_fst_is_iso_ntcf_Hom_fst_unique[OF r s assms(2)]
  from unique(1) have Ym_Hf: 
    "Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,s) r\<lparr>Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(-,f)\<rparr> : r \<mapsto>\<^bsub>\<CC>\<^esub> s"
    by auto
  from unique(1) show ?thesis
    unfolding cat_ntcf_Hom_fst_inj[OF unique(2) assms(1) Ym_Hf, symmetric]
    by simp
qed


subsubsection\<open>
The relationship between a \<open>Hom\<close>-natural transformation and the compositions 
of a \<open>Hom\<close>-natural transformation and a natural transformation
\<close>

lemma (in category) cat_ntcf_lcomp_Hom_ntcf_Hom_snd_NTMap_app:
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-)\<lparr>NTMap\<rparr>\<lparr>b, c\<rparr>\<^sub>\<bullet> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<phi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>,-)\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
proof-      
  interpret \<phi>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))
  from assms(2) have b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" unfolding cat_op_simps by simp
  from category_axioms assms(1,3) b show ?thesis
    by 
      (
        cs_concl 
          cs_simp: 
            cat_ntcf_lcomp_Hom_component_is_Yoneda_component cat_cs_simps 
          cs_intro: cat_cs_intros cat_op_intros
      )
qed

lemmas [cat_cs_simps] = category.cat_ntcf_lcomp_Hom_ntcf_Hom_snd_NTMap_app

lemma (in category) cat_bnt_proj_snd_tcf_lcomp_Hom_ntcf_Hom_snd:
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-)\<^bsub>op_cat \<BB>,\<CC>\<^esub>(b,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<phi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>,-)"
proof-
  interpret \<phi>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))  
  show ?thesis
  proof(rule ntcf_eqI[of \<alpha>])
    from category_axioms assms show 
      "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-)\<^bsub>op_cat \<BB>,\<CC>\<^esub>(b,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F : 
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) : 
      \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"      
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)
    from assms this have dom_lhs:
      "\<D>\<^sub>\<circ> ((Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-)\<^bsub>op_cat \<BB>,\<CC>\<^esub>(b,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from category_axioms assms show 
      "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<phi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>,-) :
        Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) :
        \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from assms this have dom_rhs: 
      "\<D>\<^sub>\<circ> (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<phi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>,-)\<lparr>NTMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    show 
      "(Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-)\<^bsub>op_cat \<BB>,\<CC>\<^esub>(b,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr> = 
        Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<phi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>,-)\<lparr>NTMap\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix a assume "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
      with category_axioms assms show
        "(Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-)\<^bsub>op_cat \<BB>,\<CC>\<^esub>(b,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
          Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<phi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>,-)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps) 
    qed (use assms(2) in \<open>auto intro: cat_cs_intros\<close>)
  qed simp_all
qed

lemmas [cat_cs_simps] = category.cat_bnt_proj_snd_tcf_lcomp_Hom_ntcf_Hom_snd


subsubsection\<open>
The relationship between the \<open>Hom\<close>-natural isomorphisms and the compositions
of a \<open>Hom\<close>-natural isomorphism and a natural transformation
\<close>

lemma (in category) cat_ntcf_lcomp_Hom_if_ntcf_Hom_snd_is_iso_ntcf:
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>b. b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr> \<Longrightarrow> Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<phi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>,-) :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) :
      \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-) :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-) :
    op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-
  interpret \<phi>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))
  have "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-)\<^bsub>op_cat \<BB>,\<CC>\<^esub>(b,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F : 
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-)\<^bsub>op_cat \<BB>,\<CC>\<^esub>(b,-)\<^sub>C\<^sub>F \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o 
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)\<^bsub>op_cat \<BB>,\<CC>\<^esub>(b,-)\<^sub>C\<^sub>F : 
    \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    if "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" for b
    unfolding 
      cat_bnt_proj_snd_tcf_lcomp_Hom_ntcf_Hom_snd[OF assms(1) that]
      cat_cf_lcomp_Hom_cf_Hom_snd[OF \<phi>.NTDom.is_functor_axioms that]
      cat_cf_lcomp_Hom_cf_Hom_snd[OF \<phi>.NTCod.is_functor_axioms that]
    by (intro assms(2) that)
  from 
    is_iso_ntcf_if_bnt_proj_snd_is_iso_ntcf[
      OF 
        \<phi>.NTDom.HomDom.category_op category_axioms 
        cat_ntcf_lcomp_Hom_is_ntcf[OF assms(1)], 
      unfolded cat_op_simps, OF this
      ]
  show ?thesis .
qed

lemma (in category) cat_ntcf_Hom_snd_if_ntcf_lcomp_Hom_is_iso_ntcf:
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-) :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-) :
      op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<phi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>,-) :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) :
    \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-
  interpret \<phi>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))
  from category_axioms assms show ?thesis
    by  
      (
        fold 
          cat_bnt_proj_snd_tcf_lcomp_Hom_ntcf_Hom_snd[OF assms(1,3)]
          cat_cf_lcomp_Hom_cf_Hom_snd[OF \<phi>.NTDom.is_functor_axioms assms(3)]
          cat_cf_lcomp_Hom_cf_Hom_snd[OF \<phi>.NTCod.is_functor_axioms assms(3)],
        intro bnt_proj_snd_is_iso_ntcf_if_is_iso_ntcf
      )    
      (cs_concl cs_simp: cat_op_simps cs_intro: cat_cs_intros)
qed



subsection\<open>Yoneda map for arbitrary functors\<close>


text\<open>
The concept of the Yoneda map for arbitrary functors was developed based
on the function that was used in the statement of Lemma 3 in 
subsection 1.15 in \cite{bodo_categories_1970}.
\<close>

definition af_Yoneda_map :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "af_Yoneda_map \<alpha> \<FF> \<GG> =
    (\<lambda>\<phi>\<in>\<^sub>\<circ>these_ntcfs \<alpha> (\<FF>\<lparr>HomDom\<rparr>) (\<FF>\<lparr>HomCod\<rparr>) \<FF> \<GG>. Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-))"


text\<open>Elementary properties.\<close>

context
  fixes \<alpha> \<BB> \<CC> \<FF> \<GG>
  assumes \<FF>: "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and \<GG>: "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
begin

interpretation \<FF>: is_functor \<alpha> \<BB> \<CC> \<FF> by (rule \<FF>)
interpretation \<GG>: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule \<GG>)

mk_VLambda 
  af_Yoneda_map_def[where \<FF>=\<FF> and \<GG>=\<GG>, unfolded \<FF>.cf_HomDom \<FF>.cf_HomCod]
  |vsv af_Yoneda_map_vsv|
  |vdomain af_Yoneda_map_vdomain[cat_cs_simps]|
  |app af_Yoneda_map_app[unfolded these_ntcfs_iff, cat_cs_simps]|

end



subsection\<open>Yoneda arrow for arbitrary functors\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The following natural transformation is used in the proof of Lemma 3 in 
subsection 1.15 in \cite{bodo_categories_1970}.
\<close>

definition af_Yoneda_arrow :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN> =
    [
      (
        \<lambda>b\<in>\<^sub>\<circ>(\<FF>\<lparr>HomDom\<rparr>)\<lparr>Obj\<rparr>.
          Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<FF>\<lparr>HomCod\<rparr>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) (\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)\<lparr>
            \<NN>\<^bsub>op_cat (\<FF>\<lparr>HomDom\<rparr>),\<FF>\<lparr>HomCod\<rparr>\<^esub>(b,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F
            \<rparr>
      ),
      \<FF>,
      \<GG>,
      \<FF>\<lparr>HomDom\<rparr>,
      \<FF>\<lparr>HomCod\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma af_Yoneda_arrow_components:
  shows "af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN>\<lparr>NTMap\<rparr> =
      (
        \<lambda>b\<in>\<^sub>\<circ>\<FF>\<lparr>HomDom\<rparr>\<lparr>Obj\<rparr>.
          Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<FF>\<lparr>HomCod\<rparr>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) (\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)\<lparr>
            \<NN>\<^bsub>op_cat (\<FF>\<lparr>HomDom\<rparr>),\<FF>\<lparr>HomCod\<rparr>\<^esub>(b,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F
            \<rparr>
      )"
    and "af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN>\<lparr>NTDom\<rparr> = \<FF>"
    and "af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN>\<lparr>NTCod\<rparr> = \<GG>"
    and "af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN>\<lparr>NTDGDom\<rparr> = \<FF>\<lparr>HomDom\<rparr>"
    and "af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN>\<lparr>NTDGCod\<rparr> = \<FF>\<lparr>HomCod\<rparr>"
  unfolding af_Yoneda_arrow_def nt_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Natural transformation map\<close>

mk_VLambda af_Yoneda_arrow_components(1)
  |vsv af_Yoneda_arrow_NTMap_vsv|

context
  fixes \<alpha> \<BB> \<CC> \<FF>
  assumes \<FF>: "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
begin

interpretation \<FF>: is_functor \<alpha> \<BB> \<CC> \<FF> by (rule \<FF>)

mk_VLambda 
  af_Yoneda_arrow_components(1)[where \<FF>=\<FF>, unfolded \<FF>.cf_HomDom \<FF>.cf_HomCod]
  |vdomain af_Yoneda_arrow_NTMap_vdomain[cat_cs_simps]|
  |app af_Yoneda_arrow_NTMap_app[cat_cs_simps]|

end

lemma (in category) cat_af_Yoneda_arrow_is_ntcf:
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-) :
      op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-

  let ?H\<GG> = \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-)\<close>
    and ?H\<FF> = \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)\<close>
    and ?Set = \<open>cat_Set \<alpha>\<close>
    and ?Ym = 
      \<open>
        \<lambda>b. Yoneda_map
          \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) (\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)\<lparr>\<NN>\<^bsub>op_cat \<BB>,\<CC>\<^esub>(b,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<rparr>
      \<close>

  interpret \<FF>: is_functor \<alpha> \<BB> \<CC> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(2))
  interpret \<NN>: is_ntcf 
    \<alpha> \<open>op_cat \<BB> \<times>\<^sub>C \<CC>\<close> \<open>cat_Set \<alpha>\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-)\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)\<close> \<NN> 
    by (rule assms)

  have comm[unfolded cat_op_simps]:
    "(\<NN>\<lparr>NTMap\<rparr> \<lparr>c, d\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (q \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>)\<rparr> =
      f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ((\<NN>\<lparr>NTMap\<rparr> \<lparr>a, b\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>q\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>)"
    if "g : a \<mapsto>\<^bsub>op_cat \<BB>\<^esub> c" and "f : b \<mapsto>\<^bsub>\<CC>\<^esub> d" and "q : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> b" 
    for q g f a b c d
  proof-
    from that(1) have g: "g : c \<mapsto>\<^bsub>\<BB>\<^esub> a" unfolding cat_op_simps by simp
    from category_axioms assms g that(2) have ab:
      "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (op_cat \<BB> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
      by 
        (
          cs_concl 
            cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
        )
    from \<NN>.ntcf_NTMap_is_arr[OF ab] category_axioms assms g that(2) have \<NN>ab: 
      "\<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> :
        Hom \<CC> (\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) b \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> (\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) b"
      by 
        (
          cs_prems 
            cs_simp: cat_cs_simps 
            cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
        )
    have \<NN>_abq: "(\<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>q\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> b"
      by 
        (
          rule cat_Set_ArrVal_app_vrange[
            OF \<NN>ab, unfolded in_Hom_iff, OF that(3)
            ]
        )
    have "[g, f]\<^sub>\<circ> : [a, b]\<^sub>\<circ> \<mapsto>\<^bsub>op_cat \<BB> \<times>\<^sub>C \<CC>\<^esub> [c, d]\<^sub>\<circ>"
      by 
        (
          rule 
            cat_prod_2_is_arrI[
              OF \<FF>.HomDom.category_op category_axioms that(1,2)
              ]
        )
    then have 
      "\<NN>\<lparr>NTMap\<rparr>\<lparr>c, d\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-)\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> =
        Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>"
      by (rule is_ntcf.ntcf_Comp_commute[OF assms(3)])
    then have 
      "(\<NN>\<lparr>NTMap\<rparr>\<lparr>c, d\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>?Set\<^esub> ?H\<GG>\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>q\<rparr> =
        (?H\<FF>\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>?Set\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>q\<rparr>"
      by auto

    from 
      this that(2,3) assms
      category_axioms \<FF>.HomDom.category_axioms \<FF>.HomDom.category_op category_op
      g \<NN>ab \<NN>_abq 
    show
      "(\<NN>\<lparr>NTMap\<rparr>\<lparr>c, d\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (q \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>)\<rparr> =
        f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> ((\<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>q\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>)" 
      by 
        (
          cs_prems
            cs_simp: cat_cs_simps 
            cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
        )
  qed

  show ?thesis
  proof(rule is_ntcfI')

    show "vfsequence (af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN>)"
      unfolding af_Yoneda_arrow_def by simp
    show "vcard (af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN>) = 5\<^sub>\<nat>"
      unfolding af_Yoneda_arrow_def by (simp add: nat_omega_simps)

    have \<NN>b: "\<NN>\<^bsub>op_cat \<BB>,\<CC>\<^esub>(b,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) :
      \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      if "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" for b
      by 
        (
          rule 
            bnt_proj_snd_is_ntcf
              [
                OF \<FF>.HomDom.category_op category_axioms assms(3),
                unfolded cat_op_simps, 
                OF that,
                unfolded 
                  cat_cf_lcomp_Hom_cf_Hom_snd[OF assms(1) that]
                  cat_cf_lcomp_Hom_cf_Hom_snd[OF assms(2) that]
              ]
        )

    show "af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      if "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" for b
    proof-
      let ?\<GG>b = \<open>\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<close>
        and ?\<FF>b = \<open>\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<close>
        and ?\<CC>\<GG>b = \<open>\<CC>\<lparr>CId\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<rparr>\<close>
      from that have \<CC>\<GG>b: "?\<CC>\<GG>b : ?\<GG>b \<mapsto>\<^bsub>\<CC>\<^esub> ?\<GG>b" by (auto simp: cat_cs_intros)
      from assms that have "[b, ?\<GG>b]\<^sub>\<circ> \<in>\<^sub>\<circ> (op_cat \<BB> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps 
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
      from \<NN>.ntcf_NTMap_is_arr[OF this] category_axioms assms that have \<NN>_b\<GG>b: 
        "\<NN>\<lparr>NTMap\<rparr>\<lparr>b, ?\<GG>b\<rparr>\<^sub>\<bullet> : Hom \<CC> ?\<GG>b ?\<GG>b \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> ?\<FF>b ?\<GG>b"
        by 
          (
            cs_prems 
              cs_simp: cat_cs_simps cat_op_simps 
              cs_intro: cat_cs_intros cat_prod_cs_intros
          )
      from \<CC>\<GG>b have \<NN>_b\<GG>b_\<CC>\<GG>b: 
        "(\<NN>\<lparr>NTMap\<rparr>\<lparr>b, ?\<GG>b\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>?\<CC>\<GG>b\<rparr> : ?\<FF>b \<mapsto>\<^bsub>\<CC>\<^esub> ?\<GG>b"
        by (rule cat_Set_ArrVal_app_vrange[OF \<NN>_b\<GG>b, unfolded in_Hom_iff])
      with category_axioms assms that \<NN>b[OF that] show ?thesis
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)
    qed

    show 
      "af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = 
        \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN>\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      if "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b" for a b f
    proof-

      from that have a: "a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" by auto
      
      let ?\<BB>a = \<open>\<BB>\<lparr>CId\<rparr>\<lparr>a\<rparr>\<close>
        and ?\<BB>b = \<open>\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>\<close>
        and ?\<GG>a = \<open>\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<close>
        and ?\<GG>b = \<open>\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<close>
        and ?\<FF>a = \<open>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<close>
        and ?\<FF>b = \<open>\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<close>
        and ?\<CC>\<GG>a = \<open>\<CC>\<lparr>CId\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>\<close>
        and ?\<CC>\<GG>b = \<open>\<CC>\<lparr>CId\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<rparr>\<close>

      from that have \<CC>\<GG>a: "?\<CC>\<GG>a : ?\<GG>a \<mapsto>\<^bsub>\<CC>\<^esub> ?\<GG>a" by (auto intro: cat_cs_intros)
      from that have \<CC>\<GG>b: "?\<CC>\<GG>b : ?\<GG>b \<mapsto>\<^bsub>\<CC>\<^esub> ?\<GG>b" by (auto intro: cat_cs_intros)
      from that have \<BB>a: "?\<BB>a : a \<mapsto>\<^bsub>\<BB>\<^esub> a" by (auto intro: cat_cs_intros)

      from assms that have "[b, ?\<GG>b]\<^sub>\<circ> \<in>\<^sub>\<circ> (op_cat \<BB> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps 
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
      from \<NN>.ntcf_NTMap_is_arr[OF this] category_axioms assms that have \<NN>_b\<GG>b: 
        "\<NN>\<lparr>NTMap\<rparr>\<lparr>b, ?\<GG>b\<rparr>\<^sub>\<bullet> : Hom \<CC> ?\<GG>b ?\<GG>b \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> ?\<FF>b ?\<GG>b"
        by 
          (
            cs_prems 
              cs_simp: cat_cs_simps cat_op_simps
              cs_intro: cat_cs_intros cat_prod_cs_intros
          )
      from \<CC>\<GG>b have \<NN>_b\<GG>b_\<CC>\<GG>b: 
        "(\<NN>\<lparr>NTMap\<rparr>\<lparr>b, ?\<GG>b\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>?\<CC>\<GG>b\<rparr> : ?\<FF>b \<mapsto>\<^bsub>\<CC>\<^esub> ?\<GG>b"
        by (rule cat_Set_ArrVal_app_vrange[OF \<NN>_b\<GG>b, unfolded in_Hom_iff])

      from assms that have "[a, ?\<GG>a]\<^sub>\<circ> \<in>\<^sub>\<circ> (op_cat \<BB> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps 
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
      from \<NN>.ntcf_NTMap_is_arr[OF this] category_axioms assms that have \<NN>_a\<GG>a: 
        "\<NN>\<lparr>NTMap\<rparr>\<lparr>a, ?\<GG>a\<rparr>\<^sub>\<bullet> : Hom \<CC> ?\<GG>a ?\<GG>a \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<CC> ?\<FF>a ?\<GG>a"
        by 
          (
            cs_prems 
              cs_simp: cat_cs_simps cat_op_simps 
              cs_intro: cat_cs_intros cat_prod_cs_intros
          )
      from \<CC>\<GG>a have \<NN>_a\<GG>a_\<CC>\<GG>a: 
        "(\<NN>\<lparr>NTMap\<rparr>\<lparr>a, ?\<GG>a\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>?\<CC>\<GG>a\<rparr> : ?\<FF>a \<mapsto>\<^bsub>\<CC>\<^esub> ?\<GG>a"
        by (rule cat_Set_ArrVal_app_vrange[OF \<NN>_a\<GG>a, unfolded in_Hom_iff])

      from 
        comm[OF \<BB>a \<GG>.cf_ArrMap_is_arr[OF that] \<CC>\<GG>a] 
        category_axioms assms that \<NN>_a\<GG>a_\<CC>\<GG>a
      have \<NN>_a_\<GG>b[symmetric, cat_cs_simps]:
        "(\<NN>\<lparr>NTMap\<rparr>\<lparr>a, ?\<GG>b\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>\<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr> =
          \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<NN>\<lparr>NTMap\<rparr>\<lparr>a, ?\<GG>a\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>?\<CC>\<GG>a\<rparr>"
        by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

      from comm[OF that \<CC>\<GG>b \<CC>\<GG>b] category_axioms assms that \<NN>_b\<GG>b_\<CC>\<GG>b
      have \<NN>_a_\<GG>b'[cat_cs_simps]:
        "(\<NN>\<lparr>NTMap\<rparr>\<lparr>a, ?\<GG>b\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>\<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr> =
          (\<NN>\<lparr>NTMap\<rparr>\<lparr>b, ?\<GG>b\<rparr>\<^sub>\<bullet>)\<lparr>ArrVal\<rparr>\<lparr>?\<CC>\<GG>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
        by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

      from category_axioms assms that \<NN>b[OF a] \<NN>b[OF b] show ?thesis
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)

    qed

  qed (auto simp: af_Yoneda_arrow_components cat_cs_simps intro: cat_cs_intros)

qed

lemma (in category) cat_af_Yoneda_arrow_is_ntcf':
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-) :
      op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "\<beta> = \<alpha>"
    and "\<FF>' = \<FF>"
    and "\<GG>' = \<GG>"
  shows "af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN> : \<FF>' \<mapsto>\<^sub>C\<^sub>F \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> \<CC>"
  using assms(1-3) unfolding assms(4-6) by (rule cat_af_Yoneda_arrow_is_ntcf)

lemmas [cat_cs_intros] = category.cat_af_Yoneda_arrow_is_ntcf'


subsubsection\<open>Yoneda Lemma for arbitrary functors\<close>


text\<open>
The following lemmas correspond to variants of the elements of Lemma 3 
in subsection 1.15 in \cite{bodo_categories_1970}.
\<close>

lemma (in category) cat_af_Yoneda_map_af_Yoneda_arrow_app:
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-) :
      op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "\<NN> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN>-,-)"
proof-

  let ?H\<GG> = \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-)\<close>
    and ?H\<FF> = \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)\<close>
    and ?aYa = \<open>\<lambda>\<NN>. af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN>\<close>

  interpret \<FF>: is_functor \<alpha> \<BB> \<CC> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(2))

  interpret \<NN>: is_ntcf \<alpha> \<open>op_cat \<BB> \<times>\<^sub>C \<CC>\<close> \<open>cat_Set \<alpha>\<close> \<open>?H\<GG>\<close> \<open>?H\<FF>\<close> \<NN>
    by (rule assms(3))
  interpret aY\<NN>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<open>?aYa \<NN>\<close>
    by (rule cat_af_Yoneda_arrow_is_ntcf[OF assms])
  interpret HY\<NN>: is_ntcf 
    \<alpha> \<open>op_cat \<BB> \<times>\<^sub>C \<CC>\<close> \<open>cat_Set \<alpha>\<close> \<open>?H\<GG>\<close> \<open>?H\<FF>\<close> \<open>Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(?aYa \<NN>-,-)\<close>
    by (rule cat_ntcf_lcomp_Hom_is_ntcf[OF aY\<NN>.is_ntcf_axioms])
  
  show [cat_cs_simps]: "\<NN> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(?aYa \<NN>-,-)"
  proof 
    (
      rule sym,
      rule ntcf_eqI[OF HY\<NN>.is_ntcf_axioms assms(3)], 
      rule vsv_eqI;
      (intro HY\<NN>.NTMap.vsv_axioms \<NN>.NTMap.vsv_axioms)?;
      (unfold \<NN>.ntcf_NTMap_vdomain HY\<NN>.ntcf_NTMap_vdomain)?
    )
    fix bc assume prems': "bc \<in>\<^sub>\<circ> (op_cat \<BB> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
    then obtain b c
      where bc_def: "bc = [b, c]\<^sub>\<circ>" 
        and op_b: "b \<in>\<^sub>\<circ> op_cat \<BB>\<lparr>Obj\<rparr>" 
        and c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
      by (auto intro: cat_prod_2_ObjE cat_cs_intros)
    from op_b have b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" unfolding cat_op_simps by simp

    then have \<GG>b: "\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and \<FF>b: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
      by (auto intro: cat_cs_intros)
    have Ym_\<NN>:
      "Yoneda_map \<alpha> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) (\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>)\<lparr>
        \<NN>\<^bsub>op_cat \<BB>,\<CC>\<^esub>(b,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F
        \<rparr> = ?aYa \<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>"
      unfolding af_Yoneda_arrow_NTMap_app[OF assms(1) b] by simp
    
    from 
      bnt_proj_snd_is_ntcf
        [
          OF \<FF>.HomDom.category_op category_axioms assms(3) op_b,
          unfolded 
            cat_cf_lcomp_Hom_cf_Hom_snd[OF assms(1) b]
            cat_cf_lcomp_Hom_cf_Hom_snd[OF assms(2) b]
        ]
    have \<NN>b: "\<NN>\<^bsub>op_cat \<BB>,\<CC>\<^esub>(b,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) :
      \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      by simp
    from c show "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(?aYa \<NN>-,-)\<lparr>NTMap\<rparr>\<lparr>bc\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>bc\<rparr>"
      unfolding 
        bc_def 
        cat_ntcf_lcomp_Hom_ntcf_Hom_snd_NTMap_app[OF aY\<NN>.is_ntcf_axioms b c]
        cat_ntcf_Hom_snd_is_ntcf_Hom_snd_unique(2)[
          OF \<GG>b \<FF>b \<NN>b, unfolded Ym_\<NN>, symmetric
          ]
      by (cs_concl cs_simp: cat_cs_simps)

  qed simp_all

qed

lemma (in category) cat_af_Yoneda_Lemma:
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "v11 (af_Yoneda_map \<alpha> \<FF> \<GG>)"
    and "\<R>\<^sub>\<circ> (af_Yoneda_map \<alpha> \<FF> \<GG>) =
    these_ntcfs \<alpha> (op_cat \<BB> \<times>\<^sub>C \<CC>) (cat_Set \<alpha>) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)"
    and "(af_Yoneda_map \<alpha> \<FF> \<GG>)\<inverse>\<^sub>\<circ> =
      (
        \<lambda>\<NN>\<in>\<^sub>\<circ>these_ntcfs
          \<alpha> (op_cat \<BB> \<times>\<^sub>C \<CC>) (cat_Set \<alpha>) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-).
          af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN>
      )"
proof-

  let ?H\<GG> = \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-)\<close>
    and ?H\<FF> = \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)\<close>
    and ?aYm = \<open>af_Yoneda_map \<alpha> \<FF> \<GG>\<close>
    and ?aYa = \<open>\<lambda>\<NN>. af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN>\<close>

  interpret \<FF>: is_functor \<alpha> \<BB> \<CC> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(2))

  show v11_aY: "v11 ?aYm"
  proof
    (
      intro vsv.vsv_valeq_v11I,
      unfold af_Yoneda_map_vdomain[OF assms] these_ntcfs_iff
    )
    
    show "vsv (af_Yoneda_map \<alpha> \<FF> \<GG>)" by (rule af_Yoneda_map_vsv[OF assms])

    fix \<phi> \<psi> assume prems:
      "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      "\<psi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
      "?aYm\<lparr>\<phi>\<rparr> = ?aYm\<lparr>\<psi>\<rparr>"

    interpret \<phi>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<phi> by (rule prems(1))
    interpret \<psi>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<psi> by (rule prems(2))

    from prems(3) have H\<phi>_H\<psi>: "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-) = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<psi>-,-)"
      unfolding 
        af_Yoneda_map_app[OF assms prems(1)]
        af_Yoneda_map_app[OF assms prems(2)]
      by simp

    show "\<phi> = \<psi>"
    proof
      (
        rule ntcf_eqI[OF prems(1,2)], 
        rule vsv_eqI, 
        unfold \<phi>.ntcf_NTMap_vdomain \<psi>.ntcf_NTMap_vdomain
      )
      fix b assume prems': "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
      from prems' have \<phi>b: "\<phi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>" 
        and \<psi>b: "\<psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>" 
        and \<GG>b: "\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
        and \<FF>b: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
        by (auto intro: cat_cs_intros cat_prod_cs_intros)
      have "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<phi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>,-) = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>,-)"
      proof
        (
          rule 
            ntcf_eqI
              [
                OF 
                  cat_ntcf_Hom_snd_is_ntcf[OF \<phi>b] 
                  cat_ntcf_Hom_snd_is_ntcf[OF \<psi>b]
              ]
        )
        show "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<phi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>,-)\<lparr>NTMap\<rparr> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>,-)\<lparr>NTMap\<rparr>"
        proof
          (
            rule vsv_eqI, 
            unfold 
              ntcf_Hom_snd_NTMap_vdomain[OF \<phi>b]
              ntcf_Hom_snd_NTMap_vdomain[OF \<psi>b]
          )
          fix c assume prems'': "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
          note H = cat_ntcf_lcomp_Hom_ntcf_Hom_snd_NTMap_app
          show 
            "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<phi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>,-)\<lparr>NTMap\<rparr>\<lparr>c\<rparr> =
              Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>,-)\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
            unfolding 
              H[OF prems(1) prems' prems'', symmetric]
              H[OF prems(2) prems' prems'', symmetric]
              H\<phi>_H\<psi>
            by simp
        qed 
          (
            simp_all add: 
              ntcf_Hom_snd_NTMap_vsv[OF \<psi>b] ntcf_Hom_snd_NTMap_vsv[OF \<phi>b]
          )
      qed simp_all
      with \<phi>b \<psi>b show "\<phi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> = \<psi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>"
        by (auto intro: cat_ntcf_Hom_snd_inj)
    qed auto

  qed

  interpret aYm: v11 ?aYm by (rule v11_aY)

  have [cat_cs_simps]: "?aYm\<lparr>?aYa \<NN>\<rparr> = \<NN>"
    if "\<NN> : ?H\<GG> \<mapsto>\<^sub>C\<^sub>F ?H\<FF> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>" for \<NN>
    using category_axioms assms that 
    by 
      (
        cs_concl 
          cs_simp: 
            cat_af_Yoneda_map_af_Yoneda_arrow_app[symmetric] cat_cs_simps
          cs_intro: cat_cs_intros
      )

  show aYm_vrange: 
    "\<R>\<^sub>\<circ> ?aYm = these_ntcfs \<alpha> (op_cat \<BB> \<times>\<^sub>C \<CC>) (cat_Set \<alpha>) ?H\<GG> ?H\<FF>"
  proof(intro vsubset_antisym)
    
    show "\<R>\<^sub>\<circ> ?aYm \<subseteq>\<^sub>\<circ> these_ntcfs \<alpha> (op_cat \<BB> \<times>\<^sub>C \<CC>) (cat_Set \<alpha>) ?H\<GG> ?H\<FF>"
    proof
      (
        rule vsv.vsv_vrange_vsubset, 
        unfold these_ntcfs_iff af_Yoneda_map_vdomain[OF assms]
      )
      fix \<phi> assume "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      with category_axioms assms show 
        "?aYm\<lparr>\<phi>\<rparr> : ?H\<GG> \<mapsto>\<^sub>C\<^sub>F ?H\<FF> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    qed (auto intro: af_Yoneda_map_vsv)

    show "these_ntcfs \<alpha> (op_cat \<BB> \<times>\<^sub>C \<CC>) (cat_Set \<alpha>) ?H\<GG> ?H\<FF> \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> ?aYm"
    proof(rule vsubsetI, unfold these_ntcfs_iff)
      fix \<NN> assume prems: 
        "\<NN> : ?H\<GG> \<mapsto>\<^sub>C\<^sub>F ?H\<FF> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      interpret aY\<NN>: is_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<open>?aYa \<NN>\<close>
        by (rule cat_af_Yoneda_arrow_is_ntcf[OF assms prems])
      from prems have \<NN>_def: "\<NN> = ?aYm\<lparr>?aYa \<NN>\<rparr>" 
        by (cs_concl cs_simp: cat_cs_simps)
      from assms aY\<NN>.is_ntcf_axioms have "?aYa \<NN> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ?aYm"
        by (cs_concl cs_simp: these_ntcfs_iff cat_cs_simps)
      then show "\<NN> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> ?aYm" by (subst \<NN>_def, intro aYm.vsv_vimageI2) auto
    qed

  qed

  show "?aYm\<inverse>\<^sub>\<circ> =
    (\<lambda>\<NN>\<in>\<^sub>\<circ>these_ntcfs \<alpha> (op_cat \<BB> \<times>\<^sub>C \<CC>) (cat_Set \<alpha>) ?H\<GG> ?H\<FF>. ?aYa \<NN>)"
  proof
    (
      rule vsv_eqI, 
      unfold vdomain_vconverse vdomain_VLambda aYm_vrange these_ntcfs_iff
    )
    from aYm.v11_axioms show "vsv ((af_Yoneda_map \<alpha> \<FF> \<GG>)\<inverse>\<^sub>\<circ>)" by auto
    fix \<NN> assume prems: "\<NN> : ?H\<GG> \<mapsto>\<^sub>C\<^sub>F ?H\<FF> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    then have \<NN>: "\<NN> \<in>\<^sub>\<circ> these_ntcfs \<alpha> (op_cat \<BB> \<times>\<^sub>C \<CC>) (cat_Set \<alpha>) ?H\<GG> ?H\<FF>" 
      by simp
    show "?aYm\<inverse>\<^sub>\<circ>\<lparr>\<NN>\<rparr> =
      (\<lambda>\<NN>\<in>\<^sub>\<circ>these_ntcfs \<alpha> (op_cat \<BB> \<times>\<^sub>C \<CC>) (cat_Set \<alpha>) ?H\<GG> ?H\<FF>. ?aYa \<NN>)\<lparr>\<NN>\<rparr>"
    proof
      (
        intro aYm.v11_vconverse_app, 
        unfold beta[OF \<NN>] af_Yoneda_map_vdomain[OF assms] these_ntcfs_iff
      )
      from prems show \<NN>_def: "?aYm\<lparr>?aYa \<NN>\<rparr> = \<NN>" 
        by (cs_concl cs_simp: cat_cs_simps)
      show "?aYa \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
        by (rule cat_af_Yoneda_arrow_is_ntcf[OF assms prems])
    qed
  qed simp_all

qed


subsubsection\<open>Inverse of the Yoneda map for arbitrary functors\<close>

lemma (in category) inv_af_Yoneda_map_v11: 
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "v11 ((af_Yoneda_map \<alpha> \<FF> \<GG>)\<inverse>\<^sub>\<circ>)"
  using cat_af_Yoneda_Lemma(1)[OF assms] by (simp add: v11.v11_vconverse)

lemma (in category) inv_af_Yoneda_map_vdomain: 
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> ((af_Yoneda_map \<alpha> \<FF> \<GG>)\<inverse>\<^sub>\<circ>) =
    these_ntcfs \<alpha> (op_cat \<BB> \<times>\<^sub>C \<CC>) (cat_Set \<alpha>) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-) Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)"
  unfolding cat_af_Yoneda_Lemma(3)[OF assms] by simp

lemmas [cat_cs_simps] = category.inv_af_Yoneda_map_vdomain

lemma (in category) inv_af_Yoneda_map_app: 
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-) \<mapsto>\<^sub>C\<^sub>F  Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-) :
      op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "(af_Yoneda_map \<alpha> \<FF> \<GG>)\<inverse>\<^sub>\<circ>\<lparr>\<NN>\<rparr> = af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN>"
  using assms(3) unfolding cat_af_Yoneda_Lemma(3)[OF assms(1,2)] by simp

lemmas [cat_cs_simps] = category.inv_af_Yoneda_map_app

lemma (in category) inv_af_Yoneda_map_vrange: 
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<R>\<^sub>\<circ> ((af_Yoneda_map \<alpha> \<FF> \<GG>)\<inverse>\<^sub>\<circ>) = these_ntcfs \<alpha> \<BB> \<CC> \<FF> \<GG>"
proof-
  interpret \<FF>: is_functor \<alpha> \<BB> \<CC> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(2))
  from assms show ?thesis 
    unfolding af_Yoneda_map_def by (simp add: cat_cs_simps)
qed


subsubsection\<open>Yoneda map for arbitrary functors and natural isomorphisms\<close>


text\<open>
The following lemmas correspond to variants of the elements of
Lemma 3 in subsection 1.15 in \cite{bodo_categories_1970}.
\<close>

lemma (in category) cat_ntcf_lcomp_Hom_is_iso_ntcf_if_is_iso_ntcf:
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-) :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-) :
    op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
proof-
  interpret \<phi>: is_iso_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<phi> by (rule assms(1))
  show ?thesis
  proof(intro cat_ntcf_lcomp_Hom_if_ntcf_Hom_snd_is_iso_ntcf)
    fix b assume "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    then show "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<phi>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>,-) :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) :
      \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      by 
        (
          auto intro!: 
            cat_is_arr_isomorphism_ntcf_Hom_snd_is_iso_ntcf cat_arrow_cs_intros
        )
  qed (auto simp: cat_cs_intros)
qed

lemma (in category) cat_ntcf_lcomp_Hom_is_iso_ntcf_if_is_iso_ntcf':
  assumes "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<beta> = \<alpha>"
    and "\<GG>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-)"
    and "\<FF>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)"
    and "\<BB>' = op_cat \<BB> \<times>\<^sub>C \<CC>"
    and "\<CC>' = cat_Set \<alpha>"
  shows "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(\<phi>-,-) : \<GG>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF>' : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> \<CC>'"
  using assms(1)
  unfolding assms(2-6) 
  by (rule cat_ntcf_lcomp_Hom_is_iso_ntcf_if_is_iso_ntcf)

lemmas [cat_cs_intros] = 
  category.cat_ntcf_lcomp_Hom_is_iso_ntcf_if_is_iso_ntcf'

lemma (in category) cat_aYa_is_iso_ntcf_if_ntcf_lcomp_Hom_is_iso_ntcf:
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-) :
      op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
  shows "af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  
  let ?aYa = \<open>af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN>\<close>
  
  interpret \<FF>: is_functor \<alpha> \<BB> \<CC> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(2))
  interpret \<NN>: is_iso_ntcf 
    \<alpha> \<open>op_cat \<BB> \<times>\<^sub>C \<CC>\<close> \<open>cat_Set \<alpha>\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-)\<close> \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)\<close> \<NN>
    by (rule assms(3))

  from assms(1,2) \<NN>.is_ntcf_axioms have \<NN>_def: "\<NN> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(?aYa-,-)" 
    by (cs_concl cs_simp: cat_af_Yoneda_map_af_Yoneda_arrow_app[symmetric])

  from category_axioms assms have aYa: "?aYa : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: cat_cs_intros)
  have Hom_aYa: "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>(?aYa-,-) :
    Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-) :
    op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (auto intro: assms(3) simp add: \<NN>_def[symmetric])
  have Hb:
    "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(?aYa\<lparr>NTMap\<rparr>\<lparr>b\<rparr>,-) :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-) :
      \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    if "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" for b
    by 
      ( 
        rule cat_ntcf_Hom_snd_if_ntcf_lcomp_Hom_is_iso_ntcf[
          OF aYa Hom_aYa that
          ]
      )

  show ?thesis
  proof(intro is_iso_ntcfI)
    from category_axioms assms show 
      "af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    fix b assume prems: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    then have \<GG>b: "\<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and \<FF>b: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
      by (auto intro: cat_cs_intros)
    from assms(1,2) aYa prems have aYa_b: 
      "?aYa\<lparr>NTMap\<rparr>\<lparr>b\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      by (cs_concl cs_intro: cat_cs_intros cs_simp: cat_cs_simps)
    show "af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN>\<lparr>NTMap\<rparr>\<lparr>b\<rparr> : \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      by 
        (
          rule cat_is_arr_isomorphism_if_ntcf_Hom_snd_is_iso_ntcf[
            OF aYa_b Hb[OF prems]
            ]
        )
  qed

qed

lemma (in category) cat_aYa_is_iso_ntcf_if_ntcf_lcomp_Hom_is_iso_ntcf':
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> :
      Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-) :
      op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    and "\<beta> = \<alpha>"
    and "\<FF>' = \<FF>"
    and "\<GG>' = \<GG>"
  shows "af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN> : \<FF>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG>' : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1-3) 
  unfolding assms(4-6) 
  by (rule cat_aYa_is_iso_ntcf_if_ntcf_lcomp_Hom_is_iso_ntcf)

lemmas [cat_cs_intros] = 
  category.cat_aYa_is_iso_ntcf_if_ntcf_lcomp_Hom_is_iso_ntcf'

lemma (in category) cat_iso_functor_if_cf_lcomp_Hom_iso_functor:
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-) \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-)"
  shows "\<FF> \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> \<GG>"
proof-
  let ?H\<GG> = \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-)\<close>
    and ?H\<FF> = \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)\<close>
    and ?aYa = \<open>\<lambda>\<NN>. af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN>\<close>
  interpret \<FF>: is_functor \<alpha> \<BB> \<CC> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(2))
  from assms(3) obtain \<NN> \<AA> \<DD> where \<NN>: "\<NN> : ?H\<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o ?H\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    by auto
  interpret \<NN>: is_iso_ntcf \<alpha> \<AA> \<DD> ?H\<FF> ?H\<GG> \<NN> by (rule \<NN>)
  from category_axioms assms have "?H\<FF> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  then have \<AA>_def: "\<AA> = op_cat \<BB> \<times>\<^sub>C \<CC>" and \<DD>_def: "\<DD> = cat_Set \<alpha>"
    by (force simp: cat_cs_simps)+
  note \<NN> = \<NN>[unfolded \<AA>_def \<DD>_def]
  from \<NN> have "\<NN> : ?H\<FF> \<mapsto>\<^sub>C\<^sub>F ?H\<GG> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros ntcf_cs_intros)
  from category_axioms assms \<NN> have 
    "af_Yoneda_arrow \<alpha> \<GG> \<FF> \<NN> : \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  then have "\<GG> \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> \<FF>" by (clarsimp intro!: iso_functorI)
  then show ?thesis by (rule iso_functor_sym)
qed

lemma (in category) cat_cf_lcomp_Hom_iso_functor_if_iso_functor:
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<FF> \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> \<GG>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-) \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-)"
proof-
  let ?H\<GG> = \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<GG>-,-)\<close>
    and ?H\<FF> = \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-)\<close>
    and ?aYa = \<open>\<lambda>\<NN>. af_Yoneda_arrow \<alpha> \<FF> \<GG> \<NN>\<close>
  interpret \<FF>: is_functor \<alpha> \<BB> \<CC> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(2))
  from assms obtain \<BB>' \<CC>' \<phi> where \<phi>: "\<phi> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>'"
    by auto
  interpret \<phi>: is_iso_ntcf \<alpha> \<BB>' \<CC>' \<FF> \<GG> \<phi> by (rule \<phi>)
  from assms \<phi>.NTDom.is_functor_axioms 
  have \<BB>'_def: "\<BB>' = \<BB>" and \<CC>'_def: "\<CC>' = \<CC>" 
    by fast+
  note \<phi> = \<phi>[unfolded \<BB>'_def \<CC>'_def]
  show ?thesis
    by (rule iso_functor_sym) 
      (
        intro iso_functorI[
          OF cat_ntcf_lcomp_Hom_is_iso_ntcf_if_is_iso_ntcf[OF \<phi>]
          ]
      )
qed

lemma (in category) cat_cf_lcomp_Hom_iso_functor_if_iso_functor':
  assumes "\<FF> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<FF> \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> \<GG>"
    and "\<alpha>' = \<alpha>"
    and "\<CC>' = \<CC>"
  shows "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(\<FF>-,-) \<approx>\<^sub>C\<^sub>F\<^bsub>\<alpha>\<^esub> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>'\<^esub>\<CC>'(\<GG>-,-)"
  using assms(1-3) 
  unfolding assms(4,5) 
  by (rule cat_cf_lcomp_Hom_iso_functor_if_iso_functor)

lemmas [cat_cs_intros] = 
  category.cat_cf_lcomp_Hom_iso_functor_if_iso_functor'



subsection\<open>The Yoneda Functor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter III-2 in \cite{mac_lane_categories_2010}.\<close>


definition Yoneda_functor :: "V \<Rightarrow> V \<Rightarrow> V"
  where "Yoneda_functor \<alpha> \<DD> =
    [
      (\<lambda>r\<in>\<^sub>\<circ>op_cat \<DD>\<lparr>Obj\<rparr>. cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(r,-))),
      (\<lambda>f\<in>\<^sub>\<circ>op_cat \<DD>\<lparr>Arr\<rparr>. ntcf_arrow (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(f,-))),
      op_cat \<DD>,
      cat_FUNCT \<alpha> \<DD> (cat_Set \<alpha>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma Yoneda_functor_components: 
  shows "Yoneda_functor \<alpha> \<DD>\<lparr>ObjMap\<rparr> =
      (\<lambda>r\<in>\<^sub>\<circ>op_cat \<DD>\<lparr>Obj\<rparr>. cf_map (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(r,-)))"
    and "Yoneda_functor \<alpha> \<DD>\<lparr>ArrMap\<rparr> =
      (\<lambda>f\<in>\<^sub>\<circ>op_cat \<DD>\<lparr>Arr\<rparr>. ntcf_arrow (Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<DD>(f,-)))"
    and "Yoneda_functor \<alpha> \<DD>\<lparr>HomDom\<rparr> = op_cat \<DD>"
    and "Yoneda_functor \<alpha> \<DD>\<lparr>HomCod\<rparr> = cat_FUNCT \<alpha> \<DD> (cat_Set \<alpha>)"
  unfolding Yoneda_functor_def dghm_field_simps 
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

mk_VLambda Yoneda_functor_components(1)
  |vsv Yoneda_functor_ObjMap_vsv[cat_cs_intros]|
  |vdomain Yoneda_functor_ObjMap_vdomain[cat_cs_simps]|
  |app Yoneda_functor_ObjMap_app[cat_cs_simps]|

lemma (in category) Yoneda_functor_ObjMap_vrange:
  "\<R>\<^sub>\<circ> (Yoneda_functor \<alpha> \<CC>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)\<lparr>Obj\<rparr>"
proof
  (
    unfold Yoneda_functor_components, 
    rule vrange_VLambda_vsubset, 
    unfold cat_op_simps
  )
  fix c assume "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  with category_axioms show 
    "cf_map Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(c,-) \<in>\<^sub>\<circ> cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)\<lparr>Obj\<rparr>" 
    unfolding cat_op_simps cat_FUNCT_components
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
qed


subsubsection\<open>Arrow map\<close>

mk_VLambda Yoneda_functor_components(2)
  |vsv Yoneda_functor_ArrMap_vsv[cat_cs_intros]|
  |vdomain Yoneda_functor_ArrMap_vdomain[cat_cs_simps]|
  |app Yoneda_functor_ArrMap_app[cat_cs_simps]|

lemma (in category) Yoneda_functor_ArrMap_vrange:
  "\<R>\<^sub>\<circ> (Yoneda_functor \<alpha> \<CC>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)\<lparr>Arr\<rparr>"
proof
  (
    unfold Yoneda_functor_components, 
    rule vrange_VLambda_vsubset, 
    unfold cat_op_simps
  )
  fix f assume "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  then obtain a b where f: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" by auto
  define \<beta> where "\<beta> = \<alpha> + \<omega>"
  have \<Z>\<beta>: "\<Z> \<beta>" and \<alpha>\<beta>: "\<alpha> \<in>\<^sub>\<circ> \<beta>"
    by (simp_all add: \<Z>_\<alpha>_\<alpha>\<omega> \<Z>.intro \<Z>_Limit_\<alpha>\<omega> \<Z>_\<omega>_\<alpha>\<omega> \<beta>_def)
  from tiny_category_cat_FUNCT category_axioms \<Z>\<beta> \<alpha>\<beta> f show
    "ntcf_arrow Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-) \<in>\<^sub>\<circ> cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)\<lparr>Arr\<rparr>" 
    unfolding cat_op_simps
    by (cs_concl cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
qed


subsubsection\<open>The Yoneda Functor is a fully faithful functor\<close>

lemma (in category) cat_Yoneda_functor_is_functor:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "Yoneda_functor \<alpha> \<CC> : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>f\<^sub>f\<^bsub>\<beta>\<^esub> cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)"
proof
  (
    intro 
      is_ff_functorI 
      is_ft_functorI' 
      is_fl_functorI' 
      vsubset_antisym 
      vsubsetI,
    unfold cat_op_simps in_Hom_iff, 
    tactic\<open>distinct_subgoals_tac\<close>
  )

  interpret Set: category \<alpha> \<open>cat_Set \<alpha>\<close> by (rule category_cat_Set)

  let ?Yf = \<open>Yoneda_functor \<alpha> \<CC>\<close> and ?FUNCT = \<open>cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)\<close>

  show Yf: "?Yf : op_cat \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> ?FUNCT"
  proof(intro is_functorI')
    show "vfsequence ?Yf" unfolding Yoneda_functor_def by simp
    from assms have "category \<beta> \<CC>" by (intro cat_category_if_ge_Limit)
    then show "category \<beta> (op_cat \<CC>)" by (intro category.category_op)
    from assms show "category \<beta> ?FUNCT" 
      by (cs_concl cs_intro: cat_small_cs_intros tiny_category_cat_FUNCT)
    show "vcard ?Yf = 4\<^sub>\<nat>"
      unfolding Yoneda_functor_def by (simp add: nat_omega_simps)
    show "\<R>\<^sub>\<circ> (?Yf\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> ?FUNCT\<lparr>Obj\<rparr>" 
      by (rule Yoneda_functor_ObjMap_vrange)
    show "?Yf\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : ?Yf\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)\<^esub> ?Yf\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      if "f : a \<mapsto>\<^bsub>op_cat \<CC>\<^esub> b" for a b f
      using that category_axioms
      unfolding cat_op_simps
      by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros cat_FUNCT_cs_intros)
    show "?Yf\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f\<rparr> = 
      ?Yf\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>?FUNCT\<^esub> ?Yf\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      if "g : b \<mapsto>\<^bsub>op_cat \<CC>\<^esub> c" and "f : a \<mapsto>\<^bsub>op_cat \<CC>\<^esub> b" for b c g a f
      using that category_axioms
      unfolding cat_op_simps
      by 
        (
          cs_concl
            cs_simp: cat_cs_simps cat_op_simps cat_FUNCT_cs_simps 
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
    show "?Yf\<lparr>ArrMap\<rparr>\<lparr>op_cat \<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = ?FUNCT\<lparr>CId\<rparr>\<lparr>?Yf\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
      if "c \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>" for c 
      using that category_axioms
      unfolding cat_op_simps
      by 
        (
          cs_concl
            cs_simp: cat_cs_simps cat_op_simps cat_FUNCT_cs_simps 
            cs_intro: cat_cs_intros cat_FUNCT_cs_intros
        )
  qed (auto simp: assms(1) Yoneda_functor_components \<Z>.intro \<Z>_Limit_\<alpha>\<omega> \<Z>_\<omega>_\<alpha>\<omega>)

  interpret Yf: is_functor \<beta> \<open>op_cat \<CC>\<close> \<open>?FUNCT\<close> \<open>?Yf\<close> by (rule Yf)

  show "v11 (?Yf\<lparr>ArrMap\<rparr> \<restriction>\<^sup>l\<^sub>\<circ> Hom \<CC> b a)"
    if "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for a b
  proof-
    from that have dom_Y_ba: "\<D>\<^sub>\<circ> (?Yf\<lparr>ArrMap\<rparr> \<restriction>\<^sup>l\<^sub>\<circ> Hom \<CC> b a) = Hom \<CC> b a"
      by 
        (
          fastforce simp: 
            cat_op_simps 
            in_Hom_iff vdomain_vlrestriction Yoneda_functor_components
        )

    show "v11 (?Yf\<lparr>ArrMap\<rparr> \<restriction>\<^sup>l\<^sub>\<circ> Hom \<CC> b a)"
    proof(intro vsv.vsv_valeq_v11I, unfold dom_Y_ba in_Hom_iff)
      fix g f assume prems:
        "g : b \<mapsto>\<^bsub>\<CC>\<^esub> a" 
        "f : b \<mapsto>\<^bsub>\<CC>\<^esub> a" 
        "(?Yf\<lparr>ArrMap\<rparr> \<restriction>\<^sup>l\<^sub>\<circ> Hom \<CC> b a)\<lparr>g\<rparr> = (?Yf\<lparr>ArrMap\<rparr> \<restriction>\<^sup>l\<^sub>\<circ> Hom \<CC> b a)\<lparr>f\<rparr>"
      from 
        prems(3) category_axioms prems(1,2) Yoneda_functor_ArrMap_vsv[of \<alpha> \<CC>] 
      have "Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(g,-) = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)"
        by 
          (
            cs_prems
              cs_simp: V_cs_simps cat_cs_simps cat_op_simps cat_FUNCT_cs_simps
              cs_intro: cat_cs_intros
          )
      from this prems(1,2) show "g = f" by (rule cat_ntcf_Hom_snd_inj)
    qed (auto simp: Yoneda_functor_components)
  qed

  fix a b assume prems: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  show "\<NN> : ?Yf\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)\<^esub> ?Yf\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    if "\<NN> \<in>\<^sub>\<circ> ?Yf\<lparr>ArrMap\<rparr> `\<^sub>\<circ> Hom \<CC> b a" for \<NN>
  proof-
    from that obtain f where "?Yf\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<NN>" and f: "f : b \<mapsto>\<^bsub>\<CC>\<^esub> a"
      by (force elim!: Yf.ArrMap.vsv_vimageE)
    then have \<NN>_def: "\<NN> = ntcf_arrow Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)"
      unfolding 
        Yoneda_functor_ArrMap_app[
          unfolded cat_op_simps, OF cat_is_arrD(1)[OF f]
          ]
      by (simp add: cat_cs_simps cat_op_simps cat_cs_intros)
    from category_axioms f show ?thesis
      unfolding \<NN>_def
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps 
            cs_intro: cat_cs_intros cat_op_intros cat_FUNCT_cs_intros
        )
  qed
  show "\<NN> \<in>\<^sub>\<circ> ?Yf\<lparr>ArrMap\<rparr> `\<^sub>\<circ> Hom \<CC> b a"
    if "\<NN> : ?Yf\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>cat_FUNCT \<alpha> \<CC> (cat_Set \<alpha>)\<^esub> ?Yf\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>" for \<NN>
  proof-
    note \<NN> = cat_FUNCT_is_arrD[OF that]
    from \<NN>(1) category_axioms prems have ntcf_\<NN>:
      "ntcf_of_ntcf_arrow \<CC> (cat_Set \<alpha>) \<NN> : 
        Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(a,-) \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(b,-) : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
      by (subst (asm) \<NN>(3), use nothing in \<open>subst (asm) \<NN>(4)\<close>)
        (
          cs_prems 
            cs_simp: cat_cs_simps cat_FUNCT_cs_simps 
            cs_intro: cat_cs_intros cat_op_intros cat_FUNCT_cs_intros
        )
    from cat_ntcf_Hom_snd_is_ntcf_Hom_snd_unique(1,2)[OF prems ntcf_\<NN>] obtain f 
      where f: "f : b \<mapsto>\<^bsub>\<CC>\<^esub> a" 
        and \<NN>_def: "ntcf_of_ntcf_arrow \<CC> (cat_Set \<alpha>) \<NN> = Hom\<^sub>A\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<CC>(f,-)"
      by auto
    from \<NN>(2) f show "\<NN> \<in>\<^sub>\<circ> Yoneda_functor \<alpha> \<CC>\<lparr>ArrMap\<rparr> `\<^sub>\<circ> Hom \<CC> b a"
      unfolding \<NN>_def
      by (intro Yf.ArrMap.vsv_vimage_eqI[of f]) 
        (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)+
  qed
qed

text\<open>\newpage\<close>

end