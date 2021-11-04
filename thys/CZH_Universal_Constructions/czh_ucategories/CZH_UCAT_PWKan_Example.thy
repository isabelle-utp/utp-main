(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Pointwise Kan extensions: application example\<close>
theory CZH_UCAT_PWKan_Example
  imports
    CZH_Elementary_Categories.CZH_ECAT_Ordinal
    CZH_UCAT_PWKan
begin



subsection\<open>Background\<close>


text\<open>
The application example presented in this section is based on 
Exercise 6.1.ii in \cite{riehl_category_2016}.
\<close>

(*TODO: is the explicit elimination rule necessary?*)
lemma cat_ordinal_2_is_arrE:
  assumes "f : a \<mapsto>\<^bsub>cat_ordinal (2\<^sub>\<nat>)\<^esub> b"
  obtains "f = [0, 0]\<^sub>\<circ>" and " a = 0" and "b = 0" 
    | "f = [0, 1\<^sub>\<nat>]\<^sub>\<circ>" and "a = 0" and "b = 1\<^sub>\<nat>"
    | "f = [1\<^sub>\<nat>, 1\<^sub>\<nat>]\<^sub>\<circ>" and "a = 1\<^sub>\<nat>" and "b = 1\<^sub>\<nat>"
  using cat_ordinal_is_arrD[OF assms] unfolding two by auto

(*TODO: is the explicit elimination rule necessary?*)
lemma cat_ordinal_3_is_arrE:
  assumes "f : a \<mapsto>\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> b"
  obtains "f = [0, 0]\<^sub>\<circ>" and " a = 0" and "b = 0" 
    | "f = [0, 1\<^sub>\<nat>]\<^sub>\<circ>" and "a = 0" and "b = 1\<^sub>\<nat>"
    | "f = [0, 2\<^sub>\<nat>]\<^sub>\<circ>" and "a = 0" and "b = 2\<^sub>\<nat>"
    | "f = [1\<^sub>\<nat>, 1\<^sub>\<nat>]\<^sub>\<circ>" and "a = 1\<^sub>\<nat>" and "b = 1\<^sub>\<nat>"
    | "f = [1\<^sub>\<nat>, 2\<^sub>\<nat>]\<^sub>\<circ>" and "a = 1\<^sub>\<nat>" and "b = 2\<^sub>\<nat>"
    | "f = [2\<^sub>\<nat>, 2\<^sub>\<nat>]\<^sub>\<circ>" and "a = 2\<^sub>\<nat>" and "b = 2\<^sub>\<nat>"
  using cat_ordinal_is_arrD[OF assms] unfolding three by auto

lemma 0123: "0 \<in>\<^sub>\<circ> 2\<^sub>\<nat>" "1\<^sub>\<nat> \<in>\<^sub>\<circ> 2\<^sub>\<nat>" "0 \<in>\<^sub>\<circ> 3\<^sub>\<nat>" "1\<^sub>\<nat> \<in>\<^sub>\<circ> 3\<^sub>\<nat>" "2\<^sub>\<nat> \<in>\<^sub>\<circ> 3\<^sub>\<nat>" by auto



subsection\<open>\<open>\<KK>23\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition \<KK>23 :: V
  where "\<KK>23 =
    [
      (\<lambda>a\<in>\<^sub>\<circ>cat_ordinal (2\<^sub>\<nat>)\<lparr>Obj\<rparr>. if a = 0 then 0 else 2\<^sub>\<nat>), 
      (
        \<lambda>f\<in>\<^sub>\<circ>cat_ordinal (2\<^sub>\<nat>)\<lparr>Arr\<rparr>.
         if f = [0, 0]\<^sub>\<circ> \<Rightarrow> [0, 0]\<^sub>\<circ>
          | f = [0, 1\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> [0, 2\<^sub>\<nat>]\<^sub>\<circ>
          | f = [1\<^sub>\<nat>, 1\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> [2\<^sub>\<nat>, 2\<^sub>\<nat>]\<^sub>\<circ>
          | otherwise \<Rightarrow> 0
      ), 
      cat_ordinal (2\<^sub>\<nat>),
      cat_ordinal (3\<^sub>\<nat>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma \<KK>23_components:
  shows "\<KK>23\<lparr>ObjMap\<rparr> = (\<lambda>a\<in>\<^sub>\<circ>cat_ordinal (2\<^sub>\<nat>)\<lparr>Obj\<rparr>. if a = 0 then 0 else 2\<^sub>\<nat>)"
    and "\<KK>23\<lparr>ArrMap\<rparr> =
      (
        \<lambda>f\<in>\<^sub>\<circ>cat_ordinal (2\<^sub>\<nat>)\<lparr>Arr\<rparr>.
         if f = [0, 0]\<^sub>\<circ> \<Rightarrow> [0, 0]\<^sub>\<circ>
          | f = [0, 1\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> [0, 2\<^sub>\<nat>]\<^sub>\<circ>
          | f = [1\<^sub>\<nat>, 1\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> [2\<^sub>\<nat>, 2\<^sub>\<nat>]\<^sub>\<circ>
          | otherwise \<Rightarrow> 0
      )"
    and [cat_Kan_cs_simps]: "\<KK>23\<lparr>HomDom\<rparr> = cat_ordinal (2\<^sub>\<nat>)"
    and [cat_Kan_cs_simps]: "\<KK>23\<lparr>HomCod\<rparr> = cat_ordinal (3\<^sub>\<nat>)"
  unfolding \<KK>23_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

mk_VLambda \<KK>23_components(1)
  |vsv \<KK>23_ObjMap_vsv[cat_Kan_cs_intros]|
  |vdomain \<KK>23_ObjMap_vdomain[cat_Kan_cs_simps]|
  |app \<KK>23_ObjMap_app|

lemma \<KK>23_ObjMap_app_0[cat_Kan_cs_simps]: 
  assumes "x = 0"
  shows "\<KK>23\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> = 0"
  by 
    (
      cs_concl 
        cs_simp: \<KK>23_ObjMap_app cat_ordinal_cs_simps V_cs_simps assms 
        cs_intro: nat_omega_intros
    )

lemma \<KK>23_ObjMap_app_1[cat_Kan_cs_simps]: 
  assumes "x = 1\<^sub>\<nat>"
  shows "\<KK>23\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> = 2\<^sub>\<nat>"
  by 
    (
      cs_concl 
        cs_simp: 
          cat_ordinal_cs_simps V_cs_simps omega_of_set \<KK>23_ObjMap_app assms
        cs_intro: nat_omega_intros V_cs_intros
    )


subsubsection\<open>Arrow map\<close>

mk_VLambda \<KK>23_components(2)
  |vsv \<KK>23_ArrMap_vsv[cat_Kan_cs_intros]|
  |vdomain \<KK>23_ArrMap_vdomain[cat_Kan_cs_simps]|
  |app \<KK>23_ArrMap_app|

lemma \<KK>23_ArrMap_app_00[cat_Kan_cs_simps]: 
  assumes "f = [0, 0]\<^sub>\<circ>"
  shows "\<KK>23\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = [0, 0]\<^sub>\<circ>"
  unfolding assms
  by 
    (
      cs_concl 
        cs_simp: \<KK>23_ArrMap_app cat_ordinal_cs_simps V_cs_simps 
        cs_intro: cat_ordinal_cs_intros nat_omega_intros
    )

lemma \<KK>23_ArrMap_app_01[cat_Kan_cs_simps]: 
  assumes "f = [0, 1\<^sub>\<nat>]\<^sub>\<circ>"
  shows "\<KK>23\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = [0, 2\<^sub>\<nat>]\<^sub>\<circ>"
proof-
  have "[0, 1\<^sub>\<nat>]\<^sub>\<circ> \<in>\<^sub>\<circ> ordinal_arrs (2\<^sub>\<nat>)"
    by 
      (
        cs_concl 
          cs_simp: omega_of_set 
          cs_intro: cat_ordinal_cs_intros V_cs_intros nat_omega_intros
      )
  then show ?thesis
    unfolding assms by (simp add: \<KK>23_components cat_ordinal_components)
qed

lemma \<KK>23_ArrMap_app_11[cat_Kan_cs_simps]: 
  assumes "f = [1\<^sub>\<nat>, 1\<^sub>\<nat>]\<^sub>\<circ>"
  shows "\<KK>23\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = [2\<^sub>\<nat>, 2\<^sub>\<nat>]\<^sub>\<circ>"
proof-
  have "[1\<^sub>\<nat>, 1\<^sub>\<nat>]\<^sub>\<circ> \<in>\<^sub>\<circ> ordinal_arrs (2\<^sub>\<nat>)"
    by 
      (
        cs_concl 
          cs_simp: omega_of_set 
          cs_intro: cat_ordinal_cs_intros V_cs_intros nat_omega_intros
      )
  then show ?thesis
    unfolding assms by (simp add: \<KK>23_components cat_ordinal_components)
qed


subsubsection\<open>\<open>\<KK>23\<close> is a tiny functor\<close>

lemma (in \<Z>) \<KK>23_is_functor: "\<KK>23 : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_ordinal (3\<^sub>\<nat>)"
proof-

  from ord_of_nat_\<omega> interpret cat_ordinal_2: finite_category \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close>
    by (cs_concl cs_intro: cat_ordinal_cs_intros)
  from ord_of_nat_\<omega> interpret cat_ordinal_3: finite_category \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close>
    by (cs_concl cs_intro: cat_ordinal_cs_intros)

  show ?thesis
  proof(intro is_tiny_functorI' is_functorI')

    show "vfsequence \<KK>23" unfolding \<KK>23_def by auto
    show "vcard \<KK>23 = 4\<^sub>\<nat>" unfolding \<KK>23_def by (simp add: nat_omega_simps)

    show "\<R>\<^sub>\<circ> (\<KK>23\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Obj\<rparr>"
    proof
      (
        rule vsv.vsv_vrange_vsubset, 
        unfold cat_Kan_cs_simps cat_ordinal_cs_simps, 
        intro cat_Kan_cs_intros
      )
      fix x assume "x \<in>\<^sub>\<circ> 2\<^sub>\<nat>"
      then consider \<open>x = 0\<close> | \<open>x = 1\<^sub>\<nat>\<close> unfolding two by auto
      then show "\<KK>23\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> \<in>\<^sub>\<circ> 3\<^sub>\<nat>"
        by (cases, use nothing in \<open>simp_all only:\<close>)
          (
            cs_concl 
              cs_simp: cat_Kan_cs_simps omega_of_set cs_intro: nat_omega_intros
          )+
    qed

    show "\<KK>23\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : \<KK>23\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> \<KK>23\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      if "f : a \<mapsto>\<^bsub>cat_ordinal (2\<^sub>\<nat>)\<^esub> b" for a b f
      using that 
      by (elim cat_ordinal_2_is_arrE; simp only:) 
        (
          cs_concl
            cs_simp: omega_of_set cat_Kan_cs_simps
            cs_intro: nat_omega_intros V_cs_intros cat_ordinal_cs_intros
        )

    show 
      "\<KK>23\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>cat_ordinal (2\<^sub>\<nat>)\<^esub> f\<rparr> =
        \<KK>23\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> \<KK>23\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      if "g : b \<mapsto>\<^bsub>cat_ordinal (2\<^sub>\<nat>)\<^esub> c" and "f : a \<mapsto>\<^bsub>cat_ordinal (2\<^sub>\<nat>)\<^esub> b"
      for b c g a f 
    proof-
      have "0 \<in>\<^sub>\<circ> 3\<^sub>\<nat>" "1\<^sub>\<nat> \<in>\<^sub>\<circ> 3\<^sub>\<nat>" "2\<^sub>\<nat> \<in>\<^sub>\<circ> 3\<^sub>\<nat>" by auto
      then show ?thesis
        using that
        by (elim cat_ordinal_2_is_arrE; simp only:)
          (
            cs_concl 
              cs_simp: cat_ordinal_cs_simps cat_Kan_cs_simps  
              cs_intro: V_cs_intros cat_ordinal_cs_intros
          )+    
    qed

    show 
      "\<KK>23\<lparr>ArrMap\<rparr>\<lparr>cat_ordinal (2\<^sub>\<nat>)\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> =
        cat_ordinal (3\<^sub>\<nat>)\<lparr>CId\<rparr>\<lparr>\<KK>23\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
      if "c \<in>\<^sub>\<circ> cat_ordinal (2\<^sub>\<nat>)\<lparr>Obj\<rparr>" for c
    proof-
      from that consider \<open>c = 0\<close> | \<open>c = 1\<^sub>\<nat>\<close>
        unfolding cat_ordinal_components(1) two by auto
      then show ?thesis
        by (cases, use nothing in \<open>simp_all only:\<close>) 
          (
            cs_concl
              cs_simp: omega_of_set cat_Kan_cs_simps cat_ordinal_cs_simps  
              cs_intro: nat_omega_intros cat_ordinal_cs_intros
          )
    qed

  qed (auto intro!: cat_cs_intros simp: \<KK>23_components)

qed

lemma (in \<Z>) \<KK>23_is_functor'[cat_Kan_cs_intros]:
  assumes "\<AA>' = cat_ordinal (2\<^sub>\<nat>)"
    and "\<BB>' = cat_ordinal (3\<^sub>\<nat>)"
  shows "\<KK>23 : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule \<KK>23_is_functor)

lemmas [cat_Kan_cs_intros] = \<Z>.\<KK>23_is_functor'

lemma (in \<Z>) \<KK>23_is_tiny_functor: 
  "\<KK>23 : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> cat_ordinal (3\<^sub>\<nat>)"
proof-
  from ord_of_nat_\<omega> interpret cat_ordinal_2: finite_category \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close>
    by (cs_concl cs_intro: cat_ordinal_cs_intros)
  from ord_of_nat_\<omega> interpret cat_ordinal_3: finite_category \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close>
    by (cs_concl cs_intro: cat_ordinal_cs_intros)
  show ?thesis
    by (intro is_tiny_functorI' \<KK>23_is_functor)
      (auto intro!: cat_small_cs_intros)
qed

lemma (in \<Z>) \<KK>23_is_tiny_functor'[cat_Kan_cs_intros]:
  assumes "\<AA>' = cat_ordinal (2\<^sub>\<nat>)"
    and "\<BB>' = cat_ordinal (3\<^sub>\<nat>)"
  shows "\<KK>23 : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule \<KK>23_is_tiny_functor)

lemmas [cat_Kan_cs_intros] = \<Z>.\<KK>23_is_tiny_functor'



subsection\<open>
\<open>LK23\<close>: the functor associated with the left Kan extension along \<^const>\<open>\<KK>23\<close>
\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition LK23 :: "V \<Rightarrow> V"
  where "LK23 \<FF> =
    [
      (
        \<lambda>a\<in>\<^sub>\<circ>cat_ordinal (3\<^sub>\<nat>)\<lparr>Obj\<rparr>.
         if a = 0 \<Rightarrow> \<FF>\<lparr>ObjMap\<rparr>\<lparr>0\<rparr>
          | a = 1\<^sub>\<nat> \<Rightarrow> \<FF>\<lparr>ObjMap\<rparr>\<lparr>0\<rparr>
          | a = 2\<^sub>\<nat> \<Rightarrow> \<FF>\<lparr>ObjMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>
          | otherwise \<Rightarrow> \<FF>\<lparr>HomCod\<rparr>\<lparr>Obj\<rparr>
      ), 
      (
        \<lambda>f\<in>\<^sub>\<circ>cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>.
         if f = [0, 0]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 0\<rparr>\<^sub>\<bullet>
          | f = [0, 1\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 0\<rparr>\<^sub>\<bullet>
          | f = [0, 2\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>
          | f = [1\<^sub>\<nat>, 1\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 0\<rparr>\<^sub>\<bullet>
          | f = [1\<^sub>\<nat>, 2\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>
          | f = [2\<^sub>\<nat>, 2\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>1\<^sub>\<nat>, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>
          | otherwise \<Rightarrow> \<FF>\<lparr>HomCod\<rparr>\<lparr>Arr\<rparr>
      ), 
      cat_ordinal (3\<^sub>\<nat>),
      \<FF>\<lparr>HomCod\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma LK23_components:
  shows "LK23 \<FF>\<lparr>ObjMap\<rparr> =
    (
      \<lambda>a\<in>\<^sub>\<circ>cat_ordinal (3\<^sub>\<nat>)\<lparr>Obj\<rparr>.
        if a = 0 \<Rightarrow> \<FF>\<lparr>ObjMap\<rparr>\<lparr>0\<rparr>
         | a = 1\<^sub>\<nat> \<Rightarrow> \<FF>\<lparr>ObjMap\<rparr>\<lparr>0\<rparr>
         | a = 2\<^sub>\<nat> \<Rightarrow> \<FF>\<lparr>ObjMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>
         | otherwise \<Rightarrow> \<FF>\<lparr>HomCod\<rparr>\<lparr>Obj\<rparr>
    )"
    and "LK23 \<FF>\<lparr>ArrMap\<rparr> =
      (
        \<lambda>f\<in>\<^sub>\<circ>cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>.
         if f = [0, 0]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 0\<rparr>\<^sub>\<bullet>
          | f = [0, 1\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 0\<rparr>\<^sub>\<bullet>
          | f = [0, 2\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>
          | f = [1\<^sub>\<nat>, 1\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 0\<rparr>\<^sub>\<bullet>
          | f = [1\<^sub>\<nat>, 2\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>
          | f = [2\<^sub>\<nat>, 2\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>1\<^sub>\<nat>, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>
          | otherwise \<Rightarrow> \<FF>\<lparr>HomCod\<rparr>\<lparr>Arr\<rparr>
      )"
    and "LK23 \<FF>\<lparr>HomDom\<rparr> = cat_ordinal (3\<^sub>\<nat>)"
    and "LK23 \<FF>\<lparr>HomCod\<rparr> = \<FF>\<lparr>HomCod\<rparr>"
  unfolding LK23_def dghm_field_simps by (simp_all add: nat_omega_simps)

context is_functor
begin

lemmas LK23_components' = LK23_components[where \<FF>=\<FF>, unfolded cat_cs_simps]

lemmas [cat_Kan_cs_simps] = LK23_components'(3,4)

end

lemmas [cat_Kan_cs_simps] = is_functor.LK23_components'(3,4)


subsubsection\<open>Object map\<close>

mk_VLambda LK23_components(1)
  |vsv LK23_ObjMap_vsv[cat_Kan_cs_intros]|
  |vdomain LK23_ObjMap_vdomain[cat_Kan_cs_simps]|
  |app LK23_ObjMap_app|

lemma LK23_ObjMap_app_0[cat_Kan_cs_simps]:
  assumes "a = 0"
  shows "LK23 \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>0\<rparr>"
  unfolding LK23_components assms cat_ordinal_components by simp

lemma LK23_ObjMap_app_1[cat_Kan_cs_simps]:
  assumes "a = 1\<^sub>\<nat>"
  shows "LK23 \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>0\<rparr>"
  unfolding LK23_components assms cat_ordinal_components by simp

lemma LK23_ObjMap_app_2[cat_Kan_cs_simps]:
  assumes "a = 2\<^sub>\<nat>"
  shows "LK23 \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>"
  unfolding LK23_components assms cat_ordinal_components by simp


subsubsection\<open>Arrow map\<close>

mk_VLambda LK23_components(2)
  |vsv LK23_ArrMap_vsv[cat_Kan_cs_intros]|
  |vdomain LK23_ArrMap_vdomain[cat_Kan_cs_simps]|
  |app LK23_ArrMap_app|

lemma LK23_ArrMap_app_00[cat_Kan_cs_simps]:
  assumes "f = [0, 0]\<^sub>\<circ>"
  shows "LK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 0\<rparr>\<^sub>\<bullet>"
proof-
  from 0123 have f: "f \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>"
    by 
      (
        cs_concl cs_simp: cs_intro:
          V_cs_intros cat_ordinal_cs_intros cat_cs_intros assms
      )
  then show ?thesis unfolding LK23_components assms by auto
qed

lemma LK23_ArrMap_app_01[cat_Kan_cs_simps]:
  assumes "f = [0, 1\<^sub>\<nat>]\<^sub>\<circ>"
  shows "LK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 0\<rparr>\<^sub>\<bullet>"
proof-
  from 0123 have f: "f \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>"
    by 
      (
        cs_concl cs_simp: cs_intro:
          V_cs_intros cat_ordinal_cs_intros cat_cs_intros assms
      )
  then show ?thesis unfolding LK23_components assms by auto
qed

lemma LK23_ArrMap_app_02[cat_Kan_cs_simps]:
  assumes "f = [0, 2\<^sub>\<nat>]\<^sub>\<circ>"
  shows "LK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>"
proof-
  from 0123 have f: "f \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>"
    by 
      (
        cs_concl cs_simp: cs_intro:
          V_cs_intros cat_ordinal_cs_intros cat_cs_intros assms
      )
  then show ?thesis unfolding LK23_components assms by auto
qed

lemma LK23_ArrMap_app_11[cat_Kan_cs_simps]:
  assumes "f = [1\<^sub>\<nat>, 1\<^sub>\<nat>]\<^sub>\<circ>"
  shows "LK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 0\<rparr>\<^sub>\<bullet>"
proof-
  from 0123 have f: "f \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>"
    by 
      (
        cs_concl cs_simp: cs_intro:
          V_cs_intros cat_ordinal_cs_intros cat_cs_intros assms
      )
  then show ?thesis unfolding LK23_components assms by auto
qed

lemma LK23_ArrMap_app_12[cat_Kan_cs_simps]:
  assumes "f = [1\<^sub>\<nat>, 2\<^sub>\<nat>]\<^sub>\<circ>"
  shows "LK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>"
proof-
  from 0123 have f: "f \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>"
    by 
      (
        cs_concl 
          cs_simp: omega_of_set   
          cs_intro: nat_omega_intros cat_ordinal_cs_intros cat_cs_intros assms
      )
  then show ?thesis unfolding LK23_components assms by auto
qed

lemma LK23_ArrMap_app_22[cat_Kan_cs_simps]:
  assumes "f = [2\<^sub>\<nat>, 2\<^sub>\<nat>]\<^sub>\<circ>"
  shows "LK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>1\<^sub>\<nat>, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>"
proof-
  from 0123 have f: "f \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>"
    by 
      (
        cs_concl cs_simp: cs_intro: 
          nat_omega_intros cat_ordinal_cs_intros cat_cs_intros assms
      )
  then show ?thesis unfolding LK23_components assms by simp
qed


subsubsection\<open>\<open>LK23\<close> is a functor\<close>

lemma cat_LK23_is_functor:
  assumes "\<FF> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "LK23 \<FF> : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-

  interpret \<FF>: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<CC> \<FF> by (rule assms(1))

  from ord_of_nat_\<omega> interpret cat_ordinal_2: finite_category \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close>
    by (cs_concl cs_intro: cat_ordinal_cs_intros)
  from ord_of_nat_\<omega> interpret cat_ordinal_3: finite_category \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close>
    by (cs_concl cs_intro: cat_ordinal_cs_intros)

  interpret \<FF>: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<CC> \<FF> by (rule assms)

  show ?thesis
  proof(intro is_functorI')
    show "vfsequence (LK23 \<FF>)" unfolding LK23_def by auto
    show "vcard (LK23 \<FF>) = 4\<^sub>\<nat>" unfolding LK23_def by (simp add: nat_omega_simps)
    show "\<R>\<^sub>\<circ> (LK23 \<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    proof(rule vsv.vsv_vrange_vsubset, unfold cat_Kan_cs_simps)
      fix x assume prems: "x \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Obj\<rparr>"
      then consider \<open>x = 0\<close> | \<open>x = 1\<^sub>\<nat>\<close> | \<open>x = 2\<^sub>\<nat>\<close>
        unfolding cat_ordinal_cs_simps three by auto
      then show "LK23 \<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
        by cases
          (
            cs_concl 
              cs_simp: cat_Kan_cs_simps cat_ordinal_cs_simps omega_of_set 
              cs_intro: cat_cs_intros nat_omega_intros
          )+
    qed (cs_concl cs_intro: cat_Kan_cs_intros)
    show "LK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : LK23 \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> LK23 \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      if "f : a \<mapsto>\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> b" for a b f
    proof-
      from 0123 that show ?thesis
        by (elim cat_ordinal_3_is_arrE; simp only:)
          (
            cs_concl
              cs_simp: cat_Kan_cs_simps
              cs_intro: V_cs_intros cat_cs_intros cat_ordinal_cs_intros
          )+
    qed
    show 
      "LK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> f\<rparr> =
        LK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> LK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      if "g : b \<mapsto>\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> c" and "f : a \<mapsto>\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> b"
      for b c g a f
    proof-
      from 0123 that show ?thesis
        by (elim cat_ordinal_3_is_arrE; simp only:; (solves\<open>simp\<close>)?) (*slow*)
          (
            cs_concl 
              cs_simp: 
                cat_ordinal_cs_simps 
                cat_Kan_cs_simps 
                \<FF>.cf_ArrMap_Comp[symmetric]
              cs_intro: V_cs_intros cat_cs_intros cat_ordinal_cs_intros
          )+
    qed
    show "LK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>cat_ordinal (3\<^sub>\<nat>)\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>LK23 \<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
      if "c \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Obj\<rparr>" for c
    proof-
      from that consider \<open>c = 0\<close> | \<open>c = 1\<^sub>\<nat>\<close> | \<open>c = 2\<^sub>\<nat>\<close>
        unfolding cat_ordinal_components three by auto
      moreover have "0 \<in>\<^sub>\<circ> 2\<^sub>\<nat>" "1\<^sub>\<nat> \<in>\<^sub>\<circ> 2\<^sub>\<nat>" "0 \<in>\<^sub>\<circ> 3\<^sub>\<nat>" "1\<^sub>\<nat> \<in>\<^sub>\<circ> 3\<^sub>\<nat>" "2\<^sub>\<nat> \<in>\<^sub>\<circ> 3\<^sub>\<nat>" by auto
      ultimately show ?thesis
        by (cases, use nothing in \<open>simp_all only:\<close>)
          (
            cs_concl 
              cs_simp: 
                cat_ordinal_cs_simps 
                cat_Kan_cs_simps 
                is_functor.cf_ObjMap_CId[symmetric]  
              cs_intro: V_cs_intros cat_cs_intros cat_ordinal_cs_intros
          )+
    qed
  qed 
    (
      cs_concl
        cs_simp: cat_Kan_cs_simps cs_intro: cat_cs_intros cat_Kan_cs_intros
    )+

qed

lemma cat_LK23_is_functor'[cat_Kan_cs_intros]:
  assumes "\<FF> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<AA>' = cat_ordinal (3\<^sub>\<nat>)"
  shows "LK23 \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1) unfolding assms(2) by (rule cat_LK23_is_functor)


subsubsection\<open>The fundamental property of \<open>LK23\<close>\<close>

lemma cf_comp_LK23_\<KK>23[cat_Kan_cs_simps]: 
  assumes "\<FF> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "LK23 \<FF> \<circ>\<^sub>C\<^sub>F \<KK>23 = \<FF>"
proof-

  interpret \<FF>: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<CC> \<FF> by (rule assms(1))
  interpret \<KK>23: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<open>\<KK>23\<close>
    by (cs_concl cs_simp: cs_intro: cat_cs_intros cat_Kan_cs_intros)
  interpret LK23: is_functor \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<CC> \<open>LK23 \<FF>\<close>
    by (cs_concl cs_simp: cs_intro: cat_Kan_cs_intros cat_cs_intros)

  show ?thesis
  proof(rule cf_eqI)
    show "\<FF> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" by (rule assms)
    have ObjMap_dom_lhs: "\<D>\<^sub>\<circ> ((LK23 \<FF> \<circ>\<^sub>C\<^sub>F \<KK>23)\<lparr>ObjMap\<rparr>) = 2\<^sub>\<nat>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_ordinal_cs_simps cs_intro: cat_cs_intros
        )
    have ObjMap_dom_rhs: "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = 2\<^sub>\<nat>"
      by (cs_concl cs_simp: cat_cs_simps cat_ordinal_cs_simps)
    show "(LK23 \<FF> \<circ>\<^sub>C\<^sub>F \<KK>23)\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>"
    proof(rule vsv_eqI, unfold ObjMap_dom_lhs ObjMap_dom_rhs)
      fix a assume prems: "a \<in>\<^sub>\<circ> 2\<^sub>\<nat>"
      then consider \<open>a = 0\<close> | \<open>a = 1\<^sub>\<nat>\<close> by force
      then show "(LK23 \<FF> \<circ>\<^sub>C\<^sub>F \<KK>23)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        by (cases, use nothing in \<open>simp_all only:\<close>)
          (
            cs_concl
              cs_simp:
                omega_of_set cat_cs_simps cat_ordinal_cs_simps cat_Kan_cs_simps
              cs_intro: cat_cs_intros nat_omega_intros
          )+
    qed (cs_concl cs_simp: cs_intro: cat_cs_intros V_cs_intros)+
    have ArrMap_dom_lhs: "\<D>\<^sub>\<circ> ((LK23 \<FF> \<circ>\<^sub>C\<^sub>F \<KK>23)\<lparr>ArrMap\<rparr>) = cat_ordinal (2\<^sub>\<nat>)\<lparr>Arr\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    have ArrMap_dom_rhs: "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = cat_ordinal (2\<^sub>\<nat>)\<lparr>Arr\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    show "(LK23 \<FF> \<circ>\<^sub>C\<^sub>F \<KK>23)\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
    proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
      fix f assume prems: "f \<in>\<^sub>\<circ> cat_ordinal (2\<^sub>\<nat>)\<lparr>Arr\<rparr>"
      then obtain a b where "f : a \<mapsto>\<^bsub>cat_ordinal (2\<^sub>\<nat>)\<^esub> b" by auto
      then show "(LK23 \<FF> \<circ>\<^sub>C\<^sub>F \<KK>23)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
        by (elim cat_ordinal_2_is_arrE; simp only:)
          (
            cs_concl
              cs_simp: cat_cs_simps cat_Kan_cs_simps cs_intro: cat_cs_intros
          )+
    qed (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros V_cs_intros)+
  qed (cs_concl cs_simp: cs_intro: cat_Kan_cs_intros cat_cs_intros)

qed



subsection\<open>
\<open>RK23\<close>: the functor associated with the right Kan extension along \<^const>\<open>\<KK>23\<close>
\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition RK23 :: "V \<Rightarrow> V"
  where "RK23 \<FF> =
    [
      (
        \<lambda>a\<in>\<^sub>\<circ>cat_ordinal (3\<^sub>\<nat>)\<lparr>Obj\<rparr>.
         if a = 0 \<Rightarrow> \<FF>\<lparr>ObjMap\<rparr>\<lparr>0\<rparr>
          | a = 1\<^sub>\<nat> \<Rightarrow> \<FF>\<lparr>ObjMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>
          | a = 2\<^sub>\<nat> \<Rightarrow> \<FF>\<lparr>ObjMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>
          | otherwise \<Rightarrow> \<FF>\<lparr>HomCod\<rparr>\<lparr>Obj\<rparr>
      ),
      (
        \<lambda>f\<in>\<^sub>\<circ>cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>.
         if f = [0, 0]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 0\<rparr>\<^sub>\<bullet>
          | f = [0, 1\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>
          | f = [0, 2\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>
          | f = [1\<^sub>\<nat>, 1\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>1\<^sub>\<nat>, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>
          | f = [1\<^sub>\<nat>, 2\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>1\<^sub>\<nat>, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>
          | f = [2\<^sub>\<nat>, 2\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>1\<^sub>\<nat>, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>
          | otherwise \<Rightarrow> \<FF>\<lparr>HomCod\<rparr>\<lparr>Arr\<rparr>
      ), 
      cat_ordinal (3\<^sub>\<nat>),
      \<FF>\<lparr>HomCod\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma RK23_components:
  shows "RK23 \<FF>\<lparr>ObjMap\<rparr> =
    (
      \<lambda>a\<in>\<^sub>\<circ>cat_ordinal (3\<^sub>\<nat>)\<lparr>Obj\<rparr>.
        if a = 0 \<Rightarrow> \<FF>\<lparr>ObjMap\<rparr>\<lparr>0\<rparr>
         | a = 1\<^sub>\<nat> \<Rightarrow> \<FF>\<lparr>ObjMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>
         | a = 2\<^sub>\<nat> \<Rightarrow> \<FF>\<lparr>ObjMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>
         | otherwise \<Rightarrow> \<FF>\<lparr>HomCod\<rparr>\<lparr>Obj\<rparr>
    )"
    and "RK23 \<FF>\<lparr>ArrMap\<rparr> =
      (
        \<lambda>f\<in>\<^sub>\<circ>cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>.
         if f = [0, 0]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 0\<rparr>\<^sub>\<bullet>
          | f = [0, 1\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>
          | f = [0, 2\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>
          | f = [1\<^sub>\<nat>, 1\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>1\<^sub>\<nat>, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>
          | f = [1\<^sub>\<nat>, 2\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>1\<^sub>\<nat>, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>
          | f = [2\<^sub>\<nat>, 2\<^sub>\<nat>]\<^sub>\<circ> \<Rightarrow> \<FF>\<lparr>ArrMap\<rparr>\<lparr>1\<^sub>\<nat>, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>
          | otherwise \<Rightarrow> \<FF>\<lparr>HomCod\<rparr>\<lparr>Arr\<rparr>
      )"
    and "RK23 \<FF>\<lparr>HomDom\<rparr> = cat_ordinal (3\<^sub>\<nat>)"
    and "RK23 \<FF>\<lparr>HomCod\<rparr> = \<FF>\<lparr>HomCod\<rparr>"
  unfolding RK23_def dghm_field_simps by (simp_all add: nat_omega_simps)

context is_functor
begin

lemmas RK23_components' = RK23_components[where \<FF>=\<FF>, unfolded cat_cs_simps]

lemmas [cat_Kan_cs_simps] = RK23_components'(3,4)

end

lemmas [cat_Kan_cs_simps] = is_functor.RK23_components'(3,4)


subsubsection\<open>Object map\<close>

mk_VLambda RK23_components(1)
  |vsv RK23_ObjMap_vsv[cat_Kan_cs_intros]|
  |vdomain RK23_ObjMap_vdomain[cat_Kan_cs_simps]|
  |app RK23_ObjMap_app|

lemma RK23_ObjMap_app_0[cat_Kan_cs_simps]:
  assumes "a = 0"
  shows "RK23 \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>0\<rparr>"
  unfolding RK23_components assms cat_ordinal_components by simp

lemma RK23_ObjMap_app_1[cat_Kan_cs_simps]:
  assumes "a = 1\<^sub>\<nat>"
  shows "RK23 \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>"
  unfolding RK23_components assms cat_ordinal_components by simp

lemma RK23_ObjMap_app_2[cat_Kan_cs_simps]:
  assumes "a = 2\<^sub>\<nat>"
  shows "RK23 \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>"
  unfolding RK23_components assms cat_ordinal_components by simp


subsubsection\<open>Arrow map\<close>

mk_VLambda RK23_components(2)
  |vsv RK23_ArrMap_vsv[cat_Kan_cs_intros]|
  |vdomain RK23_ArrMap_vdomain[cat_Kan_cs_simps]|
  |app RK23_ArrMap_app|

lemma RK23_ArrMap_app_00[cat_Kan_cs_simps]:
  assumes "f = [0, 0]\<^sub>\<circ>"
  shows "RK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 0\<rparr>\<^sub>\<bullet>"
proof-
  from 0123 have f: "f \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>"
    by 
      (
        cs_concl cs_simp: cs_intro:
          V_cs_intros cat_ordinal_cs_intros cat_cs_intros assms
      )
  then show ?thesis unfolding RK23_components assms by auto
qed

lemma RK23_ArrMap_app_01[cat_Kan_cs_simps]:
  assumes "f = [0, 1\<^sub>\<nat>]\<^sub>\<circ>"
  shows "RK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>"
proof-
  from 0123 have f: "f \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>"
    by 
      (
        cs_concl cs_simp: cs_intro:
          V_cs_intros cat_ordinal_cs_intros cat_cs_intros assms
      )
  then show ?thesis unfolding RK23_components assms by auto
qed

lemma RK23_ArrMap_app_02[cat_Kan_cs_simps]:
  assumes "f = [0, 2\<^sub>\<nat>]\<^sub>\<circ>"
  shows "RK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>0, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>"
proof-
  from 0123 have f: "f \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>"
    by 
      (
        cs_concl cs_simp: cs_intro:
          V_cs_intros cat_ordinal_cs_intros cat_cs_intros assms
      )
  then show ?thesis unfolding RK23_components assms by auto
qed

lemma RK23_ArrMap_app_11[cat_Kan_cs_simps]:
  assumes "f = [1\<^sub>\<nat>, 1\<^sub>\<nat>]\<^sub>\<circ>"
  shows "RK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>1\<^sub>\<nat>, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>"
proof-
  from 0123 have f: "f \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>"
    by 
      (
        cs_concl cs_simp: cs_intro:
          V_cs_intros cat_ordinal_cs_intros cat_cs_intros assms
      )
  then show ?thesis unfolding RK23_components assms by auto
qed

lemma RK23_ArrMap_app_12[cat_Kan_cs_simps]:
  assumes "f = [1\<^sub>\<nat>, 2\<^sub>\<nat>]\<^sub>\<circ>"
  shows "RK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>1\<^sub>\<nat>, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>"
proof-
  from 0123 have f: "f \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>"
    by 
      (
        cs_concl 
          cs_simp: omega_of_set   
          cs_intro: nat_omega_intros cat_ordinal_cs_intros cat_cs_intros assms
      )
  then show ?thesis unfolding RK23_components assms by auto
qed

lemma RK23_ArrMap_app_22[cat_Kan_cs_simps]:
  assumes "f = [2\<^sub>\<nat>, 2\<^sub>\<nat>]\<^sub>\<circ>"
  shows "RK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>1\<^sub>\<nat>, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>"
proof-
  from 0123 have f: "f \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>"
    by 
      (
        cs_concl cs_simp: cs_intro: 
          nat_omega_intros cat_ordinal_cs_intros cat_cs_intros assms
      )
  then show ?thesis unfolding RK23_components assms by simp
qed


subsubsection\<open>\<open>RK23\<close> is a functor\<close>

lemma cat_RK23_is_functor:
  assumes "\<FF> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "RK23 \<FF> : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-

  interpret \<FF>: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<CC> \<FF> by (rule assms(1))

  from ord_of_nat_\<omega> interpret cat_ordinal_2: finite_category \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close>
    by (cs_concl cs_intro: cat_ordinal_cs_intros)
  from ord_of_nat_\<omega> interpret cat_ordinal_3: finite_category \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close>
    by (cs_concl cs_intro: cat_ordinal_cs_intros)

  interpret \<FF>: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<CC> \<FF> by (rule assms)

  show ?thesis
  proof(intro is_functorI')
    show "vfsequence (RK23 \<FF>)" unfolding RK23_def by auto
    show "vcard (RK23 \<FF>) = 4\<^sub>\<nat>" unfolding RK23_def by (simp add: nat_omega_simps)
    show "\<R>\<^sub>\<circ> (RK23 \<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    proof(rule vsv.vsv_vrange_vsubset, unfold cat_Kan_cs_simps)
      fix x assume prems: "x \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Obj\<rparr>"
      then consider \<open>x = 0\<close> | \<open>x = 1\<^sub>\<nat>\<close> | \<open>x = 2\<^sub>\<nat>\<close>
        unfolding cat_ordinal_cs_simps three by auto
      then show "RK23 \<FF>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
        by cases
          (
            cs_concl 
              cs_simp: cat_Kan_cs_simps cat_ordinal_cs_simps omega_of_set 
              cs_intro: cat_cs_intros nat_omega_intros
          )+
    qed (cs_concl cs_intro: cat_Kan_cs_intros)
    show "RK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : RK23 \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> RK23 \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      if "f : a \<mapsto>\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> b" for a b f
    proof-
      from 0123 that show ?thesis
        by (elim cat_ordinal_3_is_arrE; simp only:)
          (
            cs_concl
              cs_simp: cat_Kan_cs_simps
              cs_intro: V_cs_intros cat_cs_intros cat_ordinal_cs_intros
          )+
    qed
    show 
      "RK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> f\<rparr> =
        RK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> RK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      if "g : b \<mapsto>\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> c" and "f : a \<mapsto>\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> b"
      for b c g a f
      using 0123 that 
      by (elim cat_ordinal_3_is_arrE; simp only:; (solves\<open>simp\<close>)?) (*slow*)
        (
          cs_concl 
            cs_simp: 
              cat_ordinal_cs_simps 
              cat_Kan_cs_simps 
              \<FF>.cf_ArrMap_Comp[symmetric]
            cs_intro: V_cs_intros cat_cs_intros cat_ordinal_cs_intros
        )+
    show "RK23 \<FF>\<lparr>ArrMap\<rparr>\<lparr>cat_ordinal (3\<^sub>\<nat>)\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>RK23 \<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
      if "c \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Obj\<rparr>" for c
    proof-
      from that consider \<open>c = 0\<close> | \<open>c = 1\<^sub>\<nat>\<close> | \<open>c = 2\<^sub>\<nat>\<close>
        unfolding cat_ordinal_components three by auto
      then show ?thesis
        by (cases, use 0123 in \<open>simp_all only:\<close>)
          (
            cs_concl
              cs_simp: 
                cat_ordinal_cs_simps 
                cat_Kan_cs_simps 
                is_functor.cf_ObjMap_CId[symmetric]  
              cs_intro: V_cs_intros cat_cs_intros cat_ordinal_cs_intros
          )+
    qed
  qed 
    (
      cs_concl
        cs_simp: cat_Kan_cs_simps cs_intro: cat_cs_intros cat_Kan_cs_intros
    )+

qed

lemma cat_RK23_is_functor'[cat_Kan_cs_intros]:
  assumes "\<FF> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<AA>' = cat_ordinal (3\<^sub>\<nat>)"
  shows "RK23 \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1) unfolding assms(2) by (rule cat_RK23_is_functor)


subsubsection\<open>The fundamental property of \<open>RK23\<close>\<close>

lemma cf_comp_RK23_\<KK>23[cat_Kan_cs_simps]: 
  assumes "\<FF> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "RK23 \<FF> \<circ>\<^sub>C\<^sub>F \<KK>23 = \<FF>"
proof-

  interpret \<FF>: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<CC> \<FF> by (rule assms(1))
  interpret \<KK>23: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<open>\<KK>23\<close>
    by (cs_concl cs_simp: cs_intro: cat_cs_intros cat_Kan_cs_intros)
  interpret RK23: is_functor \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<CC> \<open>RK23 \<FF>\<close>
    by (cs_concl cs_simp: cs_intro: cat_Kan_cs_intros cat_cs_intros)

  show ?thesis
  proof(rule cf_eqI)
    show "\<FF> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" by (rule assms)
    have ObjMap_dom_lhs: "\<D>\<^sub>\<circ> ((RK23 \<FF> \<circ>\<^sub>C\<^sub>F \<KK>23)\<lparr>ObjMap\<rparr>) = 2\<^sub>\<nat>"
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_ordinal_cs_simps cs_intro: cat_cs_intros
        )
    have ObjMap_dom_rhs: "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = 2\<^sub>\<nat>"
      by (cs_concl cs_simp: cat_cs_simps cat_ordinal_cs_simps)
    show "(RK23 \<FF> \<circ>\<^sub>C\<^sub>F \<KK>23)\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>"
    proof(rule vsv_eqI, unfold ObjMap_dom_lhs ObjMap_dom_rhs)
      fix a assume prems: "a \<in>\<^sub>\<circ> 2\<^sub>\<nat>"
      then consider \<open>a = 0\<close> | \<open>a = 1\<^sub>\<nat>\<close> by force
      then show "(RK23 \<FF> \<circ>\<^sub>C\<^sub>F \<KK>23)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        by (cases, use nothing in \<open>simp_all only:\<close>)
          (
            cs_concl
              cs_simp:
                omega_of_set cat_cs_simps cat_ordinal_cs_simps cat_Kan_cs_simps
              cs_intro: cat_cs_intros nat_omega_intros
          )+
    qed (cs_concl cs_simp: cs_intro: cat_cs_intros V_cs_intros)+
    have ArrMap_dom_lhs: "\<D>\<^sub>\<circ> ((RK23 \<FF> \<circ>\<^sub>C\<^sub>F \<KK>23)\<lparr>ArrMap\<rparr>) = cat_ordinal (2\<^sub>\<nat>)\<lparr>Arr\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    have ArrMap_dom_rhs: "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = cat_ordinal (2\<^sub>\<nat>)\<lparr>Arr\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    show "(RK23 \<FF> \<circ>\<^sub>C\<^sub>F \<KK>23)\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
    proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
      fix f assume prems: "f \<in>\<^sub>\<circ> cat_ordinal (2\<^sub>\<nat>)\<lparr>Arr\<rparr>"
      then obtain a b where "f : a \<mapsto>\<^bsub>cat_ordinal (2\<^sub>\<nat>)\<^esub> b" by auto
      then show "(RK23 \<FF> \<circ>\<^sub>C\<^sub>F \<KK>23)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
        by (elim cat_ordinal_2_is_arrE; simp only:)
          (
            cs_concl
              cs_simp: cat_cs_simps cat_Kan_cs_simps cs_intro: cat_cs_intros
          )+
    qed (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros V_cs_intros)+
  qed (cs_concl cs_simp: cs_intro: cat_Kan_cs_intros cat_cs_intros)

qed



subsection\<open>
\<open>RK_\<sigma>23\<close>: towards the universal property of the right Kan extension along \<open>\<KK>23\<close>
\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition RK_\<sigma>23 :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "RK_\<sigma>23 \<TT> \<epsilon>' \<FF>' =
    [
      (
        \<lambda>a\<in>\<^sub>\<circ>cat_ordinal (3\<^sub>\<nat>)\<lparr>Obj\<rparr>.
         if a = 0 \<Rightarrow> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>0\<rparr>
          | a = 1\<^sub>\<nat> \<Rightarrow> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>\<TT>\<lparr>HomCod\<rparr>\<^esub> \<FF>'\<lparr>ArrMap\<rparr>\<lparr>1\<^sub>\<nat>, 2\<^sub>\<nat>\<rparr>\<^sub>\<bullet>
          | a = 2\<^sub>\<nat> \<Rightarrow> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>
          | otherwise \<Rightarrow> \<TT>\<lparr>HomCod\<rparr>\<lparr>Arr\<rparr>
      ),
      \<FF>',
      RK23 \<TT>,
      cat_ordinal (3\<^sub>\<nat>),
      \<FF>'\<lparr>HomCod\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma RK_\<sigma>23_components:
  shows "RK_\<sigma>23 \<TT> \<epsilon>' \<FF>'\<lparr>NTMap\<rparr> =
    (
      \<lambda>a\<in>\<^sub>\<circ>cat_ordinal (3\<^sub>\<nat>)\<lparr>Obj\<rparr>.
        if a = 0 \<Rightarrow> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>0\<rparr>
         | a = 1\<^sub>\<nat> \<Rightarrow> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>\<TT>\<lparr>HomCod\<rparr>\<^esub> \<FF>'\<lparr>ArrMap\<rparr>\<lparr>1\<^sub>\<nat>, 2\<^sub>\<nat>\<rparr>\<^sub>\<bullet>
         | a = 2\<^sub>\<nat> \<Rightarrow> \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>
         | otherwise \<Rightarrow> \<TT>\<lparr>HomCod\<rparr>\<lparr>Arr\<rparr>
    )"
    and "RK_\<sigma>23 \<TT> \<epsilon>' \<FF>'\<lparr>NTDom\<rparr> = \<FF>'"
    and "RK_\<sigma>23 \<TT> \<epsilon>' \<FF>'\<lparr>NTCod\<rparr> = RK23 \<TT>"
    and "RK_\<sigma>23 \<TT> \<epsilon>' \<FF>'\<lparr>NTDGDom\<rparr> = cat_ordinal (3\<^sub>\<nat>)"
    and "RK_\<sigma>23 \<TT> \<epsilon>' \<FF>'\<lparr>NTDGCod\<rparr> = \<FF>'\<lparr>HomCod\<rparr>"
  unfolding RK_\<sigma>23_def nt_field_simps by (simp_all add: nat_omega_simps)

context
  fixes \<alpha> \<AA> \<FF>' \<TT>  
  assumes \<FF>': "\<FF>' : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and \<TT>: "\<TT> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
begin

interpretation \<FF>': is_functor \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<AA> \<FF>' by (rule \<FF>')
interpretation \<TT>: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<AA> \<TT> by (rule \<TT>)

lemmas RK_\<sigma>23_components' = 
  RK_\<sigma>23_components[where \<FF>'=\<FF>' and \<TT>=\<TT>, unfolded cat_cs_simps]

lemmas [cat_Kan_cs_simps] = RK_\<sigma>23_components'(2-5)

end


subsubsection\<open>Natural transformation map\<close>

mk_VLambda RK_\<sigma>23_components(1)
  |vsv RK_\<sigma>23_NTMap_vsv[cat_Kan_cs_intros]|
  |vdomain RK_\<sigma>23_NTMap_vdomain[cat_Kan_cs_simps]|
  |app RK_\<sigma>23_NTMap_app|

lemma RK_\<sigma>23_NTMap_app_0[cat_Kan_cs_simps]:
  assumes "a = 0"
  shows "RK_\<sigma>23 \<TT> \<epsilon>' \<FF>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>0\<rparr>"
  using assms unfolding RK_\<sigma>23_components cat_ordinal_cs_simps by simp

lemma (in is_functor) RK_\<sigma>23_NTMap_app_1[cat_Kan_cs_simps]:
  assumes "a = 1\<^sub>\<nat>"
  shows "RK_\<sigma>23 \<FF> \<epsilon>' \<FF>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>'\<lparr>ArrMap\<rparr>\<lparr>1\<^sub>\<nat>, 2\<^sub>\<nat>\<rparr>\<^sub>\<bullet>"
  using assms 
  unfolding RK_\<sigma>23_components cat_ordinal_cs_simps cat_cs_simps 
  by simp

lemmas [cat_Kan_cs_simps] = is_functor.RK_\<sigma>23_NTMap_app_1

lemma RK_\<sigma>23_NTMap_app_2[cat_Kan_cs_simps]:
  assumes "a = 2\<^sub>\<nat>"
  shows "RK_\<sigma>23 \<TT> \<epsilon>' \<FF>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<epsilon>'\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>"
  using assms unfolding RK_\<sigma>23_components cat_ordinal_cs_simps by simp


subsubsection\<open>\<open>RK_\<sigma>23\<close> is a natural transformation\<close>

lemma RK_\<sigma>23_is_ntcf:
  assumes "\<FF>' : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
    and "\<TT> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<epsilon>' : \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>23 \<mapsto>\<^sub>C\<^sub>F \<TT> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "RK_\<sigma>23 \<TT> \<epsilon>' \<FF>' : \<FF>' \<mapsto>\<^sub>C\<^sub>F RK23 \<TT> : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
proof-
 
  interpret \<FF>': is_functor \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<AA> \<FF>' by (rule assms(1))
  interpret \<TT>: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<AA> \<TT> by (rule assms(2))
  interpret \<epsilon>': is_ntcf \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<AA> \<open>\<FF>' \<circ>\<^sub>C\<^sub>F \<KK>23\<close> \<TT> \<epsilon>' 
    by (rule assms(3))

  interpret \<KK>23: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<open>\<KK>23\<close>
    by (cs_concl cs_simp: cs_intro: cat_cs_intros cat_Kan_cs_intros)
  interpret RK23: is_functor \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<AA> \<open>RK23 \<TT>\<close>
    by (cs_concl cs_simp: cs_intro: cat_Kan_cs_intros cat_cs_intros)

  from 0123 have [cat_cs_simps]: "\<TT>\<lparr>ArrMap\<rparr>\<lparr>1\<^sub>\<nat>, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet> = \<AA>\<lparr>CId\<rparr>\<lparr>\<TT>\<lparr>ObjMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>\<rparr>"
    by 
      (
        cs_concl 
          cs_simp: cat_ordinal_cs_simps is_functor.cf_ObjMap_CId[symmetric] 
          cs_intro: cat_cs_intros
      )

  show ?thesis
  proof(rule is_ntcfI')
    show "vfsequence (RK_\<sigma>23 \<TT> \<epsilon>' \<FF>')" unfolding RK_\<sigma>23_def by simp
    show "vcard (RK_\<sigma>23 \<TT> \<epsilon>' \<FF>') = 5\<^sub>\<nat>"
      unfolding RK_\<sigma>23_def by (simp_all add: nat_omega_simps)
    show "RK_\<sigma>23 \<TT> \<epsilon>' \<FF>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : \<FF>'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> RK23 \<TT>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Obj\<rparr>" for a
    proof-
      from that consider \<open>a = 0\<close> | \<open>a = 1\<^sub>\<nat>\<close> | \<open>a = 2\<^sub>\<nat>\<close>
        unfolding cat_ordinal_cs_simps three by auto
      from this 0123 show ?thesis
        by (cases, use nothing in \<open>simp_all only:\<close>)
          (
            cs_concl
              cs_simp: cat_cs_simps cat_ordinal_cs_simps cat_Kan_cs_simps
              cs_intro:
                cat_cs_intros
                cat_ordinal_cs_intros
                cat_Kan_cs_intros 
                nat_omega_intros
          )+
    qed
    show
      "RK_\<sigma>23 \<TT> \<epsilon>' \<FF>'\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<FF>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
        RK23 \<TT>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> RK_\<sigma>23 \<TT> \<epsilon>' \<FF>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      if "f : a \<mapsto>\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> b" for a b f
      using that 0123
      by  (elim cat_ordinal_3_is_arrE, use nothing in \<open>simp_all only:\<close>) (*slow*)
        (
          cs_concl
            cs_simp:
              cat_cs_simps
              cat_ordinal_cs_simps
              \<FF>'.cf_ArrMap_Comp[symmetric]
              \<FF>'.HomCod.cat_Comp_assoc
              \<epsilon>'.ntcf_Comp_commute[symmetric]
              cat_Kan_cs_simps 
            cs_intro: cat_cs_intros cat_ordinal_cs_intros nat_omega_intros
        )+
  qed
    (
      cs_concl
        cs_simp: cat_Kan_cs_simps cs_intro: cat_cs_intros cat_Kan_cs_intros
    )+

qed

lemma RK_\<sigma>23_is_ntcf'[cat_Kan_cs_intros]:
  assumes "\<FF>' : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
    and "\<TT> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<epsilon>' : \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>23 \<mapsto>\<^sub>C\<^sub>F \<TT> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<GG>' = \<FF>'"
    and "\<HH>' = RK23 \<TT>"
    and "\<CC>' = cat_ordinal (3\<^sub>\<nat>)"
  shows "RK_\<sigma>23 \<TT> \<epsilon>' \<FF>' : \<GG>' \<mapsto>\<^sub>C\<^sub>F \<HH>': \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  using assms(1-3) unfolding assms(4-6) by (rule RK_\<sigma>23_is_ntcf)



subsection\<open>The right Kan extension along \<open>\<KK>23\<close>\<close>

lemma \<epsilon>23_is_cat_rKe:
  assumes "\<TT> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "ntcf_id \<TT> :
    RK23 \<TT> \<circ>\<^sub>C\<^sub>F \<KK>23 \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<TT> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<^sub>C cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<^sub>C \<AA>"
proof-

  interpret \<TT>: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<AA> \<TT> by (rule assms(1))
  interpret \<KK>23: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<open>\<KK>23\<close>
    by (cs_concl cs_simp: cs_intro: cat_cs_intros cat_Kan_cs_intros)
  interpret RK23: is_functor \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<AA> \<open>RK23 \<TT>\<close>
    by (cs_concl cs_simp: cs_intro: cat_Kan_cs_intros cat_cs_intros)

  from 0123 have [cat_cs_simps]: "\<TT>\<lparr>ArrMap\<rparr>\<lparr>1\<^sub>\<nat>, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet> = \<AA>\<lparr>CId\<rparr>\<lparr>\<TT>\<lparr>ObjMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>\<rparr>"
    by
      (
        cs_concl
          cs_simp: cat_ordinal_cs_simps is_functor.cf_ObjMap_CId[symmetric]
          cs_intro: cat_cs_intros
      )

  show ?thesis
  proof(intro is_cat_rKeI')
    
    fix \<FF>' \<epsilon>' assume prems:
      "\<FF>' : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      "\<epsilon>' : \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>23 \<mapsto>\<^sub>C\<^sub>F \<TT> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"

    interpret \<FF>': is_functor \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<AA> \<FF>' by (rule prems(1))
    interpret \<epsilon>': is_ntcf \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<AA> \<open>\<FF>' \<circ>\<^sub>C\<^sub>F \<KK>23\<close> \<TT> \<epsilon>' 
      by (rule prems(2))
    interpret RK_\<sigma>23: is_ntcf \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<AA> \<FF>' \<open>RK23 \<TT>\<close> \<open>RK_\<sigma>23 \<TT> \<epsilon>' \<FF>'\<close>
      by (intro RK_\<sigma>23_is_ntcf prems assms)

    show "\<exists>!\<sigma>.
      \<sigma> : \<FF>' \<mapsto>\<^sub>C\<^sub>F RK23 \<TT> : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> \<and>
      \<epsilon>' = ntcf_id \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23)"
    proof(intro ex1I conjI; (elim conjE)?)
      show "RK_\<sigma>23 \<TT> \<epsilon>' \<FF>' : \<FF>' \<mapsto>\<^sub>C\<^sub>F RK23 \<TT> : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
        by (intro RK_\<sigma>23.is_ntcf_axioms)
      show "\<epsilon>' = ntcf_id \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (RK_\<sigma>23 \<TT> \<epsilon>' \<FF>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23)"
      proof(rule ntcf_eqI)
        show "\<epsilon>' : \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>23 \<mapsto>\<^sub>C\<^sub>F \<TT> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
          by (intro prems)
        then have dom_lhs: "\<D>\<^sub>\<circ> (\<epsilon>'\<lparr>NTMap\<rparr>) = 2\<^sub>\<nat>"
          by (cs_concl cs_simp: cat_ordinal_cs_simps cat_cs_simps)
        show rhs:
          "ntcf_id \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (RK_\<sigma>23 \<TT> \<epsilon>' \<FF>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23) :
            \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>23 \<mapsto>\<^sub>C\<^sub>F \<TT> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
          by
            (
              cs_concl 
                cs_simp: cat_Kan_cs_simps cat_cs_simps 
                cs_intro: cat_Kan_cs_intros cat_cs_intros
            )
        then have dom_rhs: 
          "\<D>\<^sub>\<circ> ((ntcf_id \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (RK_\<sigma>23 \<TT> \<epsilon>' \<FF>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23))\<lparr>NTMap\<rparr>) = 2\<^sub>\<nat>"
          by (cs_concl cs_simp: cat_ordinal_cs_simps cat_cs_simps)
        show "\<epsilon>'\<lparr>NTMap\<rparr> = (ntcf_id \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (RK_\<sigma>23 \<TT> \<epsilon>' \<FF>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23))\<lparr>NTMap\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
          fix a assume prems: "a \<in>\<^sub>\<circ> 2\<^sub>\<nat>"
          then consider \<open>a = 0\<close> | \<open>a = 1\<^sub>\<nat>\<close> unfolding two by auto
          then show 
            "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
              (ntcf_id \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (RK_\<sigma>23 \<TT> \<epsilon>' \<FF>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23))\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
            by (cases; use nothing in \<open>simp_all only:\<close>)
              (
                cs_concl
                  cs_simp:
                    omega_of_set
                    cat_Kan_cs_simps
                    cat_cs_simps
                    cat_ordinal_cs_simps
                  cs_intro: cat_Kan_cs_intros cat_cs_intros nat_omega_intros
              )+
        qed (use rhs in \<open>cs_concl cs_simp: cs_intro: V_cs_intros cat_cs_intros\<close>)+
      qed simp_all

      fix \<sigma> assume prems': 
        "\<sigma> : \<FF>' \<mapsto>\<^sub>C\<^sub>F RK23 \<TT> : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
        "\<epsilon>' = ntcf_id \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23)"

      interpret \<sigma>: is_ntcf \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<AA> \<FF>' \<open>RK23 \<TT>\<close> \<sigma> 
        by (rule prems'(1))

      from prems'(2) have 
        "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>0\<rparr> = (ntcf_id \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23))\<lparr>NTMap\<rparr>\<lparr>0\<rparr>"
        by auto
      then have [cat_cs_simps]: "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>0\<rparr> = \<sigma>\<lparr>NTMap\<rparr>\<lparr>0\<rparr>"
        by
          (
            cs_prems
              cs_simp: cat_Kan_cs_simps cat_cs_simps cat_ordinal_cs_simps 
              cs_intro: cat_cs_intros nat_omega_intros
          )
      from prems'(2) have
        "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr> = (ntcf_id \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23))\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>"
        by auto
      then have [cat_cs_simps]: "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr> = \<sigma>\<lparr>NTMap\<rparr>\<lparr>2\<^sub>\<nat>\<rparr>"
        by
          (
            cs_prems
              cs_simp:
                omega_of_set cat_Kan_cs_simps cat_cs_simps cat_ordinal_cs_simps
              cs_intro: cat_cs_intros nat_omega_intros
          )

      show "\<sigma> = RK_\<sigma>23 \<TT> \<epsilon>' \<FF>'"
      proof(rule ntcf_eqI)
        show "\<sigma> : \<FF>' \<mapsto>\<^sub>C\<^sub>F RK23 \<TT> : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
          by (rule prems'(1))
        then have dom_lhs: "\<D>\<^sub>\<circ> (\<sigma>\<lparr>NTMap\<rparr>) = 3\<^sub>\<nat>"
          by (cs_concl cs_simp: cat_cs_simps cat_ordinal_cs_simps)
        show "RK_\<sigma>23 \<TT> \<epsilon>' \<FF>' : \<FF>' \<mapsto>\<^sub>C\<^sub>F RK23 \<TT> : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
          by (cs_concl cs_simp: cs_intro: cat_cs_intros cat_Kan_cs_intros)
        then have dom_rhs: "\<D>\<^sub>\<circ> (RK_\<sigma>23 \<TT> \<epsilon>' \<FF>'\<lparr>NTMap\<rparr>) = 3\<^sub>\<nat>"
          by (cs_concl cs_simp: cat_cs_simps cat_ordinal_cs_simps)
        from 0123 have 013: "[0, 1\<^sub>\<nat>]\<^sub>\<circ> : 0 \<mapsto>\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> 1\<^sub>\<nat>"
          by (cs_concl cs_simp: cs_intro: cat_ordinal_cs_intros nat_omega_intros)
        from 0123 have 123: "[1\<^sub>\<nat>, 2\<^sub>\<nat>]\<^sub>\<circ> : 1\<^sub>\<nat> \<mapsto>\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> 2\<^sub>\<nat>"
          by (cs_concl cs_simp: cs_intro: cat_ordinal_cs_intros nat_omega_intros)

        from \<sigma>.ntcf_Comp_commute[OF 123] 013 0123 
        have [symmetric, cat_Kan_cs_simps]:
          "\<sigma>\<lparr>NTMap\<rparr>\<lparr>2\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<FF>'\<lparr>ArrMap\<rparr> \<lparr>1\<^sub>\<nat>, 2\<^sub>\<nat>\<rparr>\<^sub>\<bullet> = \<sigma>\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>"
          by
            (
              cs_prems 
                cs_simp: cat_cs_simps cat_Kan_cs_simps RK23_ArrMap_app_12 
                cs_intro: cat_cs_intros
            )
        show "\<sigma>\<lparr>NTMap\<rparr> = RK_\<sigma>23 \<TT> \<epsilon>' \<FF>'\<lparr>NTMap\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
          fix a assume prems: "a \<in>\<^sub>\<circ> 3\<^sub>\<nat>"
          then consider \<open>a = 0\<close> | \<open>a = 1\<^sub>\<nat>\<close> | \<open>a = 2\<^sub>\<nat>\<close> unfolding three by auto
          then show "\<sigma>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = RK_\<sigma>23 \<TT> \<epsilon>' \<FF>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
            by (cases; use nothing in \<open>simp_all only:\<close>) 
              (cs_concl cs_simp: cat_cs_simps cat_Kan_cs_simps)+
        qed auto
      qed simp_all

    qed

  qed (cs_concl cs_simp: cat_Kan_cs_simps cs_intro: cat_cs_intros)+

qed



subsection\<open>
\<open>LK_\<sigma>23\<close>: towards the universal property of the left Kan extension along \<open>\<KK>23\<close>
\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition LK_\<sigma>23 :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "LK_\<sigma>23 \<TT> \<eta>' \<FF>' =
    [
      (
        \<lambda>a\<in>\<^sub>\<circ>cat_ordinal (3\<^sub>\<nat>)\<lparr>Obj\<rparr>.
         if a = 0 \<Rightarrow> \<eta>'\<lparr>NTMap\<rparr>\<lparr>0\<rparr>
          | a = 1\<^sub>\<nat> \<Rightarrow> \<FF>'\<lparr>ArrMap\<rparr>\<lparr>0, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<TT>\<lparr>HomCod\<rparr>\<^esub> \<eta>'\<lparr>NTMap\<rparr>\<lparr>0\<rparr>
          | a = 2\<^sub>\<nat> \<Rightarrow> \<eta>'\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>
          | otherwise \<Rightarrow> \<TT>\<lparr>HomCod\<rparr>\<lparr>Arr\<rparr>
      ),
      LK23 \<TT>,
      \<FF>',
      cat_ordinal (3\<^sub>\<nat>),
      \<FF>'\<lparr>HomCod\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma LK_\<sigma>23_components:
  shows "LK_\<sigma>23 \<TT> \<eta>' \<FF>'\<lparr>NTMap\<rparr> =
    (
      \<lambda>a\<in>\<^sub>\<circ>cat_ordinal (3\<^sub>\<nat>)\<lparr>Obj\<rparr>.
        if a = 0 \<Rightarrow> \<eta>'\<lparr>NTMap\<rparr>\<lparr>0\<rparr>
         | a = 1\<^sub>\<nat> \<Rightarrow> \<FF>'\<lparr>ArrMap\<rparr>\<lparr>0, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<TT>\<lparr>HomCod\<rparr>\<^esub> \<eta>'\<lparr>NTMap\<rparr>\<lparr>0\<rparr>
         | a = 2\<^sub>\<nat> \<Rightarrow> \<eta>'\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>
         | otherwise \<Rightarrow> \<TT>\<lparr>HomCod\<rparr>\<lparr>Arr\<rparr>
    )"
    and "LK_\<sigma>23 \<TT> \<eta>' \<FF>'\<lparr>NTDom\<rparr> = LK23 \<TT>"
    and "LK_\<sigma>23 \<TT> \<eta>' \<FF>'\<lparr>NTCod\<rparr> = \<FF>'"
    and "LK_\<sigma>23 \<TT> \<eta>' \<FF>'\<lparr>NTDGDom\<rparr> = cat_ordinal (3\<^sub>\<nat>)"
    and "LK_\<sigma>23 \<TT> \<eta>' \<FF>'\<lparr>NTDGCod\<rparr> = \<FF>'\<lparr>HomCod\<rparr>"
  unfolding LK_\<sigma>23_def nt_field_simps by (simp_all add: nat_omega_simps)

context
  fixes \<alpha> \<AA> \<FF>' \<TT>  
  assumes \<FF>': "\<FF>' : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and \<TT>: "\<TT> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
begin

interpretation \<FF>': is_functor \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<AA> \<FF>' by (rule \<FF>')
interpretation \<TT>: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<AA> \<TT> by (rule \<TT>)

lemmas LK_\<sigma>23_components' = 
  LK_\<sigma>23_components[where \<FF>'=\<FF>' and \<TT>=\<TT>, unfolded cat_cs_simps]

lemmas [cat_Kan_cs_simps] = LK_\<sigma>23_components'(2-5)

end


subsubsection\<open>Natural transformation map\<close>

mk_VLambda LK_\<sigma>23_components(1)
  |vsv LK_\<sigma>23_NTMap_vsv[cat_Kan_cs_intros]|
  |vdomain LK_\<sigma>23_NTMap_vdomain[cat_Kan_cs_simps]|
  |app LK_\<sigma>23_NTMap_app|

lemma LK_\<sigma>23_NTMap_app_0[cat_Kan_cs_simps]:
  assumes "a = 0"
  shows "LK_\<sigma>23 \<TT> \<eta>' \<FF>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<eta>'\<lparr>NTMap\<rparr>\<lparr>0\<rparr>"
  using assms unfolding LK_\<sigma>23_components cat_ordinal_cs_simps by simp

lemma (in is_functor) LK_\<sigma>23_NTMap_app_1[cat_Kan_cs_simps]:
  assumes "a = 1\<^sub>\<nat>"
  shows "LK_\<sigma>23 \<FF> \<eta>' \<FF>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<FF>'\<lparr>ArrMap\<rparr>\<lparr>0, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<eta>'\<lparr>NTMap\<rparr>\<lparr>0\<rparr>"
  using assms unfolding LK_\<sigma>23_components cat_ordinal_cs_simps cat_cs_simps by simp

lemmas [cat_Kan_cs_simps] = is_functor.LK_\<sigma>23_NTMap_app_1

lemma LK_\<sigma>23_NTMap_app_2[cat_Kan_cs_simps]:
  assumes "a = 2\<^sub>\<nat>"
  shows "LK_\<sigma>23 \<TT> \<eta>' \<FF>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = \<eta>'\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>"
  using assms unfolding LK_\<sigma>23_components cat_ordinal_cs_simps by simp


subsubsection\<open>\<open>LK_\<sigma>23\<close> is a natural transformation\<close>

lemma LK_\<sigma>23_is_ntcf:
  assumes "\<FF>' : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
    and "\<TT> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<eta>' : \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>23 : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "LK_\<sigma>23 \<TT> \<eta>' \<FF>' : LK23 \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
proof-
 
  interpret \<FF>': is_functor \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<AA> \<FF>' by (rule assms(1))
  interpret \<TT>: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<AA> \<TT> by (rule assms(2))
  interpret \<eta>': is_ntcf \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<AA> \<TT> \<open>\<FF>' \<circ>\<^sub>C\<^sub>F \<KK>23\<close> \<eta>' 
    by (rule assms(3))

  interpret \<KK>23: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<open>\<KK>23\<close>
    by (cs_concl cs_simp: cs_intro: cat_cs_intros cat_Kan_cs_intros)
  interpret LK23: is_functor \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<AA> \<open>LK23 \<TT>\<close>
    by (cs_concl cs_simp: cs_intro: cat_Kan_cs_intros cat_cs_intros)
 
  show ?thesis
  proof(rule is_ntcfI')
    show "vfsequence (LK_\<sigma>23 \<TT> \<eta>' \<FF>')" unfolding LK_\<sigma>23_def by simp
    show "vcard (LK_\<sigma>23 \<TT> \<eta>' \<FF>') = 5\<^sub>\<nat>"
      unfolding LK_\<sigma>23_def by (simp_all add: nat_omega_simps)
    show "LK_\<sigma>23 \<TT> \<eta>' \<FF>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : LK23 \<TT>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> \<FF>'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Obj\<rparr>" for a
    proof-
      from that consider \<open>a = 0\<close> | \<open>a = 1\<^sub>\<nat>\<close> | \<open>a = 2\<^sub>\<nat>\<close>
        unfolding cat_ordinal_cs_simps three by auto
      from this 0123 show 
        "LK_\<sigma>23 \<TT> \<eta>' \<FF>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> : LK23 \<TT>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> \<FF>'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        by (cases, use nothing in \<open>simp_all only:\<close>)
          (
            cs_concl
              cs_simp: cat_cs_simps cat_ordinal_cs_simps cat_Kan_cs_simps
              cs_intro:
                cat_cs_intros 
                cat_ordinal_cs_intros 
                cat_Kan_cs_intros
                nat_omega_intros
          )+
    qed
    show
      "LK_\<sigma>23 \<TT> \<eta>' \<FF>'\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> LK23 \<TT>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
        \<FF>'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> LK_\<sigma>23 \<TT> \<eta>' \<FF>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      if "f : a \<mapsto>\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> b" for a b f
      using that 0123 
      by (elim cat_ordinal_3_is_arrE, use nothing in \<open>simp_all only:\<close>) (*slow*)
        (
          cs_concl
            cs_simp:
              cat_cs_simps
              cat_ordinal_cs_simps
              \<FF>'.cf_ArrMap_Comp[symmetric]
              \<FF>'.HomCod.cat_Comp_assoc[symmetric]
              \<eta>'.ntcf_Comp_commute
              cat_Kan_cs_simps
            cs_intro: cat_cs_intros cat_ordinal_cs_intros nat_omega_intros
        )+
  qed
    (
      cs_concl
        cs_simp: cat_Kan_cs_simps cs_intro: cat_cs_intros cat_Kan_cs_intros
    )+

qed

lemma LK_\<sigma>23_is_ntcf'[cat_Kan_cs_intros]:
  assumes "\<FF>' : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<TT> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<eta>' : \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>23 : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    and "\<GG>' = LK23 \<TT>"
    and "\<HH>' = \<FF>'"
    and "\<CC>' = cat_ordinal (3\<^sub>\<nat>)"
  shows "LK_\<sigma>23 \<TT> \<eta>' \<FF>' : \<GG>' \<mapsto>\<^sub>C\<^sub>F \<HH>': \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  using assms(1-3) unfolding assms(4-6) by (rule LK_\<sigma>23_is_ntcf)



subsection\<open>The left Kan extension along \<open>\<KK>23\<close>\<close>

lemma \<eta>23_is_cat_rKe:
  assumes "\<TT> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "ntcf_id \<TT> :
    \<TT> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> LK23 \<TT> \<circ>\<^sub>C\<^sub>F \<KK>23 : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<^sub>C cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<^sub>C \<AA>"
proof-

  interpret \<TT>: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<AA> \<TT> by (rule assms(1))
  interpret \<KK>23: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<open>\<KK>23\<close>
    by (cs_concl cs_simp: cs_intro: cat_cs_intros cat_Kan_cs_intros)
  interpret LK23: is_functor \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<AA> \<open>LK23 \<TT>\<close>
    by (cs_concl cs_simp: cs_intro: cat_Kan_cs_intros cat_cs_intros)

  show ?thesis
  proof(intro is_cat_lKeI')
    fix \<FF>' \<eta>' assume prems:
      "\<FF>' : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      "\<eta>' : \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>23 : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"

    interpret \<FF>': is_functor \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<AA> \<FF>' by (rule prems(1))
    interpret \<eta>': is_ntcf \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<AA> \<TT> \<open>\<FF>' \<circ>\<^sub>C\<^sub>F \<KK>23\<close> \<eta>' 
      by (rule prems(2))
    interpret LK_\<sigma>23: is_ntcf \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<AA> \<open>LK23 \<TT>\<close> \<FF>' \<open>LK_\<sigma>23 \<TT> \<eta>' \<FF>'\<close>
      by (intro LK_\<sigma>23_is_ntcf prems assms)

    show "\<exists>!\<sigma>.
      \<sigma> : LK23 \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> \<and>
      \<eta>' = \<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23 \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT>"
    proof(intro ex1I conjI; (elim conjE)?)
      show "LK_\<sigma>23 \<TT> \<eta>' \<FF>' : LK23 \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
        by (intro LK_\<sigma>23.is_ntcf_axioms)
      show "\<eta>' = LK_\<sigma>23 \<TT> \<eta>' \<FF>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23 \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT>"
      proof(rule ntcf_eqI)
        show "\<eta>' : \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>23 : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
          by (intro prems)
        then have dom_lhs: "\<D>\<^sub>\<circ> (\<eta>'\<lparr>NTMap\<rparr>) = 2\<^sub>\<nat>"
          by (cs_concl cs_simp: cat_ordinal_cs_simps cat_cs_simps)
        show rhs:
          "LK_\<sigma>23 \<TT> \<eta>' \<FF>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23 \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT> :
            \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>23 : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
          by 
            (
              cs_concl 
                cs_simp: cat_Kan_cs_simps cat_cs_simps 
                cs_intro: cat_Kan_cs_intros cat_cs_intros
            )
        then have dom_rhs: 
          "\<D>\<^sub>\<circ> ((LK_\<sigma>23 \<TT> \<eta>' \<FF>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23 \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT>)\<lparr>NTMap\<rparr>) = 2\<^sub>\<nat>"
          by (cs_concl cs_simp: cat_ordinal_cs_simps cat_cs_simps)
        show "\<eta>'\<lparr>NTMap\<rparr> = (LK_\<sigma>23 \<TT> \<eta>' \<FF>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23 \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT>)\<lparr>NTMap\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
          fix a assume prems: "a \<in>\<^sub>\<circ> 2\<^sub>\<nat>"
          then consider \<open>a = 0\<close> | \<open>a = 1\<^sub>\<nat>\<close> unfolding two by auto
          then show 
            "\<eta>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr> =
              (LK_\<sigma>23 \<TT> \<eta>' \<FF>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23 \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT>)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
            by (cases; use nothing in \<open>simp_all only:\<close>)
              (
                cs_concl 
                  cs_simp: 
                    omega_of_set 
                    cat_Kan_cs_simps 
                    cat_cs_simps 
                    cat_ordinal_cs_simps 
                  cs_intro: cat_Kan_cs_intros cat_cs_intros nat_omega_intros
              )+
        qed (use rhs in \<open>cs_concl cs_simp: cs_intro: V_cs_intros cat_cs_intros\<close>)+
      qed simp_all

      fix \<sigma> assume prems': 
        "\<sigma> : LK23 \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
        "\<eta>' = \<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23 \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT>"

      interpret \<sigma>: is_ntcf \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<AA> \<open>LK23 \<TT>\<close> \<FF>' \<sigma> 
        by (rule prems'(1))

      from prems'(2) have 
        "\<eta>'\<lparr>NTMap\<rparr>\<lparr>0\<rparr> = (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23 \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT>)\<lparr>NTMap\<rparr>\<lparr>0\<rparr>"
        by auto
      then have [cat_cs_simps]: "\<eta>'\<lparr>NTMap\<rparr>\<lparr>0\<rparr> = \<sigma>\<lparr>NTMap\<rparr>\<lparr>0\<rparr>"
        by 
          (
            cs_prems 
              cs_simp: cat_Kan_cs_simps cat_cs_simps cat_ordinal_cs_simps 
              cs_intro: cat_cs_intros nat_omega_intros
          )
      from prems'(2) have
        "\<eta>'\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr> = (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23 \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT>)\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>"
        by auto
      then have [cat_cs_simps]: "\<eta>'\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr> = \<sigma>\<lparr>NTMap\<rparr>\<lparr>2\<^sub>\<nat>\<rparr>"
        by
          (
            cs_prems
              cs_simp:
                omega_of_set cat_Kan_cs_simps cat_cs_simps cat_ordinal_cs_simps
              cs_intro: cat_cs_intros nat_omega_intros
          )

      show "\<sigma> = LK_\<sigma>23 \<TT> \<eta>' \<FF>'"
      proof(rule ntcf_eqI)

        show "\<sigma> : LK23 \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>" 
          by (rule prems'(1))
        then have dom_lhs: "\<D>\<^sub>\<circ> (\<sigma>\<lparr>NTMap\<rparr>) = 3\<^sub>\<nat>"
          by (cs_concl cs_simp: cat_cs_simps cat_ordinal_cs_simps)
        show "LK_\<sigma>23 \<TT> \<eta>' \<FF>' : LK23 \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
          by (cs_concl cs_simp: cs_intro: cat_cs_intros cat_Kan_cs_intros)
        then have dom_rhs: "\<D>\<^sub>\<circ> (LK_\<sigma>23 \<TT> \<eta>' \<FF>'\<lparr>NTMap\<rparr>) = 3\<^sub>\<nat>"
          by (cs_concl cs_simp: cat_cs_simps cat_ordinal_cs_simps)
        from 0123 have 012: "[0, 1\<^sub>\<nat>]\<^sub>\<circ> : 0 \<mapsto>\<^bsub>cat_ordinal (2\<^sub>\<nat>)\<^esub> 1\<^sub>\<nat>"
          by (cs_concl cs_simp: cs_intro: cat_ordinal_cs_intros nat_omega_intros)
        from 0123 have 013: "[0, 1\<^sub>\<nat>]\<^sub>\<circ> : 0 \<mapsto>\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> 1\<^sub>\<nat>"
          by (cs_concl cs_simp: cs_intro: cat_ordinal_cs_intros nat_omega_intros)
        from 0123 have 00: "[0, 0]\<^sub>\<circ> = (cat_ordinal (2\<^sub>\<nat>))\<lparr>CId\<rparr>\<lparr>0\<rparr>"
          by (cs_concl cs_simp: cat_ordinal_cs_simps)
        from \<sigma>.ntcf_Comp_commute[OF 013] 013 0123 
        have [symmetric, cat_Kan_cs_simps]:
          "\<sigma>\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr> = \<FF>'\<lparr>ArrMap\<rparr>\<lparr>0, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<sigma>\<lparr>NTMap\<rparr>\<lparr>0\<rparr>"
          by
            (
              cs_prems
                cs_simp: cat_cs_simps cat_Kan_cs_simps 00 LK23_ArrMap_app_01
                cs_intro: cat_cs_intros cat_ordinal_cs_intros nat_omega_intros
            )

        show "\<sigma>\<lparr>NTMap\<rparr> = LK_\<sigma>23 \<TT> \<eta>' \<FF>'\<lparr>NTMap\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
          fix a assume prems: "a \<in>\<^sub>\<circ> 3\<^sub>\<nat>"
          then consider \<open>a = 0\<close> | \<open>a = 1\<^sub>\<nat>\<close> | \<open>a = 2\<^sub>\<nat>\<close> unfolding three by auto
          then show "\<sigma>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = LK_\<sigma>23 \<TT> \<eta>' \<FF>'\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
            by (cases; use nothing in \<open>simp_all only:\<close>) 
              (
                cs_concl 
                  cs_simp: cat_ordinal_cs_simps cat_cs_simps cat_Kan_cs_simps 
                  cs_intro: cat_cs_intros
              )+
        qed auto
      qed simp_all

    qed

  qed (cs_concl cs_simp: cat_Kan_cs_simps cs_intro: cat_cs_intros)+

qed



subsection\<open>Pointwise Kan extensions along \<open>\<KK>23\<close>\<close>

lemma \<epsilon>23_is_cat_pw_rKe:
  assumes "\<TT> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "ntcf_id \<TT> :
    RK23 \<TT> \<circ>\<^sub>C\<^sub>F \<KK>23 \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^sub>.\<^sub>p\<^sub>w\<^bsub>\<alpha>\<^esub> \<TT> :
    cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<^sub>C cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<^sub>C \<AA>"
proof-

  interpret \<TT>: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<AA> \<TT> by (rule assms(1))

  show ?thesis
  proof(intro is_cat_pw_rKeI \<epsilon>23_is_cat_rKe[OF assms])

    fix a assume prems: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    
    show
      "ntcf_id \<TT> : 
        RK23 \<TT> \<circ>\<^sub>C\<^sub>F \<KK>23 \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> \<TT> :
        cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<^sub>C
        cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<^sub>C
        (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) : \<AA> \<mapsto>\<mapsto>\<^sub>C cat_Set \<alpha>)"
    proof(intro is_cat_rKe_preservesI \<epsilon>23_is_cat_rKe[OF assms])
      from prems show "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
      show "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT> :
        (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F RK23 \<TT>) \<circ>\<^sub>C\<^sub>F \<KK>23 \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT> :
        cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<^sub>C cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<^sub>C cat_Set \<alpha>"
      proof(intro is_cat_rKeI')
        show "\<KK>23 : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_ordinal (3\<^sub>\<nat>)"
          by (cs_concl cs_simp: cs_intro: cat_Kan_cs_intros)
        from prems show
          "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F RK23 \<TT> : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
          by (cs_concl cs_simp: cs_intro: cat_cs_intros cat_Kan_cs_intros)
        from prems show 
          "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT> :
            Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F RK23 \<TT> \<circ>\<^sub>C\<^sub>F \<KK>23 \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT> :
            cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
          by
            (
              cs_concl
                cs_simp: cat_cs_simps cat_Kan_cs_simps
                cs_intro: cat_cs_intros cat_Kan_cs_intros
            )

        fix \<GG>' \<epsilon>' assume prems':
          "\<GG>' : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
          "\<epsilon>' :
            \<GG>' \<circ>\<^sub>C\<^sub>F \<KK>23 \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT> :
            cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"

        interpret \<GG>': is_functor \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<open>cat_Set \<alpha>\<close> \<GG>' 
          by (rule prems'(1))
        interpret \<epsilon>': is_ntcf
          \<alpha>
          \<open>cat_ordinal (2\<^sub>\<nat>)\<close>
          \<open>cat_Set \<alpha>\<close>
          \<open>\<GG>' \<circ>\<^sub>C\<^sub>F \<KK>23\<close>
          \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>\<close>
          \<epsilon>'
          by (rule prems'(2))

        show "\<exists>!\<sigma>.
          \<sigma> :
            \<GG>' \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F RK23 \<TT> :
            cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha> \<and>
          \<epsilon>' = Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23)"
        proof(intro ex1I conjI; (elim conjE)?)
          have [cat_Kan_cs_simps]: 
            "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F RK23 \<TT> = RK23 (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>)"
          proof(rule cf_eqI)
            from prems show lhs: "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F RK23 \<TT> : 
              cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
              by
                (
                  cs_concl
                    cs_simp: cat_cs_simps
                    cs_intro: cat_cs_intros cat_Kan_cs_intros
                )
            from prems show rhs: "RK23 (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>) : 
              cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
              by
                (
                  cs_concl
                    cs_simp: cat_cs_simps
                    cs_intro: cat_cs_intros cat_Kan_cs_intros
                )
            from lhs prems have ObjMap_dom_lhs: 
              "\<D>\<^sub>\<circ> ((Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F RK23 \<TT>)\<lparr>ObjMap\<rparr>) = 3\<^sub>\<nat>"
              by
                (
                  cs_concl
                    cs_simp: cat_ordinal_cs_simps cat_cs_simps 
                    cs_intro: cat_Kan_cs_intros cat_cs_intros
                )
            from rhs prems have ObjMap_dom_rhs:
              "\<D>\<^sub>\<circ> ((RK23 (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>))\<lparr>ObjMap\<rparr>) = 3\<^sub>\<nat>"
              by 
                (
                  cs_concl 
                    cs_simp: cat_ordinal_cs_simps cat_cs_simps 
                    cs_intro: cat_Kan_cs_intros 
                )
            show 
              "(Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F RK23 \<TT>)\<lparr>ObjMap\<rparr> =
                RK23 (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>)\<lparr>ObjMap\<rparr>"
            proof(rule vsv_eqI, unfold ObjMap_dom_lhs ObjMap_dom_rhs)
              fix c assume prems'': "c \<in>\<^sub>\<circ> 3\<^sub>\<nat>"
              with 0123 consider \<open>c = 0\<close> | \<open>c = 1\<^sub>\<nat>\<close> | \<open>c = 2\<^sub>\<nat>\<close> by force
              from this prems prems'' 0123 show 
                "(Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F RK23 \<TT>)\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> =
                  RK23 (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>)\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
                by (cases; use nothing in \<open>simp_all only:\<close>)
                  (
                    cs_concl
                      cs_simp:
                        cat_ordinal_cs_simps
                        cat_cs_simps
                        cat_op_simps
                        cat_Kan_cs_simps
                      cs_intro: cat_Kan_cs_intros cat_cs_intros
                 )+
            qed 
              (
                use prems in \<open>
                  cs_concl cs_simp: cs_intro: cat_Kan_cs_intros cat_cs_intros
                  \<close>
              )+
            from lhs prems have ArrMap_dom_lhs: 
              "\<D>\<^sub>\<circ> ((Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F RK23 \<TT>)\<lparr>ArrMap\<rparr>) = 
                cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>"
              by
                (
                  cs_concl
                    cs_simp: cat_ordinal_cs_simps cat_cs_simps 
                    cs_intro: cat_Kan_cs_intros cat_cs_intros
                )
            from rhs prems have ArrMap_dom_rhs:
              "\<D>\<^sub>\<circ> ((RK23 (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>))\<lparr>ArrMap\<rparr>) = 
                cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>"
              by 
                (
                  cs_concl 
                    cs_simp: cat_ordinal_cs_simps cat_cs_simps 
                    cs_intro: cat_Kan_cs_intros 
                )
            show 
              "(Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F RK23 \<TT>)\<lparr>ArrMap\<rparr> =
                RK23 (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>)\<lparr>ArrMap\<rparr>"
            proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
              fix f assume prems'': "f \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>"
              then obtain a' b' where "f : a' \<mapsto>\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> b'" by auto
              from this 0123 prems show 
                "(Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F RK23 \<TT>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
                  RK23 (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
                by (*slow*)
                  (
                    elim cat_ordinal_3_is_arrE;
                    use nothing in \<open>simp_all only:\<close>
                  )
                  (
                    cs_concl
                      cs_simp: cat_cs_simps cat_Kan_cs_simps cat_op_simps
                      cs_intro:
                        cat_ordinal_cs_intros
                        cat_Kan_cs_intros
                        cat_cs_intros
                        nat_omega_intros
                  )+
            qed 
              (
                use prems in 
                  \<open>cs_concl cs_simp: cs_intro: cat_Kan_cs_intros cat_cs_intros\<close>
              )+
          qed simp_all

          show "RK_\<sigma>23 (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>) \<epsilon>' \<GG>' : 
            \<GG>' \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F RK23 \<TT> : 
            cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
            by (intro RK_\<sigma>23_is_ntcf')
              (cs_concl cs_simp: cat_Kan_cs_simps cs_intro: cat_cs_intros)+
          show "\<epsilon>' = 
            Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F 
            ntcf_id \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F 
            (RK_\<sigma>23 (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>) \<epsilon>' \<GG>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23)"
          proof(rule ntcf_eqI)
            show "\<epsilon>' :
              \<GG>' \<circ>\<^sub>C\<^sub>F \<KK>23 \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT> :
              cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
              by (intro prems')
            then have dom_lhs: "\<D>\<^sub>\<circ> (\<epsilon>'\<lparr>NTMap\<rparr>) = 2\<^sub>\<nat>"
              by (cs_concl cs_simp: cat_ordinal_cs_simps cat_cs_simps)
            from prems show 
              "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F 
                ntcf_id \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F 
                (RK_\<sigma>23 (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>) \<epsilon>' \<GG>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23) :
              \<GG>' \<circ>\<^sub>C\<^sub>F \<KK>23 \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT> :
              cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
              by
                (
                  cs_concl
                    cs_simp: cat_Kan_cs_simps
                    cs_intro: cat_Kan_cs_intros cat_cs_intros
                )
            then have dom_rhs: 
              "\<D>\<^sub>\<circ> 
                (
                  (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F
                  ntcf_id \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F 
                  (RK_\<sigma>23 (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>) \<epsilon>' \<GG>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23)
                )\<lparr>NTMap\<rparr>) = 2\<^sub>\<nat>"
              by (cs_concl cs_simp: cat_ordinal_cs_simps cat_cs_simps)
            show "\<epsilon>'\<lparr>NTMap\<rparr> =
              (
                Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F
                ntcf_id \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F
                (RK_\<sigma>23 (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>) \<epsilon>' \<GG>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23)
              )\<lparr>NTMap\<rparr>"
            proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
              fix c assume prems'': "c \<in>\<^sub>\<circ> 2\<^sub>\<nat>"
              then consider \<open>c = 0\<close> | \<open>c = 1\<^sub>\<nat>\<close> unfolding two by auto
              from this prems 0123 show "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>c\<rparr> =
                (
                  Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F 
                  ntcf_id \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F 
                  (RK_\<sigma>23 (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>) \<epsilon>' \<GG>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23)
                )\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
                by (cases; use nothing in \<open>simp_all only:\<close>)
                  (
                    cs_concl
                      cs_simp: 
                        cat_Kan_cs_simps 
                        cat_ordinal_cs_simps 
                        cat_cs_simps
                        cat_op_simps
                        cat_Set_components(1)
                      cs_intro:
                        cat_Kan_cs_intros
                        cat_cs_intros
                        cat_prod_cs_intros
                        \<TT>.HomCod.cat_Hom_in_Vset
                  )+
            qed (cs_concl cs_simp: cs_intro: cat_cs_intros V_cs_intros)+

          qed simp_all

          fix \<sigma> assume prems'':
            "\<sigma> :
              \<GG>' \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F RK23 \<TT> :
              cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
            "\<epsilon>' =
              Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23)"

          interpret \<sigma>: is_ntcf 
            \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<open>cat_Set \<alpha>\<close> \<GG>' \<open>Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F RK23 \<TT>\<close> \<sigma>
            by (rule prems''(1))

          from prems''(2) have "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>0\<rparr> =
            (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23))\<lparr>NTMap\<rparr>\<lparr>0\<rparr>"
            by auto
          from this prems 0123 have \<epsilon>'_NTMap_app_0: "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>0\<rparr> = \<sigma>\<lparr>NTMap\<rparr>\<lparr>0\<rparr>"
            by
              (
                cs_prems
                  cs_simp:
                    cat_ordinal_cs_simps
                    cat_cs_simps
                    cat_Kan_cs_simps
                    cat_op_simps
                    \<KK>23_ObjMap_app_0
                    cat_Set_components(1)
                  cs_intro: 
                    cat_Kan_cs_intros
                    cat_cs_intros
                    cat_prod_cs_intros
                    \<TT>.HomCod.cat_Hom_in_Vset
              )
          from 0123 have 01: "[0, 1\<^sub>\<nat>]\<^sub>\<circ> : 0 \<mapsto>\<^bsub>cat_ordinal (2\<^sub>\<nat>)\<^esub> 1\<^sub>\<nat>"
            by
              (
                cs_concl
                  cs_simp: cat_cs_simps
                  cs_intro: cat_ordinal_cs_intros nat_omega_intros
              )
          from prems''(2) have 
            "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr> =
              (
                Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F
                ntcf_id \<TT> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F
                (\<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23)
              )\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>"
            by auto
          from this prems 0123 have \<epsilon>'_NTMap_app_1:  
            "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr> = \<sigma>\<lparr>NTMap\<rparr>\<lparr>2\<^sub>\<nat>\<rparr>"
            by
              (
                cs_prems
                  cs_simp:
                    cat_ordinal_cs_simps
                    cat_cs_simps
                    cat_Kan_cs_simps
                    cat_op_simps
                    \<KK>23_ObjMap_app_1
                    cat_Set_components(1)
                  cs_intro: 
                    cat_Kan_cs_intros
                    cat_cs_intros
                    cat_prod_cs_intros
                    \<TT>.HomCod.cat_Hom_in_Vset
              )

          from 0123 have 012: "[0, 1\<^sub>\<nat>]\<^sub>\<circ> : 0 \<mapsto>\<^bsub>cat_ordinal (2\<^sub>\<nat>)\<^esub> 1\<^sub>\<nat>"
            by 
              (
                cs_concl cs_simp: cs_intro:
                  cat_ordinal_cs_intros nat_omega_intros
              )
          from 0123 have 013: "[0, 1\<^sub>\<nat>]\<^sub>\<circ> : 0 \<mapsto>\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> 1\<^sub>\<nat>"
            by 
              ( 
                cs_concl cs_simp: cs_intro: 
                  cat_ordinal_cs_intros nat_omega_intros
              )
          from 0123 have 123: "[1\<^sub>\<nat>, 2\<^sub>\<nat>]\<^sub>\<circ> : 1\<^sub>\<nat> \<mapsto>\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> 2\<^sub>\<nat>"
            by 
              (
                cs_concl cs_simp: cs_intro:
                  cat_ordinal_cs_intros nat_omega_intros
              )
          from 0123 have 11: "[1\<^sub>\<nat>, 1\<^sub>\<nat>]\<^sub>\<circ> = (cat_ordinal (2\<^sub>\<nat>))\<lparr>CId\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>"
            by (cs_concl cs_simp: cat_ordinal_cs_simps)

          from \<sigma>.ntcf_Comp_commute[OF 123] prems 012 013 
          have [cat_Kan_cs_simps]:
            "\<epsilon>'\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> \<GG>'\<lparr>ArrMap\<rparr>\<lparr>1\<^sub>\<nat>, 2\<^sub>\<nat>\<rparr>\<^sub>\<bullet> = \<sigma>\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>"
            by (*slow*)
              (
                cs_prems 1
                  cs_simp:
                    cat_cs_simps
                    cat_Kan_cs_simps
                    \<epsilon>'_NTMap_app_1[symmetric]
                    is_functor.cf_ObjMap_CId
                    RK23_ArrMap_app_12
                    11
                  cs_intro: cat_cs_intros nat_omega_intros 
              )
          
          show "\<sigma> = RK_\<sigma>23 (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>) \<epsilon>' \<GG>'"
          proof(rule ntcf_eqI)

            show \<sigma>: "\<sigma> : 
              \<GG>' \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F RK23 \<TT> : 
              cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
              by (rule prems''(1))
            then have dom_lhs: "\<D>\<^sub>\<circ> (\<sigma>\<lparr>NTMap\<rparr>) = 3\<^sub>\<nat>"
              by (cs_concl cs_simp: cat_ordinal_cs_simps cat_cs_simps)
            show "RK_\<sigma>23 (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>) \<epsilon>' \<GG>' :
              \<GG>' \<mapsto>\<^sub>C\<^sub>F Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F RK23 \<TT> : 
              cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
              by 
                (
                  cs_concl 
                    cs_simp: cat_Kan_cs_simps 
                    cs_intro: cat_Kan_cs_intros cat_cs_intros
                )
            then have dom_rhs: 
              "\<D>\<^sub>\<circ> (RK_\<sigma>23 (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>) \<epsilon>' \<GG>'\<lparr>NTMap\<rparr>) = 3\<^sub>\<nat>"
              by (cs_concl cs_simp: cat_ordinal_cs_simps cat_cs_simps)
            show "\<sigma>\<lparr>NTMap\<rparr> = RK_\<sigma>23 (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>) \<epsilon>' \<GG>'\<lparr>NTMap\<rparr>"
            proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
              fix c assume "c \<in>\<^sub>\<circ> 3\<^sub>\<nat>"
              then consider \<open>c = 0\<close> | \<open>c = 1\<^sub>\<nat>\<close> | \<open>c = 2\<^sub>\<nat>\<close>  
                unfolding three by auto
              from this 0123 show
                "\<sigma>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> = RK_\<sigma>23 (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(a,-) \<circ>\<^sub>C\<^sub>F \<TT>) \<epsilon>' \<GG>'\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
                by (cases; use nothing in \<open>simp_all only:\<close>)
                  (
                    cs_concl cs_simp:
                      cat_Kan_cs_simps \<epsilon>'_NTMap_app_1 \<epsilon>'_NTMap_app_0
                  )+
            qed (cs_concl cs_simp: cs_intro: cat_Kan_cs_intros V_cs_intros)+

          qed simp_all

        qed

      qed

    qed

  qed

qed

lemma \<eta>23_is_cat_pw_lKe:
  assumes "\<TT> : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "ntcf_id \<TT> :
    \<TT> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^sub>.\<^sub>p\<^sub>w\<^bsub>\<alpha>\<^esub> LK23 \<TT> \<circ>\<^sub>C\<^sub>F \<KK>23 :
    cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<^sub>C cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<^sub>C \<AA>"
proof-

  interpret \<TT>: is_functor \<alpha> \<open>cat_ordinal (2\<^sub>\<nat>)\<close> \<AA> \<TT> by (rule assms(1))

  from ord_of_nat_\<omega> interpret cat_ordinal_3: finite_category \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close>
    by (cs_concl cs_intro: cat_ordinal_cs_intros)

  from 0123 have 002: "[0, 0]\<^sub>\<circ> : 0 \<mapsto>\<^bsub>cat_ordinal (2\<^sub>\<nat>)\<^esub> 0"
    by (cs_concl cs_simp: cat_ordinal_cs_simps cs_intro: cat_cs_intros)

  show ?thesis
  proof(intro is_cat_pw_lKeI \<eta>23_is_cat_rKe assms, unfold cat_op_simps)
    fix a assume prems: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    show 
      "op_ntcf (ntcf_id \<TT>) :
        op_cf (LK23 \<TT>) \<circ>\<^sub>C\<^sub>F op_cf \<KK>23 \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> op_cf \<TT> :
        op_cat (cat_ordinal (2\<^sub>\<nat>)) \<mapsto>\<^sub>C op_cat (cat_ordinal (3\<^sub>\<nat>)) \<mapsto>\<^sub>C
        (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C cat_Set \<alpha>)"
    proof(intro is_cat_rKe_preservesI)
      show 
        "op_ntcf (ntcf_id \<TT>) :
          op_cf (LK23 \<TT>) \<circ>\<^sub>C\<^sub>F op_cf \<KK>23 \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> op_cf \<TT> :
          op_cat (cat_ordinal (2\<^sub>\<nat>)) \<mapsto>\<^sub>C op_cat (cat_ordinal (3\<^sub>\<nat>)) \<mapsto>\<^sub>C op_cat \<AA>"
      proof(cs_intro_step cat_op_intros)
        show "ntcf_id \<TT> :
          \<TT> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub> LK23 \<TT> \<circ>\<^sub>C\<^sub>F \<KK>23 :
          cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<^sub>C cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<^sub>C \<AA>"
          by (intro \<eta>23_is_cat_rKe assms)
      qed simp_all
      from prems show "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Set \<alpha>"
        by (cs_concl cs_simp: cs_intro: cat_cs_intros)

      have 
        "op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT> :
          op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub>
          (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F LK23 \<TT>) \<circ>\<^sub>C\<^sub>F \<KK>23 :
          cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<^sub>C cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<^sub>C op_cat (cat_Set \<alpha>)"
      proof(intro is_cat_lKeI')
        show "\<KK>23 : cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_ordinal (3\<^sub>\<nat>)"
          by (cs_concl cs_simp: cs_intro: cat_Kan_cs_intros)
        from prems show "op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F LK23 \<TT> :
          cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat (cat_Set \<alpha>)"
          by 
            (
              cs_concl
                cs_simp: cat_cs_simps cat_op_simps 
                cs_intro: cat_Kan_cs_intros cat_cs_intros cat_op_intros
            )

        from prems show 
          "op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT> :
            op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT> \<mapsto>\<^sub>C\<^sub>F 
            op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F LK23 \<TT> \<circ>\<^sub>C\<^sub>F \<KK>23 :
            cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat (cat_Set \<alpha>)"
          by 
            (
              cs_concl 
                cs_simp: cat_cs_simps cat_Kan_cs_simps cat_op_simps
                cs_intro: cat_Kan_cs_intros cat_cs_intros cat_op_intros
            )

        fix \<FF>' \<eta>' assume prems':
          "\<FF>' : cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat (cat_Set \<alpha>)"
          "\<eta>' :
            op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>23 :
            cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat (cat_Set \<alpha>)"

        interpret \<FF>': is_functor \<alpha> \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<open>op_cat (cat_Set \<alpha>)\<close> \<FF>'
          by (rule prems'(1))
        interpret \<eta>': is_ntcf
          \<alpha>
          \<open>cat_ordinal (2\<^sub>\<nat>)\<close>
          \<open>op_cat (cat_Set \<alpha>)\<close>
          \<open>op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>\<close> 
          \<open>\<FF>' \<circ>\<^sub>C\<^sub>F \<KK>23\<close> 
          \<eta>'
          by (rule prems'(2))
        note [unfolded cat_op_simps, cat_cs_intros] = 
          \<eta>'.ntcf_NTMap_is_arr'
          \<FF>'.cf_ArrMap_is_arr'
        show
          "\<exists>!\<sigma>.
            \<sigma> :
              op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F LK23 \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' :
              cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat (cat_Set \<alpha>) \<and>
            \<eta>' = \<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23 \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT>)"
        proof(intro ex1I conjI; (elim conjE)?) 
          have [cat_Kan_cs_simps]:
            "op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F LK23 \<TT> =
              LK23 (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>)"
          proof(rule cf_eqI)
            from prems show lhs: "op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F LK23 \<TT> :
              cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat (cat_Set \<alpha>)"
              by
                (
                  cs_concl
                    cs_simp: cat_op_simps
                    cs_intro: cat_Kan_cs_intros cat_cs_intros cat_op_intros
                )
            from prems show rhs: "LK23 (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>) :
              cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat (cat_Set \<alpha>)"
              by (cs_concl cs_simp: cs_intro: cat_Kan_cs_intros cat_cs_intros)
            from lhs prems have ObjMap_dom_lhs:
              "\<D>\<^sub>\<circ> ((op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F LK23 \<TT>)\<lparr>ObjMap\<rparr>) = 3\<^sub>\<nat>"
              by
                (
                  cs_concl
                    cs_simp: cat_ordinal_cs_simps cat_cs_simps cat_op_simps 
                    cs_intro: cat_Kan_cs_intros cat_cs_intros
                )
            from rhs prems have ObjMap_dom_rhs:
              "\<D>\<^sub>\<circ> (LK23 (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>)\<lparr>ObjMap\<rparr>) = 3\<^sub>\<nat>"
              by (cs_concl cs_simp: cat_ordinal_cs_simps cat_cs_simps)
            show
              "(op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F LK23 \<TT>)\<lparr>ObjMap\<rparr> =
                LK23 (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>)\<lparr>ObjMap\<rparr>"
            proof(rule vsv_eqI, unfold ObjMap_dom_lhs ObjMap_dom_rhs)
             fix c assume prems'': "c \<in>\<^sub>\<circ> 3\<^sub>\<nat>"
             then consider \<open>c = 0\<close> | \<open>c = 1\<^sub>\<nat>\<close> | \<open>c = 2\<^sub>\<nat>\<close> 
               unfolding three by auto
              from this prems 0123 show 
                "(op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F LK23 \<TT>)\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> =
                  LK23 (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>)\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
                by (cases; use nothing in \<open>simp_all only:\<close>)
                  (
                    cs_concl
                      cs_simp:
                        cat_ordinal_cs_simps 
                        cat_Kan_cs_simps 
                        cat_cs_simps 
                        cat_op_simps
                      cs_intro: cat_Kan_cs_intros cat_cs_intros cat_op_intros
                  )+
            qed
              (
                use prems in 
                  \<open>
                    cs_concl
                      cs_simp: cat_op_simps 
                      cs_intro: cat_Kan_cs_intros cat_cs_intros cat_op_intros
                  \<close>
              )+

            from lhs prems have ArrMap_dom_lhs:
              "\<D>\<^sub>\<circ> ((op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F LK23 \<TT>)\<lparr>ArrMap\<rparr>) = 
                cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>"
              by
                (
                  cs_concl
                    cs_simp: cat_ordinal_cs_simps cat_cs_simps cat_op_simps 
                    cs_intro: cat_Kan_cs_intros cat_cs_intros
                )
            from rhs prems have ArrMap_dom_rhs:
              "\<D>\<^sub>\<circ> (LK23 (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>)\<lparr>ArrMap\<rparr>) =
                cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>"
              by (cs_concl cs_simp: cat_cs_simps)

            show
              "(op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F LK23 \<TT>)\<lparr>ArrMap\<rparr> =
                LK23 (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>)\<lparr>ArrMap\<rparr>"
            proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
              fix f assume "f \<in>\<^sub>\<circ> cat_ordinal (3\<^sub>\<nat>)\<lparr>Arr\<rparr>"
              then obtain a' b' where f: "f : a' \<mapsto>\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> b'" 
                by auto
              from f prems 0123 002 show
                "(op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F LK23 \<TT>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
                  LK23 (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
                by (elim cat_ordinal_3_is_arrE, (simp_all only:)?)
                  (
                    cs_concl
                      cs_simp: cat_cs_simps cat_Kan_cs_simps cat_op_simps 
                      cs_intro: 
                        cat_ordinal_cs_intros 
                        cat_Kan_cs_intros 
                        cat_cs_intros   
                        cat_op_intros 
                        nat_omega_intros
                  )+
            qed
              (
                use prems in
                  \<open>
                    cs_concl 
                      cs_simp: cat_op_simps
                      cs_intro: cat_Kan_cs_intros cat_cs_intros cat_op_intros\<close>
              )+
          
          qed simp_all

          show "LK_\<sigma>23 (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>) \<eta>' \<FF>' : 
            op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F LK23 \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' : 
            cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat (cat_Set \<alpha>)"
            by
              (
                cs_concl 
                  cs_simp: cat_cs_simps cat_Kan_cs_simps cat_op_simps 
                  cs_intro: cat_Kan_cs_intros cat_cs_intros cat_op_intros
              )

          show "\<eta>' =
            LK_\<sigma>23
              (
                op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>) \<eta>' \<FF>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F
                \<KK>23 \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F 
                (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT>
              )"
          proof(rule ntcf_eqI)
            show lhs: "\<eta>' :
              op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>23 :
              cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat (cat_Set \<alpha>)"
              by (rule prems'(2))
            from lhs have "\<D>\<^sub>\<circ> (\<eta>'\<lparr>NTMap\<rparr>) = cat_ordinal (2\<^sub>\<nat>)\<lparr>Obj\<rparr>"
              by (cs_concl cs_simp: cat_cs_simps)
            from prems show rhs: 
              "LK_\<sigma>23
                (
                  op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>) \<eta>' \<FF>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F 
                  \<KK>23 \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F 
                  (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT>
                ) : 
              op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' \<circ>\<^sub>C\<^sub>F \<KK>23 :
              cat_ordinal (2\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat (cat_Set \<alpha>)"
              by 
                (
                  cs_concl 
                    cs_simp: cat_Kan_cs_simps cat_op_simps 
                    cs_intro: cat_Kan_cs_intros cat_cs_intros cat_op_intros
                )
            from lhs have dom_lhs: "\<D>\<^sub>\<circ> (\<eta>'\<lparr>NTMap\<rparr>) = 2\<^sub>\<nat>"
              by (cs_concl cs_simp: cat_ordinal_cs_simps cat_cs_simps)
            from rhs have dom_rhs: "\<D>\<^sub>\<circ> ((LK_\<sigma>23
              (
                op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>) \<eta>' \<FF>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F 
                \<KK>23 \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F
                (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT>
              ))\<lparr>NTMap\<rparr>) = 2\<^sub>\<nat>"
              by (cs_concl cs_simp: cat_ordinal_cs_simps cat_cs_simps)
            show
              "\<eta>'\<lparr>NTMap\<rparr> =
                (
                  LK_\<sigma>23
                    (
                      op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>) \<eta>' \<FF>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F
                      \<KK>23 \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F 
                      (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT>
                    )
                )\<lparr>NTMap\<rparr>"
            proof(rule vsv_eqI, unfold dom_lhs dom_rhs cat_ordinal_cs_simps)
              fix c assume "c \<in>\<^sub>\<circ> 2\<^sub>\<nat>"
              then consider \<open>c = 0\<close> | \<open>c = 1\<^sub>\<nat>\<close> unfolding two by auto
              from this prems 0123 show 
                "\<eta>'\<lparr>NTMap\<rparr>\<lparr>c\<rparr> = 
                  (
                    LK_\<sigma>23 (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>) \<eta>' \<FF>' \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F 
                    \<KK>23 \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT>)
                  )\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
                by (cases, use nothing in \<open>simp_all only:\<close>)
                  (
                    cs_concl
                      cs_simp: 
                        cat_ordinal_cs_simps 
                        cat_Kan_cs_simps 
                        cat_cs_simps 
                        cat_op_simps 
                        \<KK>23_ObjMap_app_1 
                        \<KK>23_ObjMap_app_0 
                        LK_\<sigma>23_NTMap_app_0 
                        cat_Set_components(1) 
                      cs_intro: 
                        cat_Kan_cs_intros 
                        cat_cs_intros 
                        cat_prod_cs_intros 
                        cat_op_intros 
                        \<TT>.HomCod.cat_Hom_in_Vset
                  )+
            qed (cs_concl cs_simp: cs_intro: V_cs_intros cat_cs_intros)+
          qed simp_all

          fix \<sigma> assume prems'':
            "\<sigma> : 
              op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F LK23 \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' : 
              cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat (cat_Set \<alpha>)"
            "\<eta>' = \<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<KK>23 \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT>)"

          interpret \<sigma>: is_ntcf 
            \<alpha>
            \<open>cat_ordinal (3\<^sub>\<nat>)\<close> \<open>op_cat (cat_Set \<alpha>)\<close> 
            \<open>op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F LK23 \<TT>\<close> 
            \<FF>' 
            \<sigma>
            by (rule prems''(1))

          note [cat_Kan_cs_intros] = \<sigma>.ntcf_NTMap_is_arr'[unfolded cat_op_simps]

          from prems''(2) have 
            "\<eta>'\<lparr>NTMap\<rparr>\<lparr>0\<rparr> =
              (
                \<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F
                \<KK>23 \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F
                (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT>)
              )\<lparr>NTMap\<rparr>\<lparr>0\<rparr>"
            by simp
          from this prems 0123 have \<eta>'_NTMap_app_0: "\<eta>'\<lparr>NTMap\<rparr>\<lparr>0\<rparr> = \<sigma>\<lparr>NTMap\<rparr>\<lparr>0\<rparr>"
            by (*very slow*) 
              (
                cs_prems 
                  cs_simp: 
                    cat_ordinal_cs_simps
                    cat_Kan_cs_simps 
                    cat_cs_simps 
                    cat_op_simps 
                    cat_Set_components(1)
                  cs_intro: 
                    cat_Kan_cs_intros 
                    cat_cs_intros 
                    cat_prod_cs_intros
                    cat_op_intros 
                    \<TT>.HomCod.cat_Hom_in_Vset
              )

          from prems''(2) have 
            "\<eta>'\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr> =
              (
                \<sigma> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F
                \<KK>23 \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F
                (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F ntcf_id \<TT>)
              )\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>"
            by simp
          from this prems 0123 have \<eta>'_NTMap_app_1: "\<eta>'\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr> = \<sigma>\<lparr>NTMap\<rparr>\<lparr>2\<^sub>\<nat>\<rparr>"
            by (*very slow*) 
              (
                cs_prems
                  cs_simp:
                    cat_ordinal_cs_simps
                    cat_Kan_cs_simps
                    cat_cs_simps
                    cat_op_simps
                    cat_Set_components(1)
                  cs_intro:
                    cat_Kan_cs_intros
                    cat_cs_intros
                    cat_prod_cs_intros
                    cat_op_intros
                    \<TT>.HomCod.cat_Hom_in_Vset
              )+

          from 0123 have 013: "[0, 1\<^sub>\<nat>]\<^sub>\<circ> : 0 \<mapsto>\<^bsub>cat_ordinal (3\<^sub>\<nat>)\<^esub> 1\<^sub>\<nat>"
            by (cs_concl cs_simp: cs_intro: cat_ordinal_cs_intros nat_omega_intros)
          from 0123 have 00: "[0, 0]\<^sub>\<circ> = (cat_ordinal (2\<^sub>\<nat>))\<lparr>CId\<rparr>\<lparr>0\<rparr>"
            by (cs_concl cs_simp: cat_ordinal_cs_simps)

          from \<sigma>.ntcf_Comp_commute[OF 013] prems 0123 013
          have [cat_Kan_cs_simps]:
            "\<sigma>\<lparr>NTMap\<rparr>\<lparr>1\<^sub>\<nat>\<rparr> = \<eta>'\<lparr>NTMap\<rparr>\<lparr>0\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> \<FF>'\<lparr>ArrMap\<rparr>\<lparr>0, 1\<^sub>\<nat>\<rparr>\<^sub>\<bullet>"
            by
              (
                cs_prems
                  cs_simp:
                    cat_ordinal_cs_simps
                    cat_Kan_cs_simps
                    cat_cs_simps
                    cat_op_simps
                    LK23_ArrMap_app_01
                  cs_intro: 
                    cat_ordinal_cs_intros
                    cat_Kan_cs_intros
                    cat_cs_intros
                    cat_prod_cs_intros
                    cat_op_intros
                    nat_omega_intros
                  cs_simp: 00 \<eta>'_NTMap_app_0[symmetric]
              )

          show "\<sigma> = LK_\<sigma>23 (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>) \<eta>' \<FF>'"
          proof(rule ntcf_eqI)
            show lhs: "\<sigma> :
              op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F LK23 \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' :
              cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat (cat_Set \<alpha>)"
              by (rule prems''(1))
            show rhs: "LK_\<sigma>23 (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>) \<eta>' \<FF>' : 
              op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F LK23 \<TT> \<mapsto>\<^sub>C\<^sub>F \<FF>' :
              cat_ordinal (3\<^sub>\<nat>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> op_cat (cat_Set \<alpha>)"
              by
                (
                  cs_concl
                    cs_simp: cat_Kan_cs_simps 
                    cs_intro: cat_Kan_cs_intros cat_cs_intros
                )
            from lhs have dom_lhs: "\<D>\<^sub>\<circ> (\<sigma>\<lparr>NTMap\<rparr>) = 3\<^sub>\<nat>"
              by (cs_concl cs_simp: cat_ordinal_cs_simps cat_cs_simps)
            from rhs have dom_rhs:
              "\<D>\<^sub>\<circ> (LK_\<sigma>23 (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>) \<eta>' \<FF>'\<lparr>NTMap\<rparr>) = 3\<^sub>\<nat>"
              by (cs_concl cs_simp: cat_ordinal_cs_simps cat_cs_simps)

            show "\<sigma>\<lparr>NTMap\<rparr> = LK_\<sigma>23 (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>) \<eta>' \<FF>'\<lparr>NTMap\<rparr>"
            proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
              fix c assume "c \<in>\<^sub>\<circ> 3\<^sub>\<nat>"
              then consider \<open>c = 0\<close> | \<open>c = 1\<^sub>\<nat>\<close> | \<open>c = 2\<^sub>\<nat>\<close> 
                unfolding three by auto
              from this 0123 show 
                "\<sigma>\<lparr>NTMap\<rparr>\<lparr>c\<rparr> =
                  LK_\<sigma>23 (op_cf Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F \<TT>) \<eta>' \<FF>'\<lparr>NTMap\<rparr>\<lparr>c\<rparr>"
                by (cases, use nothing in \<open>simp_all only:\<close>)
                  (
                    cs_concl
                      cs_simp:
                        cat_ordinal_cs_simps
                        cat_cs_simps
                        cat_Kan_cs_simps
                        cat_op_simps
                        \<eta>'_NTMap_app_0
                        LK_\<sigma>23_NTMap_app_0
                        \<eta>'_NTMap_app_1
                      cs_intro: 
                        cat_ordinal_cs_intros
                        cat_Kan_cs_intros
                        cat_cs_intros
                        cat_op_intros
                        nat_omega_intros
                  )+
            qed (cs_concl cs_simp: cs_intro: cat_Kan_cs_intros V_cs_intros)+

          qed simp_all

        qed

      qed

      then have 
        "op_ntcf (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf (ntcf_id \<TT>)) :
          op_cf (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F op_cf \<TT>) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>l\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub>
          op_cf ((Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F op_cf (LK23 \<TT>))) \<circ>\<^sub>C\<^sub>F op_cf (op_cf \<KK>23) :
          op_cat (op_cat (cat_ordinal (2\<^sub>\<nat>))) \<mapsto>\<^sub>C
          op_cat (op_cat (cat_ordinal (3\<^sub>\<nat>))) \<mapsto>\<^sub>C
          op_cat (cat_Set \<alpha>)"
        by
          (
            cs_concl
              cs_simp: cat_op_simps 
              cs_intro: cat_cs_intros cat_Kan_cs_intros cat_op_intros
          )
      from is_cat_lKe.is_cat_rKe_op[OF this] prems show
        "Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F op_ntcf (ntcf_id \<TT>) :
          (Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F op_cf (LK23 \<TT>)) \<circ>\<^sub>C\<^sub>F op_cf \<KK>23 \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>r\<^sub>K\<^sub>e\<^bsub>\<alpha>\<^esub>
          Hom\<^sub>O\<^sub>.\<^sub>C\<^bsub>\<alpha>\<^esub>\<AA>(-,a) \<circ>\<^sub>C\<^sub>F op_cf \<TT> :
          op_cat (cat_ordinal (2\<^sub>\<nat>)) \<mapsto>\<^sub>C 
          op_cat (cat_ordinal (3\<^sub>\<nat>)) \<mapsto>\<^sub>C
          cat_Set \<alpha>"
        by
          (
            cs_prems
              cs_simp: cat_op_simps 
              cs_intro: cat_Kan_cs_intros cat_cs_intros cat_op_intros
          )

    qed

  qed

qed

text\<open>\newpage\<close>

end