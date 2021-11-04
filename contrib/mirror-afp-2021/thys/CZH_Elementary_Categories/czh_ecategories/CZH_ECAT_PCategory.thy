(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Product category\<close>
theory CZH_ECAT_PCategory
  imports 
    CZH_ECAT_NTCF
    CZH_ECAT_Small_Category
    CZH_Foundations.CZH_SMC_PSemicategory
begin



subsection\<open>Background\<close>


text\<open>See Chapter II-3 in \cite{mac_lane_categories_2010}.\<close>

named_theorems cat_prod_cs_simps
named_theorems cat_prod_cs_intros



subsection\<open>Product category: definition and elementary properties\<close> 

definition cat_prod :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V" 
  where "cat_prod I \<AA> =
    [
      (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Obj\<rparr>),
      (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>),
      (\<lambda>f\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>). (\<lambda>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Dom\<rparr>\<lparr>f\<lparr>i\<rparr>\<rparr>)),
      (\<lambda>f\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>). (\<lambda>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Cod\<rparr>\<lparr>f\<lparr>i\<rparr>\<rparr>)),
      (
        \<lambda>gf\<in>\<^sub>\<circ>composable_arrs (dg_prod I \<AA>).
          (\<lambda>i\<in>\<^sub>\<circ>I. vpfst gf\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<AA> i\<^esub> vpsnd gf\<lparr>i\<rparr>)
      ),
      (\<lambda>a\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Obj\<rparr>). (\<lambda>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>CId\<rparr>\<lparr>a\<lparr>i\<rparr>\<rparr>))
    ]\<^sub>\<circ>"

syntax "_PCATEGORY" :: "pttrn \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V" 
  ("(3\<Prod>\<^sub>C_\<in>\<^sub>\<circ>_./ _)" [0, 0, 10] 10)
translations "\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA>" \<rightleftharpoons> "CONST cat_prod I (\<lambda>i. \<AA>)"


text\<open>Components.\<close>

lemma cat_prod_components:
  shows "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr> = (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Obj\<rparr>)"
    and "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr> = (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>)"
    and "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Dom\<rparr> =
      (\<lambda>f\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>). (\<lambda>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Dom\<rparr>\<lparr>f\<lparr>i\<rparr>\<rparr>))"
    and "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Cod\<rparr> =
      (\<lambda>f\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>). (\<lambda>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Cod\<rparr>\<lparr>f\<lparr>i\<rparr>\<rparr>))"
    and "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Comp\<rparr> =
      (
        \<lambda>gf\<in>\<^sub>\<circ>composable_arrs (dg_prod I \<AA>).
          (\<lambda>i\<in>\<^sub>\<circ>I. vpfst gf\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<AA> i\<^esub> vpsnd gf\<lparr>i\<rparr>)
      )"
    and "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr> =
      (\<lambda>a\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Obj\<rparr>). (\<lambda>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>CId\<rparr>\<lparr>a\<lparr>i\<rparr>\<rparr>))"
  unfolding cat_prod_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma cat_smc_cat_prod[slicing_commute]: 
  "smc_prod I (\<lambda>i. cat_smc (\<AA> i)) = cat_smc (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)"
  unfolding dg_prod_def cat_smc_def cat_prod_def smc_prod_def dg_field_simps
  by (simp_all add: nat_omega_simps)

context
  fixes \<AA> \<phi> :: "V \<Rightarrow> V"
    and \<CC> :: V
begin

lemmas_with [
  where \<AA>=\<open>\<lambda>i. cat_smc (\<AA> i)\<close>, unfolded slicing_simps slicing_commute
  ]:
  cat_prod_ObjI = smc_prod_ObjI
  and cat_prod_ObjD = smc_prod_ObjD
  and cat_prod_ObjE = smc_prod_ObjE
  and cat_prod_Obj_cong = smc_prod_Obj_cong
  and cat_prod_ArrI = smc_prod_ArrI
  and cat_prod_ArrD = smc_prod_ArrD
  and cat_prod_ArrE = smc_prod_ArrE
  and cat_prod_Arr_cong = smc_prod_Arr_cong
  and cat_prod_Dom_vsv[cat_cs_intros] = smc_prod_Dom_vsv
  and cat_prod_Dom_vdomain[cat_cs_simps] = smc_prod_Dom_vdomain
  and cat_prod_Dom_app = smc_prod_Dom_app
  and cat_prod_Dom_app_component_app[cat_cs_simps] = 
    smc_prod_Dom_app_component_app
  and cat_prod_Cod_vsv[cat_cs_intros] = smc_prod_Cod_vsv
  and cat_prod_Cod_app = smc_prod_Cod_app
  and cat_prod_Cod_vdomain[cat_cs_simps] = smc_prod_Cod_vdomain
  and cat_prod_Cod_app_component_app[cat_cs_simps] = 
    smc_prod_Cod_app_component_app
  and cat_prod_Comp = smc_prod_Comp
  and cat_prod_Comp_vdomain[cat_cs_simps] = smc_prod_Comp_vdomain
  and cat_prod_Comp_app = smc_prod_Comp_app
  and cat_prod_Comp_app_component[cat_cs_simps] = 
    smc_prod_Comp_app_component
  and cat_prod_Comp_app_vdomain = smc_prod_Comp_app_vdomain
  and cat_prod_vunion_Obj_in_Obj = smc_prod_vunion_Obj_in_Obj
  and cat_prod_vdiff_vunion_Obj_in_Obj = smc_prod_vdiff_vunion_Obj_in_Obj
  and cat_prod_vunion_Arr_in_Arr = smc_prod_vunion_Arr_in_Arr
  and cat_prod_vdiff_vunion_Arr_in_Arr = smc_prod_vdiff_vunion_Arr_in_Arr

end



subsection\<open>Local assumptions for a product category\<close>

locale pcategory_base = \<Z> \<alpha> for \<alpha> I \<AA> +
  assumes pcat_categories: "i \<in>\<^sub>\<circ> I \<Longrightarrow> category \<alpha> (\<AA> i)"
    and pcat_index_in_Vset[cat_cs_intros]: "I \<in>\<^sub>\<circ> Vset \<alpha>"

lemma (in pcategory_base) pcat_categories'[cat_prod_cs_intros]:
  assumes "i \<in>\<^sub>\<circ> I" and "\<alpha>' = \<alpha>"
  shows "category \<alpha>' (\<AA> i)" 
  using assms(1) unfolding assms(2) by (rule pcat_categories)


text\<open>Rules.\<close>

lemma (in pcategory_base) pcategory_base_axioms'[cat_prod_cs_intros]: 
  assumes "\<alpha>' = \<alpha>" and "I' = I"
  shows "pcategory_base \<alpha>' I' \<AA>"
  unfolding assms by (rule pcategory_base_axioms)

mk_ide rf pcategory_base_def[unfolded pcategory_base_axioms_def]
  |intro pcategory_baseI|
  |dest pcategory_baseD[dest]|
  |elim pcategory_baseE[elim]|

lemma pcategory_base_psemicategory_baseI:
  assumes "psemicategory_base \<alpha> I (\<lambda>i. cat_smc (\<AA> i))" 
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> category \<alpha> (\<AA> i)"
  shows "pcategory_base \<alpha> I \<AA>"
proof-
  interpret psemicategory_base \<alpha> I \<open>\<lambda>i. cat_smc (\<AA> i)\<close> by (rule assms(1))
  show ?thesis
    by (intro pcategory_baseI)
      (auto simp: assms(2) psmc_index_in_Vset psmc_Obj_in_Vset psmc_Arr_in_Vset) 
qed


text\<open>Product category is a product semicategory.\<close>

context pcategory_base
begin

lemma pcat_psemicategory_base: "psemicategory_base \<alpha> I (\<lambda>i. cat_smc (\<AA> i))"
proof(intro psemicategory_baseI)
  from pcat_index_in_Vset show "I \<in>\<^sub>\<circ> Vset \<alpha>" by auto
qed (auto simp: category.cat_semicategory cat_prod_cs_intros)

interpretation psmc: psemicategory_base \<alpha> I \<open>\<lambda>i. cat_smc (\<AA> i)\<close> 
  by (rule pcat_psemicategory_base)

lemmas_with [unfolded slicing_simps slicing_commute]: 
  pcat_Obj_in_Vset = psmc.psmc_Obj_in_Vset
  and pcat_Arr_in_Vset = psmc.psmc_Arr_in_Vset
  and pcat_smc_prod_Obj_in_Vset = psmc.psmc_smc_prod_Obj_in_Vset
  and pcat_smc_prod_Arr_in_Vset = psmc.psmc_smc_prod_Arr_in_Vset
  and cat_prod_Dom_app_in_Obj[cat_cs_intros] = psmc.smc_prod_Dom_app_in_Obj
  and cat_prod_Cod_app_in_Obj[cat_cs_intros] = psmc.smc_prod_Cod_app_in_Obj
  and cat_prod_is_arrI = psmc.smc_prod_is_arrI
  and cat_prod_is_arrD[dest] = psmc.smc_prod_is_arrD
  and cat_prod_is_arrE[elim] = psmc.smc_prod_is_arrE

end

lemma cat_prod_dg_prod_is_arr: 
  "g : b \<mapsto>\<^bsub>dg_prod I \<AA>\<^esub> c \<longleftrightarrow> g : b \<mapsto>\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<^esub> c"
  unfolding is_arr_def cat_prod_def smc_prod_def dg_prod_def dg_field_simps
  by (simp add: nat_omega_simps)

lemma smc_prod_composable_arrs_dg_prod:
  "composable_arrs (dg_prod I \<AA>) = composable_arrs (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)"
  unfolding composable_arrs_def cat_prod_dg_prod_is_arr by simp


text\<open>Elementary properties.\<close>

lemma (in pcategory_base) pcat_vsubset_index_pcategory_base:
  assumes "J \<subseteq>\<^sub>\<circ> I"
  shows "pcategory_base \<alpha> J \<AA>"
proof(intro pcategory_baseI)
  show "category \<alpha> (\<AA> i)" if "i \<in>\<^sub>\<circ> J" for i 
    using that assms by (auto intro: cat_prod_cs_intros)
  from assms show "J \<in>\<^sub>\<circ> Vset \<alpha>" by (simp add: vsubset_in_VsetI cat_cs_intros)
qed auto


subsubsection\<open>Identity\<close>

lemma cat_prod_CId_vsv[cat_cs_intros]: "vsv ((\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>)"
  unfolding cat_prod_components by auto

lemma cat_prod_CId_vdomain[cat_cs_simps]: 
  "\<D>\<^sub>\<circ> ((\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>) = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>" 
  unfolding cat_prod_components by simp

lemma cat_prod_CId_app: 
  assumes "a \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"
  shows "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>a\<rparr> = (\<lambda>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>CId\<rparr>\<lparr>a\<lparr>i\<rparr>\<rparr>)" 
  using assms unfolding cat_prod_components by simp

lemma cat_prod_CId_app_component[cat_cs_simps]: 
  assumes "a \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>" and "i \<in>\<^sub>\<circ> I"
  shows "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>a\<rparr>\<lparr>i\<rparr> = \<AA> i\<lparr>CId\<rparr>\<lparr>a\<lparr>i\<rparr>\<rparr>" 
  using assms unfolding cat_prod_components by simp

lemma (in pcategory_base) cat_prod_CId_vrange: 
  "\<R>\<^sub>\<circ> ((\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>) \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>)" 
proof(intro vsubsetI)
  interpret CId: vsv \<open>((\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>)\<close> by (rule cat_prod_CId_vsv)
  fix f assume "f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> ((\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>)"
  then obtain a where f_def: "f = ((\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>)\<lparr>a\<rparr>" 
    and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>)"
    by (blast dest: CId.vrange_atD)
  then have a: "a \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>" 
    unfolding cat_prod_components by simp
  show "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>)"
    unfolding f_def cat_prod_CId_app[OF a]
  proof(rule VLambda_in_vproduct)
    fix i assume prems: "i \<in>\<^sub>\<circ> I"
    interpret \<AA>: category \<alpha> \<open>\<AA> i\<close> 
      by (simp add: \<open>i \<in>\<^sub>\<circ> I\<close> cat_cs_intros cat_prod_cs_intros)
    from prems a have "a\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>" unfolding cat_prod_components by auto
    with is_arrD(1) show "\<AA> i\<lparr>CId\<rparr>\<lparr>a\<lparr>i\<rparr>\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Arr\<rparr>" 
      by (auto intro: cat_cs_intros)
  qed
qed


subsubsection\<open>A product \<open>\<alpha>\<close>-category is a tiny \<open>\<beta>\<close>-category\<close>

lemma (in pcategory_base) pcat_tiny_category_cat_prod:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
  shows "tiny_category \<beta> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)"
proof-

  interpret \<beta>: \<Z> \<beta> by (rule assms(1))

  show ?thesis
  proof(intro tiny_categoryI, (unfold slicing_simps)?)
  
    show \<Pi>: "tiny_semicategory \<beta> (cat_smc (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i))"
      unfolding slicing_commute[symmetric]
      by 
        (
          intro psemicategory_base.psmc_tiny_semicategory_smc_prod; 
          (rule assms pcat_psemicategory_base)?
        )
    interpret \<Pi>: tiny_semicategory \<beta> \<open>cat_smc (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<close> by (rule \<Pi>)
  
    show "vfsequence (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)" unfolding cat_prod_def by auto
    show "vcard (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i) = 6\<^sub>\<nat>"
      unfolding cat_prod_def by (simp add: nat_omega_simps)
  
    show CId: "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<^esub> a"
      if a: "a \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>" for a
    proof(rule cat_prod_is_arrI)
      have [cat_cs_intros]: "a\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>" if i: "i \<in>\<^sub>\<circ> I" for i
        by (rule cat_prod_ObjD(3)[OF a i])
      from that show "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>a\<rparr>\<lparr>i\<rparr> : a\<lparr>i\<rparr> \<mapsto>\<^bsub>\<AA> i\<^esub> a\<lparr>i\<rparr>"
        if "i \<in>\<^sub>\<circ> I" for i
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps 
              cs_intro: cat_cs_intros cat_prod_cs_intros that
          )
    qed (use that in \<open>auto simp: cat_prod_components cat_prod_CId_app that\<close>)
  
    show "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<^esub> f = f"
      if "f : a \<mapsto>\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<^esub> b" for f a b
    proof(rule cat_prod_Arr_cong)
      note f = \<Pi>.smc_is_arrD[unfolded slicing_simps, OF that]
      note a = f(2) and b = f(3) and f = f(1)
      from CId[OF b] have CId_b: 
        "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>b\<rparr> : b \<mapsto>\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<^esub> b"
        by simp
      from \<Pi>.smc_Comp_is_arr[unfolded slicing_simps, OF this that] show 
        "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<^esub> f \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
        by (simp add: cat_cs_intros)
      from that show "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>" by auto
      fix i assume prems: "i \<in>\<^sub>\<circ> I"
      interpret \<AA>i: category \<alpha> \<open>\<AA> i\<close> by (simp add: prems cat_prod_cs_intros)
      from prems cat_prod_is_arrD(7)[OF that] have fi: 
        "f\<lparr>i\<rparr> : a\<lparr>i\<rparr> \<mapsto>\<^bsub>\<AA> i\<^esub> b\<lparr>i\<rparr>" 
        by auto
      from prems show "((\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<^esub> f)\<lparr>i\<rparr> = f\<lparr>i\<rparr>"
        unfolding cat_prod_Comp_app_component[OF CId_b that prems]
        unfolding cat_prod_CId_app[OF b]
        by (auto intro: \<AA>i.cat_CId_left_left[OF fi])
    qed

    show "f \<circ>\<^sub>A\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<^esub> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>b\<rparr> = f"
      if "f : b \<mapsto>\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<^esub> c" for f b c
    proof(rule cat_prod_Arr_cong)
      note f = \<Pi>.smc_is_arrD[unfolded slicing_simps, OF that]
      note b = f(2) and c = f(3) and f = f(1)
      from CId[OF b] have CId_b: 
        "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>b\<rparr> : b \<mapsto>\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<^esub> b"
        by simp
      from \<Pi>.smc_Comp_is_arr[unfolded slicing_simps, OF that this] show 
        "f \<circ>\<^sub>A\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<^esub> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>b\<rparr> \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
        by (simp add: cat_cs_intros)
      from that show "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>" by auto
      fix i assume prems: "i \<in>\<^sub>\<circ> I"
      interpret \<AA>i: category \<alpha> \<open>\<AA> i\<close> by (simp add: prems cat_prod_cs_intros)
      from prems cat_prod_is_arrD[OF that] have fi: "f\<lparr>i\<rparr> : b\<lparr>i\<rparr> \<mapsto>\<^bsub>\<AA> i\<^esub> c\<lparr>i\<rparr>"
        by simp
      from prems show "(f \<circ>\<^sub>A\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<^esub> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>b\<rparr>)\<lparr>i\<rparr> = f\<lparr>i\<rparr>"
        unfolding cat_prod_Comp_app_component[OF that CId_b prems]
        unfolding cat_prod_CId_app[OF b]
        by (auto intro: \<AA>i.cat_CId_right_left[OF fi])
    qed
  
  qed (auto simp: cat_cs_intros cat_cs_simps intro: cat_cs_intros)

qed



subsection\<open>Further local assumptions for product categories\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale pcategory = pcategory_base \<alpha> I \<AA> for \<alpha> I \<AA> +
  assumes pcat_Obj_vsubset_Vset: "J \<subseteq>\<^sub>\<circ> I \<Longrightarrow> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>J. \<AA> i)\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    and pcat_Hom_vifunion_in_Vset: 
      "\<lbrakk>
        J \<subseteq>\<^sub>\<circ> I;
        A \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>J. \<AA> i)\<lparr>Obj\<rparr>;
        B \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>J. \<AA> i)\<lparr>Obj\<rparr>;
        A \<in>\<^sub>\<circ> Vset \<alpha>;
        B \<in>\<^sub>\<circ> Vset \<alpha>
      \<rbrakk> \<Longrightarrow> (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>J. \<AA> i) a b) \<in>\<^sub>\<circ> Vset \<alpha>"


text\<open>Rules.\<close>

lemma (in pcategory) pcategory_axioms'[cat_prod_cs_intros]: 
  assumes "\<alpha>' = \<alpha>" and "I' = I"
  shows "pcategory \<alpha>' I' \<AA>"
  unfolding assms by (rule pcategory_axioms)

mk_ide rf pcategory_def[unfolded pcategory_axioms_def]
  |intro pcategoryI|
  |dest pcategoryD[dest]|
  |elim pcategoryE[elim]|

lemmas [cat_prod_cs_intros] = pcategoryD(1)

lemma pcategory_psemicategoryI:
  assumes "psemicategory \<alpha> I (\<lambda>i. cat_smc (\<AA> i))" 
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> category \<alpha> (\<AA> i)"
  shows "pcategory \<alpha> I \<AA>"
proof-
  interpret psemicategory \<alpha> I \<open>\<lambda>i. cat_smc (\<AA> i)\<close> by (rule assms(1))
  note [unfolded slicing_simps slicing_commute, cat_cs_intros] = 
    psmc_Obj_vsubset_Vset
    psmc_Hom_vifunion_in_Vset
  show ?thesis
    by (intro pcategoryI pcategory_base_psemicategory_baseI)
      (auto simp: assms(2) smc_prod_cs_intros intro!: cat_cs_intros)
qed


text\<open>Product category is a product semicategory.\<close>

context pcategory
begin

lemma pcat_psemicategory: "psemicategory \<alpha> I (\<lambda>i. cat_smc (\<AA> i))"
proof(intro psemicategoryI, unfold slicing_simps slicing_commute)
  show "psemicategory_base \<alpha> I (\<lambda>i. cat_smc (\<AA> i))" 
    by (rule pcat_psemicategory_base)
qed (auto intro!: pcat_Obj_vsubset_Vset pcat_Hom_vifunion_in_Vset)

interpretation psmc: psemicategory \<alpha> I \<open>\<lambda>i. cat_smc (\<AA> i)\<close> 
  by (rule pcat_psemicategory)

lemmas_with [unfolded slicing_simps slicing_commute]: 
  pcat_Obj_vsubset_Vset' = psmc.psmc_Obj_vsubset_Vset'
  and pcat_Hom_vifunion_in_Vset' = psmc.psmc_Hom_vifunion_in_Vset'
  and pcat_cat_prod_vunion_is_arr = psmc.psmc_smc_prod_vunion_is_arr
  and pcat_cat_prod_vdiff_vunion_is_arr = psmc.psmc_smc_prod_vdiff_vunion_is_arr

lemmas_with [unfolded slicing_simps slicing_commute]: 
  pcat_cat_prod_vunion_Comp = psmc.psmc_smc_prod_vunion_Comp
  and pcat_cat_prod_vdiff_vunion_Comp = psmc.psmc_smc_prod_vdiff_vunion_Comp

end


text\<open>Elementary properties.\<close>

lemma (in pcategory) pcat_vsubset_index_pcategory:
  assumes "J \<subseteq>\<^sub>\<circ> I"
  shows "pcategory \<alpha> J \<AA>"
proof(intro pcategoryI pcategory_psemicategoryI)
  show "cat_prod J' \<AA>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>" if \<open>J' \<subseteq>\<^sub>\<circ> J\<close> for J'
  proof-
    from that assms have "J' \<subseteq>\<^sub>\<circ> I" by simp
    then show "cat_prod J' \<AA>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>" by (rule pcat_Obj_vsubset_Vset)
  qed
  fix A B J' assume prems:
    "J' \<subseteq>\<^sub>\<circ> J"
    "A \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>J'. \<AA> i)\<lparr>Obj\<rparr>"
    "B \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>J'. \<AA> i)\<lparr>Obj\<rparr>"
    "A \<in>\<^sub>\<circ> Vset \<alpha>" 
    "B \<in>\<^sub>\<circ> Vset \<alpha>"
  show "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>J'. \<AA> i) a b) \<in>\<^sub>\<circ> Vset \<alpha>"
  proof-
    from prems(1) assms have "J' \<subseteq>\<^sub>\<circ> I" by simp
    from pcat_Hom_vifunion_in_Vset[OF this prems(2-5)] show ?thesis.
  qed
  
qed (rule pcat_vsubset_index_pcategory_base[OF assms])


subsubsection\<open>A product \<open>\<alpha>\<close>-category is an \<open>\<alpha>\<close>-category\<close>

lemma (in pcategory) pcat_category_cat_prod: "category \<alpha> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)"
proof-
  interpret tiny_category \<open>\<alpha> + \<omega>\<close> \<open>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i\<close>
    by (intro pcat_tiny_category_cat_prod) 
      (auto simp: \<Z>_\<alpha>_\<alpha>\<omega> \<Z>.intro \<Z>_Limit_\<alpha>\<omega> \<Z>_\<omega>_\<alpha>\<omega>)
  show ?thesis
    by (rule category_if_category)  
      (
        auto 
          intro!: pcat_Hom_vifunion_in_Vset pcat_Obj_vsubset_Vset
          intro: cat_cs_intros
      )
qed



subsection\<open>Local assumptions for a finite product category\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale finite_pcategory = pcategory_base \<alpha> I \<AA> for \<alpha> I \<AA> +
  assumes fin_pcat_index_vfinite: "vfinite I"


text\<open>Rules.\<close>

lemma (in finite_pcategory) finite_pcategory_axioms[cat_prod_cs_intros]: 
  assumes "\<alpha>' = \<alpha>" and "I' = I"
  shows "finite_pcategory \<alpha>' I' \<AA>"
  unfolding assms by (rule finite_pcategory_axioms)

mk_ide rf finite_pcategory_def[unfolded finite_pcategory_axioms_def]
  |intro finite_pcategoryI|
  |dest finite_pcategoryD[dest]|
  |elim finite_pcategoryE[elim]|

lemmas [cat_prod_cs_intros] = finite_pcategoryD(1)

lemma finite_pcategory_finite_psemicategoryI:
  assumes "finite_psemicategory \<alpha> I (\<lambda>i. cat_smc (\<AA> i))" 
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> category \<alpha> (\<AA> i)"
  shows "finite_pcategory \<alpha> I \<AA>"
proof-
  interpret finite_psemicategory \<alpha> I \<open>\<lambda>i. cat_smc (\<AA> i)\<close> by (rule assms(1))
  show ?thesis
    by 
      (
        intro 
          assms
          finite_pcategoryI 
          pcategory_base_psemicategory_baseI 
          finite_psemicategoryD(1)[OF assms(1)]
          fin_psmc_index_vfinite
      )
qed


subsubsection\<open>
Local assumptions for a finite product semicategory and local
assumptions for an arbitrary product semicategory
\<close>

sublocale finite_pcategory \<subseteq> pcategory \<alpha> I \<AA>
proof-
  interpret finite_psemicategory \<alpha> I \<open>\<lambda>i. cat_smc (\<AA> i)\<close>
  proof(intro finite_psemicategoryI psemicategory_baseI)
    fix i assume "i \<in>\<^sub>\<circ> I"
    then interpret \<AA>i: category \<alpha> \<open>\<AA> i\<close> by (simp add: pcat_categories)
    show "semicategory \<alpha> (cat_smc (\<AA> i))" by (simp add: \<AA>i.cat_semicategory)
  qed (auto intro!: cat_cs_intros fin_pcat_index_vfinite)
  show "pcategory \<alpha> I \<AA>"
    by (intro pcategory_psemicategoryI) 
      (simp_all add: pcat_categories psemicategory_axioms)
qed



subsection\<open>Binary union and complement\<close>

lemma (in pcategory) pcat_cat_prod_vunion_CId:
  assumes "vdisjnt J K"
    and "J \<subseteq>\<^sub>\<circ> I"
    and "K \<subseteq>\<^sub>\<circ> I"
    and "a \<in>\<^sub>\<circ> (\<Prod>\<^sub>Cj\<in>\<^sub>\<circ>J. \<AA> j)\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> (\<Prod>\<^sub>Cj\<in>\<^sub>\<circ>K. \<AA> j)\<lparr>Obj\<rparr>"
  shows 
    "(\<Prod>\<^sub>Cj\<in>\<^sub>\<circ>J. \<AA> j)\<lparr>CId\<rparr>\<lparr>a\<rparr> \<union>\<^sub>\<circ> (\<Prod>\<^sub>Cj\<in>\<^sub>\<circ>K. \<AA> j)\<lparr>CId\<rparr>\<lparr>b\<rparr> = 
      (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>J \<union>\<^sub>\<circ> K. \<AA> i)\<lparr>CId\<rparr>\<lparr>a \<union>\<^sub>\<circ> b\<rparr>"
proof-

  interpret J\<AA>: pcategory \<alpha> J \<AA> 
    using assms(2) by (simp add: pcat_vsubset_index_pcategory)
  interpret K\<AA>: pcategory \<alpha> K \<AA> 
    using assms(3) by (simp add: pcat_vsubset_index_pcategory)
  interpret JK\<AA>: pcategory \<alpha> \<open>J \<union>\<^sub>\<circ> K\<close> \<AA> 
    using assms(2,3) by (simp add: pcat_vsubset_index_pcategory)

  interpret J\<AA>': category \<alpha> \<open>cat_prod J \<AA>\<close> 
    by (rule J\<AA>.pcat_category_cat_prod)
  interpret K\<AA>': category \<alpha> \<open>cat_prod K \<AA>\<close> 
    by (rule K\<AA>.pcat_category_cat_prod)
  interpret JK\<AA>': category \<alpha> \<open>cat_prod (J \<union>\<^sub>\<circ> K) \<AA>\<close> 
    by (rule JK\<AA>.pcat_category_cat_prod)

  from assms(4) have CId_a: "cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>(\<Prod>\<^sub>Cj\<in>\<^sub>\<circ>J. \<AA> j)\<^esub> a" 
    by (auto intro: cat_cs_intros)
  from assms(5) have CId_b: "cat_prod K \<AA>\<lparr>CId\<rparr>\<lparr>b\<rparr> : b \<mapsto>\<^bsub>(\<Prod>\<^sub>Ck\<in>\<^sub>\<circ>K. \<AA> k)\<^esub> b" 
    by (auto intro: cat_cs_intros)
  have CId_a_CId_b: "cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr> \<union>\<^sub>\<circ> cat_prod K \<AA>\<lparr>CId\<rparr>\<lparr>b\<rparr> :
    a \<union>\<^sub>\<circ> b \<mapsto>\<^bsub>cat_prod (J \<union>\<^sub>\<circ> K) \<AA>\<^esub> a \<union>\<^sub>\<circ> b"
    by (rule pcat_cat_prod_vunion_is_arr[OF assms(1-3) CId_a CId_b])
  from CId_a have a: "a \<in>\<^sub>\<circ> cat_prod J \<AA>\<lparr>Obj\<rparr>" by (auto intro: cat_cs_intros)
  from CId_b have b: "b \<in>\<^sub>\<circ> cat_prod K \<AA>\<lparr>Obj\<rparr>" by (auto intro: cat_cs_intros)
  from CId_a_CId_b have ab: "a \<union>\<^sub>\<circ> b \<in>\<^sub>\<circ> cat_prod (J \<union>\<^sub>\<circ> K) \<AA>\<lparr>Obj\<rparr>" 
    by (auto intro: cat_cs_intros)

  note CId_aD = J\<AA>.cat_prod_is_arrD[OF CId_a]
    and CId_bD = K\<AA>.cat_prod_is_arrD[OF CId_b]

  show ?thesis
  proof(rule cat_prod_Arr_cong[of _ \<open>J \<union>\<^sub>\<circ> K\<close> \<AA>])
    from CId_a_CId_b show 
      "cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr> \<union>\<^sub>\<circ> cat_prod K \<AA>\<lparr>CId\<rparr>\<lparr>b\<rparr> \<in>\<^sub>\<circ> cat_prod (J \<union>\<^sub>\<circ> K) \<AA>\<lparr>Arr\<rparr>"
      by auto
    from ab show "cat_prod (J \<union>\<^sub>\<circ> K) \<AA>\<lparr>CId\<rparr>\<lparr>a \<union>\<^sub>\<circ> b\<rparr> \<in>\<^sub>\<circ> cat_prod (J \<union>\<^sub>\<circ> K) \<AA>\<lparr>Arr\<rparr>"
      by (auto intro: JK\<AA>'.cat_is_arrD(1) cat_cs_intros)
    fix i assume "i \<in>\<^sub>\<circ> J \<union>\<^sub>\<circ> K"
    then consider (iJ) \<open>i \<in>\<^sub>\<circ> J\<close> | (iK) \<open>i \<in>\<^sub>\<circ> K\<close> by auto
    then show "(cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr> \<union>\<^sub>\<circ> cat_prod K \<AA>\<lparr>CId\<rparr>\<lparr>b\<rparr>)\<lparr>i\<rparr> = 
      cat_prod (J \<union>\<^sub>\<circ> K) \<AA>\<lparr>CId\<rparr>\<lparr>a \<union>\<^sub>\<circ> b\<rparr>\<lparr>i\<rparr>"
      by cases
        (
          auto simp: 
            assms(1) 
            CId_aD(1-4) 
            CId_bD(1-4)
            cat_prod_CId_app[OF ab]
            cat_prod_CId_app[OF a]
            cat_prod_CId_app[OF b]
         )
  qed

qed

lemma (in pcategory) pcat_cat_prod_vdiff_vunion_CId:
  assumes "J \<subseteq>\<^sub>\<circ> I"
    and "a \<in>\<^sub>\<circ> (\<Prod>\<^sub>Cj\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> j)\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> (\<Prod>\<^sub>Cj\<in>\<^sub>\<circ>J. \<AA> j)\<lparr>Obj\<rparr>"
  shows 
    "(\<Prod>\<^sub>Cj\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> j)\<lparr>CId\<rparr>\<lparr>a\<rparr> \<union>\<^sub>\<circ> (\<Prod>\<^sub>Cj\<in>\<^sub>\<circ>J. \<AA> j)\<lparr>CId\<rparr>\<lparr>b\<rparr> = 
      (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>a \<union>\<^sub>\<circ> b\<rparr>"
  by 
    (
      vdiff_of_vunion' 
        rule: pcat_cat_prod_vunion_CId assms: assms(2-3) subset: assms(1)
    )



subsection\<open>Projection\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter II-3 in \cite{mac_lane_categories_2010}.\<close>

definition cf_proj :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> V" (\<open>\<pi>\<^sub>C\<close>)
  where "\<pi>\<^sub>C I \<AA> i =
    [
      (\<lambda>a\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Obj\<rparr>). a\<lparr>i\<rparr>),
      (\<lambda>f\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>). f\<lparr>i\<rparr>),
      (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i),
      \<AA> i
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_proj_components:
  shows "\<pi>\<^sub>C I \<AA> i\<lparr>ObjMap\<rparr> = (\<lambda>a\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Obj\<rparr>). a\<lparr>i\<rparr>)"
    and "\<pi>\<^sub>C I \<AA> i\<lparr>ArrMap\<rparr> = (\<lambda>f\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>). f\<lparr>i\<rparr>)"
    and "\<pi>\<^sub>C I \<AA> i\<lparr>HomDom\<rparr> = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)"
    and "\<pi>\<^sub>C I \<AA> i\<lparr>HomCod\<rparr> = \<AA> i"
  unfolding cf_proj_def dghm_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing\<close>

lemma cf_smcf_cf_proj[slicing_commute]: 
  "\<pi>\<^sub>S\<^sub>M\<^sub>C I (\<lambda>i. cat_smc (\<AA> i)) i = cf_smcf (\<pi>\<^sub>C I \<AA> i)"
  unfolding 
    cat_smc_def 
    cf_smcf_def 
    smcf_proj_def 
    cf_proj_def 
    cat_prod_def 
    smc_prod_def
    dg_prod_def
    dg_field_simps 
    dghm_field_simps 
  by (simp add: nat_omega_simps)

context pcategory
begin

interpretation psmc: psemicategory \<alpha> I \<open>\<lambda>i. cat_smc (\<AA> i)\<close> 
  by (rule pcat_psemicategory)

lemmas_with [unfolded slicing_simps slicing_commute]: 
  pcat_cf_proj_is_semifunctor = psmc.psmc_smcf_proj_is_semifunctor

end


subsubsection\<open>Projection functor is a functor\<close>

lemma (in pcategory) pcat_cf_proj_is_functor: 
  assumes "i \<in>\<^sub>\<circ> I"
  shows "\<pi>\<^sub>C I \<AA> i : (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> i"
proof(intro is_functorI)
  interpret \<AA>: category \<alpha> \<open>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<close> 
    by (simp add: pcat_category_cat_prod)
  show "vfsequence (\<pi>\<^sub>C I \<AA> i)" unfolding cf_proj_def by simp
  show "category \<alpha> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)" by (simp add: \<AA>.category_axioms)
  show "vcard (\<pi>\<^sub>C I \<AA> i) = 4\<^sub>\<nat>"
    unfolding cf_proj_def by (simp add: nat_omega_simps)
  show "\<pi>\<^sub>C I \<AA> i\<lparr>ArrMap\<rparr>\<lparr>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<AA> i\<lparr>CId\<rparr>\<lparr>\<pi>\<^sub>C I \<AA> i\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
    if "c \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>" for c
  proof-
    interpret \<AA>i: category \<alpha> \<open>\<AA> i\<close> 
      by (auto intro: assms cat_prod_cs_intros)
    from that have "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>c\<rparr> : c \<mapsto>\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<^esub> c"
      by (simp add: \<AA>.cat_CId_is_arr)
    then have "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>c\<rparr> \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>" 
      by (auto intro: cat_cs_intros)
    with assms have 
      "\<pi>\<^sub>C I \<AA> i\<lparr>ArrMap\<rparr>\<lparr>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>c\<rparr>\<lparr>i\<rparr>"
      unfolding cf_proj_components cat_prod_components by simp
    also from assms have "\<dots> = \<AA> i\<lparr>CId\<rparr>\<lparr>c\<lparr>i\<rparr>\<rparr>"
      unfolding cat_prod_CId_app[OF that] by simp
    also from that have "\<dots> = \<AA> i\<lparr>CId\<rparr>\<lparr>\<pi>\<^sub>C I \<AA> i\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
      unfolding cf_proj_components cat_prod_components by simp
    finally show 
      "\<pi>\<^sub>C I \<AA> i\<lparr>ArrMap\<rparr>\<lparr>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = \<AA> i\<lparr>CId\<rparr>\<lparr>\<pi>\<^sub>C I \<AA> i\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
      by simp
  qed
qed 
  (
    auto simp: 
      assms cf_proj_components pcat_cf_proj_is_semifunctor cat_prod_cs_intros
  ) 

lemma (in pcategory) pcat_cf_proj_is_functor':
  assumes "i \<in>\<^sub>\<circ> I" and "\<CC> = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)" and "\<DD> = \<AA> i"
  shows "\<pi>\<^sub>C I \<AA> i : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms(1) unfolding assms(2,3) by (rule pcat_cf_proj_is_functor)

lemmas [cat_cs_intros] = pcategory.pcat_cf_proj_is_functor'



subsection\<open>Category product universal property functor\<close>


subsubsection\<open>Definition and elementary properties\<close>

text\<open>
The functor that is presented in this section is used in the proof of 
the universal property of the product category later in this work.
\<close>

definition cf_up :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "cf_up I \<AA> \<CC> \<phi> =
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. (\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)),
      (\<lambda>f\<in>\<^sub>\<circ>\<CC>\<lparr>Arr\<rparr>. (\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>)),
      \<CC>,
      (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_up_components: 
  shows "cf_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr> = (\<lambda>a\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. (\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>))"
    and "cf_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr> = (\<lambda>f\<in>\<^sub>\<circ>\<CC>\<lparr>Arr\<rparr>. (\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>))"
    and "cf_up I \<AA> \<CC> \<phi>\<lparr>HomDom\<rparr> = \<CC>"
    and "cf_up I \<AA> \<CC> \<phi>\<lparr>HomCod\<rparr> = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)"
  unfolding cf_up_def dghm_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smcf_dghm_cf_up[slicing_commute]: 
  "smcf_up I (\<lambda>i. cat_smc (\<AA> i)) (cat_smc \<CC>) (\<lambda>i. cf_smcf (\<phi> i)) = 
    cf_smcf (cf_up I \<AA> \<CC> \<phi>)"
  unfolding 
    cat_smc_def 
    cf_smcf_def 
    cf_up_def 
    smcf_up_def 
    cat_prod_def 
    smc_prod_def
    dg_prod_def
    dg_field_simps 
    dghm_field_simps 
  by (simp add: nat_omega_simps)

context
  fixes \<AA> \<phi> :: "V \<Rightarrow> V"
    and \<CC> :: V
begin

lemmas_with 
  [
    where \<AA>=\<open>\<lambda>i. cat_smc (\<AA> i)\<close> and \<phi>=\<open>\<lambda>i. cf_smcf (\<phi> i)\<close> and \<CC> = \<open>cat_smc \<CC>\<close>, 
    unfolded slicing_simps slicing_commute
  ]:
  cf_up_ObjMap_vdomain[simp] = smcf_up_ObjMap_vdomain
  and cf_up_ObjMap_app = smcf_up_ObjMap_app
  and cf_up_ObjMap_app_vdomain[simp] = smcf_up_ObjMap_app_vdomain
  and cf_up_ObjMap_app_component = smcf_up_ObjMap_app_component
  and cf_up_ArrMap_vdomain[simp] = smcf_up_ArrMap_vdomain
  and cf_up_ArrMap_app = smcf_up_ArrMap_app
  and cf_up_ArrMap_app_vdomain[simp] = smcf_up_ArrMap_app_vdomain
  and cf_up_ArrMap_app_component = smcf_up_ArrMap_app_component

lemma cf_up_ObjMap_vrange:
  assumes "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> i"
  shows "\<R>\<^sub>\<circ> (cf_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"
proof
  (
    rule smcf_up_ObjMap_vrange[
      where \<AA>=\<open>\<lambda>i. cat_smc (\<AA> i)\<close> 
        and \<phi>=\<open>\<lambda>i. cf_smcf (\<phi> i)\<close> 
        and \<CC>=\<open>cat_smc \<CC>\<close>, 
      unfolded slicing_simps slicing_commute
      ]
  )
  fix i assume "i \<in>\<^sub>\<circ> I"
  then interpret is_functor \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (rule assms)
  show "cf_smcf (\<phi> i) : cat_smc \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc (\<AA> i)"
    by (rule cf_is_semifunctor)
qed

lemma cf_up_ObjMap_app_vrange:
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> i"
  shows " \<R>\<^sub>\<circ> (cf_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Obj\<rparr>)"
proof
  (
    rule smcf_up_ObjMap_app_vrange[
      where \<AA>=\<open>\<lambda>i. cat_smc (\<AA> i)\<close> 
        and \<phi>=\<open>\<lambda>i. cf_smcf (\<phi> i)\<close> 
        and \<CC>=\<open>cat_smc \<CC>\<close>, 
      unfolded slicing_simps slicing_commute
      ]
  )
  show "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by (rule assms)
  fix i assume "i \<in>\<^sub>\<circ> I"
  then interpret is_functor \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (rule assms(2))
  show "cf_smcf (\<phi> i) : cat_smc \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc (\<AA> i)"
    by (rule cf_is_semifunctor)
qed

lemma cf_up_ArrMap_vrange:
  assumes "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> i"
  shows "\<R>\<^sub>\<circ> (cf_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
proof
  (
    rule smcf_up_ArrMap_vrange[
      where \<AA>=\<open>\<lambda>i. cat_smc (\<AA> i)\<close> 
        and \<phi>=\<open>\<lambda>i. cf_smcf (\<phi> i)\<close> 
        and \<CC>=\<open>cat_smc \<CC>\<close>, 
      unfolded slicing_simps slicing_commute
      ]
  )
  fix i assume "i \<in>\<^sub>\<circ> I"
  then interpret is_functor \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (rule assms)
  show "cf_smcf (\<phi> i) : cat_smc \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc (\<AA> i)"
    by (rule cf_is_semifunctor)
qed

lemma cf_up_ArrMap_app_vrange:
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> i"
  shows " \<R>\<^sub>\<circ> (cf_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>) \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>)"
proof
  (
    rule smcf_up_ArrMap_app_vrange
      [
        where \<AA>=\<open>\<lambda>i. cat_smc (\<AA> i)\<close> 
          and \<phi>=\<open>\<lambda>i. cf_smcf (\<phi> i)\<close> 
          and \<CC>=\<open>cat_smc \<CC>\<close>, 
        unfolded slicing_simps slicing_commute
      ]
  )
  fix i assume "i \<in>\<^sub>\<circ> I"
  then interpret is_functor \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (rule assms(2))
  show "cf_smcf (\<phi> i) : cat_smc \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc (\<AA> i)"
    by (rule cf_is_semifunctor)
qed (rule assms)

end

context pcategory
begin

interpretation psmc: psemicategory \<alpha> I \<open>\<lambda>i. cat_smc (\<AA> i)\<close> 
  by (rule pcat_psemicategory)

lemmas_with [unfolded slicing_simps slicing_commute]: 
  pcat_smcf_comp_smcf_proj_smcf_up = psmc.psmc_Comp_smcf_proj_smcf_up
  and pcat_smcf_up_eq_smcf_proj = psmc.psmc_smcf_up_eq_smcf_proj

end


subsubsection\<open>Category product universal property functor is a functor\<close>

lemma (in pcategory) pcat_cf_up_is_functor:
  assumes "category \<alpha> \<CC>" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> i"
  shows "cf_up I \<AA> \<CC> \<phi> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)"
proof-
  interpret \<CC>: category \<alpha> \<CC> by (simp add: assms(1))
  interpret \<AA>: category \<alpha> \<open>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<close> by (rule pcat_category_cat_prod)
  show ?thesis
  proof(intro is_functorI)
    show "vfsequence (cf_up I \<AA> \<CC> \<phi>)" unfolding cf_up_def by simp
    show "vcard (cf_up I \<AA> \<CC> \<phi>) = 4\<^sub>\<nat>"
      unfolding cf_up_def by (simp add: nat_omega_simps)
    show "cf_smcf (cf_up I \<AA> \<CC> \<phi>) : cat_smc \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)"
      unfolding slicing_commute[symmetric]
      by (rule psemicategory.psmc_smcf_up_is_semifunctor)
        (
          auto simp: 
            assms(2)
            pcat_psemicategory 
            is_functor.cf_is_semifunctor 
            slicing_intros
        )
    show "cf_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = 
      (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>cf_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
      if "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for c
    proof(rule cat_prod_Arr_cong)
      from that is_arrD(1) have CId_c: "\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" 
        by (auto intro: cat_cs_intros)
      from CId_c cf_up_ArrMap_vrange[OF assms(2), simplified]
      show "cf_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
        unfolding cf_up_components by force
      have cf_up_\<phi>_c: "cf_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"
        unfolding cat_prod_components
      proof(intro vproductI ballI)
        fix i assume prems: "i \<in>\<^sub>\<circ> I"
        interpret \<phi>: is_functor \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (simp add: prems assms(2))
        from that show  "cf_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>"
          unfolding cf_up_ObjMap_app_component[OF that prems] 
          by (auto intro: cat_cs_intros)
      qed (simp_all add: cf_up_ObjMap_app that cf_up_ObjMap_app[OF that])
      from \<AA>.cat_CId_is_arr[OF this] show 
        "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>cf_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr> \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
        by auto
      fix i assume prems: "i \<in>\<^sub>\<circ> I"
      interpret \<phi>: is_functor \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (simp add: prems assms(2))
      from cf_up_\<phi>_c prems show 
        "cf_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr>\<lparr>i\<rparr> =
          (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>CId\<rparr>\<lparr>cf_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>\<lparr>i\<rparr>"
        unfolding cf_up_ArrMap_app_component[OF CId_c prems] cat_prod_components
        by 
          (
            simp add: 
              that cf_up_ObjMap_app_component[OF that prems] \<phi>.cf_ObjMap_CId 
          )
    qed 
  qed (auto simp: cf_up_components cat_cs_intros)
qed


subsubsection\<open>Further properties\<close>

lemma (in pcategory) pcat_Comp_cf_proj_cf_up: 
  assumes "category \<alpha> \<CC>" 
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> i" 
    and "i \<in>\<^sub>\<circ> I" 
  shows "\<phi> i = \<pi>\<^sub>C I \<AA> i \<circ>\<^sub>C\<^sub>F (cf_up I \<AA> \<CC> \<phi>)"
proof-
  interpret \<phi>: is_functor \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (rule assms(2)[OF assms(3)])
  interpret \<pi>: is_functor \<alpha> \<open>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<close> \<open>\<AA> i\<close> \<open>\<pi>\<^sub>C I \<AA> i\<close>
    by (simp add: assms(3) pcat_cf_proj_is_functor)
  interpret up: is_functor \<alpha> \<CC> \<open>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<close> \<open>cf_up I \<AA> \<CC> \<phi>\<close>
    by (simp add: assms(2) \<phi>.HomDom.category_axioms pcat_cf_up_is_functor)
  show ?thesis
  proof(rule cf_smcf_eqI)
    show "\<pi>\<^sub>C I \<AA> i \<circ>\<^sub>C\<^sub>F cf_up I \<AA> \<CC> \<phi> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> i" 
      by (auto intro: cat_cs_intros)
    from assms show "cf_smcf (\<phi> i) = cf_smcf (\<pi>\<^sub>C I \<AA> i \<circ>\<^sub>C\<^sub>F cf_up I \<AA> \<CC> \<phi>)"
      unfolding slicing_simps slicing_commute[symmetric]
      by 
        (
          intro pcat_smcf_comp_smcf_proj_smcf_up[
            where \<phi>=\<open>\<lambda>i. cf_smcf (\<phi> i)\<close>, unfolded slicing_commute[symmetric]
            ]
        )
        (auto simp: is_functor.cf_is_semifunctor)
  qed (auto intro: cat_cs_intros)
qed

lemma (in pcategory) pcat_cf_up_eq_cf_proj:
  assumes "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)"
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i = \<pi>\<^sub>C I \<AA> i \<circ>\<^sub>C\<^sub>F \<FF>"
  shows "cf_up I \<AA> \<CC> \<phi> = \<FF>"
proof(rule cf_smcf_eqI)
  interpret \<FF>: is_functor \<alpha> \<CC> \<open>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<close> \<FF> by (rule assms(1))
  show "cf_up I \<AA> \<CC> \<phi> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)"
  proof(rule pcat_cf_up_is_functor)
    fix i assume prems: "i \<in>\<^sub>\<circ> I"
    then interpret \<pi>: is_functor \<alpha> \<open>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<close> \<open>\<AA> i\<close> \<open>\<pi>\<^sub>C I \<AA> i\<close>
      by (rule pcat_cf_proj_is_functor)
    show "\<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> i" 
      unfolding assms(2)[OF prems] by (auto intro: cat_cs_intros)
  qed (auto intro: cat_cs_intros)
  show "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)" by (rule assms(1))
  from assms show "cf_smcf (cf_up I \<AA> \<CC> \<phi>) = cf_smcf \<FF>"
    unfolding slicing_commute[symmetric]
    by (intro pcat_smcf_up_eq_smcf_proj) (auto simp: slicing_commute)
qed simp_all



subsection\<open>Prodfunctor with respect to a fixed argument\<close>

text\<open>
A prodfunctor is a functor whose domain is a product category. 
It is a generalization of the concept of the bifunctor,
as presented in Chapter II-3 in \cite{mac_lane_categories_2010}.  
\<close>

definition prodfunctor_proj :: "V \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "prodfunctor_proj \<SS> I \<AA> \<DD> J c =
    [
      (\<lambda>b\<in>\<^sub>\<circ>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> i)\<lparr>Obj\<rparr>. \<SS>\<lparr>ObjMap\<rparr>\<lparr>b \<union>\<^sub>\<circ> c\<rparr>),
      (\<lambda>f\<in>\<^sub>\<circ>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> i)\<lparr>Arr\<rparr>. \<SS>\<lparr>ArrMap\<rparr>\<lparr>f \<union>\<^sub>\<circ> (\<Prod>\<^sub>Cj\<in>\<^sub>\<circ>J. \<AA> j)\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr>),
      (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> i),
      \<DD>
    ]\<^sub>\<circ>"

syntax "_PPRODFUNCTOR_PROJ" :: "V \<Rightarrow> pttrn \<Rightarrow> V \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" 
  (\<open>(_\<^bsub>(3\<Prod>\<^sub>C_\<in>\<^sub>\<circ>_-\<^sub>\<circ>_./_),_\<^esub>/'(/-,_/'))\<close> [51, 51, 51, 51, 51, 51, 51] 51)
translations "\<SS>\<^bsub>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I-\<^sub>\<circ>J. \<AA>,\<DD>\<^esub>(-,c)" \<rightleftharpoons> 
  "CONST prodfunctor_proj \<SS> I (\<lambda>i. \<AA>) \<DD> J c"


text\<open>Components.\<close>

lemma prodfunctor_proj_components:
  shows "(\<SS>\<^bsub>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> i,\<DD>\<^esub>(-,c))\<lparr>ObjMap\<rparr> = 
      (\<lambda>b\<in>\<^sub>\<circ>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> i)\<lparr>Obj\<rparr>. \<SS>\<lparr>ObjMap\<rparr>\<lparr>b \<union>\<^sub>\<circ> c\<rparr>)"
    and "(\<SS>\<^bsub>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> i,\<DD>\<^esub>(-,c))\<lparr>ArrMap\<rparr> = 
      (\<lambda>f\<in>\<^sub>\<circ>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> i)\<lparr>Arr\<rparr>. \<SS>\<lparr>ArrMap\<rparr>\<lparr>f \<union>\<^sub>\<circ> (\<Prod>\<^sub>Cj\<in>\<^sub>\<circ>J. \<AA> j)\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr>)"
    and "(\<SS>\<^bsub>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> i,\<DD>\<^esub>(-,c))\<lparr>HomDom\<rparr> = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> i)"
    and "(\<SS>\<^bsub>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> i,\<DD>\<^esub>(-,c))\<lparr>HomCod\<rparr> = \<DD>"
  unfolding prodfunctor_proj_def dghm_field_simps
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

mk_VLambda prodfunctor_proj_components(1)
  |vsv prodfunctor_proj_ObjMap_vsv[cat_cs_intros]|
  |vdomain prodfunctor_proj_ObjMap_vdomain[cat_cs_simps]|
  |app prodfunctor_proj_ObjMap_app[cat_cs_simps]|


subsubsection\<open>Arrow map\<close>

mk_VLambda prodfunctor_proj_components(2)
  |vsv prodfunctor_proj_ArrMap_vsv[cat_cs_intros]|
  |vdomain prodfunctor_proj_ArrMap_vdomain[cat_cs_simps]|
  |app  prodfunctor_proj_ArrMap_app[cat_cs_simps]|


subsubsection\<open>Prodfunctor with respect to a fixed argument is a functor\<close>

lemma (in pcategory) pcat_prodfunctor_proj_is_functor: 
  assumes "\<SS> : (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" 
    and "c \<in>\<^sub>\<circ> (\<Prod>\<^sub>Cj\<in>\<^sub>\<circ>J. \<AA> j)\<lparr>Obj\<rparr>"
    and "J \<subseteq>\<^sub>\<circ> I"
  shows "(\<SS>\<^bsub>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> i,\<DD>\<^esub>(-,c)) : (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> i) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
proof-

  interpret is_functor \<alpha> \<open>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<close> \<DD> \<SS> by (rule assms(1))
  interpret \<AA>: pcategory \<alpha> J \<AA>
    using assms(3) by (intro pcat_vsubset_index_pcategory) auto
  interpret J_\<AA>: category \<alpha> \<open>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>J. \<AA> i\<close> by (rule \<AA>.pcat_category_cat_prod)
  interpret IJ: pcategory \<alpha> \<open>I -\<^sub>\<circ> J\<close> \<AA>
    using assms(3) by (intro pcat_vsubset_index_pcategory) auto
  interpret IJ_\<AA>: category \<alpha> \<open>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> i\<close>
    by (rule IJ.pcat_category_cat_prod)

  let ?IJ\<AA> = \<open>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> i)\<close>

  from assms(2) have "c \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>j\<in>\<^sub>\<circ>J. \<AA> j\<lparr>Obj\<rparr>)"
    unfolding cat_prod_components by simp
  then have "(\<Prod>\<^sub>\<circ>j\<in>\<^sub>\<circ>J. \<AA> j\<lparr>Obj\<rparr>) \<noteq> 0" by (auto intro!: cat_cs_intros)

  show ?thesis
  proof(intro is_functorI', unfold prodfunctor_proj_components)

    show "vfsequence (prodfunctor_proj \<SS> I \<AA> \<DD> J c)"
      unfolding prodfunctor_proj_def by simp
    show "vcard (prodfunctor_proj \<SS> I \<AA> \<DD> J c) = 4\<^sub>\<nat>"
      unfolding prodfunctor_proj_def by (simp add: nat_omega_simps)

    show "\<R>\<^sub>\<circ> (\<lambda>b\<in>\<^sub>\<circ>?IJ\<AA>\<lparr>Obj\<rparr>. \<SS>\<lparr>ObjMap\<rparr>\<lparr>b \<union>\<^sub>\<circ> c\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
    proof(intro vsubsetI)
      fix x assume "x \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<lambda>b\<in>\<^sub>\<circ>?IJ\<AA>\<lparr>Obj\<rparr>. \<SS>\<lparr>ObjMap\<rparr>\<lparr>b \<union>\<^sub>\<circ> c\<rparr>)"
      then obtain b where x_def: "x = \<SS>\<lparr>ObjMap\<rparr>\<lparr>b \<union>\<^sub>\<circ> c\<rparr>" and b: "b \<in>\<^sub>\<circ> ?IJ\<AA>\<lparr>Obj\<rparr>"  
        by auto
      have "b \<union>\<^sub>\<circ> c \<in>\<^sub>\<circ> cat_prod I \<AA>\<lparr>Obj\<rparr>"
      proof(rule cat_prod_vdiff_vunion_Obj_in_Obj)
        show "b \<in>\<^sub>\<circ> ?IJ\<AA>\<lparr>Obj\<rparr>" by (rule b)
      qed (intro assms(2,3))+
      then show "x \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>" unfolding x_def by (auto intro: cat_cs_intros)
    qed

    show is_arr:
      "(\<lambda>f\<in>\<^sub>\<circ>?IJ\<AA>\<lparr>Arr\<rparr>. \<SS>\<lparr>ArrMap\<rparr>\<lparr>f \<union>\<^sub>\<circ> cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr>)\<lparr>f\<rparr> : 
        (\<lambda>b\<in>\<^sub>\<circ>?IJ\<AA>\<lparr>Obj\<rparr>. \<SS>\<lparr>ObjMap\<rparr>\<lparr>b \<union>\<^sub>\<circ> c\<rparr>)\<lparr>a\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> 
        (\<lambda>b\<in>\<^sub>\<circ>?IJ\<AA>\<lparr>Obj\<rparr>. \<SS>\<lparr>ObjMap\<rparr>\<lparr>b \<union>\<^sub>\<circ> c\<rparr>)\<lparr>b\<rparr>"
      (is \<open>?V_f: ?V_a \<mapsto>\<^bsub>\<DD>\<^esub> ?V_b\<close>)
      if "f : a \<mapsto>\<^bsub>?IJ\<AA>\<^esub> b" for f a b
    proof-
      let ?fc = \<open>f \<union>\<^sub>\<circ> cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<close>
      have "?fc : a \<union>\<^sub>\<circ> c \<mapsto>\<^bsub>cat_prod I \<AA>\<^esub> b \<union>\<^sub>\<circ> c"
      proof(rule pcat_cat_prod_vdiff_vunion_is_arr)
        show "f : a \<mapsto>\<^bsub>?IJ\<AA>\<^esub> b" by (rule that)
      qed (auto simp: assms cat_cs_intros)
      then have "\<SS>\<lparr>ArrMap\<rparr>\<lparr>?fc\<rparr> : \<SS>\<lparr>ObjMap\<rparr>\<lparr>a \<union>\<^sub>\<circ> c\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> \<SS>\<lparr>ObjMap\<rparr>\<lparr>b \<union>\<^sub>\<circ> c\<rparr>"
        by (auto intro: cat_cs_intros)
      moreover from that have "f \<in>\<^sub>\<circ> ?IJ\<AA>\<lparr>Arr\<rparr>" "a \<in>\<^sub>\<circ> ?IJ\<AA>\<lparr>Obj\<rparr>" "b \<in>\<^sub>\<circ> ?IJ\<AA>\<lparr>Obj\<rparr>"
        by (auto intro: cat_cs_intros) 
      ultimately show ?thesis by simp
    qed

    show 
      "(\<lambda>f\<in>\<^sub>\<circ>?IJ\<AA>\<lparr>Arr\<rparr>. \<SS>\<lparr>ArrMap\<rparr>\<lparr>f \<union>\<^sub>\<circ> cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr>)\<lparr>g \<circ>\<^sub>A\<^bsub>?IJ\<AA>\<^esub> f\<rparr> =
      (\<lambda>f\<in>\<^sub>\<circ>?IJ\<AA>\<lparr>Arr\<rparr>. \<SS>\<lparr>ArrMap\<rparr>\<lparr>f \<union>\<^sub>\<circ> cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr>)\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> 
      (\<lambda>f\<in>\<^sub>\<circ>?IJ\<AA>\<lparr>Arr\<rparr>. \<SS>\<lparr>ArrMap\<rparr>\<lparr>f \<union>\<^sub>\<circ> cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr>)\<lparr>f\<rparr>"
      if "g : b' \<mapsto>\<^bsub>?IJ\<AA>\<^esub> c'" and "f : a' \<mapsto>\<^bsub>?IJ\<AA>\<^esub> b'" for g b' c' f a'
    proof-
      from that have gf: "g \<circ>\<^sub>A\<^bsub>?IJ\<AA>\<^esub> f : a' \<mapsto>\<^bsub>?IJ\<AA>\<^esub> c'" 
        by (auto intro: cat_cs_intros)
      from assms(2) have CId_c: "cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr> : c \<mapsto>\<^bsub>cat_prod J \<AA>\<^esub> c" 
        by (auto intro: cat_cs_intros)
      then have [simp]:  
        "cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr> \<circ>\<^sub>A\<^bsub>cat_prod J \<AA>\<^esub> cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr> = 
          cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>"
        by (auto simp: cat_cs_simps)
      from assms(3) that(1) CId_c have g_CId_c:
        "g \<union>\<^sub>\<circ> cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr> : b' \<union>\<^sub>\<circ> c \<mapsto>\<^bsub>cat_prod I \<AA>\<^esub> c' \<union>\<^sub>\<circ> c"
        by (rule pcat_cat_prod_vdiff_vunion_is_arr)
      from assms(3) that(2) CId_c have f_CId_c:
        "f \<union>\<^sub>\<circ> cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr> : a' \<union>\<^sub>\<circ> c \<mapsto>\<^bsub>cat_prod I \<AA>\<^esub> b' \<union>\<^sub>\<circ> c"
        by (rule pcat_cat_prod_vdiff_vunion_is_arr)
      have 
        "\<SS>\<lparr>ArrMap\<rparr>\<lparr>(g \<circ>\<^sub>A\<^bsub>?IJ\<AA>\<^esub> f) \<union>\<^sub>\<circ> cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = 
          \<SS>\<lparr>ArrMap\<rparr>\<lparr>g \<union>\<^sub>\<circ> cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub>
          \<SS>\<lparr>ArrMap\<rparr>\<lparr>f \<union>\<^sub>\<circ> cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr>"
        unfolding 
          pcat_cat_prod_vdiff_vunion_Comp[
            OF assms(3) that(1) CId_c that(2) CId_c, simplified
            ]
        by (intro cf_ArrMap_Comp[OF g_CId_c f_CId_c])
      moreover from gf have "g \<circ>\<^sub>A\<^bsub>?IJ\<AA>\<^esub> f \<in>\<^sub>\<circ> ?IJ\<AA>\<lparr>Arr\<rparr>" by auto
      moreover from that have "g \<in>\<^sub>\<circ> ?IJ\<AA>\<lparr>Arr\<rparr>" "f \<in>\<^sub>\<circ> ?IJ\<AA>\<lparr>Arr\<rparr>" by auto
      ultimately show ?thesis by simp
    qed

    show 
      "(\<lambda>f\<in>\<^sub>\<circ>?IJ\<AA>\<lparr>Arr\<rparr>. \<SS>\<lparr>ArrMap\<rparr>\<lparr>f \<union>\<^sub>\<circ> cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr>)\<lparr>?IJ\<AA>\<lparr>CId\<rparr>\<lparr>c'\<rparr>\<rparr> = 
        \<DD>\<lparr>CId\<rparr>\<lparr>(\<lambda>b\<in>\<^sub>\<circ>?IJ\<AA>\<lparr>Obj\<rparr>. \<SS>\<lparr>ObjMap\<rparr>\<lparr>b \<union>\<^sub>\<circ> c\<rparr>)\<lparr>c'\<rparr>\<rparr>"
      if "c' \<in>\<^sub>\<circ> ?IJ\<AA>\<lparr>Obj\<rparr>" for c'
    proof-
      have "?IJ\<AA>\<lparr>CId\<rparr>\<lparr>c'\<rparr> \<union>\<^sub>\<circ> cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr> = cat_prod I \<AA>\<lparr>CId\<rparr>\<lparr>c' \<union>\<^sub>\<circ> c\<rparr>"
        unfolding pcat_cat_prod_vdiff_vunion_CId[OF assms(3) that assms(2)] ..
      moreover from assms(3) that assms(2) have "c' \<union>\<^sub>\<circ> c \<in>\<^sub>\<circ> cat_prod I \<AA>\<lparr>Obj\<rparr>"
        by (rule cat_prod_vdiff_vunion_Obj_in_Obj)
      ultimately have "\<SS>\<lparr>ArrMap\<rparr>\<lparr>?IJ\<AA>\<lparr>CId\<rparr>\<lparr>c'\<rparr> \<union>\<^sub>\<circ> cat_prod J \<AA>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> =
        \<DD>\<lparr>CId\<rparr>\<lparr>\<SS>\<lparr>ObjMap\<rparr>\<lparr>c' \<union>\<^sub>\<circ> c\<rparr>\<rparr>"
        by (auto intro: cat_cs_intros) 
      moreover from that have CId_c': "?IJ\<AA>\<lparr>CId\<rparr>\<lparr>c'\<rparr> \<in>\<^sub>\<circ> ?IJ\<AA>\<lparr>Arr\<rparr>"
        by (auto dest!: IJ_\<AA>.cat_CId_is_arr)
      ultimately show ?thesis by (simp add: that)
    qed

  qed (auto intro: cat_cs_intros) 

qed

lemma (in pcategory) pcat_prodfunctor_proj_is_functor': 
  assumes "\<SS> : (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" 
    and "c \<in>\<^sub>\<circ> (\<Prod>\<^sub>Cj\<in>\<^sub>\<circ>J. \<AA> j)\<lparr>Obj\<rparr>"
    and "J \<subseteq>\<^sub>\<circ> I"
    and "\<AA>' = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> i)"
    and "\<BB>' = \<DD>"
  shows "(\<SS>\<^bsub>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> i,\<DD>\<^esub>(-,c)) : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  using assms(1-3)
  unfolding assms(4,5)
  by (rule pcat_prodfunctor_proj_is_functor)

lemmas [cat_cs_intros] = pcategory.pcat_prodfunctor_proj_is_functor'



subsection\<open>Singleton category\<close>


subsubsection\<open>Slicing\<close>

context
  fixes \<CC> :: V
begin

lemmas_with [where \<CC>=\<open>cat_smc \<CC>\<close>, unfolded slicing_simps slicing_commute]:
  cat_singleton_ObjI = smc_singleton_ObjI
  and cat_singleton_ObjE = smc_singleton_ObjE
  and cat_singleton_ArrI = smc_singleton_ArrI
  and cat_singleton_ArrE = smc_singleton_ArrE

end

context category
begin

interpretation smc: semicategory \<alpha> \<open>cat_smc \<CC>\<close> by (rule cat_semicategory)

lemmas_with [unfolded slicing_simps slicing_commute]:
  cat_finite_psemicategory_cat_singleton = 
    smc.smc_finite_psemicategory_smc_singleton
  and cat_singleton_is_arrI = smc.smc_singleton_is_arrI
  and cat_singleton_is_arrD = smc.smc_singleton_is_arrD
  and cat_singleton_is_arrE = smc.smc_singleton_is_arrE

end


subsubsection\<open>Identity\<close>

lemma cat_singleton_CId_app: 
  assumes "set {\<langle>j, a\<rangle>} \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {j}. \<CC>)\<lparr>Obj\<rparr>"
  shows "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {j}. \<CC>)\<lparr>CId\<rparr>\<lparr>set {\<langle>j, a\<rangle>}\<rparr> = set {\<langle>j, \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>\<rangle>}"
  using assms unfolding cat_prod_components VLambda_vsingleton by simp


subsubsection\<open>Singleton category is a category\<close>

lemma (in category) cat_finite_pcategory_cat_singleton: 
  assumes "j \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "finite_pcategory \<alpha> (set {j}) (\<lambda>i. \<CC>)"
  by 
    (
      auto intro: 
        assms
        category_axioms 
        finite_pcategory_finite_psemicategoryI 
        cat_finite_psemicategory_cat_singleton 
    )

lemma (in category) cat_category_cat_singleton:
  assumes "j \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "category \<alpha> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {j}. \<CC>)"
proof-
  interpret finite_pcategory \<alpha> \<open>set {j}\<close> \<open>\<lambda>i. \<CC>\<close>
    using assms by (rule cat_finite_pcategory_cat_singleton)
  show ?thesis by (rule pcat_category_cat_prod)
qed



subsection\<open>Singleton functor\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition cf_singleton :: "V \<Rightarrow> V \<Rightarrow> V"
  where "cf_singleton j \<CC> =
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. set {\<langle>j, a\<rangle>}),
      (\<lambda>f\<in>\<^sub>\<circ>\<CC>\<lparr>Arr\<rparr>. set {\<langle>j, f\<rangle>}),
      \<CC>,
      (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {j}. \<CC>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_singleton_components:
  shows "cf_singleton j \<CC>\<lparr>ObjMap\<rparr> = (\<lambda>a\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. set {\<langle>j, a\<rangle>})"
    and "cf_singleton j \<CC>\<lparr>ArrMap\<rparr> = (\<lambda>f\<in>\<^sub>\<circ>\<CC>\<lparr>Arr\<rparr>. set {\<langle>j, f\<rangle>})"
    and "cf_singleton j \<CC>\<lparr>HomDom\<rparr> = \<CC>"
    and "cf_singleton j \<CC>\<lparr>HomCod\<rparr> = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {j}. \<CC>)"
  unfolding cf_singleton_def dghm_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma cf_smcf_cf_singleton[slicing_commute]: 
  "smcf_singleton j (cat_smc \<CC>)= cf_smcf (cf_singleton j \<CC>)"
  unfolding smcf_singleton_def cf_singleton_def slicing_simps slicing_commute
  by 
    (
      simp add: 
        nat_omega_simps dghm_field_simps dg_field_simps cat_smc_def cf_smcf_def
     )

context
  fixes \<CC> :: V
begin

lemmas_with [where \<CC>=\<open>cat_smc \<CC>\<close>, unfolded slicing_simps slicing_commute]:
  cf_singleton_ObjMap_vsv[cat_cs_intros] = smcf_singleton_ObjMap_vsv
  and cf_singleton_ObjMap_vdomain[cat_cs_simps] = smcf_singleton_ObjMap_vdomain
  and cf_singleton_ObjMap_vrange = smcf_singleton_ObjMap_vrange
  and cf_singleton_ObjMap_app[cat_prod_cs_simps] = smcf_singleton_ObjMap_app
  and cf_singleton_ArrMap_vsv[cat_cs_intros] = smcf_singleton_ArrMap_vsv
  and cf_singleton_ArrMap_vdomain[cat_cs_simps] = smcf_singleton_ArrMap_vdomain
  and cf_singleton_ArrMap_vrange = smcf_singleton_ArrMap_vrange
  and cf_singleton_ArrMap_app[cat_prod_cs_simps] = smcf_singleton_ArrMap_app

end


subsubsection\<open>Singleton functor is an isomorphism of categories\<close>

lemma (in category) cat_cf_singleton_is_functor:
  assumes "j \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "cf_singleton j \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {j}. \<CC>)"
proof(intro is_iso_functorI is_functorI)
  from assms show smcf_singleton: "cf_smcf (cf_singleton j \<CC>) : 
    cat_smc \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> cat_smc (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {j}. \<CC>)"
    unfolding slicing_commute[symmetric]
    by (intro semicategory.smc_smcf_singleton_is_iso_semifunctor) 
      (auto intro: smc_cs_intros slicing_intros)
  show "vfsequence (cf_singleton j \<CC>)" unfolding cf_singleton_def by simp
  show "vcard (cf_singleton j \<CC>) = 4\<^sub>\<nat>"
    unfolding cf_singleton_def by (simp add: nat_omega_simps)
  show "cf_smcf (cf_singleton j \<CC>) : 
    cat_smc \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> cat_smc (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {j}. \<CC>)"
    by (intro is_iso_semifunctor.axioms(1) smcf_singleton)
  show "cf_singleton j \<CC>\<lparr>ArrMap\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = 
    (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {j}. \<CC>)\<lparr>CId\<rparr>\<lparr>cf_singleton j \<CC>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>"
    if "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for c 
  proof-
    from that have CId_c: "\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr> : c \<mapsto>\<^bsub>\<CC>\<^esub> c" by (auto simp: cat_cs_intros)
    have "set {\<langle>j, c\<rangle>} \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {j}. \<CC>)\<lparr>Obj\<rparr>"
      by (simp add: cat_singleton_ObjI that)
    with that have "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {j}. \<CC>)\<lparr>CId\<rparr>\<lparr>cf_singleton j \<CC>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr> = 
      set {\<langle>j, \<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rangle>}"
      by (simp add: cf_singleton_ObjMap_app cat_singleton_CId_app)
    moreover from CId_c have 
      "cf_singleton j \<CC>\<lparr>ArrMap\<rparr>\<lparr>\<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr> = set {\<langle>j, \<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rangle>}"
      by (auto simp: cf_singleton_ArrMap_app cat_cs_intros)
    ultimately show ?thesis by simp
  qed
qed 
  (
    auto simp: 
      cat_cs_intros assms cat_category_cat_singleton cf_singleton_components 
  )



subsection\<open>Product of two categories\<close>


subsubsection\<open>Definition and elementary properties.\<close>


text\<open>See Chapter II-3 in \cite{mac_lane_categories_2010}.\<close>

definition cat_prod_2 :: "V \<Rightarrow> V \<Rightarrow> V" (infixr \<open>\<times>\<^sub>C\<close> 80)
  where "\<AA> \<times>\<^sub>C \<BB> \<equiv> cat_prod (2\<^sub>\<nat>) (\<lambda>i. if i = 0 then \<AA> else \<BB>)"


text\<open>Slicing.\<close>
  
lemma cat_smc_cat_prod_2[slicing_commute]: 
  "cat_smc \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C cat_smc \<BB> = cat_smc (\<AA> \<times>\<^sub>C \<BB>)"
  unfolding cat_prod_2_def smc_prod_2_def slicing_commute[symmetric] if_distrib
  by simp

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "category \<alpha> \<AA>" and \<BB>: "category \<alpha> \<BB>"
begin

interpretation \<AA>: category \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: category \<alpha> \<BB> by (rule \<BB>)

lemmas_with 
  [
    where \<AA>=\<open>cat_smc \<AA>\<close> and \<BB>=\<open>cat_smc \<BB>\<close>, 
    unfolded slicing_simps slicing_commute, 
    OF \<AA>.cat_semicategory \<BB>.cat_semicategory
  ]:
  cat_prod_2_ObjI = smc_prod_2_ObjI 
  and cat_prod_2_ObjI'[cat_prod_cs_intros] = smc_prod_2_ObjI'
  and cat_prod_2_ObjE = smc_prod_2_ObjE
  and cat_prod_2_ArrI = smc_prod_2_ArrI
  and cat_prod_2_ArrI'[cat_prod_cs_intros] = smc_prod_2_ArrI'
  and cat_prod_2_ArrE = smc_prod_2_ArrE
  and cat_prod_2_is_arrI = smc_prod_2_is_arrI
  and cat_prod_2_is_arrI'[cat_prod_cs_intros] = smc_prod_2_is_arrI'
  and cat_prod_2_is_arrE = smc_prod_2_is_arrE
  and cat_prod_2_Dom_vsv = smc_prod_2_Dom_vsv
  and cat_prod_2_Dom_vdomain[cat_cs_simps] = smc_prod_2_Dom_vdomain
  and cat_prod_2_Dom_app[cat_prod_cs_simps] = smc_prod_2_Dom_app
  and cat_prod_2_Dom_vrange = smc_prod_2_Dom_vrange
  and cat_prod_2_Cod_vsv = smc_prod_2_Cod_vsv
  and cat_prod_2_Cod_vdomain[cat_cs_simps] = smc_prod_2_Cod_vdomain
  and cat_prod_2_Cod_app[cat_prod_cs_simps] = smc_prod_2_Cod_app
  and cat_prod_2_Cod_vrange = smc_prod_2_Cod_vrange
  and cat_prod_2_op_cat_cat_Obj[cat_op_simps] = smc_prod_2_op_smc_smc_Obj
  and cat_prod_2_cat_op_cat_Obj[cat_op_simps] = smc_prod_2_smc_op_smc_Obj
  and cat_prod_2_op_cat_cat_Arr[cat_op_simps] = smc_prod_2_op_smc_smc_Arr
  and cat_prod_2_cat_op_cat_Arr[cat_op_simps] = smc_prod_2_smc_op_smc_Arr

lemmas_with 
  [
    where \<AA>=\<open>cat_smc \<AA>\<close> and \<BB>=\<open>cat_smc \<BB>\<close>, 
    unfolded slicing_simps slicing_commute, 
    OF \<AA>.cat_semicategory \<BB>.cat_semicategory
  ]:
  cat_prod_2_Comp_app[cat_prod_cs_simps] = smc_prod_2_Comp_app

end


subsubsection\<open>Product of two categories is a category\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "category \<alpha> \<AA>" and \<BB>: "category \<alpha> \<BB>"
begin

interpretation \<Z> \<alpha> by (rule categoryD[OF \<AA>])
interpretation \<AA>: category \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: category \<alpha> \<BB> by (rule \<BB>)

lemma finite_pcategory_cat_prod_2: "finite_pcategory \<alpha> (2\<^sub>\<nat>) (if2 \<AA> \<BB>)"
proof(intro finite_pcategoryI pcategory_baseI)
  from Axiom_of_Infinity show z1_in_Vset: "2\<^sub>\<nat> \<in>\<^sub>\<circ> Vset \<alpha>" by blast
  show "category \<alpha> (i = 0 ? \<AA> : \<BB>)" if "i \<in>\<^sub>\<circ> 2\<^sub>\<nat>" for i
    by (auto simp: cat_cs_intros)
qed auto

interpretation finite_pcategory \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 \<AA> \<BB>\<close>
  by (intro finite_pcategory_cat_prod_2 \<AA> \<BB>)

lemma category_cat_prod_2[cat_cs_intros]: "category \<alpha> (\<AA> \<times>\<^sub>C \<BB>)"
  unfolding cat_prod_2_def by (rule pcat_category_cat_prod)

end


subsubsection\<open>Identity\<close>

lemma cat_prod_2_CId_vsv[cat_cs_intros]: "vsv ((\<AA> \<times>\<^sub>C \<BB>)\<lparr>CId\<rparr>)"
  unfolding cat_prod_2_def cat_prod_components by simp

lemma cat_prod_2_CId_vdomain[cat_cs_simps]: 
  "\<D>\<^sub>\<circ> ((\<AA> \<times>\<^sub>C \<BB>)\<lparr>CId\<rparr>) = (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
  unfolding cat_prod_2_def cat_prod_components by simp

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "category \<alpha> \<AA>" and \<BB>: "category \<alpha> \<BB>"
begin

interpretation \<AA>: category \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: category \<alpha> \<BB> by (rule \<BB>)

interpretation finite_pcategory \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>(\<lambda>i. if i = 0 then \<AA> else \<BB>)\<close>
  by (intro finite_pcategory_cat_prod_2 \<AA> \<BB>)

lemma cat_prod_2_CId_app[cat_prod_cs_simps]:
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
  shows "(\<AA> \<times>\<^sub>C \<BB>)\<lparr>CId\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> = [\<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr>, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>]\<^sub>\<circ>"
proof-
  have "(\<AA> \<times>\<^sub>C \<BB>)\<lparr>CId\<rparr> \<lparr>a, b\<rparr>\<^sub>\<bullet> = 
    (\<lambda>i\<in>\<^sub>\<circ>2\<^sub>\<nat>. (if i = 0 then \<AA> else \<BB>)\<lparr>CId\<rparr>\<lparr>[a, b]\<^sub>\<circ>\<lparr>i\<rparr>\<rparr>)"
    by 
      (
        rule 
          cat_prod_CId_app[
            OF assms[unfolded cat_prod_2_def], folded cat_prod_2_def
            ]
      )
  also have 
    "(\<lambda>i\<in>\<^sub>\<circ>2\<^sub>\<nat>. (if i = 0 then \<AA> else \<BB>)\<lparr>CId\<rparr>\<lparr>[a, b]\<^sub>\<circ>\<lparr>i\<rparr>\<rparr>) = 
      [\<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr>, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>]\<^sub>\<circ>"
  proof(rule vsv_eqI, unfold vdomain_VLambda)
    fix i assume "i \<in>\<^sub>\<circ> 2\<^sub>\<nat>"
    then consider \<open>i = 0\<close> | \<open>i = 1\<^sub>\<nat>\<close> unfolding two by auto
    then show 
      "(\<lambda>i\<in>\<^sub>\<circ>2\<^sub>\<nat>. (if i = 0 then \<AA> else \<BB>)\<lparr>CId\<rparr>\<lparr>[a, b]\<^sub>\<circ>\<lparr>i\<rparr>\<rparr>)\<lparr>i\<rparr> = 
        [\<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr>, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>]\<^sub>\<circ>\<lparr>i\<rparr>"
      by cases (simp_all add: two nat_omega_simps)
  qed (auto simp: two nat_omega_simps)
  finally show ?thesis by simp
qed

lemma cat_prod_2_CId_vrange: "\<R>\<^sub>\<circ> ((\<AA> \<times>\<^sub>C \<BB>)\<lparr>CId\<rparr>) \<subseteq>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Arr\<rparr>"
proof(rule vsv.vsv_vrange_vsubset, unfold cat_cs_simps)
  show "vsv ((\<AA> \<times>\<^sub>C \<BB>)\<lparr>CId\<rparr>)" by (rule cat_prod_2_CId_vsv)
  fix ab assume "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
  then obtain a b where ab_def: "ab = [a, b]\<^sub>\<circ>" 
    and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    by (elim cat_prod_2_ObjE[OF \<AA> \<BB>])
  from \<AA> \<BB> a b show "(\<AA> \<times>\<^sub>C \<BB>)\<lparr>CId\<rparr>\<lparr>ab\<rparr> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Arr\<rparr>"
    unfolding ab_def 
    by (cs_concl cs_intro: cat_cs_intros cat_prod_cs_intros)
qed

end


subsubsection\<open>Opposite product category\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "category \<alpha> \<AA>" and \<BB>: "category \<alpha> \<BB>"
begin

interpretation \<AA>: category \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: category \<alpha> \<BB> by (rule \<BB>)

lemma op_smc_smc_prod_2[smc_op_simps]: 
  "op_cat (\<AA> \<times>\<^sub>C \<BB>) = op_cat \<AA> \<times>\<^sub>C op_cat \<BB>"
proof(rule cat_smc_eqI [of \<alpha>])
  from \<AA> \<BB> show cat_lhs: "category \<alpha> (op_cat (\<AA> \<times>\<^sub>C \<BB>))"
    by 
      (
        cs_concl 
          cs_simp: cat_op_simps cs_intro: cat_cs_intros cat_op_intros
      )
  interpret cat_lhs: category \<alpha> \<open>op_cat (\<AA> \<times>\<^sub>C \<BB>)\<close> by (rule cat_lhs)
  from \<AA> \<BB> show cat_rhs: "category \<alpha> (op_cat \<AA> \<times>\<^sub>C op_cat \<BB>)"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros
      )
  interpret cat_rhs: category \<alpha> \<open>op_cat \<AA> \<times>\<^sub>C op_cat \<BB>\<close> by (rule cat_rhs)
  show "op_cat (\<AA> \<times>\<^sub>C \<BB>)\<lparr>CId\<rparr> = (op_cat \<AA> \<times>\<^sub>C op_cat \<BB>)\<lparr>CId\<rparr>"
    unfolding cat_op_simps
  proof(rule vsv_eqI, unfold cat_cs_simps)
    show "vsv ((\<AA> \<times>\<^sub>C \<BB>)\<lparr>CId\<rparr>)" by (rule cat_prod_2_CId_vsv)
    show "vsv ((op_cat \<AA> \<times>\<^sub>C op_cat \<BB>)\<lparr>CId\<rparr>)" by (rule cat_prod_2_CId_vsv)
    from \<AA> \<BB> show "(\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr> = (op_cat \<AA> \<times>\<^sub>C op_cat \<BB>)\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_op_intros)
    show "(\<AA> \<times>\<^sub>C \<BB>)\<lparr>CId\<rparr>\<lparr>ab\<rparr> = (op_cat \<AA> \<times>\<^sub>C op_cat \<BB>)\<lparr>CId\<rparr>\<lparr>ab\<rparr>"
      if "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>" for ab
      using that unfolding cat_cs_simps
    proof-
      from that obtain a b
        where ab_def: "ab = [a, b]\<^sub>\<circ>" 
          and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
          and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
        by (elim cat_prod_2_ObjE[OF \<AA> \<BB>])
      from \<AA> \<BB> a b show "(\<AA> \<times>\<^sub>C \<BB>)\<lparr>CId\<rparr>\<lparr>ab\<rparr> = (op_cat \<AA> \<times>\<^sub>C op_cat \<BB>)\<lparr>CId\<rparr>\<lparr>ab\<rparr>"
        unfolding ab_def
        by 
          (
            cs_concl
              cs_simp: cat_op_simps cat_prod_cs_simps
              cs_intro: cat_op_intros cat_prod_cs_intros
          )
    qed
  qed

  from \<AA> \<BB> show "cat_smc (op_cat (\<AA> \<times>\<^sub>C \<BB>)) = cat_smc (op_cat \<AA> \<times>\<^sub>C op_cat \<BB>)"
    unfolding slicing_commute[symmetric]
    by (cs_concl cs_simp: smc_op_simps cs_intro: slicing_intros)

qed

end


subsubsection\<open>Flip\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "category \<alpha> \<AA>" and \<BB>: "category \<alpha> \<BB>"
begin

interpretation \<AA>: category \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: category \<alpha> \<BB> by (rule \<BB>)

lemma cat_prod_2_Obj_fconverse[cat_cs_simps]:
  "((\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>)\<inverse>\<^sub>\<bullet> = (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>"
proof-
  interpret fbrelation \<open>((\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>)\<close> 
    by (auto elim: cat_prod_2_ObjE[OF \<AA> \<BB>])
  show ?thesis
  proof(intro vsubset_antisym vsubsetI)
    fix ba assume prems: "ba \<in>\<^sub>\<circ> ((\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>)\<inverse>\<^sub>\<bullet>"
    then obtain a b where ba_def: "ba = [b, a]\<^sub>\<circ>" by clarsimp
    from prems[unfolded ba_def] have "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>" by auto
    then have "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
      by (auto elim: cat_prod_2_ObjE[OF \<AA> \<BB>])
    with \<AA> \<BB> show "ba \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>"
      unfolding ba_def by (cs_concl cs_intro: cat_prod_cs_intros)
  next
    fix ba assume "ba \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>"  
    then obtain a b 
      where ba_def: "ba = [b, a]\<^sub>\<circ>" 
        and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
        and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
      by (elim cat_prod_2_ObjE[OF \<BB> \<AA>])
    from b a show "ba \<in>\<^sub>\<circ> ((\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>)\<inverse>\<^sub>\<bullet>"
      unfolding ba_def by (auto simp: cat_prod_2_ObjI[OF \<AA> \<BB> a b])
  qed
qed

lemma cat_prod_2_Arr_fconverse[cat_cs_simps]:
  "((\<AA> \<times>\<^sub>C \<BB>)\<lparr>Arr\<rparr>)\<inverse>\<^sub>\<bullet> = (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Arr\<rparr>"
proof-
  interpret fbrelation \<open>((\<AA> \<times>\<^sub>C \<BB>)\<lparr>Arr\<rparr>)\<close> 
    by (auto elim: cat_prod_2_ArrE[OF \<AA> \<BB>])
  show ?thesis
  proof(intro vsubset_antisym vsubsetI)
    fix ba assume prems: "ba \<in>\<^sub>\<circ> ((\<AA> \<times>\<^sub>C \<BB>)\<lparr>Arr\<rparr>)\<inverse>\<^sub>\<bullet>"
    then obtain a b where ba_def: "ba = [b, a]\<^sub>\<circ>" by clarsimp
    from prems[unfolded ba_def] have "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Arr\<rparr>" by auto
    then have "a \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
      by (auto elim: cat_prod_2_ArrE[OF \<AA> \<BB>])
    with \<AA> \<BB> show "ba \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Arr\<rparr>"
      unfolding ba_def 
      by 
        (
          cs_concl 
            cs_simp: cat_prod_cs_simps 
            cs_intro: cat_prod_cs_intros cat_cs_intros
        )
  next
    fix ba assume "ba \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Arr\<rparr>"  
    then obtain a b 
      where ba_def: "ba = [b, a]\<^sub>\<circ>" 
        and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
        and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
      by (elim cat_prod_2_ArrE[OF \<BB> \<AA>])
    from b a show "ba \<in>\<^sub>\<circ> ((\<AA> \<times>\<^sub>C \<BB>)\<lparr>Arr\<rparr>)\<inverse>\<^sub>\<bullet>"
      unfolding ba_def by (auto simp: cat_prod_2_ArrI[OF \<AA> \<BB> a b])
  qed
qed

end



subsection\<open>Projections for the product of two categories\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter II-3 in \cite{mac_lane_categories_2010}.\<close>

definition cf_proj_fst :: "V \<Rightarrow> V \<Rightarrow> V" (\<open>\<pi>\<^sub>C\<^sub>.\<^sub>1\<close>)
  where "\<pi>\<^sub>C\<^sub>.\<^sub>1 \<AA> \<BB> = cf_proj (2\<^sub>\<nat>) (\<lambda>i. if i = 0 then \<AA> else \<BB>) 0"
definition cf_proj_snd :: "V \<Rightarrow> V \<Rightarrow> V" (\<open>\<pi>\<^sub>C\<^sub>.\<^sub>2\<close>)
  where "\<pi>\<^sub>C\<^sub>.\<^sub>2 \<AA> \<BB> = cf_proj (2\<^sub>\<nat>) (\<lambda>i. if i = 0 then \<AA> else \<BB>) (1\<^sub>\<nat>)"


text\<open>Slicing\<close>

lemma cf_smcf_cf_proj_fst[slicing_commute]: 
  "\<pi>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>1 (cat_smc \<AA>) (cat_smc \<BB>) = cf_smcf (\<pi>\<^sub>C\<^sub>.\<^sub>1 \<AA> \<BB>)"
  unfolding 
    cf_proj_fst_def smcf_proj_fst_def slicing_commute[symmetric] if_distrib ..

lemma cf_smcf_cf_proj_snd[slicing_commute]: 
  "\<pi>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>2 (cat_smc \<AA>) (cat_smc \<BB>) = cf_smcf (\<pi>\<^sub>C\<^sub>.\<^sub>2 \<AA> \<BB>)"
  unfolding 
    cf_proj_snd_def smcf_proj_snd_def slicing_commute[symmetric] if_distrib ..

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "category \<alpha> \<AA>" and \<BB>: "category \<alpha> \<BB>"
begin

interpretation \<AA>: category \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: category \<alpha> \<BB> by (rule \<BB>)

lemmas_with 
  [
    where \<AA>=\<open>cat_smc \<AA>\<close> and \<BB>=\<open>cat_smc \<BB>\<close>, 
    unfolded slicing_simps slicing_commute, 
    OF \<AA>.cat_semicategory \<BB>.cat_semicategory
  ]:
  cf_proj_fst_ObjMap_app = smcf_proj_fst_ObjMap_app 
  and cf_proj_snd_ObjMap_app = smcf_proj_snd_ObjMap_app
  and cf_proj_fst_ArrMap_app = smcf_proj_fst_ArrMap_app
  and cf_proj_snd_ArrMap_app = smcf_proj_snd_ArrMap_app

end


subsubsection\<open>
Domain and codomain of a projection of a product of two categories
\<close>

lemma cf_proj_fst_HomDom: "\<pi>\<^sub>C\<^sub>.\<^sub>1 \<AA> \<BB>\<lparr>HomDom\<rparr> = \<AA> \<times>\<^sub>C \<BB>"
  unfolding cf_proj_fst_def cf_proj_components cat_prod_2_def ..

lemma cf_proj_fst_HomCod: "\<pi>\<^sub>C\<^sub>.\<^sub>1 \<AA> \<BB>\<lparr>HomCod\<rparr> = \<AA>"
  unfolding cf_proj_fst_def cf_proj_components cat_prod_2_def by simp
  
lemma cf_proj_snd_HomDom: "\<pi>\<^sub>C\<^sub>.\<^sub>2 \<AA> \<BB>\<lparr>HomDom\<rparr> = \<AA> \<times>\<^sub>C \<BB>"
  unfolding cf_proj_snd_def cf_proj_components cat_prod_2_def ..

lemma cf_proj_snd_HomCod: "\<pi>\<^sub>C\<^sub>.\<^sub>2 \<AA> \<BB>\<lparr>HomCod\<rparr> = \<BB>"
  unfolding cf_proj_snd_def cf_proj_components cat_prod_2_def by simp


subsubsection\<open>Projection of a product of two categories is a functor\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "category \<alpha> \<AA>" and \<BB>: "category \<alpha> \<BB>"
begin

interpretation \<Z> \<alpha> by (rule categoryD[OF \<AA>])
interpretation \<AA>: category \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: category \<alpha> \<BB> by (rule \<BB>)
interpretation finite_pcategory \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 \<AA> \<BB>\<close>
  by (intro finite_pcategory_cat_prod_2 \<AA> \<BB>)

lemma cf_proj_fst_is_functor: 
  assumes "i \<in>\<^sub>\<circ> I" 
  shows "\<pi>\<^sub>C\<^sub>.\<^sub>1 \<AA> \<BB> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  by 
    (
      rule 
        pcat_cf_proj_is_functor[
          where i=0, simplified, folded cf_proj_fst_def cat_prod_2_def
          ]
    )

lemma cf_proj_fst_is_functor'[cat_cs_intros]: 
  assumes "i \<in>\<^sub>\<circ> I" and "\<CC> = \<AA> \<times>\<^sub>C \<BB>" and "\<DD> = \<AA>"
  shows "\<pi>\<^sub>C\<^sub>.\<^sub>1 \<AA> \<BB> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms(1) unfolding assms(2,3) by (rule cf_proj_fst_is_functor)

lemma cf_proj_snd_is_functor: 
  assumes "i \<in>\<^sub>\<circ> I" 
  shows "\<pi>\<^sub>C\<^sub>.\<^sub>2 \<AA> \<BB> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  by 
    (
      rule 
        pcat_cf_proj_is_functor[
          where i=\<open>1\<^sub>\<nat>\<close>, simplified, folded cf_proj_snd_def cat_prod_2_def
          ]
    )

lemma cf_proj_snd_is_functor'[cat_cs_intros]: 
  assumes "i \<in>\<^sub>\<circ> I" and "\<CC> = \<AA> \<times>\<^sub>C \<BB>" and "\<DD> = \<BB>"
  shows "\<pi>\<^sub>C\<^sub>.\<^sub>2 \<AA> \<BB> : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms(1) unfolding assms(2,3) by (rule cf_proj_snd_is_functor)

end



subsection\<open>Product of three categories\<close>


subsubsection\<open>Definition and elementary properties.\<close>

definition cat_prod_3 :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" ("(_ \<times>\<^sub>C\<^sub>3 _ \<times>\<^sub>C\<^sub>3 _)" [81, 81, 81] 80)
  where "\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC> = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>3\<^sub>\<nat>. if3 \<AA> \<BB> \<CC> i)"

abbreviation cat_pow_3 :: "V \<Rightarrow> V" (\<open>_^\<^sub>C\<^sub>3\<close> [81] 80)
  where "\<CC>^\<^sub>C\<^sub>3 \<equiv> \<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC>"


text\<open>Slicing.\<close>
  
lemma cat_smc_cat_prod_3[slicing_commute]: 
  "cat_smc \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C\<^sub>3 cat_smc \<BB> \<times>\<^sub>S\<^sub>M\<^sub>C\<^sub>3 cat_smc \<CC> = cat_smc (\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)"
  unfolding cat_prod_3_def smc_prod_3_def slicing_commute[symmetric] if_distrib
  by (simp add: if_distrib[symmetric])

context 
  fixes \<alpha> \<AA> \<BB> \<CC>
  assumes \<AA>: "category \<alpha> \<AA>" and \<BB>: "category \<alpha> \<BB>" and \<CC>: "category \<alpha> \<CC>"
begin

interpretation \<AA>: category \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: category \<alpha> \<BB> by (rule \<BB>)
interpretation \<CC>: category \<alpha> \<CC> by (rule \<CC>)

lemmas_with 
  [
    where \<AA>=\<open>cat_smc \<AA>\<close> and \<BB>=\<open>cat_smc \<BB>\<close> and \<CC>=\<open>cat_smc \<CC>\<close>, 
    unfolded slicing_simps slicing_commute, 
    OF \<AA>.cat_semicategory \<BB>.cat_semicategory \<CC>.cat_semicategory
  ]:
  cat_prod_3_ObjI = smc_prod_3_ObjI 
  and cat_prod_3_ObjI'[cat_prod_cs_intros] = smc_prod_3_ObjI'
  and cat_prod_3_ObjE = smc_prod_3_ObjE
  and cat_prod_3_ArrI = smc_prod_3_ArrI
  and cat_prod_3_ArrI'[cat_prod_cs_intros] = smc_prod_3_ArrI'
  and cat_prod_3_ArrE = smc_prod_3_ArrE
  and cat_prod_3_is_arrI = smc_prod_3_is_arrI
  and cat_prod_3_is_arrI'[cat_prod_cs_intros] = smc_prod_3_is_arrI'
  and cat_prod_3_is_arrE = smc_prod_3_is_arrE
  and cat_prod_3_Dom_vsv = smc_prod_3_Dom_vsv
  and cat_prod_3_Dom_vdomain[cat_cs_simps] = smc_prod_3_Dom_vdomain
  and cat_prod_3_Dom_app[cat_prod_cs_simps] = smc_prod_3_Dom_app
  and cat_prod_3_Dom_vrange = smc_prod_3_Dom_vrange
  and cat_prod_3_Cod_vsv = smc_prod_3_Cod_vsv
  and cat_prod_3_Cod_vdomain[cat_cs_simps] = smc_prod_3_Cod_vdomain
  and cat_prod_3_Cod_app[cat_prod_cs_simps] = smc_prod_3_Cod_app
  and cat_prod_3_Cod_vrange = smc_prod_3_Cod_vrange

lemmas_with 
  [
    where \<AA>=\<open>cat_smc \<AA>\<close> and \<BB>=\<open>cat_smc \<BB>\<close> and \<CC>=\<open>cat_smc \<CC>\<close>, 
    unfolded slicing_simps slicing_commute, 
    OF \<AA>.cat_semicategory \<BB>.cat_semicategory \<CC>.cat_semicategory
  ]:
  cat_prod_3_Comp_app[cat_prod_cs_simps] = smc_prod_3_Comp_app

end


subsubsection\<open>Product of three categories is a category\<close>

context 
  fixes \<alpha> \<AA> \<BB> \<CC>
  assumes \<AA>: "category \<alpha> \<AA>" and \<BB>: "category \<alpha> \<BB>" and \<CC>: "category \<alpha> \<CC>"
begin

interpretation \<Z> \<alpha> by (rule categoryD[OF \<AA>])
interpretation \<AA>: category \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: category \<alpha> \<BB> by (rule \<BB>)
interpretation \<CC>: category \<alpha> \<CC> by (rule \<CC>)

lemma finite_pcategory_cat_prod_3: "finite_pcategory \<alpha> (3\<^sub>\<nat>) (if3 \<AA> \<BB> \<CC>)"
proof(intro finite_pcategoryI pcategory_baseI)
  from Axiom_of_Infinity show z1_in_Vset: "3\<^sub>\<nat> \<in>\<^sub>\<circ> Vset \<alpha>" by blast
  show "category \<alpha> (if3 \<AA> \<BB> \<CC> i)" if "i \<in>\<^sub>\<circ> 3\<^sub>\<nat>" for i
    by (auto simp: cat_cs_intros)
qed auto

interpretation finite_pcategory \<alpha> \<open>3\<^sub>\<nat>\<close> \<open>if3 \<AA> \<BB> \<CC>\<close>
  by (intro finite_pcategory_cat_prod_3 \<AA> \<BB> \<CC>)

lemma category_cat_prod_3[cat_cs_intros]: "category \<alpha> (\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)"
  unfolding cat_prod_3_def by (rule pcat_category_cat_prod)

end


subsubsection\<open>Identity\<close>

lemma cat_prod_3_CId_vsv[cat_cs_intros]: "vsv ((\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>CId\<rparr>)"
  unfolding cat_prod_3_def cat_prod_components by simp

lemma cat_prod_3_CId_vdomain[cat_cs_simps]: 
  "\<D>\<^sub>\<circ> ((\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>CId\<rparr>) = (\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Obj\<rparr>"
  unfolding cat_prod_3_def cat_prod_components by simp

context 
  fixes \<alpha> \<AA> \<BB> \<CC>
  assumes \<AA>: "category \<alpha> \<AA>" and \<BB>: "category \<alpha> \<BB>" and \<CC>: "category \<alpha> \<CC>"
begin

interpretation \<AA>: category \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: category \<alpha> \<BB> by (rule \<BB>)
interpretation \<CC>: category \<alpha> \<CC> by (rule \<CC>)

interpretation finite_pcategory \<alpha> \<open>3\<^sub>\<nat>\<close> \<open>if3 \<AA> \<BB> \<CC>\<close>
  by (intro finite_pcategory_cat_prod_3 \<AA> \<BB> \<CC>)

lemma cat_prod_3_CId_app[cat_prod_cs_simps]:
  assumes "[a, b, c]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Obj\<rparr>"
  shows "(\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>CId\<rparr>\<lparr>a, b, c\<rparr>\<^sub>\<bullet> = [\<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr>, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>, \<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>]\<^sub>\<circ>"
proof-
  have "(\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>CId\<rparr>\<lparr>a, b, c\<rparr>\<^sub>\<bullet> = 
    (\<lambda>i\<in>\<^sub>\<circ>3\<^sub>\<nat>. if3 \<AA> \<BB> \<CC> i\<lparr>CId\<rparr>\<lparr>[a, b, c]\<^sub>\<circ>\<lparr>i\<rparr>\<rparr>)"
    by 
      (
        rule 
          cat_prod_CId_app[
            OF assms[unfolded cat_prod_3_def], folded cat_prod_3_def
            ]
      )
  also have 
    "(\<lambda>i\<in>\<^sub>\<circ>3\<^sub>\<nat>. if3 \<AA> \<BB> \<CC> i\<lparr>CId\<rparr>\<lparr>[a, b, c]\<^sub>\<circ>\<lparr>i\<rparr>\<rparr>) = [\<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr>, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>, \<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>]\<^sub>\<circ>"
  proof(rule vsv_eqI, unfold vdomain_VLambda)
    fix i assume "i \<in>\<^sub>\<circ> 3\<^sub>\<nat>"
    then consider \<open>i = 0\<close> | \<open>i = 1\<^sub>\<nat>\<close> | \<open>i = 2\<^sub>\<nat>\<close> unfolding three by auto
    then show 
      "(\<lambda>i\<in>\<^sub>\<circ>3\<^sub>\<nat>. (if3 \<AA> \<BB> \<CC> i)\<lparr>CId\<rparr>\<lparr>[a, b, c]\<^sub>\<circ>\<lparr>i\<rparr>\<rparr>)\<lparr>i\<rparr> = 
        [\<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr>, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>, \<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>]\<^sub>\<circ>\<lparr>i\<rparr>"
      by cases (simp_all add: three nat_omega_simps)
  qed (auto simp: three nat_omega_simps)
  finally show ?thesis by simp
qed

lemma cat_prod_3_CId_vrange: 
  "\<R>\<^sub>\<circ> ((\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>CId\<rparr>) \<subseteq>\<^sub>\<circ> (\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Arr\<rparr>"
proof(rule vsv.vsv_vrange_vsubset, unfold cat_cs_simps)
  show "vsv ((\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>CId\<rparr>)" by (rule cat_prod_3_CId_vsv)
  fix abc assume "abc \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Obj\<rparr>"
  then obtain a b c where abc_def: "abc = [a, b, c]\<^sub>\<circ>" 
    and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    and c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    by (elim cat_prod_3_ObjE[OF \<AA> \<BB> \<CC>])
  from \<AA> \<BB> \<CC> a b c show "(\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>CId\<rparr>\<lparr>abc\<rparr> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Arr\<rparr>"
    unfolding abc_def 
    by (cs_concl cs_intro: cat_cs_intros cat_prod_cs_intros)
qed

end



subsection\<open>
Conversion of a product of three categories to products of two categories
\<close>

definition cf_cat_prod_21_of_3 :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_cat_prod_21_of_3 \<AA> \<BB> \<CC> =
    [
      (\<lambda>A\<in>\<^sub>\<circ>(\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Obj\<rparr>. [[A\<lparr>0\<rparr>, A\<lparr>1\<^sub>\<nat>\<rparr>]\<^sub>\<circ>, A\<lparr>2\<^sub>\<nat>\<rparr>]\<^sub>\<circ>),
      (\<lambda>F\<in>\<^sub>\<circ>(\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Arr\<rparr>. [[F\<lparr>0\<rparr>, F\<lparr>1\<^sub>\<nat>\<rparr>]\<^sub>\<circ>, F\<lparr>2\<^sub>\<nat>\<rparr>]\<^sub>\<circ>),
      \<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>,
      (\<AA> \<times>\<^sub>C \<BB>) \<times>\<^sub>C \<CC>
    ]\<^sub>\<circ>"

definition cf_cat_prod_12_of_3 :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_cat_prod_12_of_3 \<AA> \<BB> \<CC> =
    [
      (\<lambda>A\<in>\<^sub>\<circ>(\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Obj\<rparr>. [A\<lparr>0\<rparr>, [A\<lparr>1\<^sub>\<nat>\<rparr>, A\<lparr>2\<^sub>\<nat>\<rparr>]\<^sub>\<circ>]\<^sub>\<circ>),
      (\<lambda>F\<in>\<^sub>\<circ>(\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Arr\<rparr>. [F\<lparr>0\<rparr>, [F\<lparr>1\<^sub>\<nat>\<rparr>, F\<lparr>2\<^sub>\<nat>\<rparr>]\<^sub>\<circ>]\<^sub>\<circ>),
      \<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>,
      \<AA> \<times>\<^sub>C (\<BB> \<times>\<^sub>C \<CC>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_cat_prod_21_of_3_components:
  shows "cf_cat_prod_21_of_3 \<AA> \<BB> \<CC>\<lparr>ObjMap\<rparr> =
    (\<lambda>A\<in>\<^sub>\<circ>(\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Obj\<rparr>. [[A\<lparr>0\<rparr>, A\<lparr>1\<^sub>\<nat>\<rparr>]\<^sub>\<circ>, A\<lparr>2\<^sub>\<nat>\<rparr>]\<^sub>\<circ>)"
    and "cf_cat_prod_21_of_3 \<AA> \<BB> \<CC>\<lparr>ArrMap\<rparr> =
    (\<lambda>F\<in>\<^sub>\<circ>(\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Arr\<rparr>. [[F\<lparr>0\<rparr>, F\<lparr>1\<^sub>\<nat>\<rparr>]\<^sub>\<circ>, F\<lparr>2\<^sub>\<nat>\<rparr>]\<^sub>\<circ>)"
    and [cat_cs_simps]: "cf_cat_prod_21_of_3 \<AA> \<BB> \<CC>\<lparr>HomDom\<rparr> = \<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>"
    and [cat_cs_simps]: "cf_cat_prod_21_of_3 \<AA> \<BB> \<CC>\<lparr>HomCod\<rparr> = (\<AA> \<times>\<^sub>C \<BB>) \<times>\<^sub>C \<CC>"
  unfolding cf_cat_prod_21_of_3_def dghm_field_simps 
  by (simp_all add: nat_omega_simps)

lemma cf_cat_prod_12_of_3_components:
  shows "cf_cat_prod_12_of_3 \<AA> \<BB> \<CC>\<lparr>ObjMap\<rparr> =
    (\<lambda>A\<in>\<^sub>\<circ>(\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Obj\<rparr>. [A\<lparr>0\<rparr>, [A\<lparr>1\<^sub>\<nat>\<rparr>, A\<lparr>2\<^sub>\<nat>\<rparr>]\<^sub>\<circ>]\<^sub>\<circ>)"
    and "cf_cat_prod_12_of_3 \<AA> \<BB> \<CC>\<lparr>ArrMap\<rparr> =
    (\<lambda>F\<in>\<^sub>\<circ>(\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Arr\<rparr>. [F\<lparr>0\<rparr>, [F\<lparr>1\<^sub>\<nat>\<rparr>, F\<lparr>2\<^sub>\<nat>\<rparr>]\<^sub>\<circ>]\<^sub>\<circ>)"
    and [cat_cs_simps]: "cf_cat_prod_12_of_3 \<AA> \<BB> \<CC>\<lparr>HomDom\<rparr> = \<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>"
    and [cat_cs_simps]: "cf_cat_prod_12_of_3 \<AA> \<BB> \<CC>\<lparr>HomCod\<rparr> = \<AA> \<times>\<^sub>C (\<BB> \<times>\<^sub>C \<CC>)"
  unfolding cf_cat_prod_12_of_3_def dghm_field_simps 
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Object\<close>

mk_VLambda cf_cat_prod_21_of_3_components(1)
  |vsv cf_cat_prod_21_of_3_ObjMap_vsv[cat_cs_intros]|
  |vdomain cf_cat_prod_21_of_3_ObjMap_vdomain[cat_cs_simps]|
  |app cf_cat_prod_21_of_3_ObjMap_app'|

mk_VLambda cf_cat_prod_12_of_3_components(1)
  |vsv cf_cat_prod_12_of_3_ObjMap_vsv[cat_cs_intros]|
  |vdomain cf_cat_prod_12_of_3_ObjMap_vdomain[cat_cs_simps]|
  |app cf_cat_prod_12_of_3_ObjMap_app'|

lemma cf_cat_prod_21_of_3_ObjMap_app[cat_cs_simps]:
  assumes "A = [a, b, c]\<^sub>\<circ>" and "[a, b, c]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Obj\<rparr>"
  shows "cf_cat_prod_21_of_3 \<AA> \<BB> \<CC>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> = [[a, b]\<^sub>\<circ>, c]\<^sub>\<circ>"
  using assms(2) 
  unfolding assms(1)
  by (simp add: cf_cat_prod_21_of_3_ObjMap_app' nat_omega_simps)

lemma cf_cat_prod_12_of_3_ObjMap_app[cat_cs_simps]:
  assumes "A = [a, b, c]\<^sub>\<circ>" and "[a, b, c]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Obj\<rparr>"
  shows "cf_cat_prod_12_of_3 \<AA> \<BB> \<CC>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> = [a, [b, c]\<^sub>\<circ>]\<^sub>\<circ>"
  using assms(2)
  unfolding assms(1)
  by (simp add: cf_cat_prod_12_of_3_ObjMap_app' nat_omega_simps)

lemma cf_cat_prod_21_of_3_ObjMap_vrange: 
  assumes "category \<alpha> \<AA>" and "category \<alpha> \<BB>" and "category \<alpha> \<CC>"
  shows "\<R>\<^sub>\<circ> (cf_cat_prod_21_of_3 \<AA> \<BB> \<CC>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> ((\<AA> \<times>\<^sub>C \<BB>) \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
proof-
  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(2))
  interpret \<CC>: category \<alpha> \<CC> by (rule assms(3))
  show ?thesis
  proof(rule vsv.vsv_vrange_vsubset, unfold cf_cat_prod_21_of_3_ObjMap_vdomain)
    fix A assume prems: "A \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Obj\<rparr>"
    then show "cf_cat_prod_21_of_3 \<AA> \<BB> \<CC>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> \<in>\<^sub>\<circ> ((\<AA> \<times>\<^sub>C \<BB>) \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
      by (elim cat_prod_3_ObjE[OF assms], insert prems, simp only:)
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_prod_cs_simps 
            cs_intro: cat_cs_intros cat_prod_cs_intros
        )
  qed (cs_concl cs_intro: cat_cs_intros)
qed

lemma cf_cat_prod_12_of_3_ObjMap_vrange: 
  assumes "category \<alpha> \<AA>" and "category \<alpha> \<BB>" and "category \<alpha> \<CC>"
  shows "\<R>\<^sub>\<circ> (cf_cat_prod_12_of_3 \<AA> \<BB> \<CC>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> (\<AA> \<times>\<^sub>C (\<BB> \<times>\<^sub>C \<CC>))\<lparr>Obj\<rparr>"
proof-
  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(2))
  interpret \<CC>: category \<alpha> \<CC> by (rule assms(3))
  show ?thesis
  proof(rule vsv.vsv_vrange_vsubset, unfold cf_cat_prod_12_of_3_ObjMap_vdomain)
    fix A assume prems: "A \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Obj\<rparr>"
    then show "cf_cat_prod_12_of_3 \<AA> \<BB> \<CC>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C (\<BB> \<times>\<^sub>C \<CC>))\<lparr>Obj\<rparr>"
      by (elim cat_prod_3_ObjE[OF assms], insert prems, simp only:)
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_prod_cs_simps 
            cs_intro: cat_cs_intros cat_prod_cs_intros
        )
  qed (cs_concl cs_intro: cat_cs_intros)
qed


subsubsection\<open>Arrow\<close>

mk_VLambda cf_cat_prod_21_of_3_components(2)
  |vsv cf_cat_prod_21_of_3_ArrMap_vsv[cat_cs_intros]|
  |vdomain cf_cat_prod_21_of_3_ArrMap_vdomain[cat_cs_simps]|
  |app cf_cat_prod_21_of_3_ArrMap_app'|

mk_VLambda cf_cat_prod_12_of_3_components(2)
  |vsv cf_cat_prod_12_of_3_ArrMap_vsv[cat_cs_intros]|
  |vdomain cf_cat_prod_12_of_3_ArrMap_vdomain[cat_cs_simps]|
  |app cf_cat_prod_12_of_3_ArrMap_app'|

lemma cf_cat_prod_21_of_3_ArrMap_app[cat_cs_simps]:
  assumes "F = [h, g, f]\<^sub>\<circ>" and "[h, g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Arr\<rparr>"
  shows "cf_cat_prod_21_of_3 \<AA> \<BB> \<CC>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> = [[h, g]\<^sub>\<circ>, f]\<^sub>\<circ>"
  using assms(2) unfolding assms(1)
  by (simp add: cf_cat_prod_21_of_3_ArrMap_app' nat_omega_simps)

lemma cf_cat_prod_12_of_3_ArrMap_app[cat_cs_simps]:
  assumes "F = [h, g, f]\<^sub>\<circ>" and "[h, g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Arr\<rparr>"
  shows "cf_cat_prod_12_of_3 \<AA> \<BB> \<CC>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> = [h, [g, f]\<^sub>\<circ>]\<^sub>\<circ>"
  using assms(2) 
  unfolding assms(1)
  by (simp add: cf_cat_prod_12_of_3_ArrMap_app' nat_omega_simps)


subsubsection\<open>
Conversion of a product of three categories to products 
of two categories is a functor
\<close>

lemma cf_cat_prod_21_of_3_is_functor:
  assumes "category \<alpha> \<AA>" and "category \<alpha> \<BB>" and "category \<alpha> \<CC>"
  shows "cf_cat_prod_21_of_3 \<AA> \<BB> \<CC> : \<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> (\<AA> \<times>\<^sub>C \<BB>) \<times>\<^sub>C \<CC>"
proof-

  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(2))
  interpret \<CC>: category \<alpha> \<CC> by (rule assms(3))

  show ?thesis
  proof(rule is_functorI')
    show "vfsequence (cf_cat_prod_21_of_3 \<AA> \<BB> \<CC>)"
      unfolding cf_cat_prod_21_of_3_def by auto
    show "vcard (cf_cat_prod_21_of_3 \<AA> \<BB> \<CC>) = 4\<^sub>\<nat>"
      unfolding cf_cat_prod_21_of_3_def by (simp add: nat_omega_simps)
    show "\<R>\<^sub>\<circ> (cf_cat_prod_21_of_3 \<AA> \<BB> \<CC>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> ((\<AA> \<times>\<^sub>C \<BB>) \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
      by (rule cf_cat_prod_21_of_3_ObjMap_vrange[OF assms])
    show 
      "cf_cat_prod_21_of_3 \<AA> \<BB> \<CC>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> : 
        cf_cat_prod_21_of_3 \<AA> \<BB> \<CC>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> \<mapsto>\<^bsub>(\<AA> \<times>\<^sub>C \<BB>) \<times>\<^sub>C \<CC>\<^esub> 
        cf_cat_prod_21_of_3 \<AA> \<BB> \<CC>\<lparr>ObjMap\<rparr>\<lparr>B\<rparr>"
      if "F : A \<mapsto>\<^bsub>\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>\<^esub> B"
      for A B F
      using that
      by (elim cat_prod_3_is_arrE[OF assms], insert that, simp only:)
        (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros)
    show 
      "cf_cat_prod_21_of_3 \<AA> \<BB> \<CC>\<lparr>ArrMap\<rparr>\<lparr>G \<circ>\<^sub>A\<^bsub>\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>\<^esub> F\<rparr> = 
        cf_cat_prod_21_of_3 \<AA> \<BB> \<CC>\<lparr>ArrMap\<rparr>\<lparr>G\<rparr> \<circ>\<^sub>A\<^bsub>(\<AA> \<times>\<^sub>C \<BB>) \<times>\<^sub>C \<CC>\<^esub> 
        cf_cat_prod_21_of_3 \<AA> \<BB> \<CC>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr>"
      if "G : B \<mapsto>\<^bsub>\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>\<^esub> C" and "F : A \<mapsto>\<^bsub>\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>\<^esub> B"
      for B C G A F
    proof- 
      from that(2) obtain f f' f'' a a' a'' b b' b''
        where F_def: "F = [f, f', f'']\<^sub>\<circ>"
          and A_def: "A = [a, a', a'']\<^sub>\<circ>"
          and B_def: "B = [b, b', b'']\<^sub>\<circ>"
          and f: "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
          and f': "f' : a' \<mapsto>\<^bsub>\<BB>\<^esub> b'"
          and f'': "f'' : a'' \<mapsto>\<^bsub>\<CC>\<^esub> b''"
        by (elim cat_prod_3_is_arrE[OF assms])
      with that(1) obtain g g' g'' c c' c''
        where G_def: "G = [g, g', g'']\<^sub>\<circ>"
          and C_def: "C = [c, c', c'']\<^sub>\<circ>"
          and g: "g : b \<mapsto>\<^bsub>\<AA>\<^esub> c"
          and g': "g' : b' \<mapsto>\<^bsub>\<BB>\<^esub> c'"
          and g'': "g'' : b'' \<mapsto>\<^bsub>\<CC>\<^esub> c''"
        by (auto elim: cat_prod_3_is_arrE[OF assms])
      from that f f' f'' g g' g'' show ?thesis
        unfolding F_def A_def B_def G_def C_def
        by
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_prod_cs_simps 
              cs_intro: cat_cs_intros cat_prod_cs_intros
          )
    qed
    show 
      "cf_cat_prod_21_of_3 \<AA> \<BB> \<CC>\<lparr>ArrMap\<rparr>\<lparr>(\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>CId\<rparr>\<lparr>C\<rparr>\<rparr> =
        ((\<AA> \<times>\<^sub>C \<BB>) \<times>\<^sub>C \<CC>)\<lparr>CId\<rparr>\<lparr>cf_cat_prod_21_of_3 \<AA> \<BB> \<CC>\<lparr>ObjMap\<rparr>\<lparr>C\<rparr>\<rparr>"
      if "C \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Obj\<rparr>" for C
      using that 
      by (elim cat_prod_3_ObjE[OF assms], insert that, simp only: )
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_prod_cs_simps 
            cs_intro: cat_cs_intros cat_prod_cs_intros
        )
  qed (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)+

qed

lemma cf_cat_prod_21_of_3_is_functor'[cat_cs_intros]:
  assumes "category \<alpha> \<AA>" 
    and "category \<alpha> \<BB>" 
    and "category \<alpha> \<CC>"
    and "\<AA>' = \<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>"
    and "\<BB>' = (\<AA> \<times>\<^sub>C \<BB>) \<times>\<^sub>C \<CC>"
  shows "cf_cat_prod_21_of_3 \<AA> \<BB> \<CC> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  using assms(1-3) unfolding assms(4,5) by (rule cf_cat_prod_21_of_3_is_functor)

lemma cf_cat_prod_12_of_3_is_functor:
  assumes "category \<alpha> \<AA>" and "category \<alpha> \<BB>" and "category \<alpha> \<CC>"
  shows "cf_cat_prod_12_of_3 \<AA> \<BB> \<CC> : \<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> \<times>\<^sub>C (\<BB> \<times>\<^sub>C \<CC>)"
proof-

  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(2))
  interpret \<CC>: category \<alpha> \<CC> by (rule assms(3))

  show ?thesis
  proof(rule is_functorI')
    show "vfsequence (cf_cat_prod_12_of_3 \<AA> \<BB> \<CC>)"
      unfolding cf_cat_prod_12_of_3_def by auto
    show "vcard (cf_cat_prod_12_of_3 \<AA> \<BB> \<CC>) = 4\<^sub>\<nat>"
      unfolding cf_cat_prod_12_of_3_def by (simp add: nat_omega_simps)
    show "\<R>\<^sub>\<circ> (cf_cat_prod_12_of_3 \<AA> \<BB> \<CC>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> (\<AA> \<times>\<^sub>C (\<BB> \<times>\<^sub>C \<CC>))\<lparr>Obj\<rparr>"
      by (rule cf_cat_prod_12_of_3_ObjMap_vrange[OF assms])
    show 
      "cf_cat_prod_12_of_3 \<AA> \<BB> \<CC>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> :
        cf_cat_prod_12_of_3 \<AA> \<BB> \<CC>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> \<mapsto>\<^bsub>\<AA> \<times>\<^sub>C (\<BB> \<times>\<^sub>C \<CC>)\<^esub> 
        cf_cat_prod_12_of_3 \<AA> \<BB> \<CC>\<lparr>ObjMap\<rparr>\<lparr>B\<rparr>"
      if "F : A \<mapsto>\<^bsub>\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>\<^esub> B"
      for A B F
      using that
      by (elim cat_prod_3_is_arrE[OF assms], insert that, simp only:)
        (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros)
    show 
      "cf_cat_prod_12_of_3 \<AA> \<BB> \<CC>\<lparr>ArrMap\<rparr>\<lparr>G \<circ>\<^sub>A\<^bsub>\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>\<^esub> F\<rparr> = 
        cf_cat_prod_12_of_3 \<AA> \<BB> \<CC>\<lparr>ArrMap\<rparr>\<lparr>G\<rparr> \<circ>\<^sub>A\<^bsub>\<AA> \<times>\<^sub>C (\<BB> \<times>\<^sub>C \<CC>)\<^esub> 
        cf_cat_prod_12_of_3 \<AA> \<BB> \<CC>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr>"
      if "G : B \<mapsto>\<^bsub>\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>\<^esub> C" and "F : A \<mapsto>\<^bsub>\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>\<^esub> B"
      for B C G A F
    proof- 
      from that(2) obtain f f' f'' a a' a'' b b' b''
        where F_def: "F = [f, f', f'']\<^sub>\<circ>"
          and A_def: "A = [a, a', a'']\<^sub>\<circ>"
          and B_def: "B = [b, b', b'']\<^sub>\<circ>"
          and f: "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
          and f': "f' : a' \<mapsto>\<^bsub>\<BB>\<^esub> b'"
          and f'': "f'' : a'' \<mapsto>\<^bsub>\<CC>\<^esub> b''"
        by (elim cat_prod_3_is_arrE[OF assms])
      with that(1) obtain g g' g'' c c' c''
        where G_def: "G = [g, g', g'']\<^sub>\<circ>"
          and C_def: "C = [c, c', c'']\<^sub>\<circ>"
          and g: "g : b \<mapsto>\<^bsub>\<AA>\<^esub> c"
          and g': "g' : b' \<mapsto>\<^bsub>\<BB>\<^esub> c'"
          and g'': "g'' : b'' \<mapsto>\<^bsub>\<CC>\<^esub> c''"
        by (auto elim: cat_prod_3_is_arrE[OF assms])
      from that f f' f'' g g' g'' show ?thesis
        unfolding F_def A_def B_def G_def C_def
        by
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_prod_cs_simps 
              cs_intro: cat_cs_intros cat_prod_cs_intros
          )
    qed
    show 
      "cf_cat_prod_12_of_3 \<AA> \<BB> \<CC>\<lparr>ArrMap\<rparr>\<lparr>(\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>CId\<rparr>\<lparr>C\<rparr>\<rparr> =
        (\<AA> \<times>\<^sub>C (\<BB> \<times>\<^sub>C \<CC>))\<lparr>CId\<rparr>\<lparr>cf_cat_prod_12_of_3 \<AA> \<BB> \<CC>\<lparr>ObjMap\<rparr>\<lparr>C\<rparr>\<rparr>"
      if "C \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Obj\<rparr>" for C
      using that 
      by (elim cat_prod_3_ObjE[OF assms], insert that, simp only: )
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_prod_cs_simps 
            cs_intro: cat_cs_intros cat_prod_cs_intros
        )
  qed (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)+

qed

lemma cf_cat_prod_12_of_3_is_functor'[cat_cs_intros]:
  assumes "category \<alpha> \<AA>" 
    and "category \<alpha> \<BB>" 
    and "category \<alpha> \<CC>"
    and "\<AA>' = \<AA> \<times>\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>C\<^sub>3 \<CC>"
    and "\<BB>' = \<AA> \<times>\<^sub>C (\<BB> \<times>\<^sub>C \<CC>)"
  shows "cf_cat_prod_12_of_3 \<AA> \<BB> \<CC> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  using assms(1-3) unfolding assms(4,5) by (rule cf_cat_prod_12_of_3_is_functor)



subsection\<open>Bifunctors\<close>

text\<open>
A bifunctor is defined as a functor from a product of two categories
to a category (see Chapter II-3 in \cite{mac_lane_categories_2010}).
This subsection exposes the elementary properties of the projections of the 
bifunctors established by fixing an argument in a functor (see Chapter II-3 
in \cite{mac_lane_categories_2010} for further information).
\<close>


subsubsection\<open>Definitions and elementary properties\<close>

definition bifunctor_proj_fst :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  (\<open>(_\<^bsub>_,_\<^esub>/'(/-,_/')/\<^sub>C\<^sub>F)\<close> [51, 51, 51, 51] 51)
  where "\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F =
    (\<SS>\<^bsub>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>2\<^sub>\<nat> -\<^sub>\<circ> set {1\<^sub>\<nat>}. (i = 0 ? \<AA> : \<BB>),\<SS>\<lparr>HomCod\<rparr>\<^esub>(-,set {\<langle>1\<^sub>\<nat>, b\<rangle>})) \<circ>\<^sub>C\<^sub>F
      cf_singleton 0 \<AA>"

definition bifunctor_proj_snd :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  (\<open>(_\<^bsub>_,_\<^esub>/'(/_,-/')/\<^sub>C\<^sub>F)\<close> [51, 51, 51, 51] 51)
  where "\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F =
    (\<SS>\<^bsub>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>2\<^sub>\<nat> -\<^sub>\<circ> set {0}. (i = 0 ? \<AA> : \<BB>),\<SS>\<lparr>HomCod\<rparr>\<^esub>(-,set {\<langle>0, a\<rangle>})) \<circ>\<^sub>C\<^sub>F
      cf_singleton (1\<^sub>\<nat>) \<BB>"

abbreviation bcf_ObjMap_app :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (infixl "\<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>O\<index>" 55)
  where "a \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>O\<^bsub>\<SS>\<^esub> b \<equiv> \<SS>\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>"
abbreviation bcf_ArrMap_app :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" (infixl "\<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>A\<index>" 55)
  where "g \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>A\<^bsub>\<SS>\<^esub> f \<equiv> \<SS>\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet>"


text\<open>Elementary properties.\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "category \<alpha> \<AA>" and \<BB>: "category \<alpha> \<BB>"
begin

interpretation \<AA>: category \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: category \<alpha> \<BB> by (rule \<BB>)
interpretation finite_pcategory \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 \<AA> \<BB>\<close>
  by (intro finite_pcategory_cat_prod_2 \<AA> \<BB>)

lemma cat_singleton_qm_fst_def[simp]: 
  "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. (i = 0 ? \<AA> : \<BB>)) = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>)"
proof(rule cat_eqI[of \<alpha>])
  show "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. (i = 0 ? \<AA> : \<BB>))\<lparr>Obj\<rparr> = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>)\<lparr>Obj\<rparr>"
    unfolding cat_prod_components by (subst vproduct_vsingleton_def) simp
  show [simp]: "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. (i = 0 ? \<AA> : \<BB>))\<lparr>Arr\<rparr> = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>)\<lparr>Arr\<rparr>"
    unfolding cat_prod_components by (subst vproduct_vsingleton_def) simp
  show [simp]: "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. (i = 0 ? \<AA> : \<BB>))\<lparr>Dom\<rparr> = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>)\<lparr>Dom\<rparr>"
    unfolding cat_prod_components 
    by (subst vproduct_vsingleton_def, subst (1 2) VLambda_vsingleton_def) simp
  show [simp]: 
    "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. (i = 0 ? \<AA> : \<BB>))\<lparr>Cod\<rparr> = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>)\<lparr>Cod\<rparr>"
    unfolding cat_prod_components 
    by (subst vproduct_vsingleton_def, subst (1 2) VLambda_vsingleton_def) simp
  have [simp]: 
    "f : a \<mapsto>\<^bsub>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. (i = 0 ? \<AA> : \<BB>)\<^esub> b \<longleftrightarrow> 
      f : a \<mapsto>\<^bsub>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>\<^esub> b"
    for f a b
    unfolding is_arr_def by simp
  show "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. (i = 0 ? \<AA> : \<BB>))\<lparr>Comp\<rparr> = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>)\<lparr>Comp\<rparr>"
  proof(rule vsv_eqI)
    show "vsv ((\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. (i = 0 ? \<AA> : \<BB>))\<lparr>Comp\<rparr>)"
      unfolding cat_prod_components by simp
    show "vsv ((\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>)\<lparr>Comp\<rparr>)"
      unfolding cat_prod_components by simp
    show "\<D>\<^sub>\<circ> ((\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. (i = 0 ? \<AA> : \<BB>))\<lparr>Comp\<rparr>) = 
      \<D>\<^sub>\<circ> ((\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>)\<lparr>Comp\<rparr>)"
      by (simp add: composable_arrs_def cat_cs_simps)
    show "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. (i = 0 ? \<AA> : \<BB>))\<lparr>Comp\<rparr>\<lparr>gf\<rparr> = 
      (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>)\<lparr>Comp\<rparr>\<lparr>gf\<rparr>"
      if "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. (i = 0 ? \<AA> : \<BB>))\<lparr>Comp\<rparr>)" for gf
    proof-
      from that have "gf \<in>\<^sub>\<circ> composable_arrs (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. (i = 0 ? \<AA> : \<BB>))"
        by (simp add: cat_cs_simps)
      then obtain g f a b c where gf_def: "gf = [g, f]\<^sub>\<circ>" 
        and g: "g : b \<mapsto>\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. (i = 0 ? \<AA> : \<BB>))\<^esub> c" 
        and f: "f : a \<mapsto>\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. (i = 0 ? \<AA> : \<BB>))\<^esub> b"
        by clarsimp
      then have g': "g : b \<mapsto>\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>)\<^esub> c" 
        and f': "f : a \<mapsto>\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>)\<^esub> b"
        by simp_all
      show ?thesis
        unfolding gf_def
        unfolding cat_prod_Comp_app[OF g f] cat_prod_Comp_app[OF g' f']
        by (subst (1 2) VLambda_vsingleton_def) simp
    qed
  qed
  show "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. (i = 0 ? \<AA> : \<BB>))\<lparr>CId\<rparr> = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>)\<lparr>CId\<rparr>"
    unfolding cat_prod_components 
    by (subst vproduct_vsingleton_def, subst (1 2) VLambda_vsingleton_def) simp    
qed 
  (
    simp_all add: 
      \<AA>.cat_category_cat_singleton
      pcategory.pcat_category_cat_prod 
      pcat_vsubset_index_pcategory 
      vsubset_vsingleton_leftI
  )

lemma cat_singleton_qm_snd_def[simp]: 
  "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. (i = 0 ? \<AA> : \<BB>)) = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. \<BB>)"
proof(rule cat_eqI[of \<alpha>])
  show "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. (i = 0 ? \<AA> : \<BB>))\<lparr>Obj\<rparr> = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. \<BB>)\<lparr>Obj\<rparr>"
    unfolding cat_prod_components by (subst vproduct_vsingleton_def) simp
  show [simp]: 
    "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. (i = 0 ? \<AA> : \<BB>))\<lparr>Arr\<rparr> = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. \<BB>)\<lparr>Arr\<rparr>"
    unfolding cat_prod_components by (subst vproduct_vsingleton_def) simp
  show [simp]: 
    "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. (i = 0 ? \<AA> : \<BB>))\<lparr>Dom\<rparr> = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. \<BB>)\<lparr>Dom\<rparr>"
    unfolding cat_prod_components 
    by (subst vproduct_vsingleton_def, subst (1 2) VLambda_vsingleton_def) simp
  show [simp]: 
    "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. (i = 0 ? \<AA> : \<BB>))\<lparr>Cod\<rparr> = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. \<BB>)\<lparr>Cod\<rparr>"
    unfolding cat_prod_components 
    by (subst vproduct_vsingleton_def, subst (1 2) VLambda_vsingleton_def) simp
  have [simp]: "f : a \<mapsto>\<^bsub>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. (i = 0 ? \<AA> : \<BB>)\<^esub> b \<longleftrightarrow> 
    f : a \<mapsto>\<^bsub>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. \<BB>\<^esub> b"
    for f a b
    unfolding is_arr_def by simp
  show "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. (i = 0 ? \<AA> : \<BB>))\<lparr>Comp\<rparr> = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. \<BB>)\<lparr>Comp\<rparr>"
  proof(rule vsv_eqI)
    show "vsv ((\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. (i = 0 ? \<AA> : \<BB>))\<lparr>Comp\<rparr>)"
      unfolding cat_prod_components by simp
    show "vsv ((\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. \<BB>)\<lparr>Comp\<rparr>)"
      unfolding cat_prod_components by simp
    show "\<D>\<^sub>\<circ> ((\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. (i = 0 ? \<AA> : \<BB>))\<lparr>Comp\<rparr>) = 
      \<D>\<^sub>\<circ> ((\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. \<BB>)\<lparr>Comp\<rparr>)"
      by (simp add: composable_arrs_def cat_cs_simps)
    show "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. (i = 0 ? \<AA> : \<BB>))\<lparr>Comp\<rparr>\<lparr>gf\<rparr> = 
      (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. \<BB>)\<lparr>Comp\<rparr>\<lparr>gf\<rparr>"
      if "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. (i = 0 ? \<AA> : \<BB>))\<lparr>Comp\<rparr>)" for gf
    proof-
      from that have "gf \<in>\<^sub>\<circ> composable_arrs (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. (i = 0 ? \<AA> : \<BB>))"
        by (simp add: cat_cs_simps)
      then obtain g f a b c where gf_def: "gf = [g, f]\<^sub>\<circ>" 
        and g: "g : b \<mapsto>\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. (i = 0 ? \<AA> : \<BB>))\<^esub> c" 
        and f: "f : a \<mapsto>\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. (i = 0 ? \<AA> : \<BB>))\<^esub> b"
        by clarsimp
      then have g': "g : b \<mapsto>\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. \<BB>)\<^esub> c" 
        and f': "f : a \<mapsto>\<^bsub>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. \<BB>)\<^esub> b"
        by simp_all
      show ?thesis
        unfolding gf_def
        unfolding cat_prod_Comp_app[OF g f] cat_prod_Comp_app[OF g' f']
        by (subst (1 2) VLambda_vsingleton_def) simp
    qed
  qed
  show "(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. (i = 0 ? \<AA> : \<BB>))\<lparr>CId\<rparr> = (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. \<BB>)\<lparr>CId\<rparr>"
    unfolding cat_prod_components 
    by (subst vproduct_vsingleton_def, subst (1 2) VLambda_vsingleton_def) simp    
qed 
  (
    simp_all add: 
      \<BB>.cat_category_cat_singleton
      pcategory.pcat_category_cat_prod 
      pcat_vsubset_index_pcategory 
      vsubset_vsingleton_leftI
  )

end


subsubsection\<open>Object map\<close>

context
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "category \<alpha> \<AA>" and \<BB>: "category \<alpha> \<BB>"
begin

interpretation \<AA>: category \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: category \<alpha> \<BB> by (rule \<BB>)

interpretation finite_pcategory \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 \<AA> \<BB>\<close>
  by (intro finite_pcategory_cat_prod_2 \<AA> \<BB>)

lemmas_with [OF \<AA>.category_axioms \<BB>.category_axioms, simp]:
  cat_singleton_qm_fst_def and cat_singleton_qm_snd_def

lemma bifunctor_proj_fst_ObjMap_app[cat_cs_simps]:
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
  shows "(\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<SS>\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>"
proof-

  let ?\<DD> = \<open>\<SS>\<lparr>HomCod\<rparr>\<close>
  let ?\<SS> = \<open>\<SS>\<^bsub>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>2\<^sub>\<nat>-\<^sub>\<circ>set {1\<^sub>\<nat>}.(i = 0 ? \<AA> : \<BB>),?\<DD>\<^esub>(-,set {\<langle>1\<^sub>\<nat>, b\<rangle>})\<close>
  let ?cfs = \<open>cf_singleton 0 \<AA>\<close>

  from assms have a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    by (all\<open>elim cat_prod_2_ObjE[OF \<AA> \<BB>]\<close>) auto

  from a have za: "set {\<langle>0, a\<rangle>} \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>)\<lparr>Obj\<rparr>"
    by (intro cat_singleton_ObjI[where a=a]) simp
  have [simp]: "vinsert \<langle>0, a\<rangle> (set {\<langle>1\<^sub>\<nat>, b\<rangle>}) = [a, b]\<^sub>\<circ>"
    using ord_of_nat_succ_vempty unfolding vcons_def by auto

  have "(\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = (?\<SS>\<lparr>ObjMap\<rparr> \<circ>\<^sub>\<circ> ?cfs\<lparr>ObjMap\<rparr>)\<lparr>a\<rparr>"
    unfolding bifunctor_proj_fst_def dghm_comp_components by simp
  also have "\<dots> = ?\<SS>\<lparr>ObjMap\<rparr>\<lparr>?cfs\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>"
    by (rule vsv_vcomp_at)
      (
        simp_all add:
          two a za
          cf_singleton_components 
          prodfunctor_proj_components 
          cf_singleton_ObjMap_app 
          
      ) 
  also from za have "\<dots> = \<SS>\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>" 
    unfolding two cf_singleton_ObjMap_app[OF a] prodfunctor_proj_components 
    by simp
  finally show ?thesis by simp

qed

lemma bifunctor_proj_snd_ObjMap_app[cat_cs_simps]:
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
  shows "(\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> = \<SS>\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>"
proof-

  let ?\<DD> = \<open>\<SS>\<lparr>HomCod\<rparr>\<close>
  let ?\<SS> = \<open>\<SS>\<^bsub>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>2\<^sub>\<nat>-\<^sub>\<circ>set {0}.(i = 0 ? \<AA> : \<BB>),?\<DD>\<^esub>(-,set {\<langle>0, a\<rangle>})\<close>
  let ?cfs = \<open>cf_singleton (1\<^sub>\<nat>) \<BB>\<close>

  from assms have a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    by (all\<open>elim cat_prod_2_ObjE[OF \<AA> \<BB>]\<close>) auto
  from a have za: "set {\<langle>0, a\<rangle>} \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>)\<lparr>Obj\<rparr>"
    by (intro cat_singleton_ObjI[where a=a]) simp
  from b have ob: "set {\<langle>1\<^sub>\<nat>, b\<rangle>} \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. \<BB>)\<lparr>Obj\<rparr>"
    by (intro cat_singleton_ObjI[where a=b]) simp
  have[simp]: "vinsert \<langle>1\<^sub>\<nat>, b\<rangle> (set {\<langle>0, a\<rangle>}) = [a, b]\<^sub>\<circ>"
    using ord_of_nat_succ_vempty unfolding vcons_def by auto

  have "(\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> = (?\<SS>\<lparr>ObjMap\<rparr> \<circ>\<^sub>\<circ> ?cfs\<lparr>ObjMap\<rparr>)\<lparr>b\<rparr>"
    unfolding bifunctor_proj_snd_def dghm_comp_components by simp
  also have "\<dots> = ?\<SS>\<lparr>ObjMap\<rparr>\<lparr>?cfs\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<rparr>"
    by (rule vsv_vcomp_at)
      (
        simp_all add: 
          two
          cf_singleton_components 
          prodfunctor_proj_components 
          cf_singleton_ObjMap_app 
          ob b
      ) 
  also from ob have "\<dots> = \<SS>\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>" 
    unfolding two cf_singleton_ObjMap_app[OF b] prodfunctor_proj_components 
    by simp
  finally show ?thesis by simp

qed

end


subsubsection\<open>Arrow map\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "category \<alpha> \<AA>" and \<BB>: "category \<alpha> \<BB>"
begin

interpretation \<AA>: category \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: category \<alpha> \<BB> by (rule \<BB>)

interpretation finite_pcategory \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 \<AA> \<BB>\<close>
  by (intro finite_pcategory_cat_prod_2 \<AA> \<BB>)

lemmas_with [OF \<AA>.category_axioms \<BB>.category_axioms, simp]:
  cat_singleton_qm_fst_def and cat_singleton_qm_snd_def

lemma bifunctor_proj_fst_ArrMap_app[cat_cs_simps]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "f \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
  shows "(\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = \<SS>\<lparr>ArrMap\<rparr>\<lparr>f, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>\<rparr>\<^sub>\<bullet>"
proof-

  let ?\<DD> = \<open>\<SS>\<lparr>HomCod\<rparr>\<close>
  let ?\<SS> = \<open>\<SS>\<^bsub>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>2\<^sub>\<nat>-\<^sub>\<circ>set {1\<^sub>\<nat>}.(i = 0 ? \<AA> : \<BB>),?\<DD>\<^esub>(-,set {\<langle>1\<^sub>\<nat>, b\<rangle>})\<close>
  let ?cfs = \<open>cf_singleton 0 \<AA>\<close>

  from assms(1) have "\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr> : b \<mapsto>\<^bsub>\<BB>\<^esub> b" by (auto intro: cat_cs_intros)
  then have CId_b: "\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr> \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" by auto

  from assms(2) have zf: "set {\<langle>0, f\<rangle>} \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>)\<lparr>Arr\<rparr>"
    by (intro cat_singleton_ArrI[where a=f]) simp
  from assms(1) have ob: "set {\<langle>1\<^sub>\<nat>, b\<rangle>} \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. \<BB>)\<lparr>Obj\<rparr>"
    by (intro cat_singleton_ObjI[where a=b]) simp
  have [simp]: "vinsert \<langle>0, f\<rangle> (set {\<langle>1\<^sub>\<nat>, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>\<rangle>}) = [f, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>]\<^sub>\<circ>"
    using ord_of_nat_succ_vempty unfolding vcons_def by auto

  have "(\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = (?\<SS>\<lparr>ArrMap\<rparr> \<circ>\<^sub>\<circ> ?cfs\<lparr>ArrMap\<rparr>)\<lparr>f\<rparr>"
    unfolding bifunctor_proj_fst_def dghm_comp_components by simp
  also have "\<dots> = ?\<SS>\<lparr>ArrMap\<rparr>\<lparr>?cfs\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr>"
    by (rule vsv_vcomp_at)
      (
        simp_all add:
          two
          assms(2)
          cf_singleton_components
          prodfunctor_proj_components
          cf_singleton_ArrMap_app 
          zf
      )   
  also from assms(1) zf have "\<dots> = \<SS>\<lparr>ArrMap\<rparr>\<lparr>f, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>\<rparr>\<^sub>\<bullet>" 
    unfolding cf_singleton_ArrMap_app[OF assms(2)] prodfunctor_proj_components 
    by (simp add: two cat_singleton_CId_app[OF ob])
  finally show ?thesis by simp

qed

lemma bifunctor_proj_snd_ArrMap_app[cat_cs_simps]:
  assumes "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and "g \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" 
  shows "(\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<SS>\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr>, g\<rparr>\<^sub>\<bullet>"
proof-

  let ?\<DD> = \<open>\<SS>\<lparr>HomCod\<rparr>\<close>
  let ?\<SS> = \<open>\<SS>\<^bsub>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>2\<^sub>\<nat>-\<^sub>\<circ>set {0}.(i = 0 ? \<AA> : \<BB>),?\<DD>\<^esub>(-,set {\<langle>0, a\<rangle>})\<close>
  let ?cfs = \<open>cf_singleton (1\<^sub>\<nat>) \<BB>\<close>

  from assms(1) have "\<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>\<AA>\<^esub> a" by (auto intro: cat_cs_intros)
  then have CId_a: "\<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" by auto

  from assms(2) have og: "set {\<langle>1\<^sub>\<nat>, g\<rangle>} \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. \<BB>)\<lparr>Arr\<rparr>"
    by (intro cat_singleton_ArrI[where a=g]) simp
  from assms(1) have ob: "set {\<langle>0, a\<rangle>} \<in>\<^sub>\<circ> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>)\<lparr>Obj\<rparr>"
    by (intro cat_singleton_ObjI[where a=a]) simp
  have [simp]: "vinsert \<langle>1\<^sub>\<nat>, g\<rangle> (set {\<langle>0, \<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr>\<rangle>}) = [\<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr>, g]\<^sub>\<circ>"
    using ord_of_nat_succ_vempty unfolding vcons_def by auto

  have "(\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = (?\<SS>\<lparr>ArrMap\<rparr> \<circ>\<^sub>\<circ> ?cfs\<lparr>ArrMap\<rparr>)\<lparr>g\<rparr>"
    unfolding two bifunctor_proj_snd_def dghm_comp_components by simp
  also have "\<dots> = ?\<SS>\<lparr>ArrMap\<rparr>\<lparr>?cfs\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>\<rparr>"
    by (rule vsv_vcomp_at)
      (
        simp_all add:
          two
          assms(2) 
          cf_singleton_components 
          prodfunctor_proj_components 
          cf_singleton_ArrMap_app 
          og
      )   
  also from assms(1) og have "\<dots> = \<SS>\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr>, g\<rparr>\<^sub>\<bullet>" 
    unfolding cf_singleton_ArrMap_app[OF assms(2)] prodfunctor_proj_components 
    by (simp add: two cat_singleton_CId_app[OF ob])
  finally show ?thesis by simp

qed

end


subsubsection\<open>Bifunctor projections are functors\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "category \<alpha> \<AA>" and \<BB>: "category \<alpha> \<BB>"
begin

interpretation \<AA>: category \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: category \<alpha> \<BB> by (rule \<BB>)

interpretation finite_pcategory \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 \<AA> \<BB>\<close>
  by (intro finite_pcategory_cat_prod_2 \<AA> \<BB>)

lemmas_with [OF \<AA>.category_axioms \<BB>.category_axioms, simp]:
  cat_singleton_qm_fst_def and cat_singleton_qm_snd_def

lemma bifunctor_proj_fst_is_functor:
  assumes "\<SS> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
proof-

  interpret \<SS>: is_functor \<alpha> \<open>\<AA> \<times>\<^sub>C \<BB>\<close> \<DD> \<SS> by (rule assms(1))

  show ?thesis
    unfolding bifunctor_proj_fst_def
  proof
    (
      intro cf_comp_is_functorI[where \<BB>=\<open>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>)\<close>], 
      unfold \<SS>.cf_HomCod
    )
    from assms(2) have zb: 
      "set {\<langle>1\<^sub>\<nat>, b\<rangle>} \<in>\<^sub>\<circ> (\<Prod>\<^sub>Cj\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. if j = 0 then \<AA> else \<BB>)\<lparr>Obj\<rparr>"
      unfolding cat_prod_components by (intro vproduct_vsingletonI) simp_all
    have o_zo: "set {1\<^sub>\<nat>} \<subseteq>\<^sub>\<circ> 2\<^sub>\<nat>" by clarsimp
    from pcat_prodfunctor_proj_is_functor[
        folded cat_prod_2_def, where J=\<open>set {1\<^sub>\<nat>}\<close>, OF assms(1) zb o_zo
        ]
    show "\<SS>\<^bsub>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>2\<^sub>\<nat>-\<^sub>\<circ>set {1\<^sub>\<nat>}.(i = 0 ? \<AA> : \<BB>),\<DD>\<^esub>(-,set {\<langle>1\<^sub>\<nat>, b\<rangle>}) :
      (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
      unfolding two by simp
    from category.cat_cf_singleton_is_functor[OF \<AA>.category_axioms, of 0] show 
      "cf_singleton 0 \<AA> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {0}. \<AA>)"
      by force
  qed

qed

lemma bifunctor_proj_fst_is_functor'[cat_cs_intros]:
  assumes "\<SS> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "\<AA>' = \<AA>"
  shows "\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms(1,2) unfolding assms(3) by (rule bifunctor_proj_fst_is_functor)

lemma bifunctor_proj_fst_ObjMap_vsv[cat_cs_intros]: 
  assumes "\<SS> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "vsv ((\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>)"
proof-
  interpret \<SS>: is_functor \<alpha> \<AA> \<DD> \<open>\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F\<close>
    by (rule bifunctor_proj_fst_is_functor[OF assms])
  show ?thesis by (rule \<SS>.cf_ObjMap_vsv)
qed

lemma bifunctor_proj_fst_ObjMap_vdomain[cat_cs_simps]: 
  assumes "\<SS> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> ((\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
proof-
  interpret \<SS>: is_functor \<alpha> \<AA> \<DD> \<open>\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F\<close>
    by (rule bifunctor_proj_fst_is_functor[OF assms])
  show ?thesis by (rule \<SS>.cf_ObjMap_vdomain)
qed

lemma bifunctor_proj_fst_ArrMap_vsv[cat_cs_intros]: 
  assumes "\<SS> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "vsv ((\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>)"
proof-
  interpret \<SS>: is_functor \<alpha> \<AA> \<DD> \<open>\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F\<close>
    by (rule bifunctor_proj_fst_is_functor[OF assms])
  show ?thesis by (rule \<SS>.cf_ArrMap_vsv)
qed

lemma bifunctor_proj_fst_ArrMap_vdomain[cat_cs_simps]: 
  assumes "\<SS> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> ((\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
proof-
  interpret \<SS>: is_functor \<alpha> \<AA> \<DD> \<open>\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F\<close>
    by (rule bifunctor_proj_fst_is_functor[OF assms])
  show ?thesis by (rule \<SS>.cf_ArrMap_vdomain)
qed

lemma bifunctor_proj_snd_is_functor:
  assumes "\<SS> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
proof-

  interpret \<SS>: is_functor \<alpha> \<open>\<AA> \<times>\<^sub>C \<BB>\<close> \<DD> \<SS> by (rule assms(1))

  show ?thesis
    unfolding bifunctor_proj_snd_def
  proof
    (
      intro cf_comp_is_functorI[where \<BB>=\<open>(\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. \<BB>)\<close>], 
      unfold \<SS>.cf_HomCod
    )
    from assms(2) have zb: 
      "set {\<langle>0, a\<rangle>} \<in>\<^sub>\<circ> (\<Prod>\<^sub>Cj\<in>\<^sub>\<circ>set {0}. if j = 0 then \<AA> else \<BB>)\<lparr>Obj\<rparr>"
      unfolding cat_prod_components by (intro vproduct_vsingletonI) simp_all
    have o_zo: "set {0} \<subseteq>\<^sub>\<circ> 2\<^sub>\<nat>" by clarsimp
    from 
      pcat_prodfunctor_proj_is_functor[
        folded cat_prod_2_def, where J=\<open>set {0}\<close>, OF assms(1) zb o_zo
        ]
    show "\<SS>\<^bsub>\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>2\<^sub>\<nat>-\<^sub>\<circ>set {0}.(i = 0 ? \<AA> : \<BB>),\<DD>\<^esub>(-,set {\<langle>0, a\<rangle>}) :
      (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. \<BB>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
      unfolding two by simp
    from category.cat_cf_singleton_is_functor[OF \<BB>.category_axioms, of \<open>1\<^sub>\<nat>\<close>] 
    show "cf_singleton (1\<^sub>\<nat>) \<BB> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> (\<Prod>\<^sub>Ci\<in>\<^sub>\<circ>set {1\<^sub>\<nat>}. \<BB>)"
      by force
  qed

qed

lemma bifunctor_proj_snd_is_functor'[cat_cs_intros]:
  assumes "\<SS> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and "\<BB>' = \<BB>"
  shows "\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms(1,2) unfolding assms(3) by (rule bifunctor_proj_snd_is_functor)

lemma bifunctor_proj_snd_ObjMap_vsv[cat_cs_intros]: 
  assumes "\<SS> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "vsv ((\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>)"
proof-
  interpret \<SS>: is_functor \<alpha> \<BB> \<DD> \<open>\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F\<close>
    by (rule bifunctor_proj_snd_is_functor[OF assms])
  show ?thesis by (rule \<SS>.cf_ObjMap_vsv)
qed

lemma bifunctor_proj_snd_ObjMap_vdomain[cat_cs_simps]: 
  assumes "\<SS> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> ((\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>) = \<BB>\<lparr>Obj\<rparr>"
proof-
  interpret \<SS>: is_functor \<alpha> \<BB> \<DD> \<open>\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F\<close>
    by (rule bifunctor_proj_snd_is_functor[OF assms])
  show ?thesis by (rule \<SS>.cf_ObjMap_vdomain)
qed

lemma bifunctor_proj_snd_ArrMap_vsv[cat_cs_intros]: 
  assumes "\<SS> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "vsv ((\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>)"
proof-
  interpret \<SS>: is_functor \<alpha> \<BB> \<DD> \<open>\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F\<close>
    by (rule bifunctor_proj_snd_is_functor[OF assms])
  show ?thesis by (rule \<SS>.cf_ArrMap_vsv)
qed

lemma bifunctor_proj_snd_ArrMap_vdomain[cat_cs_simps]: 
  assumes "\<SS> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> ((\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>) = \<BB>\<lparr>Arr\<rparr>"
proof-
  interpret \<SS>: is_functor \<alpha> \<BB> \<DD> \<open>\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F\<close>
    by (rule bifunctor_proj_snd_is_functor[OF assms])
  show ?thesis by (rule \<SS>.cf_ArrMap_vdomain)
qed

end



subsection\<open>Bifunctor flip\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition bifunctor_flip :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "bifunctor_flip \<AA> \<BB> \<FF> =
    [fflip (\<FF>\<lparr>ObjMap\<rparr>), fflip (\<FF>\<lparr>ArrMap\<rparr>), \<BB> \<times>\<^sub>C \<AA>, \<FF>\<lparr>HomCod\<rparr>]\<^sub>\<circ>"


text\<open>Components\<close>

lemma bifunctor_flip_components:
  shows "bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr> = fflip (\<FF>\<lparr>ObjMap\<rparr>)"
    and "bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr> = fflip (\<FF>\<lparr>ArrMap\<rparr>)"
    and "bifunctor_flip \<AA> \<BB> \<FF>\<lparr>HomDom\<rparr> = \<BB> \<times>\<^sub>C \<AA>"
    and "bifunctor_flip \<AA> \<BB> \<FF>\<lparr>HomCod\<rparr> = \<FF>\<lparr>HomCod\<rparr>"
  unfolding bifunctor_flip_def dghm_field_simps 
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Bifunctor flip object map\<close>

lemma bifunctor_flip_ObjMap_vsv[cat_cs_intros]: 
  "vsv (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>)"
  unfolding bifunctor_flip_components by (rule fflip_vsv)

lemma bifunctor_flip_ObjMap_app:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<FF> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b, a\<rparr>\<^sub>\<bullet> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>"
  using assms
  unfolding bifunctor_flip_components assms(4,5)
  by (cs_concl cs_simp: V_cs_simps cat_cs_simps cs_intro: cat_prod_cs_intros)

lemma bifunctor_flip_ObjMap_app'[cat_cs_simps]:
  assumes "ba = [b, a]\<^sub>\<circ>"
    and "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<FF> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>\<lparr>ba\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>"
  using assms(2-6) unfolding assms(1) by (rule bifunctor_flip_ObjMap_app)

lemma bifunctor_flip_ObjMap_vdomain[cat_cs_simps]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<FF> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>) = (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>"
  using assms
  unfolding bifunctor_flip_components 
  by (cs_concl cs_simp: V_cs_simps cat_cs_simps)

lemma bifunctor_flip_ObjMap_vrange[cat_cs_simps]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<FF> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<R>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>) = \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>)"
proof-
  
  interpret \<FF>: is_functor \<alpha> \<open>\<AA> \<times>\<^sub>C \<BB>\<close> \<CC> \<FF> by (rule assms(3))

  show ?thesis
  proof(intro vsubset_antisym)

    show "\<R>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>)"
    proof
      (
        intro vsv.vsv_vrange_vsubset, 
        unfold bifunctor_flip_ObjMap_vdomain[OF assms]
      )
      fix ba assume "ba \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>"
      then obtain a b
        where ba_def: "ba = [b, a]\<^sub>\<circ>" 
          and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
          and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
        by (elim cat_prod_2_ObjE[OF assms(2,1)])
      from assms a b show 
        "bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>\<lparr>ba\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>)"
        unfolding ba_def
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps cs_intro: V_cs_intros cat_prod_cs_intros
          )
    qed (auto intro: cat_cs_intros)

    show "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>)"
    proof(intro vsv.vsv_vrange_vsubset, unfold \<FF>.cf_ObjMap_vdomain)
      fix ab assume prems: "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
      then obtain a b 
        where ab_def: "ab = [a, b]\<^sub>\<circ>" 
          and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
          and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
        by (elim cat_prod_2_ObjE[OF assms(1,2)])
      from assms a b have ba: "[b, a]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>"
        by (cs_concl cs_intro: cat_prod_cs_intros)
      from assms bifunctor_flip_ObjMap_vsv prems a b ba show 
        "\<FF>\<lparr>ObjMap\<rparr>\<lparr>ab\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>)"
        by (cs_concl cs_simp: ab_def cat_cs_simps cs_intro: V_cs_intros)
    qed auto

  qed

qed


subsubsection\<open>Bifunctor flip arrow map\<close>

lemma bifunctor_flip_ArrMap_vsv[cat_cs_intros]: 
  "vsv (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>)"
  unfolding bifunctor_flip_components by (rule fflip_vsv)

lemma bifunctor_flip_ArrMap_app:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<FF> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "g \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
    and "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
  shows "bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f, g\<rparr>\<^sub>\<bullet> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet>"
  using assms
  unfolding bifunctor_flip_components
  by (cs_concl cs_simp: V_cs_simps cat_cs_simps cs_intro: cat_prod_cs_intros)

lemma bifunctor_flip_ArrMap_app'[cat_cs_simps]:
  assumes "fg = [f, g]\<^sub>\<circ>"
    and "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<FF> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "g \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
    and "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
  shows "bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>\<lparr>fg\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet>"
  using assms(2-6) unfolding assms(1) by (rule bifunctor_flip_ArrMap_app)

lemma bifunctor_flip_ArrMap_vdomain[cat_cs_simps]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<FF> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>) = (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Arr\<rparr>"
  using assms
  unfolding bifunctor_flip_components 
  by (cs_concl cs_simp: V_cs_simps cat_cs_simps)

lemma bifunctor_flip_ArrMap_vrange[cat_cs_simps]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<FF> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<R>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>) = \<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>)"
proof-
  
  interpret \<FF>: is_functor \<alpha> \<open>\<AA> \<times>\<^sub>C \<BB>\<close> \<CC> \<FF> by (rule assms(3))

  show ?thesis
  proof(intro vsubset_antisym)

    show "\<R>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>)"
    proof
      (
        intro vsv.vsv_vrange_vsubset, 
        unfold bifunctor_flip_ArrMap_vdomain[OF assms]
      )
      fix fg assume "fg \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Arr\<rparr>"
      then obtain f g
        where fg_def: "fg = [f, g]\<^sub>\<circ>" 
          and f: "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" 
          and g: "g \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
        by (elim cat_prod_2_ArrE[OF assms(2,1)])
      from f obtain a b where f: "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b" by (auto intro: is_arrI)
      from g obtain a' b' where g: "g : a' \<mapsto>\<^bsub>\<AA>\<^esub> b'" by (auto intro: is_arrI)
      from \<FF>.cf_ArrMap_vsv assms f g show 
        "bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>\<lparr>fg\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>)"
        unfolding fg_def
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps 
              cs_intro: V_cs_intros cat_cs_intros cat_prod_cs_intros
          )
    qed (auto intro: cat_cs_intros)

    show "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>)"
    proof(intro vsv.vsv_vrange_vsubset, unfold \<FF>.cf_ArrMap_vdomain)
      fix gf assume prems: "gf \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Arr\<rparr>"
      then obtain g f 
        where gf_def: "gf = [g, f]\<^sub>\<circ>" 
          and g: "g \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
          and f: "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
        by (elim cat_prod_2_ArrE[OF assms(1,2)])
      from assms g f have fg: "[f, g]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Arr\<rparr>"
        by (cs_concl cs_intro: cat_prod_cs_intros)
      from assms bifunctor_flip_ArrMap_vsv prems g f fg show 
        "\<FF>\<lparr>ArrMap\<rparr>\<lparr>gf\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>)"
        unfolding gf_def
        by (cs_concl cs_simp: cat_cs_simps cs_intro: V_cs_intros)
    qed auto

  qed

qed


subsubsection\<open>Bifunctor flip is a bifunctor\<close>

lemma bifunctor_flip_is_functor:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<FF> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "bifunctor_flip \<AA> \<BB> \<FF> : \<BB> \<times>\<^sub>C \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> "
proof-

  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(2))
  interpret \<FF>: is_functor \<alpha> \<open>\<AA> \<times>\<^sub>C \<BB>\<close> \<CC> \<FF> by (rule assms)

  show ?thesis
  proof(intro is_functorI')
    show "vfsequence (bifunctor_flip \<AA> \<BB> \<FF>)"
      unfolding bifunctor_flip_def by simp
    from assms(1,2) show "category \<alpha> (\<BB> \<times>\<^sub>C \<AA>)"
      by (cs_concl cs_intro: cat_cs_intros)
    show "vcard (bifunctor_flip \<AA> \<BB> \<FF>) = 4\<^sub>\<nat>"
      unfolding bifunctor_flip_def by (simp add: nat_omega_simps)
    show "vsv (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>)" by (auto intro: cat_cs_intros)
    show "vsv (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>)" by (auto intro: cat_cs_intros)
    from assms show "\<D>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>) = (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps)
    from assms \<FF>.cf_ObjMap_vrange show 
      "\<R>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps)
    from assms show "\<D>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>) = (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Arr\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps)
    show "bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>\<lparr>gf\<rparr> :
      bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>\<lparr>ba\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub>
      bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b'a'\<rparr>"
      if "gf : ba \<mapsto>\<^bsub>\<BB> \<times>\<^sub>C \<AA>\<^esub> b'a'" for ba b'a' gf
    proof-
      from that obtain g f a b a' b'
        where gf_def: "gf = [g, f]\<^sub>\<circ>"
          and ba_def: "ba = [b, a]\<^sub>\<circ>"
          and b'a'_def: "b'a' = [b', a']\<^sub>\<circ>"
          and g: "g : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
          and f: "f : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
        by (elim cat_prod_2_is_arrE[OF assms(2,1)])
      from assms g f show ?thesis
        unfolding gf_def ba_def b'a'_def
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros
          )
    qed
    show 
      "bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>\<lparr>gg' \<circ>\<^sub>A\<^bsub>\<BB> \<times>\<^sub>C \<AA>\<^esub> ff'\<rparr> =
        bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>\<lparr>gg'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> 
        bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>\<lparr>ff'\<rparr>"
      if gg': "gg' : bb' \<mapsto>\<^bsub>\<BB> \<times>\<^sub>C \<AA>\<^esub> cc'" and ff': "ff' : aa' \<mapsto>\<^bsub>\<BB> \<times>\<^sub>C \<AA>\<^esub> bb'" 
      for bb' cc' gg' aa' ff'
    proof-
      obtain g g' b b' c c' 
        where gg'_def: "gg' = [g, g']\<^sub>\<circ>"
          and bb'_def: "bb' = [b, b']\<^sub>\<circ>"
          and cc'_def: "cc' = [c, c']\<^sub>\<circ>"   
          and g: "g : b \<mapsto>\<^bsub>\<BB>\<^esub> c"  
          and g': "g' : b' \<mapsto>\<^bsub>\<AA>\<^esub> c'"
        by (elim cat_prod_2_is_arrE[OF assms(2,1) gg'])
      moreover obtain f f' a a' b'' b''' 
        where ff'_def: "ff' = [f, f']\<^sub>\<circ>"
          and aa'_def: "aa' = [a, a']\<^sub>\<circ>"
          and "bb' = [b'', b''']\<^sub>\<circ>"   
          and "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b''"  
          and "f' : a' \<mapsto>\<^bsub>\<AA>\<^esub> b'''"
        by (elim cat_prod_2_is_arrE[OF assms(2,1) ff'])
      ultimately have f: "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b" and f': "f' : a' \<mapsto>\<^bsub>\<AA>\<^esub> b'" 
        by (auto simp: cat_op_simps)
      from assms g g' f f' have [cat_cs_simps]:
        "\<FF>\<lparr>ArrMap\<rparr>\<lparr>g' \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f', g \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f\<rparr>\<^sub>\<bullet> = 
          \<FF>\<lparr>ArrMap\<rparr>\<lparr>[g', g]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>\<AA> \<times>\<^sub>C \<BB>\<^esub> [f', f]\<^sub>\<circ>\<rparr>"
        by (cs_concl cs_simp: cat_prod_2_Comp_app cs_intro: cat_prod_cs_intros)
      from assms g g' f f' show 
        "bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>\<lparr>gg' \<circ>\<^sub>A\<^bsub>\<BB> \<times>\<^sub>C \<AA>\<^esub> ff'\<rparr> =
          bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>\<lparr>gg'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub>
          bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>\<lparr>ff'\<rparr>"
        unfolding gg'_def ff'_def (*slow*)
        by 
          (
            cs_concl 
              cs_simp: cat_prod_cs_simps cat_cs_simps
              cs_intro: cat_prod_cs_intros cat_cs_intros
          )
    qed
    show 
      "bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>\<lparr>(\<BB> \<times>\<^sub>C \<AA>)\<lparr>CId\<rparr>\<lparr>ba\<rparr>\<rparr> = 
        \<CC>\<lparr>CId\<rparr>\<lparr>bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>\<lparr>ba\<rparr>\<rparr>"
      if "ba \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>" for ba
    proof-
      from that obtain b a 
        where ba_def: "ba = [b, a]\<^sub>\<circ>" 
          and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
          and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
        by (elim cat_prod_2_ObjE[rotated 2]) (auto intro: cat_cs_intros)
      from assms b a have [cat_cs_simps]:
        "\<FF>\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr>, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>\<rparr>\<^sub>\<bullet> =
          \<FF>\<lparr>ArrMap\<rparr>\<lparr>(\<AA> \<times>\<^sub>C \<BB>)\<lparr>CId\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>\<rparr>"
        by (cs_concl cs_simp: cat_prod_2_CId_app cs_intro: cat_prod_cs_intros)
      from assms b a show ?thesis
        unfolding ba_def
        by 
          (
            cs_concl 
              cs_intro: cat_cs_intros cat_prod_cs_intros 
              cs_simp: cat_prod_cs_simps cat_cs_simps
          )
    qed
  qed (auto simp: bifunctor_flip_components cat_cs_simps cat_cs_intros)

qed

lemma bifunctor_flip_is_functor'[cat_cs_intros]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<FF> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<DD> = \<BB> \<times>\<^sub>C \<AA>"
  shows "bifunctor_flip \<AA> \<BB> \<FF> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1-3) unfolding assms(4) by (intro bifunctor_flip_is_functor)


subsubsection\<open>Double-flip of a bifunctor\<close>

lemma bifunctor_flip_flip[cat_cs_simps]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<FF> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "bifunctor_flip \<BB> \<AA> (bifunctor_flip \<AA> \<BB> \<FF>) = \<FF>"
proof(rule cf_eqI)

  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(2))
  interpret \<FF>: is_functor \<alpha> \<open>\<AA> \<times>\<^sub>C \<BB>\<close> \<CC> \<FF> by (rule assms(3))

  from assms show 
    "bifunctor_flip \<BB> \<AA> (bifunctor_flip \<AA> \<BB> \<FF>) : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: cat_cs_intros)

  from assms have ObjMap_dom_lhs: 
    "\<D>\<^sub>\<circ> (bifunctor_flip \<BB> \<AA> (bifunctor_flip \<AA> \<BB> \<FF>)\<lparr>ObjMap\<rparr>) = 
      (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  have ObjMap_dom_rhs: "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) = (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>" 
    by (simp add: cat_cs_simps)
  from assms have ArrMap_dom_lhs: 
    "\<D>\<^sub>\<circ> (bifunctor_flip \<BB> \<AA> (bifunctor_flip \<AA> \<BB> \<FF>)\<lparr>ArrMap\<rparr>) =
      (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  have ArrMap_dom_rhs: "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) = (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Arr\<rparr>" 
    by (simp add: cat_cs_simps)

  show "bifunctor_flip \<BB> \<AA> (bifunctor_flip \<AA> \<BB> \<FF>)\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>"
  proof(rule vsv_eqI, unfold ObjMap_dom_lhs ObjMap_dom_rhs)
    fix ab assume "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
    then obtain a b
      where ab_def: "ab = [a, b]\<^sub>\<circ>" and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
      by (rule cat_prod_2_ObjE[OF assms(1,2)])
    from assms a b show 
      "bifunctor_flip \<BB> \<AA> (bifunctor_flip \<AA> \<BB> \<FF>)\<lparr>ObjMap\<rparr>\<lparr>ab\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>ab\<rparr>"
      unfolding ab_def
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed (auto simp: cat_cs_intros)

  show "bifunctor_flip \<BB> \<AA> (bifunctor_flip \<AA> \<BB> \<FF>)\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
  proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
    fix ab assume "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Arr\<rparr>"
    then obtain a b
      where ab_def: "ab = [a, b]\<^sub>\<circ>" and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" 
      by (rule cat_prod_2_ArrE[OF assms(1,2)])
    from assms a b show 
      "bifunctor_flip \<BB> \<AA> (bifunctor_flip \<AA> \<BB> \<FF>)\<lparr>ArrMap\<rparr>\<lparr>ab\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>ab\<rparr>"
      unfolding ab_def 
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed (auto simp: cat_cs_intros)

qed (simp_all add: assms(3))


subsubsection\<open>A projection of a bifunctor flip\<close>

lemma bifunctor_flip_proj_snd[cat_cs_simps]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<FF> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "bifunctor_flip \<AA> \<BB> \<FF>\<^bsub>\<BB>,\<AA>\<^esub>(b,-)\<^sub>C\<^sub>F = \<FF>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F"
proof(rule cf_eqI)

  from assms show f_\<FF>b: "bifunctor_flip \<AA> \<BB> \<FF>\<^bsub>\<BB>,\<AA>\<^esub>(b,-)\<^sub>C\<^sub>F : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: cat_cs_intros)
  from assms show \<FF>b: "\<FF>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: cat_cs_intros)

  from assms have ObjMap_dom_lhs:
    "\<D>\<^sub>\<circ> ((bifunctor_flip \<AA> \<BB> \<FF>\<^bsub>\<BB>,\<AA>\<^esub>(b,-)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms have ObjMap_dom_rhs: "\<D>\<^sub>\<circ> ((\<FF>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)
  from assms have ArrMap_dom_lhs:
    "\<D>\<^sub>\<circ> ((bifunctor_flip \<AA> \<BB> \<FF>\<^bsub>\<BB>,\<AA>\<^esub>(b,-)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms have ArrMap_dom_rhs: "\<D>\<^sub>\<circ> ((\<FF>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>) = \<AA>\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)

  show "(bifunctor_flip \<AA> \<BB> \<FF>\<^bsub>\<BB>,\<AA>\<^esub>(b,-)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr> = (\<FF>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>"
  proof(rule vsv_eqI, unfold ObjMap_dom_lhs ObjMap_dom_rhs)
    from assms show "vsv ((bifunctor_flip \<AA> \<BB> \<FF>\<^bsub>\<BB>,\<AA>\<^esub>(b,-)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>)"
      by (intro bifunctor_proj_snd_ObjMap_vsv)
        (cs_concl cs_intro: cat_cs_intros)
    from assms show "vsv ((\<FF>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>)"
      by (intro bifunctor_proj_fst_ObjMap_vsv)
        (cs_concl cs_intro: cat_cs_intros)
    fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    with assms show 
      "(bifunctor_flip \<AA> \<BB> \<FF>\<^bsub>\<BB>,\<AA>\<^esub>(b,-)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = 
        (\<FF>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_prod_cs_intros)
  qed simp

  show 
    "(bifunctor_flip \<AA> \<BB> \<FF>\<^bsub>\<BB>,\<AA>\<^esub>(b,-)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr> = (\<FF>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>"
  proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
    from assms show "vsv ((bifunctor_flip \<AA> \<BB> \<FF>\<^bsub>\<BB>,\<AA>\<^esub>(b,-)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>)"
      by (intro bifunctor_proj_snd_ArrMap_vsv)
        (cs_concl cs_intro: cat_cs_intros)
    from assms show "vsv ((\<FF>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>)"
      by (intro bifunctor_proj_fst_ArrMap_vsv)
        (cs_concl cs_intro: cat_cs_intros)
    fix f assume "f \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
    with assms show 
      "(bifunctor_flip \<AA> \<BB> \<FF>\<^bsub>\<BB>,\<AA>\<^esub>(b,-)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
        (\<FF>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  qed simp

qed simp_all

lemma bifunctor_flip_proj_fst[cat_cs_simps]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<FF> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "bifunctor_flip \<AA> \<BB> \<FF>\<^bsub>\<BB>,\<AA>\<^esub>(-,a)\<^sub>C\<^sub>F = \<FF>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F"
proof-
  from assms have f_\<FF>: "bifunctor_flip \<AA> \<BB> \<FF> : \<BB> \<times>\<^sub>C \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: cat_cs_intros)
  show ?thesis
    by 
      (
        rule 
          bifunctor_flip_proj_snd
            [
              OF assms(2,1) f_\<FF> assms(4), 
              unfolded bifunctor_flip_flip[OF assms(1,2,3)],
              symmetric
            ]
      )
qed


subsubsection\<open>A flip of a bifunctor isomorphism\<close>

lemma bifunctor_flip_is_iso_functor:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<FF> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "bifunctor_flip \<AA> \<BB> \<FF> : \<BB> \<times>\<^sub>C \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> \<CC> "
proof-

  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(2))
  interpret \<FF>: is_iso_functor \<alpha> \<open>\<AA> \<times>\<^sub>C \<BB>\<close> \<CC> \<FF> by (rule assms(3))

  from assms have f_\<FF>: "bifunctor_flip \<AA> \<BB> \<FF> : \<BB> \<times>\<^sub>C \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> "
    by (cs_concl cs_intro: cat_cs_intros)

  from f_\<FF> have ObjMap_dom: 
    "\<D>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>) = (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>" 
    by (cs_concl cs_simp: cat_cs_simps)
  from f_\<FF> have ArrMap_dom: 
    "\<D>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>) = (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Arr\<rparr>" 
    by (cs_concl cs_simp: cat_cs_simps)

  show ?thesis
  proof(intro is_iso_functorI' vsv.vsv_valeq_v11I, unfold ObjMap_dom ArrMap_dom)
    from assms show "bifunctor_flip \<AA> \<BB> \<FF> : \<BB> \<times>\<^sub>C \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    fix ba b'a'
    assume prems: 
      "ba \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>"
      "b'a' \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>"
      "bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>\<lparr>ba\<rparr> = bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b'a'\<rparr>"
    from prems(1) obtain b a
      where ba_def: "ba = [b, a]\<^sub>\<circ>" 
        and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
        and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
      by (elim cat_prod_2_ObjE[OF assms(2,1)])
    from prems(2) obtain a' b'
      where b'a'_def: "b'a' = [b', a']\<^sub>\<circ>" 
        and b': "b' \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
        and a': "a' \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
      by (rule cat_prod_2_ObjE[OF assms(2,1)])
    from prems(3) assms a b b' a' have \<FF>ab_\<FF>a'b': 
      "\<FF>\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>a', b'\<rparr>\<^sub>\<bullet>"
      unfolding ba_def b'a'_def
      by (cs_prems cs_simp: cat_cs_simps cs_intro: cf_cs_intros)
    from assms a b a' b' have "[a, b]\<^sub>\<circ> = [a', b']\<^sub>\<circ>"
      by 
        (
          cs_concl 
            cs_intro: 
              \<FF>.ObjMap.v11_eq_iff[THEN iffD1, OF _ _ \<FF>ab_\<FF>a'b'] 
              cat_prod_cs_intros
        )
    then show "ba = b'a'" unfolding ba_def b'a'_def by simp
  next
    fix fg f'g' assume prems:
      "fg \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Arr\<rparr>"
      "f'g' \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Arr\<rparr>" 
      "bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>\<lparr>fg\<rparr> = bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f'g'\<rparr>"
    from prems(1) obtain f g
      where fg_def: "fg = [f, g]\<^sub>\<circ>" 
        and f: "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" 
        and g: "g \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" 
      by (elim cat_prod_2_ArrE[OF assms(2,1)])
    from prems(2) obtain f' g'
      where f'g'_def: "f'g' = [f', g']\<^sub>\<circ>" 
        and f': "f' \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" 
        and g': "g' \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" 
      by (rule cat_prod_2_ArrE[OF assms(2,1)])
    from prems(3) assms f g f' g' have \<FF>gf_\<FF>g'f': 
      "\<FF>\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>g', f'\<rparr>\<^sub>\<bullet>"
      unfolding fg_def f'g'_def
      by (cs_prems cs_simp: cat_cs_simps cs_intro: cf_cs_intros)
    from assms g f g' f' have "[g, f]\<^sub>\<circ> = [g', f']\<^sub>\<circ>"
      by 
        (
          cs_concl 
            cs_simp: 
            cs_intro:
              \<FF>.ArrMap.v11_eq_iff[THEN iffD1, OF _ _ \<FF>gf_\<FF>g'f'] 
              cat_prod_cs_intros
        )
    then show "fg = f'g'" unfolding fg_def f'g'_def by simp
  next
    
    show "\<R>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
    proof(rule vsubset_antisym)
      show "\<R>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
      proof(rule vsv.vsv_vrange_vsubset, unfold ObjMap_dom)
        fix ba assume "ba \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>"
        then obtain b a
          where ba_def: "ba = [b, a]\<^sub>\<circ>" 
            and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
            and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
          by (elim cat_prod_2_ObjE[OF assms(2,1)])
        from assms b a show "bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>\<lparr>ba\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
          unfolding ba_def 
          by (cs_concl cs_intro: cat_cs_intros cf_cs_intros cat_prod_cs_intros)
      qed (auto simp: cat_cs_intros)
      show "\<CC>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>)"
      proof(intro vsubsetI)
        fix c assume prems: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
        from prems obtain ab 
          where ab: "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>" and \<FF>ab: "\<FF>\<lparr>ObjMap\<rparr>\<lparr>ab\<rparr> = c"
          by blast
        from ab obtain b a
          where ab_def: "ab = [a, b]\<^sub>\<circ>" 
            and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
            and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
          by (elim cat_prod_2_ObjE[OF assms(1,2)])
        show "c \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>)"
        proof(intro vsv.vsv_vimageI2', unfold ObjMap_dom)
          from assms a b show "[b, a]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>"
            by (cs_concl cs_intro: cat_prod_cs_intros)
          from assms b a prems show "c = bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b, a\<rparr>\<^sub>\<bullet>"
            by 
              (
                cs_concl 
                  cs_simp: \<FF>ab[unfolded ab_def] cat_cs_simps
                  cs_intro: cf_cs_intros
              )
        qed (auto intro: cat_cs_intros)
      qed
    qed

    show "\<R>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>) = \<CC>\<lparr>Arr\<rparr>"
    proof(rule vsubset_antisym)
      show "\<R>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
      proof(rule vsv.vsv_vrange_vsubset, unfold ArrMap_dom)
        show "vsv (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>)" by (auto intro: cat_cs_intros)
        fix fg assume "fg \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Arr\<rparr>"
        then obtain f g
          where fg_def: "fg = [f, g]\<^sub>\<circ>" 
            and f: "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" 
            and g: "g \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" 
          by (elim cat_prod_2_ArrE[OF assms(2,1)])
        from g f obtain a b a' b' 
          where f: "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b" and g: "g : a' \<mapsto>\<^bsub>\<AA>\<^esub> b'"
          by (auto intro!: is_arrI)
        from assms f g show "bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>\<lparr>fg\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
          by (cs_concl cs_simp: fg_def cs_intro: cat_cs_intros cat_prod_cs_intros)
      qed
      show "\<CC>\<lparr>Arr\<rparr> \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>)"
      proof(intro vsubsetI)
        fix c assume prems: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
        from prems obtain ab 
          where ab: "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Arr\<rparr>" and \<FF>ab: "\<FF>\<lparr>ArrMap\<rparr>\<lparr>ab\<rparr> = c"
          by blast
        from ab obtain b a
          where ab_def: "ab = [a, b]\<^sub>\<circ>" 
            and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" 
            and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" 
          by (elim cat_prod_2_ArrE[OF assms(1,2)])
        show "c \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>)"
        proof(intro vsv.vsv_vimageI2', unfold ArrMap_dom)
          from assms a b show "[b, a]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Arr\<rparr>"
            by (cs_concl cs_intro: cat_prod_cs_intros)
          from assms b a prems show "c = bifunctor_flip \<AA> \<BB> \<FF>\<lparr>ArrMap\<rparr>\<lparr>b, a\<rparr>\<^sub>\<bullet>"
            by 
              (
                cs_concl 
                  cs_simp: \<FF>ab[unfolded ab_def] cat_cs_simps 
                  cs_intro: cat_cs_intros 
              )
        qed (auto intro: cat_cs_intros)
      qed
    qed

  qed (auto intro: cat_cs_intros)

qed



subsection\<open>Array bifunctor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter II-3 in \cite{mac_lane_categories_2010}.\<close>

definition cf_array :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "cf_array \<BB> \<CC> \<DD> \<FF> \<GG> =
    [
      (\<lambda>a\<in>\<^sub>\<circ>(\<BB> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>. \<GG> (vpfst a)\<lparr>ObjMap\<rparr>\<lparr>vpsnd a\<rparr>),
      (
        \<lambda>f\<in>\<^sub>\<circ>(\<BB> \<times>\<^sub>C \<CC>)\<lparr>Arr\<rparr>.
          \<GG> (\<BB>\<lparr>Cod\<rparr>\<lparr>vpfst f\<rparr>)\<lparr>ArrMap\<rparr>\<lparr>vpsnd f\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub>
          \<FF> (\<CC>\<lparr>Dom\<rparr>\<lparr>vpsnd f\<rparr>)\<lparr>ArrMap\<rparr>\<lparr>vpfst f\<rparr>
      ),
      \<BB> \<times>\<^sub>C \<CC>,
      \<DD>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_array_components:
  shows "cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ObjMap\<rparr> =
    (\<lambda>a\<in>\<^sub>\<circ>(\<BB> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>. \<GG> (vpfst a)\<lparr>ObjMap\<rparr>\<lparr>vpsnd a\<rparr>)"
    and "cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ArrMap\<rparr> =
      (
        \<lambda>f\<in>\<^sub>\<circ>(\<BB> \<times>\<^sub>C \<CC>)\<lparr>Arr\<rparr>.
          \<GG> (\<BB>\<lparr>Cod\<rparr>\<lparr>vpfst f\<rparr>)\<lparr>ArrMap\<rparr>\<lparr>vpsnd f\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub>
          \<FF> (\<CC>\<lparr>Dom\<rparr>\<lparr>vpsnd f\<rparr>)\<lparr>ArrMap\<rparr>\<lparr>vpfst f\<rparr>
      )"
    and "cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>HomDom\<rparr> = \<BB> \<times>\<^sub>C \<CC>"
    and "cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>HomCod\<rparr> = \<DD>"
  unfolding cf_array_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

lemma cf_array_ObjMap_vsv: "vsv (cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ObjMap\<rparr>)"
  unfolding cf_array_components by simp

lemma cf_array_ObjMap_vdomain[cat_cs_simps]:
  "\<D>\<^sub>\<circ> (cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ObjMap\<rparr>) = (\<BB> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
  unfolding cf_array_components by simp

lemma cf_array_ObjMap_app[cat_cs_simps]:
  assumes "[b, c]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
  shows "cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b, c\<rparr>\<^sub>\<bullet> = \<GG> b\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
  using assms unfolding cf_array_components by (simp add: nat_omega_simps)

lemma cf_array_ObjMap_vrange:
  assumes "category \<alpha> \<BB>" 
    and "category \<alpha> \<CC>"
    and "\<And>b. b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr> \<Longrightarrow> \<GG> b : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "\<R>\<^sub>\<circ> (cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
proof(rule vsv.vsv_vrange_vsubset, unfold cf_array_ObjMap_vdomain)
  show "vsv (cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ObjMap\<rparr>)" by (rule cf_array_ObjMap_vsv)
  fix x assume prems: "x \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
  then obtain b c where x_def: "x = [b, c]\<^sub>\<circ>" 
    and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
    and c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    by (elim cat_prod_2_ObjE[OF assms(1,2)])
  interpret \<GG>b: is_functor \<alpha> \<CC> \<DD> \<open>\<GG> b\<close> by (rule assms(3)[OF b])
  from prems c show "cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ObjMap\<rparr>\<lparr>x\<rparr> \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
    unfolding x_def cf_array_components 
    by (auto simp: nat_omega_simps cat_cs_intros)
qed


subsubsection\<open>Arrow map\<close>

lemma cf_array_ArrMap_vsv: "vsv (cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ArrMap\<rparr>)"
  unfolding cf_array_components by simp

lemma cf_array_ArrMap_vdomain[cat_cs_simps]:
  "\<D>\<^sub>\<circ> (cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ArrMap\<rparr>) = (\<BB> \<times>\<^sub>C \<CC>)\<lparr>Arr\<rparr>"
  unfolding cf_array_components by simp

lemma cf_array_ArrMap_app[cat_cs_simps]:
  assumes "category \<alpha> \<BB>"
    and "category \<alpha> \<CC>"
    and "g : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
    and "f : a' \<mapsto>\<^bsub>\<CC>\<^esub> b'"
  shows "cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> = 
    \<GG> b\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF> a'\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>"
proof-
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(1))
  interpret \<CC>: category \<alpha> \<CC> by (rule assms(2))
  from cat_prod_2_is_arrI[OF assms] have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<CC>)\<lparr>Arr\<rparr>" by auto
  with assms show ?thesis
    unfolding cf_array_components by (simp add: nat_omega_simps cat_cs_simps)
qed

lemma cf_array_ArrMap_vrange:
  assumes "category \<alpha> \<BB>" 
    and "category \<alpha> \<CC>"
    and "\<And>c. c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> \<FF> c : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<And>b. b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr> \<Longrightarrow> \<GG> b : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and [cat_cs_simps]: 
      "\<And>b c. b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr> \<Longrightarrow> c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> \<GG> b\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> = \<FF> c\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
  shows "\<R>\<^sub>\<circ> (cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Arr\<rparr>"
proof(rule vsv.vsv_vrange_vsubset, unfold cf_array_ArrMap_vdomain)
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(1))
  interpret \<CC>: category \<alpha> \<CC> by (rule assms(2))
  interpret \<BB>\<CC>: category \<alpha> \<open>\<BB> \<times>\<^sub>C \<CC>\<close> 
    by (simp add: \<BB>.category_axioms \<CC>.category_axioms category_cat_prod_2)
  fix gf assume prems: "gf \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<CC>)\<lparr>Arr\<rparr>"
  then obtain bc b'c' where gf: "gf : bc \<mapsto>\<^bsub>\<BB> \<times>\<^sub>C \<CC>\<^esub> b'c'" by auto
  then obtain g f b c b' c'
    where gf_def: "gf = [g, f]\<^sub>\<circ>" 
      and "bc = [b, c]\<^sub>\<circ>" 
      and "b'c' = [b', c']\<^sub>\<circ>"
      and g: "g : b \<mapsto>\<^bsub>\<BB>\<^esub> b'" 
      and f: "f : c \<mapsto>\<^bsub>\<CC>\<^esub> c'"
    by (elim cat_prod_2_is_arrE[OF assms(1,2)])
  then have b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
    and b': "b' \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
    and c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and c': "c' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    by auto
  interpret \<GG>b: is_functor \<alpha> \<CC> \<DD> \<open>\<GG> b\<close> by (rule assms(4)[OF b])
  interpret \<FF>c: is_functor \<alpha> \<BB> \<DD> \<open>\<FF> c\<close> by (rule assms(3)[OF c])
  interpret \<GG>b': is_functor \<alpha> \<CC> \<DD> \<open>\<GG> b'\<close> by (rule assms(4)[OF b'])
  interpret \<FF>c': is_functor \<alpha> \<BB> \<DD> \<open>\<FF> c'\<close> by (rule assms(3)[OF c'])
  from 
    \<GG>b.is_functor_axioms 
    \<FF>c.is_functor_axioms 
    \<GG>b'.is_functor_axioms 
    \<FF>c'.is_functor_axioms 
    \<GG>b.HomCod.category_axioms 
    g f
  have "\<GG> b'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF> c\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<in>\<^sub>\<circ> \<DD>\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  with g f prems show "cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>gf\<rparr> \<in>\<^sub>\<circ> \<DD>\<lparr>Arr\<rparr>"
    unfolding gf_def cf_array_components 
    by (simp add: nat_omega_simps cat_cs_simps)
qed (simp add: cf_array_ArrMap_vsv)


subsubsection\<open>Array bifunctor is a bifunctor\<close>

lemma cf_array_specification:
  \<comment>\<open>See Proposition 1 from Chapter II-3 in \cite{mac_lane_categories_2010}.\<close>
  assumes "category \<alpha> \<BB>"
    and "category \<alpha> \<CC>"
    and "category \<alpha> \<DD>"
    and "\<And>c. c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> \<FF> c : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<And>b. b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr> \<Longrightarrow> \<GG> b : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<And>b c. b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr> \<Longrightarrow> c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> \<GG> b\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> = \<FF> c\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    and 
      "\<And>b c b' c' f g. \<lbrakk> f : b \<mapsto>\<^bsub>\<BB>\<^esub> b'; g : c \<mapsto>\<^bsub>\<CC>\<^esub> c' \<rbrakk> \<Longrightarrow>
        \<GG> b'\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF> c\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
          \<FF> c'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<GG> b\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>"
  shows cf_array_is_functor: "cf_array \<BB> \<CC> \<DD> \<FF> \<GG> : \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and cf_array_ObjMap_app_fst: "\<And>b c. \<lbrakk> b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>; c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow>
      cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b, c\<rparr>\<^sub>\<bullet> = \<FF> c\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    and cf_array_ObjMap_app_snd: "\<And>b c. \<lbrakk> b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>; c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow>
      cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b, c\<rparr>\<^sub>\<bullet> = \<GG> b\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
    and cf_array_ArrMap_app_fst: "\<And>a b f c. \<lbrakk> f : a \<mapsto>\<^bsub>\<BB>\<^esub> b; c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>\<rbrakk> \<Longrightarrow>
      cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f, \<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr>\<^sub>\<bullet> = \<FF> c\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
    and cf_array_ArrMap_app_snd: "\<And>a b g c. \<lbrakk> g : a \<mapsto>\<^bsub>\<CC>\<^esub> b; c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow>
      cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>\<BB>\<lparr>CId\<rparr>\<lparr>c\<rparr>, g\<rparr>\<^sub>\<bullet> = \<GG> c\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>"
proof-

  interpret \<BB>: category \<alpha> \<BB> by (rule assms(1))
  interpret \<CC>: category \<alpha> \<CC> by (rule assms(2))
  interpret \<DD>: category \<alpha> \<DD> by (rule assms(3))

  from assms(4) have [cat_cs_intros]: "\<FF> c : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<DD>'" 
    if "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "\<BB>' = \<BB>" "\<DD>' = \<DD>" "\<alpha>' = \<alpha>" for \<alpha>' c \<BB>' \<DD>'
    using that(1) unfolding that(2-4) by (intro assms(4))
  from assms(4) have [cat_cs_intros]: "\<GG> c : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<DD>'" 
    if "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" "\<CC>' = \<CC>" "\<DD>' = \<DD>" "\<alpha>' = \<alpha>" for \<alpha>' c \<CC>' \<DD>'
    using that(1) unfolding that(2-4) by (intro assms(5))

  show "cf_array \<BB> \<CC> \<DD> \<FF> \<GG> : \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  proof(intro is_functorI')
    show "vfsequence (cf_array \<BB> \<CC> \<DD> \<FF> \<GG>)" unfolding cf_array_def by auto
    from assms(1,2) show "category \<alpha> (\<BB> \<times>\<^sub>C \<CC>)"
      by (simp add: category_cat_prod_2)
    show "vcard (cf_array \<BB> \<CC> \<DD> \<FF> \<GG>) = 4\<^sub>\<nat>"
      unfolding cf_array_def by (simp add: nat_omega_simps)
    show "\<R>\<^sub>\<circ> (cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
      by (rule cf_array_ObjMap_vrange) (auto simp: assms intro: cat_cs_intros)
    show cf_array_is_arrI: "cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>ff'\<rparr> :
      cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ObjMap\<rparr>\<lparr>aa'\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ObjMap\<rparr>\<lparr>bb'\<rparr>"
      if ff': "ff' : aa' \<mapsto>\<^bsub>\<BB> \<times>\<^sub>C \<CC>\<^esub> bb'" for aa' bb' ff'
    proof-
      obtain f f' a a' b b' 
        where ff'_def: "ff' = [f, f']\<^sub>\<circ>"
          and aa'_def: "aa' = [a, a']\<^sub>\<circ>"
          and bb'_def: "bb' = [b, b']\<^sub>\<circ>"   
          and f: "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"  
          and f': "f' : a' \<mapsto>\<^bsub>\<CC>\<^esub> b'"
        by (elim cat_prod_2_is_arrE[OF \<BB>.category_axioms \<CC>.category_axioms ff'])
      then have a: "a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
        and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
        and a': "a' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
        and b': "b' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
        by auto
      from f' assms(5)[OF a] a have
        "\<GG> a\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> : \<FF> a'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> \<FF> b'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        by (cs_concl cs_simp: assms(6)[symmetric] cs_intro: cat_cs_intros)
      with assms(1-3) f f' assms(4)[OF b'] show ?thesis
        unfolding ff'_def aa'_def bb'_def
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps assms(6) 
              cs_intro: cat_cs_intros cat_prod_cs_intros
          )
    qed
    show "cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>gg' \<circ>\<^sub>A\<^bsub>\<BB> \<times>\<^sub>C \<CC>\<^esub> ff'\<rparr> = 
      cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>gg'\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>ff'\<rparr>"
      if gg': "gg' : bb' \<mapsto>\<^bsub>\<BB> \<times>\<^sub>C \<CC>\<^esub> cc'" and ff': "ff' : aa' \<mapsto>\<^bsub>\<BB> \<times>\<^sub>C \<CC>\<^esub> bb'" 
      for bb' cc' gg' aa' ff'
    proof-
      obtain g g' b b' c c' 
        where gg'_def: "gg' = [g, g']\<^sub>\<circ>"
          and bb'_def: "bb' = [b, b']\<^sub>\<circ>"
          and cc'_def: "cc' = [c, c']\<^sub>\<circ>"   
          and g: "g : b \<mapsto>\<^bsub>\<BB>\<^esub> c"  
          and g': "g' : b' \<mapsto>\<^bsub>\<CC>\<^esub> c'"
        by (elim cat_prod_2_is_arrE[OF \<BB>.category_axioms \<CC>.category_axioms gg'])
      moreover obtain f f' a a' b'' b''' 
        where ff'_def: "ff' = [f, f']\<^sub>\<circ>"
          and aa'_def: "aa' = [a, a']\<^sub>\<circ>"
          and "bb' = [b'', b''']\<^sub>\<circ>"   
          and f: "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b''"  
          and f': "f' : a' \<mapsto>\<^bsub>\<CC>\<^esub> b'''"
        by (elim cat_prod_2_is_arrE[OF \<BB>.category_axioms \<CC>.category_axioms ff'])
      ultimately have f: "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b" and f': "f' : a' \<mapsto>\<^bsub>\<CC>\<^esub> b'" by auto
      with g have a: "a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
        and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
        and c: "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
        and a': "a' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
        and b': "b' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
        and c': "b' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
        by auto
      from f' assms(5)[OF a] a have \<GG>a_f':
        "\<GG> a\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> : \<FF> a'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> \<FF> b'\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        by (cs_concl cs_simp: assms(6)[symmetric] cs_intro: cat_cs_intros)
      from f' b assms(5)[OF b] have \<GG>b_f': 
        "\<GG> b\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> : \<FF> a'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> \<FF> b'\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
        by (cs_concl cs_simp: assms(6)[symmetric] cs_intro: cat_cs_intros)
      from f' c assms(5)[OF c] have \<GG>c_f':
        "\<GG> c\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> : \<FF> a'\<lparr>ObjMap\<rparr>\<lparr>c\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> \<FF> b'\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
        by (cs_concl cs_simp: assms(6)[symmetric] cs_intro: cat_cs_intros)
      have
        "\<FF> b'\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> (\<FF> b'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<GG> a\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>) = 
          (\<GG> c\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF> a'\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>) \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF> a'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
        using f' f g \<GG>b_f' assms(4)[OF a'] assms(4)[OF b'] 
        by (cs_concl cs_simp: cat_cs_simps assms(7) cs_intro: cat_cs_intros)
      also have "\<dots> =
        \<GG> c\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> (\<FF> a'\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF> a'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>)"
        using assms(2) f f' g g' assms(4)[OF a'] assms(5)[OF c]
        by (cs_concl cs_simp: assms(6) cat_cs_simps cs_intro: cat_cs_intros)
      finally have [cat_cs_simps]:
        "\<FF> b'\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> (\<FF> b'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<GG> a\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>) =
          \<GG> c\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> (\<FF> a'\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> \<FF> a'\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>)"
        by simp
      show ?thesis
        using 
          \<GG>a_f' \<GG>c_f'
          f f' 
          g g'
          assms(1,2)  
          assms(4)[OF a'] 
          assms(4)[OF c']
          assms(5)[OF c]
        unfolding gg'_def ff'_def aa'_def bb'_def cc'_def (*slow*)
        by 
          (
            cs_concl
              cs_simp: assms(6,7) cat_prod_cs_simps cat_cs_simps 
              cs_intro: cat_prod_cs_intros cat_cs_intros
          )
    qed
    show "cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>(\<BB> \<times>\<^sub>C \<CC>)\<lparr>CId\<rparr>\<lparr>cc'\<rparr>\<rparr> = 
      \<DD>\<lparr>CId\<rparr>\<lparr>cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ObjMap\<rparr>\<lparr>cc'\<rparr>\<rparr>"
      if "cc' \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>" for cc'
    proof-
      from that obtain c c' 
        where cc'_def: "cc' = [c, c']\<^sub>\<circ>" 
          and c: "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
          and c': "c' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
        by (elim cat_prod_2_ObjE[rotated 2]) (auto intro: cat_cs_intros)
      from assms(1,2,3) c c' assms(4)[OF c'] assms(5)[OF c] show ?thesis
        unfolding cc'_def (*very slow*)
        by 
          (
            cs_concl 
              cs_simp: cat_prod_cs_simps cat_cs_simps assms(6) 
              cs_intro: cat_cs_intros cat_prod_cs_intros
          )
    qed
  qed (auto simp: cf_array_components cat_cs_intros)

  show "cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ObjMap\<rparr> \<lparr>b, c\<rparr>\<^sub>\<bullet> = \<FF> c\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    if "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for b c
    using that assms(1,2,3)
    by (cs_concl cs_simp: cat_cs_simps assms(6) cs_intro: cat_prod_cs_intros)
  show "cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ObjMap\<rparr> \<lparr>b, c\<rparr>\<^sub>\<bullet> = \<GG> b\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>"
    if "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for b c 
    using that assms(1,2,3)
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_prod_cs_intros)
  show "cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ArrMap\<rparr> \<lparr>f, \<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>\<rparr>\<^sub>\<bullet> = \<FF> c\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
    if f: "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b" and c: "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" for a b f c
  proof-
    from f have "a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" by auto
    from assms(5)[OF this(1)] assms(5)[OF this(2)] assms(4)[OF c] show ?thesis
      using assms(1,2,3) f c 
      by (cs_concl cs_simp: cat_cs_simps assms(6) cs_intro: cat_cs_intros)
  qed

  show "cf_array \<BB> \<CC> \<DD> \<FF> \<GG>\<lparr>ArrMap\<rparr> \<lparr>\<BB>\<lparr>CId\<rparr>\<lparr>c\<rparr>, g\<rparr>\<^sub>\<bullet> = \<GG> c\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>"
    if g: "g : a \<mapsto>\<^bsub>\<CC>\<^esub> b" and c: "c \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" for a b g c
  proof-
    from g have "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
    from assms(4)[OF this(1)] assms(4)[OF this(2)] assms(5)[OF c] show ?thesis
      using assms(1,2,3) g c
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps assms(6)[symmetric] cs_intro: cat_cs_intros
        )
  qed

qed



subsection\<open>Composition of a covariant bifunctor and covariant functors\<close>


subsubsection\<open>Definition and elementary properties.\<close>

definition cf_bcomp :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_bcomp \<SS> \<FF> \<GG> =
    [
      (
        \<lambda>a\<in>\<^sub>\<circ>(\<FF>\<lparr>HomDom\<rparr> \<times>\<^sub>C \<GG>\<lparr>HomDom\<rparr>)\<lparr>Obj\<rparr>.
          \<SS>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>vpfst a\<rparr>, \<GG>\<lparr>ObjMap\<rparr>\<lparr>vpsnd a\<rparr>\<rparr>\<^sub>\<bullet>
      ),
      (
        \<lambda>f\<in>\<^sub>\<circ>(\<FF>\<lparr>HomDom\<rparr> \<times>\<^sub>C \<GG>\<lparr>HomDom\<rparr>)\<lparr>Arr\<rparr>.
          \<SS>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>vpfst f\<rparr>, \<GG>\<lparr>ArrMap\<rparr>\<lparr>vpsnd f\<rparr>\<rparr>\<^sub>\<bullet>
      ),
      \<FF>\<lparr>HomDom\<rparr> \<times>\<^sub>C \<GG>\<lparr>HomDom\<rparr>,
      \<SS>\<lparr>HomCod\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_bcomp_components:
  shows "cf_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr> = 
      (
        \<lambda>a\<in>\<^sub>\<circ>(\<FF>\<lparr>HomDom\<rparr> \<times>\<^sub>C \<GG>\<lparr>HomDom\<rparr>)\<lparr>Obj\<rparr>.
          \<SS>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>vpfst a\<rparr>, \<GG>\<lparr>ObjMap\<rparr>\<lparr>vpsnd a\<rparr>\<rparr>\<^sub>\<bullet>
      )"
    and "cf_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr> = 
      (
        \<lambda>f\<in>\<^sub>\<circ>(\<FF>\<lparr>HomDom\<rparr> \<times>\<^sub>C \<GG>\<lparr>HomDom\<rparr>)\<lparr>Arr\<rparr>.
          \<SS>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>vpfst f\<rparr>, \<GG>\<lparr>ArrMap\<rparr>\<lparr>vpsnd f\<rparr>\<rparr>\<^sub>\<bullet>
      )"
    and "cf_bcomp \<SS> \<FF> \<GG>\<lparr>HomDom\<rparr> = \<FF>\<lparr>HomDom\<rparr> \<times>\<^sub>C \<GG>\<lparr>HomDom\<rparr>"
    and "cf_bcomp \<SS> \<FF> \<GG>\<lparr>HomCod\<rparr> = \<SS>\<lparr>HomCod\<rparr>"
  unfolding cf_bcomp_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

lemma cf_bcomp_ObjMap_vsv: "vsv (cf_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>)"
  unfolding cf_bcomp_components by simp

lemma cf_bcomp_ObjMap_vdomain[cat_cs_simps]:
  assumes "\<FF> : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<GG> : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (cf_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>) = (\<BB>' \<times>\<^sub>C \<CC>')\<lparr>Obj\<rparr>"
proof-
  interpret \<FF>: is_functor \<alpha> \<BB>' \<BB> \<FF> by (rule assms)
  interpret \<GG>: is_functor \<alpha> \<CC>' \<CC> \<GG> by (rule assms)
  show ?thesis unfolding cf_bcomp_components by (simp add: cat_cs_simps)
qed

lemma cf_bcomp_ObjMap_app[cat_cs_simps]:
  assumes "\<FF> : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<BB>' \<times>\<^sub>C \<CC>')\<lparr>Obj\<rparr>"
  shows "cf_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> = \<SS>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>, \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<rparr>\<^sub>\<bullet>"
proof-
  interpret \<FF>: is_functor \<alpha> \<BB>' \<BB> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<CC>' \<CC> \<GG> by (rule assms(2))
  from assms show ?thesis 
    unfolding cf_bcomp_components 
    by (simp_all add: cat_cs_simps nat_omega_simps)
qed

lemma cf_bcomp_ObjMap_vrange:
  assumes "\<FF> : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<SS> : \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "\<R>\<^sub>\<circ> (cf_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
proof
  (
    rule vsv.vsv_vrange_vsubset, 
    unfold cf_bcomp_ObjMap_vdomain[OF assms(1,2)]
  )
  interpret \<FF>: is_functor \<alpha> \<BB>' \<BB> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<CC>' \<CC> \<GG> by (rule assms(2))
  show "vsv (cf_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>)" by (rule cf_bcomp_ObjMap_vsv)
  fix bc assume "bc \<in>\<^sub>\<circ> (\<BB>' \<times>\<^sub>C \<CC>')\<lparr>Obj\<rparr>"
  with \<FF>.HomDom.category_axioms \<GG>.HomDom.category_axioms obtain b c 
    where bc_def: "bc = [b, c]\<^sub>\<circ>" and b: "b \<in>\<^sub>\<circ> \<BB>'\<lparr>Obj\<rparr>" and c: "c \<in>\<^sub>\<circ> \<CC>'\<lparr>Obj\<rparr>"
    by (elim cat_prod_2_ObjE[rotated -1])  
  from assms b c show "cf_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>\<lparr>bc\<rparr> \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
    unfolding bc_def 
    by 
      (
        cs_concl
          cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros
      )
qed


subsubsection\<open>Arrow map\<close>

lemma cf_bcomp_ArrMap_vsv: "vsv (cf_bcomp \<CC> \<SS> \<FF>\<lparr>ArrMap\<rparr>)"
  unfolding cf_bcomp_components by simp

lemma cf_bcomp_ArrMap_vdomain[cat_cs_simps]:
  assumes "\<FF> : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<GG> : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (cf_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr>) = (\<BB>' \<times>\<^sub>C \<CC>')\<lparr>Arr\<rparr>"
proof-
  interpret \<FF>: is_functor \<alpha> \<BB>' \<BB> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<CC>' \<CC> \<GG> by (rule assms(2))
  show ?thesis unfolding cf_bcomp_components by (simp add: cat_cs_simps)
qed

lemma cf_bcomp_ArrMap_app[cat_cs_simps]:
  assumes "\<FF> : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<BB>' \<times>\<^sub>C \<CC>')\<lparr>Arr\<rparr>"
  shows "cf_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> = \<SS>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>, \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr>\<^sub>\<bullet>"
proof-
  interpret \<FF>: is_functor \<alpha> \<BB>' \<BB> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<CC>' \<CC> \<GG> by (rule assms(2))
  from assms show ?thesis 
    unfolding cf_bcomp_components by (simp_all add: nat_omega_simps cat_cs_simps)
qed

lemma cf_bcomp_ArrMap_vrange:
  assumes "\<FF> : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<SS> : \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "\<R>\<^sub>\<circ> (cf_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Arr\<rparr>"
proof(rule vsv.vsv_vrange_vsubset, unfold cf_bcomp_ArrMap_vdomain[OF assms(1,2)])
  interpret \<FF>: is_functor \<alpha> \<BB>' \<BB> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<CC>' \<CC> \<GG> by (rule assms(2))
  fix gf assume "gf \<in>\<^sub>\<circ> (\<BB>' \<times>\<^sub>C \<CC>')\<lparr>Arr\<rparr>"
  with \<FF>.HomDom.category_axioms \<GG>.HomDom.category_axioms obtain g f
    where gf_def: "gf = [g, f]\<^sub>\<circ>" and g: "g \<in>\<^sub>\<circ> \<BB>'\<lparr>Arr\<rparr>" and f: "f \<in>\<^sub>\<circ> \<CC>'\<lparr>Arr\<rparr>"
    by (elim cat_prod_2_ArrE[rotated -1])  
  from g obtain a b where g: "g : a \<mapsto>\<^bsub>\<BB>'\<^esub> b" by auto
  from f obtain a' b' where f: "f : a' \<mapsto>\<^bsub>\<CC>'\<^esub> b'" by auto
  from assms g f show "cf_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>gf\<rparr> \<in>\<^sub>\<circ> \<DD>\<lparr>Arr\<rparr>"
    unfolding gf_def 
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros
      )
qed (simp add: cf_bcomp_ArrMap_vsv)


subsubsection\<open>
Composition of a covariant bifunctor and 
covariant functors is a functor
\<close>

lemma cf_bcomp_is_functor:
  assumes "\<FF> : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<SS> : \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "cf_bcomp \<SS> \<FF> \<GG> : \<BB>' \<times>\<^sub>C \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
proof-

  interpret \<FF>: is_functor \<alpha> \<BB>' \<BB> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<CC>' \<CC> \<GG> by (rule assms(2))
  interpret \<SS>: is_functor \<alpha> \<open>\<BB> \<times>\<^sub>C \<CC>\<close> \<DD> \<SS> by (rule assms(3))

  show ?thesis
  proof(intro is_functorI')
    show "vfsequence (cf_bcomp \<SS> \<FF> \<GG>)" unfolding cf_bcomp_def by simp
    show "category \<alpha> (\<BB>' \<times>\<^sub>C \<CC>')"
      by 
        (
          simp add: 
            \<FF>.HomDom.category_axioms  
            \<GG>.HomDom.category_axioms 
            category_cat_prod_2
        )
    show "vcard (cf_bcomp \<SS> \<FF> \<GG>) = 4\<^sub>\<nat>"
      unfolding cf_bcomp_def by (simp add: nat_omega_simps)
    from assms show "\<R>\<^sub>\<circ> (cf_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
      by (rule cf_bcomp_ObjMap_vrange)
    show "cf_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>ff'\<rparr> :
      cf_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>\<lparr>aa'\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub> cf_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>\<lparr>bb'\<rparr>"
    if ff': "ff' : aa' \<mapsto>\<^bsub>\<BB>' \<times>\<^sub>C \<CC>'\<^esub> bb'" for aa' bb' ff'
    proof-
      obtain f f' a a' b b' 
        where ff'_def: "ff' = [f, f']\<^sub>\<circ>"
          and aa'_def: "aa' = [a, a']\<^sub>\<circ>"
          and bb'_def: "bb' = [b, b']\<^sub>\<circ>"   
          and f: "f : a \<mapsto>\<^bsub>\<BB>'\<^esub> b"  
          and f': "f' : a' \<mapsto>\<^bsub>\<CC>'\<^esub> b'"
        by 
          (
            elim 
              cat_prod_2_is_arrE[
                OF \<FF>.HomDom.category_axioms \<GG>.HomDom.category_axioms ff'
                ]
          )
      from assms f f' show ?thesis
        unfolding ff'_def aa'_def bb'_def
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros
          )
    qed
    show "cf_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>gg' \<circ>\<^sub>A\<^bsub>\<BB>' \<times>\<^sub>C \<CC>'\<^esub> ff'\<rparr> =
      cf_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>gg'\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> cf_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>ff'\<rparr>"
      if gg': "gg' : bb' \<mapsto>\<^bsub>\<BB>' \<times>\<^sub>C \<CC>'\<^esub> cc'" 
        and ff': "ff' : aa' \<mapsto>\<^bsub>\<BB>' \<times>\<^sub>C \<CC>'\<^esub> bb'"
      for bb' cc' gg' aa' ff'
    proof-
      obtain g g' b b' c c' 
        where gg'_def: "gg' = [g, g']\<^sub>\<circ>"
          and bb'_def: "bb' = [b, b']\<^sub>\<circ>"
          and cc'_def: "cc' = [c, c']\<^sub>\<circ>"   
          and g: "g : b \<mapsto>\<^bsub>\<BB>'\<^esub> c"  
          and g': "g' : b' \<mapsto>\<^bsub>\<CC>'\<^esub> c'"
        by 
          (
            elim cat_prod_2_is_arrE[
              OF \<FF>.HomDom.category_axioms \<GG>.HomDom.category_axioms gg'
              ]
          )
      moreover obtain f f' a a' b'' b''' 
        where ff'_def: "ff' = [f, f']\<^sub>\<circ>"
          and aa'_def: "aa' = [a, a']\<^sub>\<circ>"
          and "bb' = [b'', b''']\<^sub>\<circ>"   
          and f: "f : a \<mapsto>\<^bsub>\<BB>'\<^esub> b''"  
          and f': "f' : a' \<mapsto>\<^bsub>\<CC>'\<^esub> b'''"
        by 
          (
            elim cat_prod_2_is_arrE[
              OF \<FF>.HomDom.category_axioms \<GG>.HomDom.category_axioms ff'
              ]
          )
      ultimately have f: "f : a \<mapsto>\<^bsub>\<BB>'\<^esub> b" and f': "f' : a' \<mapsto>\<^bsub>\<CC>'\<^esub> b'" by auto
      from assms f f' g g' have [cat_cs_simps]:
        "[\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>, \<GG>\<lparr>ArrMap\<rparr>\<lparr>g'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>]\<^sub>\<circ> = 
          [\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>, \<GG>\<lparr>ArrMap\<rparr>\<lparr>g'\<rparr>]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>\<BB> \<times>\<^sub>C \<CC>\<^esub> [\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>, \<GG>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>]\<^sub>\<circ>"
        by 
          (
            cs_concl 
              cs_simp: cat_prod_cs_simps
              cs_intro: cat_cs_intros cat_prod_cs_intros
          )
      from assms f f' g g' show ?thesis
        unfolding gg'_def ff'_def aa'_def bb'_def cc'_def
        by
          (
            cs_concl
              cs_simp: cat_prod_cs_simps cat_cs_simps 
              cs_intro: cat_cs_intros cat_prod_cs_intros
          )
    qed
    show 
      "cf_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>(\<BB>' \<times>\<^sub>C \<CC>')\<lparr>CId\<rparr>\<lparr>cc'\<rparr>\<rparr> = 
        \<DD>\<lparr>CId\<rparr>\<lparr>cf_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>\<lparr>cc'\<rparr>\<rparr>"
      if "cc' \<in>\<^sub>\<circ> (\<BB>' \<times>\<^sub>C \<CC>')\<lparr>Obj\<rparr>" for cc'
    proof-
      from that obtain c c' 
        where cc'_def: "cc' = [c, c']\<^sub>\<circ>" 
          and c: "c \<in>\<^sub>\<circ> \<BB>'\<lparr>Obj\<rparr>"
          and c': "c' \<in>\<^sub>\<circ> \<CC>'\<lparr>Obj\<rparr>"
        by (elim cat_prod_2_ObjE[rotated 2]) (auto intro: cat_cs_intros)
      from assms c c' have [cat_cs_simps]: 
        "[\<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>, \<CC>\<lparr>CId\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>c'\<rparr>\<rparr>]\<^sub>\<circ> = 
          (\<BB> \<times>\<^sub>C \<CC>)\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>, \<GG>\<lparr>ObjMap\<rparr>\<lparr>c'\<rparr>\<rparr>\<^sub>\<bullet>"
        by
          (
            cs_concl
              cs_simp: cat_prod_cs_simps
              cs_intro: cat_cs_intros cat_prod_cs_intros
          )
      from assms c c' show ?thesis
        unfolding cc'_def
        by
          (
            cs_concl 
              cs_simp: cat_prod_cs_simps cat_cs_simps
              cs_intro: cat_cs_intros cat_prod_cs_intros
          )
    qed
  qed (auto simp: cf_bcomp_components cat_cs_intros cat_cs_simps)

qed

lemma cf_bcomp_is_functor'[cat_cs_intros]:
  assumes "\<FF> : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<SS> : \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<AA>' =  \<BB>' \<times>\<^sub>C \<CC>'"
  shows "cf_bcomp \<SS> \<FF> \<GG> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms(1-3) unfolding assms(4) by (rule cf_bcomp_is_functor)



subsection\<open>Composition of a contracovariant bifunctor and covariant functors\<close>

text\<open>
The term \<open>contracovariant bifunctor\<close> is used to refer to a bifunctor
that is contravariant in the first argument and covariant in the second
argument.
\<close>

definition cf_cn_cov_bcomp :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_cn_cov_bcomp \<SS> \<FF> \<GG> =
    [
      (
        \<lambda>a\<in>\<^sub>\<circ>(op_cat (\<FF>\<lparr>HomDom\<rparr>) \<times>\<^sub>C \<GG>\<lparr>HomDom\<rparr>)\<lparr>Obj\<rparr>.
          \<SS>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>vpfst a\<rparr>, \<GG>\<lparr>ObjMap\<rparr>\<lparr>vpsnd a\<rparr>\<rparr>\<^sub>\<bullet>
      ),
      (
        \<lambda>f\<in>\<^sub>\<circ>(op_cat (\<FF>\<lparr>HomDom\<rparr>) \<times>\<^sub>C \<GG>\<lparr>HomDom\<rparr>)\<lparr>Arr\<rparr>.
          \<SS>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>vpfst f\<rparr>, \<GG>\<lparr>ArrMap\<rparr>\<lparr>vpsnd f\<rparr>\<rparr>\<^sub>\<bullet>
      ),
      op_cat (\<FF>\<lparr>HomDom\<rparr>) \<times>\<^sub>C \<GG>\<lparr>HomDom\<rparr>,
      \<SS>\<lparr>HomCod\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_cn_cov_bcomp_components:
  shows "cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr> =
      (
        \<lambda>a\<in>\<^sub>\<circ>(op_cat (\<FF>\<lparr>HomDom\<rparr>) \<times>\<^sub>C \<GG>\<lparr>HomDom\<rparr>)\<lparr>Obj\<rparr>.
          \<SS>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>vpfst a\<rparr>, \<GG>\<lparr>ObjMap\<rparr>\<lparr>vpsnd a\<rparr>\<rparr>\<^sub>\<bullet>
      )"
    and "cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr> =
      (
        \<lambda>f\<in>\<^sub>\<circ>(op_cat (\<FF>\<lparr>HomDom\<rparr>) \<times>\<^sub>C \<GG>\<lparr>HomDom\<rparr>)\<lparr>Arr\<rparr>.
          \<SS>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>vpfst f\<rparr>, \<GG>\<lparr>ArrMap\<rparr>\<lparr>vpsnd f\<rparr>\<rparr>\<^sub>\<bullet>
      )"
    and "cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>HomDom\<rparr> = op_cat (\<FF>\<lparr>HomDom\<rparr>) \<times>\<^sub>C \<GG>\<lparr>HomDom\<rparr>"
    and "cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>HomCod\<rparr> = \<SS>\<lparr>HomCod\<rparr>"
  unfolding cf_cn_cov_bcomp_def dghm_field_simps 
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

lemma cf_cn_cov_bcomp_ObjMap_vsv: "vsv (cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>)"
  unfolding cf_cn_cov_bcomp_components by simp

lemma cf_cn_cov_bcomp_ObjMap_vdomain[cat_cs_simps]:
  assumes "\<FF> : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<GG> : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>) = (op_cat \<BB>' \<times>\<^sub>C \<CC>')\<lparr>Obj\<rparr>"
proof-
  interpret \<FF>: is_functor \<alpha> \<BB>' \<BB> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<CC>' \<CC> \<GG> by (rule assms(2))
  show ?thesis 
    unfolding cf_cn_cov_bcomp_components 
    by (simp add: nat_omega_simps cat_cs_simps)
qed

lemma cf_cn_cov_bcomp_ObjMap_app[cat_cs_simps]:
  assumes "\<FF> : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (op_cat \<BB>' \<times>\<^sub>C \<CC>')\<lparr>Obj\<rparr>"
  shows 
    "cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> =
      \<SS>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>, \<GG>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<rparr>\<^sub>\<bullet>"
proof-
  interpret \<FF>: is_functor \<alpha> \<BB>' \<BB> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<CC>' \<CC> \<GG> by (rule assms(2))
  from assms show ?thesis 
    unfolding cf_cn_cov_bcomp_components 
    by (simp_all add: cat_cs_simps nat_omega_simps)
qed

lemma cf_cn_cov_bcomp_ObjMap_vrange:
  assumes "\<FF> : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<SS> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "\<R>\<^sub>\<circ> (cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
proof
  (
    rule vsv.vsv_vrange_vsubset, 
    unfold cf_cn_cov_bcomp_ObjMap_vdomain[OF assms(1,2)]
  )
  interpret \<FF>: is_functor \<alpha> \<BB>' \<BB> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<CC>' \<CC> \<GG> by (rule assms(2))
  show "vsv (cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>)" 
    by (rule cf_cn_cov_bcomp_ObjMap_vsv)
  fix bc assume "bc \<in>\<^sub>\<circ> (op_cat \<BB>' \<times>\<^sub>C \<CC>')\<lparr>Obj\<rparr>"
  with \<FF>.HomDom.category_op \<GG>.HomDom.category_axioms obtain b c 
    where bc_def: "bc = [b, c]\<^sub>\<circ>" 
      and b: "b \<in>\<^sub>\<circ> op_cat \<BB>'\<lparr>Obj\<rparr>" 
      and c: "c \<in>\<^sub>\<circ> \<CC>'\<lparr>Obj\<rparr>"
    by (elim cat_prod_2_ObjE[rotated -1])  
  from assms b c show "cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>\<lparr>bc\<rparr> \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
    unfolding bc_def cat_op_simps
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps 
          cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
      )
qed


subsubsection\<open>Arrow map\<close>

lemma cf_cn_cov_bcomp_ArrMap_vsv: "vsv (cf_cn_cov_bcomp \<CC> \<SS> \<FF>\<lparr>ArrMap\<rparr>)"
  unfolding cf_cn_cov_bcomp_components by simp

lemma cf_cn_cov_bcomp_ArrMap_vdomain[cat_cs_simps]:
  assumes "\<FF> : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<GG> : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr>) = (op_cat \<BB>' \<times>\<^sub>C \<CC>')\<lparr>Arr\<rparr>"
proof-
  interpret \<FF>: is_functor \<alpha> \<BB>' \<BB> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<CC>' \<CC> \<GG> by (rule assms(2))
  show ?thesis unfolding cf_cn_cov_bcomp_components by (simp add: cat_cs_simps)
qed

lemma cf_cn_cov_bcomp_ArrMap_app[cat_cs_simps]:
  assumes "\<FF> : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> (op_cat \<BB>' \<times>\<^sub>C \<CC>')\<lparr>Arr\<rparr>"
  shows "cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> =
    \<SS>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>, \<GG>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<rparr>\<^sub>\<bullet>"
proof-
  interpret \<FF>: is_functor \<alpha> \<BB>' \<BB> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<CC>' \<CC> \<GG> by (rule assms(2))
  from assms show ?thesis 
    unfolding cf_cn_cov_bcomp_components 
    by (simp_all add: nat_omega_simps cat_cs_simps)
qed

lemma cf_cn_cov_bcomp_ArrMap_vrange:
  assumes "\<FF> : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<SS> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "\<R>\<^sub>\<circ> (cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Arr\<rparr>"
proof(rule vsv.vsv_vrange_vsubset, unfold cf_cn_cov_bcomp_ArrMap_vdomain[OF assms(1,2)])
  interpret \<FF>: is_functor \<alpha> \<BB>' \<BB> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<CC>' \<CC> \<GG> by (rule assms(2))
  fix gf assume "gf \<in>\<^sub>\<circ> (op_cat \<BB>' \<times>\<^sub>C \<CC>')\<lparr>Arr\<rparr>"
  with \<FF>.HomDom.category_op \<GG>.HomDom.category_axioms obtain g f
    where gf_def: "gf = [g, f]\<^sub>\<circ>" 
      and g: "g \<in>\<^sub>\<circ> op_cat \<BB>'\<lparr>Arr\<rparr>" 
      and f: "f \<in>\<^sub>\<circ> \<CC>'\<lparr>Arr\<rparr>"
    by (elim cat_prod_2_ArrE[rotated -1])  
  from g obtain a b where g: "g : a \<mapsto>\<^bsub>\<BB>'\<^esub> b" unfolding cat_op_simps by auto
  from f obtain a' b' where f: "f : a' \<mapsto>\<^bsub>\<CC>'\<^esub> b'" by auto
  from assms g f show "cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>gf\<rparr> \<in>\<^sub>\<circ> \<DD>\<lparr>Arr\<rparr>"
    unfolding gf_def 
    by
      (
        cs_concl
          cs_simp: cat_cs_simps 
          cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
      )
qed (rule cf_cn_cov_bcomp_ArrMap_vsv)


subsubsection\<open>
Composition of a contracovariant bifunctor and functors is a functor
\<close>

lemma cf_cn_cov_bcomp_is_functor:
  assumes "\<FF> : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<SS> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "cf_cn_cov_bcomp \<SS> \<FF> \<GG> : op_cat \<BB>' \<times>\<^sub>C \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
proof-

  interpret \<FF>: is_functor \<alpha> \<BB>' \<BB> \<FF> by (rule assms(1))
  interpret \<GG>: is_functor \<alpha> \<CC>' \<CC> \<GG> by (rule assms(2))
  interpret \<SS>: is_functor \<alpha> \<open>op_cat \<BB> \<times>\<^sub>C \<CC>\<close> \<DD> \<SS> by (rule assms(3))

  show ?thesis
  proof(intro is_functorI')
    show "vfsequence (cf_cn_cov_bcomp \<SS> \<FF> \<GG>)" 
      unfolding cf_cn_cov_bcomp_def by simp
    show "category \<alpha> (op_cat \<BB>' \<times>\<^sub>C \<CC>')"
      by 
        (
          simp add: 
            \<FF>.HomDom.category_op \<GG>.HomDom.category_axioms category_cat_prod_2
        )
    show "vcard (cf_cn_cov_bcomp \<SS> \<FF> \<GG>) = 4\<^sub>\<nat>"
      unfolding cf_cn_cov_bcomp_def by (simp add: nat_omega_simps)
    from assms show "\<R>\<^sub>\<circ> (cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
      by (rule cf_cn_cov_bcomp_ObjMap_vrange)
    show 
      "cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>ff'\<rparr> :
        cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>\<lparr>aa'\<rparr> \<mapsto>\<^bsub>\<DD>\<^esub>
        cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>\<lparr>bb'\<rparr>"
      if ff': "ff' : aa' \<mapsto>\<^bsub>op_cat \<BB>' \<times>\<^sub>C \<CC>'\<^esub> bb'" for aa' bb' ff'
    proof-
      obtain f f' a a' b b' 
        where ff'_def: "ff' = [f, f']\<^sub>\<circ>"
          and aa'_def: "aa' = [a, a']\<^sub>\<circ>"
          and bb'_def: "bb' = [b, b']\<^sub>\<circ>"   
          and f: "f : a \<mapsto>\<^bsub>op_cat \<BB>'\<^esub> b"  
          and f': "f' : a' \<mapsto>\<^bsub>\<CC>'\<^esub> b'"
        by 
          (
            elim 
              cat_prod_2_is_arrE[
                OF \<FF>.HomDom.category_op \<GG>.HomDom.category_axioms ff'
                ]
          )
      from assms f f' show ?thesis
        unfolding ff'_def aa'_def bb'_def cat_op_simps
        by (*slow*)
          (
            cs_concl
              cs_simp: cat_cs_simps cat_op_simps
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
    qed
    show 
      "cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>gg' \<circ>\<^sub>A\<^bsub>op_cat \<BB>' \<times>\<^sub>C \<CC>'\<^esub> ff'\<rparr> =
        cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>gg'\<rparr> \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> 
        cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>ff'\<rparr>"
      if gg': "gg' : bb' \<mapsto>\<^bsub>op_cat \<BB>' \<times>\<^sub>C \<CC>'\<^esub> cc'" 
        and ff': "ff' : aa' \<mapsto>\<^bsub>op_cat \<BB>' \<times>\<^sub>C \<CC>'\<^esub> bb'"
      for bb' cc' gg' aa' ff'
    proof-
      obtain g g' b b' c c' 
        where gg'_def: "gg' = [g, g']\<^sub>\<circ>"
          and bb'_def: "bb' = [b, b']\<^sub>\<circ>"
          and cc'_def: "cc' = [c, c']\<^sub>\<circ>"   
          and g: "g : b \<mapsto>\<^bsub>op_cat \<BB>'\<^esub> c"  
          and g': "g' : b' \<mapsto>\<^bsub>\<CC>'\<^esub> c'"
        by 
          (
            elim cat_prod_2_is_arrE[
              OF \<FF>.HomDom.category_op \<GG>.HomDom.category_axioms gg'
              ]
          )
      moreover obtain f f' a a' b'' b''' 
        where ff'_def: "ff' = [f, f']\<^sub>\<circ>"
          and aa'_def: "aa' = [a, a']\<^sub>\<circ>"
          and "bb' = [b'', b''']\<^sub>\<circ>"   
          and f: "f : a \<mapsto>\<^bsub>op_cat \<BB>'\<^esub> b''"  
          and "f' : a' \<mapsto>\<^bsub>\<CC>'\<^esub> b'''"
        by 
          (
            elim cat_prod_2_is_arrE[
              OF \<FF>.HomDom.category_op \<GG>.HomDom.category_axioms ff'
              ]
          )
      ultimately have f: "f : a \<mapsto>\<^bsub>op_cat \<BB>'\<^esub> b" and f': "f' : a' \<mapsto>\<^bsub>\<CC>'\<^esub> b'" 
        by auto
      from assms f f' g g' have [cat_cs_simps]:
        "[
          \<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>, 
          \<GG>\<lparr>ArrMap\<rparr>\<lparr>g'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>
         ]\<^sub>\<circ> = 
          [\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>, \<GG>\<lparr>ArrMap\<rparr>\<lparr>g'\<rparr>]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>op_cat \<BB> \<times>\<^sub>C \<CC>\<^esub> 
          [\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>, \<GG>\<lparr>ArrMap\<rparr>\<lparr>f'\<rparr>]\<^sub>\<circ>"
        unfolding cat_op_simps
        by 
          (
            cs_concl 
              cs_simp: cat_prod_cs_simps cat_cs_simps cat_op_simps 
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
      from assms f f' g g' show ?thesis
        unfolding gg'_def ff'_def aa'_def bb'_def cc'_def cat_op_simps
        by
          (
            cs_concl
              cs_simp: cat_prod_cs_simps cat_cs_simps cat_op_simps 
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
    qed
    show 
      "cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ArrMap\<rparr>\<lparr>(op_cat \<BB>' \<times>\<^sub>C \<CC>')\<lparr>CId\<rparr>\<lparr>cc'\<rparr>\<rparr> = 
        \<DD>\<lparr>CId\<rparr>\<lparr>cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<lparr>ObjMap\<rparr>\<lparr>cc'\<rparr>\<rparr>"
      if "cc' \<in>\<^sub>\<circ> (op_cat \<BB>' \<times>\<^sub>C \<CC>')\<lparr>Obj\<rparr>" for cc'
    proof-
      from that obtain c c' 
        where cc'_def: "cc' = [c, c']\<^sub>\<circ>" 
          and c: "c \<in>\<^sub>\<circ> op_cat \<BB>'\<lparr>Obj\<rparr>"
          and c': "c' \<in>\<^sub>\<circ> \<CC>'\<lparr>Obj\<rparr>"
        by (elim cat_prod_2_ObjE[rotated 2]) 
          (auto intro: cat_cs_intros)
      from assms c c' have [cat_cs_simps]: 
        "[\<BB>\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>\<rparr>, \<CC>\<lparr>CId\<rparr>\<lparr>\<GG>\<lparr>ObjMap\<rparr>\<lparr>c'\<rparr>\<rparr>]\<^sub>\<circ> =
          (op_cat \<BB> \<times>\<^sub>C \<CC>)\<lparr>CId\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>c\<rparr>, \<GG>\<lparr>ObjMap\<rparr>\<lparr>c'\<rparr>\<rparr>\<^sub>\<bullet>"
        unfolding cat_op_simps
        by 
          (
            cs_concl
              cs_simp: cat_prod_cs_simps cat_op_simps 
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
      from assms c c' show ?thesis
        unfolding cc'_def cat_op_simps
        by (*slow*)
          (
            cs_concl 
              cs_simp: cat_prod_cs_simps cat_cs_simps cat_op_simps 
              cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
          )
    qed
  qed (auto simp: cf_cn_cov_bcomp_components cat_cs_simps intro: cat_cs_intros)

qed

lemma cf_cn_cov_bcomp_is_functor'[cat_cs_intros]:
  assumes "\<FF> : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<SS> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<AA>' = op_cat \<BB>' \<times>\<^sub>C \<CC>'"
  shows "cf_cn_cov_bcomp \<SS> \<FF> \<GG> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms(1-3) unfolding assms(4) by (rule cf_cn_cov_bcomp_is_functor)


subsubsection\<open>Projection of a contracovariant bifunctor and functors\<close>

lemma cf_cn_cov_bcomp_bifunctor_proj_snd[cat_cs_simps]:
  assumes "\<FF> : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<GG> : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<SS> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "b \<in>\<^sub>\<circ> \<BB>'\<lparr>Obj\<rparr>"
  shows
    "cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<^bsub>op_cat \<BB>',\<CC>'\<^esub>(b,-)\<^sub>C\<^sub>F =
      (\<SS>\<^bsub>op_cat \<BB>,\<CC>\<^esub>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-)\<^sub>C\<^sub>F) \<circ>\<^sub>C\<^sub>F \<GG>"
proof(rule cf_eqI)
  from assms show [intro]: 
    "cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<^bsub>op_cat \<BB>',\<CC>'\<^esub>(b,-)\<^sub>C\<^sub>F : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    "(\<SS>\<^bsub>op_cat \<BB>,\<CC>\<^esub>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-)\<^sub>C\<^sub>F) \<circ>\<^sub>C\<^sub>F \<GG> : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    by (cs_concl cs_intro: cat_cs_intros cat_op_intros)+
  from assms have ObjMap_dom_lhs:
    "\<D>\<^sub>\<circ> ((cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<^bsub>op_cat \<BB>',\<CC>'\<^esub>(b,-)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>) = \<CC>'\<lparr>Obj\<rparr>"
    and ObjMap_dom_rhs:
    "\<D>\<^sub>\<circ> (((\<SS>\<^bsub>op_cat \<BB>,\<CC>\<^esub>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-)\<^sub>C\<^sub>F) \<circ>\<^sub>C\<^sub>F \<GG>)\<lparr>ObjMap\<rparr>) = \<CC>'\<lparr>Obj\<rparr>"
    and ArrMap_dom_lhs:
    "\<D>\<^sub>\<circ> ((cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<^bsub>op_cat \<BB>',\<CC>'\<^esub>(b,-)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>) = \<CC>'\<lparr>Arr\<rparr>"
    and ArrMap_dom_rhs:
    "\<D>\<^sub>\<circ> (((\<SS>\<^bsub>op_cat \<BB>,\<CC>\<^esub>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-)\<^sub>C\<^sub>F) \<circ>\<^sub>C\<^sub>F \<GG>)\<lparr>ArrMap\<rparr>) = \<CC>'\<lparr>Arr\<rparr>"
    by (cs_concl cs_intro: cat_cs_intros cat_op_intros cs_simp: cat_cs_simps)+
  show 
    "(cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<^bsub>op_cat \<BB>',\<CC>'\<^esub>(b,-)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr> =
      ((\<SS>\<^bsub>op_cat \<BB>,\<CC>\<^esub>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-)\<^sub>C\<^sub>F) \<circ>\<^sub>C\<^sub>F \<GG>)\<lparr>ObjMap\<rparr>"
  proof(rule vsv_eqI, unfold ObjMap_dom_lhs ObjMap_dom_rhs)
    fix a assume "a \<in>\<^sub>\<circ> \<CC>'\<lparr>Obj\<rparr>"
    with assms show 
      "(cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<^bsub>op_cat \<BB>',\<CC>'\<^esub>(b,-)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> =
        ((\<SS>\<^bsub>op_cat \<BB>,\<CC>\<^esub>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-)\<^sub>C\<^sub>F) \<circ>\<^sub>C\<^sub>F \<GG>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      by 
        (
          cs_concl 
            cs_simp: cat_prod_cs_simps cat_cs_simps 
            cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
        )
  qed (auto intro: is_functor.cf_ObjMap_vsv) 
  show 
    "(cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<^bsub>op_cat \<BB>',\<CC>'\<^esub>(b,-)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr> =
      ((\<SS>\<^bsub>op_cat \<BB>,\<CC>\<^esub>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-)\<^sub>C\<^sub>F) \<circ>\<^sub>C\<^sub>F \<GG>)\<lparr>ArrMap\<rparr>"
  proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
    fix f assume "f \<in>\<^sub>\<circ> \<CC>'\<lparr>Arr\<rparr>"
    then obtain a' b' where "f : a' \<mapsto>\<^bsub>\<CC>'\<^esub> b'" by (auto intro: is_arrI)
    with assms show 
      "(cf_cn_cov_bcomp \<SS> \<FF> \<GG>\<^bsub>op_cat \<BB>',\<CC>'\<^esub>(b,-)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
        ((\<SS>\<^bsub>op_cat \<BB>,\<CC>\<^esub>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-)\<^sub>C\<^sub>F) \<circ>\<^sub>C\<^sub>F \<GG>)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      by 
        (
          cs_concl
            cs_simp: cat_cs_simps cat_op_simps 
            cs_intro: cat_cs_intros cat_op_intros cat_prod_cs_intros
        )
  qed (auto intro: is_functor.cf_ArrMap_vsv) 
qed simp_all



subsection\<open>Composition of a covariant bifunctor and a covariant functor\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition cf_lcomp :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_lcomp \<CC> \<SS> \<FF> = cf_bcomp \<SS> \<FF> (cf_id \<CC>)"

definition cf_rcomp :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_rcomp \<BB> \<SS> \<GG> = cf_bcomp \<SS> (cf_id \<BB>) \<GG>"


text\<open>Components.\<close>

lemma cf_lcomp_components:
  shows "cf_lcomp \<CC> \<SS> \<FF>\<lparr>HomDom\<rparr> = \<FF>\<lparr>HomDom\<rparr> \<times>\<^sub>C \<CC>"
    and "cf_lcomp \<CC> \<SS> \<FF>\<lparr>HomCod\<rparr> = \<SS>\<lparr>HomCod\<rparr>"
  unfolding cf_lcomp_def cf_bcomp_components dghm_id_components by simp_all

lemma cf_rcomp_components:
  shows "cf_rcomp \<BB> \<SS> \<GG>\<lparr>HomDom\<rparr> = \<BB> \<times>\<^sub>C \<GG>\<lparr>HomDom\<rparr>"
    and "cf_rcomp \<BB> \<SS> \<GG>\<lparr>HomCod\<rparr> = \<SS>\<lparr>HomCod\<rparr>"
  unfolding cf_rcomp_def cf_bcomp_components dghm_id_components by simp_all


subsubsection\<open>Object map\<close>

lemma cf_lcomp_ObjMap_vsv: "vsv (cf_lcomp \<CC> \<SS> \<FF>\<lparr>ObjMap\<rparr>)"
  unfolding cf_lcomp_def by (rule cf_bcomp_ObjMap_vsv)

lemma cf_rcomp_ObjMap_vsv: "vsv (cf_rcomp \<CC> \<SS> \<FF>\<lparr>ObjMap\<rparr>)"
  unfolding cf_rcomp_def by (rule cf_bcomp_ObjMap_vsv)

lemma cf_lcomp_ObjMap_vdomain[cat_cs_simps]:
  assumes "category \<alpha> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> (cf_lcomp \<CC> \<SS> \<FF>\<lparr>ObjMap\<rparr>) = (\<AA> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
  using assms 
  unfolding cf_lcomp_def 
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

lemma cf_rcomp_ObjMap_vdomain[cat_cs_simps]:
  assumes "category \<alpha> \<BB>" and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (cf_rcomp \<BB> \<SS> \<GG>\<lparr>ObjMap\<rparr>) = (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>"
  using assms 
  unfolding cf_rcomp_def 
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

lemma cf_lcomp_ObjMap_app[cat_cs_simps]:
  assumes "category \<alpha> \<CC>" 
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "cf_lcomp \<CC> \<SS> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a, c\<rparr>\<^sub>\<bullet> = \<SS>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>, c\<rparr>\<^sub>\<bullet>"
  using assms 
  unfolding cf_lcomp_def 
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros)

lemma cf_rcomp_ObjMap_app[cat_cs_simps]:
  assumes "category \<alpha> \<BB>" 
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "cf_rcomp \<BB> \<SS> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b, a\<rparr>\<^sub>\<bullet> = \<SS>\<lparr>ObjMap\<rparr>\<lparr>b, \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>\<^sub>\<bullet>"
  using assms 
  unfolding cf_rcomp_def
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros)

lemma cf_lcomp_ObjMap_vrange:
  assumes "category \<alpha> \<CC>" 
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<SS> : \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "\<R>\<^sub>\<circ> (cf_lcomp \<CC> \<SS> \<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
  using assms
  unfolding cf_lcomp_def 
  by (intro cf_bcomp_ObjMap_vrange) (cs_concl cs_intro: cat_cs_intros)+

lemma cf_rcomp_ObjMap_vrange:
  assumes "category \<alpha> \<BB>" 
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<SS> : \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "\<R>\<^sub>\<circ> (cf_rcomp \<BB> \<SS> \<GG>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
  using assms
  unfolding cf_rcomp_def 
  by (intro cf_bcomp_ObjMap_vrange) (cs_concl cs_intro: cat_cs_intros)+


subsubsection\<open>Arrow map\<close>

lemma cf_lcomp_ArrMap_vsv: "vsv (cf_lcomp \<CC> \<SS> \<FF>\<lparr>ArrMap\<rparr>)"
  unfolding cf_lcomp_def by (rule cf_bcomp_ArrMap_vsv)

lemma cf_rcomp_ArrMap_vsv: "vsv (cf_rcomp \<BB> \<SS> \<GG>\<lparr>ArrMap\<rparr>)"
  unfolding cf_rcomp_def by (rule cf_bcomp_ArrMap_vsv)

lemma cf_lcomp_ArrMap_vdomain[cat_cs_simps]:
  assumes "category \<alpha> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> (cf_lcomp \<CC> \<SS> \<FF>\<lparr>ArrMap\<rparr>) = (\<AA> \<times>\<^sub>C \<CC>)\<lparr>Arr\<rparr>"
  using assms 
  unfolding cf_lcomp_def 
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

lemma cf_rcomp_ArrMap_vdomain[cat_cs_simps]:
  assumes "category \<alpha> \<BB>" and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (cf_rcomp \<BB> \<SS> \<GG>\<lparr>ArrMap\<rparr>) = (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Arr\<rparr>"
  using assms 
  unfolding cf_rcomp_def 
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

lemma cf_lcomp_ArrMap_app[cat_cs_simps]:
  assumes "category \<alpha> \<CC>" 
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "f \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" 
    and "g \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  shows "cf_lcomp \<CC> \<SS> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f, g\<rparr>\<^sub>\<bullet> = \<SS>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>, g\<rparr>\<^sub>\<bullet>"
  using assms 
  unfolding cf_lcomp_def
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros)

lemma cf_rcomp_ArrMap_app[cat_cs_simps]:
  assumes "category \<alpha> \<BB>" 
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" 
    and "g \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
  shows "cf_rcomp \<BB> \<SS> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f, g\<rparr>\<^sub>\<bullet> = \<SS>\<lparr>ArrMap\<rparr>\<lparr>f, \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>\<rparr>\<^sub>\<bullet>"
  using assms 
  unfolding cf_rcomp_def
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros)

lemma cf_lcomp_ArrMap_vrange:
  assumes "category \<alpha> \<CC>" 
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<SS> : \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "\<R>\<^sub>\<circ> (cf_lcomp \<CC> \<SS> \<FF>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Arr\<rparr>"
  using assms
  unfolding cf_lcomp_def
  by (intro cf_bcomp_ArrMap_vrange) (cs_concl cs_intro: cat_cs_intros)+

lemma cf_rcomp_ArrMap_vrange:
  assumes "category \<alpha> \<BB>" 
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<SS> : \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "\<R>\<^sub>\<circ> (cf_rcomp \<BB> \<SS> \<GG>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Arr\<rparr>"
  using assms
  unfolding cf_rcomp_def
  by (intro cf_bcomp_ArrMap_vrange) (cs_concl cs_intro: cat_cs_intros)+


subsubsection\<open>
Composition of a covariant bifunctor and a covariant functor is a functor
\<close>

lemma cf_lcomp_is_functor:
  assumes "category \<alpha> \<CC>" 
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<SS> : \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "cf_lcomp \<CC> \<SS> \<FF> : \<AA> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms
  unfolding cf_lcomp_def
  by (cs_concl cs_intro: cat_cs_intros)+

lemma cf_lcomp_is_functor'[cat_cs_intros]:
  assumes "category \<alpha> \<CC>" 
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<SS> : \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<AA>' = \<AA> \<times>\<^sub>C \<CC>"
  shows "cf_lcomp \<CC> \<SS> \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms(1-3) unfolding assms(4) by (rule cf_lcomp_is_functor)

lemma cf_rcomp_is_functor:
  assumes "category \<alpha> \<BB>" 
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<SS> : \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "cf_rcomp \<BB> \<SS> \<GG> : \<BB> \<times>\<^sub>C \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms 
  unfolding cf_rcomp_def 
  by (cs_concl cs_intro: cat_cs_intros)+

lemma cf_rcomp_is_functor'[cat_cs_intros]:
  assumes "category \<alpha> \<BB>" 
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<SS> : \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<AA>' = \<BB> \<times>\<^sub>C \<AA>"
  shows "cf_rcomp \<BB> \<SS> \<GG> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms(1-3) unfolding assms(4) by (rule cf_rcomp_is_functor)



subsection\<open>Composition of a contracovariant bifunctor and a covariant functor\<close>

definition cf_cn_cov_lcomp :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_cn_cov_lcomp \<CC> \<SS> \<FF> = cf_cn_cov_bcomp \<SS> \<FF> (cf_id \<CC>)"

definition cf_cn_cov_rcomp :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cf_cn_cov_rcomp \<BB> \<SS> \<GG> = cf_cn_cov_bcomp \<SS> (cf_id \<BB>) \<GG>"


text\<open>Components.\<close>

lemma cf_cn_cov_lcomp_components:
  shows "cf_cn_cov_lcomp \<CC> \<SS> \<FF>\<lparr>HomDom\<rparr> = op_cat (\<FF>\<lparr>HomDom\<rparr>) \<times>\<^sub>C \<CC>"
    and "cf_cn_cov_lcomp \<CC> \<SS> \<FF>\<lparr>HomCod\<rparr> = \<SS>\<lparr>HomCod\<rparr>"
  unfolding cf_cn_cov_lcomp_def cf_cn_cov_bcomp_components dghm_id_components 
  by simp_all

lemma cf_cn_cov_rcomp_components:
  shows "cf_cn_cov_rcomp \<BB> \<SS> \<GG>\<lparr>HomDom\<rparr> = op_cat \<BB> \<times>\<^sub>C \<GG>\<lparr>HomDom\<rparr>"
    and "cf_cn_cov_rcomp \<BB> \<SS> \<GG>\<lparr>HomCod\<rparr> = \<SS>\<lparr>HomCod\<rparr>"
  unfolding cf_cn_cov_rcomp_def cf_cn_cov_bcomp_components dghm_id_components 
  by simp_all


subsubsection\<open>Object map\<close>

lemma cf_cn_cov_lcomp_ObjMap_vsv: "vsv (cf_cn_cov_lcomp \<CC> \<SS> \<FF>\<lparr>ObjMap\<rparr>)"
  unfolding cf_cn_cov_lcomp_def by (rule cf_cn_cov_bcomp_ObjMap_vsv)

lemma cf_cn_cov_rcomp_ObjMap_vsv: "vsv (cf_cn_cov_rcomp \<CC> \<SS> \<FF>\<lparr>ObjMap\<rparr>)"
  unfolding cf_cn_cov_rcomp_def by (rule cf_cn_cov_bcomp_ObjMap_vsv)

lemma cf_cn_cov_lcomp_ObjMap_vdomain[cat_cs_simps]:
  assumes "category \<alpha> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> (cf_cn_cov_lcomp \<CC> \<SS> \<FF>\<lparr>ObjMap\<rparr>) = (op_cat \<AA> \<times>\<^sub>C \<CC>)\<lparr>Obj\<rparr>"
  using assms 
  unfolding cf_cn_cov_lcomp_def 
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

lemma cf_cn_cov_rcomp_ObjMap_vdomain[cat_cs_simps]:
  assumes "category \<alpha> \<BB>" and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (cf_cn_cov_rcomp \<BB> \<SS> \<GG>\<lparr>ObjMap\<rparr>) = (op_cat \<BB> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>"
  using assms 
  unfolding cf_cn_cov_rcomp_def 
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

lemma cf_cn_cov_lcomp_ObjMap_app[cat_cs_simps]:
  assumes "category \<alpha> \<CC>" 
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "a \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Obj\<rparr>" 
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "cf_cn_cov_lcomp \<CC> \<SS> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a, c\<rparr>\<^sub>\<bullet> = \<SS>\<lparr>ObjMap\<rparr>\<lparr>\<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>, c\<rparr>\<^sub>\<bullet>"
  using assms 
  unfolding cf_cn_cov_lcomp_def cat_op_simps
  by
    (
      cs_concl
        cs_simp: cat_cs_simps cat_op_simps 
        cs_intro: cat_cs_intros cat_prod_cs_intros
    )

lemma cf_cn_cov_rcomp_ObjMap_app[cat_cs_simps]:
  assumes "category \<alpha> \<BB>" 
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "b \<in>\<^sub>\<circ> op_cat \<BB>\<lparr>Obj\<rparr>" 
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "cf_cn_cov_rcomp \<BB> \<SS> \<GG>\<lparr>ObjMap\<rparr>\<lparr>b, a\<rparr>\<^sub>\<bullet> = \<SS>\<lparr>ObjMap\<rparr>\<lparr>b, \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<rparr>\<^sub>\<bullet>"
  using assms 
  unfolding cf_cn_cov_rcomp_def cat_op_simps
  by
    (
      cs_concl
        cs_simp: cat_cs_simps cat_op_simps 
        cs_intro: cat_cs_intros cat_prod_cs_intros
    )

lemma cf_cn_cov_lcomp_ObjMap_vrange:
  assumes "category \<alpha> \<CC>" 
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<SS> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "\<R>\<^sub>\<circ> (cf_cn_cov_lcomp \<CC> \<SS> \<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
  using assms
  unfolding cf_cn_cov_lcomp_def 
  by (intro cf_cn_cov_bcomp_ObjMap_vrange) 
    (cs_concl cs_intro: cat_cs_intros)+

lemma cf_cn_cov_rcomp_ObjMap_vrange:
  assumes "category \<alpha> \<BB>" 
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<SS> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "\<R>\<^sub>\<circ> (cf_cn_cov_rcomp \<BB> \<SS> \<GG>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
  using assms
  unfolding cf_cn_cov_rcomp_def 
  by (intro cf_cn_cov_bcomp_ObjMap_vrange) 
    (cs_concl cs_intro: cat_cs_intros)+


subsubsection\<open>Arrow map\<close>

lemma cf_cn_cov_lcomp_ArrMap_vsv: "vsv (cf_cn_cov_lcomp \<CC> \<SS> \<FF>\<lparr>ArrMap\<rparr>)"
  unfolding cf_cn_cov_lcomp_def by (rule cf_cn_cov_bcomp_ArrMap_vsv)

lemma cf_cn_cov_rcomp_ArrMap_vsv: "vsv (cf_cn_cov_rcomp \<BB> \<SS> \<GG>\<lparr>ArrMap\<rparr>)"
  unfolding cf_cn_cov_rcomp_def by (rule cf_cn_cov_bcomp_ArrMap_vsv)

lemma cf_cn_cov_lcomp_ArrMap_vdomain[cat_cs_simps]:
  assumes "category \<alpha> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<D>\<^sub>\<circ> (cf_cn_cov_lcomp \<CC> \<SS> \<FF>\<lparr>ArrMap\<rparr>) = (op_cat \<AA> \<times>\<^sub>C \<CC>)\<lparr>Arr\<rparr>"
  using assms 
  unfolding cf_cn_cov_lcomp_def 
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

lemma cf_cn_cov_rcomp_ArrMap_vdomain[cat_cs_simps]:
  assumes "category \<alpha> \<BB>" and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (cf_cn_cov_rcomp \<BB> \<SS> \<GG>\<lparr>ArrMap\<rparr>) = (op_cat \<BB> \<times>\<^sub>C \<AA>)\<lparr>Arr\<rparr>"
  using assms 
  unfolding cf_cn_cov_rcomp_def 
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

lemma cf_cn_cov_lcomp_ArrMap_app[cat_cs_simps]:
  assumes "category \<alpha> \<CC>" 
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "f \<in>\<^sub>\<circ> op_cat \<AA>\<lparr>Arr\<rparr>" 
    and "g \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  shows "cf_cn_cov_lcomp \<CC> \<SS> \<FF>\<lparr>ArrMap\<rparr>\<lparr>f, g\<rparr>\<^sub>\<bullet> = \<SS>\<lparr>ArrMap\<rparr>\<lparr>\<FF>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>, g\<rparr>\<^sub>\<bullet>"
  using assms 
  unfolding cf_cn_cov_lcomp_def cat_op_simps
  by 
    (
      cs_concl 
        cs_simp: cat_cs_simps cat_op_simps 
        cs_intro: cat_cs_intros cat_prod_cs_intros
    )

lemma cf_cn_cov_rcomp_ArrMap_app[cat_cs_simps]:
  assumes "category \<alpha> \<BB>" 
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "f \<in>\<^sub>\<circ> op_cat \<BB>\<lparr>Arr\<rparr>" 
    and "g \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
  shows "cf_cn_cov_rcomp \<BB> \<SS> \<GG>\<lparr>ArrMap\<rparr>\<lparr>f, g\<rparr>\<^sub>\<bullet> = \<SS>\<lparr>ArrMap\<rparr>\<lparr>f, \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>\<rparr>\<^sub>\<bullet>"
  using assms 
  unfolding cf_cn_cov_rcomp_def cat_op_simps
  by 
    (
      cs_concl 
        cs_simp: cat_cs_simps cat_op_simps
        cs_intro: cat_cs_intros cat_prod_cs_intros
    )

lemma cf_cn_cov_lcomp_ArrMap_vrange:
  assumes "category \<alpha> \<CC>" 
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<SS> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "\<R>\<^sub>\<circ> (cf_cn_cov_lcomp \<CC> \<SS> \<FF>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Arr\<rparr>"
  using assms
  unfolding cf_cn_cov_lcomp_def
  by (intro cf_cn_cov_bcomp_ArrMap_vrange) 
    (cs_concl cs_intro: cat_cs_intros)+

lemma cf_cn_cov_rcomp_ArrMap_vrange:
  assumes "category \<alpha> \<BB>" 
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<SS> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "\<R>\<^sub>\<circ> (cf_cn_cov_rcomp \<BB> \<SS> \<GG>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<DD>\<lparr>Arr\<rparr>"
  using assms
  unfolding cf_cn_cov_rcomp_def cat_op_simps
  by (intro cf_cn_cov_bcomp_ArrMap_vrange) 
    (cs_concl cs_intro: cat_cs_intros)+


subsubsection\<open>
Composition of a contracovariant bifunctor and a covariant functor is a functor
\<close>

lemma cf_cn_cov_lcomp_is_functor:
  assumes "category \<alpha> \<CC>" 
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<SS> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "cf_cn_cov_lcomp \<CC> \<SS> \<FF> : op_cat \<AA> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms
  unfolding cf_cn_cov_lcomp_def cat_op_simps
  by (cs_concl cs_intro: cat_cs_intros)+

lemma cf_cn_cov_lcomp_is_functor'[cat_cs_intros]:
  assumes "category \<alpha> \<CC>" 
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<SS> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<AA>\<CC> = op_cat \<AA> \<times>\<^sub>C \<CC>"
  shows "cf_cn_cov_lcomp \<CC> \<SS> \<FF> : \<AA>\<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms(1-3) unfolding assms(4) by (rule cf_cn_cov_lcomp_is_functor)

lemma cf_cn_cov_rcomp_is_functor:
  assumes "category \<alpha> \<BB>" 
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<SS> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  shows "cf_cn_cov_rcomp \<BB> \<SS> \<GG> : op_cat \<BB> \<times>\<^sub>C \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms
  unfolding cf_cn_cov_rcomp_def cat_op_simps
  by (cs_concl cs_intro: cat_cs_intros)+

lemma cf_cn_cov_rcomp_is_functor'[cat_cs_intros]:
  assumes "category \<alpha> \<BB>" 
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<SS> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "\<BB>\<AA> = op_cat \<BB> \<times>\<^sub>C \<AA>"
  shows "cf_cn_cov_rcomp \<BB> \<SS> \<GG> : \<BB>\<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms(1-3) unfolding assms(4) by (rule cf_cn_cov_rcomp_is_functor)


subsubsection\<open>
Projection of a composition of a contracovariant bifunctor and a covariant 
functor
\<close>

lemma cf_cn_cov_rcomp_bifunctor_proj_snd[cat_cs_simps]:
  assumes "category \<alpha> \<BB>" 
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<SS> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows
    "cf_cn_cov_rcomp \<BB> \<SS> \<GG>\<^bsub>op_cat \<BB>,\<AA>\<^esub>(b,-)\<^sub>C\<^sub>F =
      (\<SS>\<^bsub>op_cat \<BB>,\<CC>\<^esub>(b,-)\<^sub>C\<^sub>F) \<circ>\<^sub>C\<^sub>F \<GG>"
  using assms 
  unfolding cf_cn_cov_rcomp_def
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

lemma cf_cn_cov_lcomp_bifunctor_proj_snd[cat_cs_simps]:
  assumes "category \<alpha> \<CC>" 
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<SS> : op_cat \<BB> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    and "b \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows
    "cf_cn_cov_lcomp \<CC> \<SS> \<FF>\<^bsub>op_cat \<AA>,\<CC>\<^esub>(b,-)\<^sub>C\<^sub>F =
      (\<SS>\<^bsub>op_cat \<BB>,\<CC>\<^esub>(\<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>,-)\<^sub>C\<^sub>F)"
  using assms 
  unfolding cf_cn_cov_lcomp_def
  by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_op_intros)



subsection\<open>Composition of bifunctors\<close>


subsubsection\<open>Definitions and elementary properties\<close>

definition cf_blcomp :: "V \<Rightarrow> V"
  where "cf_blcomp \<SS> = 
    cf_lcomp (\<SS>\<lparr>HomCod\<rparr>) \<SS> \<SS> \<circ>\<^sub>C\<^sub>F  
    cf_cat_prod_21_of_3 (\<SS>\<lparr>HomCod\<rparr>) (\<SS>\<lparr>HomCod\<rparr>) (\<SS>\<lparr>HomCod\<rparr>)"

definition cf_brcomp :: "V \<Rightarrow> V"
  where "cf_brcomp \<SS> = 
    cf_rcomp (\<SS>\<lparr>HomCod\<rparr>) \<SS> \<SS> \<circ>\<^sub>C\<^sub>F
    cf_cat_prod_12_of_3 (\<SS>\<lparr>HomCod\<rparr>) (\<SS>\<lparr>HomCod\<rparr>) (\<SS>\<lparr>HomCod\<rparr>)"


text\<open>Alternative forms of the definitions.\<close>

lemma cf_blcomp_def':
  assumes "\<SS> : \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "cf_blcomp \<SS> = cf_lcomp \<CC> \<SS> \<SS> \<circ>\<^sub>C\<^sub>F cf_cat_prod_21_of_3 \<CC> \<CC> \<CC>"
proof-
  interpret \<SS>: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C \<CC>\<close> \<CC> \<SS> by (rule assms)
  show ?thesis
    by (cs_concl cs_simp: cat_cs_simps cf_blcomp_def cs_intro: cat_cs_intros)
qed

lemma cf_brcomp_def':
  assumes "\<SS> : \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "cf_brcomp \<SS> = cf_rcomp \<CC> \<SS> \<SS> \<circ>\<^sub>C\<^sub>F cf_cat_prod_12_of_3 \<CC> \<CC> \<CC>"
proof-
  interpret \<SS>: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C \<CC>\<close> \<CC> \<SS> by (rule assms)
  show ?thesis
    by (cs_concl cs_simp: cat_cs_simps cf_brcomp_def cs_intro: cat_cs_intros)
qed


subsubsection\<open>Compositions of bifunctors are functors\<close>

lemma cf_blcomp_is_functor:
  assumes "\<SS> : \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "cf_blcomp \<SS> : \<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<SS>: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C \<CC>\<close> \<CC> \<SS> by (rule assms)
  show ?thesis
    by (cs_concl cs_simp: cat_cs_simps cf_blcomp_def' cs_intro: cat_cs_intros)
qed

lemma cf_blcomp_is_functor'[cat_cs_intros]:
  assumes "\<SS> : \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<AA>' = \<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC>"
  shows "cf_blcomp \<SS> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1) unfolding assms(2) by (rule cf_blcomp_is_functor)

lemma cf_brcomp_is_functor:
  assumes "\<SS> : \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "cf_brcomp \<SS> : \<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<SS>: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C \<CC>\<close> \<CC> \<SS> by (rule assms)
  show ?thesis
    by (cs_concl cs_simp: cat_cs_simps cf_brcomp_def' cs_intro: cat_cs_intros)
qed

lemma cf_brcomp_is_functor'[cat_cs_intros]:
  assumes "\<SS> : \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<AA>' = \<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC>"
  shows "cf_brcomp \<SS> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1) unfolding assms(2) by (rule cf_brcomp_is_functor)


subsubsection\<open>Object map\<close>

lemma cf_blcomp_ObjMap_vsv[cat_cs_intros]: 
  assumes "\<SS> : \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "vsv (cf_blcomp \<SS>\<lparr>ObjMap\<rparr>)"
proof-
  interpret cf_blcomp: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC>\<close> \<CC> \<open>cf_blcomp \<SS>\<close>
    by (rule cf_blcomp_is_functor[OF assms])
  show ?thesis by auto
qed

lemma cf_brcomp_ObjMap_vsv[cat_cs_intros]: 
  assumes "\<SS> : \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "vsv (cf_brcomp \<SS>\<lparr>ObjMap\<rparr>)"
proof-
  interpret cf_brcomp: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC>\<close> \<CC> \<open>cf_brcomp \<SS>\<close>
    by (rule cf_brcomp_is_functor[OF assms])
  show ?thesis by auto
qed
 
lemma cf_blcomp_ObjMap_vdomain[cat_cs_simps]: 
  assumes "\<SS> : \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (cf_blcomp \<SS>\<lparr>ObjMap\<rparr>) = (\<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Obj\<rparr>"
proof-
  interpret \<SS>: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C \<CC>\<close> \<CC> \<SS> by (rule assms)
  interpret cf_blcomp: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC>\<close> \<CC> \<open>cf_blcomp \<SS>\<close>
    by (rule cf_blcomp_is_functor[OF assms])
  show ?thesis by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed

lemma cf_brcomp_ObjMap_vdomain[cat_cs_simps]: 
  assumes "\<SS> : \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (cf_brcomp \<SS>\<lparr>ObjMap\<rparr>) = (\<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Obj\<rparr>"
proof-
  interpret \<SS>: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C \<CC>\<close> \<CC> \<SS> by (rule assms)
  interpret cf_brcomp: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC>\<close> \<CC> \<open>cf_brcomp \<SS>\<close>
    by (rule cf_brcomp_is_functor[OF assms])
  show ?thesis by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed

lemma cf_blcomp_ObjMap_app[cat_cs_simps]: 
  assumes "\<SS> : \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "A = [a, b, c]\<^sub>\<circ>"
    and "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "cf_blcomp \<SS>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> = (a \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>O\<^bsub>\<SS>\<^esub> b) \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>O\<^bsub>\<SS>\<^esub> c"
proof-
  interpret \<SS>: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C \<CC>\<close> \<CC> \<SS> by (rule assms)
  interpret cf_blcomp: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC>\<close> \<CC> \<open>cf_blcomp \<SS>\<close>
    by (rule cf_blcomp_is_functor[OF assms(1)])
  from assms(3-5) show ?thesis
    unfolding assms(2)
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps cat_prod_cs_simps cf_blcomp_def' 
          cs_intro: cat_cs_intros cat_prod_cs_intros
      )
qed

lemma cf_brcomp_ObjMap_app[cat_cs_simps]: 
  assumes "\<SS> : \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "A = [a, b, c]\<^sub>\<circ>"
    and "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "cf_brcomp \<SS>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> = a \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>O\<^bsub>\<SS>\<^esub> (b \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>O\<^bsub>\<SS>\<^esub> c)"
proof-
  interpret \<SS>: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C \<CC>\<close> \<CC> \<SS> by (rule assms)
  interpret cf_brcomp: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC>\<close> \<CC> \<open>cf_brcomp \<SS>\<close>
    by (rule cf_brcomp_is_functor[OF assms(1)])
  from assms(3-5) show ?thesis
    unfolding assms(2)
    by
      (
        cs_concl
          cs_simp: cat_cs_simps cat_prod_cs_simps cf_brcomp_def'
          cs_intro: cat_cs_intros cat_prod_cs_intros
      )
qed


subsubsection\<open>Arrow map\<close>

lemma cf_blcomp_ArrMap_vsv[cat_cs_intros]: 
  assumes "\<SS> : \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "vsv (cf_blcomp \<SS>\<lparr>ArrMap\<rparr>)"
proof-
  interpret cf_blcomp: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC>\<close> \<CC> \<open>cf_blcomp \<SS>\<close>
    by (rule cf_blcomp_is_functor[OF assms])
  show ?thesis by auto
qed

lemma cf_brcomp_ArrMap_vsv[cat_cs_intros]: 
  assumes "\<SS> : \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "vsv (cf_brcomp \<SS>\<lparr>ArrMap\<rparr>)"
proof-
  interpret cf_brcomp: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC>\<close> \<CC> \<open>cf_brcomp \<SS>\<close>
    by (rule cf_brcomp_is_functor[OF assms])
  show ?thesis by auto
qed
 
lemma cf_blcomp_ArrMap_vdomain[cat_cs_simps]: 
  assumes "\<SS> : \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (cf_blcomp \<SS>\<lparr>ArrMap\<rparr>) = (\<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Arr\<rparr>"
proof-
  interpret \<SS>: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C \<CC>\<close> \<CC> \<SS> by (rule assms)
  interpret cf_blcomp: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC>\<close> \<CC> \<open>cf_blcomp \<SS>\<close>
    by (rule cf_blcomp_is_functor[OF assms])
  show ?thesis by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed

lemma cf_brcomp_ArrMap_vdomain[cat_cs_simps]: 
  assumes "\<SS> : \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (cf_brcomp \<SS>\<lparr>ArrMap\<rparr>) = (\<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC>)\<lparr>Arr\<rparr>"
proof-
  interpret \<SS>: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C \<CC>\<close> \<CC> \<SS> by (rule assms)
  interpret cf_brcomp: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC>\<close> \<CC> \<open>cf_brcomp \<SS>\<close>
    by (rule cf_brcomp_is_functor[OF assms])
  show ?thesis by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
qed

lemma cf_blcomp_ArrMap_app[cat_cs_simps]: 
  assumes "\<SS> : \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "F = [h, g, f]\<^sub>\<circ>"
    and "h \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    and "g \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    and "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  shows "cf_blcomp \<SS>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> = (h \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>A\<^bsub>\<SS>\<^esub> g) \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>A\<^bsub>\<SS>\<^esub> f"
proof-
  interpret \<SS>: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C \<CC>\<close> \<CC> \<SS> by (rule assms)
  interpret cf_blcomp: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC>\<close> \<CC> \<open>cf_blcomp \<SS>\<close>
    by (rule cf_blcomp_is_functor[OF assms(1)])
  from assms(3-5) show ?thesis
    unfolding assms(2)
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps cat_prod_cs_simps cf_blcomp_def' 
          cs_intro: cat_cs_intros cat_prod_cs_intros
      )
qed

lemma cf_brcomp_ArrMap_app[cat_cs_simps]: 
  assumes "\<SS> : \<CC> \<times>\<^sub>C \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "F = [h, g, f]\<^sub>\<circ>"
    and "h \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    and "g \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    and "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  shows "cf_brcomp \<SS>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> = h \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>A\<^bsub>\<SS>\<^esub> (g \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>A\<^bsub>\<SS>\<^esub> f)"
proof-
  interpret \<SS>: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C \<CC>\<close> \<CC> \<SS> by (rule assms)
  interpret cf_brcomp: is_functor \<alpha> \<open>\<CC> \<times>\<^sub>C\<^sub>3 \<CC> \<times>\<^sub>C\<^sub>3 \<CC>\<close> \<CC> \<open>cf_brcomp \<SS>\<close>
    by (rule cf_brcomp_is_functor[OF assms(1)])
  from assms(3-5) show ?thesis
    unfolding assms(2)
    by
      (
        cs_concl
          cs_simp: cat_cs_simps cat_prod_cs_simps cf_brcomp_def'
          cs_intro: cat_cs_intros cat_prod_cs_intros
      )
qed



subsection\<open>Binatural transformation\<close>


subsubsection\<open>Definitions and elementary properties\<close>

text\<open>
In this work, a \<open>binatural transformation\<close> is used to denote a natural 
transformation of bifunctors.
\<close>

definition bnt_proj_fst :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  (\<open>(_\<^bsub>_,_\<^esub>/'(/-,_/')/\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<close> [51, 51, 51, 51] 51)
  where "\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F =
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<AA>\<lparr>Obj\<rparr>. \<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>),
      \<NN>\<lparr>NTDom\<rparr>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F,
      \<NN>\<lparr>NTCod\<rparr>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F,
      \<AA>,
      \<NN>\<lparr>NTDGCod\<rparr>
    ]\<^sub>\<circ>"

definition bnt_proj_snd :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  (\<open>(_\<^bsub>_,_\<^esub>/'(/_,-/')/\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<close> [51, 51, 51, 51] 51)
  where "\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F =
    [
      (\<lambda>b\<in>\<^sub>\<circ>\<BB>\<lparr>Obj\<rparr>. \<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>),
      \<NN>\<lparr>NTDom\<rparr>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F,
      \<NN>\<lparr>NTCod\<rparr>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F,
      \<BB>,
      \<NN>\<lparr>NTDGCod\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components\<close>

lemma bnt_proj_fst_components:
  shows "(\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr> = (\<lambda>a\<in>\<^sub>\<circ>\<AA>\<lparr>Obj\<rparr>. \<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>)"
    and "(\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTDom\<rparr> = \<NN>\<lparr>NTDom\<rparr>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F"
    and "(\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTCod\<rparr> = \<NN>\<lparr>NTCod\<rparr>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F"
    and "(\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTDGDom\<rparr> = \<AA>"
    and "(\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTDGCod\<rparr> = \<NN>\<lparr>NTDGCod\<rparr>"
  unfolding bnt_proj_fst_def nt_field_simps by (simp_all add: nat_omega_simps)

lemma bnt_proj_snd_components:
  shows "(\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr> = (\<lambda>b\<in>\<^sub>\<circ>\<BB>\<lparr>Obj\<rparr>. \<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>)"
    and "(\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTDom\<rparr> = \<NN>\<lparr>NTDom\<rparr>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F"
    and "(\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTCod\<rparr> = \<NN>\<lparr>NTCod\<rparr>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F"
    and "(\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTDGDom\<rparr> = \<BB>"
    and "(\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTDGCod\<rparr> = \<NN>\<lparr>NTDGCod\<rparr>"
  unfolding bnt_proj_snd_def nt_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Natural transformation maps\<close>

mk_VLambda bnt_proj_fst_components(1)[folded VLambda_vconst_on]
  |vsv bnt_proj_fst_NTMap_vsv[cat_cs_intros]|
  |vdomain bnt_proj_fst_NTMap_vdomain[cat_cs_simps]|
  |app bnt_proj_fst_NTMap_app[cat_cs_simps]|

lemma bnt_proj_fst_vrange:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<R>\<^sub>\<circ> ((\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof-
  interpret \<NN>: is_ntcf \<alpha> \<open>\<AA> \<times>\<^sub>C \<BB>\<close> \<CC> \<SS> \<SS>' \<NN> by (rule assms(3))
  show ?thesis
    unfolding bnt_proj_fst_components
  proof(rule vrange_VLambda_vsubset)
    fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"    
    with assms show "\<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
      by (cs_concl cs_intro: cat_cs_intros cat_prod_cs_intros)
  qed
qed

mk_VLambda bnt_proj_snd_components(1)[folded VLambda_vconst_on]
  |vsv bnt_proj_snd_NTMap_vsv[intro]|
  |vdomain bnt_proj_snd_NTMap_vdomain[cat_cs_simps]|
  |app bnt_proj_snd_NTMap_app[cat_cs_simps]|

lemma bnt_proj_snd_vrange:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "\<R>\<^sub>\<circ> ((\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof-
  interpret \<NN>: is_ntcf \<alpha> \<open>\<AA> \<times>\<^sub>C \<BB>\<close> \<CC> \<SS> \<SS>' \<NN> by (rule assms(3))
  show ?thesis
    unfolding bnt_proj_snd_components
  proof(rule vrange_VLambda_vsubset)
    fix b assume "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"    
    with assms show "\<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
      by (cs_concl cs_intro: cat_cs_intros cat_prod_cs_intros)
  qed
qed


subsubsection\<open>Binatural transformation projection is a natural transformation\<close>

lemma bnt_proj_snd_is_ntcf:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F : \<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F \<mapsto>\<^sub>C\<^sub>F \<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(2))
  interpret \<NN>: is_ntcf \<alpha> \<open>\<AA> \<times>\<^sub>C \<BB>\<close> \<CC> \<SS> \<SS>' \<NN> by (rule assms(3))
  show ?thesis
  proof(intro is_ntcfI')
    show "vfsequence (\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)" unfolding bnt_proj_snd_def by simp 
    show "vcard (\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F) = 5\<^sub>\<nat>"
      unfolding bnt_proj_snd_def by (simp add: nat_omega_simps)
    from assms show "\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from assms show "\<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    show "(\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>\<lparr>b\<rparr> :
      (\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> (\<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      if "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" for b
      using that assms 
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros
        )
    show "(\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
      (\<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>\<lparr>a'\<rparr>"
      if "f : a' \<mapsto>\<^bsub>\<BB>\<^esub> b" for a' b f
      using that assms 
      by 
        (
          cs_concl 
            cs_simp: is_ntcf.ntcf_Comp_commute cat_cs_simps 
            cs_intro: cat_cs_intros cat_prod_cs_intros
        )
  qed (auto simp: bnt_proj_snd_components cat_cs_simps)
qed

lemma bnt_proj_snd_is_ntcf'[cat_cs_intros]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "\<FF> = \<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F"
    and "\<GG> = \<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F"
  shows "\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms by (auto intro: bnt_proj_snd_is_ntcf)

lemma bnt_proj_fst_is_ntcf:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F : \<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F \<mapsto>\<^sub>C\<^sub>F \<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(2))
  interpret \<NN>: is_ntcf \<alpha> \<open>\<AA> \<times>\<^sub>C \<BB>\<close> \<CC> \<SS> \<SS>' \<NN> by (rule assms(3))
  show ?thesis
  proof(intro is_ntcfI')
    show "vfsequence (\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)" unfolding bnt_proj_fst_def by simp 
    show "vcard (\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F) = 5\<^sub>\<nat>"
      unfolding bnt_proj_fst_def by (simp add: nat_omega_simps)
    from assms show "\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F : \<AA>  \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_intro: cat_cs_intros)
    from assms show "\<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
      by (cs_concl cs_intro: cat_cs_intros)
    show "(\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> :
      (\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> (\<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      if "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" for a
      using that assms 
      by
        (
          cs_concl
            cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros
        )
    show "(\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>\<lparr>b'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> =
      (\<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      if "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b'" for a b' f
      using that assms 
      by
        (
          cs_concl
            cs_simp: is_ntcf.ntcf_Comp_commute cat_cs_simps 
            cs_intro: cat_cs_intros cat_prod_cs_intros
        )
  qed (auto simp: bnt_proj_fst_components cat_cs_simps)
qed

lemma bnt_proj_fst_is_ntcf'[cat_cs_intros]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    and "\<FF> = \<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F"
    and "\<GG> = \<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F"
    and "\<AA>' = \<AA>"
  shows "\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1-4) unfolding assms(5-7) by (rule bnt_proj_fst_is_ntcf)


subsubsection\<open>Array binatural transformation is a natural transformation\<close>

lemma ntcf_array_is_ntcf:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<SS> : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "vfsequence \<NN>"
    and "vcard \<NN> = 5\<^sub>\<nat>"
    and "\<NN>\<lparr>NTDom\<rparr> = \<SS>"
    and "\<NN>\<lparr>NTCod\<rparr> = \<SS>'"
    and "\<NN>\<lparr>NTDGDom\<rparr> = \<AA> \<times>\<^sub>C \<BB>"
    and "\<NN>\<lparr>NTDGCod\<rparr> = \<CC>"
    and "vsv (\<NN>\<lparr>NTMap\<rparr>)"
    and "\<D>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>) = (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
    and "\<And>a b. \<lbrakk> a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow>
      \<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> : \<SS>\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> \<mapsto>\<^bsub>\<CC>\<^esub> \<SS>'\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>"
    and "\<And>a. a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<Longrightarrow>
      \<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F : \<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F \<mapsto>\<^sub>C\<^sub>F \<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<And>b. b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr> \<Longrightarrow>
      \<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F : \<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F \<mapsto>\<^sub>C\<^sub>F \<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"  
  shows "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
proof-

  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(2))
  interpret \<NN>: vsv \<open>\<NN>\<lparr>NTMap\<rparr>\<close> by (rule assms(11))  

  have [cat_cs_intros]:
    "\<lbrakk> a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>; A = \<SS>\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>; B = \<SS>'\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> \<rbrakk> \<Longrightarrow>
      \<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> : A \<mapsto>\<^bsub>\<CC>\<^esub> B"
    for a b A B
    by (auto intro: assms(13))

  show ?thesis
  proof(intro is_ntcfI')

    show "\<NN>\<lparr>NTMap\<rparr>\<lparr>ab\<rparr> : \<SS>\<lparr>ObjMap\<rparr>\<lparr>ab\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<SS>'\<lparr>ObjMap\<rparr>\<lparr>ab\<rparr>"
      if "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>" for ab
    proof-
      from that obtain a b 
        where ab_def: "ab = [a, b]\<^sub>\<circ>" and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
        by (elim cat_prod_2_ObjE[OF assms(1,2)])
      from a b show ?thesis unfolding ab_def by (rule assms(13))
    qed
    
    show
      "\<NN>\<lparr>NTMap\<rparr>\<lparr>a'b'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<SS>\<lparr>ArrMap\<rparr>\<lparr>gf\<rparr> = \<SS>'\<lparr>ArrMap\<rparr>\<lparr>gf\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>ab\<rparr>"
      if "gf : ab \<mapsto>\<^bsub>\<AA> \<times>\<^sub>C \<BB>\<^esub> a'b'" for ab a'b' gf
    proof-
      from that obtain g f a b a' b'
        where gf_def: "gf = [g, f]\<^sub>\<circ>" 
          and ab_def: "ab = [a, b]\<^sub>\<circ>" 
          and a'b'_def: "a'b' = [a', b']\<^sub>\<circ>"
          and g: "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
          and f: "f : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
        by (elim cat_prod_2_is_arrE[OF assms(1,2)])
      then have a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
        and a': "a' \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
        and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
        and b': "b' \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
        by auto
      show ?thesis
        unfolding gf_def ab_def a'b'_def
      proof-
        from is_ntcfD'(13)[OF assms(15)[OF b] g] g f assms(1,2,3,4) 
        have [cat_cs_simps]:
          "(\<SS>'\<lparr>ArrMap\<rparr>\<lparr>g, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>) =
            (\<NN>\<lparr>NTMap\<rparr>\<lparr>a', b\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<SS>\<lparr>ArrMap\<rparr>\<lparr>g, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>\<rparr>\<^sub>\<bullet>)"
          by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros) auto
        from is_ntcfD'(13)[OF assms(14)[OF a'] f] g f assms(1,2) 
        have \<SS>'\<NN>:
          "\<SS>'\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>a'\<rparr>, f\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a', b\<rparr>\<^sub>\<bullet> =
            \<NN>\<lparr>NTMap\<rparr>\<lparr>a', b'\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<SS>\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>a'\<rparr>,f\<rparr>\<^sub>\<bullet>"
          by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros) auto
        from g f assms(1-4) have [cat_cs_simps]: 
          "\<SS>'\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>a'\<rparr>, f\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<NN>\<lparr>NTMap\<rparr>\<lparr>a', b\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> q) =
            \<NN>\<lparr>NTMap\<rparr>\<lparr>a', b'\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (\<SS>\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>a'\<rparr>,f\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> q)"
          if "q : r \<mapsto>\<^bsub>\<CC>\<^esub> \<SS>\<lparr>ObjMap\<rparr>\<lparr>a', b\<rparr>\<^sub>\<bullet>" for q r
          using that
          by
            (
              cs_concl
                cs_simp: \<SS>'\<NN> category.cat_Comp_assoc[symmetric]  
                cs_intro: cat_cs_intros cat_prod_cs_intros
            ) 

        from assms(1-4) g f have 
          "\<SS>'\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>a'\<rparr>, f\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<SS>'\<lparr>ArrMap\<rparr>\<lparr>g, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>\<rparr>\<^sub>\<bullet> =
            \<SS>'\<lparr>ArrMap\<rparr>\<lparr>[\<AA>\<lparr>CId\<rparr>\<lparr>a'\<rparr>, f]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>\<AA> \<times>\<^sub>C \<BB>\<^esub> [g, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>]\<^sub>\<circ>\<rparr>"
          by 
            (
              cs_concl 
                cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros
            ) 
        also from assms(1-4) g f have "\<dots> = \<SS>'\<lparr>ArrMap\<rparr> \<lparr>g, f\<rparr>\<^sub>\<bullet>"
          by 
            (
              cs_concl 
                cs_simp: cat_cs_simps cat_prod_cs_simps
                cs_intro: cat_cs_intros cat_prod_cs_intros
            )
        finally have \<SS>'_gf: "\<SS>'\<lparr>ArrMap\<rparr> \<lparr>g, f\<rparr>\<^sub>\<bullet> =
          \<SS>'\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>a'\<rparr>, f\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<SS>'\<lparr>ArrMap\<rparr>\<lparr>g, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>\<rparr>\<^sub>\<bullet>"
          by simp
        from assms(1-4) g f have 
          "\<SS>\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>a'\<rparr>, f\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<SS>\<lparr>ArrMap\<rparr>\<lparr>g, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>\<rparr>\<^sub>\<bullet> =
            \<SS>\<lparr>ArrMap\<rparr>\<lparr>[\<AA>\<lparr>CId\<rparr>\<lparr>a'\<rparr>, f]\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>\<AA> \<times>\<^sub>C \<BB>\<^esub> [g, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>]\<^sub>\<circ>\<rparr>"
          by 
            (
              cs_concl 
                cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros
            ) 
        also from assms(1-4) g f have "\<dots> = \<SS>\<lparr>ArrMap\<rparr> \<lparr>g, f\<rparr>\<^sub>\<bullet>"
          by 
            (
              cs_concl 
                cs_simp: cat_cs_simps cat_prod_cs_simps
                cs_intro: cat_cs_intros cat_prod_cs_intros
            )
        finally have \<SS>_gf: "\<SS>\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> =
          \<SS>\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>a'\<rparr>, f\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<SS>\<lparr>ArrMap\<rparr>\<lparr>g, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>\<rparr>\<^sub>\<bullet>"
          by simp
        from assms(1-4) g f assms(13)[OF a b] assms(13)[OF a' b] have 
          "\<SS>'\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> =
            (\<SS>'\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>a'\<rparr>, f\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a', b\<rparr>\<^sub>\<bullet>) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub>
            \<SS>\<lparr>ArrMap\<rparr>\<lparr>g, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>\<rparr>\<^sub>\<bullet>"
          unfolding \<SS>'_gf 
          by
            (
              cs_concl
                cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros
            )
        also from assms(1-4) g f have 
          "\<dots> = (\<NN>\<lparr>NTMap\<rparr>\<lparr>a', b'\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<SS>\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>a'\<rparr>,f\<rparr>\<^sub>\<bullet>) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub>
            \<SS>\<lparr>ArrMap\<rparr>\<lparr>g, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>\<rparr>\<^sub>\<bullet>"
          by
            (
              cs_concl
                cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros
            )
        also from assms(1-4) g f assms(13)[OF a' b'] have 
          "\<dots> = \<NN>\<lparr>NTMap\<rparr>\<lparr>a', b'\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub>
            (\<SS>\<lparr>ArrMap\<rparr>\<lparr>\<AA>\<lparr>CId\<rparr>\<lparr>a'\<rparr>,f\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<SS>\<lparr>ArrMap\<rparr>\<lparr>g, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>\<rparr>\<^sub>\<bullet>)"
          by 
            (
              cs_concl 
                cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_prod_cs_intros
            )
        also from assms(1-4) g f assms(13)[OF a' b'] have 
          "\<dots> = \<NN>\<lparr>NTMap\<rparr>\<lparr>a', b'\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<SS>\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet>"
          unfolding \<SS>_gf[symmetric] by simp
        finally show 
          "\<NN>\<lparr>NTMap\<rparr>\<lparr>a', b'\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<SS>\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> =
            \<SS>'\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>"
          by simp
      qed
    qed

  qed (auto simp: assms)

qed


subsubsection\<open>Binatural transformation projections and isomorphisms\<close>

lemma is_iso_ntcf_if_bnt_proj_snd_is_iso_ntcf:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<And>a. a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<Longrightarrow> 
      \<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F : \<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
proof-
  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(2))
  show ?thesis  
  proof(intro is_iso_ntcfI)
    show "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" by (rule assms(3))
    fix ab assume "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
    then obtain a b 
      where ab_def: "ab = [a, b]\<^sub>\<circ>" and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
      by (elim cat_prod_2_ObjE[OF assms(1,2)])
    interpret \<NN>a: is_iso_ntcf 
      \<alpha> \<BB> \<CC> \<open>\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F\<close> \<open>\<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F\<close> \<open>\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<close>
      by (rule assms(4)[OF a])
    from b have \<NN>ab: "\<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> = (\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>\<lparr>b\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps)
    from \<NN>a.iso_ntcf_is_arr_isomorphism[OF b] assms(1,2,3) a b show
      "\<NN>\<lparr>NTMap\<rparr>\<lparr>ab\<rparr> : \<SS>\<lparr>ObjMap\<rparr>\<lparr>ab\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> \<SS>'\<lparr>ObjMap\<rparr>\<lparr>ab\<rparr>" 
      by (cs_prems cs_simp: cat_cs_simps ab_def cs_intro: cat_prod_cs_intros)
  qed
qed

lemma is_iso_ntcf_if_bnt_proj_fst_is_iso_ntcf:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<And>b. b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr> \<Longrightarrow>
      \<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F : \<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
proof-
  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(2))
  show ?thesis  
  proof(intro is_iso_ntcfI)
    show "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" by (rule assms(3))
    fix ab assume "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
    then obtain a b 
      where ab_def: "ab = [a, b]\<^sub>\<circ>" and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
      by (elim cat_prod_2_ObjE[OF assms(1,2)])
    interpret \<NN>a: is_iso_ntcf 
      \<alpha> \<AA> \<CC> \<open>\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F\<close> \<open>\<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F\<close> \<open>\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<close>
      by (rule assms(4)[OF b])
    from b have \<NN>ab: "\<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> = (\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>\<lparr>b\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    from \<NN>a.iso_ntcf_is_arr_isomorphism[OF a] assms(1,2,3) a b show
      "\<NN>\<lparr>NTMap\<rparr>\<lparr>ab\<rparr> : \<SS>\<lparr>ObjMap\<rparr>\<lparr>ab\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> \<SS>'\<lparr>ObjMap\<rparr>\<lparr>ab\<rparr>"
      unfolding ab_def 
      by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_prod_cs_intros)
  qed
qed

lemma bnt_proj_snd_is_iso_ntcf_if_is_iso_ntcf:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F :
    \<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_iso_ntcfI)
  from assms show "\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F :
    \<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F \<mapsto>\<^sub>C\<^sub>F \<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: cat_cs_intros ntcf_cs_intros)
  show "(\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>\<lparr>b\<rparr> :
    (\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> (\<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    if "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" for b
    using assms that 
    by
      (
        cs_concl
          cs_simp: cat_cs_simps cs_intro: cat_prod_cs_intros cat_arrow_cs_intros
      )
qed

lemma bnt_proj_snd_is_iso_ntcf_if_is_iso_ntcf'[cat_cs_intros]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<FF> = \<SS>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F"
    and "\<GG> = \<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>C\<^sub>F"
    and "\<BB>' = \<BB>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<BB>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  unfolding assms(4-6) 
  by (rule bnt_proj_snd_is_iso_ntcf_if_is_iso_ntcf[OF assms(1-3,7)])

lemma bnt_proj_fst_is_iso_ntcf_if_is_iso_ntcf:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F :
    \<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof(intro is_iso_ntcfI)
  from assms show "\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F :
    \<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F \<mapsto>\<^sub>C\<^sub>F \<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: cat_cs_intros ntcf_cs_intros)
  show "(\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> :
    (\<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> (\<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    if "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" for a
    using assms that 
    by
      (
        cs_concl
          cs_simp: cat_cs_simps
          cs_intro: cat_prod_cs_intros cat_arrow_cs_intros
      )
qed

lemma bnt_proj_fst_is_iso_ntcf_if_is_iso_ntcf'[cat_cs_intros]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<FF> = \<SS>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F"
    and "\<GG> = \<SS>'\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>C\<^sub>F"
    and "\<AA>' = \<AA>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  unfolding assms(4-6) 
  by (rule bnt_proj_fst_is_iso_ntcf_if_is_iso_ntcf[OF assms(1-3,7)])



subsection\<open>Binatural transformation flip\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition bnt_flip :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "bnt_flip \<AA> \<BB> \<NN> =
    [
      fflip (\<NN>\<lparr>NTMap\<rparr>), 
      bifunctor_flip \<AA> \<BB> (\<NN>\<lparr>NTDom\<rparr>),
      bifunctor_flip \<AA> \<BB> (\<NN>\<lparr>NTCod\<rparr>),
      \<BB> \<times>\<^sub>C \<AA>,
      \<NN>\<lparr>NTDGCod\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma bnt_flip_components:
  shows "bnt_flip \<AA> \<BB> \<NN>\<lparr>NTMap\<rparr> = fflip (\<NN>\<lparr>NTMap\<rparr>)"
    and "bnt_flip \<AA> \<BB> \<NN>\<lparr>NTDom\<rparr> = bifunctor_flip \<AA> \<BB> (\<NN>\<lparr>NTDom\<rparr>)"
    and "bnt_flip \<AA> \<BB> \<NN>\<lparr>NTCod\<rparr> = bifunctor_flip \<AA> \<BB> (\<NN>\<lparr>NTCod\<rparr>)"
    and "bnt_flip \<AA> \<BB> \<NN>\<lparr>NTDGDom\<rparr> = \<BB> \<times>\<^sub>C \<AA>"
    and "bnt_flip \<AA> \<BB> \<NN>\<lparr>NTDGCod\<rparr> = \<NN>\<lparr>NTDGCod\<rparr>"
  unfolding bnt_flip_def nt_field_simps by (simp_all add: nat_omega_simps)

context 
  fixes \<alpha> \<AA> \<BB> \<CC> \<SS> \<SS>' \<NN>
  assumes \<NN>: "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
begin

interpretation \<NN>: is_ntcf \<alpha> \<open>\<AA> \<times>\<^sub>C \<BB>\<close> \<CC> \<SS> \<SS>' \<NN> by (rule \<NN>)

lemmas bnt_flip_components' = 
  bnt_flip_components[where \<AA>=\<AA> and \<BB>=\<BB> and \<NN>=\<NN>, unfolded cat_cs_simps]

lemmas [cat_cs_simps] = bnt_flip_components'(2-5)

end


subsubsection\<open>Natural transformation map\<close>

lemma bnt_flip_NTMap_vsv[cat_cs_intros]: "vsv (bnt_flip \<AA> \<BB> \<NN>\<lparr>NTMap\<rparr>)"
  unfolding bnt_flip_components by (rule fflip_vsv)

lemma bnt_flip_NTMap_app:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "bnt_flip \<AA> \<BB> \<NN>\<lparr>NTMap\<rparr>\<lparr>b, a\<rparr>\<^sub>\<bullet> = \<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>"
  using assms
  unfolding bnt_flip_components
  by (cs_concl cs_simp: V_cs_simps cat_cs_simps cs_intro: cat_prod_cs_intros)

lemma bnt_flip_NTMap_app'[cat_cs_simps]:
  assumes "ba = [b, a]\<^sub>\<circ>"
    and "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "bnt_flip \<AA> \<BB> \<NN>\<lparr>NTMap\<rparr>\<lparr>ba\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet>"
  using assms(2-6) unfolding assms(1) by (rule bnt_flip_NTMap_app)

lemma bnt_flip_NTMap_vdomain[cat_cs_simps]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
  shows "\<D>\<^sub>\<circ> (bnt_flip \<AA> \<BB> \<NN>\<lparr>NTMap\<rparr>) = (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>"
  using assms
  unfolding bnt_flip_components
  by (cs_concl cs_simp: V_cs_simps cat_cs_simps)

lemma bnt_flip_NTMap_vrange[cat_cs_simps]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
  shows "\<R>\<^sub>\<circ> (bnt_flip \<AA> \<BB> \<NN>\<lparr>NTMap\<rparr>) = \<R>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>)"
proof-
  
  interpret \<NN>: is_ntcf \<alpha> \<open>\<AA> \<times>\<^sub>C \<BB>\<close> \<CC> \<SS> \<SS>' \<NN> by (rule assms(3))

  show ?thesis
  proof(intro vsubset_antisym)

    show "\<R>\<^sub>\<circ> (bnt_flip \<AA> \<BB> \<NN>\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>)"
    proof
      (
        intro vsv.vsv_vrange_vsubset, 
        unfold bnt_flip_NTMap_vdomain[OF assms]
      )
      fix ba assume "ba \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>"
      then obtain a b
        where ba_def: "ba = [b, a]\<^sub>\<circ>" 
          and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
          and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
        by (elim cat_prod_2_ObjE[OF assms(2,1)])
      from \<NN>.ntcf_NTMap_vsv assms a b show 
        "bnt_flip \<AA> \<BB> \<NN>\<lparr>NTMap\<rparr>\<lparr>ba\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>)"
        unfolding ba_def
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cs_intro: V_cs_intros cat_prod_cs_intros
          )
    qed (cs_concl cs_intro: cat_cs_intros)

    show "\<R>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (bnt_flip \<AA> \<BB> \<NN>\<lparr>NTMap\<rparr>)"
    proof(intro vsv.vsv_vrange_vsubset, unfold \<NN>.ntcf_NTMap_vdomain)
      fix ab assume prems: "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
      then obtain a b 
        where ab_def: "ab = [a, b]\<^sub>\<circ>" 
          and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
          and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
        by (elim cat_prod_2_ObjE[OF assms(1,2)])
      from assms a b have ba: "[b, a]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>"
        by (cs_concl cs_intro: cat_prod_cs_intros)
      from assms bnt_flip_NTMap_vsv prems a b ba show 
        "\<NN>\<lparr>NTMap\<rparr>\<lparr>ab\<rparr> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (bnt_flip \<AA> \<BB> \<NN>\<lparr>NTMap\<rparr>)"
        unfolding ab_def 
        by (cs_concl cs_simp: cat_cs_simps cs_intro: V_cs_intros)
    qed auto

  qed

qed


subsubsection\<open>Binatural transformation flip natural transformation map\<close>

lemma bnt_flip_NTMap_is_ntcf:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
  shows "bnt_flip \<AA> \<BB> \<NN> : 
    bifunctor_flip \<AA> \<BB> \<SS> \<mapsto>\<^sub>C\<^sub>F bifunctor_flip \<AA> \<BB> \<SS>' : 
    \<BB> \<times>\<^sub>C \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-

  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(2))

  interpret \<NN>: is_ntcf \<alpha> \<open>\<AA> \<times>\<^sub>C \<BB>\<close> \<CC> \<SS> \<SS>' \<NN> by (rule assms(3))

  show ?thesis
  proof(intro is_ntcfI')
    show "vfsequence (bnt_flip \<AA> \<BB> \<NN>)" unfolding bnt_flip_def by simp
    show "vcard (bnt_flip \<AA> \<BB> \<NN>) = 5\<^sub>\<nat>"
      unfolding bnt_flip_def by (simp add: nat_omega_simps)
    show "bnt_flip \<AA> \<BB> \<NN>\<lparr>NTMap\<rparr>\<lparr>ba\<rparr> :
      bifunctor_flip \<AA> \<BB> \<SS>\<lparr>ObjMap\<rparr>\<lparr>ba\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub>
      bifunctor_flip \<AA> \<BB> \<SS>'\<lparr>ObjMap\<rparr>\<lparr>ba\<rparr>"
      if "ba \<in>\<^sub>\<circ> (\<BB> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>" for ba
    proof-
      from that obtain b a 
        where ba_def: "ba = [b, a]\<^sub>\<circ>" 
          and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
          and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
        by (elim cat_prod_2_ObjE[rotated 2]) (auto intro: cat_cs_intros)
      from assms a b show ?thesis 
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps ba_def 
              cs_intro: cat_cs_intros cat_prod_cs_intros
          )
    qed
    show 
      "bnt_flip \<AA> \<BB> \<NN>\<lparr>NTMap\<rparr>\<lparr>b'a'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> bifunctor_flip \<AA> \<BB> \<SS>\<lparr>ArrMap\<rparr>\<lparr>gf\<rparr> =
        bifunctor_flip \<AA> \<BB> \<SS>'\<lparr>ArrMap\<rparr>\<lparr>gf\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> bnt_flip \<AA> \<BB> \<NN>\<lparr>NTMap\<rparr>\<lparr>ba\<rparr>"
      if "gf : ba \<mapsto>\<^bsub>\<BB> \<times>\<^sub>C \<AA>\<^esub> b'a'" for ba b'a' gf
    proof-
      from that obtain g f a b a' b'
        where gf_def: "gf = [g, f]\<^sub>\<circ>"
          and ba_def: "ba = [b, a]\<^sub>\<circ>"
          and b'a'_def: "b'a' = [b', a']\<^sub>\<circ>"
          and g: "g : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
          and f: "f : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
        by (elim cat_prod_2_is_arrE[OF assms(2,1)])
      from assms g f show ?thesis
        unfolding gf_def ba_def b'a'_def
        by 
          ( 
            cs_concl 
              cs_simp: cat_cs_simps cat_cs_simps \<NN>.ntcf_Comp_commute
              cs_intro: cat_cs_intros cat_prod_cs_intros
          )
    qed

  qed (use assms in \<open>cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros\<close>)+

qed

lemma bnt_flip_NTMap_is_ntcf'[cat_cs_intros]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<T> = bifunctor_flip \<AA> \<BB> \<SS>"
    and "\<T>' = bifunctor_flip \<AA> \<BB> \<SS>'"
    and "\<DD> = \<BB> \<times>\<^sub>C \<AA>"
  shows "bnt_flip \<AA> \<BB> \<NN> : \<T> \<mapsto>\<^sub>C\<^sub>F \<T>' : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1-3) unfolding assms(4-6) by (intro bnt_flip_NTMap_is_ntcf)


subsubsection\<open>Double-flip of a binatural transformation\<close>

lemma bnt_flip_flip[cat_cs_simps]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
  shows "bnt_flip \<BB> \<AA> (bnt_flip \<AA> \<BB> \<NN>) = \<NN>"
proof(rule ntcf_eqI)
  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(2))
  interpret \<NN>: is_ntcf \<alpha> \<open>\<AA> \<times>\<^sub>C \<BB>\<close> \<CC> \<SS> \<SS>' \<NN> by (rule assms(3))
  from assms show
    "bnt_flip \<BB> \<AA> (bnt_flip \<AA> \<BB> \<NN>) : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  then have dom_lhs:
    "\<D>\<^sub>\<circ> (bnt_flip \<BB> \<AA> (bnt_flip \<AA> \<BB> \<NN>)\<lparr>NTMap\<rparr>) = (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)
  show "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" by (rule assms(3))
  then have dom_rhs: "\<D>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>) = (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)
  show "bnt_flip \<BB> \<AA> (bnt_flip \<AA> \<BB> \<NN>)\<lparr>NTMap\<rparr> = \<NN>\<lparr>NTMap\<rparr>"
  proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
    fix ab assume "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<BB>)\<lparr>Obj\<rparr>"
    then obtain a b
      where ab_def: "ab = [a, b]\<^sub>\<circ>" 
        and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
        and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
      by (rule cat_prod_2_ObjE[OF assms(1,2)])
    from assms a b show 
      "bnt_flip \<BB> \<AA> (bnt_flip \<AA> \<BB> \<NN>)\<lparr>NTMap\<rparr>\<lparr>ab\<rparr> = \<NN>\<lparr>NTMap\<rparr>\<lparr>ab\<rparr>" 
      by (cs_concl cs_simp: cat_cs_simps ab_def cs_intro: cat_cs_intros)
  qed (cs_concl cs_intro: V_cs_intros cat_cs_intros)+
qed simp_all


subsubsection\<open>A projection of a flip of a binatural transformation\<close>

lemma bnt_flip_proj_snd[cat_cs_simps]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "bnt_flip \<AA> \<BB> \<NN>\<^bsub>\<BB>,\<AA>\<^esub>(b,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F = \<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F"
proof(rule ntcf_eqI)
  from assms show "bnt_flip \<AA> \<BB> \<NN>\<^bsub>\<BB>,\<AA>\<^esub>(b,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F :
    bifunctor_flip \<AA> \<BB> \<SS>\<^bsub>\<BB>,\<AA>\<^esub>(b,-)\<^sub>C\<^sub>F \<mapsto>\<^sub>C\<^sub>F bifunctor_flip \<AA> \<BB> \<SS>'\<^bsub>\<BB>,\<AA>\<^esub>(b,-)\<^sub>C\<^sub>F :
    \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: cat_cs_intros)
  from assms show "\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F :
    bifunctor_flip \<AA> \<BB> \<SS>\<^bsub>\<BB>,\<AA>\<^esub>(b,-)\<^sub>C\<^sub>F \<mapsto>\<^sub>C\<^sub>F bifunctor_flip \<AA> \<BB> \<SS>'\<^bsub>\<BB>,\<AA>\<^esub>(b,-)\<^sub>C\<^sub>F :
    \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms have dom_lhs: 
    "\<D>\<^sub>\<circ> ((bnt_flip \<AA> \<BB> \<NN>\<^bsub>\<BB>,\<AA>\<^esub>(b,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)
  from assms have dom_rhs: "\<D>\<^sub>\<circ> ((\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>) = \<AA>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps)
  show "(bnt_flip \<AA> \<BB> \<NN>\<^bsub>\<BB>,\<AA>\<^esub>(b,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr> = (\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>"
  proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
    fix a assume "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    with assms show 
      "(bnt_flip \<AA> \<BB> \<NN>\<^bsub>\<BB>,\<AA>\<^esub>(b,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>\<lparr>a\<rparr> = (\<NN>\<^bsub>\<AA>,\<BB>\<^esub>(-,b)\<^sub>N\<^sub>T\<^sub>C\<^sub>F)\<lparr>NTMap\<rparr>\<lparr>a\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps)
  qed (auto simp: cat_cs_intros)
qed simp_all

lemma bnt_flip_proj_fst[cat_cs_simps]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
  shows "bnt_flip \<AA> \<BB> \<NN>\<^bsub>\<BB>,\<AA>\<^esub>(-,a)\<^sub>N\<^sub>T\<^sub>C\<^sub>F = \<NN>\<^bsub>\<AA>,\<BB>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F"
proof-
  from assms have f_\<NN>: 
    "bnt_flip \<AA> \<BB> \<NN> :
      bifunctor_flip \<AA> \<BB> \<SS> \<mapsto>\<^sub>C\<^sub>F bifunctor_flip \<AA> \<BB> \<SS>' :
      \<BB> \<times>\<^sub>C \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: cat_cs_intros)
  show ?thesis
    by 
      (
        rule 
          bnt_flip_proj_snd
            [
              OF assms(2,1) f_\<NN> assms(4), 
              unfolded bnt_flip_flip[OF assms(1,2,3)],
              symmetric
            ]
      )
qed


subsubsection\<open>A flip of a binatural isomorphism\<close>

lemma bnt_flip_is_iso_ntcf:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "bnt_flip \<AA> \<BB> \<NN> :
    bifunctor_flip \<AA> \<BB> \<SS> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o bifunctor_flip \<AA> \<BB> \<SS>' : 
    \<BB> \<times>\<^sub>C \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof(rule is_iso_ntcf_if_bnt_proj_snd_is_iso_ntcf)
  from assms show f_\<NN>: "bnt_flip \<AA> \<BB> \<NN> :
    bifunctor_flip \<AA> \<BB> \<SS> \<mapsto>\<^sub>C\<^sub>F bifunctor_flip \<AA> \<BB> \<SS>' :
    \<BB> \<times>\<^sub>C \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: cat_cs_intros ntcf_cs_intros)
  fix a assume "a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  with assms f_\<NN> show 
    "bnt_flip \<AA> \<BB> \<NN>\<^bsub>\<BB>,\<AA>\<^esub>(a,-)\<^sub>N\<^sub>T\<^sub>C\<^sub>F :
      bifunctor_flip \<AA> \<BB> \<SS>\<^bsub>\<BB>,\<AA>\<^esub>(a,-)\<^sub>C\<^sub>F \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o
      bifunctor_flip \<AA> \<BB> \<SS>'\<^bsub>\<BB>,\<AA>\<^esub>(a,-)\<^sub>C\<^sub>F :
      \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros ntcf_cs_intros)
qed (simp_all add: assms)

lemma bnt_flip_is_iso_ntcf'[cat_cs_intros]:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<NN> : \<SS> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<SS>' : \<AA> \<times>\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<FF> = bifunctor_flip \<AA> \<BB> \<SS>"
    and "\<GG> = bifunctor_flip \<AA> \<BB> \<SS>'"
    and "\<DD> = \<BB> \<times>\<^sub>C \<AA>"
  shows "bnt_flip \<AA> \<BB> \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<DD> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  using bnt_flip_is_iso_ntcf[OF assms(1-3)] unfolding assms(4-6) by simp

text\<open>\newpage\<close>

end