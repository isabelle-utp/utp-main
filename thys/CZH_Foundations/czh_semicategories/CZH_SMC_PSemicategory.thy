(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Product semicategory\<close>
theory CZH_SMC_PSemicategory
  imports 
    CZH_SMC_Semifunctor
    CZH_SMC_Small_Semicategory
    CZH_DG_PDigraph
begin



subsection\<open>Background\<close>


text\<open>
The concept of a product semicategory, as presented in this work, 
is a generalization of the concept of a product category, as presented in
Chapter II-3 in \cite{mac_lane_categories_2010}.
\<close>

named_theorems smc_prod_cs_simps
named_theorems smc_prod_cs_intros



subsection\<open>Product semicategory: definition and elementary properties\<close>

definition smc_prod :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V" 
  where "smc_prod I \<AA> = 
    [
      (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Obj\<rparr>), 
      (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>), 
      (\<lambda>f\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>). (\<lambda>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Dom\<rparr>\<lparr>f\<lparr>i\<rparr>\<rparr>)), 
      (\<lambda>f\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>). (\<lambda>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Cod\<rparr>\<lparr>f\<lparr>i\<rparr>\<rparr>)),
      (\<lambda>gf\<in>\<^sub>\<circ>composable_arrs (dg_prod I \<AA>). (\<lambda>i\<in>\<^sub>\<circ>I. gf\<lparr>0\<rparr>\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<AA> i\<^esub> gf\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>i\<rparr>))
    ]\<^sub>\<circ>"

syntax "_PSEMICATEGORY" :: "pttrn \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V" 
  ("(3\<Prod>\<^sub>S\<^sub>M\<^sub>C_\<in>\<^sub>\<circ>_./ _)" [0, 0, 10] 10)
translations "\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA>" \<rightleftharpoons> "CONST smc_prod I (\<lambda>i. \<AA>)"


text\<open>Components.\<close>

lemma smc_prod_components:
  shows "(\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr> = (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Obj\<rparr>)"
    and "(\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr> = (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>)"
    and "(\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Dom\<rparr> = 
      (\<lambda>f\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>). (\<lambda>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Dom\<rparr>\<lparr>f\<lparr>i\<rparr>\<rparr>))"
    and "(\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Cod\<rparr> = 
      (\<lambda>f\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>). (\<lambda>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Cod\<rparr>\<lparr>f\<lparr>i\<rparr>\<rparr>))"
    and "(\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Comp\<rparr> = 
      (\<lambda>gf\<in>\<^sub>\<circ>composable_arrs (dg_prod I \<AA>). (\<lambda>i\<in>\<^sub>\<circ>I. gf\<lparr>0\<rparr>\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<AA> i\<^esub> gf\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>i\<rparr>))"
  unfolding smc_prod_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smc_dg_smc_prod[slicing_commute]: 
  "dg_prod I (\<lambda>i. smc_dg (\<AA> i)) = smc_dg (smc_prod I \<AA>)"
  unfolding dg_prod_def smc_dg_def smc_prod_def dg_field_simps
  by (simp_all add: nat_omega_simps)

context
  fixes \<AA> \<phi> :: "V \<Rightarrow> V"
    and \<CC> :: V
begin

lemmas_with 
  [where \<AA>=\<open>\<lambda>i. smc_dg (\<AA> i)\<close>, unfolded slicing_simps slicing_commute]:
  smc_prod_ObjI = dg_prod_ObjI
  and smc_prod_ObjD = dg_prod_ObjD
  and smc_prod_ObjE = dg_prod_ObjE
  and smc_prod_Obj_cong = dg_prod_Obj_cong
  and smc_prod_ArrI = dg_prod_ArrI
  and smc_prod_ArrD = dg_prod_ArrD
  and smc_prod_ArrE = dg_prod_ArrE
  and smc_prod_Arr_cong = dg_prod_Arr_cong
  and smc_prod_Dom_vsv[smc_cs_intros] = dg_prod_Dom_vsv
  and smc_prod_Dom_vdomain[smc_cs_simps] = dg_prod_Dom_vdomain
  and smc_prod_Dom_app = dg_prod_Dom_app
  and smc_prod_Dom_app_component_app[smc_cs_simps] = 
    dg_prod_Dom_app_component_app
  and smc_prod_Cod_vsv[smc_cs_intros] = dg_prod_Cod_vsv
  and smc_prod_Cod_app = dg_prod_Cod_app
  and smc_prod_Cod_vdomain[smc_cs_simps] = dg_prod_Cod_vdomain
  and smc_prod_Cod_app_component_app[smc_cs_simps] = 
    dg_prod_Cod_app_component_app
  and smc_prod_vunion_Obj_in_Obj = dg_prod_vunion_Obj_in_Obj
  and smc_prod_vdiff_vunion_Obj_in_Obj = dg_prod_vdiff_vunion_Obj_in_Obj
  and smc_prod_vunion_Arr_in_Arr = dg_prod_vunion_Arr_in_Arr
  and smc_prod_vdiff_vunion_Arr_in_Arr = dg_prod_vdiff_vunion_Arr_in_Arr

end

lemma smc_prod_dg_prod_is_arr: 
  "g : b \<mapsto>\<^bsub>\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i\<^esub> c \<longleftrightarrow> g : b \<mapsto>\<^bsub>\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i\<^esub> c"
  unfolding is_arr_def smc_prod_def dg_prod_def dg_field_simps
  by (simp add: nat_omega_simps)

lemma smc_prod_composable_arrs_dg_prod:
  "composable_arrs (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i) = composable_arrs (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)"
  unfolding composable_arrs_def smc_prod_dg_prod_is_arr by simp



subsection\<open>Local assumptions for a product semicategory\<close>

locale psemicategory_base = \<Z> \<alpha> for \<alpha> I \<AA> +
  assumes psmc_semicategories[smc_prod_cs_intros]: 
    "i \<in>\<^sub>\<circ> I \<Longrightarrow> semicategory \<alpha> (\<AA> i)"
    and psmc_index_in_Vset[smc_cs_intros]: "I \<in>\<^sub>\<circ> Vset \<alpha>"


text\<open>Rules.\<close>

lemma (in psemicategory_base) psemicategory_base_axioms'[smc_prod_cs_intros]: 
  assumes "\<alpha>' = \<alpha>" and "I' = I"
  shows "psemicategory_base \<alpha>' I' \<AA>"
  unfolding assms by (rule psemicategory_base_axioms)

mk_ide rf psemicategory_base_def[unfolded psemicategory_base_axioms_def]
  |intro psemicategory_baseI|
  |dest psemicategory_baseD[dest]|
  |elim psemicategory_baseE[elim]|

lemma psemicategory_base_pdigraph_baseI:
  assumes "pdigraph_base \<alpha> I (\<lambda>i. smc_dg (\<AA> i))" 
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> semicategory \<alpha> (\<AA> i)"
  shows "psemicategory_base \<alpha> I \<AA>"
proof-
  interpret pdigraph_base \<alpha> I \<open>\<lambda>i. smc_dg (\<AA> i)\<close>
    rewrites "smc_dg \<CC>'\<lparr>Obj\<rparr> = \<CC>'\<lparr>Obj\<rparr>" and "smc_dg \<CC>'\<lparr>Arr\<rparr> = \<CC>'\<lparr>Arr\<rparr>" for \<CC>'
    by (rule assms(1)) (simp_all add: slicing_simps)
  show ?thesis
    by (intro psemicategory_baseI)
      (auto simp: assms(2) pdg_index_in_Vset pdg_Obj_in_Vset pdg_Arr_in_Vset) 
qed


text\<open>Product semicategory is a product digraph.\<close>

context psemicategory_base
begin

lemma psmc_pdigraph_base: "pdigraph_base \<alpha> I (\<lambda>i. smc_dg (\<AA> i))"
proof(intro pdigraph_baseI)
  show "digraph \<alpha> (smc_dg (\<AA> i))" if "i \<in>\<^sub>\<circ> I" for i 
    using that by (cs_concl cs_intro: slicing_intros smc_prod_cs_intros)
  show "I \<in>\<^sub>\<circ> Vset \<alpha>" by (cs_concl cs_intro: smc_cs_intros)
qed auto

interpretation pdg: pdigraph_base \<alpha> I \<open>\<lambda>i. smc_dg (\<AA> i)\<close> 
  by (rule psmc_pdigraph_base)

lemmas_with [unfolded slicing_simps slicing_commute]: 
  psmc_Obj_in_Vset = pdg.pdg_Obj_in_Vset
  and psmc_Arr_in_Vset = pdg.pdg_Arr_in_Vset
  and psmc_smc_prod_Obj_in_Vset = pdg.pdg_dg_prod_Obj_in_Vset
  and psmc_smc_prod_Arr_in_Vset = pdg.pdg_dg_prod_Arr_in_Vset
  and smc_prod_Dom_app_in_Obj[smc_cs_intros] = pdg.dg_prod_Dom_app_in_Obj
  and smc_prod_Cod_app_in_Obj[smc_cs_intros] = pdg.dg_prod_Cod_app_in_Obj
  and smc_prod_is_arrI = pdg.dg_prod_is_arrI
  and smc_prod_is_arrD[dest] = pdg.dg_prod_is_arrD
  and smc_prod_is_arrE[elim] = pdg.dg_prod_is_arrE

end

lemmas [smc_cs_intros] = psemicategory_base.smc_prod_is_arrD(7)


text\<open>Elementary properties.\<close>

lemma (in psemicategory_base) psmc_vsubset_index_psemicategory_base:
  assumes "J \<subseteq>\<^sub>\<circ> I"
  shows "psemicategory_base \<alpha> J \<AA>"
proof(intro psemicategory_baseI)
  show "semicategory \<alpha> (\<AA> i)" if "i \<in>\<^sub>\<circ> J" for i 
    using that assms by (auto intro: smc_prod_cs_intros)
  from assms show "J \<in>\<^sub>\<circ> Vset \<alpha>" by (simp add: vsubset_in_VsetI smc_cs_intros)
qed auto


subsubsection\<open>Composition\<close>

lemma smc_prod_Comp:
  "(\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Comp\<rparr> = 
    (
      \<lambda>gf\<in>\<^sub>\<circ>composable_arrs (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i). 
        (\<lambda>i\<in>\<^sub>\<circ>I. gf\<lparr>0\<rparr>\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<AA> i\<^esub> gf\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>i\<rparr>)
    )"
  unfolding smc_prod_components smc_prod_composable_arrs_dg_prod by simp

lemma smc_prod_Comp_vdomain[smc_cs_simps]: 
  "\<D>\<^sub>\<circ> ((\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Comp\<rparr>) = composable_arrs (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)" 
  unfolding smc_prod_Comp by simp

lemma smc_prod_Comp_app: 
  assumes "g : b \<mapsto>\<^bsub>\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i\<^esub> c" and "f : a \<mapsto>\<^bsub>\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i\<^esub> b"
  shows "g \<circ>\<^sub>A\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<^esub> f = (\<lambda>i\<in>\<^sub>\<circ>I. g\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<AA> i\<^esub> f\<lparr>i\<rparr>)" 
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> composable_arrs (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)" 
    by (auto intro: smc_cs_intros)  
  then show ?thesis unfolding smc_prod_Comp by (auto simp: nat_omega_simps)
qed

lemma smc_prod_Comp_app_component[smc_cs_simps]: 
  assumes "g : b \<mapsto>\<^bsub>\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i\<^esub> c" 
    and "f : a \<mapsto>\<^bsub>\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i\<^esub> b"
    and "i \<in>\<^sub>\<circ> I"
  shows "(g \<circ>\<^sub>A\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<^esub> f)\<lparr>i\<rparr> = g\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<AA> i\<^esub> f\<lparr>i\<rparr>"
  using assms(3) unfolding smc_prod_Comp_app[OF assms(1,2)] by simp

lemma (in psemicategory_base) smc_prod_Comp_vrange: 
  "\<R>\<^sub>\<circ> ((\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Comp\<rparr>) \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>" 
proof(intro vsubsetI)
  fix h assume prems: "h \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> ((\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Comp\<rparr>)"
  then obtain gf 
    where h_def: "h = (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Comp\<rparr>\<lparr>gf\<rparr>" 
      and "gf \<in>\<^sub>\<circ> composable_arrs (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)"
    by (auto simp: smc_prod_Comp intro: smc_cs_intros)
  then obtain g f a b c 
    where gf_def: "gf = [g, f]\<^sub>\<circ>" 
      and g: "g : b \<mapsto>\<^bsub>\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i\<^esub> c" 
      and f: "f : a \<mapsto>\<^bsub>\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i\<^esub> b"
    by clarsimp
  from g f have gf_comp: "g \<circ>\<^sub>A\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<^esub> f = (\<lambda>i\<in>\<^sub>\<circ>I. g\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<AA> i\<^esub> f\<lparr>i\<rparr>)"
    by (rule smc_prod_Comp_app)
  show "h \<in>\<^sub>\<circ> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
    unfolding smc_prod_components
    unfolding h_def gf_def gf_comp
  proof(rule VLambda_in_vproduct)
    fix i assume prems: "i \<in>\<^sub>\<circ> I"
    interpret semicategory \<alpha> \<open>\<AA> i\<close> 
      using prems by (simp add: smc_prod_cs_intros)
    from prems smc_prod_is_arrD(7)[OF g] smc_prod_is_arrD(7)[OF f] have
      "g\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<AA> i\<^esub> f\<lparr>i\<rparr> : a\<lparr>i\<rparr> \<mapsto>\<^bsub>\<AA> i\<^esub> c\<lparr>i\<rparr>" 
      by (auto intro: smc_cs_intros)
    then show "g\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<AA> i\<^esub> f\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Arr\<rparr>" by (simp add: smc_cs_intros)
  qed
qed

lemma smc_prod_Comp_app_vdomain[smc_cs_simps]:
  assumes "g : b \<mapsto>\<^bsub>\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i\<^esub> c" and "f : a \<mapsto>\<^bsub>\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i\<^esub> b"
  shows "\<D>\<^sub>\<circ> (g \<circ>\<^sub>A\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<^esub> f) = I" 
  unfolding smc_prod_Comp_app[OF assms] by simp


subsubsection\<open>A product \<open>\<alpha>\<close>-semicategory is a tiny \<open>\<beta>\<close>-semicategory\<close>

lemma (in psemicategory_base) psmc_tiny_semicategory_smc_prod:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
  shows "tiny_semicategory \<beta> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)"
proof(intro tiny_semicategoryI, (unfold slicing_simps)?)

  show "tiny_digraph \<beta> (smc_dg (smc_prod I \<AA>))"
    unfolding slicing_commute[symmetric]
    by 
      (
        intro pdigraph_base.pdg_tiny_digraph_dg_prod; 
        (rule assms psmc_pdigraph_base)?
      )

  show "vfsequence (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)" unfolding smc_prod_def by auto
  show "vcard (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i) = 5\<^sub>\<nat>"
    unfolding smc_prod_def by (simp add: nat_omega_simps)
  show "vsv ((\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Comp\<rparr>)" unfolding smc_prod_Comp by simp
  
  show
    "(gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Comp\<rparr>)) \<longleftrightarrow>
      (
        \<exists>g f b c a. 
          gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>smc_prod I \<AA>\<^esub> c \<and> f : a \<mapsto>\<^bsub>smc_prod I \<AA>\<^esub> b
      )"
    for gf
    by (auto intro: smc_cs_intros simp: smc_cs_simps)
  
  show Comp_is_arr[intro]: "g \<circ>\<^sub>A\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<^esub> f : a \<mapsto>\<^bsub>\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i\<^esub> c"
    if "g : b \<mapsto>\<^bsub>\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i\<^esub> c" and "f : a \<mapsto>\<^bsub>\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i\<^esub> b" 
    for g b c f a
  proof(intro smc_prod_is_arrI)
    from that show "vsv (g \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> f)" 
      by (auto simp: smc_prod_Comp_app)
    from that show "\<D>\<^sub>\<circ> (g \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> f) = I"
      by (auto simp: smc_prod_Comp_app)
    from that(2) have f: "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
      by (elim is_arrE) (auto simp: smc_prod_components)
    from that(1) have g: "g \<in>\<^sub>\<circ> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
      by (elim is_arrE) (auto simp: smc_prod_components)
    from f have a: "a \<in>\<^sub>\<circ> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"
      by (rule smc_prod_Dom_app_in_Obj[of f, unfolded is_arrD(2)[OF that(2)]])
    then show "vsv a" by (auto simp: smc_prod_components)
    from a show "\<D>\<^sub>\<circ> a = I" by (auto simp: smc_prod_components)
    from g have c: "c \<in>\<^sub>\<circ> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"
      by (rule smc_prod_Cod_app_in_Obj[of g, unfolded is_arrD(3)[OF that(1)]])
    then show "vsv c" by (auto simp: smc_prod_components)
    from c show "\<D>\<^sub>\<circ> c = I" by (auto simp: smc_prod_components)
    fix i assume prems: "i \<in>\<^sub>\<circ> I"
    interpret semicategory \<alpha> \<open>\<AA> i\<close> 
      using prems by (auto intro: smc_prod_cs_intros)
    from 
      prems 
      smc_prod_is_arrD(7)[OF that(1) prems] 
      smc_prod_is_arrD(7)[OF that(2) prems] 
    show "(g \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> f)\<lparr>i\<rparr> : a\<lparr>i\<rparr> \<mapsto>\<^bsub>\<AA> i\<^esub> c\<lparr>i\<rparr>"
      unfolding smc_prod_Comp_app[OF that] by (auto intro: smc_cs_intros)
  qed
  
  show 
    "h \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> g \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> f =
      h \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> (g \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> f)"
    if "h : c \<mapsto>\<^bsub>smc_prod I \<AA>\<^esub> d"
      and "g : b \<mapsto>\<^bsub>smc_prod I \<AA>\<^esub> c"
      and "f : a \<mapsto>\<^bsub>smc_prod I \<AA>\<^esub> b"
    for h c d g b f a
  proof(rule smc_prod_Arr_cong)
    show "(h \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> g) \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> f \<in>\<^sub>\<circ> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
      by (meson that Comp_is_arr is_arrD)
    show "h \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> (g \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> f) \<in>\<^sub>\<circ> smc_prod I \<AA>\<lparr>Arr\<rparr>"
      by (meson that Comp_is_arr is_arrD)
    fix i assume prems: "i \<in>\<^sub>\<circ> I"
    then interpret semicategory \<alpha> \<open>\<AA> i\<close> by (simp add: smc_prod_cs_intros)
    from prems that have "h\<lparr>i\<rparr> : c\<lparr>i\<rparr> \<mapsto>\<^bsub>\<AA> i\<^esub> d\<lparr>i\<rparr>"
      and "g\<lparr>i\<rparr> : b\<lparr>i\<rparr> \<mapsto>\<^bsub>\<AA> i\<^esub> c\<lparr>i\<rparr>"
      and "f\<lparr>i\<rparr> : a\<lparr>i\<rparr> \<mapsto>\<^bsub>\<AA> i\<^esub> b\<lparr>i\<rparr>"
      and "h \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> g : b \<mapsto>\<^bsub>smc_prod I \<AA>\<^esub> d"
      and "g \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> f : a \<mapsto>\<^bsub>smc_prod I \<AA>\<^esub> c"
      by (auto simp: smc_prod_is_arrD)
    with prems that show 
      "(h \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> g \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> f)\<lparr>i\<rparr> =
        (h \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> (g \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> f))\<lparr>i\<rparr>"
      by (simp add: smc_prod_Comp_app_component smc_Comp_assoc)
  qed

qed (intro assms)



subsection\<open>Further local assumptions for product semicategories\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale psemicategory = psemicategory_base \<alpha> I \<AA> for \<alpha> I \<AA> +
  assumes psmc_Obj_vsubset_Vset: 
    "J \<subseteq>\<^sub>\<circ> I \<Longrightarrow> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>J. \<AA> i)\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    and psmc_Hom_vifunion_in_Vset: 
      "\<lbrakk>
        J \<subseteq>\<^sub>\<circ> I;
        A \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>J. \<AA> i)\<lparr>Obj\<rparr>;
        B \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>J. \<AA> i)\<lparr>Obj\<rparr>;
        A \<in>\<^sub>\<circ> Vset \<alpha>;
        B \<in>\<^sub>\<circ> Vset \<alpha>
      \<rbrakk> \<Longrightarrow> (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>J. \<AA> i) a b) \<in>\<^sub>\<circ> Vset \<alpha>"


text\<open>Rules.\<close>

lemma (in psemicategory) psemicategory_axioms'[smc_prod_cs_intros]: 
  assumes "\<alpha>' = \<alpha>" and "I' = I"
  shows "psemicategory \<alpha>' I' \<AA>"
  unfolding assms by (rule psemicategory_axioms)

mk_ide rf psemicategory_def[unfolded psemicategory_axioms_def]
  |intro psemicategoryI|
  |dest psemicategoryD[dest]|
  |elim psemicategoryE[elim]|

lemmas [smc_prod_cs_intros] = psemicategoryD(1)

lemma psemicategory_pdigraphI:
  assumes "pdigraph \<alpha> I (\<lambda>i. smc_dg (\<AA> i))" 
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> semicategory \<alpha> (\<AA> i)"
  shows "psemicategory \<alpha> I \<AA>"
proof-
  interpret pdigraph \<alpha> I \<open>\<lambda>i. smc_dg (\<AA> i)\<close> by (rule assms(1))
  note [unfolded slicing_simps slicing_commute, smc_cs_intros] = 
    pdg_Obj_vsubset_Vset
    pdg_Hom_vifunion_in_Vset
  show ?thesis
    by (intro psemicategoryI psemicategory_base_pdigraph_baseI)
      (auto simp: assms(2) dg_prod_cs_intros intro!: smc_cs_intros) 
qed


text\<open>Product semicategory is a product digraph.\<close>

context psemicategory
begin

lemma psmc_pdigraph: "pdigraph \<alpha> I (\<lambda>i. smc_dg (\<AA> i))"
proof(intro pdigraphI, unfold slicing_simps slicing_commute)
  show "pdigraph_base \<alpha> I (\<lambda>i. smc_dg (\<AA> i))" by (rule psmc_pdigraph_base)
qed (auto intro!: psmc_Obj_vsubset_Vset psmc_Hom_vifunion_in_Vset)

interpretation pdg: pdigraph \<alpha> I \<open>\<lambda>i. smc_dg (\<AA> i)\<close> by (rule psmc_pdigraph)

lemmas_with [unfolded slicing_simps slicing_commute]: 
  psmc_Obj_vsubset_Vset' = pdg.pdg_Obj_vsubset_Vset'
  and psmc_Hom_vifunion_in_Vset' = pdg.pdg_Hom_vifunion_in_Vset'
  and psmc_smc_prod_vunion_is_arr = pdg.pdg_dg_prod_vunion_is_arr
  and psmc_smc_prod_vdiff_vunion_is_arr = pdg.pdg_dg_prod_vdiff_vunion_is_arr

end


text\<open>Elementary properties.\<close>

lemma (in psemicategory) psmc_vsubset_index_psemicategory:
  assumes "J \<subseteq>\<^sub>\<circ> I"
  shows "psemicategory \<alpha> J \<AA>"
proof(intro psemicategoryI psemicategory_pdigraphI)
  show "smc_prod J' \<AA>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>" if \<open>J' \<subseteq>\<^sub>\<circ> J\<close> for J'
  proof-
    from that assms have "J' \<subseteq>\<^sub>\<circ> I" by simp
    then show "smc_prod J' \<AA>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>" by (rule psmc_Obj_vsubset_Vset)
  qed
  fix A B J' assume prems:
    "J' \<subseteq>\<^sub>\<circ> J"
    "A \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>J'. \<AA> i)\<lparr>Obj\<rparr>"
    "B \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>J'. \<AA> i)\<lparr>Obj\<rparr>"
    "A \<in>\<^sub>\<circ> Vset \<alpha>" 
    "B \<in>\<^sub>\<circ> Vset \<alpha>"
  show "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>J'. \<AA> i) a b) \<in>\<^sub>\<circ> Vset \<alpha>"
  proof-
    from prems(1) assms have "J' \<subseteq>\<^sub>\<circ> I" by simp
    from psmc_Hom_vifunion_in_Vset[OF this prems(2-5)] show ?thesis.
  qed
qed (rule psmc_vsubset_index_psemicategory_base[OF assms])


subsubsection\<open>A product \<open>\<alpha>\<close>-semicategory is an \<open>\<alpha>\<close>-semicategory\<close>

lemma (in psemicategory) psmc_semicategory_smc_prod: 
  "semicategory \<alpha> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)"
proof-
  interpret tiny_semicategory \<open>\<alpha> + \<omega>\<close> \<open>\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i\<close>
    by (intro psmc_tiny_semicategory_smc_prod) 
      (auto simp: \<Z>_\<alpha>_\<alpha>\<omega> \<Z>.intro \<Z>_Limit_\<alpha>\<omega> \<Z>_\<omega>_\<alpha>\<omega>)
  show ?thesis
    by (rule semicategory_if_semicategory)  
      (
        auto 
          intro!: psmc_Hom_vifunion_in_Vset psmc_Obj_vsubset_Vset
          intro: smc_cs_intros
      )
qed



subsection\<open>Local assumptions for a finite product semicategory\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale finite_psemicategory = psemicategory_base \<alpha> I \<AA> for \<alpha> I \<AA> +
  assumes fin_psmc_index_vfinite: "vfinite I"


text\<open>Rules.\<close>

lemma (in finite_psemicategory) finite_psemicategory_axioms[smc_prod_cs_intros]: 
  assumes "\<alpha>' = \<alpha>" and "I' = I"
  shows "finite_psemicategory \<alpha>' I' \<AA>"
  unfolding assms by (rule finite_psemicategory_axioms)

mk_ide rf finite_psemicategory_def[unfolded finite_psemicategory_axioms_def]
  |intro finite_psemicategoryI|
  |dest finite_psemicategoryD[dest]|
  |elim finite_psemicategoryE[elim]|

lemmas [smc_prod_cs_intros] = finite_psemicategoryD(1)

lemma finite_psemicategory_finite_pdigraphI:
  assumes "finite_pdigraph \<alpha> I (\<lambda>i. smc_dg (\<AA> i))" 
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> semicategory \<alpha> (\<AA> i)"
  shows "finite_psemicategory \<alpha> I \<AA>"
proof-
  interpret finite_pdigraph \<alpha> I \<open>\<lambda>i. smc_dg (\<AA> i)\<close> by (rule assms(1))
  show ?thesis
    by 
      (
        intro 
          assms
          finite_psemicategoryI 
          psemicategory_base_pdigraph_baseI 
          finite_pdigraphD(1)[OF assms(1)]
          fin_pdg_index_vfinite
      )
qed


subsubsection\<open>
Local assumptions for a finite product semicategory and local
assumptions for an arbitrary product semicategory
\<close>

sublocale finite_psemicategory \<subseteq> psemicategory \<alpha> I \<AA>
proof-
  interpret finite_pdigraph \<alpha> I \<open>\<lambda>i. smc_dg (\<AA> i)\<close>
  proof(intro finite_pdigraphI pdigraph_baseI)
    fix i assume i: "i \<in>\<^sub>\<circ> I"
    interpret \<AA>i: semicategory \<alpha> \<open>\<AA> i\<close> by (simp add: i psmc_semicategories)
    show "digraph \<alpha> (smc_dg (\<AA> i))" by (simp add: \<AA>i.smc_digraph)
  qed (auto intro!: smc_cs_intros fin_psmc_index_vfinite)
  show "psemicategory \<alpha> I \<AA>"
    by (intro psemicategory_pdigraphI) 
      (simp_all add: psmc_semicategories pdigraph_axioms)
qed



subsection\<open>Binary union and complement\<close>

lemma (in psemicategory) psmc_smc_prod_vunion_Comp:
  assumes "vdisjnt J K"
    and "J \<subseteq>\<^sub>\<circ> I"
    and "K \<subseteq>\<^sub>\<circ> I"
    and "g : b \<mapsto>\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Cj\<in>\<^sub>\<circ>J. \<AA> j)\<^esub> c"
    and "g' : b' \<mapsto>\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Ck\<in>\<^sub>\<circ>K. \<AA> k)\<^esub> c'"
    and "f : a \<mapsto>\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Cj\<in>\<^sub>\<circ>J. \<AA> j)\<^esub> b"
    and "f' : a' \<mapsto>\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Ck\<in>\<^sub>\<circ>K. \<AA> k)\<^esub> b'"
  shows "(g \<circ>\<^sub>A\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Cj\<in>\<^sub>\<circ>J. \<AA> j)\<^esub> f) \<union>\<^sub>\<circ> (g' \<circ>\<^sub>A\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Cj\<in>\<^sub>\<circ>K. \<AA> j)\<^esub> f') = 
    g \<union>\<^sub>\<circ> g' \<circ>\<^sub>A\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Cj\<in>\<^sub>\<circ>J \<union>\<^sub>\<circ> K. \<AA> j)\<^esub> f \<union>\<^sub>\<circ> f'"
proof-

  interpret J\<AA>: psemicategory \<alpha> J \<AA> 
    using assms(2) by (simp add: psmc_vsubset_index_psemicategory)
  interpret K\<AA>: psemicategory \<alpha> K \<AA> 
    using assms(3) by (simp add: psmc_vsubset_index_psemicategory)
  interpret JK\<AA>: psemicategory \<alpha> \<open>J \<union>\<^sub>\<circ> K\<close> \<AA> 
    using assms(2,3) by (simp add: psmc_vsubset_index_psemicategory)

  interpret J\<AA>': semicategory \<alpha> \<open>smc_prod J \<AA>\<close> 
    by (rule J\<AA>.psmc_semicategory_smc_prod)
  interpret K\<AA>': semicategory \<alpha> \<open>smc_prod K \<AA>\<close> 
    by (rule K\<AA>.psmc_semicategory_smc_prod)
  interpret JK\<AA>': semicategory \<alpha> \<open>smc_prod (J \<union>\<^sub>\<circ> K) \<AA>\<close> 
    by (rule JK\<AA>.psmc_semicategory_smc_prod)

  note gg' = psmc_smc_prod_vunion_is_arr[OF assms(1-3,4,5)]
    and ff' = psmc_smc_prod_vunion_is_arr[OF assms(1-3,6,7)]

  note gD = J\<AA>.smc_prod_is_arrD[OF assms(4)]
    and g'D = K\<AA>.smc_prod_is_arrD[OF assms(5)]
    and fD = J\<AA>.smc_prod_is_arrD[OF assms(6)]
    and f'D = K\<AA>.smc_prod_is_arrD[OF assms(7)]

  from assms(4,6) have gf: 
    "g \<circ>\<^sub>A\<^bsub>smc_prod J \<AA>\<^esub> f : a \<mapsto>\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Cj\<in>\<^sub>\<circ>J. \<AA> j)\<^esub> c" 
    by (auto intro: smc_cs_intros)
  from assms(5,7) have g'f': 
    "g' \<circ>\<^sub>A\<^bsub>smc_prod K \<AA>\<^esub> f' : a' \<mapsto>\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Ck\<in>\<^sub>\<circ>K. \<AA> k)\<^esub> c'"
    by (auto intro: smc_cs_intros)
  from gf have "g \<circ>\<^sub>A\<^bsub>smc_prod J \<AA>\<^esub> f \<in>\<^sub>\<circ> smc_prod J \<AA>\<lparr>Arr\<rparr>" by auto
  from g'f' have "g' \<circ>\<^sub>A\<^bsub>smc_prod K \<AA>\<^esub> f' \<in>\<^sub>\<circ> smc_prod K \<AA>\<lparr>Arr\<rparr>" by auto
  from gg' ff' have gg'_ff': 
    "g \<union>\<^sub>\<circ> g' \<circ>\<^sub>A\<^bsub>smc_prod (J \<union>\<^sub>\<circ> K) \<AA>\<^esub> f \<union>\<^sub>\<circ> f' :
      a \<union>\<^sub>\<circ> a' \<mapsto>\<^bsub>smc_prod (J \<union>\<^sub>\<circ> K) \<AA>\<^esub> c \<union>\<^sub>\<circ> c'"
    by (simp add: smc_cs_intros)

  show ?thesis
  proof(rule smc_prod_Arr_cong[of _ \<open>J \<union>\<^sub>\<circ> K\<close> \<AA>])
    from gf g'f' assms(1) show 
      "(g \<circ>\<^sub>A\<^bsub>smc_prod J \<AA>\<^esub> f) \<union>\<^sub>\<circ> (g' \<circ>\<^sub>A\<^bsub>smc_prod K \<AA>\<^esub> f') \<in>\<^sub>\<circ> 
        smc_prod (J \<union>\<^sub>\<circ> K) \<AA>\<lparr>Arr\<rparr>"
      by (auto intro: smc_prod_vunion_Arr_in_Arr)
    from gg'_ff' show 
      "g \<union>\<^sub>\<circ> g' \<circ>\<^sub>A\<^bsub>smc_prod (J \<union>\<^sub>\<circ> K) \<AA>\<^esub> f \<union>\<^sub>\<circ> f' \<in>\<^sub>\<circ> smc_prod (J \<union>\<^sub>\<circ> K) \<AA>\<lparr>Arr\<rparr>"
      by auto
    fix i assume prems: "i \<in>\<^sub>\<circ> J \<union>\<^sub>\<circ> K"
    then consider (iJ) \<open>i \<in>\<^sub>\<circ> J\<close> | (iK) \<open>i \<in>\<^sub>\<circ> K\<close> by auto
    then show 
      "((g \<circ>\<^sub>A\<^bsub>smc_prod J \<AA>\<^esub> f) \<union>\<^sub>\<circ> (g' \<circ>\<^sub>A\<^bsub>smc_prod K \<AA>\<^esub> f'))\<lparr>i\<rparr> =
        (g \<union>\<^sub>\<circ> g' \<circ>\<^sub>A\<^bsub>smc_prod (J \<union>\<^sub>\<circ> K) \<AA>\<^esub> f \<union>\<^sub>\<circ> f')\<lparr>i\<rparr>"
    proof cases
      case iJ
      have [simp]:
        "((g \<circ>\<^sub>A\<^bsub>smc_prod J \<AA>\<^esub> f) \<union>\<^sub>\<circ> (g' \<circ>\<^sub>A\<^bsub>smc_prod K \<AA>\<^esub> f'))\<lparr>i\<rparr> = 
          g\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<AA> i\<^esub> f\<lparr>i\<rparr>"
      proof
        (
          fold smc_prod_Comp_app_component[OF assms(4,6) iJ], 
          rule vsv_vunion_app_left
        )
        from gf show "vsv (g \<circ>\<^sub>A\<^bsub>smc_prod J \<AA>\<^esub> f)" by auto
        from g'f' show "vsv (g' \<circ>\<^sub>A\<^bsub>smc_prod K \<AA>\<^esub> f')" by auto
      qed 
        (
          use assms(4-7) in 
            \<open>simp_all add: iJ assms(1) smc_prod_Comp_app_vdomain\<close>
        )
      have gg'_i: "(g \<union>\<^sub>\<circ> g')\<lparr>i\<rparr> = g\<lparr>i\<rparr>" 
        by (simp add: iJ assms(1) gD(1,2) g'D(1,2))
      have ff'_i: "(f \<union>\<^sub>\<circ> f')\<lparr>i\<rparr> = f\<lparr>i\<rparr>" 
        by (simp add: iJ assms(1) fD(1,2) f'D(1,2))
      have [simp]: 
        "(g \<union>\<^sub>\<circ> g' \<circ>\<^sub>A\<^bsub>smc_prod (J \<union>\<^sub>\<circ> K) \<AA>\<^esub> f \<union>\<^sub>\<circ> f')\<lparr>i\<rparr> = g\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<AA> i\<^esub> f\<lparr>i\<rparr>" 
        by (fold gg'_i ff'_i) 
          (rule smc_prod_Comp_app_component[OF gg' ff' prems])
      show ?thesis by simp
    next
      case iK
      have [simp]:
        "((g \<circ>\<^sub>A\<^bsub>smc_prod J \<AA>\<^esub> f) \<union>\<^sub>\<circ> (g' \<circ>\<^sub>A\<^bsub>smc_prod K \<AA>\<^esub> f'))\<lparr>i\<rparr> = 
          g'\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<AA> i\<^esub> f'\<lparr>i\<rparr>"
      proof
        (
          fold smc_prod_Comp_app_component[OF assms(5,7) iK], 
          rule vsv_vunion_app_right
        )
        from gf show "vsv (g \<circ>\<^sub>A\<^bsub>smc_prod J \<AA>\<^esub> f)" by auto
        from g'f' show "vsv (g' \<circ>\<^sub>A\<^bsub>smc_prod K \<AA>\<^esub> f')" by auto
      qed 
        (
          use assms(4-7) in 
            \<open>simp_all add: iK smc_prod_Comp_app_vdomain assms(1)\<close>
        )
      have gg'_i: "(g \<union>\<^sub>\<circ> g')\<lparr>i\<rparr> = g'\<lparr>i\<rparr>" 
        by (simp add: iK assms(1) gD(1,2) g'D(1,2))
      have ff'_i: "(f \<union>\<^sub>\<circ> f')\<lparr>i\<rparr> = f'\<lparr>i\<rparr>" 
        by (simp add: iK assms(1) fD(1,2) f'D(1,2))
      have [simp]:
        "(g \<union>\<^sub>\<circ> g' \<circ>\<^sub>A\<^bsub>smc_prod (J \<union>\<^sub>\<circ> K) \<AA>\<^esub> f \<union>\<^sub>\<circ> f')\<lparr>i\<rparr> = g'\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<AA> i\<^esub> f'\<lparr>i\<rparr>" 
        by (fold gg'_i ff'_i)
          (rule smc_prod_Comp_app_component[OF gg' ff' prems])
      show ?thesis by simp
    qed
  qed

qed

lemma (in psemicategory) psmc_smc_prod_vdiff_vunion_Comp:
  assumes "J \<subseteq>\<^sub>\<circ> I"   
    and "g : b \<mapsto>\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Cj\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> j)\<^esub> c"
    and "g' : b' \<mapsto>\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Ck\<in>\<^sub>\<circ>J. \<AA> k)\<^esub> c'"
    and "f : a \<mapsto>\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Cj\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> j)\<^esub> b"
    and "f' : a' \<mapsto>\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Ck\<in>\<^sub>\<circ>J. \<AA> k)\<^esub> b'"
  shows "(g \<circ>\<^sub>A\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Cj\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> j)\<^esub> f) \<union>\<^sub>\<circ> (g' \<circ>\<^sub>A\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Cj\<in>\<^sub>\<circ>J. \<AA> j)\<^esub> f') = 
    g \<union>\<^sub>\<circ> g' \<circ>\<^sub>A\<^bsub>(\<Prod>\<^sub>S\<^sub>M\<^sub>Cj\<in>\<^sub>\<circ>I. \<AA> j)\<^esub> f \<union>\<^sub>\<circ> f'"
  by 
    (
      vdiff_of_vunion' 
        rule: psmc_smc_prod_vunion_Comp assms: assms(2-5) subset: assms(1)
    )



subsection\<open>Projection\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter II-3 in \cite{mac_lane_categories_2010}.\<close>

definition smcf_proj :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> V" (\<open>\<pi>\<^sub>S\<^sub>M\<^sub>C\<close>)
  where "\<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i =
    [
      (\<lambda>a\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Obj\<rparr>). a\<lparr>i\<rparr>),
      (\<lambda>f\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>). f\<lparr>i\<rparr>),
      (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i),
      \<AA> i
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smcf_proj_components:
  shows "(\<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i)\<lparr>ObjMap\<rparr> = (\<lambda>a\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Obj\<rparr>). a\<lparr>i\<rparr>)"
    and "(\<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i)\<lparr>ArrMap\<rparr> = (\<lambda>f\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>). f\<lparr>i\<rparr>)"
    and "(\<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i)\<lparr>HomDom\<rparr> = (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)"
    and "(\<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i)\<lparr>HomCod\<rparr> = \<AA> i"
  unfolding smcf_proj_def dghm_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing\<close>

lemma smcf_dghm_smcf_proj[slicing_commute]: 
  "\<pi>\<^sub>D\<^sub>G I (\<lambda>i. smc_dg (\<AA> i)) i = smcf_dghm (\<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i)"
  unfolding 
    smc_dg_def 
    smcf_dghm_def 
    smcf_proj_def 
    dghm_proj_def 
    smc_prod_def 
    dg_prod_def
    dg_field_simps 
    dghm_field_simps 
  by (simp add: nat_omega_simps)

context psemicategory
begin

interpretation pdg: pdigraph \<alpha> I \<open>\<lambda>i. smc_dg (\<AA> i)\<close> by (rule psmc_pdigraph)

lemmas_with [unfolded slicing_simps slicing_commute]: 
  smcf_proj_is_dghm = pdg.pdg_dghm_proj_is_dghm

end


subsubsection\<open>Projection semifunctor is a semifunctor\<close>

lemma (in psemicategory) psmc_smcf_proj_is_semifunctor: 
  assumes "i \<in>\<^sub>\<circ> I"
  shows "\<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i : (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i) \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> i"
proof(intro is_semifunctorI)
  show "vfsequence (\<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i)"
    unfolding smcf_proj_def by (simp add: nat_omega_simps)
  show "vcard (\<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i) = 4\<^sub>\<nat>"
    unfolding smcf_proj_def by (simp add: nat_omega_simps)
  interpret \<AA>: semicategory \<alpha> \<open>smc_prod I \<AA>\<close> 
    by (rule psmc_semicategory_smc_prod)
  interpret \<AA>i: semicategory \<alpha> \<open>\<AA> i\<close> 
    using assms by (simp add: smc_prod_cs_intros)
  show "\<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> f\<rparr> =
    \<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<AA> i\<^esub> \<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
    if "g : b \<mapsto>\<^bsub>smc_prod I \<AA>\<^esub> c" and "f : a \<mapsto>\<^bsub>smc_prod I \<AA>\<^esub> b" for g b c f a
  proof-
    from that have "g \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> f : a \<mapsto>\<^bsub>smc_prod I \<AA>\<^esub> c" 
      by (auto simp: smc_cs_intros)
    then have "g \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>)"
      unfolding smc_prod_components[symmetric] by auto
    then have \<pi>_gf: "\<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> f\<rparr> = g\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<AA> i\<^esub> f\<lparr>i\<rparr>"
      unfolding smcf_proj_components 
      by (simp add: smc_prod_Comp_app_component[OF that assms])
    from that(1) have g: "g \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>)" 
      unfolding smc_prod_components[symmetric] by auto
    from that(2) have f: "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>)" 
      unfolding smc_prod_components[symmetric] by auto
    from g f have \<pi>g_\<pi>f: 
      "\<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<AA> i\<^esub> \<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> = g\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>\<AA> i\<^esub> f\<lparr>i\<rparr>"
      unfolding smcf_proj_components by simp
    from \<pi>_gf \<pi>g_\<pi>f show ?thesis by simp
  qed
qed 
  (
    auto simp:
      smc_prod_cs_intros
      assms
      smcf_proj_components
      psmc_semicategory_smc_prod 
      smcf_proj_is_dghm
  )

lemma (in psemicategory) psmc_smcf_proj_is_semifunctor':
  assumes "i \<in>\<^sub>\<circ> I" and "\<CC> = (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)" and "\<DD> = \<AA> i"
  shows "\<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms(1) unfolding assms(2,3) by (rule psmc_smcf_proj_is_semifunctor)

lemmas [smc_cs_intros] = psemicategory.psmc_smcf_proj_is_semifunctor'



subsection\<open>Semicategory product universal property semifunctor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The following semifunctor is used in the 
proof of the universal property of the product semicategory 
later in this work.
\<close>

definition smcf_up :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "smcf_up I \<AA> \<CC> \<phi> =
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. (\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)),
      (\<lambda>f\<in>\<^sub>\<circ>\<CC>\<lparr>Arr\<rparr>. (\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>)),
      \<CC>,
      (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smcf_up_components: 
  shows "smcf_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr> = (\<lambda>a\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. (\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>))"
    and "smcf_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr> = (\<lambda>f\<in>\<^sub>\<circ>\<CC>\<lparr>Arr\<rparr>. (\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>))"
    and "smcf_up I \<AA> \<CC> \<phi>\<lparr>HomDom\<rparr> = \<CC>"
    and "smcf_up I \<AA> \<CC> \<phi>\<lparr>HomCod\<rparr> = (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)"
  unfolding smcf_up_def dghm_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smcf_dghm_smcf_up[slicing_commute]: 
  "dghm_up I (\<lambda>i. smc_dg (\<AA> i)) (smc_dg \<CC>) (\<lambda>i. smcf_dghm (\<phi> i)) = 
    smcf_dghm (smcf_up I \<AA> \<CC> \<phi>)"
  unfolding 
    smc_dg_def 
    smcf_dghm_def 
    smcf_up_def 
    dghm_up_def 
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
    where \<AA>=\<open>\<lambda>i. smc_dg (\<AA> i)\<close> and \<phi>=\<open>\<lambda>i. smcf_dghm (\<phi> i)\<close> and \<CC>=\<open>smc_dg \<CC>\<close>, 
    unfolded slicing_simps slicing_commute
  ]:
  smcf_up_ObjMap_vdomain[smc_cs_simps] = dghm_up_ObjMap_vdomain
  and smcf_up_ObjMap_app = dghm_up_ObjMap_app
  and smcf_up_ObjMap_app_vdomain[smc_cs_simps] = dghm_up_ObjMap_app_vdomain
  and smcf_up_ObjMap_app_component[smc_cs_simps] = dghm_up_ObjMap_app_component
  and smcf_up_ArrMap_vdomain[smc_cs_simps] = dghm_up_ArrMap_vdomain
  and smcf_up_ArrMap_app = dghm_up_ArrMap_app
  and smcf_up_ArrMap_app_vdomain[smc_cs_simps] = dghm_up_ArrMap_app_vdomain
  and smcf_up_ArrMap_app_component[smc_cs_simps] = dghm_up_ArrMap_app_component

lemma smcf_up_ObjMap_vrange:
  assumes "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> i"
  shows "\<R>\<^sub>\<circ> (smcf_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"
proof
  (
    rule dghm_up_ObjMap_vrange
      [
        where \<AA>=\<open>\<lambda>i. smc_dg (\<AA> i)\<close> 
          and \<phi>=\<open>\<lambda>i. smcf_dghm (\<phi> i)\<close> 
          and \<CC>=\<open>smc_dg \<CC>\<close>, 
        unfolded slicing_simps slicing_commute
      ]
  )
  fix i assume "i \<in>\<^sub>\<circ> I"
  then interpret is_semifunctor \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (rule assms)
  show "smcf_dghm (\<phi> i) : smc_dg \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg (\<AA> i)" 
    by (rule smcf_is_dghm)
qed

lemma smcf_up_ObjMap_app_vrange:
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> i"
  shows " \<R>\<^sub>\<circ> (smcf_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Obj\<rparr>)"
proof
  (
    rule dghm_up_ObjMap_app_vrange
      [
        where \<AA>=\<open>\<lambda>i. smc_dg (\<AA> i)\<close> 
          and \<phi>=\<open>\<lambda>i. smcf_dghm (\<phi> i)\<close> 
          and \<CC>=\<open>smc_dg \<CC>\<close>, 
        unfolded slicing_simps slicing_commute
      ]
  )
  show "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by (rule assms)
  fix i assume "i \<in>\<^sub>\<circ> I"
  then interpret is_semifunctor \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (rule assms(2))
  show "smcf_dghm (\<phi> i) : smc_dg \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg (\<AA> i)"
    by (rule smcf_is_dghm)
qed

lemma smcf_up_ArrMap_vrange:
  assumes "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> i"
  shows "\<R>\<^sub>\<circ> (smcf_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
proof
  (
    rule dghm_up_ArrMap_vrange
      [
        where \<AA>=\<open>\<lambda>i. smc_dg (\<AA> i)\<close> 
          and \<phi>=\<open>\<lambda>i. smcf_dghm (\<phi> i)\<close> 
          and \<CC>=\<open>smc_dg \<CC>\<close>, 
        unfolded slicing_simps slicing_commute
      ]
  )
  fix i assume "i \<in>\<^sub>\<circ> I"
  then interpret is_semifunctor \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (rule assms)
  show "smcf_dghm (\<phi> i) : smc_dg \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg (\<AA> i)"
    by (rule smcf_is_dghm)
qed

lemma smcf_up_ArrMap_app_vrange:
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> i"
  shows "\<R>\<^sub>\<circ> (smcf_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>) \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>)"
proof
  (
    rule dghm_up_ArrMap_app_vrange[
      where \<AA>=\<open>\<lambda>i. smc_dg (\<AA> i)\<close> 
        and \<phi>=\<open>\<lambda>i. smcf_dghm (\<phi> i)\<close> 
        and \<CC>=\<open>smc_dg \<CC>\<close>, 
      unfolded slicing_simps slicing_commute
      ]
  )
  show "a \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" by (rule assms)
  fix i assume "i \<in>\<^sub>\<circ> I"
  then interpret is_semifunctor \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (rule assms(2))
  show "smcf_dghm (\<phi> i) : smc_dg \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg (\<AA> i)"
    by (rule smcf_is_dghm)
qed

end

context psemicategory
begin

interpretation pdg: pdigraph \<alpha> I \<open>\<lambda>i. smc_dg (\<AA> i)\<close> by (rule psmc_pdigraph)

lemmas_with [unfolded slicing_simps slicing_commute]: 
  psmc_dghm_comp_dghm_proj_dghm_up = pdg.pdg_dghm_comp_dghm_proj_dghm_up
  and psmc_dghm_up_eq_dghm_proj = pdg.pdg_dghm_up_eq_dghm_proj

end


subsubsection\<open>
Semicategory product universal property semifunctor is a semifunctor
\<close>

lemma (in psemicategory) psmc_smcf_up_is_semifunctor:
  assumes "semicategory \<alpha> \<CC>" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> i"
  shows "smcf_up I \<AA> \<CC> \<phi> : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)"
proof(intro is_semifunctorI)
  interpret \<CC>: semicategory \<alpha> \<CC> by (simp add: assms(1))
  interpret \<AA>: semicategory \<alpha> \<open>smc_prod I \<AA>\<close> 
    by (rule psmc_semicategory_smc_prod)
  show "vfsequence (smcf_up I \<AA> \<CC> \<phi>)"
    unfolding smcf_up_def by simp
  show "vcard (smcf_up I \<AA> \<CC> \<phi>) = 4\<^sub>\<nat>"
    unfolding smcf_up_def by (simp add: nat_omega_simps)
  show dghm_smcf_up: 
    "smcf_dghm (smcf_up I \<AA> \<CC> \<phi>) : smc_dg \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg (smc_prod I \<AA>)"
    by 
      (
        simp add: 
          assms 
          slicing_commute[symmetric]
          psmc_pdigraph 
          is_semifunctor.smcf_is_dghm 
          pdigraph.pdg_dghm_up_is_dghm 
          semicategory.smc_digraph
      )
  interpret smcf_up:
    is_dghm \<alpha> \<open>smc_dg \<CC>\<close> \<open>smc_dg (smc_prod I \<AA>)\<close> \<open>smcf_dghm (smcf_up I \<AA> \<CC> \<phi>)\<close>
    by (rule dghm_smcf_up)
  show "smcf_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<rparr> = 
    smcf_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> smcf_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
    if "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" for g b c f a
  proof(rule smc_prod_Arr_cong[of _ I \<AA>])
    note smcf_up_f = 
        smcf_up.dghm_ArrMap_is_arr[unfolded slicing_simps, OF that(2)]
      and smcf_up_g = 
        smcf_up.dghm_ArrMap_is_arr[unfolded slicing_simps, OF that(1)]
    from that have gf: "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c" 
      by (simp add: smc_cs_intros)
    from smcf_up.dghm_ArrMap_is_arr[unfolded slicing_simps, OF this] show
      "smcf_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<rparr> \<in>\<^sub>\<circ> smc_prod I \<AA>\<lparr>Arr\<rparr>" 
      by (simp add: smc_cs_intros)
    from smcf_up_g smcf_up_f show 
      "smcf_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> smcf_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> \<in>\<^sub>\<circ> 
        smc_prod I \<AA>\<lparr>Arr\<rparr>"
      by (meson \<AA>.smc_is_arrE \<AA>.smc_Comp_is_arr)
    fix i assume prems: "i \<in>\<^sub>\<circ> I"
    from gf have gf': "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" by (simp add: smc_cs_intros)
    from that have g: "g \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" and f: "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" by auto
    interpret \<phi>: is_semifunctor \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (rule assms(2)[OF prems])
    from that show "smcf_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<rparr>\<lparr>i\<rparr> = 
      (
        smcf_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>smc_prod I \<AA>\<^esub> smcf_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>
      )\<lparr>i\<rparr>"
      unfolding 
        smcf_up_ArrMap_app_component[OF gf' prems]
        smc_prod_Comp_app_component[OF smcf_up_g smcf_up_f prems]
        smcf_up_ArrMap_app_component[OF g prems]
        smcf_up_ArrMap_app_component[OF f prems]
      by (rule \<phi>.smcf_ArrMap_Comp)
  qed
qed (auto simp: assms(1) psmc_semicategory_smc_prod smcf_up_components)


subsubsection\<open>Further properties\<close>

lemma (in psemicategory) psmc_Comp_smcf_proj_smcf_up: 
  assumes "semicategory \<alpha> \<CC>" 
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> i" 
    and "i \<in>\<^sub>\<circ> I" 
  shows "\<phi> i = \<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F smcf_up I \<AA> \<CC> \<phi>"
proof(rule smcf_dghm_eqI)
  interpret \<phi>: is_semifunctor \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (rule assms(2)[OF assms(3)])
  interpret \<pi>: is_semifunctor \<alpha> \<open>smc_prod I \<AA>\<close> \<open>\<AA> i\<close> \<open>\<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i\<close>
    by (simp add: assms(3) psmc_smcf_proj_is_semifunctor)
  interpret up: is_semifunctor \<alpha> \<CC> \<open>smc_prod I \<AA>\<close> \<open>smcf_up I \<AA> \<CC> \<phi>\<close>
    by 
      (
        simp add: 
          assms(2) \<phi>.HomDom.semicategory_axioms psmc_smcf_up_is_semifunctor
      )
  show "\<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> i" by (simp add: smc_cs_intros)
  show "\<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F smcf_up I \<AA> \<CC> \<phi> : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> i" 
      by (auto intro: smc_cs_intros)
  from assms show 
    "smcf_dghm (\<phi> i) = smcf_dghm (\<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F smcf_up I \<AA> \<CC> \<phi>)"
    unfolding slicing_simps[symmetric] slicing_commute[symmetric]
    by 
      (
        intro 
          psmc_dghm_comp_dghm_proj_dghm_up
            [
              where \<phi>=\<open>\<lambda>i. smcf_dghm (\<phi> i)\<close>, 
              unfolded slicing_simps[symmetric] slicing_commute[symmetric]
            ]
      )
      (auto simp: is_semifunctor.smcf_is_dghm)
qed simp_all

lemma (in psemicategory) psmc_smcf_up_eq_smcf_proj:
  assumes "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)"
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i = \<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>"
  shows "smcf_up I \<AA> \<CC> \<phi> = \<FF>"
proof(rule smcf_dghm_eqI)
  interpret \<FF>: is_semifunctor \<alpha> \<CC> \<open>(\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<close> \<FF> by (rule assms(1))
  show "smcf_up I \<AA> \<CC> \<phi> : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)"
  proof(rule psmc_smcf_up_is_semifunctor)
    fix i assume prems: "i \<in>\<^sub>\<circ> I"
    interpret \<pi>: is_semifunctor \<alpha> \<open>(\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)\<close> \<open>\<AA> i\<close> \<open>\<pi>\<^sub>S\<^sub>M\<^sub>C I \<AA> i\<close>
      using prems by (rule psmc_smcf_proj_is_semifunctor)
    show "\<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA> i" 
      unfolding assms(2)[OF prems] by (auto intro: smc_cs_intros)
  qed (auto intro: smc_cs_intros)
  show "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>I. \<AA> i)" by (rule assms(1))
  from assms show "smcf_dghm (smcf_up I \<AA> \<CC> \<phi>) = smcf_dghm \<FF>"
    unfolding slicing_simps[symmetric] slicing_commute[symmetric]
    by (intro psmc_dghm_up_eq_dghm_proj) 
      (auto simp: slicing_simps slicing_commute)
qed simp_all



subsection\<open>Singleton semicategory\<close>


subsubsection\<open>Slicing\<close>

context
  fixes \<CC> :: V
begin

lemmas_with [where \<CC>=\<open>smc_dg \<CC>\<close>, unfolded slicing_simps slicing_commute]:
  smc_singleton_ObjI = dg_singleton_ObjI
  and smc_singleton_ObjE = dg_singleton_ObjE
  and smc_singleton_ArrI = dg_singleton_ArrI
  and smc_singleton_ArrE = dg_singleton_ArrE

end

context semicategory
begin

interpretation dg: digraph \<alpha> \<open>smc_dg \<CC>\<close> by (rule smc_digraph)

lemmas_with [unfolded slicing_simps slicing_commute]:
  smc_finite_pdigraph_smc_singleton = dg.dg_finite_pdigraph_dg_singleton
  and smc_singleton_is_arrI = dg.dg_singleton_is_arrI
  and smc_singleton_is_arrD = dg.dg_singleton_is_arrD
  and smc_singleton_is_arrE = dg.dg_singleton_is_arrE

end


subsubsection\<open>Singleton semicategory is a semicategory\<close>

lemma (in semicategory) smc_finite_psemicategory_smc_singleton: 
  assumes "j \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "finite_psemicategory \<alpha> (set {j}) (\<lambda>i. \<CC>)"
  by 
    (
      auto intro: 
        assms
        semicategory_axioms 
        finite_psemicategory_finite_pdigraphI 
        smc_finite_pdigraph_smc_singleton 
    )

lemma (in semicategory) smc_semicategory_smc_singleton:
  assumes "j \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "semicategory \<alpha> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>set {j}. \<CC>)"
proof-
  interpret finite_psemicategory \<alpha> \<open>set {j}\<close> \<open>\<lambda>i. \<CC>\<close>
    using assms by (rule smc_finite_psemicategory_smc_singleton)
  show ?thesis by (rule psmc_semicategory_smc_prod)
qed



subsection\<open>Singleton semifunctor\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition smcf_singleton :: "V \<Rightarrow> V \<Rightarrow> V"
  where "smcf_singleton j \<CC> =
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. set {\<langle>j, a\<rangle>}),
      (\<lambda>f\<in>\<^sub>\<circ>\<CC>\<lparr>Arr\<rparr>. set {\<langle>j, f\<rangle>}),
      \<CC>,
      (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>set {j}. \<CC>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma smcf_singleton_components:
  shows "smcf_singleton j \<CC>\<lparr>ObjMap\<rparr> = (\<lambda>a\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. set {\<langle>j, a\<rangle>})"
    and "smcf_singleton j \<CC>\<lparr>ArrMap\<rparr> = (\<lambda>f\<in>\<^sub>\<circ>\<CC>\<lparr>Arr\<rparr>. set {\<langle>j, f\<rangle>})"
    and "smcf_singleton j \<CC>\<lparr>HomDom\<rparr> = \<CC>"
    and "smcf_singleton j \<CC>\<lparr>HomCod\<rparr> = (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>set {j}. \<CC>)"
  unfolding smcf_singleton_def dghm_field_simps 
  by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma smcf_dghm_smcf_singleton[slicing_commute]: 
  "dghm_singleton j (smc_dg \<CC>)= smcf_dghm (smcf_singleton j \<CC>)"
  unfolding dghm_singleton_def smcf_singleton_def slicing_simps slicing_commute
  by 
    (
      simp add: 
        nat_omega_simps dghm_field_simps dg_field_simps smc_dg_def smcf_dghm_def
     )

context
  fixes \<CC> :: V
begin

lemmas_with [where \<CC>=\<open>smc_dg \<CC>\<close>, unfolded slicing_simps slicing_commute]:
  smcf_singleton_ObjMap_vsv[smc_cs_intros] = dghm_singleton_ObjMap_vsv
  and smcf_singleton_ObjMap_vdomain[smc_cs_simps] = 
    dghm_singleton_ObjMap_vdomain
  and smcf_singleton_ObjMap_vrange = dghm_singleton_ObjMap_vrange
  and smcf_singleton_ObjMap_app[smc_prod_cs_simps] = dghm_singleton_ObjMap_app
  and smcf_singleton_ArrMap_vsv[smc_cs_intros] = dghm_singleton_ArrMap_vsv
  and smcf_singleton_ArrMap_vdomain[smc_cs_simps] = 
    dghm_singleton_ArrMap_vdomain
  and smcf_singleton_ArrMap_vrange = dghm_singleton_ArrMap_vrange
  and smcf_singleton_ArrMap_app[smc_prod_cs_simps] = dghm_singleton_ArrMap_app

end

context semicategory
begin

interpretation dg: digraph \<alpha> \<open>smc_dg \<CC>\<close> by (rule smc_digraph)

lemmas_with [unfolded slicing_simps slicing_commute]:
  smc_smcf_singleton_is_dghm = dg.dg_dghm_singleton_is_dghm

end


subsubsection\<open>Singleton semifunctor is an isomorphism of semicategories\<close>

lemma (in semicategory) smc_smcf_singleton_is_iso_semifunctor:
  assumes "j \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "smcf_singleton j \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>set {j}. \<CC>)"
proof(intro is_iso_semifunctorI is_semifunctorI)
  show dghm_singleton: 
    "smcf_dghm (smcf_singleton j \<CC>) :
      smc_dg \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> smc_dg (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>set {j}. \<CC>)"
    by (rule smc_smcf_singleton_is_dghm[OF assms, unfolded slicing_simps])
  show "vfsequence (smcf_singleton j \<CC>)" unfolding smcf_singleton_def by simp
  show "vcard (smcf_singleton j \<CC>) = 4\<^sub>\<nat>"
    unfolding smcf_singleton_def by (simp add: nat_omega_simps)
  from dghm_singleton show 
    "smcf_dghm (smcf_singleton j \<CC>) :
      smc_dg \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>set {j}. \<CC>)"
    by (simp add: is_iso_dghm.axioms(1))
  show "smcf_singleton j \<CC>\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<rparr> =
    smcf_singleton j \<CC>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>set {j}. \<CC>\<^esub>
    smcf_singleton j \<CC>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
    if "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" for g b c f a
  proof-
    let ?jg = \<open>smcf_singleton j \<CC>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>\<close>
      and ?jf = \<open>smcf_singleton j \<CC>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<close>
    from that have [simp]: "?jg = set {\<langle>j, g\<rangle>}" "?jf = set {\<langle>j, f\<rangle>}"
       by (simp_all add: smcf_singleton_ArrMap_app smc_cs_intros)
     from that have "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c" by (auto intro: smc_cs_intros)
    then have "smcf_singleton j \<CC>\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<rparr> = set {\<langle>j, g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<rangle>}"
      by (simp_all add: smcf_singleton_ArrMap_app smc_cs_intros)
    moreover from 
      smc_singleton_is_arrI[OF assms that(1)]
      smc_singleton_is_arrI[OF assms that(2)] 
    have "?jg \<circ>\<^sub>A\<^bsub>\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>set {j}. \<CC>\<^esub> ?jf = set {\<langle>j, g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<rangle>}"
      by (simp add: smc_prod_Comp_app VLambda_vsingleton)
    ultimately show ?thesis by auto
  qed
qed 
  (
    auto intro:
      smc_cs_intros
      assms 
      smc_semicategory_smc_singleton 
      smcf_singleton_components 
  )

lemmas [smc_cs_intros] = semicategory.smc_smcf_singleton_is_iso_semifunctor



subsection\<open>Product of two semicategories\<close>


subsubsection\<open>Definition and elementary properties.\<close>


text\<open>See Chapter II-3 in \cite{mac_lane_categories_2010}.\<close>

definition smc_prod_2 :: "V \<Rightarrow> V \<Rightarrow> V" (infixr \<open>\<times>\<^sub>S\<^sub>M\<^sub>C\<close> 80)
  where "\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB> \<equiv> smc_prod (2\<^sub>\<nat>) (\<lambda>i. (i = 0 ? \<AA> : \<BB>))"


text\<open>Slicing.\<close>
  
lemma smc_dg_smc_prod_2[slicing_commute]: 
  "smc_dg \<AA> \<times>\<^sub>D\<^sub>G smc_dg \<BB> = smc_dg (\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>)"
  unfolding smc_prod_2_def dg_prod_2_def slicing_commute[symmetric] if_distrib
  by simp

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "semicategory \<alpha> \<AA>" and \<BB>: "semicategory \<alpha> \<BB>"
begin

interpretation \<AA>: semicategory \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: semicategory \<alpha> \<BB> by (rule \<BB>)

lemmas_with 
  [
    where \<AA>=\<open>smc_dg \<AA>\<close> and \<BB>=\<open>smc_dg \<BB>\<close>, 
    unfolded slicing_simps slicing_commute, 
    OF \<AA>.smc_digraph \<BB>.smc_digraph
  ]:
  smc_prod_2_ObjI = dg_prod_2_ObjI 
  and smc_prod_2_ObjI'[smc_prod_cs_intros] = dg_prod_2_ObjI'
  and smc_prod_2_ObjE = dg_prod_2_ObjE
  and smc_prod_2_ArrI = dg_prod_2_ArrI
  and smc_prod_2_ArrI'[smc_prod_cs_intros] = dg_prod_2_ArrI'
  and smc_prod_2_ArrE = dg_prod_2_ArrE
  and smc_prod_2_is_arrI = dg_prod_2_is_arrI
  and smc_prod_2_is_arrI'[smc_prod_cs_intros] = dg_prod_2_is_arrI'
  and smc_prod_2_is_arrE = dg_prod_2_is_arrE
  and smc_prod_2_Dom_vsv = dg_prod_2_Dom_vsv
  and smc_prod_2_Dom_vdomain[smc_cs_simps] = dg_prod_2_Dom_vdomain
  and smc_prod_2_Dom_app[smc_prod_cs_simps] = dg_prod_2_Dom_app
  and smc_prod_2_Dom_vrange = dg_prod_2_Dom_vrange
  and smc_prod_2_Cod_vsv = dg_prod_2_Cod_vsv
  and smc_prod_2_Cod_vdomain[smc_cs_simps] = dg_prod_2_Cod_vdomain
  and smc_prod_2_Cod_app[smc_prod_cs_simps] = dg_prod_2_Cod_app
  and smc_prod_2_Cod_vrange = dg_prod_2_Cod_vrange
  and smc_prod_2_op_smc_smc_Obj[smc_op_simps] = dg_prod_2_op_dg_dg_Obj
  and smc_prod_2_smc_op_smc_Obj[smc_op_simps] = dg_prod_2_dg_op_dg_Obj
  and smc_prod_2_op_smc_smc_Arr[smc_op_simps] = dg_prod_2_op_dg_dg_Arr
  and smc_prod_2_smc_op_smc_Arr[smc_op_simps] = dg_prod_2_dg_op_dg_Arr

end


subsubsection\<open>Product of two semicategories is a semicategory\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "semicategory \<alpha> \<AA>" and \<BB>: "semicategory \<alpha> \<BB>"
begin

interpretation \<Z> \<alpha> by (rule semicategoryD[OF \<AA>])
interpretation \<AA>: semicategory \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: semicategory \<alpha> \<BB> by (rule \<BB>)

lemma finite_psemicategory_smc_prod_2: 
  "finite_psemicategory \<alpha> (2\<^sub>\<nat>) (if2 \<AA> \<BB>)"
proof(intro finite_psemicategoryI psemicategory_baseI)
  from Axiom_of_Infinity show z1_in_Vset: "2\<^sub>\<nat> \<in>\<^sub>\<circ> Vset \<alpha>" by blast
  show "semicategory \<alpha> (i = 0 ? \<AA> : \<BB>)" if "i \<in>\<^sub>\<circ> 2\<^sub>\<nat>" for i
    by (auto simp: smc_cs_intros)
qed auto

interpretation finite_psemicategory \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 \<AA> \<BB>\<close>
  by (intro finite_psemicategory_smc_prod_2 \<AA> \<BB>)

lemma semicategory_smc_prod_2[smc_cs_intros]: "semicategory \<alpha> (\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>)"
  unfolding smc_prod_2_def by (rule psmc_semicategory_smc_prod)

end


subsubsection\<open>Composition\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "semicategory \<alpha> \<AA>" and \<BB>: "semicategory \<alpha> \<BB>"
begin

interpretation \<Z> \<alpha> by (rule semicategoryD[OF \<AA>])

interpretation finite_psemicategory \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 \<AA> \<BB>\<close>
  by (intro finite_psemicategory_smc_prod_2 \<AA> \<BB>)

lemma smc_prod_2_Comp_app[smc_prod_cs_simps]:
  assumes "[g, g']\<^sub>\<circ> : [b, b']\<^sub>\<circ> \<mapsto>\<^bsub>\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>\<^esub> [c, c']\<^sub>\<circ>" 
    and "[f, f']\<^sub>\<circ> : [a, a']\<^sub>\<circ> \<mapsto>\<^bsub>\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>\<^esub> [b, b']\<^sub>\<circ>"
  shows "[g, g']\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>\<^esub> [f, f']\<^sub>\<circ> = [g \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f, g' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f']\<^sub>\<circ>"
proof-
  have "[g, g']\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>\<^esub> [f, f']\<^sub>\<circ> = 
    (\<lambda>i\<in>\<^sub>\<circ>2\<^sub>\<nat>. [g, g']\<^sub>\<circ>\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>i = 0 ? \<AA> : \<BB>\<^esub> [f, f']\<^sub>\<circ>\<lparr>i\<rparr>)"
    by 
      (
        rule smc_prod_Comp_app[
          OF assms[unfolded smc_prod_2_def], folded smc_prod_2_def
          ]
      )
  also have 
    "(\<lambda>i\<in>\<^sub>\<circ>2\<^sub>\<nat>. [g, g']\<^sub>\<circ>\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>i = 0 ? \<AA> : \<BB>\<^esub> [f, f']\<^sub>\<circ>\<lparr>i\<rparr>) = 
      [g \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f, g' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f']\<^sub>\<circ>"
  proof(rule vsv_eqI, unfold vdomain_VLambda)
    fix i assume "i \<in>\<^sub>\<circ> 2\<^sub>\<nat>"
    then consider \<open>i = 0\<close> | \<open>i = 1\<^sub>\<nat>\<close> unfolding two by auto 
    then show 
      "(\<lambda>i\<in>\<^sub>\<circ>2\<^sub>\<nat>. [g, g']\<^sub>\<circ>\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>i = 0 ? \<AA> : \<BB>\<^esub> [f, f']\<^sub>\<circ>\<lparr>i\<rparr>)\<lparr>i\<rparr> = 
        [g \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f, g' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f']\<^sub>\<circ>\<lparr>i\<rparr>"
      by cases (simp_all add: two nat_omega_simps)
  qed (auto simp: two nat_omega_simps)
  finally show ?thesis by simp
qed

end


subsubsection\<open>Opposite product semicategory\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "semicategory \<alpha> \<AA>" and \<BB>: "semicategory \<alpha> \<BB>"
begin

interpretation \<AA>: semicategory \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: semicategory \<alpha> \<BB> by (rule \<BB>)

lemma op_smc_smc_prod_2[smc_op_simps]: 
  "op_smc (\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>) = op_smc \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C op_smc \<BB>"
proof(rule smc_dg_eqI[of \<alpha>])

  from \<AA> \<BB> show smc_lhs: "semicategory \<alpha> (op_smc (\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>))"
    by 
      (
        cs_concl 
          cs_simp: smc_cs_simps smc_op_simps 
          cs_intro: smc_cs_intros smc_op_intros
      )
  interpret smc_lhs: semicategory \<alpha> \<open>op_smc (\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>)\<close> by (rule smc_lhs)
  
  from \<AA> \<BB> show smc_rhs: "semicategory \<alpha> (op_smc \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C op_smc \<BB>)"
    by 
      (
        cs_concl 
          cs_simp: smc_cs_simps smc_op_simps 
          cs_intro: smc_cs_intros smc_op_intros
      )
  interpret smc_rhs: semicategory \<alpha> \<open>op_smc \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C op_smc \<BB>\<close> by (rule smc_rhs)

  show "op_smc (\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>)\<lparr>Comp\<rparr> = (op_smc \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C op_smc \<BB>)\<lparr>Comp\<rparr>"
  proof(rule vsv_eqI)
    show "vsv (op_smc (\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>)\<lparr>Comp\<rparr>)"
      unfolding op_smc_components by (rule fflip_vsv)
    show "vsv ((op_smc \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C op_smc \<BB>)\<lparr>Comp\<rparr>)"
      unfolding smc_prod_2_def smc_prod_components by simp      
    show "\<D>\<^sub>\<circ> (op_smc (\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>)\<lparr>Comp\<rparr>) = \<D>\<^sub>\<circ> ((op_smc \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C op_smc \<BB>)\<lparr>Comp\<rparr>)"
    proof(intro vsubset_antisym vsubsetI)
      fix gg'ff' assume gf: "gg'ff' \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (op_smc (\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>)\<lparr>Comp\<rparr>)"
      then obtain gg' ff' aa' bb' cc' 
        where gg'ff'_def: "gg'ff' = [gg', ff']\<^sub>\<circ>" 
          and "gg' : bb' \<mapsto>\<^bsub>op_smc (\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>)\<^esub> cc'" 
          and "ff' : aa' \<mapsto>\<^bsub>op_smc (\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>)\<^esub> bb'"
        by clarsimp
      then have gg': "gg' : cc' \<mapsto>\<^bsub>\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>\<^esub> bb'" 
        and ff': "ff' : bb' \<mapsto>\<^bsub>\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>\<^esub> aa'"
        unfolding smc_op_simps by simp_all
      from gg' obtain g g' b b' c c' 
        where gg'_def: "gg' = [g, g']\<^sub>\<circ>" 
          and "cc' = [c, c']\<^sub>\<circ>" 
          and "bb' = [b, b']\<^sub>\<circ>"
          and g: "g : c \<mapsto>\<^bsub>\<AA>\<^esub> b" 
          and g': "g' : c' \<mapsto>\<^bsub>\<BB>\<^esub> b'"
        by (elim smc_prod_2_is_arrE[OF \<AA> \<BB>])
      with ff' obtain f f' a a' 
        where ff'_def: "ff' = [f, f']\<^sub>\<circ>" 
          and "bb' = [b, b']\<^sub>\<circ>" 
          and "aa' = [a, a']\<^sub>\<circ>"
          and f: "f : b \<mapsto>\<^bsub>\<AA>\<^esub> a" 
          and f': "f' : b' \<mapsto>\<^bsub>\<BB>\<^esub> a'"
        by (auto elim: smc_prod_2_is_arrE[OF \<AA> \<BB>])
      from \<AA> \<BB> g g' f f' show "gg'ff' \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((op_smc \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C op_smc \<BB>)\<lparr>Comp\<rparr>)"
        by
          (
            intro smc_rhs.smc_Comp_vdomainI[OF _ _ gg'ff'_def], 
            unfold gg'_def ff'_def
          )
          (
            cs_concl 
              cs_simp: smc_cs_simps smc_op_simps 
              cs_intro: smc_op_intros smc_prod_cs_intros
          )
    next
      fix gg'ff' assume gf: "gg'ff' \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((op_smc \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C op_smc \<BB>)\<lparr>Comp\<rparr>)"
      then obtain gg' ff' aa' bb' cc' 
        where gg'ff'_def: "gg'ff' = [gg', ff']\<^sub>\<circ>" 
          and gg': "gg' : bb' \<mapsto>\<^bsub>op_smc \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C op_smc \<BB>\<^esub> cc'" 
          and ff': "ff' : aa' \<mapsto>\<^bsub>op_smc \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C op_smc \<BB>\<^esub> bb'"
        by clarsimp
      from gg' obtain g g' b b' c c' 
        where gg'_def: "gg' = [g, g']\<^sub>\<circ>" 
          and "bb' = [b, b']\<^sub>\<circ>"
          and "cc' = [c, c']\<^sub>\<circ>" 
          and g: "g : b \<mapsto>\<^bsub>op_smc \<AA>\<^esub> c" 
          and g': "g' : b' \<mapsto>\<^bsub>op_smc \<BB>\<^esub> c'"
        by (elim smc_prod_2_is_arrE[OF \<AA>.semicategory_op \<BB>.semicategory_op])
      with ff' obtain f f' a a' 
        where ff'_def: "ff' = [f, f']\<^sub>\<circ>" 
          and "aa' = [a, a']\<^sub>\<circ>"
          and "bb' = [b, b']\<^sub>\<circ>" 
          and f: "f : a \<mapsto>\<^bsub>op_smc \<AA>\<^esub> b" 
          and f': "f' : a' \<mapsto>\<^bsub>op_smc \<BB>\<^esub> b'"
        by 
          (
            auto elim: 
              smc_prod_2_is_arrE[OF \<AA>.semicategory_op \<BB>.semicategory_op]
          )
      from \<AA> \<BB> g g' f f' show "gg'ff' \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (op_smc (\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>)\<lparr>Comp\<rparr>)"
        by 
          (
            intro smc_lhs.smc_Comp_vdomainI[OF _ _ gg'ff'_def], 
            unfold gg'_def ff'_def smc_op_simps
          )
          (
            cs_concl 
              cs_simp: smc_cs_simps smc_op_simps 
              cs_intro: smc_op_intros smc_prod_cs_intros
          )
    qed
    fix gg'ff' assume "gg'ff' \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (op_smc (\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>)\<lparr>Comp\<rparr>)"
    then obtain gg' ff' aa' bb' cc' 
      where gg'ff'_def: "gg'ff' = [gg', ff']\<^sub>\<circ>" 
        and "gg' : bb' \<mapsto>\<^bsub>op_smc (\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>)\<^esub> cc'" 
        and "ff' : aa' \<mapsto>\<^bsub>op_smc (\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>)\<^esub> bb'"
      by clarsimp
    then have gg': "gg' : cc' \<mapsto>\<^bsub>\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>\<^esub> bb'" 
      and ff': "ff' : bb' \<mapsto>\<^bsub>\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>\<^esub> aa'"
      unfolding smc_op_simps by simp_all
    from gg' obtain g g' b b' c c' 
      where gg'_def[smc_cs_simps]: "gg' = [g, g']\<^sub>\<circ>" 
        and "cc' = [c, c']\<^sub>\<circ>" 
        and "bb' = [b, b']\<^sub>\<circ>"
        and g: "g : c \<mapsto>\<^bsub>\<AA>\<^esub> b" 
        and g': "g' : c' \<mapsto>\<^bsub>\<BB>\<^esub> b'"
      by (elim smc_prod_2_is_arrE[OF \<AA> \<BB>])
    with ff' obtain f f' a a' 
      where ff'_def[smc_cs_simps]: "ff' = [f, f']\<^sub>\<circ>" 
        and "bb' = [b, b']\<^sub>\<circ>" 
        and "aa' = [a, a']\<^sub>\<circ>"
        and f: "f : b \<mapsto>\<^bsub>\<AA>\<^esub> a" 
        and f': "f' : b' \<mapsto>\<^bsub>\<BB>\<^esub> a'"
      by (auto elim: smc_prod_2_is_arrE[OF \<AA> \<BB>])
    from \<AA> \<BB> g g' f f' show "op_smc (\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>)\<lparr>Comp\<rparr>\<lparr>gg'ff'\<rparr> = 
      (op_smc \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C op_smc \<BB>)\<lparr>Comp\<rparr>\<lparr>gg'ff'\<rparr>"
      unfolding gg'ff'_def 
      by 
        (
          cs_concl 
            cs_simp: smc_cs_simps smc_op_simps smc_prod_cs_simps
            cs_intro: smc_cs_intros smc_op_intros smc_prod_cs_intros
        )
  qed

  from \<AA> \<BB> show 
    "smc_dg (op_smc (\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>)) = smc_dg (op_smc \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C op_smc \<BB>)"
    unfolding slicing_commute[symmetric]
    by (cs_concl cs_simp: dg_op_simps cs_intro: slicing_intros)

qed
  
end



subsection\<open>Projections for the product of two semicategories\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter II-3 in \cite{mac_lane_categories_2010}.\<close>

definition smcf_proj_fst :: "V \<Rightarrow> V \<Rightarrow> V" (\<open>\<pi>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>1\<close>)
  where "\<pi>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>1 \<AA> \<BB> = smcf_proj (2\<^sub>\<nat>) (\<lambda>i. (i = 0 ? \<AA> : \<BB>)) 0"
definition smcf_proj_snd :: "V \<Rightarrow> V \<Rightarrow> V" (\<open>\<pi>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>2\<close>)
  where "\<pi>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>2 \<AA> \<BB> = smcf_proj (2\<^sub>\<nat>) (\<lambda>i. (i = 0 ? \<AA> : \<BB>)) (1\<^sub>\<nat>)"


text\<open>Slicing\<close>

lemma smcf_dghm_smcf_proj_fst[slicing_commute]: 
  "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>1 (smc_dg \<AA>) (smc_dg \<BB>) = smcf_dghm (\<pi>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>1 \<AA> \<BB>)"
  unfolding 
    smcf_proj_fst_def dghm_proj_fst_def slicing_commute[symmetric] if_distrib 
    ..

lemma smcf_dghm_smcf_proj_snd[slicing_commute]: 
  "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>2 (smc_dg \<AA>) (smc_dg \<BB>) = smcf_dghm (\<pi>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>2 \<AA> \<BB>)"
  unfolding 
    smcf_proj_snd_def dghm_proj_snd_def slicing_commute[symmetric] if_distrib 
    ..

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "semicategory \<alpha> \<AA>" and \<BB>: "semicategory \<alpha> \<BB>"
begin

interpretation \<Z> \<alpha> by (rule semicategoryD[OF \<AA>])
interpretation \<AA>: semicategory \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: semicategory \<alpha> \<BB> by (rule \<BB>)

lemmas_with 
  [
    where \<AA>=\<open>smc_dg \<AA>\<close> and \<BB>=\<open>smc_dg \<BB>\<close>, 
    unfolded slicing_simps slicing_commute, 
    OF \<AA>.smc_digraph \<BB>.smc_digraph
  ]:
  smcf_proj_fst_ObjMap_app[smc_cs_simps] = dghm_proj_fst_ObjMap_app 
  and smcf_proj_snd_ObjMap_app[smc_cs_simps] = dghm_proj_snd_ObjMap_app
  and smcf_proj_fst_ArrMap_app[smc_cs_simps] = dghm_proj_fst_ArrMap_app
  and smcf_proj_snd_ArrMap_app[smc_cs_simps] = dghm_proj_snd_ArrMap_app

end


subsubsection\<open>
Domain and codomain of a projection of a product of two semicategories
\<close>

lemma smcf_proj_fst_HomDom: "\<pi>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>1 \<AA> \<BB>\<lparr>HomDom\<rparr> = \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>"
  unfolding smcf_proj_fst_def smcf_proj_components smc_prod_2_def ..

lemma smcf_proj_fst_HomCod: "\<pi>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>1 \<AA> \<BB>\<lparr>HomCod\<rparr> = \<AA>"
  unfolding smcf_proj_fst_def smcf_proj_components smc_prod_2_def by simp
  
lemma smcf_proj_snd_HomDom: "\<pi>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>2 \<AA> \<BB>\<lparr>HomDom\<rparr> = \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>"
  unfolding smcf_proj_snd_def smcf_proj_components smc_prod_2_def ..

lemma smcf_proj_snd_HomCod: "\<pi>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>2 \<AA> \<BB>\<lparr>HomCod\<rparr> = \<BB>"
  unfolding smcf_proj_snd_def smcf_proj_components smc_prod_2_def by simp


subsubsection\<open>Projection of a product of two semicategories is a semifunctor\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "semicategory \<alpha> \<AA>" and \<BB>: "semicategory \<alpha> \<BB>"
begin

interpretation \<Z> \<alpha> by (rule semicategoryD[OF \<AA>])
interpretation finite_psemicategory \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 \<AA> \<BB>\<close>
  by (intro finite_psemicategory_smc_prod_2 \<AA> \<BB>)

lemma smcf_proj_fst_is_semifunctor: 
  assumes "i \<in>\<^sub>\<circ> I" 
  shows "\<pi>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>1 \<AA> \<BB> : \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  by 
    (
      rule 
        psmc_smcf_proj_is_semifunctor[
          where i=0, simplified, folded smcf_proj_fst_def smc_prod_2_def
          ]
    )

lemma smcf_proj_fst_is_semifunctor'[smc_cs_intros]: 
  assumes "i \<in>\<^sub>\<circ> I" and "\<CC> = \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>" and "\<DD> = \<AA>"
  shows "\<pi>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>1 \<AA> \<BB> : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms(1) unfolding assms(2,3) by (rule smcf_proj_fst_is_semifunctor)

lemma smcf_proj_snd_is_semifunctor: 
  assumes "i \<in>\<^sub>\<circ> I" 
  shows "\<pi>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>2 \<AA> \<BB> : \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  by 
    (
      rule 
        psmc_smcf_proj_is_semifunctor[
          where i=\<open>1\<^sub>\<nat>\<close>, simplified, folded smcf_proj_snd_def smc_prod_2_def
          ]
    )

lemma smcf_proj_snd_is_semifunctor'[smc_cs_intros]: 
  assumes "i \<in>\<^sub>\<circ> I" and "\<CC> = \<AA> \<times>\<^sub>S\<^sub>M\<^sub>C \<BB>" and "\<DD> = \<BB>"
  shows "\<pi>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>2 \<AA> \<BB> : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms(1) unfolding assms(2,3) by (rule smcf_proj_snd_is_semifunctor)

end



subsection\<open>Product of three semicategories\<close>
(*TODO: find a way to generalize to the product of n semicategories*)


subsubsection\<open>Definition and elementary properties.\<close>

definition smc_prod_3 :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  ("(_ \<times>\<^sub>S\<^sub>M\<^sub>C\<^sub>3 _ \<times>\<^sub>S\<^sub>M\<^sub>C\<^sub>3 _)" [81, 81, 81] 80)
  where "\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>S\<^sub>M\<^sub>C\<^sub>3 \<CC> = (\<Prod>\<^sub>S\<^sub>M\<^sub>Ci\<in>\<^sub>\<circ>3\<^sub>\<nat>. if3 \<AA> \<BB> \<CC> i)"


text\<open>Slicing.\<close>

lemma smc_dg_smc_prod_3[slicing_commute]: 
  "smc_dg \<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 smc_dg \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 smc_dg \<CC> = smc_dg (\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>S\<^sub>M\<^sub>C\<^sub>3 \<CC>)"
  unfolding smc_prod_3_def dg_prod_3_def slicing_commute[symmetric] if_distrib
  by (simp add: if_distrib[symmetric])

context
  fixes \<alpha> \<AA> \<BB> \<CC>
  assumes \<AA>: "semicategory \<alpha> \<AA>" 
    and \<BB>: "semicategory \<alpha> \<BB>"
    and \<CC>: "semicategory \<alpha> \<CC>"
begin

interpretation \<AA>: semicategory \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: semicategory \<alpha> \<BB> by (rule \<BB>)
interpretation \<CC>: semicategory \<alpha> \<CC> by (rule \<CC>)

lemmas_with 
  [
    where \<AA>=\<open>smc_dg \<AA>\<close> and \<BB>=\<open>smc_dg \<BB>\<close> and \<CC>=\<open>smc_dg \<CC>\<close>, 
    unfolded slicing_simps slicing_commute, 
    OF \<AA>.smc_digraph \<BB>.smc_digraph \<CC>.smc_digraph
  ]:
  smc_prod_3_ObjI = dg_prod_3_ObjI 
  and smc_prod_3_ObjI'[smc_prod_cs_intros] = dg_prod_3_ObjI'
  and smc_prod_3_ObjE = dg_prod_3_ObjE
  and smc_prod_3_ArrI = dg_prod_3_ArrI
  and smc_prod_3_ArrI'[smc_prod_cs_intros] = dg_prod_3_ArrI'
  and smc_prod_3_ArrE = dg_prod_3_ArrE
  and smc_prod_3_is_arrI = dg_prod_3_is_arrI
  and smc_prod_3_is_arrI'[smc_prod_cs_intros] = dg_prod_3_is_arrI'
  and smc_prod_3_is_arrE = dg_prod_3_is_arrE
  and smc_prod_3_Dom_vsv = dg_prod_3_Dom_vsv
  and smc_prod_3_Dom_vdomain[smc_cs_simps] = dg_prod_3_Dom_vdomain
  and smc_prod_3_Dom_app[smc_prod_cs_simps] = dg_prod_3_Dom_app
  and smc_prod_3_Dom_vrange = dg_prod_3_Dom_vrange
  and smc_prod_3_Cod_vsv = dg_prod_3_Cod_vsv
  and smc_prod_3_Cod_vdomain[smc_cs_simps] = dg_prod_3_Cod_vdomain
  and smc_prod_3_Cod_app[smc_prod_cs_simps] = dg_prod_3_Cod_app
  and smc_prod_3_Cod_vrange = dg_prod_3_Cod_vrange

end


subsubsection\<open>Product of three semicategories is a semicategory\<close>

context 
  fixes \<alpha> \<AA> \<BB> \<CC>
  assumes \<AA>: "semicategory \<alpha> \<AA>" 
    and \<BB>: "semicategory \<alpha> \<BB>"
    and \<CC>: "semicategory \<alpha> \<CC>"
begin

interpretation \<Z> \<alpha> by (rule semicategoryD[OF \<AA>])
interpretation \<AA>: semicategory \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: semicategory \<alpha> \<BB> by (rule \<BB>)
interpretation \<CC>: semicategory \<alpha> \<CC> by (rule \<CC>)

lemma finite_psemicategory_smc_prod_3: 
  "finite_psemicategory \<alpha> (3\<^sub>\<nat>) (if3 \<AA> \<BB> \<CC>)"
proof(intro finite_psemicategoryI psemicategory_baseI)
  from Axiom_of_Infinity show z1_in_Vset: "3\<^sub>\<nat> \<in>\<^sub>\<circ> Vset \<alpha>" by blast
  show "semicategory \<alpha> (if3 \<AA> \<BB> \<CC> i)" if "i \<in>\<^sub>\<circ> 3\<^sub>\<nat>" for i
    by (auto simp: smc_cs_intros)
qed auto

interpretation finite_psemicategory \<alpha> \<open>3\<^sub>\<nat>\<close> \<open>if3 \<AA> \<BB> \<CC>\<close>
  by (intro finite_psemicategory_smc_prod_3 \<AA> \<BB>)

lemma semicategory_smc_prod_3[smc_cs_intros]: 
  "semicategory \<alpha> (\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>S\<^sub>M\<^sub>C\<^sub>3 \<CC>)"
  unfolding smc_prod_3_def by (rule psmc_semicategory_smc_prod)

end


subsubsection\<open>Composition\<close>

context 
  fixes \<alpha> \<AA> \<BB> \<CC>
  assumes \<AA>: "semicategory \<alpha> \<AA>" 
    and \<BB>: "semicategory \<alpha> \<BB>"
    and \<CC>: "semicategory \<alpha> \<CC>"
begin

interpretation \<Z> \<alpha> by (rule semicategoryD[OF \<AA>])

interpretation finite_psemicategory \<alpha> \<open>3\<^sub>\<nat>\<close> \<open>if3 \<AA> \<BB> \<CC>\<close>
  by (intro finite_psemicategory_smc_prod_3 \<AA> \<BB> \<CC>)

lemma smc_prod_3_Comp_app[smc_prod_cs_simps]:
  assumes "[g, g', g'']\<^sub>\<circ> : [b, b', b'']\<^sub>\<circ> \<mapsto>\<^bsub>\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>S\<^sub>M\<^sub>C\<^sub>3 \<CC>\<^esub> [c, c', c'']\<^sub>\<circ>" 
    and "[f, f', f'']\<^sub>\<circ> : [a, a', a'']\<^sub>\<circ> \<mapsto>\<^bsub>\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>S\<^sub>M\<^sub>C\<^sub>3 \<CC>\<^esub> [b, b', b'']\<^sub>\<circ>"
  shows 
    "[g, g', g'']\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>S\<^sub>M\<^sub>C\<^sub>3 \<CC>\<^esub> [f, f', f'']\<^sub>\<circ> =
      [g \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f, g' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f', g'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'']\<^sub>\<circ>"
proof-
  have 
    "[g, g', g'']\<^sub>\<circ> \<circ>\<^sub>A\<^bsub>\<AA> \<times>\<^sub>S\<^sub>M\<^sub>C\<^sub>3 \<BB> \<times>\<^sub>S\<^sub>M\<^sub>C\<^sub>3 \<CC>\<^esub> [f, f', f'']\<^sub>\<circ> =
      (\<lambda>i\<in>\<^sub>\<circ>3\<^sub>\<nat>. [g, g', g'']\<^sub>\<circ>\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>if3 \<AA> \<BB> \<CC> i\<^esub> [f, f', f'']\<^sub>\<circ>\<lparr>i\<rparr>)"
    by 
      (
        rule smc_prod_Comp_app[
          OF assms[unfolded smc_prod_3_def], folded smc_prod_3_def
          ]
      )
  also have 
    "(\<lambda>i\<in>\<^sub>\<circ>3\<^sub>\<nat>. [g, g', g'']\<^sub>\<circ>\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>if3 \<AA> \<BB> \<CC> i\<^esub> [f, f', f'']\<^sub>\<circ>\<lparr>i\<rparr>) = 
      [g \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f, g' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f', g'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'']\<^sub>\<circ>"
  proof(rule vsv_eqI, unfold vdomain_VLambda)
    fix i assume "i \<in>\<^sub>\<circ> 3\<^sub>\<nat>"
    then consider \<open>i = 0\<close> | \<open>i = 1\<^sub>\<nat>\<close> | \<open>i = 2\<^sub>\<nat>\<close> unfolding three by auto 
    then show 
      "(\<lambda>i\<in>\<^sub>\<circ>3\<^sub>\<nat>. [g, g', g'']\<^sub>\<circ>\<lparr>i\<rparr> \<circ>\<^sub>A\<^bsub>if3 \<AA> \<BB> \<CC> i\<^esub> [f, f', f'']\<^sub>\<circ>\<lparr>i\<rparr>)\<lparr>i\<rparr> = 
        [g \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f, g' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f', g'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'']\<^sub>\<circ>\<lparr>i\<rparr>"
      by cases (simp_all add: three nat_omega_simps)
  qed (auto simp: three nat_omega_simps)
  finally show ?thesis by simp
qed

end

text\<open>\newpage\<close>

end