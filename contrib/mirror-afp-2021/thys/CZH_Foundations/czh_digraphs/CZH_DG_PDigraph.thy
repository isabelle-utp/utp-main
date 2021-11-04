(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Product digraph\<close>
theory CZH_DG_PDigraph
  imports 
    CZH_DG_TDGHM
    CZH_DG_Small_Digraph
begin



subsection\<open>Background\<close>


text\<open>
The concept of a product digraph, as presented in this work, 
is a generalization of the concept of a product category,
as presented in Chapter II-3 in \cite{mac_lane_categories_2010}.
\<close>

named_theorems dg_prod_cs_simps
named_theorems dg_prod_cs_intros



subsection\<open>Product digraph: definition and elementary properties\<close>

definition dg_prod :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "dg_prod I \<AA> =
    [
      (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Obj\<rparr>),
      (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>),
      (\<lambda>f\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>). (\<lambda>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Dom\<rparr>\<lparr>f\<lparr>i\<rparr>\<rparr>)),
      (\<lambda>f\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>). (\<lambda>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Cod\<rparr>\<lparr>f\<lparr>i\<rparr>\<rparr>))
    ]\<^sub>\<circ>"

syntax "_PDIGRAPH" :: "pttrn \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  (\<open>(3\<Prod>\<^sub>D\<^sub>G_\<in>\<^sub>\<circ>_./ _)\<close> [0, 0, 10] 10)
translations "\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA>" \<rightleftharpoons> "CONST dg_prod I (\<lambda>i. \<AA>)"


text\<open>Components.\<close>

lemma dg_prod_components:
  shows "(\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr> = (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Obj\<rparr>)"
    and "(\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr> = (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>)"
    and "(\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Dom\<rparr> =
      (\<lambda>f\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>). (\<lambda>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Dom\<rparr>\<lparr>f\<lparr>i\<rparr>\<rparr>))"
    and "(\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Cod\<rparr> =
      (\<lambda>f\<in>\<^sub>\<circ>(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>). (\<lambda>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Cod\<rparr>\<lparr>f\<lparr>i\<rparr>\<rparr>))"
  unfolding dg_prod_def dg_field_simps by (simp_all add: nat_omega_simps)



subsection\<open>Local assumptions for a product digraph\<close>

locale pdigraph_base = \<Z> \<alpha> for \<alpha> I and \<AA> :: "V \<Rightarrow> V" +
  assumes pdg_digraphs[dg_prod_cs_intros]: "i \<in>\<^sub>\<circ> I \<Longrightarrow> digraph \<alpha> (\<AA> i)"
    and pdg_index_in_Vset[dg_cs_intros]: "I \<in>\<^sub>\<circ> Vset \<alpha>"


text\<open>Rules.\<close>

lemma (in pdigraph_base) pdigraph_base_axioms'[dg_prod_cs_intros]: 
  assumes "\<alpha>' = \<alpha>" and "I' = I"
  shows "pdigraph_base \<alpha>' I' \<AA>"
  unfolding assms by (rule pdigraph_base_axioms)

mk_ide rf pdigraph_base_def[unfolded pdigraph_base_axioms_def]
  |intro pdigraph_baseI|
  |dest pdigraph_baseD[dest]|
  |elim pdigraph_baseE[elim]|


text\<open>Elementary properties.\<close>

lemma (in pdigraph_base) pdg_Obj_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
  shows "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Obj\<rparr>) \<in>\<^sub>\<circ> Vset \<beta>"
proof(rule Vset_trans)
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Obj\<rparr>) \<in>\<^sub>\<circ> Vset (succ (succ \<alpha>))"
  proof
    (
      rule vsubset_in_VsetI,
      rule Limit_vproduct_vsubset_Vset_succI,
      rule Limit_\<alpha>,
      intro dg_cs_intros
    )
    show "Vset (succ \<alpha>) \<in>\<^sub>\<circ> Vset (succ (succ \<alpha>))" 
      by (cs_concl cs_intro: V_cs_intros)
    fix i assume prems: "i \<in>\<^sub>\<circ> I"
    interpret digraph \<alpha> \<open>\<AA> i\<close>
      using prems by (cs_concl cs_intro: dg_cs_intros dg_prod_cs_intros)
    show "\<AA> i\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>" by (rule dg_Obj_vsubset_Vset)
  qed
  from assms(2) show "Vset (succ (succ \<alpha>)) \<in>\<^sub>\<circ> Vset \<beta>"
    by (cs_concl cs_intro: V_cs_intros succ_in_Limit_iff[THEN iffD2])
qed

lemma (in pdigraph_base) pdg_Arr_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
  shows "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>) \<in>\<^sub>\<circ> Vset \<beta>"
proof(rule Vset_trans)
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>) \<in>\<^sub>\<circ> Vset (succ (succ \<alpha>))"
  proof
    (
      rule vsubset_in_VsetI,
      rule Limit_vproduct_vsubset_Vset_succI,
      rule Limit_\<alpha>,
      intro dg_cs_intros
    )
    fix i assume "i \<in>\<^sub>\<circ> I"
    then interpret digraph \<alpha> \<open>\<AA> i\<close> 
      by (cs_concl cs_intro: dg_prod_cs_intros)
    show "\<AA> i\<lparr>Arr\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>" by (rule dg_Arr_vsubset_Vset)
  qed (cs_concl cs_intro: V_cs_intros)
  from assms(2) show "Vset (succ (succ \<alpha>)) \<in>\<^sub>\<circ> Vset \<beta>"
    by (cs_concl cs_intro: V_cs_intros succ_in_Limit_iff[THEN iffD2])
qed

lemmas_with (in pdigraph_base) [folded dg_prod_components]:
  pdg_dg_prod_Obj_in_Vset[dg_cs_intros] = pdg_Obj_in_Vset
  and pdg_dg_prod_Arr_in_Vset[dg_cs_intros] = pdg_Arr_in_Vset

lemma (in pdigraph_base) pdg_vsubset_index_pdigraph_base:
  assumes "J \<subseteq>\<^sub>\<circ> I"
  shows "pdigraph_base \<alpha> J \<AA>"
  using assms
  by (intro pdigraph_baseI)
    (auto simp: vsubset_in_VsetI dg_cs_intros intro: dg_prod_cs_intros)


subsubsection\<open>Object\<close>

lemma dg_prod_ObjI:
  assumes "vsv a" and "\<D>\<^sub>\<circ> a = I" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> a\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>"
  shows "a \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"
  using assms unfolding dg_prod_components by auto

lemma dg_prod_ObjD:
  assumes "a \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>" 
  shows "vsv a" and "\<D>\<^sub>\<circ> a = I" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> a\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>"
  using assms unfolding dg_prod_components by auto

lemma dg_prod_ObjE:
  assumes "a \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>" 
  obtains "vsv a" and "\<D>\<^sub>\<circ> a = I" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> a\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>"
  using assms by (auto dest: dg_prod_ObjD)

lemma dg_prod_Obj_cong:
  assumes "g \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"
    and "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> g\<lparr>i\<rparr> = f\<lparr>i\<rparr>"
  shows "g = f"
  using assms by (intro vsv_eqI[of g f]) (force simp: dg_prod_components)+


subsubsection\<open>Arrow\<close>

lemma dg_prod_ArrI:
  assumes "vsv f" and "\<D>\<^sub>\<circ> f = I" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> f\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Arr\<rparr>"
  shows "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
  using assms unfolding dg_prod_components by auto

lemma dg_prod_ArrD:
  assumes "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>" 
  shows "vsv f" and "\<D>\<^sub>\<circ> f = I" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> f\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Arr\<rparr>"
  using assms unfolding dg_prod_components by auto

lemma dg_prod_ArrE:
  assumes "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>" 
  obtains "vsv f" and "\<D>\<^sub>\<circ> f = I" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> f\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Arr\<rparr>"
  using assms by (auto dest: dg_prod_ArrD)

lemma dg_prod_Arr_cong:
  assumes "g \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
    and "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> g\<lparr>i\<rparr> = f\<lparr>i\<rparr>"
  shows "g = f"
  using assms by (intro vsv_eqI[of g f]) (force simp: dg_prod_components)+


subsubsection\<open>Domain\<close>

mk_VLambda dg_prod_components(3)
  |vsv dg_prod_Dom_vsv[dg_cs_intros]|
  |vdomain dg_prod_Dom_vdomain[folded dg_prod_components, dg_cs_simps]|
  |app dg_prod_Dom_app[folded dg_prod_components]|

lemma (in pdigraph_base) dg_prod_Dom_app_in_Obj[dg_cs_intros]:
  assumes "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
  shows "(\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Dom\<rparr>\<lparr>f\<rparr> \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"
  unfolding dg_prod_components(1) dg_prod_Dom_app[OF assms]
proof(intro vproductI ballI)
  fix i assume prems: "i \<in>\<^sub>\<circ> I" 
  interpret digraph \<alpha> \<open>\<AA> i\<close> 
    by (auto simp: prems intro: dg_prod_cs_intros)
  from assms prems show "(\<lambda>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Dom\<rparr>\<lparr>f\<lparr>i\<rparr>\<rparr>)\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>"
    unfolding dg_prod_components(2) by force
qed simp_all

lemma dg_prod_Dom_app_component_app[dg_cs_simps]:
  assumes "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>" and "i \<in>\<^sub>\<circ> I"
  shows "(\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Dom\<rparr>\<lparr>f\<rparr>\<lparr>i\<rparr> = \<AA> i\<lparr>Dom\<rparr>\<lparr>f\<lparr>i\<rparr>\<rparr>"
  using assms(2) unfolding dg_prod_Dom_app[OF assms(1)] by simp


subsubsection\<open>Codomain\<close>

mk_VLambda dg_prod_components(4)
  |vsv dg_prod_Cod_vsv[dg_cs_intros]|
  |vdomain dg_prod_Cod_vdomain[folded dg_prod_components, dg_cs_simps]|
  |app dg_prod_Cod_app[folded dg_prod_components]|

lemma (in pdigraph_base) dg_prod_Cod_app_in_Obj[dg_cs_intros]:
  assumes "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
  shows "(\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Cod\<rparr>\<lparr>f\<rparr> \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"
  unfolding dg_prod_components(1) dg_prod_Cod_app[OF assms]
proof(rule vproductI)
  show "\<forall>i\<in>\<^sub>\<circ>I. (\<lambda>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Cod\<rparr>\<lparr>f\<lparr>i\<rparr>\<rparr>)\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>"
  proof(intro ballI)
    fix i assume prems: "i \<in>\<^sub>\<circ> I" 
    then interpret digraph \<alpha> \<open>\<AA> i\<close> 
      by (auto intro: dg_prod_cs_intros)
    from assms prems show "(\<lambda>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Cod\<rparr>\<lparr>f\<lparr>i\<rparr>\<rparr>)\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>"
      unfolding dg_prod_components(2) by force
  qed
qed simp_all

lemma dg_prod_Cod_app_component_app[dg_cs_simps]:
  assumes "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>" and "i \<in>\<^sub>\<circ> I"
  shows "(\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<lparr>i\<rparr> = \<AA> i\<lparr>Cod\<rparr>\<lparr>f\<lparr>i\<rparr>\<rparr>"
  using assms(2) unfolding dg_prod_Cod_app[OF assms(1)] by simp


subsubsection\<open>A product \<open>\<alpha>\<close>-digraph is a tiny \<open>\<beta>\<close>-digraph\<close>

lemma (in pdigraph_base) pdg_tiny_digraph_dg_prod:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" 
  shows "tiny_digraph \<beta> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)"
proof(intro tiny_digraphI)
  show "vfsequence (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)" unfolding dg_prod_def by simp
  show "vcard (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i) = 4\<^sub>\<nat>"
    unfolding dg_prod_def by (simp add: nat_omega_simps)
  show vsv_dg_prod_Dom: "vsv ((\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Dom\<rparr>)" 
    unfolding dg_prod_components by simp
  show vdomain_dg_prod_Dom: "\<D>\<^sub>\<circ> ((\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Dom\<rparr>) = (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
    unfolding dg_prod_components by simp
  show "\<R>\<^sub>\<circ> ((\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"  
    by (rule vsubsetI)
      (
        metis 
          dg_prod_Dom_app_in_Obj 
          dg_prod_Dom_vdomain 
          vsv.vrange_atE 
          vsv_dg_prod_Dom
      )
  show vsv_dg_prod_Cod: "vsv ((\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Cod\<rparr>)" 
    unfolding dg_prod_components by auto
  show vdomain_dg_prod_Cod: "\<D>\<^sub>\<circ> ((\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Cod\<rparr>) = (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
    unfolding dg_prod_components by auto
  show "\<R>\<^sub>\<circ> ((\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"  
    by (rule vsubsetI)
      (
        metis 
          dg_prod_Cod_app_in_Obj 
          vdomain_dg_prod_Cod 
          vsv.vrange_atE 
          vsv_dg_prod_Cod
      )
qed 
  (
    auto simp:
      dg_cs_intros
      assms 
      pdg_dg_prod_Arr_in_Vset[OF assms(1,2)]
      pdg_dg_prod_Obj_in_Vset[OF assms(1,2)]
  )


lemma (in pdigraph_base) pdg_tiny_digraph_dg_prod': 
  "tiny_digraph (\<alpha> + \<omega>) (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)"
  by (rule pdg_tiny_digraph_dg_prod)
    (simp_all add: \<Z>_\<alpha>_\<alpha>\<omega> \<Z>.intro \<Z>_Limit_\<alpha>\<omega> \<Z>_\<omega>_\<alpha>\<omega>)


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma (in pdigraph_base) dg_prod_is_arrI:
  assumes "vsv f"
    and "\<D>\<^sub>\<circ> f = I"
    and "vsv a"
    and "\<D>\<^sub>\<circ> a = I"
    and "vsv b"
    and "\<D>\<^sub>\<circ> b = I"
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> f\<lparr>i\<rparr> : a\<lparr>i\<rparr> \<mapsto>\<^bsub>\<AA> i\<^esub> b\<lparr>i\<rparr>"
  shows "f : a \<mapsto>\<^bsub>\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i\<^esub> b"
proof(intro is_arrI)
  interpret f: vsv f by (rule assms(1))
  interpret a: vsv a by (rule assms(3))
  interpret b: vsv b by (rule assms(5))
  from assms(7) have f_components: "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> f\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Arr\<rparr>" by auto
  from assms(7) have a_components: "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> a\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>"
    by (meson digraph.dg_is_arrD(2) pdg_digraphs)
  from assms(7) have b_components: "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> b\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>"
    by (meson digraph.dg_is_arrD(3) pdg_digraphs)
  show f_in_Arr: "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
    unfolding dg_prod_components
    by (intro vproductI)
      (auto simp: f_components assms(2) f.vsv_vrange_vsubset_vifunion_app)
  show "(\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Dom\<rparr>\<lparr>f\<rparr> = a"
  proof(rule vsv_eqI)
    from dg_prod_Dom_app_in_Obj[OF f_in_Arr] show "vsv ((\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Dom\<rparr>\<lparr>f\<rparr>)"
      unfolding dg_prod_components by clarsimp
    from dg_prod_Dom_app_in_Obj[OF f_in_Arr] assms(4) show [simp]:
      "\<D>\<^sub>\<circ> ((\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Dom\<rparr>\<lparr>f\<rparr>) = \<D>\<^sub>\<circ> a"
      unfolding dg_prod_components by clarsimp
    fix i assume "i \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Dom\<rparr>\<lparr>f\<rparr>)"
    then have i: "i \<in>\<^sub>\<circ> I" by (simp add: assms(4))
    from a_components assms(7) i show "(\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Dom\<rparr>\<lparr>f\<rparr>\<lparr>i\<rparr> = a\<lparr>i\<rparr>"
      unfolding dg_prod_Dom_app_component_app[OF f_in_Arr i] by auto
  qed auto
  show "(\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Cod\<rparr>\<lparr>f\<rparr> = b"
  proof(rule vsv_eqI)
    from dg_prod_Cod_app_in_Obj[OF f_in_Arr] show "vsv ((\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Cod\<rparr>\<lparr>f\<rparr>)"
      unfolding dg_prod_components by clarsimp
    from dg_prod_Cod_app_in_Obj[OF f_in_Arr] assms(6) show [simp]:
      "\<D>\<^sub>\<circ> ((\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Cod\<rparr>\<lparr>f\<rparr>) = \<D>\<^sub>\<circ> b"
      unfolding dg_prod_components by clarsimp
    fix i assume "i \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Cod\<rparr>\<lparr>f\<rparr>)"
    then have i: "i \<in>\<^sub>\<circ> I" by (simp add: assms(6))
    from b_components assms(7) i show "(\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Cod\<rparr>\<lparr>f\<rparr>\<lparr>i\<rparr> = b\<lparr>i\<rparr>"
      unfolding dg_prod_Cod_app_component_app[OF f_in_Arr i] by auto
  qed auto
qed

lemma (in pdigraph_base) dg_prod_is_arrD[dest]:
  assumes "f : a \<mapsto>\<^bsub>\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i\<^esub> b"
  shows "vsv f"
    and "\<D>\<^sub>\<circ> f = I"
    and "vsv a"
    and "\<D>\<^sub>\<circ> a = I"
    and "vsv b"
    and "\<D>\<^sub>\<circ> b = I"
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> f\<lparr>i\<rparr> : a\<lparr>i\<rparr> \<mapsto>\<^bsub>\<AA> i\<^esub> b\<lparr>i\<rparr>"
proof-
  from is_arrD[OF assms] have f: "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
    and a: "a \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>" 
    and b: "b \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>" 
    by (auto intro: dg_cs_intros)
  then show "\<D>\<^sub>\<circ> f = I" "\<D>\<^sub>\<circ> a = I" "\<D>\<^sub>\<circ> b = I" "vsv f" "vsv a" "vsv b"
    unfolding dg_prod_components by auto
  fix i assume prems: "i \<in>\<^sub>\<circ> I"
  show "f\<lparr>i\<rparr> : a\<lparr>i\<rparr> \<mapsto>\<^bsub>\<AA> i\<^esub> b\<lparr>i\<rparr>"
  proof(intro is_arrI)
    from assms(1) have f: "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
      and a: "a \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"
      and b: "b \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"
    by (auto intro: dg_cs_intros)
    from f prems show "f\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Arr\<rparr>"
      unfolding dg_prod_components by clarsimp
    from a b assms(1) prems dg_prod_components(2,3,4) show 
      "\<AA> i\<lparr>Dom\<rparr>\<lparr>f\<lparr>i\<rparr>\<rparr> = a\<lparr>i\<rparr>" "\<AA> i\<lparr>Cod\<rparr>\<lparr>f\<lparr>i\<rparr>\<rparr> = b\<lparr>i\<rparr>"
      by fastforce+
  qed
qed

lemma (in pdigraph_base) dg_prod_is_arrE[elim]:
  assumes "f : a \<mapsto>\<^bsub>\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i\<^esub> b"
  obtains "vsv f"
    and "\<D>\<^sub>\<circ> f = I"
    and "vsv a"
    and "\<D>\<^sub>\<circ> a = I"
    and "vsv b"
    and "\<D>\<^sub>\<circ> b = I"
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> f\<lparr>i\<rparr> : a\<lparr>i\<rparr> \<mapsto>\<^bsub>\<AA> i\<^esub> b\<lparr>i\<rparr>"
  using assms by auto



subsection\<open>Further local assumptions for product digraphs\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale pdigraph = pdigraph_base \<alpha> I \<AA> for \<alpha> I \<AA> +
  assumes pdg_Obj_vsubset_Vset: "J \<subseteq>\<^sub>\<circ> I \<Longrightarrow> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>J. \<AA> i)\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    and pdg_Hom_vifunion_in_Vset: 
      "\<lbrakk>
        J \<subseteq>\<^sub>\<circ> I;
        A \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>J. \<AA> i)\<lparr>Obj\<rparr>;
        B \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>J. \<AA> i)\<lparr>Obj\<rparr>;
        A \<in>\<^sub>\<circ> Vset \<alpha>;
        B \<in>\<^sub>\<circ> Vset \<alpha>
      \<rbrakk> \<Longrightarrow> (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>J. \<AA> i) a b) \<in>\<^sub>\<circ> Vset \<alpha>"


text\<open>Rules.\<close>

lemma (in pdigraph) pdigraph_axioms'[dg_prod_cs_intros]: 
  assumes "\<alpha>' = \<alpha>" and "I' = I"
  shows "pdigraph \<alpha>' I' \<AA>"
  unfolding assms by (rule pdigraph_axioms)

mk_ide rf pdigraph_def[unfolded pdigraph_axioms_def]
  |intro pdigraphI|
  |dest pdigraphD[dest]|
  |elim pdigraphE[elim]|

lemmas [dg_prod_cs_intros] = pdigraphD(1)


text\<open>Elementary properties.\<close>

lemma (in pdigraph) pdg_Obj_vsubset_Vset': "(\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  by (rule pdg_Obj_vsubset_Vset) simp

lemma (in pdigraph) pdg_Hom_vifunion_in_Vset':
  assumes "A \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"
    and "B \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"
    and "A \<in>\<^sub>\<circ> Vset \<alpha>"
    and "B \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i) a b) \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms by (intro pdg_Hom_vifunion_in_Vset) simp_all

lemma (in pdigraph) pdg_vsubset_index_pdigraph:
  assumes "J \<subseteq>\<^sub>\<circ> I"
  shows "pdigraph \<alpha> J \<AA>"
proof(intro pdigraphI)
  show "dg_prod J' \<AA>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>" if \<open>J' \<subseteq>\<^sub>\<circ> J\<close> for J'
  proof-
    from that assms have "J' \<subseteq>\<^sub>\<circ> I" by simp
    then show "dg_prod J' \<AA>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>" by (rule pdg_Obj_vsubset_Vset)
  qed
  fix A B J' assume prems: 
    "J' \<subseteq>\<^sub>\<circ> J"
    "A \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>J'. \<AA> i)\<lparr>Obj\<rparr>"
    "B \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>J'. \<AA> i)\<lparr>Obj\<rparr>"
    "A \<in>\<^sub>\<circ> Vset \<alpha>" 
    "B \<in>\<^sub>\<circ> Vset \<alpha>"
  show "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>J'. \<AA> i) a b) \<in>\<^sub>\<circ> Vset \<alpha>"
  proof-
    from prems(1) assms have "J' \<subseteq>\<^sub>\<circ> I" by simp
    from pdg_Hom_vifunion_in_Vset[OF this prems(2-5)] show ?thesis.
  qed
qed (rule pdg_vsubset_index_pdigraph_base[OF assms])


subsubsection\<open>A product \<open>\<alpha>\<close>-digraph is an \<open>\<alpha>\<close>-digraph\<close>

lemma (in pdigraph) pdg_digraph_dg_prod: "digraph \<alpha> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)"
proof-
  interpret tiny_digraph \<open>\<alpha> + \<omega>\<close> \<open>\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i\<close>
    by (intro pdg_tiny_digraph_dg_prod) 
      (auto simp: \<Z>_\<alpha>_\<alpha>\<omega> \<Z>.intro \<Z>_Limit_\<alpha>\<omega> \<Z>_\<omega>_\<alpha>\<omega>)
  show ?thesis
    by (rule digraph_if_digraph)  
      (
        auto 
          intro!: pdg_Hom_vifunion_in_Vset pdg_Obj_vsubset_Vset
          intro: dg_cs_intros
      )
qed



subsection\<open>Local assumptions for a finite product digraph\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale finite_pdigraph = pdigraph_base \<alpha> I \<AA> for \<alpha> I \<AA> +
  assumes fin_pdg_index_vfinite: "vfinite I"


text\<open>Rules.\<close>

lemma (in finite_pdigraph) finite_pdigraph_axioms'[dg_prod_cs_intros]: 
  assumes "\<alpha>' = \<alpha>" and "I' = I"
  shows "finite_pdigraph \<alpha>' I' \<AA>"
  unfolding assms by (rule finite_pdigraph_axioms)

mk_ide rf finite_pdigraph_def[unfolded finite_pdigraph_axioms_def]
  |intro finite_pdigraphI|
  |dest finite_pdigraphD[dest]|
  |elim finite_pdigraphE[elim]|

lemmas [dg_prod_cs_intros] = finite_pdigraphD(1)


subsubsection\<open>
Local assumptions for a finite product digraph and local
assumptions for an arbitrary product digraph
\<close>

sublocale finite_pdigraph \<subseteq> pdigraph \<alpha> I \<AA>
proof(intro pdigraphI)
  show "(\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>J. \<AA> i)\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>" if "J \<subseteq>\<^sub>\<circ> I" for J
    unfolding dg_prod_components
  proof-
    from that fin_pdg_index_vfinite have J: "vfinite J"
      by (cs_concl cs_intro: vfinite_vsubset)
    show "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>J. \<AA> i\<lparr>Obj\<rparr>) \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    proof(intro vsubsetI)
      fix A assume prems: "A \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>J. \<AA> i\<lparr>Obj\<rparr>)"
      note A = vproductD[OF prems, rule_format]
      show "A \<in>\<^sub>\<circ> Vset \<alpha>"
      proof(rule vsv.vsv_Limit_vsv_in_VsetI)
        from that show "\<D>\<^sub>\<circ> A \<in>\<^sub>\<circ> Vset \<alpha>" 
          unfolding A(2) by (auto intro: pdg_index_in_Vset)
        show "\<R>\<^sub>\<circ> A \<subseteq>\<^sub>\<circ> Vset \<alpha>"
        proof(intro vsv.vsv_vrange_vsubset, unfold A(2))
          fix i assume prems': "i \<in>\<^sub>\<circ> J"
          with that have i: "i \<in>\<^sub>\<circ> I" by auto
          interpret digraph \<alpha> \<open>\<AA> i\<close>
            by (cs_concl cs_intro: dg_prod_cs_intros i)
          have "A\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>" by (rule A(3)[OF prems'])
          then show "A\<lparr>i\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" by (cs_concl cs_intro: dg_cs_intros)
        qed (intro A(1))
      qed (auto simp: A(2) intro!: J A(1))
    qed
  qed
  show "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>J. \<AA> i) a b) \<in>\<^sub>\<circ> Vset \<alpha>"
    if J: "J \<subseteq>\<^sub>\<circ> I"
      and A: "A \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>J. \<AA> i)\<lparr>Obj\<rparr>"
      and B: "B \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>J. \<AA> i)\<lparr>Obj\<rparr>"
      and A_in_Vset: "A \<in>\<^sub>\<circ> Vset \<alpha>"
      and B_in_Vset: "B \<in>\<^sub>\<circ> Vset \<alpha>"
    for J A B 
  proof-
    interpret J: pdigraph_base \<alpha> J \<AA> 
      by (intro J pdg_vsubset_index_pdigraph_base)
    let ?UA = \<open>\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>A))\<close> and ?UB = \<open>\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>B))\<close>
    from that(4) have UA: "?UA \<in>\<^sub>\<circ> Vset \<alpha>" by (intro VUnion_in_VsetI)
    from that(5) have UB: "?UB \<in>\<^sub>\<circ> Vset \<alpha>" by (intro VUnion_in_VsetI)
    have "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>J. (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>?UA. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>?UB. Hom (\<AA> i) a b)) \<in>\<^sub>\<circ> Vset \<alpha>"
    proof(intro Limit_vproduct_in_VsetI)
      from that(1) show "J \<in>\<^sub>\<circ> Vset \<alpha>" by (auto intro!: pdg_index_in_Vset)
      show "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>?UA. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>?UB. Hom (\<AA> i) a b) \<in>\<^sub>\<circ> Vset \<alpha>" if i: "i \<in>\<^sub>\<circ> J" for i
      proof-
        from i J have i: "i \<in>\<^sub>\<circ> I" by auto
        interpret digraph \<alpha> \<open>\<AA> i\<close> 
          using i by (cs_concl cs_intro: dg_prod_cs_intros)
        have [dg_cs_simps]: "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>?UA. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>?UB. Hom (\<AA> i) a b) \<subseteq>\<^sub>\<circ>
          (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>?UA \<inter>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>?UB \<inter>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>. Hom (\<AA> i) a b)"
        proof(intro vsubsetI)
          fix f assume "f \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>?UA. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>?UB. Hom (\<AA> i) a b)"
          then obtain a b
            where a: "a \<in>\<^sub>\<circ> ?UA" and b: "b \<in>\<^sub>\<circ> ?UB" and f: "f : a \<mapsto>\<^bsub>\<AA> i\<^esub> b" 
            by (elim vifunionE, unfold in_Hom_iff)
          then show
            "f \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>?UA \<inter>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>?UB \<inter>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>. Hom (\<AA> i) a b)"
            by (intro vifunionI, unfold in_Hom_iff) (auto intro!: f b a)
        qed
        moreover from UA UB have 
          "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>?UA \<inter>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>?UB \<inter>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>. Hom (\<AA> i) a b) \<in>\<^sub>\<circ> 
            Vset \<alpha>"
          by (intro dg_Hom_vifunion_in_Vset) auto
        ultimately show ?thesis by auto
      qed
      from J show "vfinite J"
        by (rule vfinite_vsubset[OF fin_pdg_index_vfinite])
    qed auto
    moreover have 
      "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>J. \<AA> i) a b) \<subseteq>\<^sub>\<circ>
        (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>J. (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>?UA. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>?UB. Hom (\<AA> i) a b))"
    proof(intro vsubsetI)
      fix f assume "f \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>J. \<AA> i) a b)"
      then obtain a b 
        where a: "a \<in>\<^sub>\<circ> A" and b: "b \<in>\<^sub>\<circ> B" and f: "f \<in>\<^sub>\<circ> Hom (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>J. \<AA> i) a b"
        by auto
      from f have f: "f : a \<mapsto>\<^bsub>(\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>J. \<AA> i)\<^esub> b" by simp
      show "f \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>J. (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>?UA. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>?UB. Hom (\<AA> i) a b))"
      proof
        (
          intro vproductI, 
          unfold Ball_def; 
          (intro allI impI)?;
          (intro vifunionI)?;
          (unfold in_Hom_iff)?
        )
        from f show "vsv f" by (auto simp: dg_prod_components(2))
        from f show "\<D>\<^sub>\<circ> f = J" by (auto simp: dg_prod_components(2))
        fix i assume i: "i \<in>\<^sub>\<circ> J"
        show "a\<lparr>i\<rparr> \<in>\<^sub>\<circ> ?UA"
          by 
            (
              intro vprojection_in_VUnionI, 
              rule that(2)[unfolded dg_prod_components(1)]; 
              intro a i
            )
        show "b\<lparr>i\<rparr> \<in>\<^sub>\<circ> ?UB"
          by 
            (
              intro vprojection_in_VUnionI, 
              rule that(3)[unfolded dg_prod_components(1)]; 
              intro b i
            )
        show "f\<lparr>i\<rparr> : a\<lparr>i\<rparr> \<mapsto>\<^bsub>\<AA> i\<^esub> b\<lparr>i\<rparr>" by (rule J.dg_prod_is_arrD(7)[OF f i])
      qed
    qed
    ultimately show "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>J. \<AA> i) a b) \<in>\<^sub>\<circ> Vset \<alpha>" 
      by blast
  qed
qed (intro pdigraph_base_axioms)



subsection\<open>Binary union and complement\<close>


subsubsection\<open>Application-specific methods\<close>

method vdiff_of_vunion uses rule assms subset = 
  (
    rule 
      rule
        [
          OF vintersection_complement assms, 
          unfolded vunion_complement[OF subset]
        ]
  )

method vdiff_of_vunion' uses rule assms subset = 
  (
    rule 
      rule
        [
          OF vintersection_complement complement_vsubset subset assms, 
          unfolded vunion_complement[OF subset]
        ]
  )


subsubsection\<open>Results\<close>

lemma dg_prod_vunion_Obj_in_Obj:
  assumes "vdisjnt J K"
    and "b \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>J. \<AA> j)\<lparr>Obj\<rparr>" 
    and "c \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gk\<in>\<^sub>\<circ>K. \<AA> k)\<lparr>Obj\<rparr>"
  shows "b \<union>\<^sub>\<circ> c \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>J \<union>\<^sub>\<circ> K. \<AA> i)\<lparr>Obj\<rparr>"
proof-

  interpret b: vsv b using assms(2) unfolding dg_prod_components by clarsimp
  interpret c: vsv c using assms(3) unfolding dg_prod_components by clarsimp

  from assms(2,3) have dom_b: "\<D>\<^sub>\<circ> b = J" and dom_c: "\<D>\<^sub>\<circ> c = K"
    unfolding dg_prod_components by auto
  from assms(1) have disjnt: "\<D>\<^sub>\<circ> b \<inter>\<^sub>\<circ> \<D>\<^sub>\<circ> c = 0" unfolding dom_b dom_c by auto

  show ?thesis
    unfolding dg_prod_components
  proof(intro vproductI)
    show "\<D>\<^sub>\<circ> (b \<union>\<^sub>\<circ> c) = J \<union>\<^sub>\<circ> K" by (auto simp: vdomain_vunion dom_b dom_c)
    show "\<forall>i\<in>\<^sub>\<circ>J \<union>\<^sub>\<circ> K. (b \<union>\<^sub>\<circ> c)\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>"
    proof(intro ballI)
      fix i assume prems: "i \<in>\<^sub>\<circ> J \<union>\<^sub>\<circ> K" 
      then consider (ib) \<open>i \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> b\<close> | (ic) \<open>i \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> c\<close> 
        unfolding dom_b dom_c by auto
      then show "(b \<union>\<^sub>\<circ> c)\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>"
      proof cases
        case ib
        with prems disjnt have bc_i: "(b \<union>\<^sub>\<circ> c)\<lparr>i\<rparr> = b\<lparr>i\<rparr>"
          by (auto intro!: vsv_vunion_app_left)
        from assms(2) ib show ?thesis unfolding bc_i dg_prod_components by auto
      next
        case ic 
        with prems disjnt have bc_i: "(b \<union>\<^sub>\<circ> c)\<lparr>i\<rparr> = c\<lparr>i\<rparr>"
          by (auto intro!: vsv_vunion_app_right)
        from assms(3) ic show ?thesis unfolding bc_i dg_prod_components by auto
      qed 
    qed
  qed (auto simp: disjnt)

qed

lemma dg_prod_vdiff_vunion_Obj_in_Obj:
  assumes "J \<subseteq>\<^sub>\<circ> I"
    and "b \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gk\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> k)\<lparr>Obj\<rparr>" 
    and "c \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>J. \<AA> j)\<lparr>Obj\<rparr>"
  shows "b \<union>\<^sub>\<circ> c \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"
  by 
    (
      vdiff_of_vunion 
        rule: dg_prod_vunion_Obj_in_Obj assms: assms(2,3) subset: assms(1)
    )

lemma dg_prod_vunion_Arr_in_Arr:
  assumes "vdisjnt J K" 
    and "b \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>J. \<AA> j)\<lparr>Arr\<rparr>" 
    and "c \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gk\<in>\<^sub>\<circ>K. \<AA> k)\<lparr>Arr\<rparr>"
  shows "b \<union>\<^sub>\<circ> c \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>J \<union>\<^sub>\<circ> K. \<AA> i)\<lparr>Arr\<rparr>"
  unfolding dg_prod_components
proof(intro vproductI)

  interpret b: vsv b using assms(2) unfolding dg_prod_components by clarsimp
  interpret c: vsv c using assms(3) unfolding dg_prod_components by clarsimp

  from assms have dom_b: "\<D>\<^sub>\<circ> b = J" and dom_c: "\<D>\<^sub>\<circ> c = K" 
    unfolding dg_prod_components by auto
  from assms have disjnt: "\<D>\<^sub>\<circ> b \<inter>\<^sub>\<circ> \<D>\<^sub>\<circ> c = 0" unfolding dom_b dom_c by auto

  from disjnt show "vsv (b \<union>\<^sub>\<circ> c)" by auto
  show dom_bc: "\<D>\<^sub>\<circ> (b \<union>\<^sub>\<circ> c) = J \<union>\<^sub>\<circ> K" 
    unfolding vdomain_vunion dom_b dom_c by auto

  show "\<forall>i\<in>\<^sub>\<circ>J \<union>\<^sub>\<circ> K. (b \<union>\<^sub>\<circ> c)\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Arr\<rparr>"
  proof(intro ballI)
    fix i assume prems: "i \<in>\<^sub>\<circ> J \<union>\<^sub>\<circ> K" 
    then consider (ib) \<open>i \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> b\<close> | (ic) \<open>i \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> c\<close> 
      unfolding dom_b dom_c by auto
    then show "(b \<union>\<^sub>\<circ> c)\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Arr\<rparr>"
    proof cases
      case ib
      with prems disjnt have bc_i: "(b \<union>\<^sub>\<circ> c)\<lparr>i\<rparr> = b\<lparr>i\<rparr>"
        by (auto intro!: vsv_vunion_app_left)
      from assms(2) ib show ?thesis unfolding bc_i dg_prod_components by auto
    next
      case ic 
      with prems disjnt have bc_i: "(b \<union>\<^sub>\<circ> c)\<lparr>i\<rparr> = c\<lparr>i\<rparr>"
        by (auto intro!: vsv_vunion_app_right)
      from assms(3) ic show ?thesis unfolding bc_i dg_prod_components by auto
    qed 
  qed

qed

lemma dg_prod_vdiff_vunion_Arr_in_Arr:
  assumes "J \<subseteq>\<^sub>\<circ> I"
    and "b \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gk\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> k)\<lparr>Arr\<rparr>" 
    and "c \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>J. \<AA> j)\<lparr>Arr\<rparr>"
  shows "b \<union>\<^sub>\<circ> c \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
  by 
    (
      vdiff_of_vunion 
        rule: dg_prod_vunion_Arr_in_Arr assms: assms(2,3) subset: assms(1)
    )

lemma (in pdigraph) pdg_dg_prod_vunion_is_arr:
  assumes "vdisjnt J K"
    and "J \<subseteq>\<^sub>\<circ> I"
    and "K \<subseteq>\<^sub>\<circ> I"
    and "g : a \<mapsto>\<^bsub>(\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>J. \<AA> j)\<^esub> b" 
    and "f : c \<mapsto>\<^bsub>(\<Prod>\<^sub>D\<^sub>Gk\<in>\<^sub>\<circ>K. \<AA> k)\<^esub> d"
  shows "g \<union>\<^sub>\<circ> f : a \<union>\<^sub>\<circ> c \<mapsto>\<^bsub>(\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>J \<union>\<^sub>\<circ> K. \<AA> i)\<^esub> b \<union>\<^sub>\<circ> d"
proof-

  interpret J\<AA>: pdigraph \<alpha> J \<AA> 
    using assms(2) by (simp add: pdg_vsubset_index_pdigraph)
  interpret K\<AA>: pdigraph \<alpha> K \<AA> 
    using assms(3) by (simp add: pdg_vsubset_index_pdigraph)
  interpret JK\<AA>: pdigraph \<alpha> \<open>J \<union>\<^sub>\<circ> K\<close> \<AA> 
    using assms(2,3) by (simp add: pdg_vsubset_index_pdigraph)

  show ?thesis
  proof(intro JK\<AA>.dg_prod_is_arrI)

    note gD = J\<AA>.dg_prod_is_arrD[OF assms(4)]
      and fD = K\<AA>.dg_prod_is_arrD[OF assms(5)]

    from assms(1) gD fD show
      "vsv (g \<union>\<^sub>\<circ> f)"
      "\<D>\<^sub>\<circ> (g \<union>\<^sub>\<circ> f) = J \<union>\<^sub>\<circ> K"
      "vsv (a \<union>\<^sub>\<circ> c)"
      "\<D>\<^sub>\<circ> (a \<union>\<^sub>\<circ> c) = J \<union>\<^sub>\<circ> K"
      "vsv (b \<union>\<^sub>\<circ> d)" 
      "\<D>\<^sub>\<circ> (b \<union>\<^sub>\<circ> d) = J \<union>\<^sub>\<circ> K"
      by (auto simp: vdomain_vunion)

    fix i assume "i \<in>\<^sub>\<circ> J \<union>\<^sub>\<circ> K"
    then consider (iJ) \<open>i \<in>\<^sub>\<circ> J\<close> | (iK) \<open>i \<in>\<^sub>\<circ> K\<close> by auto
    then show "(g \<union>\<^sub>\<circ> f)\<lparr>i\<rparr> : (a \<union>\<^sub>\<circ> c)\<lparr>i\<rparr> \<mapsto>\<^bsub>\<AA> i\<^esub> (b \<union>\<^sub>\<circ> d)\<lparr>i\<rparr>" 
    proof cases
      case iJ
      have gf_i: "(g \<union>\<^sub>\<circ> f)\<lparr>i\<rparr> = g\<lparr>i\<rparr>" by (simp add: iJ assms(1) gD(1,2) fD(1,2))        
      have ac_i: "(a \<union>\<^sub>\<circ> c)\<lparr>i\<rparr> = a\<lparr>i\<rparr>" by (simp add: iJ assms(1) gD(3,4) fD(3,4))
      have bd_i: "(b \<union>\<^sub>\<circ> d)\<lparr>i\<rparr> = b\<lparr>i\<rparr>" by (simp add: iJ assms(1) gD(5,6) fD(5,6))
      show ?thesis unfolding gf_i ac_i bd_i by (rule gD(7)[OF iJ])
    next
      case iK
      have gf_i: "(g \<union>\<^sub>\<circ> f)\<lparr>i\<rparr> = f\<lparr>i\<rparr>" by (simp add: iK assms(1) gD(1,2) fD(1,2))        
      have ac_i: "(a \<union>\<^sub>\<circ> c)\<lparr>i\<rparr> = c\<lparr>i\<rparr>" by (simp add: iK assms(1) gD(3,4) fD(3,4))
      have bd_i: "(b \<union>\<^sub>\<circ> d)\<lparr>i\<rparr> = d\<lparr>i\<rparr>" by (simp add: iK assms(1) gD(5,6) fD(5,6))
      show ?thesis unfolding gf_i ac_i bd_i by (rule fD(7)[OF iK])
    qed

  qed

qed

lemma (in pdigraph) pdg_dg_prod_vdiff_vunion_is_arr:
  assumes "J \<subseteq>\<^sub>\<circ> I"  
    and "g : a \<mapsto>\<^bsub>(\<Prod>\<^sub>D\<^sub>Gk\<in>\<^sub>\<circ>I -\<^sub>\<circ> J. \<AA> k)\<^esub> b" 
    and "f : c \<mapsto>\<^bsub>(\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>J. \<AA> j)\<^esub> d"
  shows "g \<union>\<^sub>\<circ> f : a \<union>\<^sub>\<circ> c \<mapsto>\<^bsub>\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i\<^esub> b \<union>\<^sub>\<circ> d"
  by 
    (
      vdiff_of_vunion' 
        rule: pdg_dg_prod_vunion_is_arr assms: assms(2,3) subset: assms(1)
    )



subsection\<open>Projection\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter II-3 in \cite{mac_lane_categories_2010}.\<close>

definition dghm_proj :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> V" (\<open>\<pi>\<^sub>D\<^sub>G\<close>)
  where "\<pi>\<^sub>D\<^sub>G I \<AA> i =
    [
      (\<lambda>a\<in>\<^sub>\<circ>((\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>). a\<lparr>i\<rparr>),
      (\<lambda>f\<in>\<^sub>\<circ>((\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>). f\<lparr>i\<rparr>),
      (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i),
      \<AA> i
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dghm_proj_components:
  shows "\<pi>\<^sub>D\<^sub>G I \<AA> i\<lparr>ObjMap\<rparr> = (\<lambda>a\<in>\<^sub>\<circ>((\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>). a\<lparr>i\<rparr>)"
    and "\<pi>\<^sub>D\<^sub>G I \<AA> i\<lparr>ArrMap\<rparr> = (\<lambda>f\<in>\<^sub>\<circ>((\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>). f\<lparr>i\<rparr>)"
    and "\<pi>\<^sub>D\<^sub>G I \<AA> i\<lparr>HomDom\<rparr> = (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)"
    and "\<pi>\<^sub>D\<^sub>G I \<AA> i\<lparr>HomCod\<rparr> = \<AA> i"
  unfolding dghm_proj_def dghm_field_simps by (simp_all add: nat_omega_simps)


text\<open>Object map.\<close>

mk_VLambda dghm_proj_components(1)
  |vsv dghm_proj_ObjMap_vsv[dg_cs_intros]|
  |vdomain dghm_proj_ObjMap_vdomain[dg_cs_simps]|
  |app dghm_proj_ObjMap_app[dg_cs_simps]|

lemma (in pdigraph) dghm_proj_ObjMap_vrange: 
  assumes "i \<in>\<^sub>\<circ> I"
  shows "\<R>\<^sub>\<circ> (\<pi>\<^sub>D\<^sub>G I \<AA> i\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>"
  using assms 
  unfolding dghm_proj_components
  by (intro vrange_VLambda_vsubset) (clarsimp simp: dg_prod_components)


text\<open>Arrow map.\<close>

mk_VLambda dghm_proj_components(2)
  |vsv dghm_proj_ArrMap_vsv[dg_cs_intros]|
  |vdomain dghm_proj_ArrMap_vdomain[dg_cs_simps]|
  |app dghm_proj_ArrMap_app[dg_cs_simps]|

lemma (in pdigraph) dghm_proj_ArrMap_vrange: 
  assumes "i \<in>\<^sub>\<circ> I"
  shows "\<R>\<^sub>\<circ> (\<pi>\<^sub>D\<^sub>G I \<AA> i\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<AA> i\<lparr>Arr\<rparr>"
  using assms 
  unfolding dghm_proj_components
  by (intro vrange_VLambda_vsubset) (clarsimp simp: dg_prod_components)


subsubsection\<open>A projection digraph homomorphism is a digraph homomorphism\<close>

lemma (in pdigraph) pdg_dghm_proj_is_dghm: 
  assumes "i \<in>\<^sub>\<circ> I" 
  shows "\<pi>\<^sub>D\<^sub>G I \<AA> i : (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i) \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA> i"
proof(intro is_dghmI)
  show "vfsequence (\<pi>\<^sub>D\<^sub>G I \<AA> i)" unfolding dghm_proj_def by auto
  show "vcard (\<pi>\<^sub>D\<^sub>G I \<AA> i) = 4\<^sub>\<nat>"
    unfolding dghm_proj_def by (simp add: nat_omega_simps)
  show "\<pi>\<^sub>D\<^sub>G I \<AA> i\<lparr>HomDom\<rparr> = (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)"
    unfolding dghm_proj_components by simp
  show "\<pi>\<^sub>D\<^sub>G I \<AA> i\<lparr>HomCod\<rparr> = \<AA> i" 
    unfolding dghm_proj_components by simp
  fix f a b assume "f : a \<mapsto>\<^bsub>\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i\<^esub> b"
  with assms pdg_digraph_dg_prod show 
    "\<pi>\<^sub>D\<^sub>G I \<AA> i\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> : \<pi>\<^sub>D\<^sub>G I \<AA> i\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<AA> i\<^esub> \<pi>\<^sub>D\<^sub>G I \<AA> i\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros dg_prod_is_arrD(7))
qed 
  (
    auto simp: 
      dg_cs_simps dg_cs_intros dg_prod_cs_intros
      assms pdg_digraph_dg_prod dghm_proj_ObjMap_vrange
  )

lemma (in pdigraph) pdg_dghm_proj_is_dghm':
  assumes "i \<in>\<^sub>\<circ> I" and "\<CC> = (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)" and "\<DD> = \<AA> i"
  shows "\<pi>\<^sub>D\<^sub>G I \<AA> i : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms(1) unfolding assms(2,3) by (rule pdg_dghm_proj_is_dghm)

lemmas [dg_cs_intros] = pdigraph.pdg_dghm_proj_is_dghm'



subsection\<open>Digraph product universal property digraph homomorphism\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The following digraph homomorphism is used in the 
proof of the universal property of the product digraph 
later in this work.
\<close>

definition dghm_up :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "dghm_up I \<AA> \<CC> \<phi> =
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. (\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)),
      (\<lambda>f\<in>\<^sub>\<circ>\<CC>\<lparr>Arr\<rparr>. (\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>)),
      \<CC>,
      (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dghm_up_components: 
  shows "dghm_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr> = (\<lambda>a\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. (\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>))"
    and "dghm_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr> = (\<lambda>f\<in>\<^sub>\<circ>\<CC>\<lparr>Arr\<rparr>. (\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>))"
    and "dghm_up I \<AA> \<CC> \<phi>\<lparr>HomDom\<rparr> = \<CC>"
    and "dghm_up I \<AA> \<CC> \<phi>\<lparr>HomCod\<rparr> = (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)"
  unfolding dghm_up_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

mk_VLambda dghm_up_components(1)
  |vsv dghm_up_ObjMap_vsv[dg_cs_intros]|
  |vdomain dghm_up_ObjMap_vdomain[dg_cs_simps]|
  |app dghm_up_ObjMap_app|

lemma dghm_up_ObjMap_vrange: 
  assumes "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA> i"
  shows "\<R>\<^sub>\<circ> (dghm_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"
  unfolding dghm_up_components dg_prod_components
proof(intro vrange_VLambda_vsubset vproductI)
  fix a assume prems: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  show "\<forall>i\<in>\<^sub>\<circ>I. (\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>"
  proof(intro ballI)
    fix i assume prems': "i \<in>\<^sub>\<circ> I"
    interpret \<phi>: is_dghm \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (rule assms[OF prems'])
    from prems prems' show "(\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>" 
      by (simp add: \<phi>.dghm_ObjMap_app_in_HomCod_Obj)
  qed
qed auto

lemma dghm_up_ObjMap_app_vdomain[dg_cs_simps]: 
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (dghm_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) = I"
  unfolding dghm_up_ObjMap_app[OF assms] by simp

lemma dghm_up_ObjMap_app_component[dg_cs_simps]: 
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "i \<in>\<^sub>\<circ> I"
  shows "dghm_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<lparr>i\<rparr> = \<phi> i\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
  using assms unfolding dghm_up_components by simp

lemma dghm_up_ObjMap_app_vrange: 
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA> i"
  shows "\<R>\<^sub>\<circ> (dghm_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>) \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Obj\<rparr>)"
proof(intro vsubsetI)
  fix b assume prems: "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (dghm_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)"
  have "vsv (dghm_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>)"
    unfolding dghm_up_ObjMap_app[OF assms(1)] by auto
  with prems obtain i where b_def: "b = dghm_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<lparr>i\<rparr>" 
    and i: "i \<in>\<^sub>\<circ> I"
    by (auto elim: vsv.vrange_atE simp: dghm_up_ObjMap_app[OF assms(1)])
  interpret \<phi>i: is_dghm \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (rule assms(2)[OF i])
  from dghm_up_ObjMap_app_component[OF assms(1) i] b_def have b_def':
    "b = \<phi> i\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    by simp
  from assms(1) have "b \<in>\<^sub>\<circ> \<AA> i\<lparr>Obj\<rparr>" 
    unfolding b_def' by (auto intro: dg_cs_intros)
  with i show "b \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Obj\<rparr>)" by force
qed


subsubsection\<open>Arrow map\<close>

mk_VLambda dghm_up_components(2)
  |vsv dghm_up_ArrMap_vsv[dg_cs_intros]|
  |vdomain dghm_up_ArrMap_vdomain[dg_cs_simps]|
  |app dghm_up_ArrMap_app|

lemma (in pdigraph) dghm_up_ArrMap_vrange: 
  assumes "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA> i"
  shows "\<R>\<^sub>\<circ> (dghm_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
  unfolding dghm_up_components dg_prod_components
proof(intro vrange_VLambda_vsubset vproductI)
  fix a assume prems: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  show "\<forall>i\<in>\<^sub>\<circ>I. (\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>)\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Arr\<rparr>"
  proof(intro ballI)
    fix i assume prems': "i \<in>\<^sub>\<circ> I"
    interpret \<phi>: is_dghm \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (rule assms[OF prems'])
    from prems prems' show "(\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>)\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Arr\<rparr>" 
      by (auto intro: dg_cs_intros)
  qed
qed auto

lemma dghm_up_ArrMap_vrange: 
  assumes "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA> i"
  shows "\<R>\<^sub>\<circ> (dghm_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
proof(intro vsubsetI)
  fix A assume "A \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (dghm_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>)"
  then obtain a where A_def: "A = dghm_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>" 
    and a: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    unfolding dghm_up_ArrMap_vdomain dghm_up_components by auto
  have "(\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>) \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>)"
  proof(intro vproductI)
    show "\<forall>i\<in>\<^sub>\<circ>I. (\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>)\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Arr\<rparr>"
    proof(intro ballI)
      fix i assume prems: "i \<in>\<^sub>\<circ> I"
      interpret \<phi>: is_dghm \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (rule assms[OF prems])
      from prems a show "(\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>)\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<AA> i\<lparr>Arr\<rparr>" 
        by (auto intro: dg_cs_intros)
    qed
  qed simp_all
  with a show "A \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Arr\<rparr>"
    unfolding A_def dg_prod_components dghm_up_components by simp
qed

lemma dghm_up_ArrMap_app_vdomain[dg_cs_simps]: 
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  shows "\<D>\<^sub>\<circ> (dghm_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>) = I"
  unfolding dghm_up_ArrMap_app[OF assms] by simp

lemma dghm_up_ArrMap_app_component[dg_cs_simps]: 
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" and "i \<in>\<^sub>\<circ> I"
  shows "dghm_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>\<lparr>i\<rparr> = \<phi> i\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>"
  using assms unfolding dghm_up_components by simp

lemma dghm_up_ArrMap_app_vrange: 
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA> i"
  shows "\<R>\<^sub>\<circ> (dghm_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>) \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>)"
proof(intro vsubsetI)
  fix b assume prems: "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (dghm_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>)"
  have "vsv (dghm_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>)"
    unfolding dghm_up_ArrMap_app[OF assms(1)] by auto
  with prems obtain i where b_def: "b = dghm_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>\<lparr>i\<rparr>" 
    and i: "i \<in>\<^sub>\<circ> I"
    by (auto elim: vsv.vrange_atE simp: dghm_up_ArrMap_app[OF assms(1)])
  interpret \<phi>i: is_dghm \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (rule assms(2)[OF i])
  from dghm_up_ArrMap_app_component[OF assms(1) i] b_def have b_def':
    "b = \<phi> i\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>"
    by simp
  from assms(1) have "b \<in>\<^sub>\<circ> \<AA> i\<lparr>Arr\<rparr>" 
    unfolding b_def' by (auto intro: dg_cs_intros)
  with i show "b \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. \<AA> i\<lparr>Arr\<rparr>)" by force
qed


subsubsection\<open>
Digraph product universal property 
digraph homomorphism is a digraph homomorphism
\<close>

lemma (in pdigraph) pdg_dghm_up_is_dghm:
  assumes "digraph \<alpha> \<CC>" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA> i"
  shows "dghm_up I \<AA> \<CC> \<phi> : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)"
proof-
  interpret \<CC>: digraph \<alpha> \<CC> by (rule assms(1))
  show ?thesis
  proof(intro is_dghmI, unfold dghm_up_components(3,4))
    show "vfsequence (dghm_up I \<AA> \<CC> \<phi>)" unfolding dghm_up_def by simp
    show "vcard (dghm_up I \<AA> \<CC> \<phi>) = 4\<^sub>\<nat>"
      unfolding dghm_up_def by (simp add: nat_omega_simps)
    from assms(2) show "\<R>\<^sub>\<circ> (dghm_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<lparr>Obj\<rparr>"
      by (intro dghm_up_ObjMap_vrange) blast
    fix f a b assume prems: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    then have f: "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" and a: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and b: "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
    show "dghm_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> :
      dghm_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i\<^esub> dghm_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    proof(rule dg_prod_is_arrI)
      fix i assume prems': "i \<in>\<^sub>\<circ> I"
      interpret \<phi>: is_dghm \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (rule assms(2)[OF prems'])
      from \<phi>.is_dghm_axioms \<CC>.digraph_axioms prems pdigraph_axioms prems prems' 
      show "dghm_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<lparr>i\<rparr> : 
        dghm_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<lparr>i\<rparr> \<mapsto>\<^bsub>\<AA> i\<^esub> dghm_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<lparr>i\<rparr>"
        by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
    qed (simp_all add: f a b dghm_up_ArrMap_app dghm_up_ObjMap_app)
  qed (auto simp: dghm_up_components pdg_digraph_dg_prod dg_cs_intros)
qed


subsubsection\<open>Further properties\<close>

lemma (in pdigraph) pdg_dghm_comp_dghm_proj_dghm_up: 
  assumes "digraph \<alpha> \<CC>"
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA> i" 
    and "i \<in>\<^sub>\<circ> I" 
  shows "\<phi> i = \<pi>\<^sub>D\<^sub>G I \<AA> i \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_up I \<AA> \<CC> \<phi>"
proof(rule dghm_eqI[of \<alpha> \<CC> \<open>\<AA> i\<close> _ \<CC> \<open>\<AA> i\<close>])
  
  interpret \<phi>: is_dghm \<alpha> \<CC> \<open>\<AA> i\<close> \<open>\<phi> i\<close> by (rule assms(2)[OF assms(3)])
  
  show "\<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA> i" by (auto intro: dg_cs_intros)

  from assms(1,2) have dghm_up: "dghm_up I \<AA> \<CC> \<phi> : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)"
    by (simp add: pdg_dghm_up_is_dghm)
  note dghm_proj = pdg_dghm_proj_is_dghm[OF assms(3)]

  from assms(3) pdg_dghm_proj_is_dghm show
    "\<pi>\<^sub>D\<^sub>G I \<AA> i \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_up I \<AA> \<CC> \<phi> : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA> i"
    by (intro dghm_comp_is_dghm[of \<alpha> \<open>(\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<close>]) 
      (auto simp: assms dghm_up)
  
  show "\<phi> i\<lparr>ObjMap\<rparr> = (\<pi>\<^sub>D\<^sub>G I \<AA> i \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_up I \<AA> \<CC> \<phi>)\<lparr>ObjMap\<rparr>"
  proof(rule vsv_eqI)
    show "vsv ((\<pi>\<^sub>D\<^sub>G I \<AA> i \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_up I \<AA> \<CC> \<phi>)\<lparr>ObjMap\<rparr>)"
      unfolding dghm_comp_components dghm_proj_components dghm_up_components 
      by (rule vsv_vcomp) simp_all
    from 
      dghm_up_ObjMap_vrange[
        OF assms(2), simplified, unfolded dg_prod_components
        ]
    have rd: "\<R>\<^sub>\<circ> (dghm_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<pi>\<^sub>D\<^sub>G I \<AA> i\<lparr>ObjMap\<rparr>)"
      by (simp add: dg_prod_components dg_cs_simps)
    show "\<D>\<^sub>\<circ> (\<phi> i\<lparr>ObjMap\<rparr>) = \<D>\<^sub>\<circ> ((\<pi>\<^sub>D\<^sub>G I \<AA> i \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_up I \<AA> \<CC> \<phi>)\<lparr>ObjMap\<rparr>)"
      unfolding dghm_comp_components vdomain_vcomp_vsubset[OF rd] 
      by (simp add: dg_cs_simps)
    fix a assume "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<phi> i\<lparr>ObjMap\<rparr>)"
    then have a: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by (simp add: dg_cs_simps) 
    with dghm_up dghm_proj assms(3) show 
      "\<phi> i\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = (\<pi>\<^sub>D\<^sub>G I \<AA> i \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_up I \<AA> \<CC> \<phi>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  qed auto

  show "\<phi> i\<lparr>ArrMap\<rparr> = (\<pi>\<^sub>D\<^sub>G I \<AA> i \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_up I \<AA> \<CC> \<phi>)\<lparr>ArrMap\<rparr>"
  proof(rule vsv_eqI)
    show "vsv ((\<pi>\<^sub>D\<^sub>G I \<AA> i \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_up I \<AA> \<CC> \<phi>)\<lparr>ArrMap\<rparr>)"
      unfolding dghm_comp_components dghm_proj_components dghm_up_components 
      by (rule vsv_vcomp) simp_all
    from 
      dghm_up_ArrMap_vrange[
        OF assms(2), simplified, unfolded dg_prod_components
        ]
    have rd: "\<R>\<^sub>\<circ> (dghm_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<pi>\<^sub>D\<^sub>G I \<AA> i\<lparr>ArrMap\<rparr>)"
      by (simp add: dg_prod_components dg_cs_simps)
    show "\<D>\<^sub>\<circ> (\<phi> i\<lparr>ArrMap\<rparr>) = \<D>\<^sub>\<circ> ((\<pi>\<^sub>D\<^sub>G I \<AA> i \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_up I \<AA> \<CC> \<phi>)\<lparr>ArrMap\<rparr>)"
      unfolding dghm_comp_components vdomain_vcomp_vsubset[OF rd] 
      by (simp add: dg_cs_simps)
    fix a assume "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<phi> i\<lparr>ArrMap\<rparr>)"
    then have a: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" by (simp add: dg_cs_simps)
    with dghm_up dghm_proj assms(3) show 
      "\<phi> i\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> = (\<pi>\<^sub>D\<^sub>G I \<AA> i \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M dghm_up I \<AA> \<CC> \<phi>)\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>"
      by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  qed auto

qed simp_all
      
lemma (in pdigraph) pdg_dghm_up_eq_dghm_proj:
  assumes "\<FF> : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)"
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i = \<pi>\<^sub>D\<^sub>G I \<AA> i \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>"
  shows "dghm_up I \<AA> \<CC> \<phi> = \<FF>"
proof(rule dghm_eqI)

  interpret \<FF>: is_dghm \<alpha> \<CC> \<open>(\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<close> \<FF> by (rule assms(1))

  show "dghm_up I \<AA> \<CC> \<phi> : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)"
  proof(rule pdg_dghm_up_is_dghm)
    fix i assume prems: "i \<in>\<^sub>\<circ> I"
    interpret \<pi>: is_dghm \<alpha> \<open>(\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>I. \<AA> i)\<close> \<open>\<AA> i\<close> \<open>\<pi>\<^sub>D\<^sub>G I \<AA> i\<close>
      using prems by (rule pdg_dghm_proj_is_dghm)
    show "\<phi> i : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA> i" 
      unfolding assms(2)[OF prems] by (auto intro: dg_cs_intros)
  qed (auto intro: dg_cs_intros)

  show "dghm_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr> = \<FF>\<lparr>ObjMap\<rparr>"
  proof(rule vsv_eqI, unfold dghm_up_ObjMap_vdomain)
    fix a assume prems: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    show "dghm_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    proof(rule vsv_eqI, unfold dghm_up_ObjMap_app_vdomain[OF prems])
      fix i assume prems': "i \<in>\<^sub>\<circ> I"
      with pdg_dghm_proj_is_dghm[OF prems'] \<FF>.is_dghm_axioms prems show 
        "dghm_up I \<AA> \<CC> \<phi>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<lparr>i\<rparr> = \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<lparr>i\<rparr>"
        by (cs_concl cs_simp: dg_cs_simps assms(2) cs_intro: dg_cs_intros)
    qed 
      (
        use \<FF>.dghm_ObjMap_app_in_HomCod_Obj prems in 
          \<open>auto simp: dg_prod_components dghm_up_ObjMap_app\<close>
      )
  qed (auto simp: dghm_up_components dg_cs_simps)

  show "dghm_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr> = \<FF>\<lparr>ArrMap\<rparr>"
  proof(rule vsv_eqI, unfold dghm_up_ArrMap_vdomain)
    fix a assume prems: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    show "dghm_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>"
    proof(rule vsv_eqI, unfold dghm_up_ArrMap_app_vdomain[OF prems])
      fix i assume prems': "i \<in>\<^sub>\<circ> I"
      with pdg_dghm_proj_is_dghm[OF prems'] \<FF>.is_dghm_axioms prems show 
        "dghm_up I \<AA> \<CC> \<phi>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>\<lparr>i\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>\<lparr>i\<rparr>"
        by (cs_concl cs_simp: dg_cs_simps assms(2) cs_intro: dg_cs_intros)
    qed 
      (
        use \<FF>.dghm_ArrMap_app_in_HomCod_Arr prems in 
          \<open>auto simp: dg_prod_components dghm_up_ArrMap_app\<close>
      )+
  qed (auto simp: dghm_up_components dg_cs_simps)

qed (simp_all add: assms(1))



subsection\<open>Singleton digraph\<close>


subsubsection\<open>Object\<close>

lemma dg_singleton_ObjI: 
  assumes "A = set {\<langle>j, a\<rangle>}" and "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "A \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>set {j}. \<CC>)\<lparr>Obj\<rparr>"
  using assms unfolding dg_prod_components by auto

lemma dg_singleton_ObjE: 
  assumes "A \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>set {j}. \<CC>)\<lparr>Obj\<rparr>"
  obtains a where "A = set {\<langle>j, a\<rangle>}" and "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
proof-
  from vproductD[OF assms[unfolded dg_prod_components], rule_format] 
  have "vsv A" and [simp]: "\<D>\<^sub>\<circ> A = set {j}" and Aj: "A\<lparr>j\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    by simp_all
  then interpret A: vsv A by simp
  from A.vsv_is_VLambda have "A = set {\<langle>j, A\<lparr>j\<rparr>\<rangle>}" 
    by (auto simp: VLambda_vsingleton)
  with Aj show ?thesis using that by simp
qed


subsubsection\<open>Arrow\<close>

lemma dg_singleton_ArrI: 
  assumes "F = set {\<langle>j, a\<rangle>}" and "a \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  shows "F \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>set {j}. \<CC>)\<lparr>Arr\<rparr>"
  using assms unfolding dg_prod_components by auto

lemma dg_singleton_ArrE: 
  assumes "F \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>set {j}. \<CC>)\<lparr>Arr\<rparr>"
  obtains a where "F = set {\<langle>j, a\<rangle>}" and "a \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof-
  from vproductD[OF assms[unfolded dg_prod_components], rule_format] 
  have "vsv F" and [simp]: "\<D>\<^sub>\<circ> F = set {j}" and Fj: "F\<lparr>j\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    by simp_all
  then interpret F: vsv F by simp
  from F.vsv_is_VLambda have "F = set {\<langle>j, F\<lparr>j\<rparr>\<rangle>}" 
    by (auto simp: VLambda_vsingleton)
  with Fj show ?thesis using that by simp
qed


subsubsection\<open>Singleton digraph is a digraph\<close>

lemma (in digraph) dg_finite_pdigraph_dg_singleton: 
  assumes "j \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "finite_pdigraph \<alpha> (set {j}) (\<lambda>i. \<CC>)"
  by (intro finite_pdigraphI pdigraph_baseI)
    (auto simp: digraph_axioms Limit_vsingleton_in_VsetI assms)

lemma (in digraph) dg_digraph_dg_singleton:
  assumes "j \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "digraph \<alpha> (\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>set {j}. \<CC>)"
proof-
  interpret finite_pdigraph \<alpha> \<open>set {j}\<close> \<open>\<lambda>i. \<CC>\<close>
    using assms by (rule dg_finite_pdigraph_dg_singleton)
  show ?thesis by (rule pdg_digraph_dg_prod)
qed


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma (in digraph) dg_singleton_is_arrI:
  assumes "j \<in>\<^sub>\<circ> Vset \<alpha>" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "set {\<langle>j, f\<rangle>} : set {\<langle>j, a\<rangle>} \<mapsto>\<^bsub>(\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>set {j}. \<CC>)\<^esub> set {\<langle>j, b\<rangle>}"
proof-
  interpret finite_pdigraph \<alpha> \<open>set {j}\<close> \<open>\<lambda>i. \<CC>\<close>
    by (rule dg_finite_pdigraph_dg_singleton[OF assms(1)])
  from assms(2) show ?thesis by (intro dg_prod_is_arrI) auto
qed

lemma (in digraph) dg_singleton_is_arrD:
  assumes "set {\<langle>j, f\<rangle>} : set {\<langle>j, a\<rangle>} \<mapsto>\<^bsub>(\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>set {j}. \<CC>)\<^esub> set {\<langle>j, b\<rangle>}" 
    and "j \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
proof-
  interpret finite_pdigraph \<alpha> \<open>set {j}\<close> \<open>\<lambda>i. \<CC>\<close>
    by (rule dg_finite_pdigraph_dg_singleton[OF assms(2)])
  from dg_prod_is_arrD(7)[OF assms(1)] show ?thesis by simp
qed

lemma (in digraph) dg_singleton_is_arrE:
  assumes "set {\<langle>j, f\<rangle>} : set {\<langle>j, a\<rangle>} \<mapsto>\<^bsub>(\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>set {j}. \<CC>)\<^esub> set {\<langle>j, b\<rangle>}" 
    and "j \<in>\<^sub>\<circ> Vset \<alpha>"
  obtains "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  using assms dg_singleton_is_arrD by auto



subsection\<open>Singleton digraph homomorphism\<close>

definition dghm_singleton :: "V \<Rightarrow> V \<Rightarrow> V"
  where "dghm_singleton j \<CC> = 
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. set {\<langle>j, a\<rangle>}), 
      (\<lambda>f\<in>\<^sub>\<circ>\<CC>\<lparr>Arr\<rparr>. set {\<langle>j, f\<rangle>}), 
      \<CC>,
      (\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>set {j}. \<CC>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dghm_singleton_components:
  shows "dghm_singleton j \<CC>\<lparr>ObjMap\<rparr> = (\<lambda>a\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. set {\<langle>j, a\<rangle>})"
    and "dghm_singleton j \<CC>\<lparr>ArrMap\<rparr> = (\<lambda>f\<in>\<^sub>\<circ>\<CC>\<lparr>Arr\<rparr>. set {\<langle>j, f\<rangle>})"
    and "dghm_singleton j \<CC>\<lparr>HomDom\<rparr> = \<CC>"
    and "dghm_singleton j \<CC>\<lparr>HomCod\<rparr> = (\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>set {j}. \<CC>)"
  unfolding dghm_singleton_def dghm_field_simps 
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

mk_VLambda dghm_singleton_components(1)
  |vsv dghm_singleton_ObjMap_vsv[dg_cs_intros]|
  |vdomain dghm_singleton_ObjMap_vdomain[dg_cs_simps]|
  |app dghm_singleton_ObjMap_app[dg_prod_cs_simps]|

lemma dghm_singleton_ObjMap_vrange[dg_cs_simps]: 
  "\<R>\<^sub>\<circ> (dghm_singleton j \<CC>\<lparr>ObjMap\<rparr>) = (\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>set {j}. \<CC>)\<lparr>Obj\<rparr>"
proof(intro vsubset_antisym vsubsetI)
  fix A assume "A \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (dghm_singleton j \<CC>\<lparr>ObjMap\<rparr>)"
  then obtain a where A_def: "A = set {\<langle>j, a\<rangle>}" and a: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    unfolding dghm_singleton_components by auto
  then show "A \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>set {j}. \<CC>)\<lparr>Obj\<rparr>"
    unfolding dg_prod_components by auto
next
  fix A assume "A \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>set {j}. \<CC>)\<lparr>Obj\<rparr>" 
  from vproductD[OF this[unfolded dg_prod_components], rule_format] 
  have "vsv A"
    and [simp]: "\<D>\<^sub>\<circ> A = set {j}" 
    and Ai: "\<And>i. i \<in>\<^sub>\<circ> set {j} \<Longrightarrow> A\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    by auto
  then interpret A: vsv A by simp
  from Ai have "A\<lparr>j\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" using Ai by auto
  moreover with A.vsv_is_VLambda have "A = (\<lambda>f\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. set {\<langle>j, f\<rangle>})\<lparr>A\<lparr>j\<rparr>\<rparr>"
    by (simp add: VLambda_vsingleton)
  ultimately show "A \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (dghm_singleton j \<CC>\<lparr>ObjMap\<rparr>)"
    unfolding dghm_singleton_components
    by 
      (
        metis 
          dghm_singleton_ObjMap_vdomain 
          dghm_singleton_ObjMap_vsv 
          dghm_singleton_components(1) 
          vsv.vsv_vimageI2
      )
qed


subsubsection\<open>Arrow map\<close>

mk_VLambda dghm_singleton_components(2)
  |vsv dghm_singleton_ArrMap_vsv[dg_cs_intros]|
  |vdomain dghm_singleton_ArrMap_vdomain[dg_cs_simps]|
  |app dghm_singleton_ArrMap_app[dg_prod_cs_simps]|

lemma dghm_singleton_ArrMap_vrange[dg_cs_simps]: 
  "\<R>\<^sub>\<circ> (dghm_singleton j \<CC>\<lparr>ArrMap\<rparr>) = (\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>set {j}. \<CC>)\<lparr>Arr\<rparr>"
proof(intro vsubset_antisym vsubsetI)
  fix F assume "F \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (dghm_singleton j \<CC>\<lparr>ArrMap\<rparr>)"
  then obtain f where "F = set {\<langle>j, f\<rangle>}" and "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" 
    unfolding dghm_singleton_components by auto
  then show "F \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>set {j}. \<CC>)\<lparr>Arr\<rparr>"
    unfolding dg_prod_components by auto
next
  fix F assume "F \<in>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>set {j}. \<CC>)\<lparr>Arr\<rparr>" 
  from vproductD[OF this[unfolded dg_prod_components], rule_format] 
  have "vsv F"
    and [simp]: "\<D>\<^sub>\<circ> F = set {j}" 
    and Fi: "\<And>i. i \<in>\<^sub>\<circ> set {j} \<Longrightarrow> F\<lparr>i\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    by auto
  then interpret F: vsv F by simp
  from Fi have "F\<lparr>j\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" using Fi by auto
  moreover with F.vsv_is_VLambda have "F = (\<lambda>f\<in>\<^sub>\<circ>\<CC>\<lparr>Arr\<rparr>. set {\<langle>j, f\<rangle>})\<lparr>F\<lparr>j\<rparr>\<rparr>"
    by (simp add: VLambda_vsingleton)
  ultimately show "F \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (dghm_singleton j \<CC>\<lparr>ArrMap\<rparr>)"
    unfolding dghm_singleton_components
    by 
      (
        metis 
          dghm_singleton_ArrMap_vdomain 
          dghm_singleton_ArrMap_vsv 
          dghm_singleton_components(2) 
          vsv.vsv_vimageI2
      )
qed


subsubsection\<open>Singleton digraph homomorphism is an isomorphism of digraphs\<close>

lemma (in digraph) dg_dghm_singleton_is_dghm:
  assumes "j \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "dghm_singleton j \<CC> : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> (\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>set {j}. \<CC>)"
proof-
  interpret finite_pdigraph \<alpha> \<open>set {j}\<close> \<open>\<lambda>i. \<CC>\<close>
    by (rule dg_finite_pdigraph_dg_singleton[OF assms])
  show ?thesis
  proof(intro is_iso_dghmI is_dghmI)
    show "vfsequence (dghm_singleton j \<CC>)" unfolding dghm_singleton_def by simp
    show "vcard (dghm_singleton j \<CC>) = 4\<^sub>\<nat>"
      unfolding dghm_singleton_def by (simp add: nat_omega_simps)
    show "\<R>\<^sub>\<circ> (dghm_singleton j \<CC>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>set {j}. \<CC>)\<lparr>Obj\<rparr>"
      by (simp add: dg_cs_simps)
    show "dghm_singleton j \<CC>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> :
      dghm_singleton j \<CC>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>set {j}. \<CC>\<^esub> 
      dghm_singleton j \<CC>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      if "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" for f a b
      using that
    proof(intro dg_prod_is_arrI)
      fix k assume "k \<in>\<^sub>\<circ> set {j}"
      then have k_def: "k = j" by simp
      from that show "dghm_singleton j \<CC>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>\<lparr>k\<rparr> :
        dghm_singleton j \<CC>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>\<lparr>k\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> dghm_singleton j \<CC>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>\<lparr>k\<rparr>"
        by 
          (
            cs_concl 
              cs_simp: k_def V_cs_simps dg_cs_simps dg_prod_cs_simps
              cs_intro: dg_cs_intros
          )
    qed 
      (
        cs_concl 
          cs_simp: V_cs_simps dg_prod_cs_simps 
          cs_intro: V_cs_intros dg_cs_intros
      )+
    show "\<R>\<^sub>\<circ> (dghm_singleton j \<CC>\<lparr>ObjMap\<rparr>) = (\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>set {j}. \<CC>)\<lparr>Obj\<rparr>" 
      by (simp add: dg_cs_simps)
    show "\<R>\<^sub>\<circ> (dghm_singleton j \<CC>\<lparr>ArrMap\<rparr>) = (\<Prod>\<^sub>D\<^sub>Gj\<in>\<^sub>\<circ>set {j}. \<CC>)\<lparr>Arr\<rparr>" 
      by (simp add: dg_cs_simps)
  qed 
    (
      auto simp: 
        dg_cs_intros 
        dg_digraph_dg_singleton[OF assms] 
        dghm_singleton_components
    )
qed



subsection\<open>Product of two digraphs\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter II-3 in \cite{mac_lane_categories_2010}.\<close>

definition dg_prod_2 :: "V \<Rightarrow> V \<Rightarrow> V" (infixr \<open>\<times>\<^sub>D\<^sub>G\<close> 80)
  where "\<AA> \<times>\<^sub>D\<^sub>G \<BB> \<equiv> dg_prod (2\<^sub>\<nat>) (if2 \<AA> \<BB>)"


subsubsection\<open>Product of two digraphs is a digraph\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "digraph \<alpha> \<AA>" and \<BB>: "digraph \<alpha> \<BB>"
begin

interpretation \<Z> \<alpha> by (rule digraphD[OF \<AA>(1)])
interpretation \<AA>: digraph \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: digraph \<alpha> \<BB> by (rule \<BB>)

lemma finite_pdigraph_dg_prod_2: "finite_pdigraph \<alpha> (2\<^sub>\<nat>) (if2 \<AA> \<BB>)"
proof(intro finite_pdigraphI pdigraph_baseI)
  from Axiom_of_Infinity show z1_in_Vset: "2\<^sub>\<nat> \<in>\<^sub>\<circ> Vset \<alpha>" by blast
  show "digraph \<alpha> (i = 0 ? \<AA> : \<BB>)" if "i \<in>\<^sub>\<circ> 2\<^sub>\<nat>" for i
    by (auto intro: dg_cs_intros)
qed auto

interpretation finite_pdigraph \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 \<AA> \<BB>\<close>
  by (intro finite_pdigraph_dg_prod_2 \<AA> \<BB>)

lemma digraph_dg_prod_2[dg_cs_intros]: "digraph \<alpha> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)"
proof-
  show ?thesis unfolding dg_prod_2_def by (rule pdg_digraph_dg_prod)
qed

end


subsubsection\<open>Object\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "digraph \<alpha> \<AA>" and \<BB>: "digraph \<alpha> \<BB>"
begin

lemma dg_prod_2_ObjI:
  assumes "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Obj\<rparr>"
  unfolding dg_prod_2_def dg_prod_components
proof(intro vproductI ballI)
  show "\<D>\<^sub>\<circ> [a, b]\<^sub>\<circ> = 2\<^sub>\<nat>" by (simp add: nat_omega_simps two)
  fix i assume "i \<in>\<^sub>\<circ> 2\<^sub>\<nat>"
  then consider \<open>i = 0\<close> | \<open>i = 1\<^sub>\<nat>\<close> unfolding two by auto 
  then show "[a, b]\<^sub>\<circ>\<lparr>i\<rparr> \<in>\<^sub>\<circ> (if i = 0 then \<AA> else \<BB>)\<lparr>Obj\<rparr>"
    by cases (simp_all add: nat_omega_simps assms(1,2))
qed auto

lemma dg_prod_2_ObjI'[dg_prod_cs_intros]:
  assumes "ab = [a, b]\<^sub>\<circ>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Obj\<rparr>"
  using assms(2,3) unfolding assms(1) by (rule dg_prod_2_ObjI)

lemma dg_prod_2_ObjE:
  assumes "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Obj\<rparr>"
  obtains a b where "ab = [a, b]\<^sub>\<circ>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
proof-
  from vproductD[OF assms[unfolded dg_prod_2_def dg_prod_components]]
  have vsv_ab: "vsv ab"
    and dom_ab: "\<D>\<^sub>\<circ> ab = 2\<^sub>\<nat>"
    and ab_app: "\<And>i. i \<in>\<^sub>\<circ> 2\<^sub>\<nat> \<Longrightarrow> ab\<lparr>i\<rparr> \<in>\<^sub>\<circ> (if i = 0 then \<AA> else \<BB>)\<lparr>Obj\<rparr>"
    by auto
  have dom_ab[simp]: "\<D>\<^sub>\<circ> ab = 2\<^sub>\<nat>"
    unfolding dom_ab by (simp add: nat_omega_simps two)
  interpret vsv ab by (rule vsv_ab)
  have "ab = [vpfst ab, vpsnd ab]\<^sub>\<circ>"
    by (rule vsv_vfsequence_two[symmetric]) auto
  moreover from ab_app[of 0] have "vpfst ab \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" by simp
  moreover from ab_app[of \<open>1\<^sub>\<nat>\<close>] have "vpsnd ab \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" by simp
  ultimately show ?thesis using that by auto
qed

end


subsubsection\<open>Arrow\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "digraph \<alpha> \<AA>" and \<BB>: "digraph \<alpha> \<BB>"
begin

lemma dg_prod_2_ArrI:
  assumes "g \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" and "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
  unfolding dg_prod_2_def dg_prod_components
proof(intro vproductI ballI)
  show "\<D>\<^sub>\<circ> [g, f]\<^sub>\<circ> = 2\<^sub>\<nat>" by (simp add: nat_omega_simps two)
  fix i assume "i \<in>\<^sub>\<circ> 2\<^sub>\<nat>"
  then consider \<open>i = 0\<close> | \<open>i = 1\<^sub>\<nat>\<close> unfolding two by auto 
  then show "[g, f]\<^sub>\<circ>\<lparr>i\<rparr> \<in>\<^sub>\<circ> (if i = 0 then \<AA> else \<BB>)\<lparr>Arr\<rparr>"
    by cases (simp_all add: nat_omega_simps assms(1,2))
qed auto

lemma dg_prod_2_ArrI'[dg_prod_cs_intros]:
  assumes "gf = [g, f]\<^sub>\<circ>" and "g \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" and "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
  shows "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
  using assms(2,3) unfolding assms(1) by (rule dg_prod_2_ArrI)

lemma dg_prod_2_ArrE:
  assumes "gf \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
  obtains g f where "gf = [g, f]\<^sub>\<circ>" and "g \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" and "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
proof-
  from vproductD[OF assms[unfolded dg_prod_2_def dg_prod_components]]
  have vsv_gf: "vsv gf"
    and dom_gf: "\<D>\<^sub>\<circ> gf = 2\<^sub>\<nat>"
    and gf_app: "\<And>i. i \<in>\<^sub>\<circ> 2\<^sub>\<nat> \<Longrightarrow> gf\<lparr>i\<rparr> \<in>\<^sub>\<circ> (if i = 0 then \<AA> else \<BB>)\<lparr>Arr\<rparr>"
    by auto
  have dom_gf[simp]: "\<D>\<^sub>\<circ> gf = 2\<^sub>\<nat>" unfolding dom_gf by (simp add: two)
  interpret vsv gf by (rule vsv_gf)
  have "gf = [vpfst gf, vpsnd gf]\<^sub>\<circ>"
    by (rule vsv_vfsequence_two[symmetric]) auto
  moreover from gf_app[of 0] have "vpfst gf \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" by simp
  moreover from gf_app[of \<open>1\<^sub>\<nat>\<close>] have "vpsnd gf \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" by simp
  ultimately show ?thesis using that by auto
qed

end


subsubsection\<open>Arrow with a domain and a codomain\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "digraph \<alpha> \<AA>" and \<BB>: "digraph \<alpha> \<BB>"
begin

interpretation \<Z> \<alpha> by (rule digraphD[OF \<AA>(1)])
interpretation \<AA>: digraph \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: digraph \<alpha> \<BB> by (rule \<BB>)
interpretation finite_pdigraph \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 \<AA> \<BB>\<close>
  by (intro finite_pdigraph_dg_prod_2 \<AA> \<BB>)

lemma dg_prod_2_is_arrI:
  assumes "g : a \<mapsto>\<^bsub>\<AA>\<^esub> c" and "f : b \<mapsto>\<^bsub>\<BB>\<^esub> d"
  shows "[g, f]\<^sub>\<circ> : [a, b]\<^sub>\<circ> \<mapsto>\<^bsub>\<AA> \<times>\<^sub>D\<^sub>G \<BB>\<^esub> [c, d]\<^sub>\<circ>"
  unfolding dg_prod_2_def
proof(rule dg_prod_is_arrI)
  show "[g, f]\<^sub>\<circ>\<lparr>i\<rparr> : [a, b]\<^sub>\<circ>\<lparr>i\<rparr> \<mapsto>\<^bsub>if i = 0 then \<AA> else \<BB>\<^esub> [c, d]\<^sub>\<circ>\<lparr>i\<rparr>"
    if "i \<in>\<^sub>\<circ> 2\<^sub>\<nat>" for i
  proof-
    from that consider \<open>i = 0\<close> | \<open>i = 1\<^sub>\<nat>\<close> unfolding two by auto 
    then show "[g, f]\<^sub>\<circ>\<lparr>i\<rparr> : [a, b]\<^sub>\<circ>\<lparr>i\<rparr> \<mapsto>\<^bsub>if i = 0 then \<AA> else \<BB>\<^esub> [c, d]\<^sub>\<circ>\<lparr>i\<rparr>"
      by cases (simp_all add: nat_omega_simps assms)
  qed
qed (auto simp: nat_omega_simps two)

lemma dg_prod_2_is_arrI'[dg_prod_cs_intros]:
  assumes "gf = [g, f]\<^sub>\<circ>"
    and "ab = [a, b]\<^sub>\<circ>"
    and "cd = [c, d]\<^sub>\<circ>"
    and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> c" 
    and "f : b \<mapsto>\<^bsub>\<BB>\<^esub> d"
  shows "gf : ab \<mapsto>\<^bsub>\<AA> \<times>\<^sub>D\<^sub>G \<BB>\<^esub> cd"
  using assms(4,5) unfolding assms(1,2,3) by (rule dg_prod_2_is_arrI)

lemma dg_prod_2_is_arrE:
  assumes "gf : ab \<mapsto>\<^bsub>\<AA> \<times>\<^sub>D\<^sub>G \<BB>\<^esub> cd"
  obtains g f a b c d 
    where "gf = [g, f]\<^sub>\<circ>"
      and "ab = [a, b]\<^sub>\<circ>"
      and "cd = [c, d]\<^sub>\<circ>"
      and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> c"
      and "f : b \<mapsto>\<^bsub>\<BB>\<^esub> d"
proof-
  from dg_prod_is_arrD[OF assms[unfolded dg_prod_2_def]] 
  have [simp]: "vsv gf" "\<D>\<^sub>\<circ> gf = 2\<^sub>\<nat>" "vsv ab" "\<D>\<^sub>\<circ> ab = 2\<^sub>\<nat>" "vsv cd" "\<D>\<^sub>\<circ> cd = 2\<^sub>\<nat>"
    and gf_app: 
      "\<And>i. i \<in>\<^sub>\<circ> 2\<^sub>\<nat> \<Longrightarrow> gf\<lparr>i\<rparr> : ab\<lparr>i\<rparr> \<mapsto>\<^bsub>if i = 0 then \<AA> else \<BB>\<^esub> cd\<lparr>i\<rparr>"
    by (auto simp: two)
  have "gf = [vpfst gf, vpsnd gf]\<^sub>\<circ>" by (simp add: vsv_vfsequence_two)
  moreover have "ab = [vpfst ab, vpsnd ab]\<^sub>\<circ>" by (simp add: vsv_vfsequence_two)
  moreover have "cd = [vpfst cd, vpsnd cd]\<^sub>\<circ>" by (simp add: vsv_vfsequence_two)
  moreover from gf_app[of 0] have "vpfst gf : vpfst ab \<mapsto>\<^bsub>\<AA>\<^esub> vpfst cd" by simp
  moreover from gf_app[of \<open>1\<^sub>\<nat>\<close>] have "vpsnd gf : vpsnd ab \<mapsto>\<^bsub>\<BB>\<^esub> vpsnd cd" 
    by (simp add: nat_omega_simps)
  ultimately show ?thesis using that by auto
qed

end


subsubsection\<open>Domain\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "digraph \<alpha> \<AA>" and \<BB>: "digraph \<alpha> \<BB>"
begin

lemma dg_prod_2_Dom_vsv: "vsv ((\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Dom\<rparr>)"
  unfolding dg_prod_2_def dg_prod_components by simp

lemma dg_prod_2_Dom_vdomain[dg_cs_simps]: 
  "\<D>\<^sub>\<circ> ((\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Dom\<rparr>) = (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
  unfolding dg_prod_2_def dg_prod_components by simp

lemma dg_prod_2_Dom_app[dg_prod_cs_simps]:
  assumes "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
  shows "(\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Dom\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> = [\<AA>\<lparr>Dom\<rparr>\<lparr>g\<rparr>, \<BB>\<lparr>Dom\<rparr>\<lparr>f\<rparr>]\<^sub>\<circ>"
proof-
  from assms obtain ab cd where gf: "[g, f]\<^sub>\<circ> : ab \<mapsto>\<^bsub>\<AA> \<times>\<^sub>D\<^sub>G \<BB>\<^esub> cd" 
    by (auto intro: is_arrI)
  then have Dom_gf: "(\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Dom\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> = ab" 
    by (simp add: dg_cs_simps)
  from gf obtain a b c d 
    where ab_def: "ab = [a, b]\<^sub>\<circ>" 
      and "cd = [c, d]\<^sub>\<circ>" 
      and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> c"
      and "f : b \<mapsto>\<^bsub>\<BB>\<^esub> d"
    by (elim dg_prod_2_is_arrE[OF \<AA> \<BB>]) simp
  then have Dom_g: "\<AA>\<lparr>Dom\<rparr>\<lparr>g\<rparr> = a" and Dom_f: "\<BB>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = b" 
    by (simp_all add: dg_cs_simps)
  show ?thesis unfolding Dom_gf ab_def Dom_g Dom_f ..
qed

lemma dg_prod_2_Dom_vrange: "\<R>\<^sub>\<circ> ((\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Obj\<rparr>"
proof(rule vsv.vsv_vrange_vsubset, unfold dg_cs_simps)
  show "vsv ((\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Dom\<rparr>)" by (rule dg_prod_2_Dom_vsv)
  fix gf assume prems: "gf \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
  then obtain g f where gf_def: "gf = [g, f]\<^sub>\<circ>" 
    and g: "g \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" 
    and f: "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
    by (elim dg_prod_2_ArrE[OF \<AA> \<BB>]) simp
  from g f obtain a b c d where g: "g : a \<mapsto>\<^bsub>\<AA>\<^esub> c" and f: "f : b \<mapsto>\<^bsub>\<BB>\<^esub> d"
    by (auto intro!: is_arrI)
  from \<AA> \<BB> g f show "(\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Dom\<rparr>\<lparr>gf\<rparr> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Obj\<rparr>"
    unfolding gf_def dg_prod_2_Dom_app[OF prems[unfolded gf_def]]
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros dg_prod_cs_intros)
qed

end


subsubsection\<open>Codomain\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "digraph \<alpha> \<AA>" and \<BB>: "digraph \<alpha> \<BB>"
begin

lemma dg_prod_2_Cod_vsv: "vsv ((\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Cod\<rparr>)"
  unfolding dg_prod_2_def dg_prod_components by simp

lemma dg_prod_2_Cod_vdomain[dg_cs_simps]: 
  "\<D>\<^sub>\<circ> ((\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Cod\<rparr>) = (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
  unfolding dg_prod_2_def dg_prod_components by simp

lemma dg_prod_2_Cod_app[dg_prod_cs_simps]:
  assumes "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
  shows "(\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Cod\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> = [\<AA>\<lparr>Cod\<rparr>\<lparr>g\<rparr>, \<BB>\<lparr>Cod\<rparr>\<lparr>f\<rparr>]\<^sub>\<circ>"
proof-
  from assms obtain ab cd where gf: "[g, f]\<^sub>\<circ> : ab \<mapsto>\<^bsub>\<AA> \<times>\<^sub>D\<^sub>G \<BB>\<^esub> cd" 
    by (auto intro: is_arrI)
  then have Cod_gf: "(\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Cod\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> = cd"
    by (simp add: dg_cs_simps)
  from gf obtain a b c d 
    where "ab = [a, b]\<^sub>\<circ>" 
      and cd_def: "cd = [c, d]\<^sub>\<circ>" 
      and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> c"
      and "f : b \<mapsto>\<^bsub>\<BB>\<^esub> d"
    by (elim dg_prod_2_is_arrE[OF \<AA> \<BB>]) simp
  then have Cod_g: "\<AA>\<lparr>Cod\<rparr>\<lparr>g\<rparr> = c" and Cod_f: "\<BB>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = d"
    by (simp_all add: dg_cs_simps)
  show ?thesis unfolding Cod_gf cd_def Cod_g Cod_f ..
qed

lemma dg_prod_2_Cod_vrange: "\<R>\<^sub>\<circ> ((\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Obj\<rparr>"
proof(rule vsv.vsv_vrange_vsubset, unfold dg_cs_simps)
  show "vsv ((\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Cod\<rparr>)" by (rule dg_prod_2_Cod_vsv)
  fix gf assume prems: "gf \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
  then obtain g f where gf_def: "gf = [g, f]\<^sub>\<circ>" 
    and g: "g \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" 
    and f: "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
    by (elim dg_prod_2_ArrE[OF \<AA> \<BB>]) simp
  from g f obtain a b c d where g: "g : a \<mapsto>\<^bsub>\<AA>\<^esub> c" and f: "f : b \<mapsto>\<^bsub>\<BB>\<^esub> d"
    by (auto intro!: is_arrI)
  from \<AA> \<BB> g f show "(\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Cod\<rparr>\<lparr>gf\<rparr> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Obj\<rparr>"
    unfolding gf_def dg_prod_2_Cod_app[OF prems[unfolded gf_def]]
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros dg_prod_cs_intros)
qed

end


subsubsection\<open>Opposite product digraph\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "digraph \<alpha> \<AA>" and \<BB>: "digraph \<alpha> \<BB>"
begin

interpretation \<AA>: digraph \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: digraph \<alpha> \<BB> by (rule \<BB>)

lemma dg_prod_2_op_dg_dg_Obj[dg_op_simps]: 
  "(op_dg \<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Obj\<rparr> = (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Obj\<rparr>"
proof
  (
    intro vsubset_antisym vsubsetI; 
    elim dg_prod_2_ObjE[OF \<AA>.digraph_op \<BB>] dg_prod_2_ObjE[OF \<AA> \<BB>],
    (unfold dg_op_simps)?
  )
  fix ab a b assume prems: "ab = [a, b]\<^sub>\<circ>" "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  from \<AA> \<BB> prems(2,3) show "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Obj\<rparr>"
    unfolding prems(1) dg_op_simps
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_prod_cs_intros)
next
  fix ab a b assume prems: "ab = [a, b]\<^sub>\<circ>" "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  from \<AA> \<BB> prems(2,3) show "ab \<in>\<^sub>\<circ> (op_dg \<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Obj\<rparr>"
    unfolding prems(1) dg_op_simps
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_op_intros dg_prod_cs_intros)  
qed

lemma dg_prod_2_dg_op_dg_Obj[dg_op_simps]: 
  "(\<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>)\<lparr>Obj\<rparr> = (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Obj\<rparr>"
proof
  (
    intro vsubset_antisym vsubsetI; 
    elim dg_prod_2_ObjE[OF \<AA> \<BB>.digraph_op] dg_prod_2_ObjE[OF \<AA> \<BB>],
    (unfold dg_op_simps)?
  )
  fix ab a b assume prems: "ab = [a, b]\<^sub>\<circ>" "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  from \<AA> \<BB> prems(2,3) show "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Obj\<rparr>"
    unfolding prems(1) dg_op_simps
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_prod_cs_intros)
next
  fix ab a b assume prems: "ab = [a, b]\<^sub>\<circ>" "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  from \<AA> \<BB> prems(2,3) show "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>)\<lparr>Obj\<rparr>"
    unfolding prems(1) dg_op_simps
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_prod_cs_intros dg_op_intros) 
qed

lemma dg_prod_2_op_dg_dg_Arr[dg_op_simps]: 
  "(op_dg \<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr> = (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
proof
  (
    intro vsubset_antisym vsubsetI; 
    elim dg_prod_2_ArrE[OF \<AA>.digraph_op \<BB>] dg_prod_2_ArrE[OF \<AA> \<BB>],
    (unfold dg_op_simps)?
  )
  fix ab a b assume prems: "ab = [a, b]\<^sub>\<circ>" "a \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" "b \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
  from \<AA> \<BB> prems(2,3) show "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
    unfolding prems(1) dg_op_simps
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_prod_cs_intros)
next
  fix ab a b assume prems: "ab = [a, b]\<^sub>\<circ>" "a \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" "b \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
  from \<AA> \<BB> prems(2,3) show "ab \<in>\<^sub>\<circ> (op_dg \<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
    unfolding prems(1) dg_op_simps
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_prod_cs_intros dg_op_intros) 
qed

lemma dg_prod_2_dg_op_dg_Arr[dg_op_simps]: 
  "(\<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>)\<lparr>Arr\<rparr> = (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
proof
  (
    intro vsubset_antisym vsubsetI; 
    elim dg_prod_2_ArrE[OF \<AA> \<BB>.digraph_op] dg_prod_2_ArrE[OF \<AA> \<BB>],
    (unfold dg_op_simps)?
  )
  fix ab a b assume prems: "ab = [a, b]\<^sub>\<circ>" "a \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" "b \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
  from \<AA> \<BB> prems(2,3) show "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
    unfolding prems(1) dg_op_simps
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_prod_cs_intros)
next
  fix ab a b assume prems: "ab = [a, b]\<^sub>\<circ>" "a \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" "b \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
  from \<AA> \<BB> prems(2,3) show "ab \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>)\<lparr>Arr\<rparr>"
    unfolding prems(1) dg_op_simps
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_prod_cs_intros dg_op_intros) 
qed

end

context
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "digraph \<alpha> \<AA>" and \<BB>: "digraph \<alpha> \<BB>"
begin

lemma op_dg_dg_prod_2[dg_op_simps]: "op_dg (\<AA> \<times>\<^sub>D\<^sub>G \<BB>) = op_dg \<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>"
proof(rule vsv_eqI)

  show "vsv (op_dg (\<AA> \<times>\<^sub>D\<^sub>G \<BB>))" unfolding op_dg_def by auto
  show "vsv (op_dg \<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>)" unfolding dg_prod_2_def dg_prod_def by auto
  have dom_lhs: "\<D>\<^sub>\<circ> (op_dg (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)) = 4\<^sub>\<nat>" 
    by (simp add: op_dg_def nat_omega_simps)
  show "\<D>\<^sub>\<circ> (op_dg (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)) = \<D>\<^sub>\<circ> (op_dg \<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>)"
    unfolding dom_lhs by (simp add: dg_prod_2_def dg_prod_def nat_omega_simps)

  have Cod_Dom: "(\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Cod\<rparr> = (op_dg \<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>)\<lparr>Dom\<rparr>"
  proof(rule vsv_eqI)
    from \<AA> \<BB> show "vsv ((\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Cod\<rparr>)" by (rule dg_prod_2_Cod_vsv)
    from \<AA> \<BB> show "vsv ((op_dg \<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>)\<lparr>Dom\<rparr>)"
      by (cs_concl cs_intro: dg_prod_2_Dom_vsv dg_op_intros)+
    from \<AA> \<BB> have dom_lhs: "\<D>\<^sub>\<circ> ((\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Cod\<rparr>) = (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
      by (cs_concl cs_simp: dg_cs_simps)
    from \<AA> \<BB> show "\<D>\<^sub>\<circ> ((\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Cod\<rparr>) = \<D>\<^sub>\<circ> ((op_dg \<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>)\<lparr>Dom\<rparr>)"
      unfolding dom_lhs
      by (cs_concl cs_simp: dg_cs_simps dg_op_simps cs_intro: dg_op_intros)
    show "(\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Cod\<rparr>\<lparr>gf\<rparr> = (op_dg \<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>)\<lparr>Dom\<rparr>\<lparr>gf\<rparr>"
      if "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Cod\<rparr>)" for gf
      using that unfolding dom_lhs
    proof-
      assume "gf \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
      then obtain g f 
        where gf_def: "gf = [g, f]\<^sub>\<circ>" 
          and g: "g \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" 
          and f: "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
        by (rule dg_prod_2_ArrE[OF \<AA> \<BB>]) simp
      from \<AA> \<BB> g f show "(\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Cod\<rparr>\<lparr>gf\<rparr> = (op_dg \<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>)\<lparr>Dom\<rparr>\<lparr>gf\<rparr>"
        unfolding gf_def
        by 
          (
            cs_concl 
              cs_simp: dg_prod_cs_simps dg_op_simps 
              cs_intro: dg_prod_cs_intros dg_op_intros
          )
    qed
  qed

  have Dom_Cod: "(\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Dom\<rparr> = (op_dg \<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>)\<lparr>Cod\<rparr>"
  proof(rule vsv_eqI)
    from \<AA> \<BB> show "vsv ((op_dg \<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>)\<lparr>Cod\<rparr>)"
      by (cs_concl cs_intro: dg_prod_2_Cod_vsv dg_op_intros)+
    from \<AA> \<BB> have dom_lhs: "\<D>\<^sub>\<circ> ((\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Dom\<rparr>) = (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
      by (cs_concl cs_simp: dg_cs_simps)
    from \<AA> \<BB> show "\<D>\<^sub>\<circ> ((\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Dom\<rparr>) = \<D>\<^sub>\<circ> ((op_dg \<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>)\<lparr>Cod\<rparr>)"
      unfolding dom_lhs
      by (cs_concl cs_simp: dg_cs_simps dg_op_simps cs_intro: dg_op_intros)
    show "(\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Dom\<rparr>\<lparr>gf\<rparr> = (op_dg \<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>)\<lparr>Cod\<rparr>\<lparr>gf\<rparr>"
      if "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Dom\<rparr>)" for gf
      using that unfolding dom_lhs
    proof-
      assume "gf \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
      then obtain g f 
        where gf_def: "gf = [g, f]\<^sub>\<circ>" 
          and g: "g \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" 
          and f: "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
        by (rule dg_prod_2_ArrE[OF \<AA> \<BB>]) simp
      from \<AA> \<BB> g f show "(\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Dom\<rparr>\<lparr>gf\<rparr> = (op_dg \<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>)\<lparr>Cod\<rparr>\<lparr>gf\<rparr>"
        unfolding gf_def
        by 
          (
            cs_concl 
              cs_simp: dg_cs_simps dg_prod_cs_simps dg_op_simps 
              cs_intro: dg_op_intros dg_prod_cs_intros
          )
    qed
  qed (auto intro: \<AA> \<BB> dg_prod_2_Dom_vsv)

  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (op_dg (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)) \<Longrightarrow>
    op_dg (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>a\<rparr> = (op_dg \<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>)\<lparr>a\<rparr>" 
    for a
  proof
    (
      unfold dom_lhs, 
      elim_in_numeral, 
      fold dg_field_simps, 
      unfold op_dg_components
    )
    from \<AA> \<BB> show "(\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Obj\<rparr> = (op_dg \<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>)\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: dg_op_simps cs_intro: dg_op_intros) 
    from \<AA> \<BB> show "(\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr> = (op_dg \<AA> \<times>\<^sub>D\<^sub>G op_dg \<BB>)\<lparr>Arr\<rparr>"
      by (cs_concl cs_simp: dg_op_simps cs_intro: dg_op_intros) 
  qed (auto simp: \<AA> \<BB> Cod_Dom Dom_Cod)

qed

end



subsection\<open>Projections for the product of two digraphs\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition dghm_proj_fst :: "V \<Rightarrow> V \<Rightarrow> V" (\<open>\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>1\<close>)
  where "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>1 \<AA> \<BB> = dghm_proj (2\<^sub>\<nat>) (if2 \<AA> \<BB>) 0"
definition dghm_proj_snd :: "V \<Rightarrow> V \<Rightarrow> V" (\<open>\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>2\<close>)
  where "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>2 \<AA> \<BB> = dghm_proj (2\<^sub>\<nat>) (if2 \<AA> \<BB>) (1\<^sub>\<nat>)"


subsubsection\<open>Object map for a projection of a product of two digraphs\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "digraph \<alpha> \<AA>" and \<BB>: "digraph \<alpha> \<BB>"
begin

lemma dghm_proj_fst_ObjMap_app[dg_cs_simps]:
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Obj\<rparr>"
  shows "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>1 \<AA> \<BB>\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> = a"
proof-
  from assms have "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>2\<^sub>\<nat>. (if i = 0 then \<AA> else \<BB>)\<lparr>Obj\<rparr>)"
    unfolding dg_prod_2_def dg_prod_components by simp
  then show "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>1 \<AA> \<BB>\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> = a"
    unfolding dghm_proj_fst_def dghm_proj_components dg_prod_components by simp
qed

lemma dghm_proj_snd_ObjMap_app[dg_cs_simps]:
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Obj\<rparr>"
  shows "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>2 \<AA> \<BB>\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> = b"
proof-
  from assms have "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>2\<^sub>\<nat>. (if i = 0 then \<AA> else \<BB>)\<lparr>Obj\<rparr>)"
    unfolding dg_prod_2_def dg_prod_components by simp
  then show "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>2 \<AA> \<BB>\<lparr>ObjMap\<rparr>\<lparr>a, b\<rparr>\<^sub>\<bullet> = b"
    unfolding dghm_proj_snd_def dghm_proj_components dg_prod_components
    by (simp add: nat_omega_simps)
qed

end


subsubsection\<open>Arrow map for a projection of a product of two digraphs\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "digraph \<alpha> \<AA>" and \<BB>: "digraph \<alpha> \<BB>"
begin

lemma dghm_proj_fst_ArrMap_app[dg_cs_simps]:
  assumes "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
  shows "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>1 \<AA> \<BB>\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> = g"
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>2\<^sub>\<nat>. (if i = 0 then \<AA> else \<BB>)\<lparr>Arr\<rparr>)"
    unfolding dg_prod_2_def dg_prod_components by simp
  then show "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>1 \<AA> \<BB>\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> = g"
    unfolding dghm_proj_fst_def dghm_proj_components dg_prod_components by simp
qed

lemma dghm_proj_snd_ArrMap_app[dg_cs_simps]:
  assumes "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G \<BB>)\<lparr>Arr\<rparr>"
  shows "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>2 \<AA> \<BB>\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> = f"
proof-
  from assms have "[g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>2\<^sub>\<nat>. (if i = 0 then \<AA> else \<BB>)\<lparr>Arr\<rparr>)"
    unfolding dg_prod_2_def dg_prod_components by simp
  then show "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>2 \<AA> \<BB>\<lparr>ArrMap\<rparr>\<lparr>g, f\<rparr>\<^sub>\<bullet> = f"
    unfolding dghm_proj_snd_def dghm_proj_components dg_prod_components
    by (simp add: nat_omega_simps)
qed

end


subsubsection\<open>Domain and codomain of a projection of a product of two digraphs\<close>

lemma dghm_proj_fst_HomDom: "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>1 \<AA> \<BB>\<lparr>HomDom\<rparr> = \<AA> \<times>\<^sub>D\<^sub>G \<BB>"
  unfolding dghm_proj_fst_def dghm_proj_components dg_prod_2_def ..

lemma dghm_proj_fst_HomCod: "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>1 \<AA> \<BB>\<lparr>HomCod\<rparr> = \<AA>"
  unfolding dghm_proj_fst_def dghm_proj_components dg_prod_2_def by simp
  
lemma dghm_proj_snd_HomDom: "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>2 \<AA> \<BB>\<lparr>HomDom\<rparr> = \<AA> \<times>\<^sub>D\<^sub>G \<BB>"
  unfolding dghm_proj_snd_def dghm_proj_components dg_prod_2_def ..

lemma dghm_proj_snd_HomCod: "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>2 \<AA> \<BB>\<lparr>HomCod\<rparr> = \<BB>"
  unfolding dghm_proj_snd_def dghm_proj_components dg_prod_2_def by simp


subsubsection\<open>Projection of a product of two digraphs is a digraph homomorphism\<close>

context 
  fixes \<alpha> \<AA> \<BB>
  assumes \<AA>: "digraph \<alpha> \<AA>" and \<BB>: "digraph \<alpha> \<BB>"
begin

interpretation finite_pdigraph \<alpha> \<open>2\<^sub>\<nat>\<close> \<open>if2 \<AA> \<BB>\<close>
  by (intro finite_pdigraph_dg_prod_2 \<AA> \<BB>)

lemma dghm_proj_fst_is_dghm: 
  assumes "i \<in>\<^sub>\<circ> I" 
  shows "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>1 \<AA> \<BB> : \<AA> \<times>\<^sub>D\<^sub>G \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA>"
  by 
    (
      rule pdg_dghm_proj_is_dghm[
        where i=0, simplified, folded dghm_proj_fst_def dg_prod_2_def
        ]
    )

lemma dghm_proj_fst_is_dghm'[dg_cs_intros]:
  assumes "i \<in>\<^sub>\<circ> I" and "\<CC> = \<AA> \<times>\<^sub>D\<^sub>G \<BB>" and "\<DD> = \<AA>"
  shows "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>1 \<AA> \<BB> : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms(1) unfolding assms(2,3) by (rule dghm_proj_fst_is_dghm)

lemma dghm_proj_snd_is_dghm:
  assumes "i \<in>\<^sub>\<circ> I"
  shows "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>2 \<AA> \<BB> : \<AA> \<times>\<^sub>D\<^sub>G \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  by
    (
      rule pdg_dghm_proj_is_dghm[
        where i=\<open>1\<^sub>\<nat>\<close>, simplified, folded dghm_proj_snd_def dg_prod_2_def
        ]
    )

lemma dghm_proj_snd_is_dghm'[dg_cs_intros]:  
  assumes "i \<in>\<^sub>\<circ> I" and "\<CC> = \<AA> \<times>\<^sub>D\<^sub>G \<BB>" and "\<DD> = \<BB>"
  shows "\<pi>\<^sub>D\<^sub>G\<^sub>.\<^sub>2 \<AA> \<BB> : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<DD>"
  using assms(1) unfolding assms(2,3) by (rule dghm_proj_snd_is_dghm)

end



subsection\<open>Product of three digraphs\<close>
(*TODO: find a way to generalize to the product of n digraphs*)

definition dg_prod_3 :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" ("(_ \<times>\<^sub>D\<^sub>G\<^sub>3 _ \<times>\<^sub>D\<^sub>G\<^sub>3 _)" [81, 81, 81] 80)
  where "\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC> = (\<Prod>\<^sub>D\<^sub>Gi\<in>\<^sub>\<circ>3\<^sub>\<nat>. if3 \<AA> \<BB> \<CC> i)"


subsubsection\<open>Product of three digraphs is a digraph\<close>

context 
  fixes \<alpha> \<AA> \<BB> \<CC>
  assumes \<AA>: "digraph \<alpha> \<AA>" and \<BB>: "digraph \<alpha> \<BB>" and \<CC>: "digraph \<alpha> \<CC>"
begin

interpretation \<Z> \<alpha> by (rule digraphD[OF \<AA>(1)])
interpretation \<AA>: digraph \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: digraph \<alpha> \<BB> by (rule \<BB>)
interpretation \<BB>: digraph \<alpha> \<CC> by (rule \<CC>)

lemma finite_pdigraph_dg_prod_3: 
  "finite_pdigraph \<alpha> (3\<^sub>\<nat>) (if3 \<AA> \<BB> \<CC>)"
proof(intro finite_pdigraphI pdigraph_baseI)
  from Axiom_of_Infinity show z1_in_Vset: "3\<^sub>\<nat> \<in>\<^sub>\<circ> Vset \<alpha>" by blast
  show "digraph \<alpha> (if3 \<AA> \<BB> \<CC> i)" if "i \<in>\<^sub>\<circ> 3\<^sub>\<nat>" for i
    by (auto intro: dg_cs_intros)
qed auto

interpretation finite_pdigraph \<alpha> \<open>3\<^sub>\<nat>\<close> \<open>if3 \<AA> \<BB> \<CC>\<close>
  by (intro finite_pdigraph_dg_prod_3 \<AA> \<BB>)

lemma digraph_dg_prod_3[dg_cs_intros]: "digraph \<alpha> (\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)"
proof-
  show ?thesis unfolding dg_prod_3_def by (rule pdg_digraph_dg_prod)
qed

end


subsubsection\<open>Object\<close>

context 
  fixes \<alpha> \<AA> \<BB> \<CC>
  assumes \<AA>: "digraph \<alpha> \<AA>" and \<BB>: "digraph \<alpha> \<BB>" and \<CC>: "digraph \<alpha> \<CC>"
begin

lemma dg_prod_3_ObjI:
  assumes "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "[a, b, c]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Obj\<rparr>"
  unfolding dg_prod_3_def dg_prod_components
proof(intro vproductI ballI)
  show "\<D>\<^sub>\<circ> [a, b, c]\<^sub>\<circ> = 3\<^sub>\<nat>" by (simp add: nat_omega_simps)
  fix i assume "i \<in>\<^sub>\<circ> 3\<^sub>\<nat>"
  then consider \<open>i = 0\<close> | \<open>i = 1\<^sub>\<nat>\<close> | \<open>i = 2\<^sub>\<nat>\<close> unfolding three by auto 
  then show "[a, b, c]\<^sub>\<circ>\<lparr>i\<rparr> \<in>\<^sub>\<circ> (if3 \<AA> \<BB> \<CC> i)\<lparr>Obj\<rparr>"
    by cases (simp_all add: nat_omega_simps assms)
qed auto

lemma dg_prod_3_ObjI'[dg_prod_cs_intros]:
  assumes "abc = [a, b, c]\<^sub>\<circ>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "abc \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Obj\<rparr>"
  using assms(2-4) unfolding assms(1) by (rule dg_prod_3_ObjI)

lemma dg_prod_3_ObjE:
  assumes "abc \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Obj\<rparr>"
  obtains a b c
    where "abc = [a, b, c]\<^sub>\<circ>" 
      and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
      and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
      and "c \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
proof-
  from vproductD[OF assms[unfolded dg_prod_3_def dg_prod_components]]
  have vsv_abc: "vsv abc"
    and dom_abc: "\<D>\<^sub>\<circ> abc = 3\<^sub>\<nat>"
    and abc_app: "\<And>i. i \<in>\<^sub>\<circ> 3\<^sub>\<nat> \<Longrightarrow> abc\<lparr>i\<rparr> \<in>\<^sub>\<circ> (if3 \<AA> \<BB> \<CC> i)\<lparr>Obj\<rparr>"
    by auto
  have dom_abc[simp]: "\<D>\<^sub>\<circ> abc = 3\<^sub>\<nat>"
    unfolding dom_abc by (simp add: nat_omega_simps two)
  interpret vsv abc by (rule vsv_abc)
  have "abc = [vpfst abc, vpsnd abc, vpthrd abc]\<^sub>\<circ>"
    by (rule vsv_vfsequence_three[symmetric]) auto
  moreover from abc_app[of 0] have "vpfst abc \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" by simp
  moreover from abc_app[of \<open>1\<^sub>\<nat>\<close>] have "vpsnd abc \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" by simp
  moreover from abc_app[of \<open>2\<^sub>\<nat>\<close>] have "vpthrd abc \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by simp
  ultimately show ?thesis using that by auto
qed

end


subsubsection\<open>Arrow\<close>

context 
  fixes \<alpha> \<AA> \<BB> \<CC>
  assumes \<AA>: "digraph \<alpha> \<AA>" and \<BB>: "digraph \<alpha> \<BB>" and \<CC>: "digraph \<alpha> \<CC>"
begin

lemma dg_prod_3_ArrI:
  assumes "h \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" and "g \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" and "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  shows "[h, g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Arr\<rparr>"
  unfolding dg_prod_3_def dg_prod_components
proof(intro vproductI ballI)
  show "\<D>\<^sub>\<circ> [h, g, f]\<^sub>\<circ> = 3\<^sub>\<nat>" by (simp add: nat_omega_simps three)
  fix i assume "i \<in>\<^sub>\<circ> 3\<^sub>\<nat>"
  then consider \<open>i = 0\<close> | \<open>i = 1\<^sub>\<nat>\<close> | \<open>i = 2\<^sub>\<nat>\<close> unfolding three by auto 
  then show "[h, g, f]\<^sub>\<circ>\<lparr>i\<rparr> \<in>\<^sub>\<circ> (if3 \<AA> \<BB> \<CC> i)\<lparr>Arr\<rparr>"
    by cases (simp_all add: nat_omega_simps assms)
qed auto

lemma dg_prod_3_ArrI'[dg_prod_cs_intros]:
  assumes "hgf = [h, g, f]\<^sub>\<circ>" 
    and "h \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" 
    and "g \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
    and "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  shows "[h, g, f]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Arr\<rparr>"
  using assms(2-4) unfolding assms(1) by (rule dg_prod_3_ArrI)

lemma dg_prod_3_ArrE:
  assumes "hgf \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Arr\<rparr>"
  obtains h g f 
    where "hgf = [h, g, f]\<^sub>\<circ>" 
      and "h \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" 
      and "g \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" 
      and "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof-
  from vproductD[OF assms[unfolded dg_prod_3_def dg_prod_components]]
  have vsv_hgf: "vsv hgf"
    and dom_hgf: "\<D>\<^sub>\<circ> hgf = 3\<^sub>\<nat>"
    and hgf_app: "\<And>i. i \<in>\<^sub>\<circ> 3\<^sub>\<nat> \<Longrightarrow> hgf\<lparr>i\<rparr> \<in>\<^sub>\<circ> (if3 \<AA> \<BB> \<CC> i)\<lparr>Arr\<rparr>"
    by auto
  have dom_hgf[simp]: "\<D>\<^sub>\<circ> hgf = 3\<^sub>\<nat>" unfolding dom_hgf by (simp add: three)
  interpret vsv hgf by (rule vsv_hgf)
  have "hgf = [vpfst hgf, vpsnd hgf, vpthrd hgf]\<^sub>\<circ>"
    by (rule vsv_vfsequence_three[symmetric]) auto
  moreover from hgf_app[of 0] have "vpfst hgf \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" by simp
  moreover from hgf_app[of \<open>1\<^sub>\<nat>\<close>] have "vpsnd hgf \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" by simp
  moreover from hgf_app[of \<open>2\<^sub>\<nat>\<close>] have "vpthrd hgf \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" by simp
  ultimately show ?thesis using that by auto
qed

end


subsubsection\<open>Arrow with a domain and a codomain\<close>

context 
  fixes \<alpha> \<AA> \<BB> \<CC>
  assumes \<AA>: "digraph \<alpha> \<AA>" and \<BB>: "digraph \<alpha> \<BB>" and \<CC>: "digraph \<alpha> \<CC>"
begin

interpretation \<Z> \<alpha> by (rule digraphD[OF \<AA>(1)])
interpretation \<AA>: digraph \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: digraph \<alpha> \<BB> by (rule \<BB>)
interpretation \<CC>: digraph \<alpha> \<CC> by (rule \<CC>)
interpretation finite_pdigraph \<alpha> \<open>3\<^sub>\<nat>\<close> \<open>if3 \<AA> \<BB> \<CC>\<close>
  by (intro finite_pdigraph_dg_prod_3 \<AA> \<BB> \<CC>)

lemma dg_prod_3_is_arrI:
  assumes "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" and "f' : a' \<mapsto>\<^bsub>\<BB>\<^esub> b'" and "f'' : a'' \<mapsto>\<^bsub>\<CC>\<^esub> b''"
  shows "[f, f', f'']\<^sub>\<circ> : [a, a', a'']\<^sub>\<circ> \<mapsto>\<^bsub>\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>\<^esub> [b, b', b'']\<^sub>\<circ>"
  unfolding dg_prod_3_def
proof(rule dg_prod_is_arrI)
  show "[f, f', f'']\<^sub>\<circ>\<lparr>i\<rparr> : [a, a', a'']\<^sub>\<circ>\<lparr>i\<rparr> \<mapsto>\<^bsub>if3 \<AA> \<BB> \<CC> i\<^esub> [b, b', b'']\<^sub>\<circ>\<lparr>i\<rparr>"
    if "i \<in>\<^sub>\<circ> 3\<^sub>\<nat>" for i
  proof-
    from that consider \<open>i = 0\<close> | \<open>i = 1\<^sub>\<nat>\<close> | \<open>i = 2\<^sub>\<nat>\<close> unfolding three by auto 
    then show 
      "[f, f', f'']\<^sub>\<circ>\<lparr>i\<rparr> : [a, a', a'']\<^sub>\<circ>\<lparr>i\<rparr> \<mapsto>\<^bsub>if3 \<AA> \<BB> \<CC> i\<^esub> [b, b', b'']\<^sub>\<circ>\<lparr>i\<rparr>"
      by cases (simp_all add: nat_omega_simps assms)
  qed
qed (auto simp: nat_omega_simps three)

lemma dg_prod_3_is_arrI'[dg_prod_cs_intros]:
  assumes "F = [f, f', f'']\<^sub>\<circ>"
    and "A = [a, a', a'']\<^sub>\<circ>"
    and "B = [b, b', b'']\<^sub>\<circ>"
    and "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
    and "f' : a' \<mapsto>\<^bsub>\<BB>\<^esub> b'"  
    and "f'' : a'' \<mapsto>\<^bsub>\<CC>\<^esub> b''"
  shows "F : A \<mapsto>\<^bsub>\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>\<^esub> B"
  using assms(4,5,6) unfolding assms(1,2,3) by (rule dg_prod_3_is_arrI)

lemma dg_prod_3_is_arrE:
  assumes "F : A \<mapsto>\<^bsub>\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>\<^esub> B"
  obtains f f' f'' a a' a'' b b' b'' 
    where "F = [f, f', f'']\<^sub>\<circ>"
      and "A = [a, a', a'']\<^sub>\<circ>"
      and "B = [b, b', b'']\<^sub>\<circ>"
      and "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
      and "f' : a' \<mapsto>\<^bsub>\<BB>\<^esub> b'"
      and "f'' : a'' \<mapsto>\<^bsub>\<CC>\<^esub> b''"
proof-
  from dg_prod_is_arrD[OF assms[unfolded dg_prod_3_def]] 
  have [simp]: "vsv F" "\<D>\<^sub>\<circ> F = 3\<^sub>\<nat>" "vsv A" "\<D>\<^sub>\<circ> A = 3\<^sub>\<nat>" "vsv B" "\<D>\<^sub>\<circ> B = 3\<^sub>\<nat>"
    and F_app: "\<And>i. i \<in>\<^sub>\<circ> 3\<^sub>\<nat> \<Longrightarrow> F\<lparr>i\<rparr> : A\<lparr>i\<rparr> \<mapsto>\<^bsub>if3 \<AA> \<BB> \<CC> i\<^esub> B\<lparr>i\<rparr>"
    by (auto simp: three)
  have "F = [vpfst F, vpsnd F, vpthrd F]\<^sub>\<circ>" 
    by (simp add: vsv_vfsequence_three)
  moreover have "A = [vpfst A, vpsnd A, vpthrd A]\<^sub>\<circ>" 
    by (simp add: vsv_vfsequence_three)
  moreover have "B = [vpfst B, vpsnd B, vpthrd B]\<^sub>\<circ>" 
    by (simp add: vsv_vfsequence_three)
  moreover from F_app[of 0] have "vpfst F : vpfst A \<mapsto>\<^bsub>\<AA>\<^esub> vpfst B" by simp
  moreover from F_app[of \<open>1\<^sub>\<nat>\<close>] have "vpsnd F : vpsnd A \<mapsto>\<^bsub>\<BB>\<^esub> vpsnd B" 
    by (simp add: nat_omega_simps)
  moreover from F_app[of \<open>2\<^sub>\<nat>\<close>] have "vpthrd F : vpthrd A \<mapsto>\<^bsub>\<CC>\<^esub> vpthrd B" 
    by (simp add: nat_omega_simps)
  ultimately show ?thesis using that by auto
qed

end


subsubsection\<open>Domain\<close>

context 
  fixes \<alpha> \<AA> \<BB> \<CC>
  assumes \<AA>: "digraph \<alpha> \<AA>" and \<BB>: "digraph \<alpha> \<BB>" and \<CC>: "digraph \<alpha> \<CC>"
begin

interpretation \<Z> \<alpha> by (rule digraphD[OF \<AA>(1)])
interpretation \<AA>: digraph \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: digraph \<alpha> \<BB> by (rule \<BB>)
interpretation \<CC>: digraph \<alpha> \<CC> by (rule \<CC>)

lemma dg_prod_3_Dom_vsv: "vsv ((\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Dom\<rparr>)"
  unfolding dg_prod_3_def dg_prod_components by simp

lemma dg_prod_3_Dom_vdomain[dg_cs_simps]: 
  "\<D>\<^sub>\<circ> ((\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Dom\<rparr>) = (\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Arr\<rparr>"
  unfolding dg_prod_3_def dg_prod_components by simp

lemma dg_prod_3_Dom_app[dg_prod_cs_simps]:
  assumes "[f, f', f'']\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Arr\<rparr>"
  shows "(\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Dom\<rparr>\<lparr>f, f', f''\<rparr>\<^sub>\<bullet> =
    [\<AA>\<lparr>Dom\<rparr>\<lparr>f\<rparr>, \<BB>\<lparr>Dom\<rparr>\<lparr>f'\<rparr>, \<CC>\<lparr>Dom\<rparr>\<lparr>f''\<rparr>]\<^sub>\<circ>"
proof-
  from assms obtain A B where F: "[f, f', f'']\<^sub>\<circ> : A \<mapsto>\<^bsub>\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>\<^esub> B" 
    by (auto intro: is_arrI)
  then have Dom_F: "(\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Dom\<rparr>\<lparr>f, f', f''\<rparr>\<^sub>\<bullet> = A" 
    by (simp add: dg_cs_simps)
  from F obtain a a' a'' b b' b'' 
    where A_def: "A = [a, a', a'']\<^sub>\<circ>" 
      and "B = [b, b', b'']\<^sub>\<circ>" 
      and "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
      and "f' : a' \<mapsto>\<^bsub>\<BB>\<^esub> b'"
      and "f'' : a'' \<mapsto>\<^bsub>\<CC>\<^esub> b''"
    by (elim dg_prod_3_is_arrE[OF \<AA> \<BB> \<CC>]) simp
  then have Dom_f: "\<AA>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = a"   
    and Dom_f': "\<BB>\<lparr>Dom\<rparr>\<lparr>f'\<rparr> = a'" 
    and Dom_f'': "\<CC>\<lparr>Dom\<rparr>\<lparr>f''\<rparr> = a''" 
    by (simp_all add: dg_cs_simps)
  show ?thesis unfolding Dom_F A_def Dom_f Dom_f' Dom_f'' ..
qed

lemma dg_prod_3_Dom_vrange: 
  "\<R>\<^sub>\<circ> ((\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Obj\<rparr>"
proof(rule vsv.vsv_vrange_vsubset, unfold dg_cs_simps)
  show "vsv ((\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Dom\<rparr>)" by (rule dg_prod_3_Dom_vsv)
  fix F assume prems: "F \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Arr\<rparr>"
  then obtain f f' f'' where F_def: "F = [f, f', f'']\<^sub>\<circ>" 
    and f: "f \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" 
    and f': "f' \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
    and f'': "f'' \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    by (elim dg_prod_3_ArrE[OF \<AA> \<BB> \<CC>]) simp
  from f f' f'' obtain a a' a'' b b' b''
    where f: "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" 
      and f': "f' : a' \<mapsto>\<^bsub>\<BB>\<^esub> b'" 
      and f'': "f'' : a'' \<mapsto>\<^bsub>\<CC>\<^esub> b''" 
    by (meson is_arrI)
  from \<AA> \<BB> f f' f'' show "(\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Dom\<rparr>\<lparr>F\<rparr> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Obj\<rparr>"
    unfolding F_def dg_prod_3_Dom_app[OF prems[unfolded F_def]]
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros dg_prod_cs_intros)
qed

end


subsubsection\<open>Codomain\<close>

context 
  fixes \<alpha> \<AA> \<BB> \<CC>
  assumes \<AA>: "digraph \<alpha> \<AA>" and \<BB>: "digraph \<alpha> \<BB>" and \<CC>: "digraph \<alpha> \<CC>"
begin

interpretation \<Z> \<alpha> by (rule digraphD[OF \<AA>(1)])
interpretation \<AA>: digraph \<alpha> \<AA> by (rule \<AA>)
interpretation \<BB>: digraph \<alpha> \<BB> by (rule \<BB>)
interpretation \<CC>: digraph \<alpha> \<CC> by (rule \<CC>)

lemma dg_prod_3_Cod_vsv: "vsv ((\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Cod\<rparr>)"
  unfolding dg_prod_3_def dg_prod_components by simp

lemma dg_prod_3_Cod_vdomain[dg_cs_simps]: 
  "\<D>\<^sub>\<circ> ((\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Cod\<rparr>) = (\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Arr\<rparr>"
  unfolding dg_prod_3_def dg_prod_components by simp

lemma dg_prod_3_Cod_app[dg_prod_cs_simps]:
  assumes "[f, f', f'']\<^sub>\<circ> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Arr\<rparr>"
  shows 
    "(\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Cod\<rparr>\<lparr>f, f', f''\<rparr>\<^sub>\<bullet> =
      [\<AA>\<lparr>Cod\<rparr>\<lparr>f\<rparr>, \<BB>\<lparr>Cod\<rparr>\<lparr>f'\<rparr>, \<CC>\<lparr>Cod\<rparr>\<lparr>f''\<rparr>]\<^sub>\<circ>"
proof-
  from assms obtain A B where F: "[f, f', f'']\<^sub>\<circ> : A \<mapsto>\<^bsub>\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>\<^esub> B" 
    by (auto intro: is_arrI)
  then have Cod_F: "(\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Cod\<rparr>\<lparr>f, f', f''\<rparr>\<^sub>\<bullet> = B"
    by (simp add: dg_cs_simps)
  from F obtain a a' a'' b b' b'' 
    where "A = [a, a', a'']\<^sub>\<circ>" 
      and B_def: "B = [b, b', b'']\<^sub>\<circ>" 
      and "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
      and "f' : a' \<mapsto>\<^bsub>\<BB>\<^esub> b'"
      and "f'' : a'' \<mapsto>\<^bsub>\<CC>\<^esub> b''"
    by (elim dg_prod_3_is_arrE[OF \<AA> \<BB> \<CC>]) simp
  then have Cod_f: "\<AA>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = b"
    and Cod_f': "\<BB>\<lparr>Cod\<rparr>\<lparr>f'\<rparr> = b'"
    and Cod_f'': "\<CC>\<lparr>Cod\<rparr>\<lparr>f''\<rparr> = b''"
    by (simp_all add: dg_cs_simps)
  show ?thesis unfolding Cod_F B_def Cod_f Cod_f' Cod_f'' ..
qed

lemma dg_prod_3_Cod_vrange: 
  "\<R>\<^sub>\<circ> ((\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Obj\<rparr>"
proof(rule vsv.vsv_vrange_vsubset, unfold dg_cs_simps)
  show "vsv ((\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Cod\<rparr>)" by (rule dg_prod_3_Cod_vsv)
  fix F assume prems: "F \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Arr\<rparr>"
  then obtain f f' f'' where F_def: "F = [f, f', f'']\<^sub>\<circ>" 
    and f: "f \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>" 
    and f': "f' \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" 
    and f'': "f'' \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    by (elim dg_prod_3_ArrE[OF \<AA> \<BB> \<CC>]) simp
  from f f' f'' obtain a a' a'' b b' b'' 
    where f: "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" 
      and f': "f' : a' \<mapsto>\<^bsub>\<BB>\<^esub> b'"
      and f'': "f'' : a'' \<mapsto>\<^bsub>\<CC>\<^esub> b''"
    by (metis is_arrI)
  from \<AA> \<BB> \<CC> f f' f'' show 
    "(\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Cod\<rparr>\<lparr>F\<rparr> \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>D\<^sub>G\<^sub>3 \<BB> \<times>\<^sub>D\<^sub>G\<^sub>3 \<CC>)\<lparr>Obj\<rparr>"
    unfolding F_def dg_prod_3_Cod_app[OF prems[unfolded F_def]]
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros dg_prod_cs_intros)
qed

end

text\<open>\newpage\<close>

end