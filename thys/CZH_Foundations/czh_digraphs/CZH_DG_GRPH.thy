(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>GRPH\<close> as a digraph\<close>
theory CZH_DG_GRPH
  imports 
    CZH_DG_DGHM
    CZH_DG_Small_Digraph
begin



subsection\<open>Background\<close>


text\<open>
Conventionally, \<open>GRPH\<close> defined as a category of digraphs and digraph 
homomorphisms (e.g., see Chapter II-7 in \cite{mac_lane_categories_2010}).
However, there is little that can prevent one from exposing \<open>GRPH\<close>
as a digraph and provide additional structure gradually in 
subsequent installments of this work. Thus, in this section, \<open>\<alpha>\<close>-\<open>GRPH\<close> is 
defined as a digraph of digraphs and digraph homomorphisms in \<open>V\<^sub>\<alpha>\<close>.
\<close>

named_theorems GRPH_cs_simps
named_theorems GRPH_cs_intros



subsection\<open>Definition and elementary properties\<close>

definition dg_GRPH :: "V \<Rightarrow> V"
  where "dg_GRPH \<alpha> =
    [
      set {\<CC>. digraph \<alpha> \<CC>},
      all_dghms \<alpha>,
      (\<lambda>\<FF>\<in>\<^sub>\<circ>all_dghms \<alpha>. \<FF>\<lparr>HomDom\<rparr>),
      (\<lambda>\<FF>\<in>\<^sub>\<circ>all_dghms \<alpha>. \<FF>\<lparr>HomCod\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dg_GRPH_components:
  shows "dg_GRPH \<alpha>\<lparr>Obj\<rparr> = set {\<CC>. digraph \<alpha> \<CC>}"
    and "dg_GRPH \<alpha>\<lparr>Arr\<rparr> = all_dghms \<alpha>"
    and "dg_GRPH \<alpha>\<lparr>Dom\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>all_dghms \<alpha>. \<FF>\<lparr>HomDom\<rparr>)"
    and "dg_GRPH \<alpha>\<lparr>Cod\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>all_dghms \<alpha>. \<FF>\<lparr>HomCod\<rparr>)"
  unfolding dg_GRPH_def dg_field_simps by (simp_all add: nat_omega_simps)



subsection\<open>Object\<close>

lemma dg_GRPH_ObjI:
  assumes "digraph \<alpha> \<AA>"
  shows "\<AA> \<in>\<^sub>\<circ> dg_GRPH \<alpha>\<lparr>Obj\<rparr>"
  using assms unfolding dg_GRPH_components by auto

lemma dg_GRPH_ObjD:
  assumes "\<AA> \<in>\<^sub>\<circ> dg_GRPH \<alpha>\<lparr>Obj\<rparr>"
  shows "digraph \<alpha> \<AA>"
  using assms unfolding dg_GRPH_components by auto

lemma dg_GRPH_ObjE:
  assumes "\<AA> \<in>\<^sub>\<circ> dg_GRPH \<alpha>\<lparr>Obj\<rparr>"
  obtains "digraph \<alpha> \<AA>"
  using assms unfolding dg_GRPH_components by auto

lemma dg_GRPH_Obj_iff[GRPH_cs_simps]: 
  "\<AA> \<in>\<^sub>\<circ> dg_GRPH \<alpha>\<lparr>Obj\<rparr> \<longleftrightarrow> digraph \<alpha> \<AA>"
  unfolding dg_GRPH_components by auto



subsection\<open>Domain\<close>

mk_VLambda dg_GRPH_components(3)
  |vsv dg_GRPH_Dom_vsv[GRPH_cs_intros]|
  |vdomain dg_GRPH_Dom_vdomain[GRPH_cs_simps]|
  |app dg_GRPH_Dom_app[GRPH_cs_simps]|

lemma dg_GRPH_Dom_vrange: "\<R>\<^sub>\<circ> (dg_GRPH \<alpha>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> dg_GRPH \<alpha>\<lparr>Obj\<rparr>"
  unfolding dg_GRPH_components by (rule vrange_VLambda_vsubset) auto



subsection\<open>Codomain\<close>

mk_VLambda dg_GRPH_components(4)
  |vsv dg_GRPH_Cod_vsv[GRPH_cs_intros]|
  |vdomain dg_GRPH_Cod_vdomain[GRPH_cs_simps]|
  |app dg_GRPH_Cod_app[GRPH_cs_simps]|

lemma dg_GRPH_Cod_vrange: "\<R>\<^sub>\<circ> (dg_GRPH \<alpha>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> dg_GRPH \<alpha>\<lparr>Obj\<rparr>"
  unfolding dg_GRPH_components by (rule vrange_VLambda_vsubset) auto



subsection\<open>\<open>GRPH\<close> is a digraph\<close>

lemma (in \<Z>) tiny_digraph_dg_GRPH: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "tiny_digraph \<beta> (dg_GRPH \<alpha>)"
proof(intro tiny_digraphI)
  show "vfsequence (dg_GRPH \<alpha>)" unfolding dg_GRPH_def by simp
  show "vcard (dg_GRPH \<alpha>) = 4\<^sub>\<nat>"
    unfolding dg_GRPH_def by (simp add: nat_omega_simps)
  show "\<R>\<^sub>\<circ> (dg_GRPH \<alpha>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> dg_GRPH \<alpha>\<lparr>Obj\<rparr>" by (simp add: dg_GRPH_Dom_vrange)
  show "\<R>\<^sub>\<circ> (dg_GRPH \<alpha>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> dg_GRPH \<alpha>\<lparr>Obj\<rparr>" by (simp add: dg_GRPH_Cod_vrange)
  show "dg_GRPH \<alpha>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
    unfolding dg_GRPH_components by (rule digraphs_in_Vset[OF assms])
  show "dg_GRPH \<alpha>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
    unfolding dg_GRPH_components by (rule all_dghms_in_Vset[OF assms])
qed (auto simp: assms dg_GRPH_components)



subsection\<open>Arrow with a domain and a codomain\<close>

lemma dg_GRPH_is_arrI:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "\<FF> : \<AA> \<mapsto>\<^bsub>dg_GRPH \<alpha>\<^esub> \<BB>"
proof(intro is_arrI; unfold dg_GRPH_components)
  from assms show "\<FF> \<in>\<^sub>\<circ> all_dghms \<alpha>" by auto
  with assms show 
    "(\<lambda>\<FF>\<in>\<^sub>\<circ>all_dghms \<alpha>. \<FF>\<lparr>HomDom\<rparr>)\<lparr>\<FF>\<rparr> = \<AA>" 
    "(\<lambda>\<FF>\<in>\<^sub>\<circ>all_dghms \<alpha>. \<FF>\<lparr>HomCod\<rparr>)\<lparr>\<FF>\<rparr> = \<BB>"
    by (auto simp: GRPH_cs_simps)
qed

lemma dg_GRPH_is_arrD:
  assumes "\<FF> : \<AA> \<mapsto>\<^bsub>dg_GRPH \<alpha>\<^esub> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" 
  using assms by (elim is_arrE) (auto simp: dg_GRPH_components)

lemma dg_GRPH_is_arrE:
  assumes "\<FF> : \<AA> \<mapsto>\<^bsub>dg_GRPH \<alpha>\<^esub> \<BB>"
  obtains "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by (simp add: dg_GRPH_is_arrD)

lemma dg_GRPH_is_arr_iff[GRPH_cs_simps]: 
  "\<FF> : \<AA> \<mapsto>\<^bsub>dg_GRPH \<alpha>\<^esub> \<BB> \<longleftrightarrow> \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" 
  by (auto intro: dg_GRPH_is_arrI dest: dg_GRPH_is_arrD)

text\<open>\newpage\<close>

end