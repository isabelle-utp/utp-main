(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>CAT\<close> as a digraph\label{sec:dg_CAT}\<close>
theory CZH_DG_CAT
  imports 
    CZH_ECAT_Functor
    CZH_ECAT_Small_Category
begin



subsection\<open>Background\<close>


text\<open>
\<open>CAT\<close> is usually defined as a category of categories and functors
(e.g., see Chapter I-2 in \cite{mac_lane_categories_2010}).
However, there is little that can prevent one from exposing \<open>CAT\<close>
as a digraph and provide additional structure gradually in
subsequent theories. 
Thus, in this section, \<open>\<alpha>\<close>-\<open>CAT\<close> is defined as a digraph of categories 
and functors in the set \<open>V\<^sub>\<alpha>\<close>, and \<open>\<alpha>\<close>-\<open>Cat\<close> is defined
as a digraph of tiny categories and tiny functors in \<open>V\<^sub>\<alpha>\<close>.
\<close>

named_theorems dg_CAT_simps
named_theorems dg_CAT_intros



subsection\<open>Definition and elementary properties\<close>

definition dg_CAT :: "V \<Rightarrow> V"
  where "dg_CAT \<alpha> =
    [
      set {\<CC>. category \<alpha> \<CC>}, 
      all_cfs \<alpha>, 
      (\<lambda>\<FF>\<in>\<^sub>\<circ>all_cfs \<alpha>. \<FF>\<lparr>HomDom\<rparr>), 
      (\<lambda>\<FF>\<in>\<^sub>\<circ>all_cfs \<alpha>. \<FF>\<lparr>HomCod\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dg_CAT_components:
  shows "dg_CAT \<alpha>\<lparr>Obj\<rparr> = set {\<CC>. category \<alpha> \<CC>}"
    and "dg_CAT \<alpha>\<lparr>Arr\<rparr> = all_cfs \<alpha>"
    and "dg_CAT \<alpha>\<lparr>Dom\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>all_cfs \<alpha>. \<FF>\<lparr>HomDom\<rparr>)"
    and "dg_CAT \<alpha>\<lparr>Cod\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>all_cfs \<alpha>. \<FF>\<lparr>HomCod\<rparr>)"
  unfolding dg_CAT_def dg_field_simps by (simp_all add: nat_omega_simps)



subsection\<open>Object\<close>

lemma dg_CAT_ObjI:
  assumes "category \<alpha> \<AA>"
  shows "\<AA> \<in>\<^sub>\<circ> dg_CAT \<alpha>\<lparr>Obj\<rparr>"
  using assms unfolding dg_CAT_components by auto

lemma dg_CAT_ObjD:
  assumes "\<AA> \<in>\<^sub>\<circ> dg_CAT \<alpha>\<lparr>Obj\<rparr>"
  shows "category \<alpha> \<AA>"
  using assms unfolding dg_CAT_components by auto

lemma dg_CAT_ObjE:
  assumes "\<AA> \<in>\<^sub>\<circ> dg_CAT \<alpha>\<lparr>Obj\<rparr>"
  obtains "category \<alpha> \<AA>"
  using assms unfolding dg_CAT_components by auto

lemma dg_CAT_Obj_iff[dg_CAT_simps]: "\<AA> \<in>\<^sub>\<circ> dg_CAT \<alpha>\<lparr>Obj\<rparr> \<longleftrightarrow> category \<alpha> \<AA>"
  unfolding dg_CAT_components by auto



subsection\<open>Domain and codomain\<close>

lemma [dg_CAT_simps]:
  assumes "\<FF> \<in>\<^sub>\<circ> all_cfs \<alpha>"  
  shows dg_CAT_Dom_app: "dg_CAT \<alpha>\<lparr>Dom\<rparr>\<lparr>\<FF>\<rparr> = \<FF>\<lparr>HomDom\<rparr>"
    and dg_CAT_Cod_app: "dg_CAT \<alpha>\<lparr>Cod\<rparr>\<lparr>\<FF>\<rparr> = \<FF>\<lparr>HomCod\<rparr>"
  using assms unfolding dg_CAT_components by auto



subsection\<open>\<open>CAT\<close> is a digraph\<close>

lemma (in \<Z>) tiny_category_dg_CAT: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "tiny_digraph \<beta> (dg_CAT \<alpha>)"
proof(intro tiny_digraphI)
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "vfsequence (dg_CAT \<alpha>)" unfolding dg_CAT_def by simp
  show "vcard (dg_CAT \<alpha>) = 4\<^sub>\<nat>"
    unfolding dg_CAT_def by (simp add: nat_omega_simps)
  show "\<R>\<^sub>\<circ> (dg_CAT \<alpha>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> dg_CAT \<alpha>\<lparr>Obj\<rparr>" 
  proof(intro vsubsetI)
    fix \<AA> assume "\<AA> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (dg_CAT \<alpha>\<lparr>Dom\<rparr>)"
    then obtain \<FF> where "\<FF> \<in>\<^sub>\<circ> all_cfs \<alpha>" and "\<AA> = \<FF>\<lparr>HomDom\<rparr>"
      unfolding dg_CAT_components by auto
    then obtain \<BB> \<FF> where "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
      unfolding dg_CAT_components by auto
    then interpret is_functor \<alpha> \<AA> \<BB> \<FF> by simp
    show "\<AA> \<in>\<^sub>\<circ> dg_CAT \<alpha>\<lparr>Obj\<rparr>"
      by (simp add: dg_CAT_components HomDom.category_axioms)
  qed
  show "\<R>\<^sub>\<circ> (dg_CAT \<alpha>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> dg_CAT \<alpha>\<lparr>Obj\<rparr>"
  proof(intro vsubsetI)
    fix \<BB> assume "\<BB> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (dg_CAT \<alpha>\<lparr>Cod\<rparr>)"
    then obtain \<FF> where "\<FF> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (dg_CAT \<alpha>\<lparr>Cod\<rparr>)" and "\<BB> = \<FF>\<lparr>HomCod\<rparr>"
      unfolding dg_CAT_components by auto
    then obtain \<AA> \<FF> 
      where dghm: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and \<BB>_def: "\<BB> = \<FF>\<lparr>HomCod\<rparr>"
      unfolding dg_CAT_components by auto
    have "\<BB> = \<FF>\<lparr>HomCod\<rparr>" unfolding \<BB>_def by simp
    interpret is_functor \<alpha> \<AA> \<BB> \<FF> by (rule dghm)
    show "\<BB> \<in>\<^sub>\<circ> dg_CAT \<alpha>\<lparr>Obj\<rparr>"
      by (simp add: HomCod.category_axioms dg_CAT_components)
  qed
  show "dg_CAT \<alpha>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
    unfolding dg_CAT_components by (rule categories_in_Vset[OF assms])
  show "dg_CAT \<alpha>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
    unfolding dg_CAT_components by (rule all_cfs_in_Vset[OF assms])
qed (simp_all add: assms dg_CAT_components)



subsection\<open>Arrow with a domain and a codomain\<close>

lemma dg_CAT_is_arrI:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "\<FF> : \<AA> \<mapsto>\<^bsub>dg_CAT \<alpha>\<^esub> \<BB>"
proof(intro is_arrI, unfold dg_CAT_components(2))
  interpret is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms)
  from assms show "\<FF> \<in>\<^sub>\<circ> all_cfs \<alpha>" by auto
  with assms show "dg_CAT \<alpha>\<lparr>Dom\<rparr>\<lparr>\<FF>\<rparr> = \<AA>" "dg_CAT \<alpha>\<lparr>Cod\<rparr>\<lparr>\<FF>\<rparr> = \<BB>"
    by (simp_all add: dg_CAT_components cat_cs_simps)
qed 

lemma dg_CAT_is_arrD:
  assumes "\<FF> : \<AA> \<mapsto>\<^bsub>dg_CAT \<alpha>\<^esub> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
  using assms by (elim is_arrE) (auto simp: dg_CAT_components)

lemma dg_CAT_is_arrE:
  assumes "\<FF> : \<AA> \<mapsto>\<^bsub>dg_CAT \<alpha>\<^esub> \<BB>"
  obtains "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by (simp add: dg_CAT_is_arrD)

lemma dg_CAT_is_arr_iff[dg_CAT_simps]: 
  "\<FF> : \<AA> \<mapsto>\<^bsub>dg_CAT \<alpha>\<^esub> \<BB> \<longleftrightarrow> \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
  by (auto intro: dg_CAT_is_arrI dest: dg_CAT_is_arrD)

text\<open>\newpage\<close>

end