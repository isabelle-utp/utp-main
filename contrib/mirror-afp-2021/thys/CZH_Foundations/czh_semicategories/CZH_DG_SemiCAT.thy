(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>SemiCAT\<close> as a digraph\label{sec:dg_SemiCAT}\<close>
theory CZH_DG_SemiCAT
  imports 
    CZH_SMC_Semifunctor
    CZH_DG_Small_Digraph
begin



subsection\<open>Background\<close>


text\<open>
\<open>SemiCAT\<close> is usually defined as a category of semicategories and semifunctors
(e.g., see \cite{noauthor_nlab_nodate}\footnote{
\url{https://ncatlab.org/nlab/show/semicategory}
}).
However, there is little that can prevent one from exposing \<open>SemiCAT\<close>
as a digraph and provide additional structure gradually in
subsequent theories. Thus, in this section, \<open>\<alpha>\<close>-\<open>SemiCAT\<close> is defined as a 
digraph of semicategories and semifunctors in \<open>V\<^sub>\<alpha>\<close>.
\<close>

named_theorems dg_SemiCAT_simps
named_theorems dg_SemiCAT_intros



subsection\<open>Definition and elementary properties\<close>

definition dg_SemiCAT :: "V \<Rightarrow> V"
  where "dg_SemiCAT \<alpha> =
    [
      set {\<CC>. semicategory \<alpha> \<CC>},
      all_smcfs \<alpha>,
      (\<lambda>\<FF>\<in>\<^sub>\<circ>all_smcfs \<alpha>. \<FF>\<lparr>HomDom\<rparr>),
      (\<lambda>\<FF>\<in>\<^sub>\<circ>all_smcfs \<alpha>. \<FF>\<lparr>HomCod\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dg_SemiCAT_components:
  shows "dg_SemiCAT \<alpha>\<lparr>Obj\<rparr> = set {\<CC>. semicategory \<alpha> \<CC>}"
    and "dg_SemiCAT \<alpha>\<lparr>Arr\<rparr> = all_smcfs \<alpha>"
    and "dg_SemiCAT \<alpha>\<lparr>Dom\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>all_smcfs \<alpha>. \<FF>\<lparr>HomDom\<rparr>)"
    and "dg_SemiCAT \<alpha>\<lparr>Cod\<rparr> = (\<lambda>\<FF>\<in>\<^sub>\<circ>all_smcfs \<alpha>. \<FF>\<lparr>HomCod\<rparr>)"
  unfolding dg_SemiCAT_def dg_field_simps by (simp_all add: nat_omega_simps)


subsection\<open>Object\<close>

lemma dg_SemiCAT_ObjI:
  assumes "semicategory \<alpha> \<AA>"
  shows "\<AA> \<in>\<^sub>\<circ> dg_SemiCAT \<alpha>\<lparr>Obj\<rparr>"
  using assms unfolding dg_SemiCAT_components by auto

lemma dg_SemiCAT_ObjD:
  assumes "\<AA> \<in>\<^sub>\<circ> dg_SemiCAT \<alpha>\<lparr>Obj\<rparr>"
  shows "semicategory \<alpha> \<AA>"
  using assms unfolding dg_SemiCAT_components by auto

lemma dg_SemiCAT_ObjE:
  assumes "\<AA> \<in>\<^sub>\<circ> dg_SemiCAT \<alpha>\<lparr>Obj\<rparr>"
  obtains "semicategory \<alpha> \<AA>"
  using assms unfolding dg_SemiCAT_components by auto

lemma dg_SemiCAT_Obj_iff[dg_SemiCAT_simps]: 
  "\<AA> \<in>\<^sub>\<circ> dg_SemiCAT \<alpha>\<lparr>Obj\<rparr> \<longleftrightarrow> semicategory \<alpha> \<AA>"
  unfolding dg_SemiCAT_components by auto



subsection\<open>Domain and codomain\<close>

lemma [dg_SemiCAT_simps]:
  assumes "\<FF> \<in>\<^sub>\<circ> all_smcfs \<alpha>"  
  shows dg_SemiCAT_Dom_app: "dg_SemiCAT \<alpha>\<lparr>Dom\<rparr>\<lparr>\<FF>\<rparr> = \<FF>\<lparr>HomDom\<rparr>"
    and dg_SemiCAT_Cod_app: "dg_SemiCAT \<alpha>\<lparr>Cod\<rparr>\<lparr>\<FF>\<rparr> = \<FF>\<lparr>HomCod\<rparr>"
  using assms unfolding dg_SemiCAT_components by auto



subsection\<open>\<open>SemiCAT\<close> is a digraph\<close>

lemma (in \<Z>) tiny_digraph_dg_SemiCAT: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "tiny_digraph \<beta> (dg_SemiCAT \<alpha>)"
proof(intro tiny_digraphI)
  show "vfsequence (dg_SemiCAT \<alpha>)" unfolding dg_SemiCAT_def by simp
  show "vcard (dg_SemiCAT \<alpha>) = 4\<^sub>\<nat>"
    unfolding dg_SemiCAT_def by (simp add: nat_omega_simps)
  show "\<R>\<^sub>\<circ> (dg_SemiCAT \<alpha>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> dg_SemiCAT \<alpha>\<lparr>Obj\<rparr>" 
  proof(intro vsubsetI)
    fix \<AA> assume "\<AA> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (dg_SemiCAT \<alpha>\<lparr>Dom\<rparr>)"
    then obtain \<FF> 
      where "\<FF> \<in>\<^sub>\<circ> all_smcfs \<alpha>" and \<AA>_def: "\<AA> = \<FF>\<lparr>HomDom\<rparr>"
      unfolding dg_SemiCAT_components by auto
    then obtain \<BB> \<FF> where "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
      unfolding dg_SemiCAT_components by auto
    then interpret is_semifunctor \<alpha> \<AA> \<BB> \<FF> .
    show "\<AA> \<in>\<^sub>\<circ> dg_SemiCAT \<alpha>\<lparr>Obj\<rparr>"
      by (simp add: dg_SemiCAT_components HomDom.semicategory_axioms)
  qed
  show "\<R>\<^sub>\<circ> (dg_SemiCAT \<alpha>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> dg_SemiCAT \<alpha>\<lparr>Obj\<rparr>"
  proof(intro vsubsetI)
    fix \<BB> assume "\<BB> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (dg_SemiCAT \<alpha>\<lparr>Cod\<rparr>)"
    then obtain \<FF> where "\<FF> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (dg_SemiCAT \<alpha>\<lparr>Cod\<rparr>)" and "\<BB> = \<FF>\<lparr>HomCod\<rparr>"
      unfolding dg_SemiCAT_components by auto
    then obtain \<AA> \<FF> 
      where \<FF>: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and \<AA>_def: "\<BB> = \<FF>\<lparr>HomCod\<rparr>"
      unfolding dg_SemiCAT_components by auto
    have "\<BB> = \<FF>\<lparr>HomCod\<rparr>" unfolding \<AA>_def by simp
    interpret is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule \<FF>)
    show "\<BB> \<in>\<^sub>\<circ> dg_SemiCAT \<alpha>\<lparr>Obj\<rparr>"
      by (simp add: HomCod.semicategory_axioms dg_SemiCAT_components)
  qed
  show "dg_SemiCAT \<alpha>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
    unfolding dg_SemiCAT_components by (rule semicategories_in_Vset[OF assms])
  show "dg_SemiCAT \<alpha>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
    unfolding dg_SemiCAT_components by (rule all_smcfs_in_Vset[OF assms])
qed (simp_all add: assms dg_SemiCAT_components)



subsection\<open>Arrow with a domain and a codomain\<close>

lemma dg_SemiCAT_is_arrI:
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
  shows "\<FF> : \<AA> \<mapsto>\<^bsub>dg_SemiCAT \<alpha>\<^esub> \<BB>"
proof(intro is_arrI, unfold dg_SemiCAT_components(2))
  interpret is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms)
  from assms show "\<FF> \<in>\<^sub>\<circ> all_smcfs \<alpha>" by auto
  with assms show "dg_SemiCAT \<alpha>\<lparr>Dom\<rparr>\<lparr>\<FF>\<rparr> = \<AA>" "dg_SemiCAT \<alpha>\<lparr>Cod\<rparr>\<lparr>\<FF>\<rparr> = \<BB>"
    by (simp_all add: smc_cs_simps dg_SemiCAT_components)
qed

lemma dg_SemiCAT_is_arrD:
  assumes "\<FF> : \<AA> \<mapsto>\<^bsub>dg_SemiCAT \<alpha>\<^esub> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
  using assms by (elim is_arrE) (auto simp: dg_SemiCAT_components)

lemma dg_SemiCAT_is_arrE:
  assumes "\<FF> : \<AA> \<mapsto>\<^bsub>dg_SemiCAT \<alpha>\<^esub> \<BB>"
  obtains "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by (simp add: dg_SemiCAT_is_arrD)

lemma dg_SemiCAT_is_arr_iff[dg_SemiCAT_simps]: 
  "\<FF> : \<AA> \<mapsto>\<^bsub>dg_SemiCAT \<alpha>\<^esub> \<BB> \<longleftrightarrow> \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
  by (auto intro: dg_SemiCAT_is_arrI dest: dg_SemiCAT_is_arrD)

text\<open>\newpage\<close>

end