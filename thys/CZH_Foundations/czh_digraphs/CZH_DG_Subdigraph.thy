(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Subdigraph\<close>
theory CZH_DG_Subdigraph
  imports 
    CZH_DG_Digraph
    CZH_DG_DGHM
begin



subsection\<open>Background\<close>


text\<open>
In this body of work, a subdigraph is a natural generalization of the concept 
of a subcategory, as defined in Chapter I-3 in \cite{mac_lane_categories_2010}, 
to digraphs. 
It should be noted that a similar concept also exists in the conventional
graph theory, but further details are considered to be outside of the scope of 
this work.
\<close>

named_theorems dg_sub_cs_intros
named_theorems dg_sub_bw_cs_intros
named_theorems dg_sub_fw_cs_intros
named_theorems dg_sub_bw_cs_simps



subsection\<open>Simple subdigraph\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale subdigraph = sdg: digraph \<alpha> \<BB> + dg: digraph \<alpha> \<CC> for \<alpha> \<BB> \<CC> +
  assumes subdg_Obj_vsubset[dg_sub_fw_cs_intros]: 
    "a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr> \<Longrightarrow> a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and subdg_is_arr_vsubset[dg_sub_fw_cs_intros]: 
      "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b \<Longrightarrow> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"

abbreviation is_subdigraph ("(_/ \<subseteq>\<^sub>D\<^sub>G\<index> _)" [51, 51] 50)
  where "\<BB> \<subseteq>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC> \<equiv> subdigraph \<alpha> \<BB> \<CC>"

lemmas [dg_sub_fw_cs_intros] = 
  subdigraph.subdg_Obj_vsubset
  subdigraph.subdg_is_arr_vsubset


text\<open>Rules.\<close>

lemma (in subdigraph) subdigraph_axioms'[dg_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<BB>' = \<BB>"
  shows "\<BB>' \<subseteq>\<^sub>D\<^sub>G\<^bsub>\<alpha>'\<^esub> \<CC>"
  unfolding assms by (rule subdigraph_axioms)

lemma (in subdigraph) subdigraph_axioms''[dg_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<CC>' = \<CC>"
  shows "\<BB> \<subseteq>\<^sub>D\<^sub>G\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule subdigraph_axioms)

mk_ide rf subdigraph_def[unfolded subdigraph_axioms_def]
  |intro subdigraphI|
  |dest subdigraphD[dest]|
  |elim subdigraphE[elim!]|

lemmas [dg_sub_cs_intros] = subdigraphD(1,2)


text\<open>The opposite subdigraph.\<close>

lemma (in subdigraph) subdg_subdigraph_op_dg_op_dg: "op_dg \<BB> \<subseteq>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> op_dg \<CC>"
proof(rule subdigraphI)
  show "a \<in>\<^sub>\<circ> op_dg \<BB>\<lparr>Obj\<rparr> \<Longrightarrow> a \<in>\<^sub>\<circ> op_dg \<CC>\<lparr>Obj\<rparr>" for a
    by (auto simp: dg_op_simps subdg_Obj_vsubset)
  show "f : a \<mapsto>\<^bsub>op_dg \<BB>\<^esub> b \<Longrightarrow> f : a \<mapsto>\<^bsub>op_dg \<CC>\<^esub> b" for f a b
    by (auto simp: dg_op_simps subdg_is_arr_vsubset)    
qed (auto simp: dg_op_simps intro: dg_op_intros)

lemmas subdg_subdigraph_op_dg_op_dg[dg_op_intros] = 
  subdigraph.subdg_subdigraph_op_dg_op_dg


text\<open>Further rules.\<close>

lemma (in subdigraph) subdg_objD:
  assumes "a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
  shows "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  using assms by (auto intro: subdg_Obj_vsubset)

lemmas [dg_sub_fw_cs_intros] = subdigraph.subdg_objD

lemma (in subdigraph) subdg_arrD[dg_sub_fw_cs_intros]:
  assumes "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" 
  shows "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof-
  from assms obtain a b where "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b" by auto
  then show "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    by (cs_concl cs_intro: subdg_is_arr_vsubset dg_cs_intros)
qed

lemmas [dg_sub_fw_cs_intros] = subdigraph.subdg_arrD

lemma (in subdigraph) subdg_dom_simp:
  assumes "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" 
  shows "\<BB>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr>"
proof-
  from assms obtain a b where "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b" by auto
  then show "\<BB>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = \<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr>" 
    by (force dest: subdg_is_arr_vsubset simp: dg_cs_simps)
qed

lemmas [dg_sub_bw_cs_simps] = subdigraph.subdg_dom_simp

lemma (in subdigraph) subdg_cod_simp:
  assumes "f \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" 
  shows "\<BB>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr>"
proof-
  from assms obtain a b where "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b" by auto
  then show "\<BB>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = \<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr>" 
    by (force dest: subdg_is_arr_vsubset simp: dg_cs_simps)
qed

lemmas [dg_sub_bw_cs_simps] = subdigraph.subdg_cod_simp

lemma (in subdigraph) subdg_is_arrD:
  assumes "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b" 
  shows "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  using assms subdg_is_arr_vsubset by simp

lemmas [dg_sub_fw_cs_intros] = subdigraph.subdg_is_arrD


subsubsection\<open>The subdigraph relation is a partial order\<close>

lemma subdg_refl: 
  assumes "digraph \<alpha> \<AA>" 
  shows "\<AA> \<subseteq>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA>"
proof-
  interpret digraph \<alpha> \<AA> by (rule assms)
  show ?thesis by unfold_locales simp
qed

lemma subdg_trans[trans]: 
  assumes "\<AA> \<subseteq>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" and "\<BB> \<subseteq>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<AA> \<subseteq>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<AA>\<BB>: subdigraph \<alpha> \<AA> \<BB> by (rule assms(1))
  interpret \<BB>\<CC>: subdigraph \<alpha> \<BB> \<CC> by (rule assms(2))
  show ?thesis
    by  unfold_locales
      (
        insert \<AA>\<BB>.subdigraph_axioms, 
        auto simp:
          \<BB>\<CC>.subdg_Obj_vsubset
          \<AA>\<BB>.subdg_Obj_vsubset 
          subdigraph.subdg_is_arr_vsubset 
          \<BB>\<CC>.subdg_is_arr_vsubset
      )
qed

lemma subdg_antisym:
  assumes "\<AA> \<subseteq>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" and "\<BB> \<subseteq>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "\<AA> = \<BB>"
proof-
  interpret \<AA>\<BB>: subdigraph \<alpha> \<AA> \<BB> by (rule assms(1))
  interpret \<BB>\<AA>: subdigraph \<alpha> \<BB> \<AA> by (rule assms(2))
  show ?thesis
  proof(rule dg_eqI)
    from assms show Arr: "\<AA>\<lparr>Arr\<rparr> = \<BB>\<lparr>Arr\<rparr>"
      by (intro vsubset_antisym vsubsetI) 
        (auto simp: dg_sub_bw_cs_simps intro: dg_sub_fw_cs_intros)
    from assms show "\<AA>\<lparr>Obj\<rparr> = \<BB>\<lparr>Obj\<rparr>"
      by (intro vsubset_antisym vsubsetI)
        (auto simp: dg_sub_bw_cs_simps intro: dg_sub_fw_cs_intros)
    show "\<AA>\<lparr>Dom\<rparr> = \<BB>\<lparr>Dom\<rparr>"
      by (rule vsv_eqI) (auto simp: \<AA>\<BB>.subdg_dom_simp Arr dg_cs_simps)
    show "\<AA>\<lparr>Cod\<rparr> = \<BB>\<lparr>Cod\<rparr>" 
      by (rule vsv_eqI) (auto simp: \<AA>\<BB>.subdg_cod_simp Arr dg_cs_simps)
  qed (cs_concl cs_intro: dg_cs_intros)+
qed



subsection\<open>Inclusion digraph homomorphism\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>

definition dghm_inc :: "V \<Rightarrow> V \<Rightarrow> V"
  where "dghm_inc \<BB> \<CC> = [vid_on (\<BB>\<lparr>Obj\<rparr>), vid_on (\<BB>\<lparr>Arr\<rparr>), \<BB>, \<CC>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dghm_inc_components:
  shows "dghm_inc \<BB> \<CC>\<lparr>ObjMap\<rparr> = vid_on (\<BB>\<lparr>Obj\<rparr>)" 
    and "dghm_inc \<BB> \<CC>\<lparr>ArrMap\<rparr> = vid_on (\<BB>\<lparr>Arr\<rparr>)" 
    and [dg_cs_simps]: "dghm_inc \<BB> \<CC>\<lparr>HomDom\<rparr> = \<BB>"
    and [dg_cs_simps]: "dghm_inc \<BB> \<CC>\<lparr>HomCod\<rparr> = \<CC>" 
  unfolding dghm_inc_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

mk_VLambda dghm_inc_components(1)[folded VLambda_vid_on]
  |vsv dghm_inc_ObjMap_vsv[dg_cs_intros]|
  |vdomain dghm_inc_ObjMap_vdomain[dg_cs_simps]|
  |app dghm_inc_ObjMap_app[dg_cs_simps]|


subsubsection\<open>Arrow map\<close>

mk_VLambda dghm_inc_components(2)[folded VLambda_vid_on]
  |vsv dghm_inc_ArrMap_vsv[dg_cs_intros]|
  |vdomain dghm_inc_ArrMap_vdomain[dg_cs_simps]|
  |app dghm_inc_ArrMap_app[dg_cs_simps]|


subsubsection\<open>
Canonical inclusion digraph homomorphism associated with a subdigraph
\<close>

sublocale subdigraph \<subseteq> inc: is_ft_dghm \<alpha> \<BB> \<CC> \<open>dghm_inc \<BB> \<CC>\<close>
proof(intro is_ft_dghmI is_dghmI)
  show "vfsequence (dghm_inc \<BB> \<CC>)" unfolding dghm_inc_def by auto
  show "vcard (dghm_inc \<BB> \<CC>) = 4\<^sub>\<nat>"
    unfolding dghm_inc_def by (simp add: nat_omega_simps)
  show "\<R>\<^sub>\<circ> (dghm_inc \<BB> \<CC>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    unfolding dghm_inc_components by (auto dest: subdg_objD)
  show "dghm_inc \<BB> \<CC>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr> :
    dghm_inc \<BB> \<CC>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> dghm_inc \<BB> \<CC>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    if "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b" for a b f
    using that 
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros dg_sub_fw_cs_intros)
  show "v11 (dghm_inc \<BB> \<CC>\<lparr>ArrMap\<rparr> \<restriction>\<^sup>l\<^sub>\<circ> Hom \<BB> a b)"
    if "a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" for a b
    using that unfolding dghm_inc_components by simp
qed (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)+

lemmas (in subdigraph) subdg_dghm_inc_is_ft_dghm = inc.is_ft_dghm_axioms


subsubsection\<open>The inclusion digraph homomorphism for the opposite digraphs\<close>

lemma (in subdigraph) subdg_dghm_inc_op_dg_is_dghm[dg_sub_cs_intros]:
  "dghm_inc (op_dg \<BB>) (op_dg \<CC>) : op_dg \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> op_dg \<CC>"
  by (intro subdigraph.subdg_dghm_inc_is_ft_dghm subdg_subdigraph_op_dg_op_dg)

lemmas [dg_sub_cs_intros] = subdigraph.subdg_dghm_inc_op_dg_is_dghm

lemma (in subdigraph) subdg_op_dg_dghm_inc[dg_op_simps]: 
  "op_dghm (dghm_inc \<BB> \<CC>) = dghm_inc (op_dg \<BB>) (op_dg \<CC>)"
  by (rule dghm_eqI, unfold dg_op_simps dghm_inc_components id_def)
    (
      auto 
        simp: subdg_dghm_inc_op_dg_is_dghm is_ft_dghmD 
        intro: dg_op_intros dg_cs_intros
    )

lemmas [dg_op_simps] = subdigraph.subdg_op_dg_dghm_inc



subsection\<open>Full subdigraph\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>

locale fl_subdigraph = subdigraph + 
  assumes fl_subdg_is_fl_dghm_inc: "dghm_inc \<BB> \<CC> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<CC>" 

abbreviation is_fl_subdigraph ("(_/ \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<index> _)" [51, 51] 50)
  where "\<BB> \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<CC> \<equiv> fl_subdigraph \<alpha> \<BB> \<CC>"

sublocale fl_subdigraph \<subseteq> inc: is_fl_dghm \<alpha> \<BB> \<CC> \<open>dghm_inc \<BB> \<CC>\<close>
  by (rule fl_subdg_is_fl_dghm_inc)


text\<open>Rules.\<close>

lemma (in fl_subdigraph) fl_subdigraph_axioms'[dg_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<BB>' = \<BB>"
  shows "\<BB>' \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>'\<^esub> \<CC>"
  unfolding assms by (rule fl_subdigraph_axioms)

lemma (in fl_subdigraph) fl_subdigraph_axioms''[dg_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<CC>' = \<CC>"
  shows "\<BB> \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule fl_subdigraph_axioms)

mk_ide rf fl_subdigraph_def[unfolded fl_subdigraph_axioms_def]
  |intro fl_subdigraphI|
  |dest fl_subdigraphD[dest]|
  |elim fl_subdigraphE[elim!]|

lemmas [dg_sub_cs_intros] = fl_subdigraphD(1)


text\<open>Elementary properties.\<close>

lemma (in fl_subdigraph) fl_subdg_Hom_eq:
  assumes "A \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "B \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "Hom \<BB> A B = Hom \<CC> A B"
proof-
  from assms have Arr_AB: "\<BB>\<lparr>Arr\<rparr> \<inter>\<^sub>\<circ> Hom \<BB> A B = Hom \<BB> A B" 
    by 
      (
        intro vsubset_antisym vsubsetI, 
        unfold vintersection_iff in_Hom_iff; 
        (elim conjE)?; 
        (intro conjI)?
      )
      (auto intro: dg_cs_intros)
  from assms have A: "vid_on (\<BB>\<lparr>Obj\<rparr>)\<lparr>A\<rparr> = A" and B: "vid_on (\<BB>\<lparr>Obj\<rparr>)\<lparr>B\<rparr> = B" 
    by simp_all
  from inc.fl_dghm_surj_on_Hom[OF assms, unfolded dghm_inc_components] show
    "Hom \<BB> A B = Hom \<CC> A B"
    by (auto simp: Arr_AB A B)
qed



subsection\<open>Wide subdigraph\<close>


subsubsection\<open>Definition and elementary properties\<close>

text\<open>
See \cite{noauthor_nlab_nodate}\footnote{
\url{https://ncatlab.org/nlab/show/wide+subcategory}
}).
\<close>

locale wide_subdigraph = subdigraph +
  assumes wide_subdg_Obj[dg_sub_bw_cs_intros]: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"

abbreviation is_wide_subdigraph ("(_/ \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<index> _)" [51, 51] 50)
  where "\<BB> \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<CC> \<equiv> wide_subdigraph \<alpha> \<BB> \<CC>"

lemmas [dg_sub_bw_cs_intros] = wide_subdigraph.wide_subdg_Obj


text\<open>Rules.\<close>

lemma (in wide_subdigraph) wide_subdigraph_axioms'[dg_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<BB>' = \<BB>"
  shows "\<BB>' \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>'\<^esub> \<CC>"
  unfolding assms by (rule wide_subdigraph_axioms)

lemma (in wide_subdigraph) wide_subdigraph_axioms''[dg_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<CC>' = \<CC>"
  shows "\<BB> \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule wide_subdigraph_axioms)

mk_ide rf wide_subdigraph_def[unfolded wide_subdigraph_axioms_def]
  |intro wide_subdigraphI|
  |dest wide_subdigraphD[dest]|
  |elim wide_subdigraphE[elim!]|

lemmas [dg_sub_cs_intros] = wide_subdigraphD(1)


text\<open>Elementary properties.\<close>

lemma (in wide_subdigraph) wide_subdg_obj_eq[dg_sub_bw_cs_simps]: 
  "\<BB>\<lparr>Obj\<rparr> = \<CC>\<lparr>Obj\<rparr>"
  using subdg_Obj_vsubset wide_subdg_Obj by auto

lemmas [dg_sub_bw_cs_simps] = wide_subdigraph.wide_subdg_obj_eq


subsubsection\<open>The wide subdigraph relation is a partial order\<close>

lemma wide_subdg_refl: 
  assumes "digraph \<alpha> \<AA>" 
  shows "\<AA> \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<AA>"
proof-
  interpret digraph \<alpha> \<AA> by (rule assms)
  show ?thesis by unfold_locales simp
qed

lemma wide_subdg_trans[trans]: 
  assumes "\<AA> \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<BB>" and "\<BB> \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<AA> \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<AA>\<BB>: wide_subdigraph \<alpha> \<AA> \<BB> by (rule assms(1))
  interpret \<BB>\<CC>: wide_subdigraph \<alpha> \<BB> \<CC> by (rule assms(2))
  interpret \<AA>\<CC>: subdigraph \<alpha> \<AA> \<CC> 
    by (rule subdg_trans) (cs_concl cs_intro: dg_cs_intros)+
  show ?thesis
    by (cs_concl cs_intro: dg_sub_bw_cs_intros dg_cs_intros wide_subdigraphI)
qed

lemma wide_subdg_antisym:
  assumes "\<AA> \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<BB>" and "\<BB> \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "\<AA> = \<BB>"
proof-
  interpret \<AA>\<BB>: wide_subdigraph \<alpha> \<AA> \<BB> by (rule assms(1))
  interpret \<BB>\<AA>: wide_subdigraph \<alpha> \<BB> \<AA> by (rule assms(2))
  show ?thesis 
    by (rule subdg_antisym[OF \<AA>\<BB>.subdigraph_axioms \<BB>\<AA>.subdigraph_axioms])
qed

text\<open>\newpage\<close>

end