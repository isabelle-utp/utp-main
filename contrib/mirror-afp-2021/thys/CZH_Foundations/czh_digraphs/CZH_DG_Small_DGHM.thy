(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Smallness for digraph homomorphisms\<close>
theory CZH_DG_Small_DGHM
  imports 
    CZH_DG_Small_Digraph
    CZH_DG_DGHM
begin



subsection\<open>Digraph homomorphism with tiny maps\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
The following construction is based on the concept
of a \<open>small functor\<close> used in \cite{shulman_set_2008}
in the context of the presentation of the set theory \<open>ZFC/S\<close>.
\<close>

locale is_tm_dghm =
  is_dghm \<alpha> \<AA> \<BB> \<FF> +
  HomDom: digraph \<alpha> \<AA> + 
  HomCod: digraph \<alpha> \<BB>
  for \<alpha> \<AA> \<BB> \<FF> +
  assumes tm_dghm_ObjMap_in_Vset[dg_small_cs_intros]: "\<FF>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    and tm_dghm_ArrMap_in_Vset[dg_small_cs_intros]: "\<FF>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"

syntax "_is_tm_dghm" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool" 
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_tm_dghm \<alpha> \<AA> \<BB> \<FF>"

abbreviation (input) is_cn_tm_dghm :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "is_cn_tm_dghm \<alpha> \<AA> \<BB> \<FF> \<equiv> \<FF> : op_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"

syntax "_is_cn_tm_dghm" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool" 
  (\<open>(_ :/ _ \<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<mapsto>\<mapsto>\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>" \<rightharpoonup> "CONST is_cn_tm_dghm \<alpha> \<AA> \<BB> \<FF>"

abbreviation all_tm_dghms :: "V \<Rightarrow> V"
  where "all_tm_dghms \<alpha> \<equiv> set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation small_tm_dghms :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "small_tm_dghms \<alpha> \<AA> \<BB> \<equiv> set {\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"

lemmas [dg_small_cs_intros] =
  is_tm_dghm.tm_dghm_ObjMap_in_Vset
  is_tm_dghm.tm_dghm_ArrMap_in_Vset


text\<open>Rules.\<close>

lemma (in is_tm_dghm) is_tm_dghm_axioms'[dg_small_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_tm_dghm_axioms)

mk_ide rf is_tm_dghm_def[unfolded is_tm_dghm_axioms_def]
  |intro is_tm_dghmI|
  |dest is_tm_dghmD[dest]|
  |elim is_tm_dghmE[elim]|

lemmas [dg_small_cs_intros] = is_tm_dghmD(1)


text\<open>Elementary properties.\<close>

sublocale is_tm_dghm \<subseteq> HomDom: tiny_digraph \<alpha> \<AA> 
proof(rule tiny_digraphI')
  show "\<AA>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by (rule vdomain_in_VsetI[OF tm_dghm_ObjMap_in_Vset, simplified dg_cs_simps])
  show "\<AA>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by (rule vdomain_in_VsetI[OF tm_dghm_ArrMap_in_Vset, simplified dg_cs_simps])
qed (cs_concl cs_intro: dg_cs_intros)

lemmas (in is_tm_dghm) 
  tm_dghm_HomDom_is_tiny_digraph = HomDom.tiny_digraph_axioms

lemmas [dg_small_cs_intros] = is_tm_dghm.tm_dghm_HomDom_is_tiny_digraph


text\<open>Further rules.\<close>

lemma is_tm_dghmI':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>"
    and [simp]: "\<FF>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    and [simp]: "\<FF>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret is_dghm \<alpha> \<AA> \<BB> \<FF> by (rule assms(1))
  from assms show ?thesis
    by (intro is_tm_dghmI) (auto simp: vfsequence_axioms dghm_ObjMap_vrange)
qed


text\<open>Size.\<close>

lemma small_all_tm_dghms[simp]: "small {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(rule down)
  show 
    "{\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq>
      elts (set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>})"
  proof
    (
      simp only: elts_of_set small_all_dghms if_True, 
      rule subsetI, 
      unfold mem_Collect_eq
    )
    fix \<FF> assume "\<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    then obtain \<AA> \<BB> where \<FF>: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" by clarsimp
    interpret is_tm_dghm \<alpha> \<AA> \<BB> \<FF> by (rule \<FF>)
    from is_dghm_axioms' show "\<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" by blast
  qed
qed


subsubsection\<open>Opposite digraph homomorphism with tiny maps\<close>

lemma (in is_tm_dghm) is_tm_dghm_op: "op_dghm \<FF> : op_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_dg \<BB>"
  by (intro is_tm_dghmI', unfold dg_op_simps)
    (cs_concl cs_intro: dg_cs_intros dg_small_cs_intros dg_op_intros)

lemma (in is_tm_dghm) is_tm_dghm_op'[dg_op_intros]:  
  assumes "\<AA>' = op_dg \<AA>" and "\<BB>' = op_dg \<BB>" and "\<alpha>' = \<alpha>"
  shows "op_dghm \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_tm_dghm_op)

lemmas is_tm_dghm_op[dg_op_intros] = is_tm_dghm.is_tm_dghm_op'


subsubsection\<open>Composition of a digraph homomorphism with tiny maps\<close>

lemma dghm_comp_is_tm_dghm[dg_small_cs_intros]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<FF>: is_tm_dghm \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  interpret \<GG>: is_tm_dghm \<alpha> \<BB> \<CC> \<GG> by (rule assms(1))
  show ?thesis
  proof(intro is_tm_dghmI')
    from assms show "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
      by 
        (
          cs_concl 
            cs_simp: dghm_comp_components 
            cs_intro: dg_small_cs_intros Limit_vcomp_in_VsetI \<FF>.Limit_\<alpha> 
        )+
    from assms show "(\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>)\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
      by 
        (
          cs_concl 
            cs_simp: dghm_comp_components 
            cs_intro: dg_small_cs_intros Limit_vcomp_in_VsetI \<FF>.Limit_\<alpha> 
        )+
  qed (auto intro: dg_cs_intros)
qed


subsubsection\<open>Finite digraphs and digraph homomorphisms with tiny maps\<close>

lemma (in is_dghm) dghm_is_tm_dghm_if_HomDom_finite_digraph:
  assumes "finite_digraph \<alpha> \<AA>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
proof(intro is_tm_dghmI')
  interpret \<AA>: finite_digraph \<alpha> \<AA> by (rule assms(1))
  show "\<FF>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  proof(rule ObjMap.vsv_Limit_vsv_in_VsetI)
    show "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    proof-
      have "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" by (simp add: dghm_ObjMap_vrange)
      moreover have "\<BB>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
        by (simp add: HomCod.dg_Obj_vsubset_Vset)
      ultimately show ?thesis by auto
    qed
  qed (auto simp: dg_cs_simps dg_small_cs_intros)
  show "\<FF>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  proof(rule ArrMap.vsv_Limit_vsv_in_VsetI)
    show "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    proof-
      have "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>" by (simp add: dghm_ArrMap_vrange)
      moreover have "\<BB>\<lparr>Arr\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
        by (simp add: HomCod.dg_Arr_vsubset_Vset)
      ultimately show ?thesis by auto
    qed
  qed (auto simp: dg_cs_simps dg_small_cs_intros)
qed (simp add: dg_cs_intros)


subsubsection\<open>Constant digraph homomorphism\<close>

lemma dghm_const_is_tm_dghm: 
  assumes "tiny_digraph \<alpha> \<CC>" and "digraph \<alpha> \<DD>" and "f : a \<mapsto>\<^bsub>\<DD>\<^esub> a"
  shows "dghm_const \<CC> \<DD> a f : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<DD>"
proof(intro is_tm_dghmI')
  interpret \<CC>: tiny_digraph \<alpha> \<CC> by (rule assms(1))
  interpret \<DD>: digraph \<alpha> \<DD> by (rule assms(2))
  from assms show "dghm_const \<CC> \<DD> a f : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<DD>"
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)
  show "dghm_const \<CC> \<DD> a f\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    unfolding dghm_const_components
  proof(rule vbrelation.vbrelation_Limit_in_VsetI)
    from assms(3) have "a \<in>\<^sub>\<circ> set {a}" by (cs_concl  cs_intro: V_cs_intros)
    with assms(3) show "\<R>\<^sub>\<circ> (vconst_on (\<CC>\<lparr>Obj\<rparr>) a) \<in>\<^sub>\<circ> Vset \<alpha>"
      by 
        (
          cs_concl cs_intro: 
            dg_cs_intros 
            V_cs_intros
            \<DD>.dg_in_Obj_in_Vset 
            vsubset_in_VsetI 
            Limit_vsingleton_in_VsetI 
        )
    show "\<D>\<^sub>\<circ> (vconst_on (\<CC>\<lparr>Obj\<rparr>) a) \<in>\<^sub>\<circ> Vset \<alpha>"
      by (cs_concl cs_simp: V_cs_simps cs_intro: V_cs_intros dg_small_cs_intros)
  qed simp_all
  show "dghm_const \<CC> \<DD> a f\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    unfolding dghm_const_components
  proof(rule vbrelation.vbrelation_Limit_in_VsetI)
    from assms(3) \<DD>.dg_Arr_vsubset_Vset show
      "\<R>\<^sub>\<circ> (vconst_on (\<CC>\<lparr>Arr\<rparr>) f) \<in>\<^sub>\<circ> Vset \<alpha>"
      by (cases \<open>\<CC>\<lparr>Arr\<rparr>=0\<close>)
        (
          auto 
            simp: dg_cs_simps \<DD>.dg_is_arrD(1) 
            intro!: Limit_vsingleton_in_VsetI
        ) 
  qed (auto simp: \<CC>.tiny_dg_Arr_in_Vset)
qed

lemma dghm_const_is_tm_dghm'[dg_small_cs_intros]:
  assumes "tiny_digraph \<alpha> \<CC>"
    and "digraph \<alpha> \<DD>" 
    and "f : a \<mapsto>\<^bsub>\<DD>\<^esub> a"
    and "\<CC>' = \<CC>"
    and "\<DD>' = \<DD>"
  shows "dghm_const \<CC> \<DD> a f : \<CC>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<DD>'"
  using assms(1-3) unfolding assms(4,5) by (rule dghm_const_is_tm_dghm)



subsection\<open>Tiny digraph homomorphism\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale is_tiny_dghm = 
  is_dghm \<alpha> \<AA> \<BB> \<FF> +
  HomDom: tiny_digraph \<alpha> \<AA> + 
  HomCod: tiny_digraph \<alpha> \<BB> 
  for \<alpha> \<AA> \<BB> \<FF>

syntax "_is_tiny_dghm" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool" 
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_tiny_dghm \<alpha> \<AA> \<BB> \<FF>"

abbreviation (input) is_cn_tiny_dghm :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "is_cn_tiny_dghm \<alpha> \<AA> \<BB> \<FF> \<equiv> \<FF> : op_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"

syntax "_is_cn_tiny_dghm" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool" 
  (\<open>(_ :/ _ \<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<mapsto>\<mapsto>\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>" \<rightharpoonup> "CONST is_cn_tiny_dghm \<alpha> \<AA> \<BB> \<FF>"

abbreviation all_tiny_dghms :: "V \<Rightarrow> V"
  where "all_tiny_dghms \<alpha> \<equiv> set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation small_dghms :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "small_dghms \<alpha> \<AA> \<BB> \<equiv> set {\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"


text\<open>Rules.\<close>

lemma (in is_tiny_dghm) is_tiny_dghm_axioms'[dg_small_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_tiny_dghm_axioms)

mk_ide rf is_tiny_dghm_def
  |intro is_tiny_dghmI|
  |dest is_tiny_dghmD[dest]|
  |elim is_tiny_dghmE[elim]|

lemmas [dg_small_cs_intros] = is_tiny_dghmD(2,3)


text\<open>Size.\<close>

lemma (in is_tiny_dghm) tiny_dghm_ObjMap_in_Vset[dg_small_cs_intros]: 
  "\<FF>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  have "\<D>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (simp add: dghm_ObjMap_vdomain HomDom.tiny_dg_Obj_in_Vset)
  moreover from dghm_ObjMap_vrange have "\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
    by (simp add: vsubset_in_VsetI HomCod.tiny_dg_Obj_in_Vset)
  ultimately show "\<FF>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" 
    by 
      (
        cs_concl cs_intro: 
          V_cs_intros dg_small_cs_intros ObjMap.vbrelation_Limit_in_VsetI 
      )
qed

lemmas [dg_small_cs_intros] = is_tiny_dghm.tiny_dghm_ObjMap_in_Vset

lemma (in is_tiny_dghm) tiny_dghm_ArrMap_in_Vset[dg_small_cs_intros]: 
  "\<FF>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  have "\<D>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
    by (simp add: dghm_ArrMap_vdomain HomDom.tiny_dg_Arr_in_Vset)
  moreover from HomCod.tiny_dg_Arr_in_Vset dghm_ArrMap_vrange have 
    "\<R>\<^sub>\<circ> (\<FF>\<lparr>ArrMap\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
    by auto
  ultimately show "\<FF>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" 
    by 
      (
        cs_concl cs_intro:  
          V_cs_intros dg_small_cs_intros ArrMap.vbrelation_Limit_in_VsetI
      )
qed

lemmas [dg_small_cs_intros] = is_tiny_dghm.tiny_dghm_ArrMap_in_Vset

lemma (in is_tiny_dghm) tiny_dghm_in_Vset: "\<FF> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  note [dg_cs_intros] = 
    tiny_dghm_ObjMap_in_Vset 
    tiny_dghm_ArrMap_in_Vset
    HomDom.tiny_dg_in_Vset 
    HomCod.tiny_dg_in_Vset 
  show ?thesis
    by (subst dghm_def) 
      (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros V_cs_intros)
qed

sublocale is_tiny_dghm \<subseteq> is_tm_dghm
  by (intro is_tm_dghmI') (auto simp: dg_cs_intros dg_small_cs_intros)

lemmas (in is_tiny_dghm) tiny_dghm_is_tm_dghm = is_tm_dghm_axioms

lemmas [dg_small_cs_intros] = is_tiny_dghm.tiny_dghm_is_tm_dghm

lemma small_all_tiny_dghms[simp]: "small {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(rule down)
  show 
    "{\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq>
      elts (set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>})"
  proof
    (
      simp only: elts_of_set small_all_dghms if_True, 
      rule subsetI, 
      unfold mem_Collect_eq
    )
    fix \<FF> assume "\<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    then obtain \<AA> \<BB> where \<FF>: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>" by clarsimp
    interpret is_tiny_dghm \<alpha> \<AA> \<BB> \<FF> by (rule \<FF>)
    from is_dghm_axioms show "\<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" by auto
  qed
qed

lemma tiny_dghms_vsubset_Vset[simp]: 
  "set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq>\<^sub>\<circ> Vset \<alpha>"
proof(rule vsubsetI) 
  fix \<FF> assume "\<FF> \<in>\<^sub>\<circ> all_tiny_dghms \<alpha>"
  then obtain \<AA> \<BB> where \<FF>: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>" by clarsimp
  then show "\<FF> \<in>\<^sub>\<circ> Vset \<alpha>" by (auto simp: is_tiny_dghm.tiny_dghm_in_Vset)
qed

lemma (in is_dghm) dghm_is_tiny_dghm_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> \<BB>"
proof(intro is_tiny_dghmI)
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<beta>\<^esub> \<BB>"
    by (intro dghm_is_dghm_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: dg_cs_intros\<close>)+
  show "tiny_digraph \<beta> \<AA>" "tiny_digraph \<beta> \<BB>"
    by 
      (
        simp_all add: 
          assms 
          HomDom.dg_tiny_digraph_if_ge_Limit 
          HomCod.dg_tiny_digraph_if_ge_Limit
      )
qed


subsubsection\<open>Opposite tiny digraph homomorphism\<close>

lemma (in is_tiny_dghm) is_tiny_dghm_op: 
  "op_dghm \<FF> : op_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> op_dg \<BB>"
  by (intro is_tiny_dghmI) 
    (cs_concl cs_intro: dg_small_cs_intros dg_cs_intros dg_op_intros)+

lemma (in is_tiny_dghm) is_tiny_dghm_op'[dg_op_intros]:  
  assumes "\<AA>' = op_dg \<AA>" and "\<BB>' = op_dg \<BB>" and "\<alpha>' = \<alpha>"
  shows "op_dghm \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_tiny_dghm_op)

lemmas is_tiny_dghm_op[dg_op_intros] = is_tiny_dghm.is_tiny_dghm_op'


subsubsection\<open>Composition of tiny digraph homomorphisms\<close>

lemma dghm_comp_is_tiny_dghm[dg_small_cs_intros]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<FF>: is_tiny_dghm \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  interpret \<GG>: is_tiny_dghm \<alpha> \<BB> \<CC> \<GG> by (rule assms(1))
  show ?thesis 
    by (intro is_tiny_dghmI) 
      (auto simp: dg_small_cs_intros dg_cs_simps intro: dg_cs_intros)
qed


subsubsection\<open>Tiny constant digraph homomorphism\<close>

lemma dghm_const_is_tiny_dghm:
  assumes "tiny_digraph \<alpha> \<CC>" and "tiny_digraph \<alpha> \<DD>" and "f : a \<mapsto>\<^bsub>\<DD>\<^esub> a"
  shows "dghm_const \<CC> \<DD> a f : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<DD>"
proof(intro is_tiny_dghmI)
  from assms show "dghm_const \<CC> \<DD> a f : \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<DD>"
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros dg_small_cs_intros)
qed (auto simp: assms(1,2))

lemma dghm_const_is_tiny_dghm'[dg_small_cs_intros]:
  assumes "tiny_digraph \<alpha> \<CC>"
    and "tiny_digraph \<alpha> \<DD>" 
    and "f : a \<mapsto>\<^bsub>\<DD>\<^esub> a"
    and "\<CC>' = \<CC>"
    and "\<DD>' = \<DD>"
  shows "dghm_const \<CC> \<DD> a f : \<CC>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<DD>'"
  using assms(1-3) unfolding assms(4,5) by (rule dghm_const_is_tiny_dghm)

text\<open>\newpage\<close>

end