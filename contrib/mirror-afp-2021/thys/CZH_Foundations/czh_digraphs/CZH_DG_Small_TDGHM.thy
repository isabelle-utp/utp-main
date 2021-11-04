(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Smallness for transformations of digraph homomorphisms\<close>
theory CZH_DG_Small_TDGHM
  imports 
    CZH_DG_Small_DGHM
    CZH_DG_TDGHM
begin



subsection\<open>Transformation of digraph homomorphisms with tiny maps\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale is_tm_tdghm = 
  \<Z> \<alpha> + 
  NTDom: is_tm_dghm \<alpha> \<AA> \<BB> \<FF> +
  NTCod: is_tm_dghm \<alpha> \<AA> \<BB> \<GG> +
  is_tdghm \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>
  for \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>

syntax "_is_tm_tdghm" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m _ :/ _ \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons>
  "CONST is_tm_tdghm \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>"

abbreviation all_tm_tdghms :: "V \<Rightarrow> V"
  where "all_tm_tdghms \<alpha> \<equiv>
    set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation tm_tdghms :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "tm_tdghms \<alpha> \<AA> \<BB> \<equiv>
    set {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation these_tm_tdghms :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "these_tm_tdghms \<alpha> \<AA> \<BB> \<FF> \<GG> \<equiv> 
    set {\<NN>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"


text\<open>Rules.\<close>

lemma (in is_tm_tdghm) is_tm_tdghm_axioms'[dg_small_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>" and "\<FF>' = \<FF>" and "\<GG>' = \<GG>"
  shows "\<NN> : \<FF>' \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_tm_tdghm_axioms)

mk_ide rf is_tm_tdghm_def
  |intro is_tm_tdghmI|
  |dest is_tm_tdghmD[dest]|
  |elim is_tm_tdghmE[elim]|

lemmas [dg_small_cs_intros] = is_tm_tdghmD(2,3,4)


text\<open>Size.\<close>

lemma (in is_tm_tdghm) tm_tdghm_NTMap_in_Vset: "\<NN>\<lparr>NTMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  show ?thesis
  proof(rule vbrelation.vbrelation_Limit_in_VsetI)
    have "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>). \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> (\<GG>\<lparr>ObjMap\<rparr>). Hom \<BB> a b) \<in>\<^sub>\<circ> Vset \<alpha>"
      by 
        (
          intro 
            NTDom.HomCod.dg_Hom_vifunion_in_Vset
            NTDom.dghm_ObjMap_vrange 
            NTDom.tm_dghm_ObjMap_in_Vset 
            NTCod.dghm_ObjMap_vrange 
            NTCod.tm_dghm_ObjMap_in_Vset
            vrange_in_VsetI
        )+
    moreover have 
      "\<R>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>) \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> (\<FF>\<lparr>ObjMap\<rparr>). \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> (\<GG>\<lparr>ObjMap\<rparr>). Hom \<BB> a b)"
      by (rule tdghm_NTMap_vrange_vifunion)
    ultimately show "\<R>\<^sub>\<circ> (\<NN>\<lparr>NTMap\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>" by (auto simp: dg_cs_simps)
  qed 
    (
      insert NTCod.tm_dghm_HomDom_is_tiny_digraph, 
      auto intro!: NTMap.vbrelation_axioms simp: dg_cs_simps
    )
qed

lemma small_all_tm_tdghms[simp]: 
  "small {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(rule down)
  show "{\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq>
    elts (set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>})"
  proof
    (
      simp only: elts_of_set small_all_tdghms if_True, 
      rule subsetI, 
      unfold mem_Collect_eq
    )
    fix \<NN> assume "\<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    then obtain \<FF> \<GG> \<AA> \<BB> where \<NN>: "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
      by clarsimp
    interpret is_tm_tdghm \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule \<NN>)
    have "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" by (auto intro: dg_cs_intros)
    then show "\<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" by auto
  qed
qed

lemma small_tm_tdghms[simp]: 
  "small {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"
  by 
    (
      rule 
        down[
          of _ \<open>set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}\<close>
          ]
    )
    auto

lemma small_these_tm_tdghms[simp]: 
  "small {\<NN>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"
  by 
    (
      rule 
        down[
          of _ \<open>set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}\<close>
          ]
    ) 
    auto


text\<open>Further elementary results.\<close>

lemma these_tm_tdghms_iff: (*not simp*)
  "\<NN> \<in>\<^sub>\<circ> these_tm_tdghms \<alpha> \<AA> \<BB> \<FF> \<GG> \<longleftrightarrow>
    \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  by auto


subsubsection\<open>
Opposite transformation of digraph homomorphisms with tiny maps
\<close>

lemma (in is_tm_tdghm) is_tm_tdghm_op:
  "op_tdghm \<NN> : op_dghm \<GG> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m op_dghm \<FF> : op_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_dg \<BB>"
  by (intro is_tm_tdghmI)
    (cs_concl cs_intro: dg_cs_intros dg_op_intros)+

lemma (in is_tm_tdghm) is_tm_tdghm_op'[dg_op_intros]: 
  assumes "\<GG>' = op_dghm \<GG>"
    and "\<FF>' = op_dghm \<FF>"
    and "\<AA>' = op_dg \<AA>"
    and "\<BB>' = op_dg \<BB>"
  shows "op_tdghm \<NN> : \<GG>' \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<FF>' : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule is_tm_tdghm_op)

lemmas is_tm_tdghm_op[dg_op_intros] = is_tm_tdghm.is_tm_tdghm_op'


subsubsection\<open>
Composition of a transformation of digraph homomorphisms with tiny
maps and a digraph homomorphism with tiny maps
\<close>

lemma tdghm_dghm_comp_is_tm_tdghm:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH> : \<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<NN>: is_tm_tdghm \<alpha> \<BB> \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<HH>: is_tm_dghm \<alpha> \<AA> \<BB> \<HH> by (rule assms(2))
  show ?thesis
    by (rule is_tm_tdghmI)
      (
        cs_concl
          cs_simp: dg_cs_simps cs_intro: dg_cs_intros dg_small_cs_intros
      )+
qed

lemma tdghm_dghm_comp_is_tm_tdghm'[dg_small_cs_intros]:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF>' = \<FF> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>"
    and "\<GG>' = \<GG> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH>"
  shows "\<NN> \<circ>\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<HH> : \<FF>' \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1,2) unfolding assms(3,4) by (rule tdghm_dghm_comp_is_tm_tdghm)


subsubsection\<open>
Composition of a digraph homomorphism with tiny maps and a  
transformation of digraph homomorphisms with tiny maps
\<close>

lemma dghm_tdghm_comp_is_tm_tdghm:
  assumes "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" and "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN> : \<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<HH>: is_tm_dghm \<alpha> \<BB> \<CC> \<HH> by (rule assms(1))
  interpret \<NN>: is_tm_tdghm \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  show ?thesis
    by (rule is_tm_tdghmI)
      (
        cs_concl
          cs_simp: dg_cs_simps cs_intro: dg_cs_intros dg_small_cs_intros
      )+
qed

lemma dghm_tdghm_comp_is_tm_tdghm'[dg_small_cs_intros]:
  assumes "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF>' = \<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<FF>"
    and "\<GG>' = \<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG>"
  shows "\<HH> \<circ>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>-\<^sub>T\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<NN> : \<FF>' \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1,2) unfolding assms(3,4) by (rule dghm_tdghm_comp_is_tm_tdghm)



subsection\<open>Transformation of homomorphisms of tiny digraphs\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale is_tiny_tdghm = 
  \<Z> \<alpha> + 
  NTDom: is_tiny_dghm \<alpha> \<AA> \<BB> \<FF> +
  NTCod: is_tiny_dghm \<alpha> \<AA> \<BB> \<GG> +
  is_tdghm \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>
  for \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>

syntax "_is_tiny_tdghm" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y _ :/ _ \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons>
  "CONST is_tiny_tdghm \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>"

abbreviation all_tiny_tdghms :: "V \<Rightarrow> V"
  where "all_tiny_tdghms \<alpha> \<equiv> 
    set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation tiny_tdghms :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "tiny_tdghms \<alpha> \<AA> \<BB> \<equiv> 
    set {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation these_tiny_tdghms :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "these_tiny_tdghms \<alpha> \<AA> \<BB> \<FF> \<GG> \<equiv> 
    set {\<NN>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"


text\<open>Rules.\<close>

lemmas (in is_tiny_tdghm) [dg_small_cs_intros] = is_tiny_tdghm_axioms

mk_ide rf is_tiny_tdghm_def
  |intro is_tiny_tdghmI[intro]|
  |dest is_tiny_tdghmD[dest]|
  |elim is_tiny_tdghmE[elim]|

lemmas [dg_small_cs_intros] = is_tiny_tdghmD(2,3,4)


text\<open>Elementary properties.\<close>

sublocale is_tiny_tdghm \<subseteq> is_tm_tdghm
  by (rule is_tm_tdghmI) 
    (auto simp: vfsequence_axioms dg_cs_intros dg_small_cs_intros)

lemmas (in is_tiny_tdghm) tiny_tdghm_is_tm_tdghm = is_tm_tdghm_axioms

lemmas [dg_small_cs_intros] = is_tiny_tdghm.tiny_tdghm_is_tm_tdghm


text\<open>Size.\<close>

lemma (in is_tiny_tdghm) tiny_tdghm_in_Vset: "\<NN> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  note [dg_cs_intros] =
    tm_tdghm_NTMap_in_Vset
    NTDom.tiny_dghm_in_Vset
    NTCod.tiny_dghm_in_Vset
    NTDom.HomDom.tiny_dg_in_Vset
    NTDom.HomCod.tiny_dg_in_Vset
  show ?thesis
    by (subst tdghm_def) 
      (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros V_cs_intros)
qed

lemma small_all_tiny_tdghms[simp]:
  "small {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(rule down)
  show "{\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq> 
    elts (set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>})"
  proof
    (
      simp only: elts_of_set small_all_tdghms if_True, 
      rule subsetI, 
      unfold mem_Collect_eq
    )
    fix \<NN> assume "\<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    then obtain \<FF> \<GG> \<AA> \<BB> where \<NN>: "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
      by clarsimp
    interpret is_tiny_tdghm \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule \<NN>)
    have "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" by (auto intro: dg_cs_intros)
    then show "\<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> \<BB>" by auto
  qed
qed

lemma small_tiny_tdghms[simp]: 
  "small {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"
  by 
    (
      rule 
        down[
          of _ \<open>set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}\<close>
          ]
    )
    auto

lemma small_these_tiny_tdghms[simp]: 
  "small {\<NN>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"
  by 
    (
      rule 
        down[
          of _ \<open>set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}\<close>
          ]
    ) 
    auto

lemma tiny_tdghms_vsubset_Vset[simp]: 
  "set {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  (is \<open>set ?tdghms \<subseteq>\<^sub>\<circ> _\<close>)
proof(cases \<open>tiny_digraph \<alpha> \<AA> \<and> tiny_digraph \<alpha> \<BB>\<close>)
  case True
  then have "tiny_digraph \<alpha> \<AA>" and "tiny_digraph \<alpha> \<BB>" by auto
  show ?thesis 
  proof(rule vsubsetI)
    fix \<NN> assume "\<NN> \<in>\<^sub>\<circ> set ?tdghms"
    then obtain \<FF> \<GG> where \<FF>: "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>" 
      by clarsimp
    interpret is_tiny_tdghm \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule \<FF>)
    from tiny_tdghm_in_Vset show "\<NN> \<in>\<^sub>\<circ> Vset \<alpha>" by simp
  qed
next
  case False
  then have "set ?tdghms = 0" by fastforce
  then show ?thesis by simp
qed

lemma (in is_tdghm) tdghm_is_tiny_tdghm_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> \<BB>" 
proof(intro is_tiny_tdghmI)
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "\<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<beta>\<^esub> \<BB>"
    by (intro tdghm_is_tdghm_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: dg_cs_intros\<close>)+
  show "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> \<BB>" "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> \<BB>"
    by 
      (
        simp_all add:
          NTDom.dghm_is_tiny_dghm_if_ge_Limit
          NTCod.dghm_is_tiny_dghm_if_ge_Limit
          \<beta>.\<Z>_axioms 
          assms(2)
      )
qed (rule assms(1))


text\<open>Further elementary results.\<close>

lemma these_tiny_tdghms_iff: (*not simp*)
  "\<NN> \<in>\<^sub>\<circ> these_tiny_tdghms \<alpha> \<AA> \<BB> \<FF> \<GG> \<longleftrightarrow>
    \<NN> : \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  by auto


subsubsection\<open>Opposite transformation of homomorphisms of tiny digraphs\<close>

lemma (in is_tiny_tdghm) is_tm_tdghm_op: "op_tdghm \<NN> :
  op_dghm \<GG> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y op_dghm \<FF> : op_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> op_dg \<BB>"
  by (intro is_tiny_tdghmI)
   (cs_concl cs_intro: dg_cs_intros dg_op_intros)+

lemma (in is_tiny_tdghm) is_tiny_tdghm_op'[dg_op_intros]: 
  assumes "\<GG>' = op_dghm \<GG>"
    and "\<FF>' = op_dghm \<FF>"
    and "\<AA>' = op_dg \<AA>"
    and "\<BB>' = op_dg \<BB>"
  shows "op_tdghm \<NN> : \<GG>' \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<FF>' : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule is_tm_tdghm_op)

lemmas is_tiny_tdghm_op[dg_op_intros] = is_tiny_tdghm.is_tiny_tdghm_op'

text\<open>\newpage\<close>

end